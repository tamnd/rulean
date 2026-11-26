//! Definitional equality of engine F on values (spec 05.4.4), and the way engine F and engine R share a query (spec 05.1).
//!
//! `conv` gives true only by official rules: the quick checks, beta, delta, iota, the `Nat` extension, proof irrelevance, lazy delta on glued heads, the same head with equal arguments, and function eta. It does not try structure eta, unit-like types or the string literal expansion. When it does not find an equality it gives false, and engine R decides the query on the terms (rule 2 of spec 05.1).
//!
//! `conv` opens a binder with a local declaration of the checker, as engine R does. So each free variable of a value is in the local context, and each value can be read back.

use rulean_format::Hints;
use rulean_store::ids::raw;
use rulean_store::{BinderInfo, Expr, ExprId, LevelListId, NameId, SATURATED};

use crate::env::compare_hints;
use crate::expr;
use crate::level;
use crate::pin::PIN_NAT;
use crate::tc::{Checker, ErrorKind, LBool, to_lbool};
use crate::trace::Rule;
use crate::value::{Closure, EnvId, Head, SpineId, Value, ValueId, small_get};

/// The engine of the definitional equality queries.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Engine {
    /// Engine R only (`--engine R`).
    #[default]
    R,
    /// Engine F first, then engine R when F does not find an equality (`--engine F`).
    F,
}

/// The counts of engine F for one run.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FStats {
    /// The queries that engine F tried.
    pub queries: u64,
    /// The queries where engine F found an equality.
    pub equal: u64,
    /// The queries that engine R decided after engine F.
    pub fallback: u64,
    /// The equalities of engine F that engine R confirmed (`--confirm all`).
    pub confirmed: u64,
    /// The equalities of engine F that engine R did not confirm. The answer is then "not equal".
    pub disagree: u64,
    /// The queries where engine F stopped with a fault, and engine R decided the query.
    pub faults: u64,
    /// The type checks and value checks of declarations that engine F inference tried (spec 05.4.5).
    pub infer: u64,
    /// The type checks and value checks that engine F inference accepted. Engine R did the others.
    pub infer_ok: u64,
}

/// The largest number of nodes that `same_value` visits. The check runs at each step of `conv`, and a failed check on a deep value runs again on each part of it, so a large budget costs time. On the Init export of v4.36.0, engine F uses 458 G instructions with 16, 435 G with 64, 423 G with 256 and 417 G with 1024. On the 42 Arena perf tests, the budget 256 makes `magma-list-pair-n21` slower (113.4 G to 120.6 G instructions), and 1024 makes `church-numerals` slower (0.1 G to 1.7 G).
const SAME_BUDGET: u32 = 64;

/// The largest number of delta steps on the side of a taken branch in `conv_lazy_delta` (row O8 of spec 05.7.3).
const TAKEN_STEPS: u32 = 32;

/// The steps of the offset view of one value (row O11 of spec 05.7.3): an unfolding of a head, a reduced projection, or a peeled offset. The view stops after these steps, and the value that it has then is the base.
const OFFSET_STEPS: u32 = 16;

/// The depth of the offset view in the second argument of `Nat.add`, which must be a literal.
const OFFSET_DEPTH: u32 = 2;

/// A bit of `Checker::f_bits`: the query used a delta step.
pub(crate) const F_DELTA: u32 = 1;
/// A bit of `Checker::f_bits`: the query used a type-directed rule (K-like reduction or structure eta of a major premise).
pub(crate) const F_TYPED: u32 = 2;

impl Checker {
    /// `is_def_eq` with engine F first (spec 05.1). The sub-queries of a query, in engine F or in engine R, use engine R only.
    ///
    /// An "equal" answer of engine F is final, but engine R confirms it if the query used both a type-directed rule and a delta step (the confirm set of spec 05.1), or if `confirm_all` is true. A "not equal" answer of engine F is only a hint, so engine R decides the query. If engine F stops with a fault, the fault is removed and engine R decides the query.
    pub(crate) fn is_def_eq_shared(&mut self, t: ExprId, s: ExprId) -> bool {
        if self.engine == Engine::R || self.eq_depth > 0 || self.bad() || self.va.full() {
            return self.is_def_eq_r(t, s);
        }
        self.f_stats.queries += 1;
        let depth = self.depth;
        self.f_bits = 0;
        self.c_conv_failure.clear();
        self.c_conv_success.clear();
        self.eq_depth += 1;
        let a = self.eval(EnvId::NIL, t);
        let b = self.eval(EnvId::NIL, s);
        let f = self.conv(a, b);
        self.eq_depth -= 1;
        let anon = self.st.anon();
        if self.bad() {
            self.fault = None;
            self.depth = depth;
            self.f_stats.faults += 1;
            self.note(Rule::FFallback, anon);
            return self.is_def_eq_r(t, s);
        }
        if !f {
            self.f_stats.fallback += 1;
            self.note(Rule::FFallback, anon);
            return self.is_def_eq_r(t, s);
        }
        self.f_stats.equal += 1;
        let confirm = self.confirm_all || self.f_bits == F_DELTA | F_TYPED;
        if !confirm {
            self.note(Rule::FEqual, anon);
            return true;
        }
        let r = self.is_def_eq_r(t, s);
        if r {
            self.f_stats.confirmed += 1;
            self.note(Rule::FConfirmed, anon);
        } else if !self.bad() {
            self.f_stats.disagree += 1;
            self.note(Rule::FDisagree, anon);
        }
        r
    }

    /// An engine R query. Its sub-queries do not use engine F.
    pub(crate) fn is_def_eq_r(&mut self, t: ExprId, s: ExprId) -> bool {
        self.eq_depth += 1;
        let r = self.is_def_eq_core(t, s);
        self.eq_depth -= 1;
        r
    }

    /// `conv(a, b)`: true if engine F finds that the values are definitionally equal. A pair that is not equal goes into a failure cache for the rest of the top-level query, as in the official kernel. Without the cache, lazy delta compares the same arguments again after each unfold of the same head, and the time can be exponential. A pair that is equal goes into a success cache for the rest of the top-level query (row O2 of spec 05.7.3). Without it, two trees with shared subtrees, such as `node a a` and `node b b`, compare `a` and `b` once for each path, and the time is exponential in the depth. A value does not change in the arena, and the local context only grows in a query, so a pair that was equal stays equal.
    pub fn conv(&mut self, a: ValueId, b: ValueId) -> bool {
        if a == b {
            return true;
        }
        if self.bad() {
            return false;
        }
        if self.c_conv_failure.contains(raw(a.0), raw(b.0))
            || self.c_conv_failure.contains(raw(b.0), raw(a.0))
        {
            return false;
        }
        if self.c_conv_success.contains(raw(a.0), raw(b.0)) {
            return true;
        }
        if !self.enter(self.dummy) {
            return false;
        }
        let r = self.conv_body(a, b);
        self.leave();
        if !self.bad() {
            if r {
                self.c_conv_success.put(raw(a.0), raw(b.0), 1);
            } else {
                self.c_conv_failure.put(raw(a.0), raw(b.0), 1);
            }
        }
        r && !self.bad()
    }

    fn conv_body(&mut self, a: ValueId, b: ValueId) -> bool {
        if self.same_value(a, b) {
            return true;
        }
        let q = self.conv_quick(a, b);
        if q != LBool::Undef {
            return q == LBool::True;
        }
        if self.flags.proof_irrel_first {
            let p = self.conv_proof_irrel(a, b);
            if p != LBool::Undef {
                return p == LBool::True;
            }
        }
        let a1 = self.force_core(a);
        let b1 = self.force_core(b);
        if self.bad() {
            return false;
        }
        if a1 != a || b1 != b {
            let q = self.conv_quick(a1, b1);
            if q != LBool::Undef {
                return q == LBool::True;
            }
        }
        if !self.flags.proof_irrel_first {
            let p = self.conv_proof_irrel(a1, b1);
            if p != LBool::Undef {
                return p == LBool::True;
            }
        }
        let (q, x, y) = self.conv_lazy_delta(a1, b1);
        if q != LBool::Undef {
            return q == LBool::True;
        }
        self.conv_whnf(x, y)
    }

    /// Proof irrelevance (spec 05.4.4 step 3 and 05.7.1). If the type of `a` is a proposition, `a` and `b` are equal when their types are equal. The rule needs the types, so it reads both values back and uses `is_def_eq_proof_irrel` of engine R. It is a type-directed rule, so it sets `F_TYPED`. Without this step, engine F compares two proofs of the same proposition by their structure, and it can unfold a proof that computes for a long time, for example a proof by `decide` on a large `Nat` literal.
    ///
    /// The step first looks at the heads of the values. If one value is never a proof (`never_proof`), the step does not apply, and the values are not read back. The step gives only "equal" or "not equal by proof irrelevance", so a skipped step can only make engine F give "not equal", and then engine R decides the query.
    fn conv_proof_irrel(&mut self, a: ValueId, b: ValueId) -> LBool {
        if self.never_proof(a) || self.never_proof(b) {
            return LBool::Undef;
        }
        let base = self.lctx_ty.len() as u32;
        let ta = self.quote(base, base, a);
        let tb = self.quote(base, base, b);
        if self.bad() {
            return LBool::Undef;
        }
        let r = self.is_def_eq_proof_irrel(ta, tb);
        if r == LBool::True {
            self.f_bits |= F_TYPED;
            let anon = self.st.anon();
            self.note(Rule::ProofIrrel, anon);
        }
        r
    }

    /// True if the type of `v` is not a proposition for each value of the level parameters. A sort, a literal and a Pi type are never proofs. An application of a constant is never a proof if the type of the constant ends in a sort, or in an inductive type whose sort is never zero (`const_never_proof`). For other values the result is false, and the step reads the values back.
    fn never_proof(&mut self, v: ValueId) -> bool {
        match self.vget(v) {
            Value::Sort(_) | Value::Lit(_) | Value::Small(..) | Value::Pi(..) => true,
            Value::Neu(Head::Const(c, _), _) => self.const_never_proof(c),
            Value::Neu(Head::FVar(l, _), _) => self.fvar_never_proof(l),
            Value::Glued(c, _, _, _) => self.const_never_proof(c),
            _ => false,
        }
    }

    /// `never_proof` for an application of the local `l`. It uses the type of the local in the local context, as `const_never_proof` uses the type of a constant. A local whose type ends in a free variable `α` is never a proof if the type of `α` is a sort with a level that is never zero. This is the case of `f : α → α` with `α : Type`. Without this case, proof irrelevance reads back each argument of `f (f (... x))`, and the time is quadratic in the depth.
    fn fvar_never_proof(&mut self, l: u32) -> bool {
        let i = l as usize;
        if i >= self.lctx_ty.len() {
            return false;
        }
        let t = self.pi_codomain(self.lctx_ty[i]);
        self.codomain_never_prop(t)
    }

    /// True if a term with the type `t` is never a proof, where `t` is the codomain of a type after its Pi binders. A sort is a type of types. An application of an inductive type whose sort is never zero, and a free variable whose type is such a sort, are types that are not propositions.
    fn codomain_never_prop(&mut self, t: ExprId) -> bool {
        match self.st.node(t) {
            Expr::Sort(_) => true,
            Expr::FVar(_, ty) => match self.st.node(ty) {
                Expr::Sort(u) => level::is_not_zero(&self.st, u),
                _ => false,
            },
            _ => self.induct_type_not_prop(t),
        }
    }

    /// `never_proof` for an application of the constant `c`, with a memo in `c_never_proof`. The function removes the Pi binders of the type of `c`. If the rest is a sort, an application of `c` is a type. If the rest is an application of an inductive type whose own type ends in a sort with a level that is never zero, an application of `c` is a value of a type that is not a proposition. A partial application of `c` has a Pi type whose codomain is that type, and it is also not a proposition. The function does not unfold the rest, so a type such as a definition that unfolds to a proposition gives false.
    fn const_never_proof(&mut self, c: NameId) -> bool {
        if let Some(x) = self.c_never_proof.get(raw(c.0), 0) {
            return x == 1;
        }
        let slot = self.env.find(c);
        let r = if slot == 0 {
            false
        } else {
            let ty = self.env.at(slot).ty;
            let t = self.pi_codomain(ty);
            self.codomain_never_prop(t) || self.bvar_codomain_never_prop(ty)
        };
        self.c_never_proof.put(raw(c.0), 0, if r { 1 } else { 2 });
        r
    }

    /// True if the type `ty` of a constant ends in a bound variable `α` of its own Pi binders, maybe applied, and the type of `α` ends in a sort with a level that is never zero. This is the case of a projection function such as `HAdd.hAdd : {α β γ : Type} → [HAdd α β γ] → α → β → γ`. The type of `α` can be `outParam (Type u)` or another application of a definition whose value is `fun x => x`, and then the step uses the argument.
    fn bvar_codomain_never_prop(&mut self, ty: ExprId) -> bool {
        let mut n: u32 = 0;
        let mut cur = ty;
        let mut walking = true;
        while walking {
            match self.st.node(cur) {
                Expr::Pi(b) => {
                    n += 1;
                    cur = b.body;
                }
                _ => walking = false,
            }
        }
        let i = match self.st.node(expr::app_fn(&self.st, cur)) {
            Expr::BVar(i) => i,
            _ => return false,
        };
        if i >= n {
            return false;
        }
        // The binder of `α` is binder n - 1 - i, counted from 0 at the outside.
        let mut k = n - 1 - i;
        let mut d = ty;
        cur = ty;
        walking = true;
        while walking {
            match self.st.node(cur) {
                Expr::Pi(b) => {
                    if k == 0 {
                        d = b.dom;
                        walking = false;
                    } else {
                        k -= 1;
                        cur = b.body;
                    }
                }
                _ => walking = false,
            }
        }
        let d = self.strip_identity_def(d);
        match self.st.node(self.pi_codomain(d)) {
            Expr::Sort(l) => level::is_not_zero(&self.st, l),
            _ => false,
        }
    }

    /// `t` without an application `f x` of a definition `f` whose value is `fun y => y`, such as `outParam` and `semiOutParam`. Other terms do not change.
    fn strip_identity_def(&mut self, t: ExprId) -> ExprId {
        if let Expr::App(f, x) = self.st.node(t) {
            if let Expr::Const(c, _) = self.st.node(f) {
                let slot = self.env.find(c);
                if slot != 0 {
                    if let Some(v) = self.env.at(slot).value() {
                        if let Expr::Lam(b) = self.st.node(v) {
                            if let Expr::BVar(0) = self.st.node(b.body) {
                                return x;
                            }
                        }
                    }
                }
            }
        }
        t
    }

    /// The term after the Pi binders of `t`, with no reduction.
    fn pi_codomain(&self, t: ExprId) -> ExprId {
        let mut cur = t;
        let mut walking = true;
        while walking {
            match self.st.node(cur) {
                Expr::Pi(b) => cur = b.body,
                _ => walking = false,
            }
        }
        cur
    }

    /// True if `t` is an application of an inductive type whose own type ends in a sort with a level that is never zero.
    pub(crate) fn induct_type_not_prop(&mut self, t: ExprId) -> bool {
        let h = expr::app_fn(&self.st, t);
        match self.st.node(h) {
            Expr::Const(i, _) => {
                let slot = self.env.find(i);
                if slot == 0 || !self.env.at(slot).is_induct() {
                    return false;
                }
                let it = self.pi_codomain(self.env.at(slot).ty);
                match self.st.node(it) {
                    Expr::Sort(l) => level::is_not_zero(&self.st, l),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// The quick checks: sorts, literals and binders with the same form.
    fn conv_quick(&mut self, a: ValueId, b: ValueId) -> LBool {
        if a == b {
            return LBool::True;
        }
        match (self.vget(a), self.vget(b)) {
            (Value::Sort(l1), Value::Sort(l2)) => {
                to_lbool(level::is_equivalent(&mut self.st, &mut self.lc, l1, l2))
            }
            (Value::Lit(x), Value::Lit(y)) => {
                if x == y {
                    LBool::True
                } else {
                    LBool::Undef
                }
            }
            (Value::Small(x1, x2), Value::Small(y1, y2)) => {
                if x1 == y1 && x2 == y2 {
                    LBool::True
                } else {
                    LBool::Undef
                }
            }
            (Value::Lam(_, _, d1, c1), Value::Lam(_, _, d2, c2)) => {
                to_lbool(self.conv_binder(d1, c1, d2, c2))
            }
            (Value::Pi(_, _, d1, c1), Value::Pi(_, _, d2, c2)) => {
                to_lbool(self.conv_binder(d1, c1, d2, c2))
            }
            _ => LBool::Undef,
        }
    }

    /// A new local declaration of the type `d`, as a neutral value.
    fn f_local(&mut self, d: ValueId) -> ValueId {
        let base = self.lctx_ty.len() as u32;
        let ty = self.quote(base, base, d);
        let anon = self.st.anon();
        self.mk_local(anon, BinderInfo::Default, ty, None);
        let v = self.va.neutral(Head::FVar(base, d));
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        v
    }

    /// Two binders: equal domains, and equal bodies under a new local.
    fn conv_binder(&mut self, d1: ValueId, c1: Closure, d2: ValueId, c2: Closure) -> bool {
        if !self.conv(d1, d2) {
            return false;
        }
        let x = self.f_local(d1);
        let b1 = self.inst_closure(c1, x);
        let b2 = self.inst_closure(c2, x);
        self.conv(b1, b2)
    }

    /// The body of a closure with `x` for its bound variable.
    fn inst_closure(&mut self, c: Closure, x: ValueId) -> ValueId {
        let env = self.va.env_push(c.env, x);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        self.eval(env, c.body)
    }

    /// The glued head of a value: the constant, its levels, the spine and the hint.
    fn glued_head(&mut self, v: ValueId) -> Option<(NameId, LevelListId, SpineId, Hints)> {
        match self.vget(v) {
            Value::Glued(c, us, sp, _) => {
                let slot = self.env.find(c);
                let h = if slot == 0 {
                    Hints::Opaque
                } else {
                    self.hints(slot)
                };
                Some((c, us, sp, h))
            }
            _ => None,
        }
    }

    /// One delta step: the `Nat` extension if it applies, else unfold the glued head. Then reduce without delta.
    fn conv_delta(&mut self, v: ValueId) -> ValueId {
        match self.vget(v) {
            Value::Glued(c, us, sp, s) => {
                let cheap = self.cheap_proj;
                self.cheap_proj = true;
                let u = match self.glued_nat(c, us, sp, s) {
                    Some(n) => n,
                    None => self.unfold_glued(c, us, sp, s),
                };
                let w = self.force_core(u);
                self.cheap_proj = cheap;
                w
            }
            _ => v,
        }
    }

    /// Lazy delta on glued heads (spec 05.4.4 step 5, A§1.8 step 5). It unfolds the side with the greater height, or both sides if the heights are equal. For two applications of the same regular definition that is not a `Nat` operation, it unfolds both sides, and two unfoldings of the same form are equal (row O12 of spec 05.7.3). If they do not have the same form, it compares the levels and the arguments, and then it goes on with the unfoldings. On `perf/short-circuit-and`, `false && a` and `false && b` both unfold to `false`, and the open terms `a` and `b` are not compared.
    ///
    /// If the heads are different and one side is an application of a binary `Nat` operation with an argument that is not a literal without delta, the other side unfolds first (row O10 of spec 05.7.3). The `Nat` extension would unfold that argument to a literal, and the other side can reach the same operation with the same argument. On `perf/unfold-before-literal`, `[slowA, 1].sum` and `slowA + (1 + 0)` both reach `Nat.add slowA _`, and the arguments are then compared before the `Nat` extension evaluates `slowA`.
    ///
    /// If one side is a definition and the other side is a projection of a folded structure, the projection is reduced first, and the definition is unfolded only if the projection does not reduce. Without this step, the definition is unfolded to its weak head normal form before the projection gives a value with the same head, and the checks of the same head and of reflexivity cannot stop the unfolding early.
    ///
    /// If the side with the smaller height has the other side as an argument, as in `ite c a b =?= a`, that side is unfolded first, for at most `TAKEN_STEPS` steps (row O8 of spec 05.7.3). A branch that the condition takes then gives the other side with no unfolding of it. On `perf/ite-taken-branch`, the official order unfolds `a`, which computes an array of 300 numbers with a loop, and engine F filled its arena on each of the three theorems.
    fn conv_lazy_delta(&mut self, a: ValueId, b: ValueId) -> (LBool, ValueId, ValueId) {
        let mut x = a;
        let mut y = b;
        let mut r = LBool::Undef;
        let mut done = false;
        // The side of a taken branch: -1 unfolds `x`, 1 unfolds `y`, 0 is the official order.
        let mut lead = 0;
        let mut taken = 0;
        while !done && !self.bad() {
            // The offset rule runs before each step, as `is_def_eq_offset` in the official kernel (row O11).
            let offset = self.conv_offset(x, y);
            match (self.glued_head(x), self.glued_head(y)) {
                _ if offset => {
                    r = LBool::True;
                    done = true;
                }
                (None, None) => done = true,
                (Some(_), None) => {
                    let y2 = self.proj_unfold(y);
                    if y2 != y {
                        y = self.force_core(y2);
                    } else {
                        x = self.conv_delta(x);
                    }
                }
                (None, Some(_)) => {
                    let x2 = self.proj_unfold(x);
                    if x2 != x {
                        x = self.force_core(x2);
                    } else {
                        y = self.conv_delta(y);
                    }
                }
                (Some((c1, us1, sp1, h1)), Some((c2, us2, sp2, h2))) => {
                    let mut c = compare_hints(h1, h2);
                    if c1 == c2 || taken >= TAKEN_STEPS {
                        lead = 0;
                    } else if lead == 0 && c > 0 && self.spine_holds(sp1, c2, y) {
                        lead = -1;
                    } else if lead == 0 && c < 0 && self.spine_holds(sp2, c1, x) {
                        lead = 1;
                    }
                    if lead != 0 {
                        c = lead;
                        taken += 1;
                    }
                    // A `Nat` operation that waits unfolds after the other side (row O10).
                    if c1 != c2 {
                        let wx = self.nat_waits(x);
                        let wy = self.nat_waits(y);
                        if wx && !wy {
                            c = 1;
                        } else if wy && !wx {
                            c = -1;
                        }
                    }
                    if c < 0 {
                        x = self.conv_delta(x);
                    } else if c > 0 {
                        y = self.conv_delta(y);
                    } else {
                        let regular = matches!(h1, Hints::Regular(_));
                        // Two sides of the same form are equal (row O7). Else, for a regular definition, the arguments are compared before the unfolding.
                        let same = c1 == c2 && self.same_value(x, y);
                        let args = regular && c1 == c2 && !same;
                        // For the same regular head, both sides unfold first, and two unfoldings of the same form are equal (row O12). Else the arguments are compared, and lazy delta goes on with the unfoldings. A `Nat` operation does not unfold first, because the `Nat` extension evaluates its arguments.
                        let first = args && self.nat_op_name_index(c1) == self.b.nat_op_names.len();
                        let bits = self.f_bits;
                        let x2 = if first { self.conv_delta(x) } else { x };
                        let y2 = if first { self.conv_delta(y) } else { y };
                        let unfolded = same || (first && !self.bad() && self.same_value(x2, y2));
                        // An equality of the arguments does not use the two unfoldings, so their bits of `f_bits` are added only if lazy delta goes on with them. Else the query goes to the confirm set with no need.
                        let delta = self.f_bits;
                        if !unfolded {
                            self.f_bits = bits;
                        }
                        if unfolded
                            || (args
                                && !self.bad()
                                && self.is_def_eq_levels(us1, us2)
                                && self.conv_spines(sp1, sp2))
                        {
                            r = LBool::True;
                            done = true;
                        } else if first {
                            self.f_bits |= delta;
                            x = x2;
                            y = y2;
                        } else {
                            x = self.conv_delta(x);
                            y = self.conv_delta(y);
                        }
                    }
                }
            }
            if !done && !self.bad() {
                let q = self.conv_quick(x, y);
                if q != LBool::Undef {
                    r = q;
                    done = true;
                }
            }
        }
        (r, x, y)
    }

    /// The offset rule of engine F (row O11 of spec 05.7.3): true if `a` is `x + k` and `b` is `y + k` for the same literal `k > 0`, and `x` and `y` are equal. The view of a value (`nat_offset`) unfolds `HAdd.hAdd`, `Add.add` and `OfNat.ofNat`, and it peels `Nat.add x n` for a literal `n`, `Nat.succ x` and literals.
    ///
    /// The official kernel peels only `Nat.succ` and literals (`is_def_eq_offset`). It does not peel `x + 1`, so on `perf/unfold-before-literal-fallback` it compares `(slowA + 1) + (1 + 0)` with `slowA + (2 + 0)` by the evaluation of `slowA` to a literal. The rule is sound because `Nat.add x n` is `Nat.succ` applied `n` times to `x` by the definition of `Nat.add`, which is pinned. The rule gives only "equal". If the offsets or the bases are different, the normal steps decide the query.
    fn conv_offset(&mut self, a: ValueId, b: ValueId) -> bool {
        let on = self.pin_on(PIN_NAT) && self.pin_on(1);
        let heads = on && self.offset_head(a) && self.offset_head(b);
        if !heads {
            return false;
        }
        let (xa, ka) = self.nat_offset(a, OFFSET_DEPTH);
        let (xb, kb) = self.nat_offset(b, OFFSET_DEPTH);
        match (xa, xb) {
            (Some(x), Some(y)) if ka == kb && ka > 0 && !self.bad() => self.conv(x, y),
            _ => false,
        }
    }

    /// True if `v` is an addition of type `Nat` or `Nat.succ x`, with no evaluation of an argument. This check comes first, so the offset rule costs little on the other queries.
    fn offset_head(&mut self, v: ValueId) -> bool {
        match self.vget(v) {
            Value::Glued(c, us, sp, _) => {
                let n = self.va.spine_len(sp);
                let add = c == self.b.nat_op_names[0] && us == LevelListId(0) && n == 2;
                let hadd = c == self.b.hadd_hadd && n == 6;
                let add2 = c == self.b.add_add && n == 4;
                add || ((hadd || add2) && self.nat_type_arg(self.va.spine_arg(sp, 0)))
            }
            Value::Neu(Head::Const(c, _), sp) => c == self.b.nat_succ && self.va.spine_len(sp) == 1,
            _ => false,
        }
    }

    /// True if the argument `a` is the type `Nat`, with no evaluation.
    fn nat_type_arg(&mut self, a: Option<ValueId>) -> bool {
        match a {
            Some(x) => match self.va.get(x) {
                Value::Neu(Head::Const(c, _), sp) => c == self.b.nat && sp == SpineId::NIL,
                Value::Susp(_, t, _) => {
                    matches!(self.st.node(t), Expr::Const(c, _) if c == self.b.nat)
                }
                _ => false,
            },
            None => false,
        }
    }

    /// The offset view of `v` (row O11 of spec 05.7.3): a base `x` and a number `k` such that `v` is `Nat.succ` applied `k` times to `x`. The base is `None` if `v` is the literal `k`. The view unfolds `HAdd.hAdd`, `Add.add` and `OfNat.ofNat`, reduces projections, and peels `Nat.add x n` if the view of `n` at depth `depth - 1` is a literal. In the literal argument of `Nat.add`, where `depth` is less than `OFFSET_DEPTH`, the view also unfolds other definitions, as the `List.foldr` of `List.sum`, but not a `Nat` operation, because the `Nat` extension would evaluate its arguments. The base of the top view is not unfolded. The view does at most `OFFSET_STEPS` steps.
    fn nat_offset(&mut self, v: ValueId, depth: u32) -> (Option<ValueId>, u64) {
        let mut w = v;
        let mut k: u64 = 0;
        let mut lit = false;
        let mut go = true;
        let mut steps = 0;
        while go && steps < OFFSET_STEPS && !self.bad() {
            steps += 1;
            match self.vget(w) {
                Value::Glued(c, ..)
                    if c == self.b.hadd_hadd
                        || c == self.b.add_add
                        || c == self.b.of_nat_of_nat =>
                {
                    w = self.conv_delta(w);
                }
                Value::Neu(Head::Proj(..), _) => {
                    let w2 = self.proj_unfold(w);
                    if w2 == w {
                        go = false;
                    } else {
                        w = self.force_core(w2);
                    }
                }
                Value::Glued(c, us, sp, s)
                    if c == self.b.nat_op_names[0]
                        && us == LevelListId(0)
                        && self.va.spine_len(sp) == 2 =>
                {
                    match self.va.slot_get(s) {
                        Some(n) => w = n,
                        None => {
                            let n = match (depth, self.va.spine_arg(sp, 1)) {
                                (d, Some(y)) if d > 0 => self.nat_offset(y, d - 1),
                                _ => (Some(w), 0),
                            };
                            let sum = k.checked_add(n.1);
                            match (n.0, sum, self.va.spine_arg(sp, 0)) {
                                (None, Some(s2), Some(x)) => {
                                    k = s2;
                                    w = x;
                                }
                                _ => go = false,
                            }
                        }
                    }
                }
                Value::Neu(Head::Const(c, _), sp)
                    if c == self.b.nat_succ && self.va.spine_len(sp) == 1 =>
                {
                    match (k.checked_add(1), self.va.spine_arg(sp, 0)) {
                        (Some(s2), Some(x)) => {
                            k = s2;
                            w = x;
                        }
                        _ => go = false,
                    }
                }
                Value::Neu(Head::Const(c, _), sp) if c == self.b.nat_zero && sp == SpineId::NIL => {
                    lit = true;
                    go = false;
                }
                Value::Small(lo, hi) => match k.checked_add(small_get(lo, hi)) {
                    Some(s2) => {
                        k = s2;
                        lit = true;
                        go = false;
                    }
                    None => go = false,
                },
                Value::Glued(c, ..)
                    if depth < OFFSET_DEPTH
                        && self.nat_op_name_index(c) >= self.b.nat_op_names.len() =>
                {
                    w = self.conv_delta(w);
                }
                _ => go = false,
            }
        }
        if lit { (None, k) } else { (Some(w), k) }
    }

    /// True if an argument of the spine `sp` has the form of `v`, a glued value of the constant `c` (row O8 of spec 05.7.3). Only an argument with the head `c` is compared, so the check evaluates no other argument.
    fn spine_holds(&mut self, sp: SpineId, c: NameId, v: ValueId) -> bool {
        let mut s = sp;
        let mut found = false;
        while !found && s != SpineId::NIL {
            let (arg, next) = self.va.spine_node(s);
            let head = match self.va.get(arg) {
                Value::Glued(c2, ..) => c2 == c,
                Value::Susp(_, t, _) => {
                    let f = expr::app_fn(&self.st, t);
                    matches!(self.st.node(f), Expr::Const(c2, _) if c2 == c)
                }
                _ => false,
            };
            found = head && self.same_value(arg, v);
            s = next;
        }
        found
    }

    /// Reflexivity on values (row O7 of spec 05.7.3): true if `a` and `b` have the same form, with no reduction. The form is the same when the constructors, the constants, the levels, the free variables and the literals are the same, and two closures have the same body and environments of the same form. Two values with the same form read back to the same term, so the answer is the quick check of the official step 1, where the official kernel compares two terms by their structure.
    ///
    /// Engine R gets this check for free, because the store shares equal terms: two equal terms are the same node. Engine F makes a new value at each evaluation, so two equal arguments are two different values. Without this check, lazy delta unfolds both sides of two equal applications of an abbreviation, and then compares the unfoldings. On `Lean.Grind.Linarith.lt_norm` in Init, engine F did 6,022 delta steps, and engine R did 55.
    ///
    /// The check visits at most `SAME_BUDGET` nodes. When the budget is used up, it gives false, and the normal steps decide the query.
    fn same_value(&mut self, a: ValueId, b: ValueId) -> bool {
        let mut budget = SAME_BUDGET;
        self.same_in(a, b, &mut budget)
    }

    fn same_in(&mut self, a: ValueId, b: ValueId, budget: &mut u32) -> bool {
        if a == b {
            return true;
        }
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        // Two suspended arguments of the same term are equal without an evaluation when they have the same environment, or when the term has no loose bound variable (spec perf/04.3 A6).
        let (xa, xb) = (self.va.get(a), self.va.get(b));
        if let (Value::Susp(e1, t1, _), Value::Susp(e2, t2, _)) = (xa, xb) {
            if t1 == t2 && self.same_env_top(e1, e2, self.st.loose_range(t1), budget) {
                return true;
            }
        }
        let xa = match xa {
            Value::Susp(..) => self.vget(a),
            x => x,
        };
        let xb = match xb {
            Value::Susp(..) => self.vget(b),
            x => x,
        };
        match (xa, xb) {
            (Value::Sort(l1), Value::Sort(l2)) => l1 == l2,
            (Value::Lit(x), Value::Lit(y)) => x == y,
            (Value::Small(x1, x2), Value::Small(y1, y2)) => x1 == y1 && x2 == y2,
            (Value::Lam(_, _, d1, c1), Value::Lam(_, _, d2, c2))
            | (Value::Pi(_, _, d1, c1), Value::Pi(_, _, d2, c2)) => {
                self.same_in(d1, d2, budget) && self.same_closure(c1, c2, budget)
            }
            (Value::Glued(c1, us1, sp1, _), Value::Glued(c2, us2, sp2, _)) => {
                c1 == c2 && us1 == us2 && self.same_spine(sp1, sp2, budget)
            }
            (Value::Neu(h1, sp1), Value::Neu(h2, sp2)) => {
                let same_head = match (h1, h2) {
                    (Head::FVar(l1, _), Head::FVar(l2, _)) => l1 == l2,
                    (Head::Const(c1, us1), Head::Const(c2, us2)) => c1 == c2 && us1 == us2,
                    (Head::Proj(s1, i1, x1), Head::Proj(s2, i2, x2)) => {
                        s1 == s2 && i1 == i2 && self.same_in(x1, x2, budget)
                    }
                    _ => false,
                };
                same_head && self.same_spine(sp1, sp2, budget)
            }
            _ => false,
        }
    }

    /// Two spines with arguments of the same form.
    fn same_spine(&mut self, s1: SpineId, s2: SpineId, budget: &mut u32) -> bool {
        let mut x = s1;
        let mut y = s2;
        let mut ok = self.va.spine_len(x) == self.va.spine_len(y);
        while ok && x != y && x != SpineId::NIL {
            let (ax, px) = self.va.spine_node(x);
            let (ay, py) = self.va.spine_node(y);
            ok = self.same_in(ax, ay, budget);
            x = px;
            y = py;
        }
        ok
    }

    /// Two closures with the same body and environments of the same form. The bound variable of the binder has index 0, so the body reads only the first `loose_range(body) - 1` values of the environment.
    fn same_closure(&mut self, c1: Closure, c2: Closure, budget: &mut u32) -> bool {
        if c1.body != c2.body {
            return false;
        }
        let k = self.st.loose_range(c1.body);
        let k = if k >= SATURATED {
            k
        } else {
            k.saturating_sub(1)
        };
        self.same_env_top(c1.env, c2.env, k, budget)
    }

    /// Two environments with the same form in the first `k` values (spec perf/04.3 A6). A term with a loose bound variable range of `k` reads only these values, so the term has the same value in the two environments. The other values are not compared. If `k` is `SATURATED`, the two environments must have the same length and the same form in all values.
    fn same_env_top(&mut self, e1: EnvId, e2: EnvId, k: u32, budget: &mut u32) -> bool {
        let mut x = e1;
        let mut y = e2;
        let (n1, n2) = (self.va.env_len(x), self.va.env_len(y));
        let mut ok = if k >= SATURATED {
            n1 == n2
        } else {
            n1 >= k && n2 >= k
        };
        let mut i = 0;
        while ok && i < k && x != y && x != EnvId::NIL {
            let (vx, px) = self.va.env_node(x);
            let (vy, py) = self.va.env_node(y);
            ok = self.same_in(vx, vy, budget);
            x = px;
            y = py;
            i += 1;
        }
        ok
    }

    /// Two spines of the same length with equal arguments.
    fn conv_spines(&mut self, s1: SpineId, s2: SpineId) -> bool {
        if self.va.spine_len(s1) != self.va.spine_len(s2) {
            return false;
        }
        let b1 = self.vstk.len();
        let n = self.va.spine_push_args(s1, &mut self.vstk);
        let b2 = self.vstk.len();
        self.va.spine_push_args(s2, &mut self.vstk);
        let mut ok = true;
        let mut i = 0;
        while ok && i < n {
            let x = self.vstk[b1 + i];
            let y = self.vstk[b2 + i];
            ok = self.conv(x, y);
            i += 1;
        }
        self.vstk.truncate(b1);
        ok
    }

    fn conv_heads(&mut self, h1: Head, h2: Head) -> bool {
        match (h1, h2) {
            (Head::FVar(l1, _), Head::FVar(l2, _)) => l1 == l2,
            (Head::Const(c1, us1), Head::Const(c2, us2)) => {
                c1 == c2 && self.is_def_eq_levels(us1, us2)
            }
            (Head::Proj(s1, i1, x1), Head::Proj(s2, i2, x2)) => {
                s1 == s2 && i1 == i2 && self.conv(x1, x2)
            }
            _ => false,
        }
    }

    /// The steps after lazy delta: the same head with equal arguments, then the projections of folded structures, then function eta.
    ///
    /// As in the official kernel, two projections are first compared by their structures, and only then are the structures unfolded (`is_def_eq_proj`, then `whnf_core` with full projections). `force_core` keeps a projection of a folded structure (`proj_value_core`), so a projection that is still neutral here can reduce after delta on its structure.
    fn conv_whnf(&mut self, a: ValueId, b: ValueId) -> bool {
        let (va, vb) = (self.vget(a), self.vget(b));
        if let (Value::Neu(h1, s1), Value::Neu(h2, s2)) = (va, vb) {
            if self.conv_heads(h1, h2) && self.conv_spines(s1, s2) {
                return true;
            }
        }
        let a2 = self.proj_unfold(a);
        let b2 = self.proj_unfold(b);
        if self.bad() {
            return false;
        }
        if a2 != a || b2 != b {
            return self.conv(a2, b2);
        }
        match (va, vb) {
            (Value::Neu(..), Value::Neu(..)) => false,
            (Value::Lam(_, _, d, c), _) => self.conv_eta(d, c, b),
            (_, Value::Lam(_, _, d, c)) => self.conv_eta(d, c, a),
            _ => false,
        }
    }

    /// Function eta: `fun x => b` and `f` are equal if `b` and `f x` are equal.
    fn conv_eta(&mut self, d: ValueId, c: Closure, f: ValueId) -> bool {
        let x = self.f_local(d);
        let b = self.inst_closure(c, x);
        let fx = self.apply(f, x, self.dummy);
        if self.bad() {
            return false;
        }
        self.conv(b, fx)
    }
}
