//! Definitional equality of engine F on values (spec 05.4.4), and the way engine F and engine R share a query (spec 05.1).
//!
//! `conv` gives true only by official rules: the quick checks, beta, delta, iota, the `Nat` extension, proof irrelevance, lazy delta on glued heads, the same head with equal arguments, and function eta. It does not try structure eta, unit-like types or the string literal expansion. When it does not find an equality it gives false, and engine R decides the query on the terms (rule 2 of spec 05.1).
//!
//! `conv` opens a binder with a local declaration of the checker, as engine R does. So each free variable of a value is in the local context, and each value can be read back.

use rulean_format::Hints;
use rulean_store::{BinderInfo, Expr, ExprId, LevelListId, NameId};

use crate::env::compare_hints;
use crate::expr;
use crate::level;
use crate::tc::{Checker, ErrorKind, LBool, to_lbool};
use crate::trace::Rule;
use crate::value::{Closure, EnvId, Head, SpineId, Value, ValueId};

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
}

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
        if self.c_conv_failure.contains(a.0, b.0) || self.c_conv_failure.contains(b.0, a.0) {
            return false;
        }
        if self.c_conv_success.contains(a.0, b.0) {
            return true;
        }
        if !self.enter(self.dummy) {
            return false;
        }
        let r = self.conv_body(a, b);
        self.leave();
        if !self.bad() {
            if r {
                self.c_conv_success.put(a.0, b.0, 1);
            } else {
                self.c_conv_failure.put(a.0, b.0, 1);
            }
        }
        r && !self.bad()
    }

    fn conv_body(&mut self, a: ValueId, b: ValueId) -> bool {
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
        match self.va.get(v) {
            Value::Sort(_) | Value::Lit(_) | Value::Pi(..) => true,
            Value::Neu(Head::Const(c, _), _) => self.const_never_proof(c),
            Value::Neu(Head::FVar(l, _), _) => self.fvar_never_proof(l),
            Value::Glued(c, _, _, _) => self.const_never_proof(c),
            _ => false,
        }
    }

    /// `never_proof` for an application of the local `l`. It uses the type of the local in the local context, as `const_never_proof` uses the type of a constant. A local whose type ends in a free variable `α` is never a proof if the type of `α` is a sort with a level that is never zero. This is the case of `f : α → α` with `α : Type`. Without this case, proof irrelevance reads back each argument of `f (f (... x))`, and the time is quadratic in the depth.
    fn fvar_never_proof(&self, l: u32) -> bool {
        let i = l as usize;
        if i >= self.lctx_ty.len() {
            return false;
        }
        let t = self.pi_codomain(self.lctx_ty[i]);
        self.codomain_never_prop(t)
    }

    /// True if a term with the type `t` is never a proof, where `t` is the codomain of a type after its Pi binders. A sort is a type of types. An application of an inductive type whose sort is never zero, and a free variable whose type is such a sort, are types that are not propositions.
    fn codomain_never_prop(&self, t: ExprId) -> bool {
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
        if let Some(x) = self.c_never_proof.get(c.0, 0) {
            return x == 1;
        }
        let slot = self.env.find(c);
        let r = if slot == 0 {
            false
        } else {
            let ty = self.env.at(slot).ty;
            let t = self.pi_codomain(ty);
            self.codomain_never_prop(t)
        };
        self.c_never_proof.put(c.0, 0, if r { 1 } else { 2 });
        r
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
    fn induct_type_not_prop(&self, t: ExprId) -> bool {
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
        match (self.va.get(a), self.va.get(b)) {
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
    fn glued_head(&self, v: ValueId) -> Option<(NameId, LevelListId, SpineId, Hints)> {
        match self.va.get(v) {
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
        match self.va.get(v) {
            Value::Glued(c, us, sp, s) => {
                let u = match self.glued_nat(c, us, sp, s) {
                    Some(n) => n,
                    None => self.unfold_glued(c, us, sp, s),
                };
                self.force_core(u)
            }
            _ => v,
        }
    }

    /// Lazy delta on glued heads (spec 05.4.4 step 5, A§1.8 step 5). It unfolds the side with the greater height, or both sides if the heights are equal. Before it unfolds two applications of the same regular definition, it compares the levels and the arguments.
    fn conv_lazy_delta(&mut self, a: ValueId, b: ValueId) -> (LBool, ValueId, ValueId) {
        let mut x = a;
        let mut y = b;
        let mut r = LBool::Undef;
        let mut done = false;
        while !done && !self.bad() {
            match (self.glued_head(x), self.glued_head(y)) {
                (None, None) => done = true,
                (Some(_), None) => x = self.conv_delta(x),
                (None, Some(_)) => y = self.conv_delta(y),
                (Some((c1, us1, sp1, h1)), Some((c2, us2, sp2, h2))) => {
                    let c = compare_hints(h1, h2);
                    if c < 0 {
                        x = self.conv_delta(x);
                    } else if c > 0 {
                        y = self.conv_delta(y);
                    } else {
                        let regular = matches!(h1, Hints::Regular(_));
                        if regular
                            && c1 == c2
                            && self.is_def_eq_levels(us1, us2)
                            && self.conv_spines(sp1, sp2)
                        {
                            r = LBool::True;
                            done = true;
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

    /// Two spines of the same length with equal arguments.
    fn conv_spines(&mut self, s1: SpineId, s2: SpineId) -> bool {
        if self.va.spine_len(s1) != self.va.spine_len(s2) {
            return false;
        }
        let a1 = self.va.spine_args(s1);
        let a2 = self.va.spine_args(s2);
        let mut ok = true;
        let mut i = 0;
        while ok && i < a1.len() {
            ok = self.conv(a1[i], a2[i]);
            i += 1;
        }
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

    /// The steps after lazy delta: the same head with equal arguments, then function eta.
    fn conv_whnf(&mut self, a: ValueId, b: ValueId) -> bool {
        match (self.va.get(a), self.va.get(b)) {
            (Value::Neu(h1, s1), Value::Neu(h2, s2)) => {
                self.conv_heads(h1, h2) && self.conv_spines(s1, s2)
            }
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
