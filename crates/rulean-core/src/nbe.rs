//! Evaluation and read-back of engine F (spec 05.4.2 and 05.4.3).
//!
//! `eval` maps a stored term to a value of the arena (spec 04.5). It does beta and zeta, and it makes a glued value for each application of a definition or a theorem. `force` unfolds glued heads. `quote` reads a value back as a stored term, and a glued value reads back in its folded form.
//!
//! `force` does iota, the quotient rules and the `Nat` and `String` extensions too. K-like reduction and structure eta need the type of the major premise. For these two rules `force` reads the major premise back and uses engine R, as spec 10.4.1 says for the type-directed rules. Under a binder that `quote` opened, these two rules are not tried. A projection reduces when its structure forces to a constructor application, and it is stuck otherwise.
//!
//! An argument of an application that is an application, a projection or a `let` is suspended (spec perf/04.3 A5). `vget` and `resolve` evaluate it at its first read and keep the value in its slot, so each other function sees only values in the forms of spec 05.4.1.
//!
//! Free variables of the local context keep their level. `quote` gives the free variables that it makes under a binder the levels from the length of the local context up, and it reads them back as bound variables.

use rulean_nat::Nat;
use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, Expr, ExprId, Kind, LevelListId, Literal, NameId, NatId};

use crate::conv::{F_DELTA, F_TYPED};
use crate::env::ConstKind;
use crate::expr;
use crate::pin::{PIN_NAT, PIN_STRING};
use crate::tc::{
    Checker, ErrorKind, NAT_ADD, NAT_BEQ, NAT_BLE, NAT_DIV, NAT_GCD, NAT_LAND, NAT_LOR, NAT_MOD,
    NAT_MUL, NAT_SHR, NAT_SUB, NAT_XOR,
};
use crate::trace::Rule;
use crate::value::{
    Closure, EnvId, Head, SMALL_NAT_LIMIT, SlotId, SpineId, Value, ValueId, small, small_get,
};
use crate::whnf::{RecShape, find_rule};

impl Checker {
    /// A value to return after a fault. The caller must check `bad` before it uses the value.
    pub(crate) fn v_dummy(&mut self) -> ValueId {
        let z = self.st.level_zero();
        self.v_alloc(Value::Sort(z))
    }

    /// Adds a value. A full arena is a resource fault.
    pub(crate) fn v_alloc(&mut self, v: Value) -> ValueId {
        let id = self.va.alloc(v);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        id
    }

    /// `eval(env, e)`: the value of the term `e` in the environment `env` (spec 05.4.2).
    pub fn eval(&mut self, env: EnvId, e: ExprId) -> ValueId {
        if !self.enter(e) {
            return self.v_dummy();
        }
        let r = self.eval_node(env, e);
        self.leave();
        r
    }

    fn eval_node(&mut self, env: EnvId, e: ExprId) -> ValueId {
        match self.st.node(e) {
            Expr::BVar(i) => match self.va.env_get(env, i) {
                Some(v) => v,
                None => {
                    self.fail(ErrorKind::LooseBVar, e);
                    self.v_dummy()
                }
            },
            Expr::Sort(l) => self.v_alloc(Value::Sort(l)),
            Expr::Const(n, us) => self.eval_const(e, n, us),
            Expr::App(f, a) => {
                let vf = self.eval(env, f);
                let va = self.eval_arg(env, a);
                self.apply(vf, va, e)
            }
            Expr::Lam(b) => {
                let d = self.eval_dom(env, b.dom);
                let clo = Closure { env, body: b.body };
                self.v_alloc(Value::Lam(b.name, b.info, d, clo))
            }
            Expr::Pi(b) => {
                let d = self.eval_dom(env, b.dom);
                let clo = Closure { env, body: b.body };
                self.v_alloc(Value::Pi(b.name, b.info, d, clo))
            }
            Expr::Let(l) => {
                let v = self.eval(env, l.value);
                let env2 = self.env_push(env, v);
                self.eval(env2, l.body)
            }
            Expr::Lit(l) => self.lit_value(l),
            Expr::Proj(p) => {
                let v = self.eval(env, p.expr);
                if self.cheap_proj {
                    self.proj_value_core(p.struct_name, p.index, v)
                } else {
                    self.proj_value(p.struct_name, p.index, v)
                }
            }
            Expr::FVar(lvl, ty) => match self.fvar_value(lvl) {
                Some(x) => self.eval(EnvId::NIL, x),
                None => {
                    let t = self.eval(EnvId::NIL, ty);
                    self.v_neutral(Head::FVar(lvl, t))
                }
            },
        }
    }

    /// The value of a literal. A `Nat` literal below `SMALL_NAT_LIMIT` becomes an inline number (spec perf/04.8).
    fn lit_value(&mut self, l: Literal) -> ValueId {
        if let Literal::Nat(id) = l {
            if let Nat::Small(x) = self.st.nat(id) {
                if *x < SMALL_NAT_LIMIT {
                    let v = small(*x);
                    return self.v_alloc(v);
                }
            }
        }
        self.v_alloc(Value::Lit(l))
    }

    /// The value of an argument `a` of an application (spec perf/04.3 A5). An application, a projection and a `let` become a suspended value, and the first read evaluates them. The other terms are cheap to evaluate, so they are evaluated now. Under a binder that `quote` opened, the argument is evaluated now too, because the read-back reads each argument, and because `force` skips the type-directed rules there (`f_under`) but not at a later read outside the binder.
    #[inline(always)]
    fn eval_arg(&mut self, env: EnvId, a: ExprId) -> ValueId {
        // The kind is in the handle, so this test reads no node.
        if self.f_under == 0 && matches!(a.kind(), Kind::App | Kind::Proj | Kind::Let) {
            let r = self.va.susp(env, a);
            if self.va.full() {
                self.fail(ErrorKind::ArenaFull, a);
            }
            r
        } else {
            self.eval(env, a)
        }
    }

    /// The value of the domain `d` of a binder. A domain that is not an atom becomes a suspended value, because most unfoldings apply the lambda and never read its domain. Under a binder that `quote` opened, the domain is evaluated now, for the reason that `eval_arg` gives.
    #[inline(always)]
    fn eval_dom(&mut self, env: EnvId, d: ExprId) -> ValueId {
        if self.f_under == 0
            && matches!(
                d.kind(),
                Kind::App | Kind::Proj | Kind::Let | Kind::Pi | Kind::Lam
            )
        {
            let r = self.va.susp(env, d);
            if self.va.full() {
                self.fail(ErrorKind::ArenaFull, d);
            }
            r
        } else {
            self.eval(env, d)
        }
    }

    /// `v`, with a suspended argument evaluated. The result is never of the form `Value::Susp`. The value of a suspended argument goes into its slot, and the bits of `f_bits` that the evaluation set go on the slot too. A later read of the slot sets these bits again, as a slot hit in `unfold_glued` sets `F_DELTA`, because the query that reads the value depends on the same steps.
    #[inline(always)]
    pub(crate) fn resolve(&mut self, v: ValueId) -> ValueId {
        match self.va.get(v) {
            Value::Susp(..) | Value::PiOpen(..) => self.resolve_susp(v),
            _ => v,
        }
    }

    /// The form of `v` after `resolve`. Engine F reads the form of a value only with this function, so that it never sees `Value::Susp`.
    #[inline(always)]
    pub(crate) fn vget(&mut self, v: ValueId) -> Value {
        match self.va.get(v) {
            Value::Susp(..) | Value::PiOpen(..) => {
                let w = self.resolve_susp(v);
                self.va.get(w)
            }
            x => x,
        }
    }

    /// The slow path of `resolve`: `v` is a suspended argument.
    #[inline(never)]
    fn resolve_susp(&mut self, v: ValueId) -> ValueId {
        let mut w = v;
        let mut done = false;
        while !done && !self.bad() {
            match self.va.get(w) {
                Value::Susp(env, e, s) => w = self.susp_value(env, e, s),
                Value::PiOpen(name, info, x, bt, s) => w = self.pi_open_value(name, info, x, bt, s),
                _ => done = true,
            }
        }
        w
    }

    /// The value of the suspended argument `e` in `env` with the slot `s`: the content of the slot, or else the evaluation, which then goes into the slot. After a fault the slot stays empty, and the caller must check `bad`.
    fn susp_value(&mut self, env: EnvId, e: ExprId, s: SlotId) -> ValueId {
        if let Some(x) = self.va.slot_get(s) {
            self.f_bits |= self.va.slot_bits(s);
            return x;
        }
        let saved = self.f_bits;
        self.f_bits = 0;
        let x = self.eval(env, e);
        let got = self.f_bits;
        self.f_bits = saved | got;
        if !self.bad() {
            self.va.slot_set(s, x);
            self.va.slot_set_bits(s, got);
        }
        x
    }

    /// The pi value of `Value::PiOpen` with the local `x` and the body type `bt`: the content of the slot, or else the read-back of `bt` as the body of a closure, which then goes into the slot. This is the value that engine F inference made for a lambda before this form.
    fn pi_open_value(
        &mut self,
        name: NameId,
        info: BinderInfo,
        x: ValueId,
        bt: ValueId,
        s: SlotId,
    ) -> ValueId {
        if let Some(w) = self.va.slot_get(s) {
            return w;
        }
        let (lvl, d) = match self.va.get(x) {
            Value::Neu(Head::FVar(l, d), _) => (l, d),
            _ => {
                self.fail(ErrorKind::Unsupported, self.dummy);
                return self.v_dummy();
            }
        };
        let body = self.quote(lvl, lvl + 1, bt);
        let clo = Closure {
            env: EnvId::NIL,
            body,
        };
        let w = self.v_alloc(Value::Pi(name, info, d, clo));
        if !self.bad() {
            self.va.slot_set(s, w);
        }
        w
    }

    pub(crate) fn env_push(&mut self, env: EnvId, v: ValueId) -> EnvId {
        let r = self.va.env_push(env, v);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        r
    }

    pub(crate) fn v_neutral(&mut self, h: Head) -> ValueId {
        let r = self.va.neutral(h);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        r
    }

    /// A constant: glued if it has a value and the right number of levels (`is_delta`), neutral otherwise. `e` is the constant node, so the step makes no new node in the store.
    fn eval_const(&mut self, e: ExprId, n: NameId, us: LevelListId) -> ValueId {
        let r = if self.is_delta_const(n, us) != 0 {
            self.va.glued(n, us)
        } else {
            self.va.neutral(Head::Const(n, us))
        };
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, e);
        }
        r
    }

    /// `apply(f, a)`: beta for a lambda, a longer spine for a neutral or a glued value. Other values are a "function expected" fault at `at`.
    pub fn apply(&mut self, f: ValueId, a: ValueId, at: ExprId) -> ValueId {
        if self.bad() {
            return self.v_dummy();
        }
        let f = self.resolve(f);
        match self.va.get(f) {
            Value::Lam(_, _, _, clo) => {
                let env2 = self.env_push(clo.env, a);
                self.eval(env2, clo.body)
            }
            _ => match self.va.apply_stuck(f, a) {
                Some(v) => {
                    if self.va.full() {
                        self.fail(ErrorKind::ArenaFull, at);
                    }
                    v
                }
                None => {
                    self.fail(ErrorKind::FunctionExpected, at);
                    self.v_dummy()
                }
            },
        }
    }

    /// `f` applied to each argument of the spine `sp`, first argument first.
    fn apply_spine(&mut self, f: ValueId, sp: SpineId, at: ExprId) -> ValueId {
        let b = self.vstk.len();
        let n = self.va.spine_push_args(sp, &mut self.vstk);
        let mut r = f;
        let mut i = 0;
        while i < n && !self.bad() {
            let a = self.vstk[b + i];
            r = self.apply(r, a, at);
            i += 1;
        }
        self.vstk.truncate(b);
        r
    }

    /// The unfolding of a glued value. It is computed once and kept in the slot of the value.
    ///
    /// A slot lives until the arena is cleared, so a later query can use an unfolding that an earlier query computed. The unfolding is a delta step of the later query too, so a slot hit also sets `F_DELTA`. Without this, the later query can use a delta step and a type-directed rule, and engine R does not confirm it (the confirm set of spec 05.1).
    pub(crate) fn unfold_glued(
        &mut self,
        c: NameId,
        us: LevelListId,
        sp: SpineId,
        s: SlotId,
    ) -> ValueId {
        match self.va.slot_get(s) {
            Some(u) => {
                self.f_bits |= F_DELTA;
                u
            }
            None => {
                let e = self.st.mk_const(c, us);
                let body = match self.unfold_definition_core(e) {
                    Some(b) => b,
                    None => {
                        self.fail(ErrorKind::BadConst, e);
                        return self.v_dummy();
                    }
                };
                self.f_bits |= F_DELTA;
                let h = self.eval(EnvId::NIL, body);
                let u = self.apply_spine(h, sp, e);
                if !self.bad() {
                    self.va.slot_set(s, u);
                }
                u
            }
        }
    }

    /// `force(v)`: reduces `v` until its head is not a redex: delta on glued heads, iota on recursors, projections of structures that reduce to a constructor, the quotient rules and the `Nat` extension (spec 05.4.2). The result is in weak head normal form.
    ///
    /// The result goes into the cache `c_force`. A neutral application of a recursor has no slot, and without the cache each `force` of the same value does the iota steps again. For example, `N.add (ldepth2 l) 1` with `N.add` by recursion on its first argument forces the value below it once for each level above it, and the time is quadratic in the depth.
    ///
    /// The bits of `f_bits` that the steps set go into `c_force` at key (value, 2). A cache hit sets these bits again, because the cache lives across the queries of a declaration, and the query that has the hit depends on the same steps.
    pub fn force(&mut self, v0: ValueId) -> ValueId {
        let v0 = self.resolve(v0);
        let cached = self.force_cached(v0);
        if cached {
            if let Some(w) = self.c_force.get(raw(v0.0), 0) {
                self.force_bits(v0, 2);
                return ValueId(low(w));
            }
        }
        let saved = self.f_bits;
        let cheap = self.cheap_proj;
        self.f_bits = 0;
        self.cheap_proj = false;
        let mut v = v0;
        let mut done = false;
        while !done && !self.bad() {
            match self.force_step(v) {
                Some(w) => v = self.resolve(w),
                None => done = true,
            }
        }
        self.cheap_proj = cheap;
        let got = self.f_bits;
        self.f_bits = saved | got;
        if cached && !self.bad() {
            self.c_force.put(raw(v0.0), 0, raw(v.0));
            self.c_force.put(raw(v0.0), 2, raw(got));
        }
        v
    }

    /// Sets the bits of `f_bits` that `c_force` keeps for `v` at key (v, `k`).
    fn force_bits(&mut self, v: ValueId, k: u32) {
        if let Some(b) = self.c_force.get(raw(v.0), raw(k)) {
            self.f_bits |= low(b);
        }
    }

    /// True if `force` and `force_core` keep the result of `v` in `c_force`: a glued value, a neutral application of a constant, or a neutral projection. The other values are already in weak head normal form.
    fn force_cached(&mut self, v: ValueId) -> bool {
        matches!(
            self.vget(v),
            Value::Glued(..) | Value::Neu(Head::Const(..) | Head::Proj(..), _)
        )
    }

    /// `force` without delta: iota, the quotient rules and the `Nat` extension on heads that do not unfold (`whnf_core` of engine R). Engine F uses it in `conv`, so that lazy delta can compare two folded definitions before it unfolds them. As in `force`, the bits of the steps go into `c_force`, here at key (value, 3).
    pub(crate) fn force_core(&mut self, v0: ValueId) -> ValueId {
        let v0 = self.resolve(v0);
        let cached = matches!(self.vget(v0), Value::Neu(Head::Const(..), _));
        if cached {
            if let Some(w) = self.c_force.get(raw(v0.0), 1) {
                self.force_bits(v0, 3);
                return ValueId(low(w));
            }
        }
        let saved = self.f_bits;
        self.f_bits = 0;
        let mut v = v0;
        let mut done = false;
        while !done && !self.bad() {
            let r = match self.vget(v) {
                Value::Neu(Head::Const(c, us), sp) => {
                    let n = self.nat_value(c, us, sp);
                    if n.is_some() || self.bad() {
                        n
                    } else {
                        self.iota_value(c, us, sp)
                    }
                }
                _ => None,
            };
            match r {
                Some(w) => v = self.resolve(w),
                None => done = true,
            }
        }
        let got = self.f_bits;
        self.f_bits = saved | got;
        if cached && !self.bad() {
            self.c_force.put(raw(v0.0), 1, raw(v.0));
            self.c_force.put(raw(v0.0), 3, raw(got));
        }
        v
    }

    /// One step of `force`, or `None` if `v` is in weak head normal form. As in `whnf` of the official kernel, the `Nat` extension comes before delta.
    fn force_step(&mut self, v: ValueId) -> Option<ValueId> {
        match self.vget(v) {
            Value::Glued(c, us, sp, s) => {
                let r = self.glued_nat(c, us, sp, s);
                if r.is_some() || self.bad() {
                    return r;
                }
                Some(self.unfold_glued(c, us, sp, s))
            }
            Value::Neu(Head::Const(c, us), sp) => {
                let r = self.nat_value(c, us, sp);
                if r.is_some() || self.bad() {
                    return r;
                }
                self.iota_value(c, us, sp)
            }
            Value::Neu(Head::Proj(..), _) => {
                let w = self.proj_unfold(v);
                if w == v { None } else { Some(w) }
            }
            _ => None,
        }
    }

    /// The content of the slot of a glued value, or else the `Nat` extension on it. The result of the `Nat` extension goes into the slot, so that the next `force` of the same value does not compute it again. Without this, each `force` of `Nat.mod (Nat.mul a b) 3` computes the product again, and on a term with shared subterms the time grows with each level. The slot then holds a literal and not the unfolding of the definition. Both are values of the same term, and the `Nat` extension is tried before delta at each place, so the answer does not change. A slot hit sets `F_DELTA`, because the slot can hold an unfolding that an earlier query computed (see `unfold_glued`). If the slot holds a literal, the bit is not necessary, but it only makes engine R confirm more answers.
    pub(crate) fn glued_nat(
        &mut self,
        c: NameId,
        us: LevelListId,
        sp: SpineId,
        s: SlotId,
    ) -> Option<ValueId> {
        if let Some(u) = self.va.slot_get(s) {
            self.f_bits |= F_DELTA;
            return Some(u);
        }
        let r = self.nat_value(c, us, sp);
        if let Some(n) = r {
            if !self.bad() {
                self.va.slot_set(s, n);
            }
        }
        r
    }

    /// The `Nat` extension (spec 05.8): `Nat.succ` and the binary operations on two literals. The arguments are forced in engine F, and the operation is the one of engine R (`reduce_nat`).
    pub(crate) fn nat_value(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
        let r = self.nat_value_body(c, us, sp);
        if r.is_some() {
            self.note(Rule::Nat, c);
        }
        r
    }

    /// The body of `nat_value`. The arguments are forced, and the operation reads the literals of the values. It makes no term for the application, so a fault has the dummy term, and engine R does the query again with the real term.
    fn nat_value_body(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
        if !self.pin_on(PIN_NAT) || us != LevelListId(0) {
            return None;
        }
        let n = self.va.spine_len(sp);
        let mut op = self.b.nat_op_names.len();
        if n == 1 {
            if c != self.b.nat_succ {
                return None;
            }
        } else if n == 2 {
            op = self.nat_op_name_index(c);
            if op >= self.b.nat_op_names.len() || !self.pin_on(1 << op) {
                return None;
            }
        } else {
            return None;
        }
        let b = self.vstk.len();
        let len = self.va.spine_push_args(sp, &mut self.vstk);
        let mut lits: [NatV; 2] = [NatV::Small(0), NatV::Small(0)];
        let mut i = 0;
        let mut ok = true;
        while ok && i < len {
            let a = self.vstk[b + i];
            let w = self.force(a);
            match self.nat_lit_of_value(w) {
                Some(x) => lits[i] = x,
                None => ok = false,
            }
            i += 1;
        }
        self.vstk.truncate(b);
        if !ok || self.bad() {
            return None;
        }
        // An inline number has 8 bytes, so the size check of `sized` passes when `nat_max` is at least 8.
        if self.nat_max >= 8 {
            if let (NatV::Small(x), NatV::Small(y)) = (lits[0], lits[1]) {
                let fast = if n == 1 {
                    Some(SmallOut::Num(x + 1))
                } else {
                    small_op(op, x, y)
                };
                if let Some(out) = fast {
                    return Some(self.small_out(out));
                }
            }
        }
        let n1 = self.nat_handle(lits[0]);
        let n2 = self.nat_handle(lits[1]);
        let d = self.dummy;
        let r = if n == 1 {
            let zero = Nat::zero();
            let v = self.nat_ref(n1, &zero).succ();
            self.sized(d, v)
        } else {
            self.nat_bin(d, op, n1, n2)
        };
        match r {
            Some(t) if !self.bad() => Some(self.eval(EnvId::NIL, t)),
            _ => None,
        }
    }

    /// The value of a result of `small_op`.
    fn small_out(&mut self, out: SmallOut) -> ValueId {
        match out {
            SmallOut::Num(r) if r < SMALL_NAT_LIMIT => self.v_alloc(small(r)),
            SmallOut::Num(r) => {
                let id = self.st.intern_nat(Nat::from_u64(r));
                self.v_alloc(Value::Lit(Literal::Nat(id)))
            }
            SmallOut::Bool(true) => self.eval(EnvId::NIL, self.b.e_bool_true),
            SmallOut::Bool(false) => self.eval(EnvId::NIL, self.b.e_bool_false),
        }
    }

    /// The handle of a literal of `nat_lit_of_value` for the operations of engine R, with `None` for zero.
    fn nat_handle(&mut self, x: NatV) -> Option<NatId> {
        match x {
            NatV::Small(0) => None,
            NatV::Small(v) => Some(self.st.intern_nat(Nat::from_u64(v))),
            NatV::Big(id) => Some(id),
        }
    }

    /// True if `v` is a glued application of a binary `Nat` operation that waits (row O10 of spec 05.7.3): the slot is empty, and an argument is a glued value or a neutral projection, so the `Nat` extension must unfold that argument to get a literal. The check reads the arguments and evaluates none of them. A suspended argument waits when its term is an application of a constant or a projection.
    pub(crate) fn nat_waits(&mut self, v: ValueId) -> bool {
        let (c, us, sp, s) = match self.vget(v) {
            Value::Glued(c, us, sp, s) => (c, us, sp, s),
            _ => return false,
        };
        if !self.pin_on(PIN_NAT) || us != LevelListId(0) || self.va.spine_len(sp) != 2 {
            return false;
        }
        let op = self.nat_op_name_index(c);
        if op >= self.b.nat_op_names.len() || self.va.slot_get(s).is_some() {
            return false;
        }
        let a0 = self.va.spine_arg(sp, 0);
        let a1 = self.va.spine_arg(sp, 1);
        let w0 = self.nat_arg_waits(a0);
        let w1 = self.nat_arg_waits(a1);
        w0 | w1
    }

    /// True if the argument `a` of a `Nat` operation is not a literal without delta (see `nat_waits`).
    fn nat_arg_waits(&mut self, a: Option<ValueId>) -> bool {
        match a {
            Some(x) => match self.va.get(x) {
                Value::Glued(..) | Value::Neu(Head::Proj(..), _) => true,
                Value::Susp(_, t, _) => matches!(
                    self.st.node(expr::app_fn(&self.st, t)),
                    Expr::Const(..) | Expr::Proj(..)
                ),
                _ => false,
            },
            None => false,
        }
    }

    /// The index of the binary `Nat` operation with the name `c` in `nat_op_names`, or the length of the table.
    pub(crate) fn nat_op_name_index(&self, c: NameId) -> usize {
        let names = &self.b.nat_op_names;
        let mut i = 0;
        while i < names.len() && names[i] != c {
            i += 1;
        }
        i
    }

    /// The literal of a value in weak head normal form, as in `nat_lit_id` of engine R. `Nat.zero` is the inline number 0. Any other value gives `None`.
    fn nat_lit_of_value(&mut self, w: ValueId) -> Option<NatV> {
        match self.vget(w) {
            Value::Small(lo, hi) => Some(NatV::Small(small_get(lo, hi))),
            Value::Lit(Literal::Nat(n)) => Some(NatV::Big(n)),
            Value::Neu(Head::Const(z, _), sp) if z == self.b.nat_zero && sp == SpineId::NIL => {
                Some(NatV::Small(0))
            }
            _ => None,
        }
    }

    /// `quot_reduce_rec` on values: `Quot.lift f h (Quot.mk r a)` is `f a`, and `Quot.ind h (Quot.mk r a)` is `h a`.
    fn quot_value(&mut self, c: NameId, sp: SpineId) -> Option<ValueId> {
        let mk_pos: u32 = if c == self.b.quot_lift {
            5
        } else if c == self.b.quot_ind {
            4
        } else {
            return None;
        };
        let b = self.vstk.len();
        let n = self.va.spine_push_args(sp, &mut self.vstk);
        let r = self.quot_value_args(mk_pos as usize, b, n);
        self.vstk.truncate(b);
        r
    }

    /// The body of `quot_value`, with the `n` arguments of the spine on `vstk` from index `b`.
    fn quot_value_args(&mut self, mk_pos: usize, b: usize, n: usize) -> Option<ValueId> {
        if n <= mk_pos {
            return None;
        }
        let m0 = self.vstk[b + mk_pos];
        let mk = self.force(m0);
        if self.bad() {
            return None;
        }
        let a = match self.vget(mk) {
            Value::Neu(Head::Const(m, _), msp) => {
                if m != self.b.quot_mk || self.va.spine_len(msp) != 3 {
                    return None;
                }
                match self.va.spine_arg(msp, 2) {
                    Some(a) => a,
                    None => return None,
                }
            }
            _ => return None,
        };
        let at = self.dummy;
        let f = self.vstk[b + 3];
        let mut r = self.apply(f, a, at);
        let mut i = mk_pos + 1;
        while i < n && !self.bad() {
            let x = self.vstk[b + i];
            r = self.apply(r, x, at);
            i += 1;
        }
        Some(r)
    }

    /// The major premise for K-like reduction (`to_cnstr_when_K`). The rule needs the type of the major premise, so it reads the value back and uses engine R. Under a binder that `quote` opened, the free variable has no entry in the local context, so the major premise stays as it is.
    fn k_major(&mut self, induct: NameId, nparams: u32, major: ValueId) -> ValueId {
        if self.f_under > 0 {
            return major;
        }
        let base = self.lctx_ty.len() as u32;
        let t = self.quote(base, base, major);
        let t2 = self.cnstr_when_k(induct, nparams, t, false, false);
        if t2 == t || self.bad() {
            major
        } else {
            self.f_bits |= F_TYPED;
            self.eval(EnvId::NIL, t2)
        }
    }

    /// True if the type of the major premise of the recursor of the slot is an inductive type that is never in `Prop`.
    fn major_not_prop(&mut self, slot: u32, major_idx: u32) -> bool {
        let mut t = self.env.at(slot).ty;
        let mut i = 0;
        while i < major_idx {
            if let Expr::Pi(b) = self.st.node(t) {
                t = b.body;
                i += 1;
            } else {
                i = major_idx;
            }
        }
        match self.st.node(t) {
            Expr::Pi(b) => self.induct_type_not_prop(b.dom),
            _ => false,
        }
    }

    /// The inline number `x` as a constructor application, as `nat_lit_to_constructor` of engine R: `Nat.zero`, or `Nat.succ` of the inline number `x - 1`. It makes no term.
    fn small_to_constructor(&mut self, x: u64) -> ValueId {
        if x == 0 {
            return self.eval(EnvId::NIL, self.b.e_nat_zero);
        }
        let f = self.eval(EnvId::NIL, self.b.e_nat_succ);
        let a = self.v_alloc(small(x - 1));
        self.apply(f, a, self.b.e_nat_succ)
    }
    /// The major premise for structure eta (`to_cnstr_when_structure`). As `k_major`, it reads the value back and uses engine R.
    fn struct_major(&mut self, rec_slot: u32, induct: NameId, major: ValueId) -> ValueId {
        if self.f_under > 0 {
            return major;
        }
        if let Value::Neu(Head::Const(c, _), _) = self.vget(major) {
            if self.ctor_shape(c).is_some() {
                return major;
            }
        }
        // `cnstr_when_structure` gives the term back when the type is not a structure without recursion and indices. Then the read-back is not necessary. A type that is not in the environment goes on, so that the fault stays the same.
        let s = self.env.find(induct);
        if s != 0 {
            // The three tests use `&` and not `&&`: Aeneas cannot join the contexts of the branches of `&&` while the match holds a borrow of the environment.
            let structure = match &self.env.at(s).kind {
                ConstKind::Induct(i) => {
                    let one = i.ctors.len() == 1;
                    let flat = i.nindices == 0;
                    let plain = !i.is_rec;
                    one & flat & plain
                }
                _ => false,
            };
            if !structure {
                return major;
            }
        }
        let base = self.lctx_ty.len() as u32;
        let t = self.quote(base, base, major);
        let t2 = self.cnstr_when_structure(rec_slot, induct, t, false, false);
        if t2 == t || self.bad() {
            major
        } else {
            self.f_bits |= F_TYPED;
            self.eval(EnvId::NIL, t2)
        }
    }

    /// `inductive_reduce_rec` on values: a recursor whose major premise forces to a constructor application steps by the rule of the constructor. A `Nat` or a `String` literal is first made a constructor application.
    fn iota_value(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
        let r = self.iota_value_body(c, us, sp);
        if r.is_some() {
            let rule = if c == self.b.quot_lift || c == self.b.quot_ind {
                Rule::Quot
            } else {
                Rule::Iota
            };
            self.note(rule, c);
        }
        r
    }

    fn iota_value_body(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
        let slot = self.env.find(c);
        if slot == 0 {
            return None;
        }
        if self.env.quot_initialized() && (c == self.b.quot_lift || c == self.b.quot_ind) {
            return self.quot_value(c, sp);
        }
        let r = match self.rec_shape(slot) {
            Some(r) => r,
            None => return None,
        };
        let b = self.vstk.len();
        let n = self.va.spine_push_args(sp, &mut self.vstk);
        let res = self.iota_value_args(slot, us, r, b, n);
        self.vstk.truncate(b);
        res
    }

    /// The body of `iota_value`, with the `n` arguments of the spine on `vstk` from index `b`. The fields of the major premise go on `vstk` above them, and the caller removes both.
    fn iota_value_args(
        &mut self,
        slot: u32,
        us: LevelListId,
        r: RecShape,
        b: usize,
        n: usize,
    ) -> Option<ValueId> {
        let major_idx = r.major_idx as usize;
        if major_idx >= n {
            return None;
        }
        let induct = self.major_induct(slot, r.major_idx);
        let mut major = self.vstk[b + major_idx];
        let first = major;
        if r.k {
            major = self.k_major(induct, r.nparams, major);
        }
        // With `no_whnf_prop_major` (lean4#15371), engine R does not reduce a major premise that is a proof. A value of engine F is already evaluated, so engine F cannot follow this rule. If the type of the major premise can be in `Prop` and K did not give a constructor, engine R must decide the query.
        if self.flags.no_whnf_prop_major
            && major == first
            && !self.major_not_prop(slot, r.major_idx)
        {
            self.fail(ErrorKind::FDefer, self.dummy);
            return None;
        }
        major = self.force(major);
        if self.bad() {
            return None;
        }
        major = match self.vget(major) {
            Value::Small(lo, hi) if self.pin_on(PIN_NAT) => {
                self.small_to_constructor(small_get(lo, hi))
            }
            Value::Lit(Literal::Nat(n)) if self.pin_on(PIN_NAT) => {
                let v = self.st.nat(n).clone();
                let t = self.nat_lit_to_constructor(&v);
                self.eval(EnvId::NIL, t)
            }
            Value::Lit(Literal::Str(s)) if self.pin_on(PIN_STRING) => {
                let t = self.string_lit_to_constructor(s);
                let w = self.eval(EnvId::NIL, t);
                self.force(w)
            }
            _ => self.struct_major(slot, induct, major),
        };
        if self.bad() {
            return None;
        }
        let (k, msp) = match self.vget(major) {
            Value::Neu(Head::Const(k, _), msp) => (k, msp),
            _ => return None,
        };
        let rule = match &self.env.at(slot).kind {
            ConstKind::Rec(info) => match find_rule(&info.rules, k) {
                Some(x) => x,
                None => return None,
            },
            _ => return None,
        };
        let mb = self.vstk.len();
        let mn = self.va.spine_push_args(msp, &mut self.vstk);
        let nfields = rule.nfields as usize;
        if nfields > mn {
            return None;
        }
        if self.st.level_list_items(us).len() != self.env.at(slot).lparams.len() {
            return None;
        }
        let rhs = self.inst_lps_cached(slot, rule.rhs, us);
        let at = self.dummy;
        let mut f = self.eval(EnvId::NIL, rhs);
        let mut i = 0;
        while i < r.nprefix as usize && !self.bad() {
            let x = self.vstk[b + i];
            f = self.apply(f, x, at);
            i += 1;
        }
        let mut j = mn - nfields;
        while j < mn && !self.bad() {
            let x = self.vstk[mb + j];
            f = self.apply(f, x, at);
            j += 1;
        }
        let mut k2 = major_idx + 1;
        while k2 < n && !self.bad() {
            let x = self.vstk[b + k2];
            f = self.apply(f, x, at);
            k2 += 1;
        }
        Some(f)
    }

    /// The value of the projection `v.idx` of the structure `sname`. It reduces when `v` forces to an application of a constructor of `sname` with enough arguments. Otherwise it is a stuck projection.
    pub(crate) fn proj_value(&mut self, sname: NameId, idx: u32, v: ValueId) -> ValueId {
        match self.proj_reduce(sname, idx, v) {
            Some(a) => a,
            None => {
                if self.bad() {
                    return self.v_dummy();
                }
                self.v_neutral(Head::Proj(sname, idx, v))
            }
        }
    }

    /// The value of the term `e.idx`, where `v` is the value of `e`. As `whnf_core` with cheap projections in `is_def_eq` of the official kernel, the structure is reduced without delta (`force_core`). If it is then not an application of a constructor, the result is a neutral projection that keeps `v`. A neutral projection of a folded structure is not in weak head normal form: `force` and `conv` reduce it later (`proj_unfold`).
    ///
    /// Without this, each unfolding of a projection function such as `S.fn (gC slowA c) x` unfolds `gC` at once. In `perf/proj-applied-struct`, `gC` decides `slowA = c` with `slowA` a long computation, and engine F filled its arena on each of the three theorems. The official kernel compares `gC slowA c` and `gC' slowA c` first, and they are equal after one delta step.
    fn proj_value_core(&mut self, sname: NameId, idx: u32, v: ValueId) -> ValueId {
        let w = self.force_core(v);
        if self.bad() {
            return self.v_dummy();
        }
        match self.proj_ctor(sname, idx, w) {
            Some(a) => a,
            None => {
                if self.bad() {
                    return self.v_dummy();
                }
                self.v_neutral(Head::Proj(sname, idx, v))
            }
        }
    }

    /// The field `idx` of `v` after `force`, or `None` if the projection is stuck.
    fn proj_reduce(&mut self, sname: NameId, idx: u32, v: ValueId) -> Option<ValueId> {
        let w = self.force(v);
        if self.bad() {
            return None;
        }
        self.proj_ctor(sname, idx, w)
    }

    /// The field `idx` of `w`, if `w` is an application of a constructor of `sname` with enough arguments, or a string literal and `sname` is `String`.
    fn proj_ctor(&mut self, sname: NameId, idx: u32, w0: ValueId) -> Option<ValueId> {
        let mut w = w0;
        if let Value::Lit(Literal::Str(s)) = self.vget(w) {
            if self.pin_on(PIN_STRING) {
                let t = self.string_lit_to_constructor(s);
                let x = self.eval(EnvId::NIL, t);
                w = self.force(x);
            }
        }
        if let Value::Neu(Head::Const(c, _), sp) = self.vget(w) {
            if let Some((induct, nparams, _)) = self.ctor_shape(c) {
                if induct == sname {
                    return self.va.spine_arg(sp, nparams + idx);
                }
            }
        }
        None
    }

    /// `v` with its head projection reduced, if `v` is a neutral projection that reduces after `force` of its structure. Other values do not change. The arguments of the spine are applied to the field.
    ///
    /// The result goes into `c_force` at key (v, 4), and the bits of `f_bits` of the step at key (v, 5). Conversion can meet the same neutral projection in many queries. Without the cache, each call applies the spine again and makes new values, so the caches of conversion, whose keys are values, do not find the earlier answers. On Init, engine F then filled its arena on 89 more declarations, most of them proofs by `omega`.
    pub(crate) fn proj_unfold(&mut self, v: ValueId) -> ValueId {
        let (s, i, x, sp) = match self.vget(v) {
            Value::Neu(Head::Proj(s, i, x), sp) => (s, i, x, sp),
            _ => return v,
        };
        if let Some(w) = self.c_force.get(raw(v.0), 4) {
            self.force_bits(v, 5);
            return ValueId(low(w));
        }
        let saved = self.f_bits;
        self.f_bits = 0;
        let w = match self.proj_reduce(s, i, x) {
            Some(a) => self.apply_spine(a, sp, self.dummy),
            None => v,
        };
        let got = self.f_bits;
        self.f_bits = saved | got;
        if !self.bad() {
            self.c_force.put(raw(v.0), 4, raw(w.0));
            self.c_force.put(raw(v.0), 5, raw(got));
        }
        w
    }

    /// The value of `e` in the local context, read back as a term. It is the beta and zeta normal form of `e`, with each definition in folded form.
    pub fn read_back(&mut self, e: ExprId) -> ExprId {
        let base = self.lctx_ty.len() as u32;
        let v = self.eval(EnvId::NIL, e);
        self.quote(base, base, v)
    }

    /// `quote(k, v)`: the term of `v` at binder depth `k` (spec 05.4.3). Free variables with a level below `base` are in the local context. The others were made by `quote` and read back as bound variables.
    pub fn quote(&mut self, base: u32, k: u32, v: ValueId) -> ExprId {
        if !self.enter(self.dummy) {
            return self.dummy;
        }
        let r = self.quote_node(base, k, v);
        self.leave();
        r
    }

    fn quote_node(&mut self, base: u32, k: u32, v: ValueId) -> ExprId {
        // A suspended argument with no loose bound variable reads back as its term (spec perf/04.3 A1). The environment cannot change the value of such a term, and the term is in the store already, so the read-back makes no new term.
        let x = match self.va.get(v) {
            Value::Susp(_, t, _) if self.st.loose_range(t) == 0 => {
                return t;
            }
            Value::Susp(..) | Value::PiOpen(..) => {
                let w = self.resolve_susp(v);
                self.va.get(w)
            }
            x => x,
        };
        match x {
            Value::Sort(l) => self.st.mk_sort(l),
            Value::Small(lo, hi) => self.mk_nat(Nat::from_u64(small_get(lo, hi))),
            Value::Lit(Literal::Nat(n)) => self.st.mk_nat_lit(n),
            Value::Lit(Literal::Str(s)) => self.st.mk_str_lit(s),
            Value::Lam(name, info, d, clo) => {
                let td = self.quote(base, k, d);
                let tb = self.quote_body(base, k, d, clo);
                self.st.mk_lam(name, info, td, tb)
            }
            Value::Pi(name, info, d, clo) => {
                let td = self.quote(base, k, d);
                let tb = self.quote_body(base, k, d, clo);
                self.st.mk_pi(name, info, td, tb)
            }
            Value::Neu(h, sp) => {
                let f = self.quote_head(base, k, h);
                self.quote_spine(base, k, f, sp)
            }
            Value::Glued(c, us, sp, _) => {
                let f = self.st.mk_const(c, us);
                self.quote_spine(base, k, f, sp)
            }
            // `vget` never gives these forms.
            Value::Susp(..) | Value::PiOpen(..) => self.fail(ErrorKind::Unsupported, self.dummy),
        }
    }

    /// The body of a closure, read back under a new free variable of level `k` and type `d`.
    fn quote_body(&mut self, base: u32, k: u32, d: ValueId, clo: Closure) -> ExprId {
        let x = self.v_neutral(Head::FVar(k, d));
        let env2 = self.env_push(clo.env, x);
        self.f_under += 1;
        let b = self.eval(env2, clo.body);
        let r = self.quote(base, k + 1, b);
        self.f_under -= 1;
        r
    }

    fn quote_head(&mut self, base: u32, k: u32, h: Head) -> ExprId {
        match h {
            Head::FVar(lvl, _) => {
                if lvl < base {
                    self.lctx_fv[lvl as usize]
                } else if lvl < k {
                    self.st.mk_bvar(k - 1 - lvl)
                } else if lvl >= expr::FAR_FVAR {
                    expr::far_fvar(&mut self.st, lvl - expr::FAR_FVAR)
                } else {
                    self.fail(ErrorKind::UnknownFVar, self.dummy)
                }
            }
            Head::Const(n, us) => self.st.mk_const(n, us),
            Head::Proj(s, i, x) => {
                let t = self.quote(base, k, x);
                self.st.mk_proj(s, i, t)
            }
        }
    }

    fn quote_spine(&mut self, base: u32, k: u32, f: ExprId, sp: SpineId) -> ExprId {
        let b = self.vstk.len();
        let n = self.va.spine_push_args(sp, &mut self.vstk);
        let mut r = f;
        let mut i = 0;
        while i < n {
            let a = self.vstk[b + i];
            let t = self.quote(base, k, a);
            r = self.st.mk_app(r, t);
            i += 1;
        }
        self.vstk.truncate(b);
        r
    }
}

/// A literal argument of the `Nat` extension of engine F: an inline number, or the handle of a literal of at least `SMALL_NAT_LIMIT`.
#[derive(Clone, Copy)]
enum NatV {
    Small(u64),
    Big(NatId),
}

/// A result of `small_op`.
enum SmallOut {
    Num(u64),
    Bool(bool),
}

/// The binary operation `op` of `reduce_nat` on two inline numbers below `SMALL_NAT_LIMIT`, with machine arithmetic. It gives `None` when the result does not fit in a `u64`, and for `Nat.pow` and `Nat.shiftLeft`, which check a count first. Then the operation of engine R computes the result. The rules are the rules of `Nat`: `x - y` is 0 when `y > x`, `x / 0` is 0 and `x % 0` is `x`.
fn small_op(op: usize, x: u64, y: u64) -> Option<SmallOut> {
    match op {
        NAT_ADD => Some(SmallOut::Num(x + y)),
        NAT_SUB => Some(SmallOut::Num(x.saturating_sub(y))),
        NAT_MUL => x.checked_mul(y).map(SmallOut::Num),
        NAT_GCD => Some(SmallOut::Num(gcd(x, y))),
        NAT_MOD => Some(SmallOut::Num(if y == 0 { x } else { x % y })),
        NAT_DIV => Some(SmallOut::Num(x.checked_div(y).unwrap_or(0))),
        NAT_BEQ => Some(SmallOut::Bool(x == y)),
        NAT_BLE => Some(SmallOut::Bool(x <= y)),
        NAT_LAND => Some(SmallOut::Num(x & y)),
        NAT_LOR => Some(SmallOut::Num(x | y)),
        NAT_XOR => Some(SmallOut::Num(x ^ y)),
        NAT_SHR => Some(SmallOut::Num(if y >= 64 { 0 } else { x >> y })),
        _ => None,
    }
}

/// The greatest common divisor, with `gcd(0, y) = y`.
fn gcd(x: u64, y: u64) -> u64 {
    let mut a = x;
    let mut b = y;
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
