//! Evaluation and read-back of engine F (spec 05.4.2 and 05.4.3).
//!
//! `eval` maps a stored term to a value of the arena (spec 04.5). It does beta and zeta, and it makes a glued value for each application of a definition or a theorem. `force` unfolds glued heads. `quote` reads a value back as a stored term, and a glued value reads back in its folded form.
//!
//! `force` does iota, the quotient rules and the `Nat` and `String` extensions too. K-like reduction and structure eta need the type of the major premise. For these two rules `force` reads the major premise back and uses engine R, as spec 10.4.1 says for the type-directed rules. Under a binder that `quote` opened, these two rules are not tried. A projection reduces when its structure forces to a constructor application, and it is stuck otherwise.
//!
//! Free variables of the local context keep their level. `quote` gives the free variables that it makes under a binder the levels from the length of the local context up, and it reads them back as bound variables.

use alloc::vec::Vec;
use rulean_store::{Expr, ExprId, LevelListId, Literal, NameId};

use crate::conv::{F_DELTA, F_TYPED};
use crate::env::ConstKind;
use crate::expr;
use crate::pin::{PIN_NAT, PIN_STRING};
use crate::tc::{Checker, ErrorKind};
use crate::value::{Closure, EnvId, Head, SlotId, SpineId, Value, ValueId};
use crate::whnf::find_rule;

impl Checker {
    /// A value to return after a fault. The caller must check `bad` before it uses the value.
    fn v_dummy(&mut self) -> ValueId {
        let z = self.st.level_zero();
        self.v_alloc(Value::Sort(z))
    }

    /// Adds a value. A full arena is a resource fault.
    fn v_alloc(&mut self, v: Value) -> ValueId {
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
            Expr::Const(n, us) => self.eval_const(n, us),
            Expr::App(f, a) => {
                let vf = self.eval(env, f);
                let va = self.eval(env, a);
                self.apply(vf, va, e)
            }
            Expr::Lam(b) => {
                let d = self.eval(env, b.dom);
                let clo = Closure { env, body: b.body };
                self.v_alloc(Value::Lam(b.name, b.info, d, clo))
            }
            Expr::Pi(b) => {
                let d = self.eval(env, b.dom);
                let clo = Closure { env, body: b.body };
                self.v_alloc(Value::Pi(b.name, b.info, d, clo))
            }
            Expr::Let(l) => {
                let v = self.eval(env, l.value);
                let env2 = self.env_push(env, v);
                self.eval(env2, l.body)
            }
            Expr::Lit(l) => self.v_alloc(Value::Lit(l)),
            Expr::Proj(p) => {
                let v = self.eval(env, p.expr);
                self.proj_value(p.struct_name, p.index, v)
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

    fn env_push(&mut self, env: EnvId, v: ValueId) -> EnvId {
        let r = self.va.env_push(env, v);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        r
    }

    fn v_neutral(&mut self, h: Head) -> ValueId {
        let r = self.va.neutral(h);
        if self.va.full() {
            self.fail(ErrorKind::ArenaFull, self.dummy);
        }
        r
    }

    /// A constant: glued if it has a value and the right number of levels (`is_delta`), neutral otherwise.
    fn eval_const(&mut self, n: NameId, us: LevelListId) -> ValueId {
        let e = self.st.mk_const(n, us);
        let r = if self.is_delta(e) != 0 {
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
        let args = self.va.spine_args(sp);
        let mut r = f;
        let mut i = 0;
        while i < args.len() && !self.bad() {
            r = self.apply(r, args[i], at);
            i += 1;
        }
        r
    }

    /// The unfolding of a glued value. It is computed once and kept in the slot of the value.
    pub(crate) fn unfold_glued(
        &mut self,
        c: NameId,
        us: LevelListId,
        sp: SpineId,
        s: SlotId,
    ) -> ValueId {
        match self.va.slot_get(s) {
            Some(u) => u,
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

    /// `force(v)`: reduces `v` until its head is not a redex: delta on glued heads, iota on recursors, the quotient rules and the `Nat` extension (spec 05.4.2). The result is in weak head normal form.
    pub fn force(&mut self, v0: ValueId) -> ValueId {
        let mut v = v0;
        let mut done = false;
        while !done && !self.bad() {
            match self.force_step(v) {
                Some(w) => v = w,
                None => done = true,
            }
        }
        v
    }

    /// `force` without delta: iota, the quotient rules and the `Nat` extension on heads that do not unfold (`whnf_core` of engine R). Engine F uses it in `conv`, so that lazy delta can compare two folded definitions before it unfolds them.
    pub(crate) fn force_core(&mut self, v0: ValueId) -> ValueId {
        let mut v = v0;
        let mut done = false;
        while !done && !self.bad() {
            let r = match self.va.get(v) {
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
                Some(w) => v = w,
                None => done = true,
            }
        }
        v
    }

    /// One step of `force`, or `None` if `v` is in weak head normal form. As in `whnf` of the official kernel, the `Nat` extension comes before delta.
    fn force_step(&mut self, v: ValueId) -> Option<ValueId> {
        match self.va.get(v) {
            Value::Glued(c, us, sp, s) => {
                let r = self.nat_value(c, us, sp);
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
            _ => None,
        }
    }

    /// The term of a `Nat` literal value, or of `Nat.zero` (`is_nat_lit_ext`).
    fn nat_lit_term(&mut self, w: ValueId) -> Option<ExprId> {
        match self.va.get(w) {
            Value::Lit(Literal::Nat(n)) => Some(self.st.mk_nat_lit(n)),
            Value::Neu(Head::Const(z, _), sp) => {
                if z == self.b.nat_zero && sp == SpineId::NIL {
                    Some(self.b.e_nat_zero)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// The `Nat` extension (spec 05.8): `Nat.succ` and the binary operations on two literals. The arguments are forced in engine F, and the operation is the one of engine R (`reduce_nat`).
    pub(crate) fn nat_value(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
        if !self.pin_on(PIN_NAT) || us != LevelListId(0) {
            return None;
        }
        let n = self.va.spine_len(sp);
        let f = self.st.mk_const(c, us);
        if n == 1 {
            if c != self.b.nat_succ {
                return None;
            }
        } else if n == 2 {
            if self.nat_op_index(f) >= self.b.nat_ops.len() {
                return None;
            }
        } else {
            return None;
        }
        let args = self.va.spine_args(sp);
        let mut terms: Vec<ExprId> = Vec::with_capacity(args.len());
        let mut i = 0;
        let mut ok = true;
        while ok && i < args.len() {
            let w = self.force(args[i]);
            match self.nat_lit_term(w) {
                Some(t) => terms.push(t),
                None => ok = false,
            }
            i += 1;
        }
        if !ok || self.bad() {
            return None;
        }
        let t = self.st.mk_apps(f, &terms);
        match self.reduce_nat(t) {
            Some(r) => Some(self.eval(EnvId::NIL, r)),
            None => None,
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
        let args = self.va.spine_args(sp);
        if args.len() <= mk_pos as usize {
            return None;
        }
        let mk = self.force(args[mk_pos as usize]);
        if self.bad() {
            return None;
        }
        let a = match self.va.get(mk) {
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
        let mut r = self.apply(args[3], a, at);
        let mut i = mk_pos as usize + 1;
        while i < args.len() && !self.bad() {
            r = self.apply(r, args[i], at);
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

    /// The major premise for structure eta (`to_cnstr_when_structure`). As `k_major`, it reads the value back and uses engine R.
    fn struct_major(&mut self, induct: NameId, major: ValueId) -> ValueId {
        if self.f_under > 0 {
            return major;
        }
        if let Value::Neu(Head::Const(c, _), _) = self.va.get(major) {
            if self.ctor_shape(c).is_some() {
                return major;
            }
        }
        let base = self.lctx_ty.len() as u32;
        let t = self.quote(base, base, major);
        let t2 = self.cnstr_when_structure(induct, t, false, false);
        if t2 == t || self.bad() {
            major
        } else {
            self.f_bits |= F_TYPED;
            self.eval(EnvId::NIL, t2)
        }
    }

    /// `inductive_reduce_rec` on values: a recursor whose major premise forces to a constructor application steps by the rule of the constructor. A `Nat` or a `String` literal is first made a constructor application.
    fn iota_value(&mut self, c: NameId, us: LevelListId, sp: SpineId) -> Option<ValueId> {
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
        let args = self.va.spine_args(sp);
        let major_idx = r.major_idx as usize;
        if major_idx >= args.len() {
            return None;
        }
        let induct = self.major_induct(slot, r.major_idx);
        let mut major = args[major_idx];
        if r.k {
            major = self.k_major(induct, r.nparams, major);
        }
        major = self.force(major);
        if self.bad() {
            return None;
        }
        major = match self.va.get(major) {
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
            _ => self.struct_major(induct, major),
        };
        if self.bad() {
            return None;
        }
        let (k, msp) = match self.va.get(major) {
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
        let margs = self.va.spine_args(msp);
        let nfields = rule.nfields as usize;
        if nfields > margs.len() {
            return None;
        }
        let ls = self.st.level_list_vec(us);
        let lps = self.const_lparams(slot);
        if ls.len() != lps.len() {
            return None;
        }
        let rhs = expr::instantiate_lparams(&mut self.st, &mut self.x, rule.rhs, &lps, &ls);
        let at = self.dummy;
        let mut f = self.eval(EnvId::NIL, rhs);
        let mut i = 0;
        while i < r.nprefix as usize && !self.bad() {
            f = self.apply(f, args[i], at);
            i += 1;
        }
        let mut j = margs.len() - nfields;
        while j < margs.len() && !self.bad() {
            f = self.apply(f, margs[j], at);
            j += 1;
        }
        let mut k2 = major_idx + 1;
        while k2 < args.len() && !self.bad() {
            f = self.apply(f, args[k2], at);
            k2 += 1;
        }
        Some(f)
    }

    /// The value of the projection `v.idx` of the structure `sname`. It reduces when `v` forces to an application of a constructor of `sname` with enough arguments. Otherwise it is a stuck projection.
    fn proj_value(&mut self, sname: NameId, idx: u32, v: ValueId) -> ValueId {
        let mut w = self.force(v);
        if self.bad() {
            return self.v_dummy();
        }
        if let Value::Lit(Literal::Str(s)) = self.va.get(w) {
            if self.pin_on(PIN_STRING) {
                let t = self.string_lit_to_constructor(s);
                let x = self.eval(EnvId::NIL, t);
                w = self.force(x);
            }
        }
        if let Value::Neu(Head::Const(c, _), sp) = self.va.get(w) {
            if let Some((induct, nparams, _)) = self.ctor_shape(c) {
                if induct == sname {
                    if let Some(a) = self.va.spine_arg(sp, nparams + idx) {
                        return a;
                    }
                }
            }
        }
        self.v_neutral(Head::Proj(sname, idx, v))
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
        match self.va.get(v) {
            Value::Sort(l) => self.st.mk_sort(l),
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
                    let ty = self.lctx_ty[lvl as usize];
                    self.st.mk_fvar(lvl, ty)
                } else if lvl < k {
                    self.st.mk_bvar(k - 1 - lvl)
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
        let args = self.va.spine_args(sp);
        let mut out: Vec<ExprId> = Vec::with_capacity(args.len());
        let mut i = 0;
        while i < args.len() {
            let t = self.quote(base, k, args[i]);
            out.push(t);
            i += 1;
        }
        self.st.mk_apps(f, &out)
    }
}
