//! Evaluation and read-back of engine F (spec 05.4.2 and 05.4.3).
//!
//! `eval` maps a stored term to a value of the arena (spec 04.5). It does beta and zeta, and it makes a glued value for each application of a definition or a theorem. `force` unfolds glued heads. `quote` reads a value back as a stored term, and a glued value reads back in its folded form.
//!
//! This version has no iota, no quotient rules and no `Nat` or `String` extensions. A recursor application, a quotient constant and a literal stay as values. They come in a later PR. A projection reduces when its structure forces to a constructor application, and it is stuck otherwise.
//!
//! Free variables of the local context keep their level. `quote` gives the free variables that it makes under a binder the levels from the length of the local context up, and it reads them back as bound variables.

use alloc::vec::Vec;
use rulean_store::{Expr, ExprId, LevelListId, Literal, NameId};

use crate::tc::{Checker, ErrorKind};
use crate::value::{Closure, EnvId, Head, SlotId, SpineId, Value, ValueId};

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
    fn unfold_glued(&mut self, c: NameId, us: LevelListId, sp: SpineId, s: SlotId) -> ValueId {
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
                let h = self.eval(EnvId::NIL, body);
                let u = self.apply_spine(h, sp, e);
                if !self.bad() {
                    self.va.slot_set(s, u);
                }
                u
            }
        }
    }

    /// `force(v)`: unfolds glued heads until the head is not a definition. This version does only delta (see the module comment).
    pub fn force(&mut self, v0: ValueId) -> ValueId {
        let mut v = v0;
        let mut done = false;
        while !done && !self.bad() {
            match self.va.get(v) {
                Value::Glued(c, us, sp, s) => v = self.unfold_glued(c, us, sp, s),
                _ => done = true,
            }
        }
        v
    }

    /// The value of the projection `v.idx` of the structure `sname`. It reduces when `v` forces to an application of a constructor of `sname` with enough arguments. Otherwise it is a stuck projection.
    fn proj_value(&mut self, sname: NameId, idx: u32, v: ValueId) -> ValueId {
        let w = self.force(v);
        if self.bad() {
            return self.v_dummy();
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
        let b = self.eval(env2, clo.body);
        self.quote(base, k + 1, b)
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
