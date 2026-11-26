//! Type inference of engine F (spec 05.4.5).
//!
//! Engine R infers the type of a term under a binder after it replaces the bound variable with a free variable (`instantiate`). Each binder copies its body, so a term with `n` nested binders and shared subterms takes time `n` times the size of the term. Engine F infers the type of a stored term in a context and does not copy the term.
//!
//! A context is a node of a tree. Each node has its parent, one more entry and the environment of values for `eval`. Two binders with the same parent node and the same domain term get the same node, so a shared subterm under two such binders has one cache key. The cache keys of inference and evaluation are a term and a node. A term without loose bound variables uses the root node.
//!
//! A binder node has a free variable in the local context, with the level of the next free variable. The local context only grows during a declaration, so the levels of the nodes stay valid. A `let` node keeps the value in the environment and has no free variable. A projection, a literal or a free variable goes to engine R, on the term with the free variables of the nodes in place of its loose bound variables. A `let` node gets its free variable only when engine R needs it.
//!
//! The result of inference is a value. A lambda gets a pi type whose body is the read-back of the type of its body (spec 05.4.3).
//!
//! Engine F tries the value check of a declaration first. Each check of an argument type, a `let` value type and the declared type is a `conv` query of engine F. If a query is "not equal", or if it needs engine R to confirm it (spec 05.1), engine R decides that query on the read-back terms, and engine F continues if engine R gives "equal" (spec perf/04.3 A2). If engine R gives "not equal", or if engine F stops with a fault, the fault is removed and engine R checks the declaration again from the start. So a reject needs engine R (spec 05.1, rule 2).

use alloc::vec::Vec;
use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, Expr, ExprId, NameId};

use crate::conv::{Engine, F_DELTA, F_TYPED};
use crate::level;
use crate::memo::Memo;
use crate::tc::{Checker, ErrorKind};
use crate::value::{Closure, EnvId, Head, Value, ValueId};

/// The root context: no entries.
const ROOT: u32 = 0;

/// A node of the context tree.
#[derive(Clone, Copy, Debug)]
struct Node {
    /// The parent node.
    parent: u32,
    /// The number of entries.
    len: u32,
    /// The values of the entries, for `eval`.
    env: EnvId,
    /// The types of the entries.
    tys: EnvId,
    /// The free variable of the entry in the local context. A `let` entry gets it when engine R needs it.
    fvar: Option<ExprId>,
    name: NameId,
    info: BinderInfo,
    /// The domain of a binder, or the type of a `let`, as a term in the parent context.
    ty: ExprId,
    /// The value of a `let`, as a term in the parent context.
    val: Option<ExprId>,
}

/// The state of engine F inference for one declaration.
#[derive(Debug)]
pub(crate) struct FInfer {
    nodes: Vec<Node>,
    /// The binder node at key (domain, parent).
    binds: Memo,
    /// The `let` node at key (value, parent).
    lets: Memo,
    /// The type at key (term, 2 * node + mode). The mode is 1 for infer-only.
    types: Memo,
    /// The value at key (term, node).
    values: Memo,
}

impl FInfer {
    pub(crate) fn new() -> FInfer {
        FInfer {
            nodes: Vec::new(),
            binds: Memo::new(),
            lets: Memo::new(),
            types: Memo::new(),
            values: Memo::new(),
        }
    }

    /// Removes all nodes and cache entries. The values are in the arena, so this goes together with the reset of the arena.
    pub(crate) fn reset(&mut self) {
        self.nodes.truncate(0);
        self.binds.clear();
        self.lets.clear();
        self.types.clear();
        self.values.clear();
    }
}

impl Checker {
    /// The value check of a definition, a theorem or an opaque constant with engine F. True if engine F accepts `value` with the type `ty`. False if engine F did not decide, and then the caller checks the declaration with engine R. False is never a reject.
    pub(crate) fn f_check_value(&mut self, value: ExprId, ty: ExprId) -> bool {
        let mark = self.scope.len();
        let ok = self.f_check_value_in(value, ty);
        self.scope.truncate(mark);
        ok
    }

    /// The body of `f_check_value`. Engine F gives no fault, so the caller removes the free variables of engine F from the scope list.
    fn f_check_value_in(&mut self, value: ExprId, ty: ExprId) -> bool {
        if self.engine == Engine::R || self.bad() || self.va.full() {
            return false;
        }
        self.f_stats.infer += 1;
        let depth = self.depth;
        self.f_root();
        let vt = self.f_infer(ROOT, value, false);
        let ok = if self.bad() {
            false
        } else {
            let t = self.f_eval(ROOT, ty);
            self.f_conv_top(vt, t)
        };
        if self.bad() {
            self.fault = None;
            self.depth = depth;
            return false;
        }
        if ok {
            self.f_stats.infer_ok += 1;
        }
        ok
    }

    /// The type check of a declaration with engine F: the type of `ty` must be a sort. It gives true if engine F accepts. It gives false if engine F stops or cannot run, and then engine R must do the check. A fault of engine F is removed, as in `f_check_value`.
    pub(crate) fn f_check_type(&mut self, ty: ExprId) -> bool {
        let mark = self.scope.len();
        let ok = self.f_check_type_in(ty);
        self.scope.truncate(mark);
        ok
    }

    /// The body of `f_check_type`. Engine F gives no fault, so the caller removes the free variables of engine F from the scope list.
    fn f_check_type_in(&mut self, ty: ExprId) -> bool {
        if self.engine == Engine::R || self.bad() || self.va.full() {
            return false;
        }
        self.f_stats.infer += 1;
        let depth = self.depth;
        self.f_root();
        let s = self.f_infer(ROOT, ty, false);
        if !self.bad() {
            self.f_sort_level(s, ty);
        }
        if self.bad() {
            self.fault = None;
            self.depth = depth;
            return false;
        }
        self.f_stats.infer_ok += 1;
        true
    }

    /// Makes the root node if the tree is empty.
    fn f_root(&mut self) {
        if self.fi.nodes.is_empty() {
            let anon = self.st.anon();
            self.fi.nodes.push(Node {
                parent: ROOT,
                len: 0,
                env: EnvId::NIL,
                tys: EnvId::NIL,
                fvar: None,
                name: anon,
                info: BinderInfo::Default,
                ty: self.dummy,
                val: None,
            });
        }
    }

    /// A top-level `conv` query of engine F inside inference. A "not equal" answer of engine F is a hint (spec perf/04.7): both values are read back, and engine R decides the query on the terms. An "equal" answer in the confirm set of spec 05.1 goes to engine R in the same way. If engine R gives "equal", the inference continues. Else the inference stops with a fault, and engine R checks the full declaration, so a reject always comes from engine R. With `confirm_all`, engine R checks the full declaration again after engine F accepts it, so an "equal" answer is not confirmed here.
    ///
    ///
    /// Before this change, each answer in the confirm set stopped the inference, and engine R checked the full declaration again. On Init this was 10,310 of 11,775 stops of engine F, and engine F used 607 G instructions. With a confirm of the query, engine F used 543 G instructions and stopped on 1,885 values.
    fn f_conv_top(&mut self, a: ValueId, b: ValueId) -> bool {
        if self.bad() {
            return false;
        }
        self.f_bits = 0;
        self.c_conv_failure.clear();
        self.c_conv_success.clear();
        self.eq_depth += 1;
        let r = self.conv(a, b);
        self.eq_depth -= 1;
        if self.bad() {
            return false;
        }
        let confirm = !self.confirm_all && self.f_bits == F_DELTA | F_TYPED;
        if r && !confirm {
            return true;
        }
        if !r {
            self.f_stats.fallback += 1;
        }
        let base = self.lctx_ty.len() as u32;
        let ta = self.quote(base, base, a);
        let tb = self.quote(base, base, b);
        if self.bad() {
            return false;
        }
        let ok = self.is_def_eq_r(ta, tb);
        if self.bad() {
            return false;
        }
        if ok {
            if r {
                self.f_stats.confirmed += 1;
            }
            return true;
        }
        if r {
            self.f_stats.disagree += 1;
        }
        self.fail(ErrorKind::Unsupported, self.dummy);
        false
    }

    /// The node of the context `c` with one more binder of domain `dom` (a term in `c`) and value `dv`.
    fn f_bind(&mut self, c: u32, name: NameId, info: BinderInfo, dom: ExprId, dv: ValueId) -> u32 {
        if let Some(n) = self.fi.binds.get(dom.0, raw(c)) {
            return low(n);
        }
        let lvl = self.lctx_ty.len() as u32;
        let ty = self.quote(lvl, lvl, dv);
        let fv = self.mk_local(name, info, ty, None);
        let x = self.v_neutral(Head::FVar(lvl, dv));
        let p = self.fi.nodes[c as usize];
        let env = self.env_push(p.env, x);
        let tys = self.env_push(p.tys, dv);
        let id = self.fi.nodes.len() as u32;
        self.fi.nodes.push(Node {
            parent: c,
            len: p.len + 1,
            env,
            tys,
            fvar: Some(fv),
            name,
            info,
            ty: dom,
            val: None,
        });
        if !self.bad() {
            self.fi.binds.put(dom.0, raw(c), raw(id));
        }
        id
    }

    /// The node of the context `c` with one more `let` entry: the type `ty` and value `val` are terms in `c`, `tv` and `vv` are their values.
    fn f_let(
        &mut self,
        c: u32,
        name: NameId,
        ty: ExprId,
        val: ExprId,
        tv: ValueId,
        vv: ValueId,
    ) -> u32 {
        let hit = self.fi.lets.get(val.0, raw(c));
        if let Some(n) = hit {
            let n = low(n);
            if self.fi.nodes[n as usize].ty == ty {
                return n;
            }
        }
        let p = self.fi.nodes[c as usize];
        let env = self.env_push(p.env, vv);
        let tys = self.env_push(p.tys, tv);
        let id = self.fi.nodes.len() as u32;
        self.fi.nodes.push(Node {
            parent: c,
            len: p.len + 1,
            env,
            tys,
            fvar: None,
            name,
            info: BinderInfo::Default,
            ty,
            val: Some(val),
        });
        if hit.is_none() && !self.bad() {
            self.fi.lets.put(val.0, raw(c), raw(id));
        }
        id
    }

    /// The free variables of the entries of `c`, from the first entry to the last. A `let` entry gets its free variable here, with the type and the value instantiated.
    fn f_subst(&mut self, c: u32) -> Vec<ExprId> {
        let mut path: Vec<u32> = Vec::new();
        let mut n = c;
        while n != ROOT {
            path.push(n);
            n = self.fi.nodes[n as usize].parent;
        }
        let mut subst: Vec<ExprId> = Vec::with_capacity(path.len());
        let mut i = path.len();
        while i > 0 {
            i -= 1;
            let id = path[i] as usize;
            let node = self.fi.nodes[id];
            let fv = match (node.fvar, node.val) {
                (Some(fv), _) => fv,
                (None, Some(val)) => {
                    let ty = self.instantiate_rev(node.ty, &subst);
                    let v = self.instantiate_rev(val, &subst);
                    let fv = self.mk_local(node.name, node.info, ty, Some(v));
                    self.fi.nodes[id].fvar = Some(fv);
                    fv
                }
                (None, None) => self.fail(ErrorKind::UnknownFVar, self.dummy),
            };
            subst.push(fv);
        }
        subst
    }

    /// The value of the term `e` in the context `c`. An application and a `let` are evaluated here, so that each node of a spine of nested applications and of a chain of `let` terms is evaluated once in each context. The value of a `let` comes from its node in the context tree, as in inference.
    pub(crate) fn f_eval(&mut self, c: u32, e: ExprId) -> ValueId {
        if self.bad() {
            return self.v_dummy();
        }
        let c = if self.st.loose_range(e) == 0 { ROOT } else { c };
        if let Some(v) = self.fi.values.get(e.0, raw(c)) {
            return ValueId(low(v));
        }
        if !self.enter(e) {
            return self.v_dummy();
        }
        let v = match self.st.node(e) {
            Expr::App(f, a) => {
                let vf = self.f_eval(c, f);
                let va = self.f_eval(c, a);
                self.apply(vf, va, e)
            }
            Expr::Let(l) => {
                let tv = self.f_eval(c, l.ty);
                let vv = self.f_eval(c, l.value);
                let c2 = self.f_let(c, l.name, l.ty, l.value, tv, vv);
                self.f_eval(c2, l.body)
            }
            _ => {
                let env = self.fi.nodes[c as usize].env;
                self.eval(env, e)
            }
        };
        self.leave();
        if !self.bad() {
            self.fi.values.put(e.0, raw(c), raw(v.0));
        }
        v
    }

    /// `infer(e)` in the context `c`, with all checks if `infer_only` is false.
    fn f_infer(&mut self, c: u32, e: ExprId, infer_only: bool) -> ValueId {
        if self.bad() {
            return self.v_dummy();
        }
        let range = self.st.loose_range(e);
        if range > self.fi.nodes[c as usize].len {
            self.fail(ErrorKind::LooseBVar, e);
            return self.v_dummy();
        }
        let c = if range == 0 { ROOT } else { c };
        let key = raw(2 * c + infer_only as u32);
        if let Some(v) = self.fi.types.get(e.0, key) {
            return ValueId(low(v));
        }
        if !self.enter(e) {
            return self.v_dummy();
        }
        let v = self.f_infer_node(c, e, infer_only);
        self.leave();
        if !self.bad() {
            self.fi.types.put(e.0, key, raw(v.0));
        }
        v
    }

    fn f_infer_node(&mut self, c: u32, e: ExprId, infer_only: bool) -> ValueId {
        match self.st.node(e) {
            Expr::BVar(i) => {
                let tys = self.fi.nodes[c as usize].tys;
                match self.va.env_get(tys, i) {
                    Some(t) => t,
                    None => {
                        self.fail(ErrorKind::LooseBVar, e);
                        self.v_dummy()
                    }
                }
            }
            Expr::Sort(l) => {
                if !infer_only {
                    self.check_level(l, e);
                }
                let s = self.st.level_succ(l);
                self.v_alloc(Value::Sort(s))
            }
            Expr::Const(..) => {
                let t = self.infer_constant(e, infer_only);
                self.f_eval(ROOT, t)
            }
            Expr::Lam(b) => {
                if !infer_only {
                    let s = self.f_infer(c, b.dom, infer_only);
                    self.f_sort_level(s, b.dom);
                }
                let dv = self.f_eval(c, b.dom);
                let c2 = self.f_bind(c, b.name, b.info, b.dom, dv);
                let bt = self.f_infer(c2, b.body, infer_only);
                if self.bad() {
                    return self.v_dummy();
                }
                let lvl = match self.fi.nodes[c2 as usize].fvar {
                    Some(fv) => match self.st.node(fv) {
                        Expr::FVar(l, _) => l,
                        _ => return self.f_stop(e),
                    },
                    None => return self.f_stop(e),
                };
                let body = self.quote(lvl, lvl + 1, bt);
                let clo = Closure {
                    env: EnvId::NIL,
                    body,
                };
                self.v_alloc(Value::Pi(b.name, b.info, dv, clo))
            }
            Expr::Pi(b) => {
                let s1 = self.f_infer(c, b.dom, infer_only);
                let u = self.f_sort_level(s1, b.dom);
                let dv = self.f_eval(c, b.dom);
                let c2 = self.f_bind(c, b.name, b.info, b.dom, dv);
                let s2 = self.f_infer(c2, b.body, infer_only);
                let v = self.f_sort_level(s2, b.body);
                if self.bad() {
                    return self.v_dummy();
                }
                let l = level::mk_imax(&mut self.st, u, v);
                self.v_alloc(Value::Sort(l))
            }
            Expr::App(f, a) => {
                let ft = self.f_infer(c, f, infer_only);
                let pv = self.force(ft);
                if self.bad() {
                    return self.v_dummy();
                }
                let (dom, clo) = match self.va.get(pv) {
                    Value::Pi(_, _, d, clo) => (d, clo),
                    _ => {
                        self.fail(ErrorKind::FunctionExpected, e);
                        return self.v_dummy();
                    }
                };
                if !infer_only {
                    if self.is_eager_reduce(a) {
                        return self.f_stop(e);
                    }
                    let at = self.f_infer(c, a, infer_only);
                    if !self.f_conv_top(at, dom) {
                        return self.v_dummy();
                    }
                }
                // A body without loose bound variables does not use the argument, so the argument is not evaluated.
                let av = if self.st.loose_range(clo.body) == 0 {
                    self.v_dummy()
                } else {
                    self.f_eval(c, a)
                };
                let env = self.env_push(clo.env, av);
                self.eval(env, clo.body)
            }
            Expr::Let(l) => {
                if !infer_only {
                    let s = self.f_infer(c, l.ty, infer_only);
                    self.f_sort_level(s, l.ty);
                    let vt = self.f_infer(c, l.value, infer_only);
                    let tv = self.f_eval(c, l.ty);
                    if !self.f_conv_top(vt, tv) {
                        return self.v_dummy();
                    }
                }
                let tv = self.f_eval(c, l.ty);
                let vv = self.f_eval(c, l.value);
                let c2 = self.f_let(c, l.name, l.ty, l.value, tv, vv);
                self.f_infer(c2, l.body, infer_only)
            }
            Expr::Lit(_) | Expr::Proj(_) | Expr::FVar(..) => self.f_infer_r(c, e, infer_only),
        }
    }

    /// The type of `e` from engine R, on `e` with the free variables of the context in place of its loose bound variables.
    fn f_infer_r(&mut self, c: u32, e: ExprId, infer_only: bool) -> ValueId {
        let subst = self.f_subst(c);
        if self.bad() {
            return self.v_dummy();
        }
        let t = self.instantiate_rev(e, &subst);
        let ty = self.infer_type_core(t, infer_only);
        if self.bad() {
            return self.v_dummy();
        }
        self.f_eval(ROOT, ty)
    }

    /// The level of a type `s` that must be a sort after `force`. Otherwise a "type expected" fault at `at`.
    fn f_sort_level(&mut self, s: ValueId, at: ExprId) -> rulean_store::LevelId {
        let w = self.force(s);
        if self.bad() {
            return self.st.level_zero();
        }
        match self.va.get(w) {
            Value::Sort(l) => l,
            _ => {
                self.fail(ErrorKind::TypeExpected, at);
                self.st.level_zero()
            }
        }
    }

    /// Stops engine F inference: engine R checks the declaration.
    fn f_stop(&mut self, at: ExprId) -> ValueId {
        self.fail(ErrorKind::Unsupported, at);
        self.v_dummy()
    }
}
