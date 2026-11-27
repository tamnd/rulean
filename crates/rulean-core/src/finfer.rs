//! Type inference of engine F (spec 05.4.5).
//!
//! Engine R infers the type of a term under a binder after it replaces the bound variable with a free variable (`instantiate`). Each binder copies its body, so a term with `n` nested binders and shared subterms takes time `n` times the size of the term. Engine F infers the type of a stored term in a context and does not copy the term.
//!
//! A context is a node of a tree. Each node has its parent, one more entry and the environment of values for `eval`. Two binders with the same parent node and the same domain term get the same node, so a shared subterm under two such binders has one cache key. The cache keys of inference and evaluation are a term and a node. A term without loose bound variables uses the root node.
//!
//! A binder node has a free variable in the local context, with the level of the next free variable. The local context only grows during a declaration, so the levels of the nodes stay valid. A `let` node keeps the value in the environment and has no free variable. A literal and a free variable get their type in engine F. A projection does too. For a structure in `Prop`, engine R decides `is_prop` of each field type as one query on its read-back. A projection whose type has a form that engine F does not read goes to engine R, on the term with the free variables of the nodes in place of its loose bound variables. A `let` node gets its free variable only when engine R needs it.
//!
//! The result of inference is a value. A lambda gets the type `Value::PiOpen`, which keeps the type of its body as a value under the local of the lambda (spec perf/04.5). `conv` compares it with a pi type under that local. Each other read of the type reads the body type back once into the body of a closure (spec 05.4.3).
//!
//! Engine F tries the value check of a declaration first. Each check of an argument type, a `let` value type and the declared type is a `conv` query of engine F. If a query is "not equal", or if it needs engine R to confirm it (spec 05.1), engine R decides that query on the read-back terms, and engine F continues if engine R gives "equal" (spec perf/04.3 A2). If engine R gives "not equal", or if engine F stops with a fault, the fault is removed and engine R checks the declaration again from the start. So a reject needs engine R (spec 05.1, rule 2).

use alloc::vec::Vec;
use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, Expr, ExprId, NameId};

use crate::conv::{Engine, F_DELTA, F_TYPED};
use crate::level;
use crate::memo::Memo;
use crate::tc::{Checker, ErrorKind};
use crate::value::{EnvId, Head, Value, ValueId};

/// The root context: no entries.
const ROOT: u32 = 0;

/// The largest value term, in distinct nodes, that engine F checks if the term is not deep. Engine R checks a larger value (spec perf/11).
const F_TERM_CAP: u32 = 64;

/// The binder depth above which a value term stays with engine F (see `term_walk`).
const F_DEEP: u32 = 64;

/// The largest number of nodes that `term_walk` reads. It is more than `F_TERM_CAP` and more than `F_DEEP`, so that the walk can find a deep chain in a term with more than `F_TERM_CAP` nodes.
const F_WALK: u32 = 1024;

/// The size of a value term, in distinct nodes, above which the queries of the declaration use engine R only. It is more than `F_TERM_CAP`, because on a small value the queries of engine R can need the rules of engine F, as in the perf test `ite-taken-branch`.
const F_R_ONLY: u32 = 256;

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
    /// The terms that `term_walk` saw.
    seen: Memo,
    /// The binder depth of each term on the stack of `term_walk`.
    walk_depth: Vec<u32>,
}

impl FInfer {
    pub(crate) fn new() -> FInfer {
        FInfer {
            nodes: Vec::new(),
            binds: Memo::new(),
            lets: Memo::new(),
            types: Memo::new(),
            values: Memo::new(),
            seen: Memo::new(),
            walk_depth: Vec::new(),
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
        // Engine R checks a large value that is not deep. If the value is larger than `F_R_ONLY`, the queries of the declaration use engine R only (spec perf/11).
        let n = self.term_walk(value);
        if n > F_TERM_CAP {
            self.f_declined = n > F_R_ONLY;
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
        // A wide type goes to engine R, as a wide value does. The type check does not set `f_declined` (spec perf/11.8).
        if self.term_walk(ty) > F_TERM_CAP {
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

    /// The number of distinct nodes of the value term `e`, at most `F_WALK + 1`, or 0 if the term has a chain of more than `F_DEEP` nested binders.
    ///
    /// Engine R copies the body of a binder when it goes under the binder, so its time grows with the depth of the binders times the size of the term. Engine F does not copy the term. So a deep term stays with engine F, and this gives 0 for it. On Init, the large values are wide proofs with a small depth, and engine R checks them with fewer instructions (spec perf/08.3). The walk goes first into the body of each binder, so it finds a deep chain early. It stops after `F_WALK + 1` nodes, so its cost is at most `F_WALK` steps.
    fn term_walk(&mut self, e: ExprId) -> u32 {
        self.fi.seen.clear();
        let mark = self.estk.len();
        self.fi.walk_depth.truncate(0);
        self.estk.push(e);
        self.fi.walk_depth.push(0);
        let mut n: u32 = 0;
        let mut deep = false;
        while self.estk.len() > mark && n <= F_WALK && !deep {
            let x = match self.estk.pop() {
                Some(x) => x,
                None => e,
            };
            // The two stacks have the same length, so `walk_depth` is not empty here.
            let top = self.fi.walk_depth.len() - 1;
            let d = self.fi.walk_depth[top];
            self.fi.walk_depth.truncate(top);
            if d > F_DEEP {
                deep = true;
            } else if !self.fi.seen.contains(x.0, 0) {
                self.fi.seen.put(x.0, 0, 1);
                n += 1;
                match self.st.node(x) {
                    Expr::App(f, a) => {
                        self.walk_push(f, d);
                        self.walk_push(a, d);
                    }
                    Expr::Lam(b) | Expr::Pi(b) => {
                        self.walk_push(b.dom, d);
                        self.walk_push(b.body, d + 1);
                    }
                    Expr::Let(l) => {
                        self.walk_push(l.ty, d);
                        self.walk_push(l.value, d);
                        self.walk_push(l.body, d + 1);
                    }
                    Expr::Proj(p) => self.walk_push(p.expr, d),
                    _ => {}
                }
            }
        }
        self.estk.truncate(mark);
        self.fi.walk_depth.truncate(0);
        if deep { 0 } else { n }
    }

    /// Pushes a term and its binder depth for `term_walk`.
    fn walk_push(&mut self, e: ExprId, d: u32) {
        self.estk.push(e);
        self.fi.walk_depth.push(d);
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
        let forced = self.c_force.len();
        let unfolded = self.c_unfold_key.len();
        let stack = self.vstk.len();
        let m = self.va.mark();
        let r = self.f_conv_top_in(a, b);
        if let Some(m) = m {
            if self.bad() || self.vstk.len() != stack || !self.va.crowded() {
                self.va.unmark();
            } else {
                self.va.release(m);
                self.c_force.truncate(forced);
                self.c_unfold_key.truncate(unfolded);
            }
        }
        r
    }

    /// The body of `f_conv_top`.
    fn f_conv_top_in(&mut self, a: ValueId, b: ValueId) -> bool {
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
        // One cache for both read-backs: the two values often share sub-values.
        self.c_quote.clear();
        self.q_depth += 1;
        let ta = self.quote(base, base, a);
        let tb = self.quote(base, base, b);
        self.q_depth -= 1;
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
    ///
    /// A pi binder uses the node at key (`dom`, `c`) in `binds` if there is one. A lambda (`fresh`) always gets a new node with a new local, and the node does not go into `binds`. The type of a lambda is a `Value::PiOpen` with this local, and `conv` compares it with a pi type under the local, in place of a new local (spec perf/04.5). This is correct only if no value outside the body of the lambda has the local. With a shared node, this is false. For example, in `fun (p q : U) => Eq.refl q` the inner lambda has no loose bound variable, so `f_infer` infers it in the root context, and the key (`U`, root) gave it the node of `p`. Then the two types had the same local, and `conv` found `@Eq U q q` equal to `@Eq U p q`. A lambda is inferred once in each context (the cache `types`), so a new node for each lambda does not repeat the inference of its body.
    fn f_bind(
        &mut self,
        c: u32,
        name: NameId,
        info: BinderInfo,
        dom: ExprId,
        dv: ValueId,
        fresh: bool,
    ) -> u32 {
        if !fresh {
            if let Some(n) = self.fi.binds.get(dom.0, raw(c)) {
                return low(n);
            }
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
        if !fresh && !self.bad() {
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
                let c2 = self.f_bind(c, b.name, b.info, b.dom, dv, true);
                let bt = self.f_infer(c2, b.body, infer_only);
                if self.bad() {
                    return self.v_dummy();
                }
                // The local of the lambda is the top of the environment of `c2`. The type keeps `bt` under it, and the read-back of `bt` comes only at a read that needs a closure (spec perf/04.5).
                let x = match self.va.env_get(self.fi.nodes[c2 as usize].env, 0) {
                    Some(x) => x,
                    None => return self.f_stop(e),
                };
                let r = self.va.pi_open(b.name, b.info, x, bt);
                if self.va.full() {
                    self.fail(ErrorKind::ArenaFull, e);
                }
                r
            }
            Expr::Pi(b) => {
                let s1 = self.f_infer(c, b.dom, infer_only);
                let u = self.f_sort_level(s1, b.dom);
                let dv = self.f_eval(c, b.dom);
                let c2 = self.f_bind(c, b.name, b.info, b.dom, dv, false);
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
                let (dom, clo) = match self.vget(pv) {
                    Value::Pi(_, _, d, clo) => (d, clo),
                    _ => {
                        self.fail(ErrorKind::FunctionExpected, e);
                        return self.v_dummy();
                    }
                };
                if !infer_only {
                    let at = self.f_infer(c, a, infer_only);
                    // The `eagerReduce` hint lets engine R use the `Nat` extension and the `Bool` reflection on terms with free variables. Engine F has no such limit, so the hint changes only the query that engine R confirms.
                    let saved = self.eager;
                    if self.is_eager_reduce(a) {
                        self.eager = true;
                    }
                    let ok = self.f_conv_top(at, dom);
                    self.eager = saved;
                    if !ok {
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
            Expr::Lit(l) => {
                let t = self.infer_lit(e, l);
                self.f_eval(ROOT, t)
            }
            Expr::FVar(lvl, ty) => {
                if (lvl as usize) < self.lctx_ty.len() {
                    self.f_eval(ROOT, ty)
                } else {
                    self.fail(ErrorKind::UnknownFVar, e);
                    self.v_dummy()
                }
            }
            Expr::Proj(p) => self.f_infer_proj(c, e, p.struct_name, p.index, p.expr, infer_only),
        }
    }

    /// `infer_proj` in engine F: the type of the field `idx` of `s`, a term of a structure `sname`. The type of `s` must force to `sname` applied to its parameters. The type of the constructor gets the parameters, and each field before `idx` gets its projection of `s`. Engine R does the inference in each other case, so the faults and their order are the faults of engine R. For a structure in `Prop`, each field must be a proof. Engine F cannot infer the type of a type, so `f_is_prop` asks engine R one query on the read-back of the field type, at the same points as engine R.
    fn f_infer_proj(
        &mut self,
        c: u32,
        e: ExprId,
        sname: NameId,
        idx: u32,
        s: ExprId,
        infer_only: bool,
    ) -> ValueId {
        let st = self.f_infer(c, s, infer_only);
        let w = self.force(st);
        if self.bad() {
            return self.v_dummy();
        }
        let (n, us, sp) = match self.vget(w) {
            Value::Neu(Head::Const(n, us), sp) if n == sname => (n, us, sp),
            _ => return self.f_infer_r(c, e, infer_only),
        };
        let slot = self.env.find(n);
        let shape = if slot == 0 {
            None
        } else {
            self.induct_shape(slot)
        };
        let (np, ni, ctor) = match shape {
            Some((np, ni, 1, ctor)) if self.va.spine_len(sp) == np + ni => (np, ni, ctor),
            _ => return self.f_infer_r(c, e, infer_only),
        };
        let cslot = self.env.find(ctor);
        let ls = self.st.level_list_vec(us);
        let is_prop_type = match self.f_struct_prop(slot, np + ni, &ls) {
            Some(b) if cslot != 0 => b,
            _ => return self.f_infer_r(c, e, infer_only),
        };
        let t = self.instantiate_type_lparams(cslot, &ls);
        let mut v = self.f_eval(ROOT, t);
        let mut ok = true;
        let mut i = 0;
        while ok && i < np && !self.bad() {
            let p = self.force(v);
            match (self.vget(p), self.va.spine_arg(sp, i)) {
                (Value::Pi(_, _, _, clo), Some(a)) => {
                    let env = self.env_push(clo.env, a);
                    v = self.eval(env, clo.body);
                }
                _ => ok = false,
            }
            i += 1;
        }
        let mut j = 0;
        while ok && j < idx && !self.bad() {
            let p = self.force(v);
            match self.vget(p) {
                Value::Pi(_, _, d, clo) => {
                    // A body without loose bound variables does not use the field, so the projection is not made.
                    let a = if self.st.loose_range(clo.body) == 0 {
                        self.v_dummy()
                    } else {
                        ok = !is_prop_type || self.f_is_prop(d);
                        let sv = self.f_eval(c, s);
                        self.proj_value(sname, j, sv)
                    };
                    let env = self.env_push(clo.env, a);
                    v = self.eval(env, clo.body);
                }
                _ => ok = false,
            }
            j += 1;
        }
        if self.bad() {
            return self.v_dummy();
        }
        let p = if ok { self.force(v) } else { v };
        let d = match (ok, self.vget(p)) {
            (true, Value::Pi(_, _, d, _)) => d,
            _ => return self.f_infer_r(c, e, infer_only),
        };
        if is_prop_type && !self.f_is_prop(d) && !self.bad() {
            return self.f_infer_r(c, e, infer_only);
        }
        d
    }

    /// `is_prop` of engine R on the read-back of the type `d`: one query of engine R (spec perf/04.3 A2). Engine F cannot infer the type of a type, and a field of a structure in `Prop` must be a proof.
    fn f_is_prop(&mut self, d: ValueId) -> bool {
        let base = self.lctx_ty.len() as u32;
        let t = self.quote(base, base, d);
        !self.bad() && self.is_prop(t)
    }

    /// True if the inductive type of `slot` with the levels `ls` is a proposition: the level of its sort after the instantiation is zero. `None` if its type is not `n` pi binders and a sort. Engine R gets the same level from `is_prop` on the type of the major premise, because the sort of an inductive type does not depend on its arguments.
    fn f_struct_prop(&mut self, slot: u32, n: u32, ls: &[rulean_store::LevelId]) -> Option<bool> {
        let mut t = self.env.at(slot).ty;
        let mut ok = true;
        let mut k = 0;
        while ok && k < n {
            match self.st.node(t) {
                Expr::Pi(b) => t = b.body,
                _ => ok = false,
            }
            k += 1;
        }
        match (ok, self.st.node(t)) {
            (true, Expr::Sort(l)) => {
                let cst = self.env.at(slot);
                let l2 = level::instantiate(&mut self.st, l, &cst.lparams, ls);
                Some(level::normalizes_to_zero(&self.st, l2))
            }
            _ => None,
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
        match self.vget(w) {
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
