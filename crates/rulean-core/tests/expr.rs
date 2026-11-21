//! Tests of the expression operations. The expected values follow `instantiate.cpp`, `abstract.cpp` and `expr.cpp` of the official kernel v4.35.0.

use rulean_core::expr::{
    Scratch, abstract_fvars, app_args, cheap_beta_reduce, expr_equal, has_loose_bvar, head_beta,
    instantiate, instantiate_lparams, instantiate_rev, lift_loose_bvars, lower_loose_bvars,
};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    st: Store,
    x: Scratch,
    ty: ExprId,
}

impl T {
    fn new() -> T {
        let mut st = Store::new();
        let z = st.level_zero();
        let ty = st.mk_sort(z);
        T {
            st,
            x: Scratch::new(),
            ty,
        }
    }
    fn name(&mut self, s: &str) -> NameId {
        let a = self.st.anon();
        self.st.name_str_bytes(a, s.as_bytes())
    }
    fn c(&mut self, s: &str) -> ExprId {
        let n = self.name(s);
        let ls = self.st.level_list_empty();
        self.st.mk_const(n, ls)
    }
    fn b(&mut self, i: u32) -> ExprId {
        self.st.mk_bvar(i)
    }
    fn app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        self.st.mk_app(f, a)
    }
    fn lam(&mut self, n: &str, body: ExprId) -> ExprId {
        let n = self.name(n);
        let ty = self.ty;
        self.st.mk_lam(n, BinderInfo::Default, ty, body)
    }
}

#[test]
fn instantiate_replaces_and_lowers() {
    let mut t = T::new();
    let (b0, b1, b2) = (t.b(0), t.b(1), t.b(2));
    let c = t.c("c");
    let e = t.app(b0, b1);
    let want = t.app(c, b0);
    assert_eq!(instantiate(&mut t.st, &mut t.x, e, &[c]), want);
    // Under a binder the index of the substituted variable moves up by one.
    let body = t.app(b0, b1);
    let l = t.lam("x", body);
    let wbody = t.app(b0, c);
    let want = t.lam("x", wbody);
    assert_eq!(instantiate(&mut t.st, &mut t.x, l, &[c]), want);
    // A value with a loose bound variable is lifted under the binder.
    let l = t.lam("x", b1);
    let want = t.lam("x", b1);
    assert_eq!(instantiate(&mut t.st, &mut t.x, l, &[b0]), want);
    let e = t.app(b2, b0);
    let want = t.app(b1, c);
    assert_eq!(instantiate(&mut t.st, &mut t.x, e, &[c]), want);
}

#[test]
fn instantiate_rev_uses_the_last_item_for_index_zero() {
    let mut t = T::new();
    let (b0, b1) = (t.b(0), t.b(1));
    let (a, b) = (t.c("a"), t.c("b"));
    let e = t.app(b0, b1);
    let want = t.app(b, a);
    assert_eq!(instantiate_rev(&mut t.st, &mut t.x, e, &[a, b]), want);
}

#[test]
fn abstract_makes_bound_variables() {
    let mut t = T::new();
    let ty = t.ty;
    let f1 = t.st.mk_fvar(0, ty);
    let f2 = t.st.mk_fvar(1, ty);
    let e = t.app(f1, f2);
    let (b0, b1, b2) = (t.b(0), t.b(1), t.b(2));
    let want = t.app(b1, b0);
    assert_eq!(abstract_fvars(&mut t.st, &mut t.x, e, &[f1, f2]), want);
    let l = t.lam("x", e);
    let wbody = t.app(b2, b1);
    let want = t.lam("x", wbody);
    assert_eq!(abstract_fvars(&mut t.st, &mut t.x, l, &[f1, f2]), want);
    // A free variable that is not in the list stays.
    let want = t.app(f1, b0);
    assert_eq!(abstract_fvars(&mut t.st, &mut t.x, e, &[f2]), want);
}

#[test]
fn lift_and_lower() {
    let mut t = T::new();
    let (b0, b2, b5) = (t.b(0), t.b(2), t.b(5));
    let e = t.app(b0, b2);
    let lifted = t.app(b0, b5);
    assert_eq!(lift_loose_bvars(&mut t.st, &mut t.x, e, 1, 3), lifted);
    assert_eq!(lower_loose_bvars(&mut t.st, &mut t.x, lifted, 3, 3), e);
}

#[test]
fn loose_bound_variable_occurrence() {
    let mut t = T::new();
    let b1 = t.b(1);
    let l = t.lam("x", b1);
    assert!(has_loose_bvar(&t.st, &mut t.x, l, 0));
    assert!(!has_loose_bvar(&t.st, &mut t.x, l, 1));
    let c = t.c("c");
    assert!(!has_loose_bvar(&t.st, &mut t.x, c, 0));
}

#[test]
fn level_instantiation() {
    let mut t = T::new();
    let nu = t.name("u");
    let u = t.st.level_param(nu);
    let us = t.st.level_list(&[u]);
    let n = t.name("c");
    let c = t.st.mk_const(n, us);
    let s = t.st.mk_sort(u);
    let e = t.app(c, s);
    let z = t.st.level_zero();
    let one = t.st.level_succ(z);
    let ones = t.st.level_list(&[one]);
    let c1 = t.st.mk_const(n, ones);
    let s1 = t.st.mk_sort(one);
    let want = t.app(c1, s1);
    assert_eq!(
        instantiate_lparams(&mut t.st, &mut t.x, e, &[nu], &[one]),
        want
    );
}

#[test]
fn beta() {
    let mut t = T::new();
    let (b0, b1) = (t.b(0), t.b(1));
    let (a, b, c) = (t.c("a"), t.c("b"), t.c("c"));
    // (fun x y => x) a b is a.
    let inner = t.lam("y", b1);
    let k = t.lam("x", inner);
    let ka = t.app(k, a);
    let kab = t.app(ka, b);
    assert_eq!(head_beta(&mut t.st, &mut t.x, kab), a);
    assert_eq!(cheap_beta_reduce(&mut t.st, kab), a);
    // (fun x => x) a b is a b.
    let id = t.lam("x", b0);
    let ida = t.app(id, a);
    let idab = t.app(ida, b);
    let ab = t.app(a, b);
    assert_eq!(head_beta(&mut t.st, &mut t.x, idab), ab);
    // (fun x y => c) a b is c.
    let inner = t.lam("y", c);
    let kc = t.lam("x", inner);
    let e = t.app(kc, a);
    let e = t.app(e, b);
    assert_eq!(cheap_beta_reduce(&mut t.st, e), c);
    // (fun x => c x) a is not cheap.
    let body = t.app(c, b0);
    let f = t.lam("x", body);
    let fa = t.app(f, a);
    assert_eq!(cheap_beta_reduce(&mut t.st, fa), fa);
    let ca = t.app(c, a);
    assert_eq!(head_beta(&mut t.st, &mut t.x, fa), ca);
}

#[test]
fn spine() {
    let mut t = T::new();
    let (f, a, b) = (t.c("f"), t.c("a"), t.c("b"));
    let fa = t.app(f, a);
    let fab = t.app(fa, b);
    let mut out = Vec::new();
    assert_eq!(app_args(&t.st, fab, &mut out), f);
    assert_eq!(out, vec![a, b]);
}

#[test]
fn alpha_equality_ignores_binder_names() {
    let mut t = T::new();
    let b0 = t.b(0);
    let lx = t.lam("x", b0);
    let ly = t.lam("y", b0);
    assert_ne!(lx, ly);
    assert!(expr_equal(&t.st, &mut t.x, lx, ly));
    let c = t.c("c");
    let lc = t.lam("x", c);
    assert!(!expr_equal(&t.st, &mut t.x, lx, lc));
    let a = t.app(lx, c);
    let b = t.app(ly, c);
    assert!(expr_equal(&t.st, &mut t.x, a, b));
}
