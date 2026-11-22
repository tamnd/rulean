//! Tests of definitional equality of engine F (spec 05.4.4) and of the way engine F and engine R share a query (spec 05.1). Each test builds a small environment by hand.

use rulean_core::conv::Engine;
use rulean_core::env::{ConstInfo, ConstKind};
use rulean_core::tc::Checker;
use rulean_format::{Hints, Safety};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    c: Checker,
    a_ty: ExprId,
}

impl T {
    fn new() -> T {
        let mut c = Checker::new(Store::new());
        c.begin(Vec::new(), Safety::Safe);
        c.engine = Engine::F;
        let l = c.st.level_zero();
        let l1 = c.st.level_succ(l);
        let ty = c.st.mk_sort(l1);
        let mut t = T { c, a_ty: ty };
        t.a_ty = t.axiom("A", ty);
        t
    }
    fn name(&mut self, s: &str) -> NameId {
        let mut n = self.c.st.anon();
        for part in s.split('.') {
            n = self.c.st.name_str_bytes(n, part.as_bytes());
        }
        n
    }
    fn k(&mut self, s: &str) -> ExprId {
        let n = self.name(s);
        let ls = self.c.st.level_list_empty();
        self.c.st.mk_const(n, ls)
    }
    fn app(&mut self, f: ExprId, args: &[ExprId]) -> ExprId {
        self.c.st.mk_apps(f, args)
    }
    fn bv(&mut self, i: u32) -> ExprId {
        self.c.st.mk_bvar(i)
    }
    fn lam(&mut self, n: &str, ty: ExprId, body: ExprId) -> ExprId {
        let n = self.name(n);
        self.c.st.mk_lam(n, BinderInfo::Default, ty, body)
    }
    fn pi(&mut self, n: &str, ty: ExprId, body: ExprId) -> ExprId {
        let n = self.name(n);
        self.c.st.mk_pi(n, BinderInfo::Default, ty, body)
    }
    fn add(&mut self, name: &str, ty: ExprId, kind: ConstKind) {
        let name = self.name(name);
        self.c.env.add(ConstInfo {
            name,
            lparams: Vec::new(),
            ty,
            safety: Safety::Safe,
            kind,
        });
    }
    fn axiom(&mut self, name: &str, ty: ExprId) -> ExprId {
        self.add(name, ty, ConstKind::Axiom);
        self.k(name)
    }
    fn def(&mut self, name: &str, ty: ExprId, value: ExprId, h: u32) -> ExprId {
        let hints = Hints::Regular(h);
        self.add(name, ty, ConstKind::Defn { value, hints });
        self.k(name)
    }
    /// The identity function on `A`.
    fn id_a(&mut self) -> ExprId {
        let b = self.bv(0);
        self.lam("x", self.a_ty, b)
    }
    /// `A -> A`.
    fn a_to_a(&mut self) -> ExprId {
        self.pi("x", self.a_ty, self.a_ty)
    }
    fn eq(&mut self, x: ExprId, y: ExprId) -> bool {
        let r = self.c.is_def_eq(x, y);
        assert!(self.c.fault().is_none(), "fault: {:?}", self.c.fault());
        r
    }
}

#[test]
fn beta_is_equal_in_engine_f() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let id = t.id_a();
    let ida = t.app(id, &[a]);
    assert!(t.eq(ida, a));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
}

#[test]
fn delta_is_equal_in_engine_f() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let ty = t.a_ty;
    let f = t.def("f", ty, a, 1);
    let g = t.def("g", ty, f, 2);
    assert!(t.eq(g, a));
    assert!(t.eq(f, g));
    assert_eq!(t.c.f_stats.equal, 2);
}

#[test]
fn lazy_delta_compares_the_arguments_first() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let fty = t.a_to_a();
    let id = t.id_a();
    let g = t.def("g", fty, id, 1);
    let ida = t.app(id, &[a]);
    let x = t.app(g, &[ida]);
    let y = t.app(g, &[a]);
    assert!(t.eq(x, y));
    assert_eq!(t.c.f_stats.equal, 1);
}

#[test]
fn binders_and_function_eta() {
    let mut t = T::new();
    let fty = t.a_to_a();
    let f = t.axiom("f", fty);
    let id = t.id_a();
    // fun x => x and fun y => (fun z => z) y.
    let b0 = t.bv(0);
    let body = t.app(id, &[b0]);
    let l2 = t.lam("y", t.a_ty, body);
    assert!(t.eq(id, l2));
    // fun x => f x and f.
    let b0 = t.bv(0);
    let fx = t.app(f, &[b0]);
    let eta = t.lam("x", t.a_ty, fx);
    assert!(t.eq(eta, f));
    assert!(t.eq(f, eta));
    // Pi types with equal domains and codomains.
    let p2 = t.pi("y", t.a_ty, t.a_ty);
    assert!(t.eq(fty, p2));
    let s = t.c.f_stats;
    assert_eq!((s.equal, s.fallback), (4, 0));
}

#[test]
fn not_equal_goes_to_engine_r() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let b = t.axiom("b", t.a_ty);
    assert!(!t.eq(a, b));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 0, 1));
}

#[test]
fn confirm_all_runs_engine_r_on_each_equality() {
    let mut t = T::new();
    t.c.confirm_all = true;
    let a = t.axiom("a", t.a_ty);
    let ty = t.a_ty;
    let f = t.def("f", ty, a, 1);
    let id = t.id_a();
    let ida = t.app(id, &[f]);
    assert!(t.eq(ida, a));
    let s = t.c.f_stats;
    assert_eq!((s.equal, s.confirmed, s.disagree), (1, 1, 0));
}

#[test]
fn engine_r_does_not_use_engine_f() {
    let mut t = T::new();
    t.c.engine = Engine::R;
    let a = t.axiom("a", t.a_ty);
    let id = t.id_a();
    let ida = t.app(id, &[a]);
    assert!(t.eq(ida, a));
    assert_eq!(t.c.f_stats.queries, 0);
}

#[test]
fn proof_irrelevance_is_equal_in_engine_f() {
    let mut t = T::new();
    let l = t.c.st.level_zero();
    let prop = t.c.st.mk_sort(l);
    let p = t.axiom("P", prop);
    let h1 = t.axiom("h1", p);
    let h2 = t.axiom("h2", p);
    assert!(t.eq(h1, h2));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
}

#[test]
fn two_values_of_a_type_are_not_equal_by_irrelevance() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let b = t.axiom("b", t.a_ty);
    let fty = t.a_to_a();
    let f = t.axiom("f", fty);
    let fa = t.app(f, &[a]);
    let fb = t.app(f, &[b]);
    assert!(!t.eq(fa, fb));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 0, 1));
}
