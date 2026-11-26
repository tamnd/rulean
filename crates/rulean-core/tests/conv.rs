//! Tests of definitional equality of engine F (spec 05.4.4) and of the way engine F and engine R share a query (spec 05.1). Each test builds a small environment by hand.

use rulean_core::conv::Engine;
use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo};
use rulean_core::tc::Checker;
use rulean_core::trace::Rule;
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
    // The query `f =?= fun x => f x` finds the success of the query before it in the success cache, so engine F does not run on it.
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (3, 3, 0));
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

/// `pick (α : s) (x y : α) : α := x`, a definition whose type ends in its bound variable `α`.
fn pick(t: &mut T, s: ExprId) -> ExprId {
    let b0 = t.bv(0);
    let b1 = t.bv(1);
    let b2 = t.bv(2);
    let inner = t.pi("y", b1, b2);
    let mid = t.pi("x", b0, inner);
    let ty = t.pi("α", s, mid);
    let x = t.bv(1);
    let b0 = t.bv(0);
    let b1 = t.bv(1);
    let lam_y = t.lam("y", b1, x);
    let lam_x = t.lam("x", b0, lam_y);
    let value = t.lam("α", s, lam_x);
    t.def("pick", ty, value, 1)
}

#[test]
fn a_constant_that_ends_in_a_bound_proposition_can_be_a_proof() {
    let mut t = T::new();
    let l = t.c.st.level_zero();
    let prop = t.c.st.mk_sort(l);
    let p = t.axiom("P", prop);
    let h1 = t.axiom("h1", p);
    let h2 = t.axiom("h2", p);
    let pk = pick(&mut t, prop);
    let x = t.app(pk, &[p, h1, h2]);
    let y = t.app(pk, &[p, h2, h1]);
    assert!(t.eq(x, y));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
}

#[test]
fn a_constant_that_ends_in_a_bound_type_is_not_a_proof() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let b = t.axiom("b", t.a_ty);
    let a_ty = t.a_ty;
    let l = t.c.st.level_zero();
    let l1 = t.c.st.level_succ(l);
    let ty1 = t.c.st.mk_sort(l1);
    let pk = pick(&mut t, ty1);
    let x = t.app(pk, &[a_ty, a, b]);
    let y = t.app(pk, &[a_ty, b, a]);
    assert!(!t.eq(x, y));
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 0, 1));
}

#[test]
fn two_values_of_the_same_form_are_equal_with_no_delta_step() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let fty = t.a_to_a();
    let f = t.axiom("f", fty);
    // `D : A → A := fun x => f x`, an abbreviation.
    let b0 = t.bv(0);
    let fx = t.app(f, &[b0]);
    let dv = t.lam("x", t.a_ty, fx);
    let n = t.name("D");
    t.c.env.add(ConstInfo {
        name: n,
        lparams: Vec::new(),
        ty: fty,
        safety: Safety::Safe,
        kind: ConstKind::Defn {
            value: dv,
            hints: Hints::Abbrev,
        },
    });
    let d = t.k("D");
    // `D a` and `(fun y => D y) a` evaluate to two values of the same form. Without the check of the form, lazy delta unfolds `D` on both sides.
    let x = t.app(d, &[a]);
    let b0 = t.bv(0);
    let dy = t.app(d, &[b0]);
    let l = t.lam("y", t.a_ty, dy);
    let y = t.app(l, &[a]);
    t.c.trace_on = true;
    assert!(t.eq(x, y));
    assert_eq!(t.c.trace.counts[Rule::Delta.index()], 0);
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
}

#[test]
fn a_taken_branch_is_unfolded_before_the_other_side() {
    let mut t = T::new();
    let a = t.axiom("a", t.a_ty);
    let ty = t.a_ty;
    // `big` has the height 3 and `sel` has the height 1. The official order unfolds `big` first.
    let k2 = t.def("k2", ty, a, 2);
    let big = t.def("big", ty, k2, 3);
    let b1 = t.bv(1);
    let inner = t.lam("y", t.a_ty, b1);
    let sv = t.lam("x", t.a_ty, inner);
    let a_a = t.a_to_a();
    let sty = t.pi("x", t.a_ty, a_a);
    let sel = t.def("sel", sty, sv, 1);
    // `sel big a` has `big` as an argument, so lazy delta unfolds `sel` and gets `big` with no unfolding of `big` (row O8 of spec 05.7.3).
    let x = t.app(sel, &[big, a]);
    t.c.trace_on = true;
    assert!(t.eq(x, big));
    assert_eq!(t.c.trace.counts[Rule::Delta.index()], 1);
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
}

#[test]
fn two_projections_compare_the_structures_before_they_unfold_them() {
    let mut t = T::new();
    let l = t.c.st.level_zero();
    let l1 = t.c.st.level_succ(l);
    let s1 = t.c.st.mk_sort(l1);
    let pr_n = t.name("Pr");
    let mk_n = t.name("Pr.mk");
    let induct = InductInfo {
        nparams: 0,
        nindices: 0,
        all: vec![pr_n],
        ctors: vec![mk_n],
        nnested: 0,
        is_rec: false,
        is_reflexive: false,
    };
    t.add("Pr", s1, ConstKind::Induct(induct));
    let pr = t.k("Pr");
    let inner = t.pi("b", t.a_ty, pr);
    let mk_ty = t.pi("a", t.a_ty, inner);
    let ctor = CtorInfo {
        induct: pr_n,
        cidx: 0,
        nparams: 0,
        nfields: 2,
    };
    t.add("Pr.mk", mk_ty, ConstKind::Ctor(ctor));
    let x = t.axiom("x", t.a_ty);
    let y = t.axiom("y", t.a_ty);
    let mk = t.k("Pr.mk");
    let v = t.app(mk, &[x, y]);
    let g = t.def("g", pr, v, 1);
    let g2 = t.def("g2", pr, g, 2);
    // The projections are behind the definitions `h1` and `h2`, so they come from a delta step of the conversion. The structures `g` and `g2` are equal after one delta step on `g2`. The structure of a projection is not unfolded before the two structures are compared, as with the cheap projections of the official kernel. So the query unfolds `h1`, `h2` and `g2`, and not `g`.
    let p1 = t.c.st.mk_proj(pr_n, 0, g);
    let p2 = t.c.st.mk_proj(pr_n, 0, g2);
    let h1 = t.def("h1", t.a_ty, p1, 3);
    let h2 = t.def("h2", t.a_ty, p2, 3);
    t.c.trace_on = true;
    assert!(t.eq(h1, h2));
    assert_eq!(t.c.trace.counts[Rule::Delta.index()], 3);
    let s = t.c.f_stats;
    assert_eq!((s.queries, s.equal, s.fallback), (1, 1, 0));
    // A projection of a structure behind a definition still reduces when the two sides are not equal by their structures.
    let p3 = t.c.st.mk_proj(pr_n, 0, g2);
    assert!(t.eq(p3, x));
    let p4 = t.c.st.mk_proj(pr_n, 1, g2);
    assert!(!t.eq(p4, x));
}
