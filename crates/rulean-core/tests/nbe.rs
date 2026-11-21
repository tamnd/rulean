//! Tests of evaluation and read-back of engine F (spec 05.4.2 and 05.4.3). Each test builds a small environment by hand.

use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_core::value::EnvId;
use rulean_format::{Hints, Safety};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    c: Checker,
}

impl T {
    fn new() -> T {
        let mut c = Checker::new(Store::new());
        c.begin(Vec::new(), Safety::Safe);
        T { c }
    }
    fn name(&mut self, s: &str) -> NameId {
        let mut n = self.c.st.anon();
        for part in s.split('.') {
            n = self.c.st.name_str_bytes(n, part.as_bytes());
        }
        n
    }
    fn sort(&mut self, k: u32) -> ExprId {
        let mut l = self.c.st.level_zero();
        for _ in 0..k {
            l = self.c.st.level_succ(l);
        }
        self.c.st.mk_sort(l)
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
    fn def(&mut self, name: &str, ty: ExprId, value: ExprId) -> ExprId {
        let hints = Hints::Regular(1);
        self.add(name, ty, ConstKind::Defn { value, hints });
        self.k(name)
    }
    fn nf(&mut self, e: ExprId) -> ExprId {
        let r = self.c.read_back(e);
        assert!(self.c.fault().is_none(), "fault: {:?}", self.c.fault());
        r
    }
}

#[test]
fn beta_under_and_outside_binders() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    let b0 = t.bv(0);
    let id = t.lam("y", a, b0);
    let e = t.app(id, &[x]);
    assert_eq!(t.nf(e), x);
    // fun (z : A) => (fun y => y) z reads back as fun (z : A) => z.
    let inner = t.app(id, &[b0]);
    let e = t.lam("z", a, inner);
    let want = t.lam("z", a, b0);
    assert_eq!(t.nf(e), want);
}

#[test]
fn bound_variables_keep_their_indices() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let f = t.axiom("f", a);
    // fun (x : A) (y : A) => f x y, with f applied as a neutral head.
    let b0 = t.bv(0);
    let b1 = t.bv(1);
    let body = t.app(f, &[b1, b0]);
    let inner = t.lam("y", a, body);
    let e = t.lam("x", a, inner);
    assert_eq!(t.nf(e), e);
    let p = t.pi("x", a, a);
    assert_eq!(t.nf(p), p);
}

#[test]
fn let_is_zeta_reduced() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    let f = t.axiom("f", a);
    let b0 = t.bv(0);
    let body = t.app(f, &[b0]);
    let n = t.name("v");
    let e = t.c.st.mk_let(n, a, x, body);
    let want = t.app(f, &[x]);
    assert_eq!(t.nf(e), want);
}

#[test]
fn a_definition_reads_back_folded() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    let b0 = t.bv(0);
    let id = t.lam("y", a, b0);
    let ty = t.pi("y", a, a);
    let d = t.def("d", ty, id);
    let e = t.app(d, &[x]);
    assert_eq!(t.nf(e), e);
    // force unfolds the head, and then beta gives x.
    let v = t.c.eval(EnvId::NIL, e);
    let w = t.c.force(v);
    let r = t.c.quote(0, 0, w);
    assert!(t.c.fault().is_none());
    assert_eq!(r, x);
    // A second force uses the slot of the glued value.
    let w2 = t.c.force(v);
    assert_eq!(w2, w);
}

#[test]
fn projection_of_a_constructor_reduces() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
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
    let inner = t.pi("b", a, pr);
    let mk_ty = t.pi("a", a, inner);
    let ctor = CtorInfo {
        induct: pr_n,
        cidx: 0,
        nparams: 0,
        nfields: 2,
    };
    t.add("Pr.mk", mk_ty, ConstKind::Ctor(ctor));
    let x = t.axiom("x", a);
    let y = t.axiom("y", a);
    let mk = t.k("Pr.mk");
    let v = t.app(mk, &[x, y]);
    // The structure is behind a definition, so the projection must force it.
    let d = t.def("d", pr, v);
    let p1 = t.c.st.mk_proj(pr_n, 1, d);
    assert_eq!(t.nf(p1), y);
    // A projection of an axiom is stuck.
    let p = t.axiom("p", pr);
    let q0 = t.c.st.mk_proj(pr_n, 0, p);
    assert_eq!(t.nf(q0), q0);
}

#[test]
fn a_loose_bound_variable_is_a_fault() {
    let mut t = T::new();
    let b0 = t.bv(0);
    t.c.read_back(b0);
    assert_eq!(t.c.fault().map(|f| f.kind), Some(ErrorKind::LooseBVar));
}

#[test]
fn applying_a_sort_is_a_fault() {
    let mut t = T::new();
    let s0 = t.sort(0);
    let e = t.app(s0, &[s0]);
    t.c.read_back(e);
    assert_eq!(
        t.c.fault().map(|f| f.kind),
        Some(ErrorKind::FunctionExpected)
    );
}
