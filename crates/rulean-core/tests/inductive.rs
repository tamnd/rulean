//! Tests of the inductive checks of engine R. The expected verdicts follow `inductive.cpp` of the official kernel v4.35.0.

use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Ctor, Decl, Induct, InductType, Rec, RecRule, Safety};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

struct T {
    c: Checker,
}

impl T {
    fn new() -> T {
        T {
            c: Checker::new(Store::new()),
        }
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
    fn ipi(&mut self, n: &str, ty: ExprId, body: ExprId) -> ExprId {
        let n = self.name(n);
        self.c.st.mk_pi(n, BinderInfo::Implicit, ty, body)
    }
    /// One type `name : ty` with no parameters, no indices and the constructors `ctors`.
    fn ind_type(&mut self, name: &str, ty: ExprId, nparams: u32, ctors: &[&str]) -> InductType {
        let n = self.name(name);
        let mut cs = Vec::new();
        for c in ctors {
            cs.push(self.name(c));
        }
        InductType {
            name: n,
            lparams: Vec::new(),
            ty,
            num_params: nparams,
            num_indices: 0,
            all: vec![n],
            ctors: cs,
            num_nested: 0,
            is_rec: false,
            is_reflexive: false,
            safety: Safety::Safe,
        }
    }
    fn ctor(
        &mut self,
        name: &str,
        ty: ExprId,
        induct: &str,
        cidx: u32,
        nparams: u32,
        nfields: u32,
    ) -> Ctor {
        Ctor {
            name: self.name(name),
            lparams: Vec::new(),
            ty,
            induct: self.name(induct),
            cidx,
            num_params: nparams,
            num_fields: nfields,
            safety: Safety::Safe,
        }
    }
    fn add(
        &mut self,
        types: Vec<InductType>,
        ctors: Vec<Ctor>,
        recs: Vec<Rec>,
    ) -> Option<ErrorKind> {
        let d = Decl::Induct(Induct { types, ctors, recs });
        self.c.add_decl(&d).map(|f| f.kind)
    }
}

/// The block of `B : Type` with the constructors `B.f` and `B.t`, and the exported recursor with the value `k` for the K flag.
fn two_ctor_block(t: &mut T, k: bool) -> (Vec<InductType>, Vec<Ctor>, Vec<Rec>) {
    let ty = t.sort(1);
    let b = t.k("B");
    let ity = t.ind_type("B", ty, 0, &["B.f", "B.t"]);
    let c0 = t.ctor("B.f", b, "B", 0, 0, 0);
    let c1 = t.ctor("B.t", b, "B", 1, 0, 0);
    // B.rec.{u} : {motive : B -> Sort u} -> motive B.f -> motive B.t -> (t : B) -> motive t
    let u = t.name("u");
    let lu = t.c.st.level_param(u);
    let su = t.c.st.mk_sort(lu);
    let motive_ty = t.pi("t", b, su);
    let bf = t.k("B.f");
    let bt = t.k("B.t");
    let v0 = t.bv(0);
    let v1 = t.bv(1);
    let v3 = t.bv(3);
    let m_f = t.app(v0, &[bf]);
    let m_t = t.app(v1, &[bt]);
    let m_major = t.app(v3, &[v0]);
    let body = t.pi("t", b, m_major);
    let body = t.pi("t", m_t, body);
    let body = t.pi("f", m_f, body);
    let rec_ty = t.ipi("motive", motive_ty, body);
    let mut rules = Vec::new();
    let r0 = t.lam("t", m_t, v1);
    let r0 = t.lam("f", m_f, r0);
    let r0 = t.lam("motive", motive_ty, r0);
    rules.push(RecRule {
        ctor: t.name("B.f"),
        nfields: 0,
        rhs: r0,
    });
    let r1 = t.lam("t", m_t, v0);
    let r1 = t.lam("f", m_f, r1);
    let r1 = t.lam("motive", motive_ty, r1);
    rules.push(RecRule {
        ctor: t.name("B.t"),
        nfields: 0,
        rhs: r1,
    });
    let rec = Rec {
        name: t.name("B.rec"),
        lparams: vec![u],
        ty: rec_ty,
        all: vec![t.name("B")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 2,
        k,
        rules,
        safety: Safety::Safe,
    };
    (vec![ity], vec![c0, c1], vec![rec])
}

#[test]
fn enum_type_is_accepted() {
    let mut t = T::new();
    let (types, ctors, recs) = two_ctor_block(&mut t, false);
    assert_eq!(t.add(types, ctors, recs), None);
    let rec = t.name("B.rec");
    assert!(t.c.env.contains(rec));
}

#[test]
fn wrong_k_flag_is_rejected() {
    let mut t = T::new();
    let (types, ctors, recs) = two_ctor_block(&mut t, true);
    assert_eq!(t.add(types, ctors, recs), Some(ErrorKind::ExportMismatch));
    // A rejected block adds nothing to the environment.
    let b = t.name("B");
    assert!(!t.c.env.contains(b));
}

#[test]
fn missing_recursor_is_rejected() {
    let mut t = T::new();
    let (types, ctors, _) = two_ctor_block(&mut t, false);
    assert_eq!(
        t.add(types, ctors, Vec::new()),
        Some(ErrorKind::ExportMismatch)
    );
}

#[test]
fn empty_block_is_rejected() {
    let mut t = T::new();
    assert_eq!(
        t.add(Vec::new(), Vec::new(), Vec::new()),
        Some(ErrorKind::BadInductive)
    );
}

#[test]
fn negative_occurrence_is_rejected() {
    // inductive N : Type | mk : (N -> N) -> N
    let mut t = T::new();
    let ty = t.sort(1);
    let n = t.k("N");
    let ity = t.ind_type("N", ty, 0, &["N.mk"]);
    let f = t.pi("x", n, n);
    let cty = t.pi("f", f, n);
    let c = t.ctor("N.mk", cty, "N", 0, 0, 1);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::NonPositive)
    );
}

#[test]
fn field_in_a_larger_universe_is_rejected() {
    // inductive U : Type | mk : Type -> U
    let mut t = T::new();
    let ty = t.sort(1);
    let u = t.k("U");
    let ity = t.ind_type("U", ty, 0, &["U.mk"]);
    let cty = t.pi("a", ty, u);
    let c = t.ctor("U.mk", cty, "U", 0, 0, 1);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::UniverseTooBig)
    );
}

#[test]
fn constructor_with_a_foreign_result_is_rejected() {
    // inductive A : Type | mk : A -> Prop
    let mut t = T::new();
    let ty = t.sort(1);
    let prop = t.sort(0);
    let a = t.k("A");
    let ity = t.ind_type("A", ty, 0, &["A.mk"]);
    let cty = t.pi("x", a, prop);
    let c = t.ctor("A.mk", cty, "A", 0, 0, 1);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::BadCtor)
    );
}

#[test]
fn non_uniform_parameter_is_rejected() {
    // inductive P (a : Type) : Type | mk : (a : Prop) -> P Prop. The official kernel checks the uniform occurrences before the constructor parameters.
    let mut t = T::new();
    let ty = t.sort(1);
    let prop = t.sort(0);
    let ity_ty = t.pi("a", ty, ty);
    let ity = t.ind_type("P", ity_ty, 1, &["P.mk"]);
    let p = t.k("P");
    let res = t.app(p, &[prop]);
    let cty = t.pi("a", prop, res);
    let c = t.ctor("P.mk", cty, "P", 0, 1, 0);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::NonUniformOcc)
    );
}

#[test]
fn type_that_is_not_a_sort_is_rejected() {
    // The type of S is a lambda, so it is not a sort and not a pi.
    let mut t = T::new();
    let ty = t.sort(1);
    let lam_ty = t.lam("x", ty, ty);
    let ity = t.ind_type("S", lam_ty, 0, &[]);
    assert!(t.add(vec![ity], Vec::new(), Vec::new()).is_some());
}
