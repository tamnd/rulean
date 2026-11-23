//! Tests of the declaration checks of engine R. The expected verdicts follow `environment.cpp` and `quot.cpp` of the official kernel v4.35.0.

use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Axiom, Decl, Defn, Hints, Quot, QuotKind, Safety, Thm};
use rulean_store::{BinderInfo, ExprId, LevelId, NameId, Store};

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
    fn names(&mut self, ns: &[&str]) -> Vec<NameId> {
        let mut out = Vec::new();
        for n in ns {
            out.push(self.name(n));
        }
        out
    }
    fn sort(&mut self, k: u32) -> ExprId {
        let mut l = self.c.st.level_zero();
        for _ in 0..k {
            l = self.c.st.level_succ(l);
        }
        self.c.st.mk_sort(l)
    }
    fn param(&mut self, s: &str) -> LevelId {
        let n = self.name(s);
        self.c.st.level_param(n)
    }
    fn k(&mut self, s: &str) -> ExprId {
        let n = self.name(s);
        let ls = self.c.st.level_list_empty();
        self.c.st.mk_const(n, ls)
    }
    fn kl(&mut self, s: &str, ls: &[LevelId]) -> ExprId {
        let n = self.name(s);
        let ls = self.c.st.level_list(ls);
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
    fn axiom(&mut self, name: &str, lps: &[&str], ty: ExprId, safety: Safety) -> Decl {
        let name = self.name(name);
        let lparams = self.names(lps);
        Decl::Axiom(Axiom {
            name,
            lparams,
            ty,
            safety,
        })
    }
    fn defn(&mut self, name: &str, ty: ExprId, value: ExprId, safety: Safety) -> Defn {
        let name = self.name(name);
        let all = vec![name];
        Defn {
            name,
            lparams: Vec::new(),
            ty,
            value,
            hints: Hints::Regular(1),
            safety,
            all,
        }
    }
    fn add(&mut self, d: &Decl) -> Option<ErrorKind> {
        self.c.add_decl(d).map(|f| f.kind)
    }
    fn has(&mut self, s: &str) -> bool {
        let n = self.name(s);
        self.c.env.contains(n)
    }
    /// Declares `Nat : Type` and `Nat.zero : Nat` as axioms.
    fn nat(&mut self) -> (ExprId, ExprId) {
        let s1 = self.sort(1);
        let d = self.axiom("Nat", &[], s1, Safety::Safe);
        assert_eq!(self.add(&d), None);
        let nat = self.k("Nat");
        let d = self.axiom("Nat.zero", &[], nat, Safety::Safe);
        assert_eq!(self.add(&d), None);
        (nat, self.k("Nat.zero"))
    }
    /// The type `{α : Sort u} → α → α → Prop`.
    fn eq_type(&mut self) -> ExprId {
        let u = self.param("u");
        let su = self.c.st.mk_sort(u);
        let p = self.sort(0);
        let (b0, b1) = (self.bv(0), self.bv(1));
        let inner = self.pi("b", b1, p);
        let rel = self.pi("a", b0, inner);
        self.ipi("α", su, rel)
    }
    /// The type `{α : Sort u} → (a : α) → @Eq.{u} α a a`.
    fn eq_refl_type(&mut self) -> ExprId {
        let u = self.param("u");
        let su = self.c.st.mk_sort(u);
        let eq = self.kl("Eq", &[u]);
        let (b0, b1) = (self.bv(0), self.bv(1));
        let body = self.app(eq, &[b1, b0, b0]);
        let a = self.pi("a", b0, body);
        self.ipi("α", su, a)
    }
    /// Puts `Eq` and `Eq.refl` in the environment with the given types.
    fn eq(&mut self, eq_ty: ExprId, refl_ty: ExprId) {
        let eq = self.name("Eq");
        let refl = self.name("Eq.refl");
        let lps = self.names(&["u"]);
        self.c.env.add(ConstInfo {
            name: eq,
            lparams: lps.clone(),
            ty: eq_ty,
            safety: Safety::Safe,
            kind: ConstKind::Induct(InductInfo {
                nparams: 2,
                nindices: 1,
                all: vec![eq],
                ctors: vec![refl],
                nnested: 0,
                is_rec: false,
                is_reflexive: false,
            }),
        });
        self.c.env.add(ConstInfo {
            name: refl,
            lparams: lps,
            ty: refl_ty,
            safety: Safety::Safe,
            kind: ConstKind::Ctor(CtorInfo {
                induct: eq,
                cidx: 0,
                nparams: 2,
                nfields: 0,
            }),
        });
    }
    fn quot(&mut self, kind: QuotKind, name: &str, lps: &[&str], ty: ExprId) -> Decl {
        let name = self.name(name);
        let lparams = self.names(lps);
        Decl::Quot(Quot {
            name,
            lparams,
            ty,
            kind,
        })
    }
    /// `α → α → Prop`, where `α` is the bound variable `k`.
    fn relation(&mut self, k: u32) -> ExprId {
        let p = self.sort(0);
        let a1 = self.bv(k + 1);
        let inner = self.pi("b", a1, p);
        let a0 = self.bv(k);
        self.pi("a", a0, inner)
    }
    /// `{α : Sort u} → (α → α → Prop) → Sort u`.
    fn quot_type(&mut self) -> ExprId {
        let u = self.param("u");
        let su = self.c.st.mk_sort(u);
        let rel = self.relation(0);
        let inner = self.pi("r", rel, su);
        self.ipi("α", su, inner)
    }
    /// `{α : Sort u} → (r : α → α → Prop) → α → @Quot.{u} α r`.
    fn quot_mk_type(&mut self) -> ExprId {
        let u = self.param("u");
        let su = self.c.st.mk_sort(u);
        let rel = self.relation(0);
        let q = self.kl("Quot", &[u]);
        let (b1, b2) = (self.bv(1), self.bv(2));
        let qr = self.app(q, &[b2, b1]);
        let a = self.pi("a", b1, qr);
        let r = self.pi("r", rel, a);
        self.ipi("α", su, r)
    }
    /// `{α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ a b, r a b → f a = f b) → Quot r → β`.
    fn quot_lift_type(&mut self) -> ExprId {
        let u = self.param("u");
        let v = self.param("v");
        let su = self.c.st.mk_sort(u);
        let sv = self.c.st.mk_sort(v);
        let rel = self.relation(0);
        let (b0, b1, b2, b3, b4) = (self.bv(0), self.bv(1), self.bv(2), self.bv(3), self.bv(4));
        let f_ty = self.pi("x", b2, b1);
        let eq = self.kl("Eq", &[v]);
        let fa = self.app(b3, &[b2]);
        let fb = self.app(b3, &[b1]);
        let eq_ab = self.app(eq, &[b4, fa, fb]);
        let rab = self.app(b4, &[b1, b0]);
        let h = self.pi("h", rab, eq_ab);
        let all_b = self.pi("b", b4, h);
        let sanity = self.pi("a", b3, all_b);
        let q = self.kl("Quot", &[u]);
        let qr = self.app(q, &[b4, b3]);
        let last = self.pi("q", qr, b3);
        let s = self.pi("h", sanity, last);
        let f = self.pi("f", f_ty, s);
        let b = self.ipi("β", sv, f);
        let r = self.ipi("r", rel, b);
        self.ipi("α", su, r)
    }
    /// `{α : Sort u} → {r : α → α → Prop} → {β : Quot r → Prop} → (∀ a, β (Quot.mk r a)) → ∀ q, β q`.
    fn quot_ind_type(&mut self) -> ExprId {
        let u = self.param("u");
        let su = self.c.st.mk_sort(u);
        let rel = self.relation(0);
        let q = self.kl("Quot", &[u]);
        let mk = self.kl("Quot.mk", &[u]);
        let (b0, b1, b2, b3) = (self.bv(0), self.bv(1), self.bv(2), self.bv(3));
        let p = self.sort(0);
        let q2 = self.app(q, &[b1, b0]);
        let beta_ty = self.pi("q", q2, p);
        let mka = self.app(mk, &[b3, b2, b0]);
        let body = self.app(b1, &[mka]);
        let mk_ty = self.pi("a", b2, body);
        let q4 = self.app(q, &[b3, b2]);
        let bq = self.app(b2, &[b0]);
        let all_q = self.pi("q", q4, bq);
        let m = self.pi("mk", mk_ty, all_q);
        let b = self.ipi("β", beta_ty, m);
        let r = self.ipi("r", rel, b);
        self.ipi("α", su, r)
    }
}

#[test]
fn axiom_checks() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let d = t.axiom("A", &[], s1, Safety::Safe);
    assert_eq!(t.add(&d), None);
    assert!(t.has("A"));
    // The same name again.
    assert_eq!(t.add(&d), Some(ErrorKind::AlreadyDeclared));
    // Two level parameters with the same name.
    let u = t.param("u");
    let su = t.c.st.mk_sort(u);
    let d = t.axiom("B", &["u", "u"], su, Safety::Safe);
    assert_eq!(t.add(&d), Some(ErrorKind::DuplicateLevelParam));
    assert!(!t.has("B"));
    // A level parameter that is not declared.
    let d = t.axiom("C", &[], su, Safety::Safe);
    assert!(t.add(&d).is_some());
    assert!(!t.has("C"));
    // The type of a type is a sort, but an element of `A` is not a type.
    let a = t.k("A");
    let d = t.axiom("x", &[], a, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let x = t.k("x");
    let d = t.axiom("y", &[], x, Safety::Safe);
    assert_eq!(t.add(&d), Some(ErrorKind::TypeExpected));
    // A loose bound variable.
    let b0 = t.bv(0);
    let d = t.axiom("z", &[], b0, Safety::Safe);
    assert!(t.add(&d).is_some());
}

#[test]
fn definition_checks() {
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let b0 = t.bv(0);
    let idf = t.lam("n", nat, b0);
    let ty = t.pi("n", nat, nat);
    let d = t.defn("id", ty, idf, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(t.has("id"));
    // The value has the type `Nat`, not `Nat → Nat`.
    let d = t.defn("bad", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(!t.has("bad"));
    // A safe definition may not refer to itself.
    let me = t.k("me");
    let d = t.defn("me", nat, me, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::UnknownConst));
    assert!(!t.has("me"));
}

#[test]
fn theorem_checks() {
    let mut t = T::new();
    let p = t.sort(0);
    let d = t.axiom("P", &[], p, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let pc = t.k("P");
    let d = t.axiom("h", &[], pc, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let h = t.k("h");
    let name = t.name("thm");
    let thm = Decl::Thm(Thm {
        name,
        lparams: Vec::new(),
        ty: pc,
        value: h,
        all: vec![name],
    });
    assert_eq!(t.add(&thm), None);
    // The type `Prop` is a type, but it is not a proposition.
    let name = t.name("thm2");
    let thm = Decl::Thm(Thm {
        name,
        lparams: Vec::new(),
        ty: p,
        value: pc,
        all: vec![name],
    });
    assert_eq!(t.add(&thm), Some(ErrorKind::TheoremNotProp));
    assert!(!t.has("thm2"));
}

#[test]
fn unsafe_and_partial_separation() {
    let mut t = T::new();
    let (nat, zero) = t.nat();
    // An unsafe definition may refer to itself.
    let lp = t.k("loop");
    let d = t.defn("loop", nat, lp, Safety::Unsafe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(t.has("loop"));
    // A safe definition may not refer to an unsafe constant.
    let d = t.defn("s", nat, lp, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::UnsafeUse));
    // An unsafe definition with a bad value is not added, and its header is removed.
    let ty = t.pi("n", nat, nat);
    let d = t.defn("u2", ty, zero, Safety::Unsafe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(!t.has("u2"));
    // A partial definition is checked as a safe one.
    let d = t.defn("p", nat, zero, Safety::Partial);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let pc = t.k("p");
    let d = t.defn("s2", nat, pc, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::PartialUse));
    // A partial definition may not refer to an unsafe constant.
    let d = t.defn("p2", nat, lp, Safety::Partial);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::UnsafeUse));
    // An unsafe axiom may refer to an unsafe constant, and a safe axiom may not.
    let s1 = t.sort(1);
    let d = t.defn("UT", s1, nat, Safety::Unsafe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let ut = t.k("UT");
    let d = t.axiom("ua", &[], ut, Safety::Unsafe);
    assert_eq!(t.add(&d), None);
    let d = t.axiom("sa", &[], ut, Safety::Safe);
    assert_eq!(t.add(&d), Some(ErrorKind::UnsafeUse));
    // A theorem may not refer to an unsafe constant or to a partial constant.
    let prop = t.sort(0);
    let d = t.axiom("uq", &[], prop, Safety::Unsafe);
    assert_eq!(t.add(&d), None);
    let uq = t.k("uq");
    let d = t.axiom("q", &[], prop, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let q = t.k("q");
    let d = t.axiom("hq", &[], q, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let hq = t.k("hq");
    let d = t.defn("pq", prop, q, Safety::Partial);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let pq = t.k("pq");
    for (n, ty, want) in [
        ("th1", uq, ErrorKind::UnsafeUse),
        ("th2", pq, ErrorKind::PartialUse),
    ] {
        let name = t.name(n);
        let thm = Decl::Thm(Thm {
            name,
            lparams: Vec::new(),
            ty,
            value: hq,
            all: vec![name],
        });
        assert_eq!(t.add(&thm), Some(want), "{n}");
        assert!(!t.has(n));
    }
}

/// The partial block `f n := g n` and `g n := f n` of type `Nat → Nat`.
fn mutual_pair(t: &mut T) -> (Defn, Defn, ExprId) {
    let (nat, zero) = t.nat();
    let ty = t.pi("n", nat, nat);
    let f = t.k("f");
    let g = t.k("g");
    let b0 = t.bv(0);
    let gn = t.app(g, &[b0]);
    let fv = t.lam("n", nat, gn);
    let fnn = t.app(f, &[b0]);
    let gv = t.lam("n", nat, fnn);
    let mut df = t.defn("f", ty, fv, Safety::Partial);
    let mut dg = t.defn("g", ty, gv, Safety::Partial);
    let all = vec![df.name, dg.name];
    df.all = all.clone();
    dg.all = all;
    (df, dg, zero)
}

fn mutual(t: &mut T, ds: &[Defn]) -> Option<ErrorKind> {
    t.c.add_mutual(ds).map(|x| x.kind)
}

#[test]
fn mutual_definitions() {
    let mut t = T::new();
    let (df, dg, zero) = mutual_pair(&mut t);
    // The block is rejected before any change: a safe block, an empty block, mixed safety, a duplicate name and different level parameters.
    let mut sf = df.clone();
    sf.safety = Safety::Safe;
    assert_eq!(mutual(&mut t, &[sf]), Some(ErrorKind::BadMutual));
    assert_eq!(mutual(&mut t, &[]), Some(ErrorKind::BadMutual));
    let mut ug = dg.clone();
    ug.safety = Safety::Unsafe;
    assert_eq!(
        mutual(&mut t, &[df.clone(), ug]),
        Some(ErrorKind::BadMutual)
    );
    assert_eq!(
        mutual(&mut t, &[df.clone(), df.clone()]),
        Some(ErrorKind::BadMutual)
    );
    let mut lg = dg.clone();
    lg.lparams = t.names(&["u"]);
    assert_eq!(
        mutual(&mut t, &[df.clone(), lg]),
        Some(ErrorKind::BadMutual)
    );
    assert!(!t.has("f") && !t.has("g"));
    // A bad value removes all the members of the block.
    let mut bg = dg.clone();
    bg.value = zero;
    assert_eq!(
        mutual(&mut t, &[df.clone(), bg]),
        Some(ErrorKind::DefTypeMismatch)
    );
    assert!(!t.has("f") && !t.has("g"));
    assert_eq!(t.c.env.len(), 2);
    // The good block is accepted, and the members refer to each other.
    assert_eq!(mutual(&mut t, &[df, dg]), None);
    assert!(t.has("f") && t.has("g"));
}

#[test]
fn a_mutual_declaration_goes_to_add_mutual() {
    let mut t = T::new();
    let (df, dg, _) = mutual_pair(&mut t);
    assert_eq!(
        t.add(&Decl::Mutual(vec![df.clone(), df.clone()])),
        Some(ErrorKind::BadMutual)
    );
    assert_eq!(t.add(&Decl::Mutual(vec![df.clone(), dg.clone()])), None);
    assert!(t.has("f") && t.has("g"));
    // A safe definition cannot use a partial constant.
    let f = t.k("f");
    let mut h = t.defn("h", df.ty, f, Safety::Safe);
    h.all = vec![h.name];
    assert!(t.add(&Decl::Defn(h)).is_some());
    assert!(!t.has("h"));
}

#[test]
fn quotient_initialization() {
    let mut t = T::new();
    let eq_ty = t.eq_type();
    let refl_ty = t.eq_refl_type();
    t.eq(eq_ty, refl_ty);
    let qt = t.quot_type();
    let qmk = t.quot_mk_type();
    let qlift = t.quot_lift_type();
    let qind = t.quot_ind_type();
    let d = t.quot(QuotKind::Type, "Quot", &["u"], qt);
    assert_eq!(t.add(&d), None);
    assert!(t.c.env.quot_initialized());
    assert!(t.has("Quot") && t.has("Quot.mk") && t.has("Quot.lift") && t.has("Quot.ind"));
    let d = t.quot(QuotKind::Ctor, "Quot.mk", &["u"], qmk);
    assert_eq!(t.add(&d), None);
    let d = t.quot(QuotKind::Lift, "Quot.lift", &["u", "v"], qlift);
    assert_eq!(t.add(&d), None);
    let d = t.quot(QuotKind::Ind, "Quot.ind", &["u"], qind);
    assert_eq!(t.add(&d), None);
    // The reference types check.
    let tys = [qt, qmk, qlift, qind];
    let lps = [vec!["u"], vec!["u"], vec!["u", "v"], vec!["u"]];
    for i in 0..4 {
        let ls = t.names(&lps[i]);
        t.c.begin(ls, Safety::Safe);
        let s = t.c.check(tys[i]);
        t.c.ensure_sort(s, tys[i]);
        assert!(t.c.fault().is_none(), "type {i}");
    }
    // An exported declaration that is not the reference is rejected.
    let d = t.quot(QuotKind::Ctor, "Quot.mk", &["u"], qt);
    assert_eq!(t.add(&d), Some(ErrorKind::BadQuot));
    let d = t.quot(QuotKind::Lift, "Quot.lift", &["u"], qlift);
    assert_eq!(t.add(&d), Some(ErrorKind::BadQuot));
    let d = t.quot(QuotKind::Ind, "Quot.mk", &["u"], qind);
    assert_eq!(t.add(&d), Some(ErrorKind::BadQuot));
}

#[test]
fn quotient_needs_eq() {
    // No `Eq`.
    let mut t = T::new();
    let qt = t.quot_type();
    let d = t.quot(QuotKind::Type, "Quot", &["u"], qt);
    assert!(t.add(&d).is_some());
    assert!(!t.c.env.quot_initialized());
    assert!(!t.has("Quot"));
    // `Eq` with the wrong type.
    let mut t = T::new();
    let refl_ty = t.eq_refl_type();
    let s1 = t.sort(1);
    t.eq(s1, refl_ty);
    let qt = t.quot_type();
    let d = t.quot(QuotKind::Type, "Quot", &["u"], qt);
    assert_eq!(t.add(&d), Some(ErrorKind::BadQuot));
    // `Eq.refl` with the wrong type.
    let mut t = T::new();
    let eq_ty = t.eq_type();
    t.eq(eq_ty, eq_ty);
    let qt = t.quot_type();
    let d = t.quot(QuotKind::Type, "Quot", &["u"], qt);
    assert_eq!(t.add(&d), Some(ErrorKind::BadQuot));
    // A name of the quotient is already taken.
    let mut t = T::new();
    let eq_ty = t.eq_type();
    let refl_ty = t.eq_refl_type();
    t.eq(eq_ty, refl_ty);
    let s1 = t.sort(1);
    let d = t.axiom("Quot.lift", &[], s1, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let qt = t.quot_type();
    let d = t.quot(QuotKind::Type, "Quot", &["u"], qt);
    assert_eq!(t.add(&d), Some(ErrorKind::AlreadyDeclared));
    assert!(!t.has("Quot"));
}

#[test]
fn definitions_use_the_scratch_tier() {
    use rulean_store::Tier;
    let mut t = T::new();
    let (nat, zero) = t.nat();
    // `fun (f : Nat → Nat) (n : Nat) => f (f n)`: the check makes free variables and the inferred type.
    let nn = t.pi("n", nat, nat);
    let (b0, b1) = (t.bv(0), t.bv(1));
    let inner = t.app(b1, &[b0]);
    let body = t.app(b1, &[inner]);
    let lam_n = t.lam("n", nat, body);
    let value = t.lam("f", nn, lam_n);
    let ty = t.pi("f", nn, nn);
    let d = t.defn("twice", ty, value, Safety::Safe);
    let before = t.c.st.expr_total();
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(t.has("twice"));
    // The terms of the check are gone, and the frozen tier did not grow.
    assert_eq!(t.c.st.scratch_total(), 0);
    assert!(!t.c.st.uses_scratch());
    assert_eq!(t.c.st.expr_total(), before);
    // A fault at a scratch term points to a frozen term after the call.
    let twice = t.k("twice");
    let bad_value = t.app(twice, &[zero]);
    let d = t.defn("bad", nat, bad_value, Safety::Safe);
    let f = t.c.add_decl(&Decl::Defn(d)).expect("the check fails");
    assert_eq!(f.kind, ErrorKind::AppTypeMismatch);
    assert_eq!(f.at.tier(), Tier::Frozen);
    assert_eq!(t.c.st.scratch_total(), 0);
}

/// `(fun (T : Type) => T) Nat`: a frozen closed type that is not in normal form.
fn id_type_of(t: &mut T, nat: ExprId) -> ExprId {
    let s1 = t.sort(1);
    let b0 = t.bv(0);
    let idt = t.lam("T", s1, b0);
    t.app(idt, &[nat])
}

#[test]
fn session_keeps_judgments_across_declarations() {
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let ty = id_type_of(&mut t, nat);
    let d = t.defn("a", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(!t.c.sess.is_empty());
    let hits = t.c.sess.stats.hits;
    // The second declaration asks the same question, and the session has the answer.
    let d = t.defn("b", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(t.c.sess.stats.hits > hits);
}

#[test]
fn session_keeps_nothing_from_a_failed_declaration() {
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let ty = id_type_of(&mut t, nat);
    // `zero` does not have the type `(fun T => T) Nat → Nat`.
    let fty = t.pi("n", ty, nat);
    let d = t.defn("bad", fty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(t.c.sess.is_empty());
    assert_eq!(t.c.sess.stats.stores, 0);
}

#[test]
fn session_off_keeps_nothing() {
    let mut t = T::new();
    t.c.sess.on = false;
    let (nat, zero) = t.nat();
    let ty = id_type_of(&mut t, nat);
    let d = t.defn("a", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let d = t.defn("b", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    assert!(t.c.sess.is_empty());
    assert_eq!(t.c.sess.stats.hits, 0);
}
