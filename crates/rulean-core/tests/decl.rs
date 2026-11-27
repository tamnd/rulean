//! Tests of the declaration checks of engine R. The expected verdicts follow `environment.cpp` and `quot.cpp` of the official kernel v4.35.0.

use rulean_core::conv::Engine;
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
    // The axioms of `nat` are accepted, so their check-mode entries can be in the session already.
    let stores = t.c.sess.stats.stores;
    let d = t.defn("bad", fty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert_eq!(t.c.sess.stats.stores, stores);
}

#[test]
fn session_keeps_check_mode_judgments_of_safe_declarations() {
    let mut t = T::new();
    let (nat, _) = t.nat();
    let ty = id_type_of(&mut t, nat);
    let d = t.axiom("a", &[], ty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let hits = t.c.sess.stats.hits;
    // The check of the type of the second axiom is the same check, and the session has the answer.
    let d = t.axiom("b", &[], ty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    assert!(t.c.sess.stats.hits > hits);
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

/// A checker with engine F (spec 05.4.5).
fn engine_f(confirm_all: bool) -> T {
    let mut t = T::new();
    t.c.engine = Engine::F;
    t.c.confirm_all = confirm_all;
    t
}

/// Adds definitions that engine F inference accepts: a lambda, a `let` with a beta step, and a type with a beta step. It gives the number of declarations, with the two axioms of `nat`.
fn f_accepts(t: &mut T) -> u64 {
    let (nat, zero) = t.nat();
    let b0 = t.bv(0);
    let idf = t.lam("n", nat, b0);
    let ty = t.pi("n", nat, nat);
    let d = t.defn("id", ty, idf, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // `let x : Nat := Nat.zero; (fun y : Nat => y) x`
    let app = t.app(idf, &[b0]);
    let x = t.name("x");
    let v = t.c.st.mk_let(x, nat, zero, app);
    let d = t.defn("z1", nat, v, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // The type `(fun T : Type => T) Nat`.
    let s1 = t.sort(1);
    let tid = t.lam("T", s1, b0);
    let ty = t.app(tid, &[nat]);
    let d = t.defn("z2", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    5
}

#[test]
fn engine_f_checks_types_and_values() {
    let mut t = engine_f(false);
    let n = f_accepts(&mut t);
    assert!(t.has("z2"));
    let s = t.c.f_stats;
    // A value check of each definition. The types are not deep, so engine R checks them (spec perf/11.19).
    assert_eq!(s.infer, n - 2);
    assert_eq!(s.infer_ok, s.infer);
    assert_eq!(s.disagree, 0);
}

#[test]
fn engine_f_checks_a_deep_type() {
    let mut t = engine_f(false);
    let (nat, _) = t.nat();
    // `Nat -> Nat -> ... -> Nat` with 70 binders. The chain is deeper than `F_DEEP`, so engine F checks the type.
    let mut ty = nat;
    for _ in 0..70 {
        ty = t.pi("n", nat, ty);
    }
    let before = t.c.f_stats.infer;
    let d = t.axiom("f", &[], ty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    assert_eq!(t.c.f_stats.infer, before + 1);
    assert_eq!(t.c.f_stats.infer_ok, t.c.f_stats.infer);
}

#[test]
fn engine_f_with_confirm_all_agrees_with_engine_r() {
    let mut t = engine_f(true);
    let n = f_accepts(&mut t);
    let s = t.c.f_stats;
    assert_eq!(s.infer, n - 2);
    assert_eq!(s.infer_ok, s.infer);
    assert_eq!(s.disagree, 0);
}

/// The type of a lambda in engine F is compared with a pi type under the local of the lambda, before its read-back (spec perf/04.5). The cases are nested lambdas, a declared type that unfolds to a pi type, a lambda as an argument, and a lambda with the wrong domain.
#[test]
fn engine_f_compares_the_type_of_a_lambda_before_read_back() {
    let mut t = engine_f(false);
    let (nat, zero) = t.nat();
    // `K : Nat → Nat → Nat := fun a b => a`.
    let b1 = t.bv(1);
    let inner = t.lam("b", nat, b1);
    let kv = t.lam("a", nat, inner);
    let nn = t.pi("b", nat, nat);
    let kty = t.pi("a", nat, nn);
    let d = t.defn("K", kty, kv, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // `Fn : Type := Nat → Nat` and `f : Fn := fun n => n`.
    let s1 = t.sort(1);
    let d = t.defn("Fn", s1, nn, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let fnc = t.k("Fn");
    let b0 = t.bv(0);
    let idf = t.lam("n", nat, b0);
    let d = t.defn("f", fnc, idf, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // `ap : (Nat → Nat) → Nat → Nat` and `v : Nat := ap (fun n => n) Nat.zero`.
    let apty = t.pi("g", nn, nn);
    let d = t.axiom("ap", &[], apty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let ap = t.k("ap");
    let v = t.app(ap, &[idf, zero]);
    let d = t.defn("v", nat, v, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let s = t.c.f_stats;
    assert_eq!(s.infer_ok, s.infer);
    // `bad : Nat → Nat := fun (g : Nat → Nat) => Nat.zero`: the domains are not equal.
    let lam_bad = t.lam("g", nn, zero);
    let d = t.defn("bad", nn, lam_bad, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(!t.has("bad"));
    assert_eq!(t.c.f_stats.disagree, 0);
}

/// Each lambda has its own local in engine F inference. In `fun a b => refl b`, the inner lambda has no loose bound variable, so it is inferred in the root context. Before the fix, it got the local of `a`, and engine F found `P b b` equal to `P a b`.
#[test]
fn engine_f_gives_each_lambda_its_own_local() {
    let mut t = engine_f(false);
    let (nat, _) = t.nat();
    // `P : Nat → Nat → Type` and `refl : (n : Nat) → P n n`.
    let s1 = t.sort(1);
    let ns = t.pi("m", nat, s1);
    let pty = t.pi("n", nat, ns);
    let d = t.axiom("P", &[], pty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let p = t.k("P");
    let b0 = t.bv(0);
    let b1 = t.bv(1);
    let pnn = t.app(p, &[b0, b0]);
    let rty = t.pi("n", nat, pnn);
    let d = t.axiom("refl", &[], rty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let refl = t.k("refl");
    let rb = t.app(refl, &[b0]);
    let inner = t.lam("b", nat, rb);
    let v = t.lam("a", nat, inner);
    // `ok : (a b : Nat) → P b b := fun a b => refl b`.
    let pbb = t.app(p, &[b0, b0]);
    let ty_ok_in = t.pi("b", nat, pbb);
    let ty_ok = t.pi("a", nat, ty_ok_in);
    let d = t.defn("ok", ty_ok, v, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // `bad : (a b : Nat) → P a b := fun a b => refl b`.
    let pab = t.app(p, &[b1, b0]);
    let ty_bad_in = t.pi("b", nat, pab);
    let ty_bad = t.pi("a", nat, ty_bad_in);
    let d = t.defn("bad", ty_bad, v, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(!t.has("bad"));
    assert_eq!(t.c.f_stats.disagree, 0);
}

#[test]
fn engine_f_gives_the_errors_of_engine_r() {
    let mut t = engine_f(false);
    let (nat, zero) = t.nat();
    let ty = t.pi("n", nat, nat);
    // The value has the type `Nat`, not `Nat → Nat`.
    let d = t.defn("bad", ty, zero, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), Some(ErrorKind::DefTypeMismatch));
    assert!(!t.has("bad"));
    // An element of `Nat` is not a type.
    let d = t.axiom("y", &[], zero, Safety::Safe);
    assert_eq!(t.add(&d), Some(ErrorKind::TypeExpected));
    // The value of the `let` has the type `Nat → Nat`, not `Nat`.
    let b0 = t.bv(0);
    let idf = t.lam("n", nat, b0);
    let x = t.name("x");
    let v = t.c.st.mk_let(x, nat, idf, zero);
    let d = t.defn("bad2", nat, v, Safety::Safe);
    assert!(t.add(&Decl::Defn(d)).is_some());
    assert!(!t.has("bad2"));
    // A loose bound variable.
    let d = t.defn("bad3", nat, b0, Safety::Safe);
    assert!(t.add(&Decl::Defn(d)).is_some());
    assert!(!t.has("bad3"));
    let s = t.c.f_stats;
    assert_eq!(s.disagree, 0);
    // Engine F accepts no value. No type is deep, so engine F checks no type (spec perf/11.19).
    assert_eq!(s.infer_ok, 0);
}

#[test]
fn engine_f_continues_after_engine_r_confirms_a_query() {
    let mut t = engine_f(false);
    let (nat, _) = t.nat();
    // `P : Prop`, `p q : P`, `C : P → Type`, `c : C p` and `D : P → Type := fun h => C h`.
    let s0 = t.sort(0);
    let s1 = t.sort(1);
    let d = t.axiom("P", &[], s0, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let pp = t.k("P");
    for n in ["p", "q"] {
        let d = t.axiom(n, &[], pp, Safety::Safe);
        assert_eq!(t.add(&d), None);
    }
    let (p, q) = (t.k("p"), t.k("q"));
    let cty = t.pi("h", pp, s1);
    let d = t.axiom("C", &[], cty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let cc = t.k("C");
    let cp = t.app(cc, &[p]);
    let d = t.axiom("c", &[], cp, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let b0 = t.bv(0);
    let ch = t.app(cc, &[b0]);
    let dv = t.lam("h", pp, ch);
    let d = t.defn("D", cty, dv, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    // `g : D q → Nat` and `v : Nat := g c`. The check of the argument `c` unfolds `D` (a delta step) and compares `p` and `q` by proof irrelevance (a type-directed rule). So the answer is in the confirm set of spec 05.1, and engine R confirms it.
    let dd = t.k("D");
    let dq = t.app(dd, &[q]);
    let gty = t.pi("x", dq, nat);
    let d = t.axiom("g", &[], gty, Safety::Safe);
    assert_eq!(t.add(&d), None);
    let g = t.k("g");
    let c = t.k("c");
    let gc = t.app(g, &[c]);
    let before = t.c.f_stats;
    let d = t.defn("v", nat, gc, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let s = t.c.f_stats;
    // Engine F accepts the value of `v`. It does not stop on the answer in the confirm set. The type is not deep, so engine R checks it.
    assert_eq!(s.infer - before.infer, 1);
    assert_eq!(s.infer_ok - before.infer_ok, 1);
    assert!(s.confirmed > before.confirmed);
    assert_eq!(s.disagree, 0);
}

#[test]
fn engine_f_checks_a_long_let_chain() {
    // The checker recurses on the depth of the terms, so the test runs in a thread with a large stack.
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(long_let_chain)
        .expect("the thread starts")
        .join()
        .expect("the checker does not panic");
}

fn long_let_chain() {
    let mut t = engine_f(false);
    let (nat, zero) = t.nat();
    // `let x : Nat := Nat.zero; let x : Nat := x; ...; x` with 5000 `let` terms.
    let x = t.name("x");
    let b0 = t.bv(0);
    let mut v = b0;
    for _ in 1..5000 {
        v = t.c.st.mk_let(x, nat, b0, v);
    }
    v = t.c.st.mk_let(x, nat, zero, v);
    let d = t.defn("chain", nat, v, Safety::Safe);
    assert_eq!(t.add(&Decl::Defn(d)), None);
    let s = t.c.f_stats;
    // Engine F checks the value. The types are not deep, so engine R checks them.
    assert_eq!(s.infer, 1);
    assert_eq!(s.infer_ok, s.infer);
}

/// Adds the definitions `a0 : Nat := Nat.zero`, `a1`, and so on, up to `n` of them. The result is the index and the error of the first definition that fails.
fn add_many(t: &mut T, nat: ExprId, zero: ExprId, n: usize) -> Option<(usize, ErrorKind)> {
    for i in 0..n {
        let d = t.defn(&format!("a{i}"), nat, zero, Safety::Safe);
        if let Some(e) = t.add(&Decl::Defn(d)) {
            return Some((i, e));
        }
    }
    None
}

#[test]
fn memory_budget_stops_the_check() {
    let mut t = T::new();
    assert_eq!(t.c.max_memory(), usize::MAX);
    assert!(!t.c.over_memory());
    let (nat, zero) = t.nat();
    assert_eq!(add_many(&mut t, nat, zero, 5000), None);
    // A budget below the memory that the checker already uses stops the check at the next memory check.
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let m = t.c.memory();
    assert!(m > 0);
    t.c.set_max_memory(m / 2);
    assert_eq!(t.c.st.max_bytes(), m / 2);
    assert!(t.c.over_memory());
    match add_many(&mut t, nat, zero, 5000) {
        Some((_, e)) => assert_eq!(e, ErrorKind::MemoryLimit),
        None => panic!("the budget did not stop the check"),
    }
    // A budget above the memory of the check changes nothing.
    let mut t = T::new();
    t.c.set_max_memory(1 << 30);
    let (nat, zero) = t.nat();
    assert_eq!(add_many(&mut t, nat, zero, 5000), None);
    assert!(t.c.memory() < 1 << 30);
}

#[test]
fn heartbeat_limit_stops_the_check() {
    // The count of a declaration without a limit.
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let d = Decl::Defn(t.defn("a", nat, zero, Safety::Safe));
    assert_eq!(t.c.max_heartbeat, 0);
    assert_eq!(t.add(&d), None);
    let h = t.c.heartbeats();
    assert!(h > 1, "the check counts {h} heartbeats");
    // The count starts at 0 for each declaration.
    let d2 = Decl::Defn(t.defn("b", nat, zero, Safety::Safe));
    assert_eq!(t.add(&d2), None);
    assert!(t.c.heartbeats() <= h);
    // The limit `h` is sufficient, and the limit `h - 1` gives `Heartbeat`.
    let mut t = T::new();
    let (nat, zero) = t.nat();
    t.c.max_heartbeat = h;
    let d = Decl::Defn(t.defn("a", nat, zero, Safety::Safe));
    assert_eq!(t.add(&d), None);
    let mut t = T::new();
    let (nat, zero) = t.nat();
    t.c.max_heartbeat = h - 1;
    let d = Decl::Defn(t.defn("a", nat, zero, Safety::Safe));
    assert_eq!(t.add(&d), Some(ErrorKind::Heartbeat));
}

#[test]
fn recursion_depth_limit_stops_the_check() {
    // `Nat.succ (Nat.succ ... Nat.zero)` with `n` applications.
    fn deep(t: &mut T, nat: ExprId, zero: ExprId, n: usize) -> ExprId {
        let pi = t.pi("n", nat, nat);
        let d = t.axiom("Nat.succ", &[], pi, Safety::Safe);
        assert_eq!(t.add(&d), None);
        let succ = t.k("Nat.succ");
        let mut e = zero;
        for _ in 0..n {
            e = t.app(succ, &[e]);
        }
        e
    }
    // Without a limit, the check accepts the term.
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let e = deep(&mut t, nat, zero, 200);
    assert_eq!(t.c.max_rec_depth, 0);
    let d = Decl::Defn(t.defn("a", nat, e, Safety::Safe));
    assert_eq!(t.add(&d), None);
    // The limit is 16 times `max_rec_depth`, as in the C++ kernel. A limit of 160 is not sufficient for 200 applications, and a limit of 320 is sufficient.
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let e = deep(&mut t, nat, zero, 200);
    t.c.max_rec_depth = 10;
    let d = Decl::Defn(t.defn("a", nat, e, Safety::Safe));
    assert_eq!(t.add(&d), Some(ErrorKind::DeepRecursion));
    let mut t = T::new();
    let (nat, zero) = t.nat();
    let e = deep(&mut t, nat, zero, 200);
    t.c.max_rec_depth = 20;
    let d = Decl::Defn(t.defn("a", nat, e, Safety::Safe));
    assert_eq!(t.add(&d), None);
}
