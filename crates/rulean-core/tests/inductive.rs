//! Tests of the inductive checks of engine R. The expected verdicts follow `inductive.cpp` of the official kernel v4.35.0.

use rulean_core::conv::Engine;
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Rec, RecRule, Safety};
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
fn unsafe_type_skips_strict_positivity() {
    // unsafe inductive N : Type | mk : (N -> N) -> N
    // The checker skips strict positivity for an unsafe type (spec 05.10). The block has no exported recursor, so the next check rejects it, and the error is not NonPositive.
    let mut t = T::new();
    let ty = t.sort(1);
    let n = t.k("N");
    let mut ity = t.ind_type("N", ty, 0, &["N.mk"]);
    ity.safety = Safety::Unsafe;
    let f = t.pi("x", n, n);
    let cty = t.pi("f", f, n);
    let mut c = t.ctor("N.mk", cty, "N", 0, 0, 1);
    c.safety = Safety::Unsafe;
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::ExportMismatch)
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

// Nested inductive types.

/// The universe parameter `u` and the sort `Sort u`.
fn sort_u(t: &mut T) -> (NameId, ExprId) {
    let u = t.name("u");
    let lu = t.c.st.level_param(u);
    (u, t.c.st.mk_sort(lu))
}

/// A constant with the level `u`.
fn const_u(t: &mut T, s: &str, u: NameId) -> ExprId {
    let n = t.name(s);
    let lu = t.c.st.level_param(u);
    let ls = t.c.st.level_list(&[lu]);
    t.c.st.mk_const(n, ls)
}

/// `inductive Bx (a : Type) : Type | mk : a -> Bx a`, with its recursor.
fn add_box(t: &mut T) {
    let ty = t.sort(1);
    let bx = t.k("Bx");
    let bx_ty = t.pi("a", ty, ty);
    let ity = t.ind_type("Bx", bx_ty, 1, &["Bx.mk"]);
    let v0 = t.bv(0);
    let v1 = t.bv(1);
    let v2 = t.bv(2);
    let bx_v1 = t.app(bx, &[v1]);
    let mk_body = t.pi("x", v0, bx_v1);
    let mk_ty = t.pi("a", ty, mk_body);
    let c = t.ctor("Bx.mk", mk_ty, "Bx", 0, 1, 1);
    // Bx.rec.{u} : {a : Type} -> {motive : Bx a -> Sort u} -> ((x : a) -> motive (Bx.mk a x)) -> (t : Bx a) -> motive t
    let (u, su) = sort_u(t);
    let bx_v0 = t.app(bx, &[v0]);
    let motive_ty = t.pi("t", bx_v0, su);
    let bmk = t.k("Bx.mk");
    let mk_app = t.app(bmk, &[v2, v0]);
    let m_mk = t.app(v1, &[mk_app]);
    let minor = t.pi("x", v1, m_mk);
    let bx_v2 = t.app(bx, &[v2]);
    let m_t = t.app(v2, &[v0]);
    let r = t.pi("t", bx_v2, m_t);
    let r = t.pi("mk", minor, r);
    let r = t.ipi("motive", motive_ty, r);
    let rec_ty = t.ipi("a", ty, r);
    let body = t.app(v1, &[v0]);
    let rhs = t.lam("x", v2, body);
    let rhs = t.lam("mk", minor, rhs);
    let rhs = t.lam("motive", motive_ty, rhs);
    let rhs = t.lam("a", ty, rhs);
    let rec = Rec {
        name: t.name("Bx.rec"),
        lparams: vec![u],
        ty: rec_ty,
        all: vec![t.name("Bx")],
        num_params: 1,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        k: false,
        rules: vec![RecRule {
            ctor: t.name("Bx.mk"),
            nfields: 1,
            rhs,
        }],
        safety: Safety::Safe,
    };
    assert_eq!(t.add(vec![ity], vec![c], vec![rec]), None);
}

/// `inductive N : Type | mk : Bx N -> N`, with `N.rec` and the auxiliary recursor `N.rec_1`.
fn nested_block(t: &mut T) -> (Vec<InductType>, Vec<Ctor>, Vec<Rec>) {
    let ty = t.sort(1);
    let n = t.k("N");
    let bx = t.k("Bx");
    let bxn = t.app(bx, &[n]);
    let mk_ty = t.pi("x", bxn, n);
    let mut ity = t.ind_type("N", ty, 0, &["N.mk"]);
    ity.num_nested = 1;
    ity.is_rec = true;
    let c = t.ctor("N.mk", mk_ty, "N", 0, 0, 1);
    let (u, su) = sort_u(t);
    let v: Vec<ExprId> = (0..5).map(|i| t.bv(i)).collect();
    let m1_ty = t.pi("t", n, su);
    let m2_ty = t.pi("t", bxn, su);
    // mk : (x : Bx N) -> motive_2 x -> motive_1 (N.mk x), under motive_1 and motive_2.
    let nmk = t.k("N.mk");
    let nmk_x = t.app(nmk, &[v[1]]);
    let m1_nmk = t.app(v[3], &[nmk_x]);
    let ih1 = t.app(v[1], &[v[0]]);
    let minor1 = t.pi("x_ih", ih1, m1_nmk);
    let minor1 = t.pi("x", bxn, minor1);
    // mk : (x : N) -> motive_1 x -> motive_2 (Bx.mk N x), under motive_1, motive_2 and the first minor.
    let bmk = t.k("Bx.mk");
    let bmk_x = t.app(bmk, &[n, v[1]]);
    let m2_bmk = t.app(v[3], &[bmk_x]);
    let ih2 = t.app(v[3], &[v[0]]);
    let minor2 = t.pi("x_ih", ih2, m2_bmk);
    let minor2 = t.pi("x", n, minor2);
    let mut recs = Vec::new();
    let names = ["N.rec", "N.rec_1"];
    let majors = [n, bxn];
    let motive_vars = [4u32, 3u32];
    let ctors = ["N.mk", "Bx.mk"];
    for j in 0..2 {
        let mv = t.bv(motive_vars[j]);
        let body = t.app(mv, &[v[0]]);
        let r = t.pi("t", majors[j], body);
        let r = t.pi("mk", minor2, r);
        let r = t.pi("mk", minor1, r);
        let r = t.ipi("motive_2", m2_ty, r);
        let rec_ty = t.ipi("motive_1", m1_ty, r);
        // The rule: fun motive_1 motive_2 mk mk x => mk x (other_rec motive_1 motive_2 mk mk x).
        let other = const_u(t, names[1 - j], u);
        let call = t.app(other, &[v[4], v[3], v[2], v[1], v[0]]);
        let minor = if j == 0 { v[2] } else { v[1] };
        let body = t.app(minor, &[v[0], call]);
        let field_ty = if j == 0 { bxn } else { n };
        let rhs = t.lam("x", field_ty, body);
        let rhs = t.lam("mk", minor2, rhs);
        let rhs = t.lam("mk", minor1, rhs);
        let rhs = t.lam("motive_2", m2_ty, rhs);
        let rhs = t.lam("motive_1", m1_ty, rhs);
        recs.push(Rec {
            name: t.name(names[j]),
            lparams: vec![u],
            ty: rec_ty,
            all: vec![t.name("N")],
            num_params: 0,
            num_indices: 0,
            num_motives: 2,
            num_minors: 2,
            k: false,
            rules: vec![RecRule {
                ctor: t.name(ctors[j]),
                nfields: 1,
                rhs,
            }],
            safety: Safety::Safe,
        });
    }
    (vec![ity], vec![c], recs)
}

#[test]
fn nested_type_is_accepted() {
    let mut t = T::new();
    add_box(&mut t);
    let (types, ctors, recs) = nested_block(&mut t);
    assert_eq!(t.add(types, ctors, recs), None);
    // The environment has the restored declarations and no auxiliary declaration.
    let rec1 = t.name("N.rec_1");
    let aux = t.name("_nested.Bx_1");
    assert!(t.c.env.contains(rec1));
    assert!(!t.c.env.contains(aux));
}

#[test]
fn nested_type_with_a_missing_constructor_is_a_fault() {
    // The mirror of rulean-ffi can have an inductive type without its constructors, until a check looks them up.
    let mut t = T::new();
    add_box(&mut t);
    let mk = t.name("Bx.mk");
    assert!(t.c.env.remove(mk));
    let (types, ctors, recs) = nested_block(&mut t);
    assert_eq!(t.add(types, ctors, recs), Some(ErrorKind::UnknownConst));
}

#[test]
fn wrong_nested_count_is_rejected() {
    let mut t = T::new();
    add_box(&mut t);
    let (mut types, ctors, recs) = nested_block(&mut t);
    types[0].num_nested = 0;
    assert_eq!(t.add(types, ctors, recs), Some(ErrorKind::ExportMismatch));
}

#[test]
fn missing_auxiliary_recursor_is_rejected() {
    let mut t = T::new();
    add_box(&mut t);
    let (types, ctors, mut recs) = nested_block(&mut t);
    recs.pop();
    assert_eq!(t.add(types, ctors, recs), Some(ErrorKind::ExportMismatch));
}

#[test]
fn nested_parameter_with_a_local_is_rejected() {
    // inductive L : Type | mk : (a : Type) -> Bx (a -> L) -> L
    let mut t = T::new();
    add_box(&mut t);
    let ty = t.sort(1);
    let l = t.k("L");
    let ity = t.ind_type("L", ty, 0, &["L.mk"]);
    let v0 = t.bv(0);
    let f = t.pi("y", v0, l);
    let bx = t.k("Bx");
    let bxf = t.app(bx, &[f]);
    let body = t.pi("x", bxf, l);
    let cty = t.pi("a", ty, body);
    let c = t.ctor("L.mk", cty, "L", 0, 0, 2);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::BadNested)
    );
}

/// Adds the declaration `name : ty` with the value `value`, or an axiom if `value` is `None`.
fn add_const(t: &mut T, name: &str, ty: ExprId, value: Option<ExprId>) {
    let name = t.name(name);
    let d = match value {
        Some(value) => Decl::Defn(Defn {
            name,
            lparams: Vec::new(),
            ty,
            value,
            hints: Hints::Regular(1),
            safety: Safety::Safe,
            all: vec![name],
        }),
        None => Decl::Axiom(Axiom {
            name,
            lparams: Vec::new(),
            ty,
            safety: Safety::Safe,
        }),
    };
    assert_eq!(t.c.add_decl(&d).map(|f| f.kind), None);
}

/// The constants of the confirm-set tests: `Bx`, `A : Type`, `F : A -> Type` and `I : A -> A := fun y => y`, with engine F.
fn confirm_env() -> T {
    let mut t = T::new();
    add_box(&mut t);
    t.c.engine = Engine::F;
    t.c.f_term_cap = 64;
    t.c.r_first_beats = 0;
    let ty = t.sort(1);
    add_const(&mut t, "A", ty, None);
    let a = t.k("A");
    let fty = t.pi("y", a, ty);
    add_const(&mut t, "F", fty, None);
    let aa = t.pi("y", a, a);
    let v0 = t.bv(0);
    let idf = t.lam("y", a, v0);
    add_const(&mut t, "I", aa, Some(idf));
    t
}

/// `F (Bx.rec.{1} A (fun _ => A) (fun y => y) x)`, where `x` is the bound variable `x`. Structure eta on `x` reduces the recursor to `x.0`.
fn f_rec(t: &mut T, x: u32) -> ExprId {
    let (a, f) = (t.k("A"), t.k("F"));
    let bx = t.k("Bx");
    let bx_a = t.app(bx, &[a]);
    let one = t.c.st.level_zero();
    let one = t.c.st.level_succ(one);
    let n = t.name("Bx.rec");
    let ls = t.c.st.level_list(&[one]);
    let rec = t.c.st.mk_const(n, ls);
    let motive = t.lam("t", bx_a, a);
    let v0 = t.bv(0);
    let idf = t.lam("y", a, v0);
    let vx = t.bv(x);
    let r = t.app(rec, &[a, motive, idf, vx]);
    t.app(f, &[r])
}

/// `F x.0`, or `F (I x.0)` if `delta` is true.
fn f_proj(t: &mut T, x: u32, delta: bool) -> ExprId {
    let n = t.name("Bx");
    let vx = t.bv(x);
    let mut p = t.c.st.mk_proj(n, 0, vx);
    if delta {
        let i = t.k("I");
        p = t.app(i, &[p]);
    }
    let f = t.k("F");
    t.app(f, &[p])
}

/// Adds `d : (x : Bx A) -> (h : H) -> (k1 : K1 -> A) -> (k2 : K2 -> A) -> A := fun x h k1 k2 => let b : A := k1 h; k2 h`. `H` is in the context [x], `K1` in [x, h] and `K2` in [x, h, k1]. The check of `k1 h` is the first query, and the check of `k2 h` is the second query, and both use the value of `H`. Engine F must accept the value of `d`. The result is the number of the answers of engine F that engine R confirmed in the check of `d`.
fn add_d(t: &mut T, h_ty: ExprId, k1_dom: ExprId, k2_dom: ExprId) -> u64 {
    let a = t.k("A");
    let bx = t.k("Bx");
    let bx_a = t.app(bx, &[a]);
    let k1_ty = t.pi("z", k1_dom, a);
    let k2_ty = t.pi("z", k2_dom, a);
    let (v1, v2, v3) = (t.bv(1), t.bv(2), t.bv(3));
    let k1h = t.app(v1, &[v2]);
    let k2h = t.app(v1, &[v3]);
    let bn = t.name("b");
    let body = t.c.st.mk_let(bn, a, k1h, k2h);
    let value = t.lam("k2", k2_ty, body);
    let value = t.lam("k1", k1_ty, value);
    let value = t.lam("h", h_ty, value);
    let value = t.lam("x", bx_a, value);
    let dty = t.pi("k2", k2_ty, a);
    let dty = t.pi("k1", k1_ty, dty);
    let dty = t.pi("h", h_ty, dty);
    let dty = t.pi("x", bx_a, dty);
    let before = t.c.f_stats;
    add_const(t, "d", dty, Some(value));
    let s = t.c.f_stats;
    // Engine F checks the value. The type is not deep, so engine R checks it (spec perf/11.19).
    assert_eq!(s.infer - before.infer, 1);
    assert_eq!(s.infer_ok - before.infer_ok, 1);
    assert_eq!(s.disagree, before.disagree);
    s.confirmed - before.confirmed
}

// The confirm set of spec 05.1: engine R confirms an answer of engine F that uses a delta step and a type-directed rule. In the two tests below, one of the two rules is in the first query, and the second query gets its result from a cache. An answer of the check of the value is in the confirm set, so engine R confirms that query, and then engine F continues and accepts the value.

#[test]
fn a_force_cache_hit_keeps_the_rules_of_its_steps() {
    // The first query uses structure eta on the recursor in `H` and puts the result into the cache of `force`. The second query has a hit in that cache and unfolds `I`.
    let mut t = confirm_env();
    let h = f_rec(&mut t, 0);
    let k1 = f_proj(&mut t, 1, false);
    let k2 = f_proj(&mut t, 2, true);
    assert_eq!(add_d(&mut t, h, k1, k2), 1);
}

#[test]
fn a_slot_hit_is_a_delta_step() {
    // The first query unfolds `I` in `H` and puts the unfolding into the slot. The second query uses the slot and structure eta on the recursor in `K2`.
    let mut t = confirm_env();
    let h = f_proj(&mut t, 0, true);
    let k1 = f_proj(&mut t, 1, false);
    let k2 = f_rec(&mut t, 2);
    assert_eq!(add_d(&mut t, h, k1, k2), 1);
}

#[test]
fn a_fault_has_only_the_free_variables_in_scope() {
    // inductive E (w : Type) : Type | mk : (w : Type) -> (l : C.0 w) -> E w. The projection is invalid. In the C++ kernel, the local context of the error has the parameter `w` of `add_inductive_fn` and the `w` of `infer_pi`, and no free variable of the earlier steps.
    let mut t = T::new();
    let ty = t.sort(1);
    let ity_ty = t.pi("w", ty, ty);
    let ity = t.ind_type("E", ity_ty, 1, &["E.mk"]);
    let e = t.k("E");
    let c_name = t.name("C");
    let w0 = t.bv(0);
    let proj = t.c.st.mk_proj(c_name, 0, w0);
    let w1 = t.bv(1);
    let res = t.app(e, &[w1]);
    let body = t.pi("l", proj, res);
    let cty = t.pi("w", ty, body);
    let c = t.ctor("E.mk", cty, "E", 0, 1, 1);
    assert_eq!(
        t.add(vec![ity], vec![c], Vec::new()),
        Some(ErrorKind::InvalidProj)
    );
    let w = t.name("w");
    let names: Vec<NameId> =
        t.c.scope()
            .iter()
            .map(|&l| t.c.local(l as usize).0)
            .collect();
    assert_eq!(names, vec![w, w]);
}

/// Adds `name : ty := value` and gives the kind of the fault, if any.
fn add_def(t: &mut T, name: &str, ty: ExprId, value: ExprId) -> Option<ErrorKind> {
    let name = t.name(name);
    let d = Decl::Defn(Defn {
        name,
        lparams: Vec::new(),
        ty,
        value,
        hints: Hints::Regular(1),
        safety: Safety::Safe,
        all: vec![name],
    });
    t.c.add_decl(&d).map(|f| f.kind)
}

// Engine F infers the type of a projection itself (spec perf/04.5). Engine R does it when the structure can be a proposition or the form is not valid, so the verdicts are the verdicts of engine R.

#[test]
fn engine_f_accepts_a_projection_of_a_structure() {
    let mut t = confirm_env();
    let a = t.k("A");
    let bx = t.k("Bx");
    let bx_a = t.app(bx, &[a]);
    let n = t.name("Bx");
    let v0 = t.bv(0);
    let p = t.c.st.mk_proj(n, 0, v0);
    let value = t.lam("x", bx_a, p);
    let ty = t.pi("x", bx_a, a);
    let before = t.c.f_stats;
    assert_eq!(add_def(&mut t, "p", ty, value), None);
    let s = t.c.f_stats;
    // Engine F checks the value. The type is not deep, so engine R checks it (spec perf/11.19).
    assert_eq!(s.infer - before.infer, 1);
    assert_eq!(s.infer_ok - before.infer_ok, 1);
}

#[test]
fn engine_f_gives_an_invalid_field_index_to_engine_r() {
    let mut t = confirm_env();
    let a = t.k("A");
    let bx = t.k("Bx");
    let bx_a = t.app(bx, &[a]);
    let n = t.name("Bx");
    let v0 = t.bv(0);
    let p = t.c.st.mk_proj(n, 1, v0);
    let value = t.lam("x", bx_a, p);
    let ty = t.pi("x", bx_a, a);
    assert_eq!(
        add_def(&mut t, "p", ty, value),
        Some(ErrorKind::InvalidProj)
    );
}

/// Adds `inductive P : Prop | mk : (y : a) -> P` with its recursor, and gives `P`. If `large` is true, `a` is a proposition, and the recursor has the motive `P -> Sort u`. Else the motive is `P -> Prop`.
fn add_prop_struct(t: &mut T, a: ExprId, large: bool) -> ExprId {
    let prop = t.sort(0);
    let pk = t.k("P");
    let ity = t.ind_type("P", prop, 0, &["P.mk"]);
    let mk_ty = t.pi("y", a, pk);
    let c = t.ctor("P.mk", mk_ty, "P", 0, 0, 1);
    // P.rec : {motive : P -> Prop} -> ((y : A) -> motive (P.mk y)) -> (t : P) -> motive t, or with `Sort u` for a large recursor.
    let (u, su) = sort_u(t);
    let msort = if large { su } else { prop };
    let lparams = if large { vec![u] } else { Vec::new() };
    let motive_ty = t.pi("t", pk, msort);
    let pmk = t.k("P.mk");
    let (v0, v1, v2) = (t.bv(0), t.bv(1), t.bv(2));
    let mk_y = t.app(pmk, &[v0]);
    let m_mk = t.app(v1, &[mk_y]);
    let minor = t.pi("y", a, m_mk);
    let m_t = t.app(v2, &[v0]);
    let body = t.pi("t", pk, m_t);
    let body = t.pi("mk", minor, body);
    let rec_ty = t.ipi("motive", motive_ty, body);
    let mk_v = t.app(v1, &[v0]);
    let rhs = t.lam("y", a, mk_v);
    let rhs = t.lam("mk", minor, rhs);
    let rhs = t.lam("motive", motive_ty, rhs);
    let rec = Rec {
        name: t.name("P.rec"),
        lparams,
        ty: rec_ty,
        all: vec![t.name("P")],
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        k: false,
        rules: vec![RecRule {
            ctor: t.name("P.mk"),
            nfields: 1,
            rhs,
        }],
        safety: Safety::Safe,
    };
    assert_eq!(t.add(vec![ity], vec![c], vec![rec]), None);
    pk
}

#[test]
fn engine_f_gives_a_field_of_a_proposition_to_engine_r() {
    // The field is not a proof, so `x.0` is not valid.
    let mut t = confirm_env();
    let a = t.k("A");
    let pk = add_prop_struct(&mut t, a, false);
    let n = t.name("P");
    let v0 = t.bv(0);
    let p = t.c.st.mk_proj(n, 0, v0);
    let value = t.lam("x", pk, p);
    let ty = t.pi("x", pk, a);
    assert_eq!(
        add_def(&mut t, "q", ty, value),
        Some(ErrorKind::InvalidProj)
    );
}

#[test]
fn engine_f_accepts_a_proof_field_of_a_proposition() {
    // `H : Prop` is an axiom, and the field of `P` is a proof of `H`, so `x.0 : H`.
    let mut t = confirm_env();
    let prop = t.sort(0);
    add_const(&mut t, "H", prop, None);
    let h = t.k("H");
    let pk = add_prop_struct(&mut t, h, true);
    let n = t.name("P");
    let v0 = t.bv(0);
    let p = t.c.st.mk_proj(n, 0, v0);
    let value = t.lam("x", pk, p);
    let ty = t.pi("x", pk, h);
    let before = t.c.f_stats;
    assert_eq!(add_def(&mut t, "q", ty, value), None);
    let s = t.c.f_stats;
    // Engine F checks the value. The type is not deep, so engine R checks it (spec perf/11.19).
    assert_eq!(s.infer - before.infer, 1);
    assert_eq!(s.infer_ok - before.infer_ok, 1);
}
