//! Tests of inference, reduction and definitional equality of engine R. Each test builds a small environment by hand. The expected values follow `type_checker.cpp` of the official kernel v4.35.0.

use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo, RecInfo, RuleInfo};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Hints, Safety};
use rulean_nat::Nat;
use rulean_store::{BinderInfo, ExprId, LevelId, NameId, Store};

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
    fn nat(&mut self, v: u64) -> ExprId {
        let id = self.c.st.intern_nat(Nat::from_u64(v));
        self.c.st.mk_nat_lit(id)
    }
    fn add(&mut self, name: &str, lparams: &[&str], ty: ExprId, kind: ConstKind) {
        let name = self.name(name);
        let mut ls = Vec::new();
        for p in lparams {
            ls.push(self.name(p));
        }
        self.c.env.add(ConstInfo {
            name,
            lparams: ls,
            ty,
            safety: Safety::Safe,
            kind,
        });
    }
    fn axiom(&mut self, name: &str, ty: ExprId) -> ExprId {
        self.add(name, &[], ty, ConstKind::Axiom);
        self.k(name)
    }
    fn def(&mut self, name: &str, ty: ExprId, value: ExprId, h: u32) -> ExprId {
        self.add(
            name,
            &[],
            ty,
            ConstKind::Defn {
                value,
                hints: Hints::Regular(h),
            },
        );
        self.k(name)
    }
    fn whnf(&mut self, e: ExprId) -> ExprId {
        self.c.whnf(e)
    }
    fn defeq(&mut self, a: ExprId, b: ExprId) -> bool {
        self.c.is_def_eq(a, b)
    }
}

#[test]
fn infer_sort_lambda_and_pi() {
    let mut t = T::new();
    let s0 = t.sort(0);
    let s1 = t.sort(1);
    let s2 = t.sort(2);
    assert_eq!(t.c.check(s0), s1);
    assert_eq!(t.c.check(s1), s2);
    // fun (A : Type) (x : A) => x has the type (A : Type) -> A -> A.
    let b0 = t.bv(0);
    let b1 = t.bv(1);
    let inner = t.lam("x", b0, b0);
    let id = t.lam("A", s1, inner);
    let pinner = t.pi("x", b0, b1);
    let want = t.pi("A", s1, pinner);
    let got = t.c.check(id);
    assert!(t.c.fault().is_none());
    assert!(t.defeq(got, want));
    // The type of a pi over a sort is the impredicative maximum.
    let p = t.pi("A", s1, b0);
    assert_eq!(t.c.check(p), s2);
    let prop_pi = t.pi("p", s0, b0);
    let ty = t.c.check(prop_pi);
    assert_eq!(ty, s0);
}

#[test]
fn unknown_constant_is_a_fault() {
    let mut t = T::new();
    let c = t.k("nothing");
    t.c.check(c);
    let f = t.c.fault().expect("fault");
    assert_eq!(f.kind, ErrorKind::UnknownConst);
}

#[test]
fn application_type_mismatch() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let b = t.axiom("B", s1);
    let x = t.axiom("x", b);
    let b0 = t.bv(0);
    let f = t.lam("y", a, b0);
    let e = t.app(f, &[x]);
    t.c.check(e);
    assert_eq!(
        t.c.fault().map(|f| f.kind),
        Some(ErrorKind::AppTypeMismatch)
    );
}

#[test]
fn beta_delta_and_zeta() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let c = t.axiom("c", a);
    let b0 = t.bv(0);
    let id = t.lam("x", a, b0);
    let e = t.app(id, &[c]);
    assert_eq!(t.whnf(e), c);
    assert_eq!(t.c.whnf_core(e, false, false), c);
    // A definition unfolds in whnf but not in whnf_core. The kernel diagnostics count the unfold.
    let d = t.def("d", a, c, 1);
    t.c.diag_on = true;
    assert_eq!(t.c.whnf_core(d, false, false), d);
    assert!(t.c.diag.is_empty());
    assert_eq!(t.whnf(d), c);
    let n = t.name("d");
    assert_eq!(t.c.diag, vec![(n, 1)]);
    t.c.diag_on = false;
    // let x := c; x
    let n = t.name("x");
    let l = t.c.st.mk_let(n, a, c, b0);
    assert_eq!(t.whnf(l), c);
    assert!(t.c.fault().is_none());
}

#[test]
fn nat_literal_extension() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let nat = t.k("Nat");
    t.axiom("Nat", s1);
    let (two, three, five) = (t.nat(2), t.nat(3), t.nat(5));
    let add = t.k("Nat.add");
    let e = t.app(add, &[two, three]);
    assert_eq!(t.whnf(e), five);
    let succ = t.k("Nat.succ");
    let four = t.nat(4);
    let e = t.app(succ, &[four]);
    assert_eq!(t.whnf(e), five);
    let ble = t.k("Nat.ble");
    let e = t.app(ble, &[five, two]);
    let f = t.k("Bool.false");
    assert_eq!(t.whnf(e), f);
    // 5 =?= Nat.succ 4 by the offset rule.
    let e = t.app(succ, &[four]);
    assert!(t.defeq(five, e));
    let zero = t.axiom("Nat.zero", nat);
    let z = t.nat(0);
    assert!(t.defeq(zero, z));
    assert!(!t.defeq(five, four));
    let _ = nat;
    assert!(t.c.fault().is_none());
}

#[test]
fn nat_pow_count_bound() {
    let mut t = T::new();
    let pow = t.k("Nat.pow");
    let two = t.nat(2);
    let big = t.nat(5_000_000_000);
    let e = t.app(pow, &[two, big]);
    t.whnf(e);
    assert_eq!(t.c.fault().map(|f| f.kind), Some(ErrorKind::CountTooLarge));
}

#[test]
fn proof_irrelevance() {
    let mut t = T::new();
    let s0 = t.sort(0);
    let p = t.axiom("P", s0);
    let h1 = t.axiom("h1", p);
    let h2 = t.axiom("h2", p);
    assert!(t.defeq(h1, h2));
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    let y = t.axiom("y", a);
    assert!(!t.defeq(x, y));
    assert!(t.c.fault().is_none());
}

#[test]
fn eta_expansion() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let fty = t.pi("x", a, a);
    let f = t.axiom("f", fty);
    let b0 = t.bv(0);
    let body = t.app(f, &[b0]);
    let l = t.lam("x", a, body);
    assert!(t.defeq(l, f));
    assert!(t.defeq(f, l));
    assert!(t.c.fault().is_none());
}

/// A structure `Pr` with the constructor `Pr.mk : A -> A -> Pr`.
fn pair(t: &mut T) -> (ExprId, ExprId, NameId) {
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let pr_n = t.name("Pr");
    let mk_n = t.name("Pr.mk");
    t.add(
        "Pr",
        &[],
        s1,
        ConstKind::Induct(InductInfo {
            nparams: 0,
            nindices: 0,
            all: vec![pr_n],
            ctors: vec![mk_n],
            nnested: 0,
            is_rec: false,
            is_reflexive: false,
        }),
    );
    let pr = t.k("Pr");
    let inner = t.pi("b", a, pr);
    let mk_ty = t.pi("a", a, inner);
    t.add(
        "Pr.mk",
        &[],
        mk_ty,
        ConstKind::Ctor(CtorInfo {
            induct: pr_n,
            cidx: 0,
            nparams: 0,
            nfields: 2,
        }),
    );
    (a, pr, pr_n)
}

#[test]
fn projections_and_structure_eta() {
    let mut t = T::new();
    let (a, pr, pr_n) = pair(&mut t);
    let x = t.axiom("x", a);
    let y = t.axiom("y", a);
    let mk = t.k("Pr.mk");
    let v = t.app(mk, &[x, y]);
    let p1 = t.c.st.mk_proj(pr_n, 1, v);
    assert_eq!(t.whnf(p1), y);
    assert_eq!(t.c.infer(p1), a);
    // p =?= Pr.mk p.1 p.2
    let p = t.axiom("p", pr);
    let q0 = t.c.st.mk_proj(pr_n, 0, p);
    let q1 = t.c.st.mk_proj(pr_n, 1, p);
    let e = t.app(mk, &[q0, q1]);
    assert!(t.defeq(p, e));
    assert!(t.defeq(e, p));
    let e = t.app(mk, &[q1, q0]);
    assert!(!t.defeq(p, e));
    assert!(t.c.fault().is_none());
}

#[test]
fn unit_like_structure() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let u_n = t.name("U");
    let star_n = t.name("U.star");
    t.add(
        "U",
        &[],
        s1,
        ConstKind::Induct(InductInfo {
            nparams: 0,
            nindices: 0,
            all: vec![u_n],
            ctors: vec![star_n],
            nnested: 0,
            is_rec: false,
            is_reflexive: false,
        }),
    );
    let u = t.k("U");
    t.add(
        "U.star",
        &[],
        u,
        ConstKind::Ctor(CtorInfo {
            induct: u_n,
            cidx: 0,
            nparams: 0,
            nfields: 0,
        }),
    );
    let a = t.axiom("a", u);
    let b = t.axiom("b", u);
    assert!(t.defeq(a, b));
    assert!(t.c.fault().is_none());
}

#[test]
fn recursor_iota() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let b_n = t.name("B");
    let bt_n = t.name("B.t");
    let bf_n = t.name("B.f");
    t.add(
        "B",
        &[],
        s1,
        ConstKind::Induct(InductInfo {
            nparams: 0,
            nindices: 0,
            all: vec![b_n],
            ctors: vec![bt_n, bf_n],
            nnested: 0,
            is_rec: false,
            is_reflexive: false,
        }),
    );
    let bty = t.k("B");
    for (n, i) in [("B.t", 0), ("B.f", 1)] {
        t.add(
            n,
            &[],
            bty,
            ConstKind::Ctor(CtorInfo {
                induct: b_n,
                cidx: i,
                nparams: 0,
                nfields: 0,
            }),
        );
    }
    // B.rec.{u} : (motive : B -> Sort u) -> motive B.t -> motive B.f -> (b : B) -> motive b
    let un = t.name("u");
    let u = t.c.st.level_param(un);
    let su = t.c.st.mk_sort(u);
    let motive_ty = t.pi("b", bty, su);
    let (b0, b1, b2, b3) = (t.bv(0), t.bv(1), t.bv(2), t.bv(3));
    let btc = t.k("B.t");
    let bfc = t.k("B.f");
    let m_t = t.app(b0, &[btc]);
    let m_f = t.app(b1, &[bfc]);
    let m_b = t.app(b3, &[b0]);
    let last = t.pi("b", bty, m_b);
    let r3 = t.pi("f", m_f, last);
    let r2 = t.pi("t", m_t, r3);
    let rec_ty = t.pi("motive", motive_ty, r2);
    // The rules: fun motive t f => t and fun motive t f => f.
    let rt = {
        let l3 = t.lam("f", m_f, b1);
        let l2 = t.lam("t", m_t, l3);
        t.lam("motive", motive_ty, l2)
    };
    let rf = {
        let l3 = t.lam("f", m_f, b0);
        let l2 = t.lam("t", m_t, l3);
        t.lam("motive", motive_ty, l2)
    };
    let _ = b2;
    t.add(
        "B.rec",
        &["u"],
        rec_ty,
        ConstKind::Rec(RecInfo {
            all: vec![b_n],
            nparams: 0,
            nindices: 0,
            nmotives: 1,
            nminors: 2,
            rules: vec![
                RuleInfo {
                    ctor: bt_n,
                    nfields: 0,
                    rhs: rt,
                },
                RuleInfo {
                    ctor: bf_n,
                    nfields: 0,
                    rhs: rf,
                },
            ],
            k: false,
        }),
    );
    let z = t.c.st.level_zero();
    let one = t.c.st.level_succ(z);
    let rec = t.kl("B.rec", &[one]);
    let m = t.k("M");
    let x = t.k("x");
    let y = t.k("y");
    // The kernel diagnostics count each step of the recursor, as `whnf_core` of the C++ kernel does.
    t.c.diag_on = true;
    let e = t.app(rec, &[m, x, y, bfc]);
    assert_eq!(t.whnf(e), y);
    let e = t.app(rec, &[m, x, y, btc]);
    assert_eq!(t.whnf(e), x);
    // A major premise that is not a constructor stays.
    let o = t.k("o");
    let e = t.app(rec, &[m, x, y, o]);
    assert_eq!(t.whnf(e), e);
    assert!(t.c.fault().is_none());
    let n = t.name("B.rec");
    assert_eq!(t.c.diag_count(n), 2);
    assert_eq!(t.c.diag.len(), 1);
}

#[test]
fn quotient_lift() {
    let mut t = T::new();
    t.c.env.mark_quot_initialized();
    let z = t.c.st.level_zero();
    let one = t.c.st.level_succ(z);
    let lift = t.kl("Quot.lift", &[one, one]);
    let mk = t.kl("Quot.mk", &[one]);
    let (a, r, b, f, h, x) = (t.k("A"), t.k("r"), t.k("B"), t.k("f"), t.k("h"), t.k("x"));
    let q = t.app(mk, &[a, r, x]);
    let e = t.app(lift, &[a, r, b, f, h, q]);
    let want = t.app(f, &[x]);
    assert_eq!(t.whnf(e), want);
}

#[test]
fn string_literal_expansion() {
    let mut t = T::new();
    let s1 = t.sort(1);
    t.axiom("String", s1);
    t.axiom("String.ofList", s1);
    let sid = t.c.st.intern_str(b"a");
    let lit = t.c.st.mk_str_lit(sid);
    let z = t.c.st.level_zero();
    let ch = t.k("Char");
    let cons = t.kl("List.cons", &[z]);
    let nil = t.kl("List.nil", &[z]);
    let nil = t.app(nil, &[ch]);
    let of_nat = t.k("Char.ofNat");
    let n97 = t.nat(97);
    let c97 = t.app(of_nat, &[n97]);
    let list = t.app(cons, &[ch, c97, nil]);
    let of_list = t.k("String.ofList");
    let s = t.app(of_list, &[list]);
    assert!(t.defeq(lit, s));
    assert!(t.c.fault().is_none());
}

#[test]
fn utf8_decode_matches_code_points() {
    let s = "aé€😀";
    let want: Vec<u32> = s.chars().map(|c| c as u32).collect();
    assert_eq!(rulean_core::whnf::utf8_decode(s.as_bytes()), want);
}
