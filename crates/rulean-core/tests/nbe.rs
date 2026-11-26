//! Tests of evaluation and read-back of engine F (spec 05.4.2 and 05.4.3). Each test builds a small environment by hand.

use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo, RecInfo, RuleInfo};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_core::value::EnvId;
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

impl T {
    /// The weak head normal form of `e` in engine F, read back.
    fn whnf_f(&mut self, e: ExprId) -> ExprId {
        let v = self.c.eval(EnvId::NIL, e);
        let w = self.c.force(v);
        let r = self.c.quote(0, 0, w);
        assert!(self.c.fault().is_none(), "fault: {:?}", self.c.fault());
        r
    }
    fn nat(&mut self, v: u64) -> ExprId {
        let id = self.c.st.intern_nat(Nat::from_u64(v));
        self.c.st.mk_nat_lit(id)
    }
    fn kl(&mut self, s: &str, ls: &[LevelId]) -> ExprId {
        let n = self.name(s);
        let ls = self.c.st.level_list(ls);
        self.c.st.mk_const(n, ls)
    }
}

#[test]
fn nat_literal_extension() {
    let mut t = T::new();
    let s1 = t.sort(1);
    t.axiom("Nat", s1);
    let (two, three, five) = (t.nat(2), t.nat(3), t.nat(5));
    let add = t.k("Nat.add");
    let e = t.app(add, &[two, three]);
    assert_eq!(t.whnf_f(e), five);
    let succ = t.k("Nat.succ");
    let four = t.nat(4);
    let e = t.app(succ, &[four]);
    assert_eq!(t.whnf_f(e), five);
    let ble = t.k("Nat.ble");
    let e = t.app(ble, &[five, two]);
    let f = t.k("Bool.false");
    assert_eq!(t.whnf_f(e), f);
    // The arguments are forced first: 2 + (2 + 3) is 7.
    let inner = t.app(add, &[two, three]);
    let e = t.app(add, &[two, inner]);
    let seven = t.nat(7);
    assert_eq!(t.whnf_f(e), seven);
    // An argument that is not a literal stays.
    let x = t.k("x");
    let e = t.app(add, &[two, x]);
    assert_eq!(t.whnf_f(e), e);
}

#[test]
fn nat_inline_numbers_give_the_answers_of_engine_r() {
    let mut t = T::new();
    let s1 = t.sort(1);
    t.axiom("Nat", s1);
    let big = 1u64 << 63;
    let vals = [0, 1, 2, 3, 7, 64, 65, 1 << 32, big - 1, big, u64::MAX];
    let ops = [
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.gcd",
        "Nat.mod",
        "Nat.div",
        "Nat.beq",
        "Nat.ble",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftRight",
    ];
    for op in ops {
        let f = t.k(op);
        for x in vals {
            for y in vals {
                let (a, b) = (t.nat(x), t.nat(y));
                let e = t.app(f, &[a, b]);
                let want = t.c.whnf(e);
                assert_eq!(t.whnf_f(e), want, "{op} {x} {y}");
            }
        }
    }
    let succ = t.k("Nat.succ");
    for x in vals {
        let a = t.nat(x);
        let e = t.app(succ, &[a]);
        let want = t.c.whnf(e);
        assert_eq!(t.whnf_f(e), want, "Nat.succ {x}");
    }
}

/// The type `B` with the constructors `B.t` and `B.f`, and `B.rec.{u}`.
fn bool_type(t: &mut T) {
    let s1 = t.sort(1);
    let b_n = t.name("B");
    let bt_n = t.name("B.t");
    let bf_n = t.name("B.f");
    let info = InductInfo {
        nparams: 0,
        nindices: 0,
        all: vec![b_n],
        ctors: vec![bt_n, bf_n],
        nnested: 0,
        is_rec: false,
        is_reflexive: false,
    };
    t.add("B", s1, ConstKind::Induct(info));
    let bty = t.k("B");
    for (n, i) in [("B.t", 0), ("B.f", 1)] {
        let ctor = CtorInfo {
            induct: b_n,
            cidx: i,
            nparams: 0,
            nfields: 0,
        };
        t.add(n, bty, ConstKind::Ctor(ctor));
    }
    let un = t.name("u");
    let u = t.c.st.level_param(un);
    let su = t.c.st.mk_sort(u);
    let motive_ty = t.pi("b", bty, su);
    let (b0, b1, b3) = (t.bv(0), t.bv(1), t.bv(3));
    let btc = t.k("B.t");
    let bfc = t.k("B.f");
    let m_t = t.app(b0, &[btc]);
    let m_f = t.app(b1, &[bfc]);
    let m_b = t.app(b3, &[b0]);
    let last = t.pi("b", bty, m_b);
    let r3 = t.pi("f", m_f, last);
    let r2 = t.pi("t", m_t, r3);
    let rec_ty = t.pi("motive", motive_ty, r2);
    let l3 = t.lam("f", m_f, b1);
    let l2 = t.lam("t", m_t, l3);
    let rt = t.lam("motive", motive_ty, l2);
    let l3 = t.lam("f", m_f, b0);
    let l2 = t.lam("t", m_t, l3);
    let rf = t.lam("motive", motive_ty, l2);
    let rec = RecInfo {
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
    };
    let rec_n = t.name("B.rec");
    t.c.env.add(ConstInfo {
        name: rec_n,
        lparams: vec![un],
        ty: rec_ty,
        safety: Safety::Safe,
        kind: ConstKind::Rec(rec),
    });
}

#[test]
fn recursor_iota() {
    let mut t = T::new();
    bool_type(&mut t);
    let z = t.c.st.level_zero();
    let one = t.c.st.level_succ(z);
    let rec = t.kl("B.rec", &[one]);
    let (m, x, y) = (t.k("M"), t.k("x"), t.k("y"));
    let btc = t.k("B.t");
    let bfc = t.k("B.f");
    let e = t.app(rec, &[m, x, y, bfc]);
    assert_eq!(t.whnf_f(e), y);
    let e = t.app(rec, &[m, x, y, btc]);
    assert_eq!(t.whnf_f(e), x);
    // The major premise is forced: a definition that unfolds to B.t.
    let bty = t.k("B");
    let d = t.def("d", bty, btc);
    let e = t.app(rec, &[m, x, y, d]);
    assert_eq!(t.whnf_f(e), x);
    // Extra arguments after the major premise are applied to the result.
    let g = t.k("g");
    let e = t.app(rec, &[m, g, y, btc, x]);
    let want = t.app(g, &[x]);
    assert_eq!(t.whnf_f(e), want);
    // A major premise that is not a constructor stays.
    let o = t.k("o");
    let e = t.app(rec, &[m, x, y, o]);
    assert_eq!(t.whnf_f(e), e);
    // read_back does only beta and zeta, so the recursor application under the binder stays.
    let b0 = t.bv(0);
    let body = t.app(rec, &[m, b0, y, btc]);
    let l = t.lam("z", bty, body);
    assert_eq!(t.nf(l), l);
}

#[test]
fn quotient_lift() {
    let mut t = T::new();
    t.c.env.mark_quot_initialized();
    let s1 = t.sort(1);
    t.axiom("Quot.lift", s1);
    let z = t.c.st.level_zero();
    let one = t.c.st.level_succ(z);
    let lift = t.kl("Quot.lift", &[one, one]);
    let mk = t.kl("Quot.mk", &[one]);
    let (a, r, b, f, h, x) = (t.k("A"), t.k("r"), t.k("B"), t.k("f"), t.k("h"), t.k("x"));
    let q = t.app(mk, &[a, r, x]);
    let e = t.app(lift, &[a, r, b, f, h, q]);
    let want = t.app(f, &[x]);
    assert_eq!(t.whnf_f(e), want);
}

#[test]
fn an_unused_argument_is_not_evaluated() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    // (fun (y : A) (z : A) => y) x (Sort 0 applied to Sort 0). The second argument is a "function expected" fault if it is evaluated, and the body does not use it.
    let s0 = t.sort(0);
    let bad = t.app(s0, &[s0]);
    let b1 = t.bv(1);
    let inner = t.lam("z", a, b1);
    let k = t.lam("y", a, inner);
    let e = t.app(k, &[x, bad]);
    assert_eq!(t.whnf_f(e), x);
}

#[test]
fn a_used_argument_reads_back_as_its_term() {
    let mut t = T::new();
    let s1 = t.sort(1);
    let a = t.axiom("A", s1);
    let x = t.axiom("x", a);
    let aa = t.pi("_", a, a);
    let g = t.axiom("g", aa);
    let aaa = t.pi("_", a, aa);
    let f = t.axiom("f", aaa);
    // (fun (y : A) => f y y) (g x) reads back as f (g x) (g x).
    let gx = t.app(g, &[x]);
    let b0 = t.bv(0);
    let body = t.app(f, &[b0, b0]);
    let lam = t.lam("y", a, body);
    let e = t.app(lam, &[gx]);
    let want = t.app(f, &[gx, gx]);
    assert_eq!(t.whnf_f(e), want);
}
