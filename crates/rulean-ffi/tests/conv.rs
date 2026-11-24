//! Tests of the conversion of `Declaration` objects (spec 09.6.3).
//!
//! Each test makes Lean objects with the layout of the Lean runtime in an `OwnedHeap`. Most tests read them through `OwnedHeap`, and the tests that end in `_live` read the same objects through `LiveHeap`.

#![allow(unsafe_code)]

use rulean_core::tc::Checker;
use rulean_ffi::conv::declaration;
use rulean_ffi::heap::{Heap, boxed};
use rulean_ffi::live::LiveHeap;
use rulean_ffi::{Fault, FaultKind};
use rulean_format::{Axiom, Decl, Defn, Hints, Safety};
use rulean_nat::Nat;
use rulean_store::{BinderInfo, Expr, Store};

mod common;

use common::{B, DATA, data_and, name, nat_like, ty};

fn checker() -> Checker {
    let mut c = Checker::new(Store::new());
    c.kernel_api = true;
    c
}

fn conv<H: Heap>(h: &H, c: &mut Checker, d: u64) -> Decl {
    match declaration(h, &mut c.st, d) {
        Ok(d) => d,
        Err(f) => panic!("the conversion failed: {f}"),
    }
}

fn conv_store<H: Heap>(h: &H, st: &mut Store, d: u64) -> Decl {
    match declaration(h, st, d) {
        Ok(d) => d,
        Err(f) => panic!("the conversion failed: {f}"),
    }
}

fn fault<H: Heap>(h: &H, d: u64) -> Fault {
    let mut st = Store::new();
    match declaration(h, &mut st, d) {
        Ok(d) => panic!("the conversion gave {d:?}"),
        Err(f) => f,
    }
}

#[test]
fn an_axiom_converts_and_checks() {
    let mut b = B::new();
    let t = b.ty();
    let d = b.axiom("A", t);
    let mut c = checker();
    let got = conv(&b.h, &mut c, d);
    let want = Decl::Axiom(Axiom {
        name: name(&mut c.st, "A"),
        lparams: Vec::new(),
        ty: ty(&mut c.st),
        safety: Safety::Safe,
    });
    assert_eq!(got, want);
    assert!(c.add_decl(&got).is_none());
    let a = name(&mut c.st, "A");
    assert_ne!(c.env.find(a), 0);
}

/// `def id.{u} (α : Sort u) (a : α) : α := fun α a => a`.
fn id_decl(b: &mut B) -> u64 {
    let u = b.param("u");
    let su = b.sort(u);
    let v0 = b.bvar(0);
    let v1 = b.bvar(1);
    let ty_in = b.pi("a", 0, v0, v1);
    let ty = b.pi("α", 0, su, ty_in);
    let su2 = b.sort(u);
    let w0 = b.bvar(0);
    let w0b = b.bvar(0);
    let body = b.lam("a", 0, w0, w0b);
    let value = b.lam("α", 0, su2, body);
    let v = b.defn_val("id", &["u"], ty, value, 1, 1);
    b.h.ctor(1, &[v], &[])
}

#[test]
fn a_polymorphic_definition_converts_and_checks() {
    let mut b = B::new();
    let d = id_decl(&mut b);
    let mut c = checker();
    let got = conv(&b.h, &mut c, d);
    let Decl::Defn(Defn {
        name: n,
        lparams,
        hints,
        safety,
        all,
        ..
    }) = &got
    else {
        panic!("not a definition: {got:?}");
    };
    let id = name(&mut c.st, "id");
    assert_eq!(*n, id);
    assert_eq!(lparams, &vec![name(&mut c.st, "u")]);
    assert_eq!(*hints, Hints::Regular(1));
    assert_eq!(*safety, Safety::Safe);
    assert_eq!(all, &vec![id]);
    assert!(c.add_decl(&got).is_none());
}

#[test]
fn a_definition_with_a_wrong_value_is_rejected() {
    let mut b = B::new();
    let u = b.param("u");
    let su = b.sort(u);
    let v0 = b.bvar(0);
    let v1 = b.bvar(1);
    let ty_in = b.pi("a", 0, v0, v1);
    let ty = b.pi("α", 0, su, ty_in);
    // `fun α a => α` has the type `(α : Sort u) → α → Sort u`, not the declared type.
    let su2 = b.sort(u);
    let w0 = b.bvar(0);
    let w1 = b.bvar(1);
    let body = b.lam("a", 0, w0, w1);
    let value = b.lam("α", 0, su2, body);
    let v = b.defn_val("bad", &["u"], ty, value, 1, 1);
    let d = b.h.ctor(1, &[v], &[]);
    let mut c = checker();
    let got = conv(&b.h, &mut c, d);
    assert!(c.add_decl(&got).is_some());
}

#[test]
fn the_live_heap_reads_the_same_objects_live() {
    let mut b = B::new();
    let d = id_decl(&mut b);
    let mut c1 = checker();
    let want = conv(&b.h, &mut c1, d);
    // SAFETY: `b.h` owns the objects that `d` points to, and it lives to the end of the test.
    let live = unsafe { LiveHeap::new() };
    let mut c2 = checker();
    let got = conv(&live, &mut c2, d);
    assert_eq!(got, want);
    assert!(c2.add_decl(&got).is_none());
}

/// `inductive N : Type | z : N | s : N → N`.
#[test]
fn an_inductive_declaration_adds_the_recursor() {
    let mut b = B::new();
    let d = nat_like(&mut b);
    let mut c = checker();
    let got = conv(&b.h, &mut c, d);
    let Decl::Induct(ind) = &got else {
        panic!("not an inductive block: {got:?}");
    };
    assert_eq!(ind.types.len(), 1);
    assert_eq!(ind.ctors.len(), 2);
    assert_eq!(ind.ctors[1].cidx, 1);
    assert!(ind.recs.is_empty());
    assert!(c.add_decl(&got).is_none());
    let rec = name(&mut c.st, "N.rec");
    assert_ne!(c.env.find(rec), 0);
}

#[test]
fn an_inductive_declaration_live() {
    let mut b = B::new();
    let d = nat_like(&mut b);
    // SAFETY: `b.h` owns the objects that `d` points to, and it lives to the end of the test.
    let live = unsafe { LiveHeap::new() };
    let mut c = checker();
    let got = conv(&live, &mut c, d);
    assert!(c.add_decl(&got).is_none());
}

#[test]
fn without_kernel_api_an_inductive_declaration_is_an_export_mismatch() {
    let mut b = B::new();
    let d = nat_like(&mut b);
    let mut c = Checker::new(Store::new());
    let got = conv(&b.h, &mut c, d);
    assert!(c.add_decl(&got).is_some());
}

/// `inductive Eq.{u} {α : Sort u} : α → α → Prop | refl (a : α) : Eq a a`.
fn eq_decl(b: &mut B) -> u64 {
    let u = b.param("u");
    let su = b.sort(u);
    let prop = b.sort(boxed(0));
    let x1 = b.bvar(1);
    let inner = b.pi("b", 0, x1, prop);
    let x0 = b.bvar(0);
    let mid = b.pi("a", 0, x0, inner);
    let ty = b.pi("α", 1, su, mid);
    let u2 = b.param("u");
    let su2 = b.sort(u2);
    let u3 = b.param("u");
    let eq = b.cnst("Eq", &[u3]);
    let a1 = b.bvar(1);
    let e1 = b.app(eq, a1);
    let a0 = b.bvar(0);
    let e2 = b.app(e1, a0);
    let a0b = b.bvar(0);
    let e3 = b.app(e2, a0b);
    let y0 = b.bvar(0);
    let r_in = b.pi("a", 0, y0, e3);
    let r_ty = b.pi("α", 1, su2, r_in);
    let r_name = b.name("Eq.refl");
    let refl = b.h.ctor(0, &[r_name, r_ty], &[]);
    let ctors = b.list(&[refl]);
    let n = b.name("Eq");
    let it = b.h.ctor(0, &[n, ty, ctors], &[]);
    let un = b.name("u");
    let lps = b.list(&[un]);
    let types = b.list(&[it]);
    b.h.ctor(6, &[lps, boxed(1), types], &[0])
}

#[test]
fn a_quotient_declaration_adds_the_four_constants_once() {
    let mut b = B::new();
    let eq = eq_decl(&mut b);
    let mut c = checker();
    let d = conv(&b.h, &mut c, eq);
    assert!(c.add_decl(&d).is_none());
    let q = conv(&b.h, &mut c, boxed(4));
    assert!(c.add_decl(&q).is_none());
    for n in ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] {
        let id = name(&mut c.st, n);
        assert_ne!(c.env.find(id), 0, "{n}");
    }
    let before = c.env.len();
    assert!(c.add_decl(&q).is_none());
    assert_eq!(c.env.len(), before);
}

#[test]
fn a_quotient_declaration_without_eq_is_rejected() {
    let b = B::new();
    let mut c = checker();
    let q = conv(&b.h, &mut c, boxed(4));
    assert!(c.add_decl(&q).is_some());
}

#[test]
fn literals_mdata_let_and_proj_convert() {
    let mut b = B::new();
    let big = b.h.mpz(&[0, 1]);
    let nat_lit = b.h.ctor(0, &[big], &[]);
    let e_nat = b.h.ctor(9, &[nat_lit], &DATA);
    let s = b.h.string("λx → ∀");
    let str_lit = b.h.ctor(1, &[s], &[]);
    let e_str = b.h.ctor(9, &[str_lit], &DATA);
    let p = b.name("Prod");
    let e_proj = b.h.ctor(11, &[p, boxed(1), e_str], &DATA);
    let md = b.h.ctor(10, &[boxed(0), e_proj], &DATA);
    let t = b.cnst("T", &[]);
    let x = b.name("x");
    let v0 = b.bvar(0);
    let body = b.app(md, v0);
    let e_let = b.h.ctor(8, &[x, t, e_nat, body], &data_and(1));
    let ty = b.ty();
    let cv = b.cval("c", &[], ty);
    let n = b.name("c");
    let all = b.list(&[n]);
    let v = b.h.ctor(0, &[cv, e_let, all], &[]);
    let d = b.h.ctor(2, &[v], &[]);

    let mut st = Store::new();
    let got = conv_store(&b.h, &mut st, d);
    let nid = st.intern_nat(Nat::from_limbs(vec![0, 1]));
    let w_nat = st.mk_nat_lit(nid);
    let sid = st.intern_str("λx → ∀".as_bytes());
    let w_str = st.mk_str_lit(sid);
    let pn = name(&mut st, "Prod");
    let w_proj = st.mk_proj(pn, 1, w_str);
    let tn = name(&mut st, "T");
    let empty = st.level_list_empty();
    let w_t = st.mk_const(tn, empty);
    let w0 = st.mk_bvar(0);
    let w_body = st.mk_app(w_proj, w0);
    let xn = name(&mut st, "x");
    let want = st.mk_let(xn, w_t, w_nat, w_body);
    let Decl::Thm(t) = got else {
        panic!("not a theorem: {got:?}");
    };
    assert_eq!(t.value, want);
}

#[test]
fn shared_objects_convert_once_and_deep_terms_do_not_overflow() {
    let mut b = B::new();
    let mut e = b.cnst("f", &[]);
    let a = b.cnst("a", &[]);
    for _ in 0..200_000 {
        e = b.app(e, a);
    }
    let lam = b.lam("x", 3, e, e);
    let d = b.axiom("A", lam);
    let mut st = Store::new();
    let got = conv_store(&b.h, &mut st, d);
    let Decl::Axiom(ax) = got else {
        panic!("not an axiom");
    };
    let Expr::Lam(bd) = st.node(ax.ty) else {
        panic!("not a lambda");
    };
    assert_eq!(bd.name, name(&mut st, "x"));
    assert_eq!(bd.info, BinderInfo::InstImplicit);
    assert_eq!(bd.dom, bd.body);
}

#[test]
fn free_variables_and_metavariables_are_faults() {
    let mut b = B::new();
    let id = b.name("_fvar.1");
    let fv = b.h.ctor(1, &[id], &DATA);
    let d = b.axiom("A", fv);
    assert_eq!(fault(&b.h, d).kind, FaultKind::FreeVar);

    let mut b = B::new();
    let id = b.name("_mvar.1");
    let mv = b.h.ctor(2, &[id], &DATA);
    let d = b.axiom("A", mv);
    assert_eq!(fault(&b.h, d).kind, FaultKind::MetaVar);

    let mut b = B::new();
    let id = b.name("_uniq.1");
    let lm = b.h.ctor(5, &[id], &DATA);
    let s = b.sort(lm);
    let d = b.axiom("A", s);
    assert_eq!(fault(&b.h, d).kind, FaultKind::MetaVar);
}

#[test]
fn malformed_objects_are_faults() {
    // A tag that is not an expression.
    let mut b = B::new();
    let e = b.h.ctor(12, &[boxed(0)], &DATA);
    let d = b.axiom("A", e);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);

    // An application with one object field.
    let mut b = B::new();
    let t = b.ty();
    let e = b.h.ctor(5, &[t], &DATA);
    let d = b.axiom("A", e);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);

    // A binder info that is not one of the four values.
    let mut b = B::new();
    let t = b.ty();
    let t2 = b.ty();
    let e = b.lam("x", 4, t, t2);
    let d = b.axiom("A", e);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);

    // A big number that is small enough to be a boxed scalar.
    let mut b = B::new();
    let m = b.h.mpz(&[5]);
    let e = b.h.ctor(0, &[m], &DATA);
    let d = b.axiom("A", e);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);

    // A boolean field with the value 2.
    let mut b = B::new();
    let t = b.ty();
    let cv = b.cval("A", &[], t);
    let v = b.h.ctor(0, &[cv], &[2]);
    let d = b.h.ctor(0, &[v], &[]);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);

    // A declaration that is a scalar other than `quotDecl`, and an address that is not aligned.
    let b = B::new();
    assert_eq!(fault(&b.h, boxed(9)).kind, FaultKind::Malformed);
    assert_eq!(fault(&b.h, 0x1004).kind, FaultKind::Malformed);

    // An address that is not in the heap.
    let mut b = B::new();
    let d = b.h.ctor(0, &[0x10], &[]);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Malformed);
}

#[test]
fn a_bound_variable_index_above_32_bits_is_a_decline() {
    let mut b = B::new();
    let e = b.bvar(1 << 40);
    let d = b.axiom("A", e);
    assert_eq!(fault(&b.h, d).kind, FaultKind::Decline);
}

#[test]
fn a_mutual_block_converts() {
    let mut b = B::new();
    let t = b.ty();
    let t2 = b.ty();
    let v1 = b.defn_val("f", &[], t, t2, 0, 0);
    let t3 = b.ty();
    let t4 = b.ty();
    let v2 = b.defn_val("g", &[], t3, t4, 0, 2);
    let l = b.list(&[v1, v2]);
    let d = b.h.ctor(5, &[l], &[]);
    let mut st = Store::new();
    let got = conv_store(&b.h, &mut st, d);
    let Decl::Mutual(ds) = got else {
        panic!("not a mutual block");
    };
    assert_eq!(ds.len(), 2);
    assert_eq!(ds[0].safety, Safety::Unsafe);
    assert_eq!(ds[1].safety, Safety::Partial);
    assert_eq!(ds[1].hints, Hints::Regular(0));
}
