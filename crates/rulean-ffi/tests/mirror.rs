//! Tests of the conversion of `ConstantInfo` objects and of the mirror of the environment (spec 09.6.3).

#![allow(unsafe_code)]

use rulean_core::env::ConstInfo;
use rulean_core::tc::Checker;
use rulean_ffi::FaultKind;
use rulean_ffi::conv::Converter;
use rulean_ffi::heap::{OwnedHeap, boxed};
use rulean_ffi::live::LiveHeap;
use rulean_ffi::make::Encoder;
use rulean_ffi::mirror::add_constants;
use rulean_store::Store;

mod common;

use common::{B, name, nat_like};

fn checker() -> Checker {
    let mut c = Checker::new(Store::new());
    c.kernel_api = true;
    c
}

/// A checker that has checked `N`, `N.z`, `N.s` and `N.rec`, and the four constants.
fn nat_checker(b: &mut B) -> (Checker, Vec<ConstInfo>) {
    let mut c = checker();
    let d = nat_like(b);
    let got = rulean_ffi::conv::declaration(&b.h, &mut c.st, d).expect("a declaration");
    assert!(c.add_decl(&got).is_none());
    let mut ks = Vec::new();
    for s in ["N", "N.z", "N.s", "N.rec"] {
        let n = name(&mut c.st, s);
        let slot = c.env.find(n);
        assert_ne!(slot, 0, "{s} is not in the environment");
        ks.push(c.env.at(slot).clone());
    }
    (c, ks)
}

/// The `ConstantInfo` objects of `ks`.
fn encode(b: &mut B, st: &Store, ks: &[ConstInfo]) -> Vec<u64> {
    let mut e = Encoder::new(&mut b.h, st);
    ks.iter()
        .map(|k| e.constant(k, &[k.name]).expect("a constant"))
        .collect()
}

#[test]
fn the_constants_of_an_inductive_type_round_trip() {
    let mut b = B::new();
    let (mut c, ks) = nat_checker(&mut b);
    let objs = encode(&mut b, &c.st, &ks);
    let mut conv = Converter::new(&b.h, &mut c.st);
    for (k, &o) in ks.iter().zip(&objs) {
        let got = conv.constant(o).expect("a constant");
        assert_eq!(&got, k);
    }
}

#[test]
fn the_constants_round_trip_live() {
    let mut b = B::new();
    let (mut c, ks) = nat_checker(&mut b);
    let objs = encode(&mut b, &c.st, &ks);
    // SAFETY: the objects are in `b.h`, which lives until the end of the test.
    let live = unsafe { LiveHeap::new() };
    let mut conv = Converter::new(&live, &mut c.st);
    for (k, &o) in ks.iter().zip(&objs) {
        assert_eq!(&conv.constant(o).expect("a constant"), k);
    }
}

/// `theorem t : P (pred (N.s N.z)) := h`, with `pred n := N.rec.{1} (fun _ => N) N.z (fun n _ => n) n`.
fn pred_decls(b: &mut B, claim_succ: bool) -> Vec<u64> {
    let prop = b.sort(boxed(0));
    let nat = b.cnst("N", &[]);
    let p_ty = b.pi("n", 0, nat, prop);
    let p = b.axiom("P", p_ty);
    let pc = b.cnst("P", &[]);
    let z = b.cnst("N.z", &[]);
    let pz = b.app(pc, z);
    let h = b.axiom("h", pz);
    let one = b.succ(boxed(0));
    let rec = b.cnst("N.rec", &[one]);
    let motive = b.lam("x", 0, nat, nat);
    let v1 = b.bvar(1);
    let ih = b.lam("ih", 0, nat, v1);
    let minor = b.lam("n", 0, nat, ih);
    let mut body = b.app(rec, motive);
    body = b.app(body, z);
    body = b.app(body, minor);
    let v0 = b.bvar(0);
    body = b.app(body, v0);
    let value = b.lam("n", 0, nat, body);
    let pred_ty = b.pi("n", 0, nat, nat);
    let pv = b.defn_val("pred", &[], pred_ty, value, 1, 1);
    let pred = b.h.ctor(1, &[pv], &[]);
    let s = b.cnst("N.s", &[]);
    let sz = b.app(s, z);
    let arg = if claim_succ {
        sz
    } else {
        let pr = b.cnst("pred", &[]);
        b.app(pr, sz)
    };
    let claim = b.app(pc, arg);
    let tv = b.cval("t", &[], claim);
    let hc = b.cnst("h", &[]);
    let tn = b.name("t");
    let all = b.list(&[tn]);
    let thm_v = b.h.ctor(0, &[tv, hc, all], &[]);
    let thm = b.h.ctor(2, &[thm_v], &[]);
    vec![p, h, pred, thm]
}

fn run_on_mirror(claim_succ: bool) -> Option<rulean_core::tc::Fault> {
    let mut b = B::new();
    let (c0, ks) = nat_checker(&mut b);
    let objs = encode(&mut b, &c0.st, &ks);
    let mut c = checker();
    assert_eq!(add_constants(&mut c, &b.h, &objs, false), Ok(4));
    let ds = pred_decls(&mut b, claim_succ);
    for (i, &d) in ds.iter().enumerate() {
        let got = rulean_ffi::conv::declaration(&b.h, &mut c.st, d).expect("a declaration");
        let f = c.add_decl(&got);
        if i + 1 < ds.len() {
            assert!(f.is_none(), "declaration {i} failed: {f:?}");
        } else {
            return f;
        }
    }
    None
}

#[test]
fn a_mirrored_recursor_reduces_in_a_new_declaration() {
    assert!(run_on_mirror(false).is_none());
}

#[test]
fn a_false_claim_on_the_mirror_is_rejected() {
    let f = run_on_mirror(true).expect("a fault");
    assert_eq!(f.kind, rulean_core::tc::ErrorKind::DefTypeMismatch);
}

#[test]
fn quot_init_marks_the_environment() {
    let b = B::new();
    let mut c = checker();
    let n = c.env.len();
    assert_eq!(add_constants(&mut c, &b.h, &[], true), Ok(0));
    assert!(c.env.quot_initialized());
    // The environment has the quotient constants, so `quotDecl` does nothing.
    let d = rulean_ffi::conv::declaration(&b.h, &mut c.st, boxed(4)).expect("a declaration");
    assert!(c.add_decl(&d).is_none());
    assert_eq!(c.env.len(), n);
}

#[test]
fn a_failed_conversion_adds_nothing() {
    let mut b = B::new();
    let t = b.ty();
    let good = b.axiom("A", t);
    let cv = b.cval("Q", &[], t);
    let qv = b.h.ctor(0, &[cv], &[4]);
    let bad_quot = b.h.ctor(4, &[qv], &[]);
    let mut c = checker();
    let n = c.env.len();
    let f = add_constants(&mut c, &b.h, &[good, bad_quot], true).expect_err("a fault");
    assert_eq!(f.kind, FaultKind::Malformed);
    assert!(f.msg.contains("kind 4"), "{f}");
    assert_eq!(c.env.len(), n);
    assert!(!c.env.quot_initialized());
}

#[test]
fn malformed_constants_are_faults() {
    let mut b = B::new();
    let t = b.ty();
    let cv = b.cval("A", &[], t);
    let v = b.h.ctor(0, &[cv], &[0]);
    let cases = [
        // A tag above `recInfo`.
        b.h.ctor(8, &[v], &[]),
        // A boxed scalar.
        boxed(0),
        // `inductInfo` with the value of an axiom.
        b.h.ctor(5, &[v], &[]),
        // An `axiomInfo` with an `isUnsafe` byte that is not a boolean.
        {
            let v2 = b.h.ctor(0, &[cv], &[7]);
            b.h.ctor(0, &[v2], &[])
        },
    ];
    for o in cases {
        let mut st = Store::new();
        let h: &OwnedHeap = &b.h;
        let f = Converter::new(h, &mut st).constant(o).expect_err("a fault");
        assert_eq!(f.kind, FaultKind::Malformed, "{f}");
    }
}
