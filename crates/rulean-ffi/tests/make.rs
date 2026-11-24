//! Tests of the construction of Lean objects from the store (spec 09.6.3).
//!
//! Each test writes terms of a store as Lean objects with `Encoder`, reads them back with `Converter` into the same store, and gets the same handles. The store interns its terms, so equal handles mean equal terms.

#![allow(unsafe_code)]

mod common;

use common::qname as name;
use common::{sample, thm};
use rulean_core::env::{ConstInfo, ConstKind};
use rulean_ffi::FaultKind;
use rulean_ffi::conv::Converter;
use rulean_ffi::heap::{Heap, OwnedHeap, boxed};
use rulean_ffi::live::LiveHeap;
use rulean_ffi::make::Encoder;
use rulean_format::{Hints, Safety};
use rulean_store::Store;

/// Writes `k` as an object and reads it back, through `LiveHeap` if `live` is true.
fn round_trip(live: bool, st: &mut Store, k: &ConstInfo) {
    let mut h = OwnedHeap::new();
    let o = Encoder::new(&mut h, st)
        .constant(k, &[k.name])
        .expect("an object");
    let got = if live {
        // SAFETY: the objects are in `h`, which lives until the end of the function.
        let r = unsafe { LiveHeap::new() };
        Converter::new(&r, st).constant(o)
    } else {
        Converter::new(&h, st).constant(o)
    };
    assert_eq!(&got.expect("a constant"), k);
}

#[test]
fn each_kind_of_term_round_trips() {
    let mut st = Store::new();
    let k = sample(&mut st);
    round_trip(false, &mut st, &k);
}

#[test]
fn each_kind_of_term_round_trips_live() {
    let mut st = Store::new();
    let k = sample(&mut st);
    round_trip(true, &mut st, &k);
}

#[test]
fn each_kind_of_constant_round_trips() {
    let mut st = Store::new();
    let p = name(&mut st, "p");
    let z = st.level_zero();
    let prop = st.mk_sort(z);
    let e = st.level_list(&[]);
    let pc = st.mk_const(p, e);
    let kinds = [
        (Safety::Unsafe, ConstKind::Axiom),
        (
            Safety::Partial,
            ConstKind::Defn {
                value: pc,
                hints: Hints::Regular(7),
            },
        ),
        (
            Safety::Safe,
            ConstKind::Defn {
                value: pc,
                hints: Hints::Abbrev,
            },
        ),
        (
            Safety::Unsafe,
            ConstKind::Defn {
                value: pc,
                hints: Hints::Opaque,
            },
        ),
        (Safety::Unsafe, ConstKind::Opaque { value: pc }),
        (
            Safety::Safe,
            ConstKind::Quot {
                kind: rulean_format::QuotKind::Lift,
            },
        ),
    ];
    for (safety, kind) in kinds {
        let k = ConstInfo {
            name: p,
            lparams: Vec::new(),
            ty: prop,
            safety,
            kind,
        };
        round_trip(false, &mut st, &k);
    }
}

#[test]
fn shared_terms_are_one_object_and_deep_terms_do_not_overflow() {
    let mut st = Store::new();
    let f = name(&mut st, "f");
    let e = st.level_list(&[]);
    let mut t = st.mk_const(f, e);
    for _ in 0..200_000 {
        t = st.mk_app(t, t);
    }
    let k = thm(&mut st, "deep", &[], t, t);
    let mut h = OwnedHeap::new();
    let o = {
        let mut enc = Encoder::new(&mut h, &st);
        enc.constant(&k, &[k.name]).expect("an object")
    };
    // The value of the `TheoremVal` and the type of its `ConstantVal` are the same object.
    let word = |h: &OwnedHeap, a: u64| {
        let mut b = [0u8; 8];
        assert!(h.read(a, &mut b));
        u64::from_le_bytes(b)
    };
    let v = word(&h, o + 8);
    let cv = word(&h, v + 8);
    assert_eq!(word(&h, v + 16), word(&h, cv + 24));
    // `t = app t' t'`, so both fields of the top node are one object.
    let top = word(&h, v + 16);
    assert_eq!(word(&h, top + 8), word(&h, top + 16));
    let got = Converter::new(&h, &mut st).constant(o).expect("a constant");
    assert_eq!(got, k);
}

#[test]
fn names_share_their_prefixes_and_zero_is_an_object() {
    let mut st = Store::new();
    let ab = name(&mut st, "a.b");
    let ac = name(&mut st, "a.c");
    let mut h = OwnedHeap::new();
    let (x, y, s) = {
        let z = st.level_zero();
        let mut enc = Encoder::new(&mut h, &st);
        (enc.name(ab), enc.name(ac), enc.level(z))
    };
    let word = |a: u64| {
        let mut b = [0u8; 8];
        assert!(h.read(a, &mut b));
        u64::from_le_bytes(b)
    };
    assert_ne!(x, y);
    assert_eq!(word(x + 8), word(y + 8));
    assert_eq!(s & 1, 0, "Level.zero is not a boxed scalar");
    assert_eq!((word(s) >> 56) as u8, 0);
    assert_ne!(word(x + 8), boxed(0));
}

#[test]
fn a_free_variable_is_a_fault() {
    let mut st = Store::new();
    let z = st.level_zero();
    let prop = st.mk_sort(z);
    let fv = st.mk_fvar(0, prop);
    let k = thm(&mut st, "t", &[], prop, fv);
    let mut h = OwnedHeap::new();
    let f = Encoder::new(&mut h, &st)
        .constant(&k, &[])
        .expect_err("a fault");
    assert_eq!(f.kind, FaultKind::FreeVar);
}
