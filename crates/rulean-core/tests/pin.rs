//! Tests of primitive pinning (spec 05.8, deviation D1).

use rulean_core::sha256::{Hasher, sha256};
use rulean_core::tc::Checker;
use rulean_format::{Axiom, Decl, Safety};
use rulean_nat::Nat;
use rulean_store::{ExprId, NameId, Store};

fn name(c: &mut Checker, s: &str) -> NameId {
    let mut n = c.st.anon();
    for part in s.split('.') {
        n = c.st.name_str_bytes(n, part.as_bytes());
    }
    n
}

fn lit(c: &mut Checker, v: u64) -> ExprId {
    let id = c.st.intern_nat(Nat::from_u64(v));
    c.st.mk_nat_lit(id)
}

/// `op a b` with `op` a constant with no levels.
fn bin(c: &mut Checker, op: &str, a: u64, b: u64) -> ExprId {
    let n = name(c, op);
    let ls = c.st.level_list_empty();
    let f = c.st.mk_const(n, ls);
    let x = lit(c, a);
    let y = lit(c, b);
    c.st.mk_apps(f, &[x, y])
}

/// Adds the axiom `n : Type`. An axiom is never equal to a reference, so this is a mismatch for a target name.
fn add_type_axiom(c: &mut Checker, n: &str) {
    let name = name(c, n);
    let z = c.st.level_zero();
    let one = c.st.level_succ(z);
    let ty = c.st.mk_sort(one);
    let d = Decl::Axiom(Axiom {
        name,
        lparams: Vec::new(),
        ty,
        safety: Safety::Safe,
    });
    assert!(c.add_decl(&d).is_none());
}

fn hex(b: &[u8]) -> String {
    let mut s = String::new();
    for x in b {
        s.push_str(&format!("{:02x}", x));
    }
    s
}

#[test]
fn sha256_gives_the_standard_digests() {
    assert_eq!(
        hex(&sha256(b"")),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        hex(&sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    let long = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
    assert_eq!(
        hex(&sha256(long)),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}

#[test]
fn hasher_parts_give_the_digest_of_the_whole() {
    let mut msg = Vec::new();
    let mut i: u32 = 0;
    while i < 1000 {
        msg.push((i * 7 % 251) as u8);
        i += 1;
    }
    let want = sha256(&msg);
    for cut in [0usize, 1, 55, 63, 64, 65, 127, 128, 500, 999, 1000] {
        let mut x = Hasher::new();
        x.update(&msg[..cut]);
        x.update(&msg[cut..]);
        assert_eq!(x.finish(), want, "cut at {cut}");
    }
    let mut x = Hasher::new();
    for b in &msg {
        x.update(&[*b]);
    }
    assert_eq!(x.finish(), want);
}

#[test]
fn extension_is_on_when_the_primitive_is_not_declared() {
    let mut c = Checker::new(Store::new());
    let e = bin(&mut c, "Nat.add", 2, 3);
    let five = lit(&mut c, 5);
    assert_eq!(c.whnf(e), five);
    assert!(c.pin_mismatch.is_empty());
}

#[test]
fn mismatch_turns_off_one_operation() {
    let mut c = Checker::new(Store::new());
    add_type_axiom(&mut c, "Nat.add");
    let n = name(&mut c, "Nat.add");
    assert_eq!(c.pin_mismatch, vec![n]);
    let add = bin(&mut c, "Nat.add", 2, 3);
    assert_eq!(c.whnf(add), add);
    let mul = bin(&mut c, "Nat.mul", 2, 3);
    let six = lit(&mut c, 6);
    assert_eq!(c.whnf(mul), six);
}

#[test]
fn nat_mismatch_turns_off_all_operations() {
    let mut c = Checker::new(Store::new());
    add_type_axiom(&mut c, "Nat");
    let mul = bin(&mut c, "Nat.mul", 2, 3);
    assert_eq!(c.whnf(mul), mul);
    let beq = bin(&mut c, "Nat.beq", 2, 2);
    assert_eq!(c.whnf(beq), beq);
}

#[test]
fn trust_by_name_keeps_the_extension_on() {
    let mut c = Checker::new(Store::new());
    c.trust_primitives = true;
    add_type_axiom(&mut c, "Nat.add");
    let n = name(&mut c, "Nat.add");
    assert_eq!(c.pin_mismatch, vec![n]);
    let add = bin(&mut c, "Nat.add", 2, 3);
    let five = lit(&mut c, 5);
    assert_eq!(c.whnf(add), five);
}

#[test]
fn other_names_are_not_compared() {
    let mut c = Checker::new(Store::new());
    add_type_axiom(&mut c, "Nat.addx");
    add_type_axiom(&mut c, "Int");
    assert!(c.pin_mismatch.is_empty());
}
