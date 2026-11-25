//! Tests of `Env::remove`, the lookup record and `Env::truncate` of the module `env`.

use rulean_core::env::{ConstInfo, ConstKind, Env};
use rulean_format::Safety;
use rulean_store::{ExprId, NameId, Store};

fn name(st: &mut Store, s: &str) -> NameId {
    let n = st.anon();
    st.name_str_bytes(n, s.as_bytes())
}

fn axiom(name: NameId, ty: ExprId) -> ConstInfo {
    ConstInfo {
        name,
        lparams: Vec::new(),
        ty,
        safety: Safety::Safe,
        kind: ConstKind::Axiom,
    }
}

#[test]
fn remove_moves_the_last_constant_to_the_free_slot() {
    let mut st = Store::new();
    let l0 = st.level_zero();
    let prop = st.mk_sort(l0);
    let [a, b, c] = ["a", "b", "c"].map(|s| name(&mut st, s));
    let mut env = Env::new();
    for n in [a, b, c] {
        env.add(axiom(n, prop));
    }
    assert!(env.remove(a));
    assert_eq!(env.len(), 2);
    assert!(!env.contains(a));
    // `c` was the last constant, and it is now in the slot of `a`.
    assert_eq!(env.find(c), 1);
    assert_eq!(env.at(env.peek(c)).name, c);
    assert_eq!(env.at(env.peek(b)).name, b);
    // A constant that the environment does not have is not removed.
    assert!(!env.remove(a));
    // The last constant is removed without a move.
    assert!(env.remove(b));
    assert_eq!(env.len(), 1);
    assert_eq!(env.find(c), 1);
    // A new constant gets the next slot.
    env.add(axiom(a, prop));
    assert_eq!(env.find(a), 2);
}

#[test]
fn remove_does_not_change_a_locked_environment_or_an_environment_with_a_cut() {
    let mut st = Store::new();
    let l0 = st.level_zero();
    let prop = st.mk_sort(l0);
    let [a, b] = ["a", "b"].map(|s| name(&mut st, s));
    let mut env = Env::new();
    env.add(axiom(a, prop));
    env.add(axiom(b, prop));
    let mut cut = env.clone();
    cut.set_cut(2);
    assert!(!cut.remove(a));
    assert!(cut.contains(a));
    env.lock();
    assert!(!env.remove(a));
    assert!(env.contains(a));
}

#[test]
fn the_record_gives_each_name_that_find_looks_up() {
    let mut st = Store::new();
    let l0 = st.level_zero();
    let prop = st.mk_sort(l0);
    let [a, b, c] = ["a", "b", "c"].map(|s| name(&mut st, s));
    let mut env = Env::new();
    env.add(axiom(a, prop));
    // A lookup before `record_start` is not recorded.
    env.find(a);
    env.record_start(st.name_count());
    env.find(b);
    env.find(a);
    env.find(b);
    let (names, over) = env.take_record();
    let mut want = vec![a, b];
    want.sort_by_key(|n| n.0);
    assert_eq!(names, want);
    assert!(!over);
    // The record is empty after `take_record`, and it continues.
    env.find(c);
    assert_eq!(env.take_record(), (vec![c], false));
    // A name that the record cannot hold sets the flag.
    let d = name(&mut st, "d");
    env.find(d);
    assert_eq!(env.take_record(), (Vec::new(), true));
    // A lookup after `record_stop` is not recorded.
    env.record_stop();
    env.find(a);
    assert_eq!(env.take_record(), (Vec::new(), false));
    // A new record does not give the names of the old record.
    env.record_start(st.name_count());
    env.find(d);
    assert_eq!(env.take_record(), (vec![d], false));
}

#[test]
fn truncate_removes_the_quotient_record_of_the_removed_constants() {
    let mut st = Store::new();
    let l0 = st.level_zero();
    let prop = st.mk_sort(l0);
    let [a, b, c] = ["a", "b", "c"].map(|s| name(&mut st, s));
    let mut env = Env::new();
    env.add(axiom(a, prop));
    env.add(axiom(b, prop));
    env.mark_quot_initialized();
    env.add(axiom(c, prop));
    // The quotient record stays when its constants stay.
    env.truncate(2);
    assert!(env.quot_initialized());
    // The quotient record goes when its constants go.
    env.truncate(1);
    assert!(!env.quot_initialized());
    env.add(axiom(b, prop));
    assert!(!env.quot_initialized());
}

#[test]
fn a_lookup_with_no_constant_sets_missed_only_for_a_name_that_is_not_known() {
    let mut st = Store::new();
    let l0 = st.level_zero();
    let prop = st.mk_sort(l0);
    let [a, b, c] = ["a", "b", "c"].map(|s| name(&mut st, s));
    let mut env = Env::new();
    env.add(axiom(a, prop));
    env.known_reset();
    env.mark_known(b);
    env.record_start(st.name_count());
    // A lookup that finds the constant, and a lookup of a known name, do not set the flag.
    env.find(a);
    env.find(b);
    assert!(!env.missed());
    env.find(c);
    assert!(env.missed());
    // A new record clears the flag.
    env.record_start(st.name_count());
    assert!(!env.missed());
    env.mark_known(c);
    env.find(c);
    assert!(!env.missed());
    // After `known_reset`, no name is known.
    env.known_reset();
    env.find(b);
    assert!(env.missed());
    // `peek` does not record the lookup.
    env.record_start(st.name_count());
    assert_eq!(env.peek(c), 0);
    assert!(!env.missed());
    assert_eq!(env.take_record(), (Vec::new(), false));
}
