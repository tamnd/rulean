//! Tests of `Env::remove` of the module `env`.

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
    assert_eq!(env.at(env.find(c)).name, c);
    assert_eq!(env.at(env.find(b)).name, b);
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
