//! Tests of the value arena of engine F (spec 04.5).

use rulean_core::value::{Arena, Closure, Counts, EnvId, Head, SpineId, Value, ValueId};
use rulean_store::{BinderInfo, ExprId, LevelId, LevelListId, NameId};

fn sort(a: &mut Arena, l: u32) -> ValueId {
    a.alloc(Value::Sort(LevelId(l)))
}

/// The arguments of a spine, first argument first.
fn args(a: &Arena, sp: SpineId) -> Vec<ValueId> {
    let mut out = Vec::new();
    a.spine_push_args(sp, &mut out);
    out
}

#[test]
fn values_keep_their_contents() {
    let mut a = Arena::new();
    let s = sort(&mut a, 0);
    let clo = Closure {
        env: EnvId::NIL,
        body: ExprId(7),
    };
    let l = a.alloc(Value::Lam(NameId(3), BinderInfo::Implicit, s, clo));
    assert_eq!(a.get(s), Value::Sort(LevelId(0)));
    assert_eq!(
        a.get(l),
        Value::Lam(NameId(3), BinderInfo::Implicit, s, clo)
    );
}

#[test]
fn env_index_zero_is_the_last_push() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let z = sort(&mut a, 3);
    let e1 = a.env_push(EnvId::NIL, x);
    let e2 = a.env_push(e1, y);
    let e3 = a.env_push(e2, z);
    assert_eq!(a.env_len(EnvId::NIL), 0);
    assert_eq!(a.env_len(e3), 3);
    assert_eq!(a.env_get(e3, 0), Some(z));
    assert_eq!(a.env_get(e3, 1), Some(y));
    assert_eq!(a.env_get(e3, 2), Some(x));
    assert_eq!(a.env_get(e3, 3), None);
    assert_eq!(a.env_get(EnvId::NIL, 0), None);
}

#[test]
fn two_envs_share_a_parent() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let z = sort(&mut a, 3);
    let base = a.env_push(EnvId::NIL, x);
    let left = a.env_push(base, y);
    let right = a.env_push(base, z);
    assert_eq!(a.env_get(left, 0), Some(y));
    assert_eq!(a.env_get(right, 0), Some(z));
    assert_eq!(a.env_get(left, 1), Some(x));
    assert_eq!(a.env_get(right, 1), Some(x));
    assert_eq!(a.counts().envs, 3);
}

#[test]
fn spine_args_are_in_application_order() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let s1 = a.spine_push(SpineId::NIL, x);
    let s2 = a.spine_push(s1, y);
    assert_eq!(a.spine_len(s2), 2);
    assert_eq!(a.spine_arg(s2, 0), Some(x));
    assert_eq!(a.spine_arg(s2, 1), Some(y));
    assert_eq!(a.spine_arg(s2, 2), None);
    assert_eq!(args(&a, s2), vec![x, y]);
    assert_eq!(args(&a, SpineId::NIL), vec![]);
}

#[test]
fn spine_push_args_keeps_the_values_below() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let s1 = a.spine_push(SpineId::NIL, x);
    let s2 = a.spine_push(s1, y);
    let mut stack = vec![y];
    assert_eq!(a.spine_push_args(s2, &mut stack), 2);
    assert_eq!(stack, vec![y, x, y]);
    assert_eq!(a.spine_push_args(SpineId::NIL, &mut stack), 0);
    assert_eq!(stack.len(), 3);
}

#[test]
fn apply_to_a_neutral_shares_the_spine() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let f = a.neutral(Head::Const(NameId(5), LevelListId(0)));
    let fx = a.apply_stuck(f, x).expect("neutral");
    let fxy = a.apply_stuck(fx, y).expect("neutral");
    let spines = a.counts().spines;
    let fxx = a.apply_stuck(fx, x).expect("neutral");
    assert_eq!(a.counts().spines, spines + 1);
    match (a.get(fxy), a.get(fxx)) {
        (Value::Neu(h1, s1), Value::Neu(h2, s2)) => {
            assert_eq!(h1, Head::Const(NameId(5), LevelListId(0)));
            assert_eq!(h1, h2);
            assert_eq!(args(&a, s1), vec![x, y]);
            assert_eq!(args(&a, s2), vec![x, x]);
        }
        other => panic!("not neutral: {other:?}"),
    }
}

#[test]
fn apply_to_a_glued_value_gets_a_new_slot() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let g = a.glued(NameId(9), LevelListId(0));
    let gx = a.apply_stuck(g, x).expect("glued");
    match (a.get(g), a.get(gx)) {
        (Value::Glued(c1, _, sp1, s1), Value::Glued(c2, _, sp2, s2)) => {
            assert_eq!(c1, c2);
            assert_ne!(s1, s2);
            assert_eq!(a.spine_len(sp1), 0);
            assert_eq!(args(&a, sp2), vec![x]);
        }
        other => panic!("not glued: {other:?}"),
    }
}

#[test]
fn apply_to_a_sort_is_not_stuck() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    assert_eq!(a.apply_stuck(x, x), None);
}

#[test]
fn a_slot_is_filled_once() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let y = sort(&mut a, 2);
    let s = a.slot_new();
    assert_eq!(a.slot_get(s), None);
    assert!(a.slot_set(s, x));
    assert!(!a.slot_set(s, y));
    assert_eq!(a.slot_get(s), Some(x));
}

#[test]
fn reset_removes_all_nodes() {
    let mut a = Arena::new();
    let x = sort(&mut a, 1);
    let e = a.env_push(EnvId::NIL, x);
    let _ = a.env_push(e, x);
    let _ = a.spine_push(SpineId::NIL, x);
    let _ = a.glued(NameId(1), LevelListId(0));
    assert_ne!(a.counts(), Counts::default());
    a.reset();
    assert_eq!(a.counts(), Counts::default());
    assert!(!a.full());
    assert_eq!(sort(&mut a, 4), ValueId(0));
}

#[test]
fn a_suspended_argument_has_an_empty_slot_with_no_bits() {
    let mut a = Arena::new();
    let v = a.susp(EnvId::NIL, ExprId(5));
    let s = match a.get(v) {
        Value::Susp(env, e, s) => {
            assert_eq!(env, EnvId::NIL);
            assert_eq!(e, ExprId(5));
            s
        }
        other => panic!("not suspended: {other:?}"),
    };
    assert_eq!(a.slot_get(s), None);
    assert_eq!(a.slot_bits(s), 0);
    let x = sort(&mut a, 1);
    assert!(a.slot_set(s, x));
    a.slot_set_bits(s, 3);
    assert_eq!(a.slot_get(s), Some(x));
    assert_eq!(a.slot_bits(s), 3);
    a.reset();
    assert_eq!(a.counts(), Counts::default());
}
