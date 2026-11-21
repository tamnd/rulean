//! Tests of the store: hash-consing, side records, names, levels and literals.

use rulean_nat::Nat;
use rulean_store::{
    BinderInfo, Expr, ExprId, Flags, Kind, Level, Literal, Name, SATURATED, Store, Tier,
};

fn name(s: &mut Store, dotted: &str) -> rulean_store::NameId {
    let mut n = s.anon();
    for part in dotted.split('.') {
        n = s.name_str_bytes(n, part.as_bytes());
    }
    n
}

#[test]
fn equal_terms_have_equal_handles() {
    let mut s = Store::new();
    let nat = name(&mut s, "Nat");
    let empty = s.level_list_empty();
    let c1 = s.mk_const(nat, empty);
    let c2 = s.mk_const(nat, empty);
    assert_eq!(c1, c2);
    let x = s.anon();
    let b0 = s.mk_bvar(0);
    let id1 = s.mk_lam(x, BinderInfo::Default, c1, b0);
    let id2 = s.mk_lam(x, BinderInfo::Default, c2, b0);
    assert_eq!(id1, id2);
    // The binder information is part of the node.
    let id3 = s.mk_lam(x, BinderInfo::Implicit, c1, b0);
    assert_ne!(id1, id3);
    // A pi with the same fields is a different node.
    let p = s.mk_pi(x, BinderInfo::Default, c1, b0);
    assert_ne!(id1, p);
    assert_eq!(p.kind(), Kind::Pi);
    assert_eq!(p.tier(), Tier::Frozen);
    assert_eq!(
        s.node(id1),
        Expr::Lam(rulean_store::Binder {
            name: x,
            info: BinderInfo::Default,
            dom: c1,
            body: b0
        })
    );
    let a1 = s.mk_app(id1, c1);
    let a2 = s.mk_app(id2, c2);
    assert_eq!(a1, a2);
    assert_eq!(s.expr_count(Kind::App), 1);
    assert_eq!(s.expr_total(), 6);
}

#[test]
fn bvar_zero_is_found_again() {
    // ExprId(0) is the handle of the first bound variable node. The lookup must find it like any other node.
    let mut s = Store::new();
    let b0 = s.mk_bvar(0);
    assert_eq!(b0, ExprId(0));
    assert_eq!(s.mk_bvar(0), b0);
    assert_eq!(s.expr_count(Kind::BVar), 1);
}

#[test]
fn loose_ranges_and_flags() {
    let mut s = Store::new();
    let x = s.anon();
    let b0 = s.mk_bvar(0);
    let b2 = s.mk_bvar(2);
    assert_eq!(s.loose_range(b0), 1);
    assert_eq!(s.loose_range(b2), 3);
    let app = s.mk_app(b0, b2);
    assert_eq!(s.loose_range(app), 3);
    let ty = s.mk_sort(s.level_zero());
    assert!(s.is_closed(ty));
    let lam = s.mk_lam(x, BinderInfo::Default, ty, app);
    assert_eq!(s.loose_range(lam), 2);
    let lam2 = s.mk_lam(x, BinderInfo::Default, ty, lam);
    let lam3 = s.mk_lam(x, BinderInfo::Default, ty, lam2);
    assert!(s.is_closed(lam3));
    // The domain is outside the binder.
    let pi = s.mk_pi(x, BinderInfo::Default, b0, ty);
    assert_eq!(s.loose_range(pi), 1);
    let let_ = s.mk_let(x, ty, b0, b0);
    assert_eq!(s.loose_range(let_), 1);
    assert!(s.flags(let_).has(Flags::HAS_LET));
    assert!(!s.flags(lam).has(Flags::HAS_LET));
    // A large index saturates, and a saturated range stays saturated under binders.
    let big = s.mk_bvar(u32::MAX);
    assert_eq!(s.loose_range(big), SATURATED);
    let under = s.mk_lam(x, BinderInfo::Default, ty, big);
    assert_eq!(s.loose_range(under), SATURATED);
    let near = s.mk_bvar(SATURATED - 2);
    assert_eq!(s.loose_range(near), SATURATED - 1);
}

#[test]
fn level_params_and_free_variables_set_flags() {
    let mut s = Store::new();
    let u = name(&mut s, "u");
    let pu = s.level_param(u);
    let z = s.level_zero();
    let one = s.level_succ(z);
    let m = s.level_max(one, pu);
    assert!(s.level_has_param(m));
    assert!(!s.level_has_param(one));
    let sort_u = s.mk_sort(m);
    let sort_1 = s.mk_sort(one);
    assert!(s.flags(sort_u).has(Flags::HAS_LEVEL_PARAM));
    assert!(!s.flags(sort_1).has(Flags::HAS_LEVEL_PARAM));
    let list = s.level_list(&[one, pu]);
    assert_eq!(s.level_list_items(list), &[one, pu]);
    assert_eq!(s.level_list(&[one, pu]), list);
    assert_ne!(s.level_list(&[pu, one]), list);
    assert_eq!(s.level_list(&[]), s.level_list_empty());
    let list_name = name(&mut s, "List");
    let c = s.mk_const(list_name, list);
    assert!(s.flags(c).has(Flags::HAS_LEVEL_PARAM));
    let fv = s.mk_fvar(0, sort_1);
    assert!(s.flags(fv).has(Flags::HAS_FVAR));
    assert!(s.is_closed(fv));
    let app = s.mk_app(c, fv);
    assert!(s.flags(app).has(Flags::HAS_FVAR | Flags::HAS_LEVEL_PARAM));
    assert_eq!(s.level(m), Level::Max(one, pu));
    assert_eq!(s.level(pu), Level::Param(u));
    assert_eq!(s.level_imax(one, pu), s.level_imax(one, pu));
    assert_ne!(s.level_imax(one, pu), m);
}

#[test]
fn names() {
    let mut s = Store::new();
    let a = name(&mut s, "Lean.Meta.foo");
    let b = name(&mut s, "Lean.Meta.foo");
    assert_eq!(a, b);
    let c = s.name_num(a, 3);
    assert_eq!(s.name_num(a, 3), c);
    assert_ne!(s.name_num(a, 4), c);
    assert_eq!(s.name_text(c), b"Lean.Meta.foo.3");
    assert_eq!(s.name_text(s.anon()), b"[anonymous]");
    let Name::Num(pre, 3) = s.name(c) else {
        panic!("not a number name")
    };
    assert_eq!(pre, a);
    // A string part and a number part with the same text are different names.
    let anon = s.anon();
    let s3 = s.name_str_bytes(anon, b"3");
    let n3 = s.name_num(anon, 3);
    assert_ne!(s3, n3);
    // anon, Lean, Lean.Meta, Lean.Meta.foo, foo.3, foo.4, "3" and 3.
    assert_eq!(s.name_count(), 8);
}

#[test]
fn literals() {
    let mut s = Store::new();
    let big = Nat::from_limbs(vec![1, 2, 3]);
    let n1 = s.intern_nat(big.clone());
    let n2 = s.intern_nat(big.clone());
    assert_eq!(n1, n2);
    assert_eq!(s.nat(n1), &big);
    // Two numbers that differ only above 2^64 must have different hashes (spec 04.2.3).
    let other = s.intern_nat(Nat::from_limbs(vec![1, 2, 4]));
    assert_ne!(s.nat_hash(n1), s.nat_hash(other));
    let e1 = s.mk_nat_lit(n1);
    assert_eq!(s.mk_nat_lit(n2), e1);
    assert!(s.flags(e1).has(Flags::HAS_LIT));
    let hello = s.intern_str("héllo".as_bytes());
    let e2 = s.mk_str_lit(hello);
    assert_ne!(e1, e2);
    assert_eq!(s.node(e2), Expr::Lit(Literal::Str(hello)));
    assert_eq!(s.str_bytes(hello), "héllo".as_bytes());
    // The literal 3 and the string "3" are different nodes.
    let three = s.intern_nat(Nat::from_u64(3));
    let three_s = s.intern_str(b"3");
    assert_ne!(s.mk_nat_lit(three), s.mk_str_lit(three_s));
}

#[test]
fn hashes_are_structural_and_deterministic() {
    // Two stores that make the same term in a different order give the term the same hash, but maybe other handles.
    let mut s1 = Store::new();
    let mut s2 = Store::new();
    let n1 = name(&mut s1, "f");
    let _ = name(&mut s2, "unused");
    let n2 = name(&mut s2, "f");
    let e1 = s1.mk_bvar(5);
    let _ = s2.mk_bvar(9);
    let e2 = s2.mk_bvar(5);
    assert_ne!(e1, e2);
    let el = s1.level_list_empty();
    let c1 = s1.mk_const(n1, el);
    let el2 = s2.level_list_empty();
    let c2 = s2.mk_const(n2, el2);
    let a1 = s1.mk_app(c1, e1);
    let a2 = s2.mk_app(c2, e2);
    assert_eq!(s1.hash(a1), s2.hash(a2));
}

#[test]
fn many_nodes() {
    let mut s = Store::new();
    let x = s.anon();
    let z = s.level_zero();
    let ty = s.mk_sort(z);
    let mut e = ty;
    let mut made = Vec::new();
    for i in 0..20_000u32 {
        let b = s.mk_bvar(i % 50);
        e = if i % 3 == 0 {
            s.mk_app(e, b)
        } else {
            s.mk_lam(x, BinderInfo::Default, ty, e)
        };
        made.push(e);
    }
    // Making the terms again gives the same handles and no new nodes.
    let total = s.expr_total();
    let mut e2 = ty;
    for (i, want) in made.iter().enumerate() {
        let b = s.mk_bvar(i as u32 % 50);
        e2 = if i % 3 == 0 {
            s.mk_app(e2, b)
        } else {
            s.mk_lam(x, BinderInfo::Default, ty, e2)
        };
        assert_eq!(e2, *want);
    }
    assert_eq!(s.expr_total(), total);
    assert!(!s.is_full());
    let m = s.memory();
    assert!(m.exprs > 0 && m.tables > 0);
    assert_eq!(
        m.total(),
        m.exprs + m.names + m.strings + m.levels + m.nats + m.tables
    );
}

#[test]
fn scratch_tier() {
    let mut s = Store::new();
    let nat = name(&mut s, "Nat");
    let empty = s.level_list_empty();
    let c = s.mk_const(nat, empty);
    let x = s.anon();
    let b0 = s.mk_bvar(0);
    let lam = s.mk_lam(x, BinderInfo::Default, c, b0);
    let frozen = s.expr_total();
    s.set_scratch(true);
    assert!(s.uses_scratch());
    // A node that is in the frozen tier keeps its frozen handle.
    assert_eq!(s.mk_lam(x, BinderInfo::Default, c, b0), lam);
    // A new node with frozen fields goes to the scratch tier.
    let a = s.mk_app(lam, c);
    assert_eq!(a.tier(), Tier::Scratch);
    assert_eq!(s.mk_app(lam, c), a);
    assert_eq!(s.node(a), Expr::App(lam, c));
    // A node with a scratch field also goes to the scratch tier, and its side record covers the field.
    let f = s.mk_fvar(0, c);
    assert_eq!(f.tier(), Tier::Scratch);
    let af = s.mk_app(a, f);
    assert_eq!(af.tier(), Tier::Scratch);
    assert!(s.flags(af).has(Flags::HAS_FVAR));
    assert_eq!(s.hash(a), {
        let mut t = Store::new();
        let nat = name(&mut t, "Nat");
        let empty = t.level_list_empty();
        let c = t.mk_const(nat, empty);
        let x = t.anon();
        let b0 = t.mk_bvar(0);
        let lam = t.mk_lam(x, BinderInfo::Default, c, b0);
        let a = t.mk_app(lam, c);
        t.hash(a)
    });
    assert_eq!(s.expr_total(), frozen);
    assert_eq!(s.scratch_total(), 3);
    s.clear_scratch();
    assert!(!s.uses_scratch());
    assert_eq!(s.scratch_total(), 0);
    // After the clear, the same term is made again in the frozen tier.
    let a2 = s.mk_app(lam, c);
    assert_eq!(a2.tier(), Tier::Frozen);
    assert_eq!(s.expr_total(), frozen + 1);
    // A second declaration with scratch on finds the frozen node.
    s.set_scratch(true);
    assert_eq!(s.mk_app(lam, c), a2);
    s.clear_scratch();
}
