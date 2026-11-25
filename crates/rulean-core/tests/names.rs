//! The name operations of `names.rs` against the results of `Name.appendAfter` and `Name.appendIndexAfter` of Lean v4.36.0. The C++ kernel of v4.36.0 calls these Lean functions for the names of the recursor, the minor premises, the induction hypotheses and the auxiliary types of a nested inductive type.

use rulean_core::names;
use rulean_store::{NameId, Store};

/// The name with the parts of `s`. A part with only digits is a number.
fn qname(st: &mut Store, s: &str) -> NameId {
    let mut n = st.anon();
    if s.is_empty() {
        return n;
    }
    for part in s.split('.') {
        n = match part.parse::<u64>() {
            Ok(k) => st.name_num(n, k),
            Err(_) => st.name_str_bytes(n, part.as_bytes()),
        };
    }
    n
}

#[test]
fn append_after_keeps_the_macro_scopes() {
    let mut st = Store::new();
    let cases = [
        ("x", "x_ih"),
        ("A.x", "A.x_ih"),
        // A numeric last part is not the last part of the result.
        ("x.3", "x.3._ih"),
        ("", "_ih"),
        // The suffix goes to the base of a hygienic name.
        ("a._@.M._hyg.5", "a_ih._@.M._hyg.5"),
        ("A.a._@.M.N._hyg.5.6", "A.a_ih._@.M.N._hyg.5.6"),
        // An imported part with scopes.
        ("a._@.I.7.M._hyg.5", "a_ih._@.I.7.M._hyg.5"),
        // A base that ends with a number.
        ("a.2._@.M._hyg.5", "a.2._ih._@.M._hyg.5"),
        // The last `_@` before `_hyg` ends the base.
        ("a._@.b._@.M._hyg.1", "a._@.b_ih._@.M._hyg.1"),
        // A hygienic name without scopes loses the parts after the base.
        ("a._@.M._hyg", "a_ih"),
        // A name with `_hyg` and without `_@` gives the default view of Lean.
        ("M._hyg.1", "_ih"),
    ];
    for (n, want) in cases {
        let a = qname(&mut st, n);
        let got = names::append_after(&mut st, a, b"_ih");
        let w = qname(&mut st, want);
        assert_eq!(got, w, "append_after of {n}");
    }
}

#[test]
fn append_index_is_append_after_with_the_index() {
    let mut st = Store::new();
    let cases = [
        ("u", 2, "u_2"),
        ("T.rec", 1, "T.rec_1"),
        ("x.3", 4, "x.3._4"),
        ("a._@.M._hyg.5", 10, "a_10._@.M._hyg.5"),
    ];
    for (n, i, want) in cases {
        let a = qname(&mut st, n);
        let got = names::append_index(&mut st, a, i);
        let w = qname(&mut st, want);
        assert_eq!(got, w, "append_index of {n} and {i}");
    }
}

#[test]
fn has_macro_scopes_reads_the_last_string_part() {
    let mut st = Store::new();
    for (n, want) in [
        ("a._@.M._hyg.1", true),
        ("a._@.M._hyg", true),
        ("a.1", false),
        ("_hyg.a", false),
        ("", false),
    ] {
        let a = qname(&mut st, n);
        assert_eq!(
            names::has_macro_scopes(&st, a),
            want,
            "has_macro_scopes of {n}"
        );
    }
}
