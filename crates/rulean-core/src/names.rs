//! Name operations of `name.cpp` of the official kernel that the inductive checks use.

use alloc::vec::Vec;
use rulean_store::{Name, NameId, Store};

/// Adds the bytes of `b` to the end of `out`.
fn push_bytes(out: &mut Vec<u8>, b: &[u8]) {
    let mut i = 0;
    while i < b.len() {
        out.push(b[i]);
        i += 1;
    }
}

/// Adds the decimal digits of `v` to the end of `out`.
fn push_dec(out: &mut Vec<u8>, v: u64) {
    let mut digits: Vec<u8> = Vec::new();
    let mut x = v;
    digits.push(b'0' + (x % 10) as u8);
    x /= 10;
    while x > 0 {
        digits.push(b'0' + (x % 10) as u8);
        x /= 10;
    }
    while digits.len() > 0 {
        let i = digits.len() - 1;
        out.push(digits[i]);
        digits.pop();
    }
}

/// True if `a` and `b` have the same bytes.
fn same_bytes(a: &[u8], b: &[u8]) -> bool {
    let mut same = a.len() == b.len();
    let mut i = 0;
    while same && i < a.len() {
        same = a[i] == b[i];
        i += 1;
    }
    same
}

/// `Name.hasMacroScopes` of Lean: the last string part of `n` is `_hyg`.
pub fn has_macro_scopes(st: &Store, n: NameId) -> bool {
    match st.name(n) {
        Name::Str(_, part) => same_bytes(st.str_bytes(part), b"_hyg"),
        Name::Num(pre, _) => has_macro_scopes(st, pre),
        Name::Anon => false,
    }
}

/// `s` after the name `b`: `Name.mkStr p (t ++ s)` if `b` is `p.t` for a string `t`, and `Name.mkStr b s` if not.
fn append_to(st: &mut Store, b: NameId, s: &[u8]) -> NameId {
    match st.name(b) {
        Name::Str(pre, part) => {
            let mut v: Vec<u8> = Vec::new();
            push_bytes(&mut v, st.str_bytes(part));
            push_bytes(&mut v, s);
            st.name_str_bytes(pre, &v)
        }
        _ => st.name_str_bytes(b, s),
    }
}

/// `name::append_after(s)`, which is `Name.appendAfter` of Lean v4.36.0 (`lean_name_append_after`). If `n` has no macro scopes, the result is `append_to(n, s)`. Then a numeric last part does not stay the last part. If `n` is a hygienic name `b._@.<parts>._hyg.<scopes>`, the result is `append_to(b, s)._@.<parts>._hyg.<scopes>`, so the macro scopes stay. `b` is the prefix of the last `_@` part before `_hyg`. As in Lean, a hygienic name without scopes gives `append_to(b, s)`, and a name with `_hyg` and without `_@` gives `append_to(anonymous, s)`, because `extractMacroScopes` panics and gives the default view. Lean also prints a message for the panic, and rulean does not.
pub fn append_after(st: &mut Store, n: NameId, s: &[u8]) -> NameId {
    if !has_macro_scopes(st, n) {
        return append_to(st, n, s);
    }
    // The macro scopes after `_hyg`, from the right.
    let mut scopes: Vec<u64> = Vec::new();
    let mut cur = n;
    loop {
        match st.name(cur) {
            Name::Num(pre, k) => {
                scopes.push(k);
                cur = pre;
            }
            Name::Str(pre, _) => {
                cur = pre;
                break;
            }
            Name::Anon => break,
        }
    }
    // The parts between `_@` and `_hyg`, from the right.
    let mut parts: Vec<NameId> = Vec::new();
    let mut base: Option<NameId> = None;
    loop {
        match st.name(cur) {
            Name::Str(pre, part) => {
                if same_bytes(st.str_bytes(part), b"_@") {
                    base = Some(pre);
                    break;
                }
                parts.push(cur);
                cur = pre;
            }
            Name::Num(pre, _) => {
                parts.push(cur);
                cur = pre;
            }
            Name::Anon => break,
        }
    }
    let b = match base {
        Some(b) => b,
        None => st.anon(),
    };
    let mut r = append_to(st, b, s);
    if base.is_none() || scopes.len() == 0 {
        return r;
    }
    r = st.name_str_bytes(r, b"_@");
    let mut i = parts.len();
    while i > 0 {
        i -= 1;
        r = match st.name(parts[i]) {
            Name::Str(_, part) => st.name_str(r, part),
            Name::Num(_, k) => st.name_num(r, k),
            Name::Anon => r,
        };
    }
    r = st.name_str_bytes(r, b"_hyg");
    let mut j = scopes.len();
    while j > 0 {
        j -= 1;
        r = st.name_num(r, scopes[j]);
    }
    r
}

/// `name::append_after(i)`, which is `Name.appendIndexAfter` of Lean v4.36.0: `append_after` with `_i`.
pub fn append_index(st: &mut Store, n: NameId, i: u64) -> NameId {
    let mut b: Vec<u8> = Vec::new();
    b.push(b'_');
    push_dec(&mut b, i);
    append_after(st, n, &b)
}

/// `name::replace_prefix`: if `n` starts with `prefix`, the prefix is changed to `new_prefix`.
pub fn replace_prefix(st: &mut Store, n: NameId, prefix: NameId, new_prefix: NameId) -> NameId {
    if n == prefix {
        return new_prefix;
    }
    match st.name(n) {
        Name::Anon => n,
        Name::Str(pre, part) => {
            let p = replace_prefix(st, pre, prefix, new_prefix);
            if p == pre { n } else { st.name_str(p, part) }
        }
        Name::Num(pre, k) => {
            let p = replace_prefix(st, pre, prefix, new_prefix);
            if p == pre { n } else { st.name_num(p, k) }
        }
    }
}

/// `is_prefix_of(p, n)`: `n` is `p` or starts with the parts of `p`.
pub fn is_prefix_of(st: &Store, p: NameId, n: NameId) -> bool {
    if n == p {
        return true;
    }
    match st.name(n) {
        Name::Anon => false,
        Name::Str(pre, _) => is_prefix_of(st, p, pre),
        Name::Num(pre, _) => is_prefix_of(st, p, pre),
    }
}

/// `a + b`: the parts of `b` after the parts of `a`.
pub fn concat(st: &mut Store, a: NameId, b: NameId) -> NameId {
    match st.name(b) {
        Name::Anon => a,
        Name::Str(pre, part) => {
            let p = concat(st, a, pre);
            st.name_str(p, part)
        }
        Name::Num(pre, k) => {
            let p = concat(st, a, pre);
            st.name_num(p, k)
        }
    }
}

/// `I.rec`, the name of the recursor of `I` (`mk_rec_name`).
pub fn rec_name(st: &mut Store, n: NameId) -> NameId {
    st.name_str_bytes(n, b"rec")
}
