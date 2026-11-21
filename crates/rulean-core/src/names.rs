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

/// `name::append_after(s)`: adds `s` to the last string part of `n`. A numeric last part stays the last part.
pub fn append_after(st: &mut Store, n: NameId, s: &[u8]) -> NameId {
    match st.name(n) {
        Name::Anon => {
            let r = st.anon();
            st.name_str_bytes(r, s)
        }
        Name::Str(pre, part) => {
            let mut b: Vec<u8> = Vec::new();
            push_bytes(&mut b, st.str_bytes(part));
            push_bytes(&mut b, s);
            st.name_str_bytes(pre, &b)
        }
        Name::Num(pre, k) => {
            let p = append_after(st, pre, s);
            st.name_num(p, k)
        }
    }
}

/// `name::append_after(i)`: adds `_i` to the last string part of `n`.
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
