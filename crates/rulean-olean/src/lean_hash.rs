//! The name hash of Lean (spec 07.3.3).
//!
//! The constant trie of version 4 (`ConstTrie`) sorts the children of each node by the cached `Name.hash` of their keys, and Lean finds a name by binary search with the hash that it computes. So the reader computes the hash as Lean does, and compares it with the cached hash.
//!
//! - `Name.hash`: the anonymous name has the hash 1723. `pre.s` has the hash `mixHash (hash pre) (String.hash s)`, and `pre.n` has the hash `mixHash (hash pre) n`, or 17 for `n` when `n` does not fit in 64 bits (`Init/Prelude.lean`).
//! - `mixHash` is `lean_uint64_mix_hash` of `lean.h`.
//! - `String.hash` is `lean_string_hash`: MurmurHash64A of the UTF-8 bytes with the seed 11 (`runtime/hash.cpp`, `runtime/object.cpp`).

use rulean_store::{Name, NameId, Store};

const M: u64 = 0xc6a4a7935bd1e995;
const R: u32 = 47;

/// The hash of the anonymous name.
pub const ANON: u64 = 1723;

/// `lean_uint64_mix_hash`.
pub fn mix(h: u64, k: u64) -> u64 {
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    (h ^ k).wrapping_mul(M)
}

/// `MurmurHash64A` of MurmurHash2 by Austin Appleby, as `runtime/hash.cpp` of Lean has it.
pub fn murmur64a(b: &[u8], seed: u64) -> u64 {
    let mut h = seed ^ (b.len() as u64).wrapping_mul(M);
    let (blocks, tail) = b.as_chunks::<8>();
    for c in blocks {
        let mut k = u64::from_le_bytes(*c).wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    if !tail.is_empty() {
        for (i, &x) in tail.iter().enumerate() {
            h ^= u64::from(x) << (8 * i);
        }
        h = h.wrapping_mul(M);
    }
    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// `String.hash`.
pub fn string(b: &[u8]) -> u64 {
    murmur64a(b, 11)
}

/// `Name.hash` of `n`. The store keeps numbers of names in 64 bits, so the case of 17 does not occur here.
pub fn name(st: &Store, n: NameId) -> u64 {
    let mut chain = Vec::new();
    let mut cur = n;
    loop {
        match st.name(cur) {
            Name::Anon => break,
            Name::Str(p, _) | Name::Num(p, _) => {
                chain.push(cur);
                cur = p;
            }
        }
    }
    let mut h = ANON;
    while let Some(c) = chain.pop() {
        h = match st.name(c) {
            Name::Str(_, s) => mix(h, string(st.str_bytes(s))),
            Name::Num(_, v) => mix(h, v),
            Name::Anon => h,
        };
    }
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_and_long_strings_use_all_bytes() {
        let a = string(b"Nat");
        let b = string(b"Nat.add_comm");
        assert_ne!(a, b);
        assert_ne!(string(b"abcdefgh"), string(b"abcdefgi"));
        assert_ne!(string(b""), string(b"\0"));
    }

    #[test]
    fn the_name_hash_follows_the_components() {
        let mut st = Store::new();
        let anon = st.anon();
        assert_eq!(name(&st, anon), ANON);
        let nat = st.name_str_bytes(anon, b"Nat");
        assert_eq!(name(&st, nat), mix(ANON, string(b"Nat")));
        let n3 = st.name_num(nat, 3);
        assert_eq!(name(&st, n3), mix(mix(ANON, string(b"Nat")), 3));
    }
}
