//! The hash function of the store (spec 04.2.3).
//!
//! The hash is a 32-bit mix with the step of MurmurHash3. It has no random seed, so two runs give the same hashes (spec 04.1). A hash is never trusted alone: each table lookup compares the full node after the hash matches.
//!
//! The multiplications are done in `u64` and then cut to `u32`. This gives the wrapping product without `wrapping_mul`, which is outside the modelled functions of spec 10.6.

/// The product of `a` and `b` modulo 2^32.
fn mul32(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) & 0xffff_ffff) as u32
}

/// The sum of `a` and `b` modulo 2^32.
fn add32(a: u32, b: u32) -> u32 {
    ((a as u64 + b as u64) & 0xffff_ffff) as u32
}

/// The rotation of `x` by `r` bits to the left, for `0 < r < 32`. `rotate_left` is outside the modelled functions.
#[allow(clippy::manual_rotate)]
fn rotl(x: u32, r: u32) -> u32 {
    (x << r) | (x >> (32 - r))
}

/// One step of MurmurHash3: mixes the word `k` into the state `h`.
pub fn mix(h: u32, k: u32) -> u32 {
    let mut k1 = mul32(k, 0xcc9e_2d51);
    k1 = rotl(k1, 15);
    k1 = mul32(k1, 0x1b87_3593);
    let h1 = rotl(h ^ k1, 13);
    add32(mul32(h1, 5), 0xe654_6b64)
}

/// Mixes a value of the handle type into `h`. Without the `wide` feature this is `mix`.
#[cfg(not(feature = "wide"))]
pub fn mix_raw(h: u32, x: crate::ids::Raw) -> u32 {
    mix(h, x)
}

/// Mixes a value of the handle type into `h`: the low 32 bits, then the high 32 bits.
#[cfg(feature = "wide")]
pub fn mix_raw(h: u32, x: crate::ids::Raw) -> u32 {
    mix(mix(h, x as u32), (x >> 32) as u32)
}

/// The last step of MurmurHash3: spreads the bits of the state.
pub fn finish(h: u32) -> u32 {
    let mut x = h ^ (h >> 16);
    x = mul32(x, 0x85eb_ca6b);
    x ^= x >> 13;
    x = mul32(x, 0xc2b2_ae35);
    x ^ (x >> 16)
}

/// The hash of a byte string. Each group of four bytes is one word, and the length is mixed in at the end.
pub fn bytes(seed: u32, b: &[u8]) -> u32 {
    let mut h = seed;
    let n = b.len();
    let mut i = 0;
    while i + 4 <= n {
        let w = b[i] as u32
            | (b[i + 1] as u32) << 8
            | (b[i + 2] as u32) << 16
            | (b[i + 3] as u32) << 24;
        h = mix(h, w);
        i += 4;
    }
    let mut tail: u32 = 0;
    let mut shift = 0;
    while i < n {
        tail |= (b[i] as u32) << shift;
        shift += 8;
        i += 1;
    }
    h = mix(h, tail);
    finish(h ^ (n as u32))
}

/// The hash of a 64-bit word.
pub fn word64(h: u32, x: u64) -> u32 {
    mix(mix(h, x as u32), (x >> 32) as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mix_raw_uses_all_bits_of_the_handle() {
        #[cfg(not(feature = "wide"))]
        assert_eq!(mix_raw(7, 5), mix(7, 5));
        #[cfg(feature = "wide")]
        assert_ne!(mix_raw(7, 5), mix_raw(7, 5 | (1 << 40)));
    }

    #[test]
    fn the_hash_is_fixed() {
        // These values fix the hash function. A change to them changes every handle order in a table, so it must be on purpose.
        assert_eq!(mix(0, 0), 0xe654_6b64);
        assert_eq!(bytes(0, b""), finish(mix(0, 0)));
        assert_ne!(bytes(0, b"Nat"), bytes(0, b"Nat\0"));
        assert_ne!(bytes(0, b"ab"), bytes(0, b"ba"));
        assert_ne!(word64(1, 1 << 32), word64(1, 1));
    }
}
