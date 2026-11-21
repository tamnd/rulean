//! SHA-256 (FIPS 180-4), for the digests of primitive pinning (spec 05.8).
//!
//! The additions are done in `u64` and then cut to `u32`, and the rotations use two shifts. This avoids `wrapping_add` and `rotate_right`, which are outside the modelled functions of spec 10.6. The proofs do not use the digest values, so Charon reads the functions as opaque.

use alloc::vec::Vec;

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

fn add(a: u32, b: u32) -> u32 {
    ((a as u64 + b as u64) & 0xffff_ffff) as u32
}

#[allow(clippy::manual_rotate)]
fn rotr(x: u32, r: u32) -> u32 {
    (x >> r) | (x << (32 - r))
}

/// One compression step over the 64-byte block at `off`.
#[cfg_attr(rulean_extract, charon::opaque)]
fn compress(h: &mut [u32; 8], m: &[u8], off: usize) {
    let mut w = [0u32; 64];
    let mut t = 0;
    while t < 16 {
        let i = off + 4 * t;
        w[t] = ((m[i] as u32) << 24)
            | ((m[i + 1] as u32) << 16)
            | ((m[i + 2] as u32) << 8)
            | (m[i + 3] as u32);
        t += 1;
    }
    while t < 64 {
        let x = w[t - 15];
        let y = w[t - 2];
        let s0 = rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3);
        let s1 = rotr(y, 17) ^ rotr(y, 19) ^ (y >> 10);
        w[t] = add(add(w[t - 16], s0), add(w[t - 7], s1));
        t += 1;
    }
    let mut a = h[0];
    let mut b = h[1];
    let mut c = h[2];
    let mut d = h[3];
    let mut e = h[4];
    let mut f = h[5];
    let mut g = h[6];
    let mut hh = h[7];
    t = 0;
    while t < 64 {
        let s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        let ch = (e & f) ^ (!e & g);
        let t1 = add(add(add(hh, s1), add(ch, K[t])), w[t]);
        let s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = add(s0, maj);
        hh = g;
        g = f;
        f = e;
        e = add(d, t1);
        d = c;
        c = b;
        b = a;
        a = add(t1, t2);
        t += 1;
    }
    h[0] = add(h[0], a);
    h[1] = add(h[1], b);
    h[2] = add(h[2], c);
    h[3] = add(h[3], d);
    h[4] = add(h[4], e);
    h[5] = add(h[5], f);
    h[6] = add(h[6], g);
    h[7] = add(h[7], hh);
}

/// The SHA-256 digest of `msg`.
#[cfg_attr(rulean_extract, charon::opaque)]
pub fn sha256(msg: &[u8]) -> [u8; 32] {
    let mut x = Hasher::new();
    x.update(msg);
    x.finish()
}

/// A SHA-256 digest that takes its input in parts. The digest of the parts is the digest of their concatenation, so a caller can hash an input that it does not keep in memory.
#[derive(Clone, Debug)]
pub struct Hasher {
    h: [u32; 8],
    /// The bytes after the last full block. There are fewer than 64.
    buf: Vec<u8>,
    /// The number of input bytes.
    len: u64,
}

impl Default for Hasher {
    fn default() -> Hasher {
        Hasher::new()
    }
}

impl Hasher {
    /// A hasher with no input.
    #[cfg_attr(rulean_extract, charon::opaque)]
    pub fn new() -> Hasher {
        Hasher {
            h: H0,
            buf: Vec::with_capacity(64),
            len: 0,
        }
    }

    /// Adds the bytes of `b` to the input.
    #[cfg_attr(rulean_extract, charon::opaque)]
    pub fn update(&mut self, b: &[u8]) {
        let mut i = 0;
        while i < b.len() && self.buf.len() > 0 {
            self.buf.push(b[i]);
            i += 1;
            if self.buf.len() == 64 {
                compress(&mut self.h, &self.buf, 0);
                self.buf.truncate(0);
            }
        }
        while i + 64 <= b.len() {
            compress(&mut self.h, b, i);
            i += 64;
        }
        while i < b.len() {
            self.buf.push(b[i]);
            i += 1;
        }
        self.len += b.len() as u64;
    }

    /// The digest of the input.
    #[cfg_attr(rulean_extract, charon::opaque)]
    pub fn finish(&self) -> [u8; 32] {
        let mut m = self.buf.clone();
        m.push(0x80);
        while m.len() % 64 != 56 {
            m.push(0);
        }
        let bits = self.len * 8;
        let mut k = 0;
        while k < 8 {
            m.push(((bits >> (56 - 8 * k)) & 0xff) as u8);
            k += 1;
        }
        let mut h = self.h;
        let mut off = 0;
        while off < m.len() {
            compress(&mut h, &m, off);
            off += 64;
        }
        let mut out = [0u8; 32];
        let mut j = 0;
        while j < 8 {
            out[4 * j] = (h[j] >> 24) as u8;
            out[4 * j + 1] = (h[j] >> 16) as u8;
            out[4 * j + 2] = (h[j] >> 8) as u8;
            out[4 * j + 3] = h[j] as u8;
            j += 1;
        }
        out
    }
}
