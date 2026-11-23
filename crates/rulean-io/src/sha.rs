//! SHA-256 of the input with the SHA instructions of the CPU (spec 12.4).
//!
//! The digest of a large input costs much: the portable code of `rulean_core::sha256` uses about 51 instructions for each byte, which is about 18 G instructions on the Init export and about 320 G on the Mathlib export. The SHA extensions of x86_64 (SHA-NI) and the SHA2 extension of aarch64 do the compression in a few instructions for each byte.
//!
//! `Sha256::new` finds at run time if the CPU has the extension. If it has, the hasher uses it. If not, the hasher uses `rulean_core::sha256::Hasher`. The two give the same digest, and the tests compare them on many lengths and on the test vectors of FIPS 180-4.
//!
//! The `unsafe` code in this module is the call of a function with `#[target_feature]` and the loads and stores of the 128-bit registers. Each `unsafe` block has a comment with its invariant.

#![allow(unsafe_code)]

use rulean_core::sha256::Hasher;

/// The round constants of FIPS 180-4, section 4.2.2.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
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

/// The initial hash value of FIPS 180-4, section 5.3.3.
const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// A SHA-256 digest that takes its input in parts, with the SHA instructions of the CPU if it has them.
#[derive(Clone, Debug)]
pub struct Sha256 {
    kind: Kind,
}

#[derive(Clone, Debug)]
enum Kind {
    Soft(Hasher),
    Hard(Hard),
}

/// The state of the hasher with the CPU instructions.
#[derive(Clone, Debug)]
struct Hard {
    h: [u32; 8],
    /// The bytes after the last full block. Only the first `fill` bytes are used.
    buf: [u8; 64],
    fill: usize,
    /// The number of input bytes.
    len: u64,
}

impl Default for Sha256 {
    fn default() -> Sha256 {
        Sha256::new()
    }
}

impl Sha256 {
    /// A hasher with no input. It uses the SHA instructions if the CPU has them.
    pub fn new() -> Sha256 {
        if has_instructions() {
            Sha256 {
                kind: Kind::Hard(Hard {
                    h: H0,
                    buf: [0; 64],
                    fill: 0,
                    len: 0,
                }),
            }
        } else {
            Sha256::portable()
        }
    }

    /// A hasher with no input that uses the portable code of `rulean_core::sha256`.
    pub fn portable() -> Sha256 {
        Sha256 {
            kind: Kind::Soft(Hasher::new()),
        }
    }

    /// True if the hasher uses the SHA instructions of the CPU.
    pub fn hardware(&self) -> bool {
        matches!(self.kind, Kind::Hard(_))
    }

    /// Adds the bytes of `b` to the input.
    pub fn update(&mut self, b: &[u8]) {
        match &mut self.kind {
            Kind::Soft(x) => x.update(b),
            Kind::Hard(x) => x.update(b),
        }
    }

    /// The digest of the input.
    pub fn finish(&self) -> [u8; 32] {
        match &self.kind {
            Kind::Soft(x) => x.finish(),
            Kind::Hard(x) => x.finish(),
        }
    }
}

/// The SHA-256 digest of `b`.
pub fn sha256(b: &[u8]) -> [u8; 32] {
    let mut x = Sha256::new();
    x.update(b);
    x.finish()
}

impl Hard {
    fn update(&mut self, b: &[u8]) {
        self.len += b.len() as u64;
        let mut rest = b;
        if self.fill > 0 {
            let n = (64 - self.fill).min(rest.len());
            self.buf[self.fill..self.fill + n].copy_from_slice(&rest[..n]);
            self.fill += n;
            rest = &rest[n..];
            if self.fill < 64 {
                return;
            }
            let block = self.buf;
            compress(&mut self.h, &block);
            self.fill = 0;
        }
        let full = rest.len() - rest.len() % 64;
        if full > 0 {
            compress(&mut self.h, &rest[..full]);
        }
        let tail = &rest[full..];
        self.buf[..tail.len()].copy_from_slice(tail);
        self.fill = tail.len();
    }

    fn finish(&self) -> [u8; 32] {
        // The padding of FIPS 180-4, section 5.1.1: the byte 0x80, zero bytes, and the length in bits as a big-endian 64-bit number. It fills one or two blocks.
        let mut last = [0u8; 128];
        last[..self.fill].copy_from_slice(&self.buf[..self.fill]);
        last[self.fill] = 0x80;
        let n = if self.fill < 56 { 64 } else { 128 };
        last[n - 8..n].copy_from_slice(&(self.len * 8).to_be_bytes());
        let mut h = self.h;
        compress(&mut h, &last[..n]);
        let mut out = [0u8; 32];
        for (o, w) in out.as_chunks_mut::<4>().0.iter_mut().zip(h) {
            o.copy_from_slice(&w.to_be_bytes());
        }
        out
    }
}

/// True if the CPU has the SHA instructions that `compress` uses.
fn has_instructions() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        std::arch::is_x86_feature_detected!("sha")
            && std::arch::is_x86_feature_detected!("sse2")
            && std::arch::is_x86_feature_detected!("ssse3")
            && std::arch::is_x86_feature_detected!("sse4.1")
    }
    #[cfg(target_arch = "aarch64")]
    {
        std::arch::is_aarch64_feature_detected!("sha2")
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        false
    }
}

/// Compresses the full blocks of `blocks` into `h`. The length of `blocks` is a multiple of 64. Only a `Hard` hasher calls it, and `Sha256::new` makes a `Hard` hasher only if `has_instructions` is true.
fn compress(h: &mut [u32; 8], blocks: &[u8]) {
    debug_assert_eq!(blocks.len() % 64, 0);
    #[cfg(target_arch = "x86_64")]
    {
        // SAFETY: `has_instructions` found the features sha, sse2, ssse3 and sse4.1, which are the features of `compress_x86`.
        unsafe { compress_x86(h, blocks) }
    }
    #[cfg(target_arch = "aarch64")]
    {
        // SAFETY: `has_instructions` found the feature sha2, which is the feature of `compress_arm`.
        unsafe { compress_arm(h, blocks) }
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        let _ = (h, blocks);
        unreachable!("no SHA instructions on this target");
    }
}

/// The compression with the SHA extensions of x86_64. This is the method of the Intel SHA extensions paper (2013): the state is in two registers, ABEF and CDGH, and each `sha256rnds2` does two rounds.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
unsafe fn compress_x86(h: &mut [u32; 8], blocks: &[u8]) {
    use std::arch::x86_64::*;

    // The byte order of each 32-bit word of a block is big-endian, so the shuffle reverses the bytes of each word.
    let mask = _mm_set_epi64x(0x0c0d_0e0f_0809_0a0b, 0x0405_0607_0001_0203);
    // SAFETY: `h` has 8 words, so the two unaligned 16-byte loads are in bounds.
    let (dcba, hgfe) = unsafe {
        (
            _mm_loadu_si128(h.as_ptr().cast::<__m128i>()),
            _mm_loadu_si128(h.as_ptr().add(4).cast::<__m128i>()),
        )
    };
    let cdab = _mm_shuffle_epi32(dcba, 0xb1);
    let efgh = _mm_shuffle_epi32(hgfe, 0x1b);
    let mut abef = _mm_alignr_epi8(cdab, efgh, 8);
    let mut cdgh = _mm_blend_epi16(efgh, cdab, 0xf0);

    for block in blocks.as_chunks::<64>().0 {
        let abef_start = abef;
        let cdgh_start = cdgh;
        // SAFETY: `block` has 64 bytes, so the four unaligned 16-byte loads are in bounds.
        let mut w = unsafe {
            [
                _mm_shuffle_epi8(_mm_loadu_si128(block.as_ptr().cast::<__m128i>()), mask),
                _mm_shuffle_epi8(
                    _mm_loadu_si128(block.as_ptr().add(16).cast::<__m128i>()),
                    mask,
                ),
                _mm_shuffle_epi8(
                    _mm_loadu_si128(block.as_ptr().add(32).cast::<__m128i>()),
                    mask,
                ),
                _mm_shuffle_epi8(
                    _mm_loadu_si128(block.as_ptr().add(48).cast::<__m128i>()),
                    mask,
                ),
            ]
        };
        for i in 0..16 {
            if i >= 4 {
                // The message schedule: W[t] for the next four t from the 16 words before them.
                let x = _mm_sha256msg1_epu32(w[i % 4], w[(i + 1) % 4]);
                let x = _mm_add_epi32(x, _mm_alignr_epi8(w[(i + 3) % 4], w[(i + 2) % 4], 4));
                w[i % 4] = _mm_sha256msg2_epu32(x, w[(i + 3) % 4]);
            }
            // SAFETY: `K` has 64 words and `4 * i + 3 < 64`, so the unaligned 16-byte load is in bounds.
            let k = unsafe { _mm_loadu_si128(K.as_ptr().add(4 * i).cast::<__m128i>()) };
            let x = _mm_add_epi32(w[i % 4], k);
            cdgh = _mm_sha256rnds2_epu32(cdgh, abef, x);
            abef = _mm_sha256rnds2_epu32(abef, cdgh, _mm_shuffle_epi32(x, 0x0e));
        }
        abef = _mm_add_epi32(abef, abef_start);
        cdgh = _mm_add_epi32(cdgh, cdgh_start);
    }

    let feba = _mm_shuffle_epi32(abef, 0x1b);
    let dchg = _mm_shuffle_epi32(cdgh, 0xb1);
    let dcba = _mm_blend_epi16(feba, dchg, 0xf0);
    let hgfe = _mm_alignr_epi8(dchg, feba, 8);
    // SAFETY: `h` has 8 words, so the two unaligned 16-byte stores are in bounds.
    unsafe {
        _mm_storeu_si128(h.as_mut_ptr().cast::<__m128i>(), dcba);
        _mm_storeu_si128(h.as_mut_ptr().add(4).cast::<__m128i>(), hgfe);
    }
}

/// The compression with the SHA2 extension of aarch64. The state is in two registers, ABCD and EFGH, and each pair of `sha256h` and `sha256h2` does four rounds.
#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "sha2")]
unsafe fn compress_arm(h: &mut [u32; 8], blocks: &[u8]) {
    use std::arch::aarch64::*;

    // SAFETY: `h` has 8 words, so the two 4-word loads are in bounds.
    let (mut abcd, mut efgh) = unsafe { (vld1q_u32(h.as_ptr()), vld1q_u32(h.as_ptr().add(4))) };
    for block in blocks.as_chunks::<64>().0 {
        let abcd_start = abcd;
        let efgh_start = efgh;
        // SAFETY: `block` has 64 bytes, so the four 16-byte loads are in bounds. The byte order of each word is big-endian, so `vrev32q_u8` reverses the bytes of each word.
        let mut w = unsafe {
            [
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr()))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(16)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(32)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(block.as_ptr().add(48)))),
            ]
        };
        for i in 0..16 {
            if i >= 4 {
                // The message schedule: W[t] for the next four t from the 16 words before them.
                let x = vsha256su0q_u32(w[i % 4], w[(i + 1) % 4]);
                w[i % 4] = vsha256su1q_u32(x, w[(i + 2) % 4], w[(i + 3) % 4]);
            }
            // SAFETY: `K` has 64 words and `4 * i + 3 < 64`, so the 4-word load is in bounds.
            let k = unsafe { vld1q_u32(K.as_ptr().add(4 * i)) };
            let x = vaddq_u32(w[i % 4], k);
            let abcd_before = abcd;
            abcd = vsha256hq_u32(abcd, efgh, x);
            efgh = vsha256h2q_u32(efgh, abcd_before, x);
        }
        abcd = vaddq_u32(abcd, abcd_start);
        efgh = vaddq_u32(efgh, efgh_start);
    }
    // SAFETY: `h` has 8 words, so the two 4-word stores are in bounds.
    unsafe {
        vst1q_u32(h.as_mut_ptr(), abcd);
        vst1q_u32(h.as_mut_ptr().add(4), efgh);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(d: &[u8; 32]) -> String {
        d.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// The bytes 0, 1, 2, and so on, with a multiplier so that the blocks are not the same.
    fn bytes(n: usize) -> Vec<u8> {
        (0..n).map(|i| (i.wrapping_mul(131) >> 3) as u8).collect()
    }

    #[test]
    fn the_test_vectors_of_fips_180_4() {
        let million = vec![b'a'; 1_000_000];
        let cases: [(&[u8], &str); 4] = [
            (
                b"",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                b"abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
            (
                &million,
                "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0",
            ),
        ];
        for (m, want) in cases {
            assert_eq!(hex(&sha256(m)), want);
            let mut p = Sha256::portable();
            p.update(m);
            assert_eq!(hex(&p.finish()), want);
        }
    }

    #[test]
    fn each_length_gives_the_portable_digest() {
        let all = bytes(1100);
        for n in 0..all.len() {
            let mut p = Sha256::portable();
            p.update(&all[..n]);
            assert_eq!(sha256(&all[..n]), p.finish(), "length {n}");
        }
    }

    #[test]
    fn the_parts_do_not_change_the_digest() {
        let all = bytes(5000);
        let want = sha256(&all);
        for step in [1, 3, 63, 64, 65, 127, 1000] {
            let mut x = Sha256::new();
            for part in all.chunks(step) {
                x.update(part);
            }
            assert_eq!(x.finish(), want, "parts of {step} bytes");
        }
    }

    #[test]
    fn the_hardware_is_used_where_the_cpu_has_it() {
        // CI runs the tests on x86_64 and aarch64 runners. The test prints which code ran, so the log of each runner shows it.
        let x = Sha256::new();
        println!("SHA-256 with the CPU instructions: {}", x.hardware());
        assert_eq!(x.hardware(), has_instructions());
        assert!(!Sha256::portable().hardware());
    }
}
