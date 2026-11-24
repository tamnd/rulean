//! The object model of the Lean runtime, as `lean.h` of Lean v4.36.0 gives it (appendix D, section 2).
//!
//! A Lean value is a word. If bit 0 of the word is 1, the word is a boxed scalar `(n << 1) | 1`. If not, the word is the address of an object. Each object starts with a header of 8 bytes: the reference count (`i32`, bytes 0 to 3), the size of a small object (`u16`, bytes 4 and 5), `m_other` (byte 6) and the tag (byte 7). A constructor object has the tag of its constructor and the number of its object fields in `m_other`. Its object fields follow the header, and its scalar fields follow the object fields.
//!
//! The conversion reads objects through the trait `Heap`. `LiveHeap` reads the memory of the process, and `OwnedHeap` reads objects that it owns. Thus the conversion is safe code, and only `LiveHeap` has `unsafe` code.

use std::collections::BTreeMap;

/// The size of a word and of a pointer field in bytes.
pub const WORD: u64 = 8;

/// The tags of objects that are not constructor objects.
pub mod tag {
    /// The largest tag of a constructor object (`LeanMaxCtorTag`).
    pub const MAX_CTOR: u8 = 243;
    pub const ARRAY: u8 = 246;
    pub const SCALAR_ARRAY: u8 = 248;
    pub const STRING: u8 = 249;
    pub const MPZ: u8 = 250;
}

/// A source of object bytes.
pub trait Heap {
    /// Copies the bytes at address `addr` into `out`. It gives false if the bytes cannot be read.
    fn read(&self, addr: u64, out: &mut [u8]) -> bool;
}

impl<T: Heap + ?Sized> Heap for &T {
    fn read(&self, addr: u64, out: &mut [u8]) -> bool {
        (**self).read(addr, out)
    }
}

/// The boxed scalar of `n`, as `lean_box` makes it.
pub const fn boxed(n: u64) -> u64 {
    (n << 1) | 1
}

/// The header word of an object with tag `tag` and the value `other` in `m_other`. The reference count is 1 and the size field is 0.
pub const fn header(tag: u8, other: u8) -> u64 {
    1 | ((other as u64) << 48) | ((tag as u64) << 56)
}

/// A heap of objects in buffers that it owns. Each object has its own buffer, and the address of the object is the address of its buffer, so a word of one object can point to another object. The tests use it to make objects with the layout of the Lean runtime, and both `OwnedHeap` and `LiveHeap` can read them.
#[derive(Debug, Default)]
pub struct OwnedHeap {
    bufs: Vec<Box<[u64]>>,
    /// The index of each buffer, keyed by its address.
    at: BTreeMap<u64, usize>,
}

impl OwnedHeap {
    pub fn new() -> OwnedHeap {
        OwnedHeap::default()
    }

    /// Adds a buffer with the words `words` and gives its address. A buffer that is empty gets one word, so each address is different.
    pub fn alloc(&mut self, words: &[u64]) -> u64 {
        let mut v = words.to_vec();
        if v.is_empty() {
            v.push(0);
        }
        let b: Box<[u64]> = v.into_boxed_slice();
        let addr = b.as_ptr() as usize as u64;
        self.at.insert(addr, self.bufs.len());
        self.bufs.push(b);
        addr
    }

    /// Adds a constructor object with tag `t`, the object fields `objs` and the scalar bytes `scalars`, and gives its address.
    pub fn ctor(&mut self, t: u8, objs: &[u64], scalars: &[u8]) -> u64 {
        let other = u8::try_from(objs.len()).unwrap_or(u8::MAX);
        let mut w = vec![header(t, other)];
        w.extend_from_slice(objs);
        w.extend(pack(scalars));
        self.alloc(&w)
    }

    /// Adds a string object with the text `s`, and gives its address.
    pub fn string(&mut self, s: &str) -> u64 {
        self.string_bytes(s.as_bytes())
    }

    /// Adds a string object with the UTF-8 bytes `b`, and gives its address. The length field counts the code points, so it counts the bytes that do not continue a code point.
    pub fn string_bytes(&mut self, b: &[u8]) -> u64 {
        let size = b.len() as u64 + 1;
        let length = b.iter().filter(|&&x| x & 0xc0 != 0x80).count() as u64;
        let mut bytes = b.to_vec();
        bytes.push(0);
        let mut w = vec![header(tag::STRING, 0), size, size, length];
        w.extend(pack(&bytes));
        self.alloc(&w)
    }

    /// Adds a big natural number in the GMP encoding with the limbs `limbs`, least significant limb first, and gives its address. The limbs are in a second buffer, as the runtime has them.
    pub fn mpz(&mut self, limbs: &[u64]) -> u64 {
        let d = self.alloc(limbs);
        let n = limbs.len() as u64;
        self.alloc(&[header(tag::MPZ, 0), n | (n << 32), d])
    }
}

/// The bytes `b` in little-endian words. The last word has zero bytes at its end.
fn pack(b: &[u8]) -> Vec<u64> {
    b.chunks(8)
        .map(|c| {
            let mut x = [0u8; 8];
            x[..c.len()].copy_from_slice(c);
            u64::from_le_bytes(x)
        })
        .collect()
}

impl Heap for OwnedHeap {
    fn read(&self, addr: u64, out: &mut [u8]) -> bool {
        let Some((&start, &i)) = self.at.range(..=addr).next_back() else {
            return false;
        };
        let words = &self.bufs[i];
        let off = addr - start;
        let len = words.len() as u64 * WORD;
        let Some(end) = off.checked_add(out.len() as u64) else {
            return false;
        };
        if end > len {
            return false;
        }
        for (k, o) in out.iter_mut().enumerate() {
            let p = off + k as u64;
            let w = words[(p / WORD) as usize];
            *o = w.to_le_bytes()[(p % WORD) as usize];
        }
        true
    }
}
