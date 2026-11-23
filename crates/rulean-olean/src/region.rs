//! The object region of the parts of one module (spec 07.3.2 and 07.3.3).
//!
//! The reader never maps a file at its base address. It keeps the bytes of each part in a vector and translates each pointer to a part and an offset. Before the typed decoder runs, `Part::new` walks each part from start to end. The walk checks the header and the size of each object and marks the offset where each object starts. A pointer that is not the start of an object in the module is an error.

use crate::header::{self, Header};
use crate::{Fault, FaultKind};

/// The offset of the root pointer in a version 2 file.
const ROOT_AT: usize = header::HEADER_BYTES;

/// The offset of the first object in a version 2 file.
pub const DATA_AT: usize = ROOT_AT + 8;

/// The offset of the `data_size` field in a version 3 or 4 file. The data starts after it, with the root pointer.
const DATA_SIZE_AT: usize = header::HEADER_BYTES;

/// The tags of the Lean runtime objects (lean.h).
pub mod tag {
    pub const MAX_CTOR: u8 = 243;
    pub const ARRAY: u8 = 246;
    pub const SCALAR_ARRAY: u8 = 248;
    pub const STRING: u8 = 249;
    pub const MPZ: u8 = 250;
    pub const THUNK: u8 = 251;
    pub const TASK: u8 = 252;
    pub const REF: u8 = 253;
}

/// The size of an object header.
pub const WORD: usize = 8;

/// Rounds `n` up to a multiple of 8.
pub fn round8(n: usize) -> Option<usize> {
    n.checked_add(7).map(|m| m & !7)
}

/// One part of a module: an `.olean`, `.olean.server` or `.olean.private` file.
#[derive(Debug)]
pub struct Part {
    pub header: Header,
    pub bytes: Vec<u8>,
    /// The root pointer.
    pub root: u64,
    /// Bit `i` is set if an object starts at offset `8 * i`.
    starts: Vec<u64>,
    /// The number of objects.
    pub objects: usize,
    /// The offset of the root pointer.
    root_at: usize,
    /// The offset after the last object.
    data_end: usize,
}

impl Part {
    /// Reads the header of `bytes` and walks the objects.
    ///
    /// In version 2, the root pointer follows the header, and the objects go to the end of the file. In versions 3 and 4, the header is followed by `data_size`, then `data_size` bytes of data (the root pointer and the objects), and then the closure section and the library table. The reader supports only a file without closures, so the two sections must be the two counts 0.
    pub fn new(bytes: Vec<u8>) -> Result<Part, Fault> {
        let header = header::read(&bytes)?;
        let (root_at, data_end) = layout(&header, &bytes)?;
        let root = word(&bytes, root_at);
        let mut starts = vec![0u64; bytes.len() / (64 * WORD) + 1];
        let mut off = root_at + WORD;
        let mut objects = 0;
        while off < data_end {
            let size = object_size(&bytes[..data_end], off)?;
            let i = off / WORD;
            starts[i / 64] |= 1 << (i % 64);
            objects += 1;
            off += size;
        }
        if off != data_end {
            return Err(Fault::new(
                FaultKind::Malformed,
                off as u64,
                "the last object goes past the end of the data",
            ));
        }
        Ok(Part {
            header,
            bytes,
            root,
            starts,
            objects,
            root_at,
            data_end,
        })
    }

    /// True if an object starts at `off`.
    pub fn starts_at(&self, off: usize) -> bool {
        let i = off / WORD;
        off.is_multiple_of(WORD)
            && off > self.root_at
            && off < self.data_end
            && self.starts[i / 64] & (1 << (i % 64)) != 0
    }

    /// The first address after the part.
    fn end(&self) -> Option<u64> {
        self.header.base.checked_add(self.bytes.len() as u64)
    }
}

/// The offset of the root pointer and the offset after the data of a file with header `h`.
fn layout(h: &Header, b: &[u8]) -> Result<(usize, usize), Fault> {
    let bad = |at: usize, msg: &str| Fault::new(FaultKind::Malformed, at as u64, msg);
    if h.version == 2 {
        if b.len() < DATA_AT {
            return Err(bad(0, "the file has no root pointer"));
        }
        return Ok((ROOT_AT, b.len()));
    }
    let root_at = DATA_SIZE_AT + 8;
    if b.len() < root_at + WORD {
        return Err(bad(DATA_SIZE_AT, "the file has no data"));
    }
    let size = usize::try_from(word(b, DATA_SIZE_AT)).unwrap_or(usize::MAX);
    let data_end = root_at
        .checked_add(size)
        .filter(|&e| e <= b.len() && size >= WORD && size.is_multiple_of(WORD))
        .ok_or_else(|| bad(DATA_SIZE_AT, "the data size does not fit the file"))?;
    // The closure section: a `u32` count and the offsets. Then the library table: a `u32` count and the entries.
    let rest = &b[data_end..];
    if rest.len() < 8 {
        return Err(bad(data_end, "the file has no closure section"));
    }
    let closures = u32::from_le_bytes([rest[0], rest[1], rest[2], rest[3]]);
    if closures != 0 {
        return Err(Fault::new(
            FaultKind::Decline,
            data_end as u64,
            "the file has closures, this reader supports only files without closures",
        ));
    }
    let libs = u32::from_le_bytes([rest[4], rest[5], rest[6], rest[7]]);
    if libs != 0 {
        return Err(bad(data_end + 4, "the file has libraries but no closures"));
    }
    if rest.len() != 8 {
        return Err(bad(
            data_end + 8,
            "the file has bytes after the library table",
        ));
    }
    Ok((root_at, data_end))
}

/// The word at `off`. The caller makes sure that the 8 bytes are in `b`.
pub fn word(b: &[u8], off: usize) -> u64 {
    let mut w = [0u8; 8];
    w.copy_from_slice(&b[off..off + 8]);
    u64::from_le_bytes(w)
}

/// The size of the object at `off`, rounded up to a multiple of 8. The function checks that the object is in `b`.
fn object_size(b: &[u8], off: usize) -> Result<usize, Fault> {
    let bad = |msg: &str| Fault::new(FaultKind::Malformed, off as u64, msg);
    if b.len() - off < WORD {
        return Err(bad("an object header goes past the end of the file"));
    }
    let rc = word(b, off) as u32;
    let cs = u16::from_le_bytes([b[off + 4], b[off + 5]]) as usize;
    let other = b[off + 6];
    let t = b[off + 7];
    if rc != 0 {
        return Err(bad("an object has a reference count that is not zero"));
    }
    let size = match t {
        tag::ARRAY | tag::SCALAR_ARRAY | tag::STRING => {
            let fixed = if t == tag::STRING { 4 * WORD } else { 3 * WORD };
            if cs != 1 {
                return Err(bad("a big object has a size field that is not 1"));
            }
            if b.len() - off < fixed {
                return Err(bad("an object header goes past the end of the file"));
            }
            let len = word(b, off + WORD);
            let cap = word(b, off + 2 * WORD);
            if len > cap {
                return Err(bad("an object has a size larger than its capacity"));
            }
            let elem = match t {
                tag::ARRAY => WORD as u64,
                tag::SCALAR_ARRAY => u64::from(other & 0x7f),
                _ => 1,
            };
            cap.checked_mul(elem)
                .and_then(|n| n.checked_add(fixed as u64))
                .and_then(|n| usize::try_from(n).ok())
                .and_then(round8)
                .ok_or_else(|| bad("an object is too large"))?
        }
        _ if t <= tag::MAX_CTOR
            || t == tag::MPZ
            || t == tag::THUNK
            || t == tag::TASK
            || t == tag::REF =>
        {
            if cs < WORD || !cs.is_multiple_of(WORD) {
                return Err(bad("an object has a size that is not a multiple of 8"));
            }
            cs
        }
        _ => return Err(bad("an object has a tag that cannot be in an olean file")),
    };
    if size > b.len() - off {
        return Err(bad("an object goes past the end of the file"));
    }
    Ok(size)
}

/// A position in the parts of a module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct At {
    pub part: usize,
    pub off: usize,
}

/// A view of a constructor object.
#[derive(Clone, Copy, Debug)]
pub struct Ctor {
    pub at: At,
    pub tag: u8,
    pub objs: usize,
}

/// The value of a field: a boxed scalar or a pointer to an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field {
    Scalar(u64),
    Object(At),
}

/// The parts of one module.
#[derive(Debug, Default)]
pub struct Region {
    pub parts: Vec<Part>,
}

impl Region {
    /// Adds a part. A later part can point into the earlier parts, so the parts must not overlap. The root of the part must point to an object in this part or in an earlier part. The decoder does not read the root of the server part, so this check finds a server part that is cut after an object.
    pub fn push(&mut self, p: Part) -> Result<(), Fault> {
        let end = p
            .end()
            .ok_or_else(|| Fault::new(FaultKind::Malformed, 80, "the base address is too large"))?;
        for q in &self.parts {
            let qend = q.end().unwrap_or(u64::MAX);
            if p.header.base < qend && q.header.base < end {
                return Err(Fault::new(
                    FaultKind::Malformed,
                    80,
                    "two parts of the module overlap in memory",
                ));
            }
        }
        let root = p.root;
        let p_root_at = p.root_at;
        let after = At {
            part: self.parts.len(),
            off: p.bytes.len(),
        };
        self.parts.push(p);
        let ok = match self.field(after, root) {
            Ok(Field::Object(_)) => Ok(()),
            Ok(Field::Scalar(_)) => Err(Fault::new(
                FaultKind::Malformed,
                p_root_at as u64,
                "the root is a scalar",
            )),
            Err(f) => Err(f),
        };
        if let Err(f) = ok {
            self.parts.pop();
            return Err(f.in_part(after.part));
        }
        Ok(())
    }

    /// The bytes of a part.
    pub fn bytes(&self, part: usize) -> &[u8] {
        &self.parts[part].bytes
    }

    /// Translates a pointer that `from` holds. The target must be the start of an object in the same part before `from`, or in an earlier part. So the object graph has no cycle.
    pub fn field(&self, from: At, ptr: u64) -> Result<Field, Fault> {
        if ptr & 1 == 1 {
            return Ok(Field::Scalar(ptr >> 1));
        }
        let bad =
            |msg: &str| Fault::new(FaultKind::Malformed, from.off as u64, msg).in_part(from.part);
        for (i, p) in self.parts.iter().enumerate().take(from.part + 1) {
            let base = p.header.base;
            if ptr >= base && ptr - base < p.bytes.len() as u64 {
                let off = (ptr - base) as usize;
                if !p.starts_at(off) {
                    return Err(bad("a pointer is not the start of an object"));
                }
                let at = At { part: i, off };
                if at >= from {
                    return Err(bad("a pointer does not point to an earlier object"));
                }
                return Ok(Field::Object(at));
            }
        }
        Err(bad("a pointer is outside the parts of the module"))
    }

    /// The field `i` of the object at `at`. The caller has checked the shape of the object.
    pub fn ptr(&self, at: At, i: usize) -> u64 {
        word(self.bytes(at.part), at.off + WORD + i * WORD)
    }

    /// The tag of the object at `at`.
    pub fn tag(&self, at: At) -> u8 {
        self.bytes(at.part)[at.off + 7]
    }

    /// Checks that the object at `at` is a constructor with one of `tags`, `objs` object fields and `scalars` bytes of scalar fields.
    pub fn ctor(
        &self,
        at: At,
        tags: core::ops::RangeInclusive<u8>,
        objs: usize,
        scalars: usize,
        what: &str,
    ) -> Result<Ctor, Fault> {
        let b = self.bytes(at.part);
        let t = b[at.off + 7];
        let other = b[at.off + 6] as usize;
        let cs = u16::from_le_bytes([b[at.off + 4], b[at.off + 5]]) as usize;
        let want = round8(WORD + objs * WORD + scalars).unwrap_or(0);
        if !tags.contains(&t) || other != objs || cs != want {
            return Err(Fault::new(
                FaultKind::Malformed,
                at.off as u64,
                format!("the object is not a {what}: tag {t}, {other} fields, size {cs}"),
            )
            .in_part(at.part));
        }
        Ok(Ctor { at, tag: t, objs })
    }

    /// The scalar byte at `k` of a constructor.
    pub fn u8_at(&self, c: Ctor, k: usize) -> u8 {
        self.bytes(c.at.part)[c.at.off + WORD + c.objs * WORD + k]
    }

    /// The scalar `u32` at `k` of a constructor.
    pub fn u32_at(&self, c: Ctor, k: usize) -> u32 {
        let b = self.bytes(c.at.part);
        let o = c.at.off + WORD + c.objs * WORD + k;
        u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
    }

    /// The scalar byte at `k` of a constructor, as a boolean. A value other than 0 or 1 is an error.
    pub fn bool_at(&self, c: Ctor, k: usize) -> Result<bool, Fault> {
        match self.u8_at(c, k) {
            0 => Ok(false),
            1 => Ok(true),
            v => Err(Fault::new(
                FaultKind::Malformed,
                c.at.off as u64,
                format!("a boolean field has the value {v}"),
            )
            .in_part(c.at.part)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A version 2 file with the objects `objs` after the header. The root points to the last object.
    pub fn file(base: u64, objs: &[Vec<u8>]) -> Vec<u8> {
        let mut b = vec![0u8; DATA_AT];
        b[..5].copy_from_slice(header::MAGIC);
        b[5] = 2;
        b[6] = header::FLAG_GMP;
        b[7..13].copy_from_slice(b"4.36.0");
        b[80..88].copy_from_slice(&base.to_le_bytes());
        let mut last = 0;
        for o in objs {
            last = b.len();
            b.extend_from_slice(o);
        }
        b[88..96].copy_from_slice(&(base + last as u64).to_le_bytes());
        b
    }

    /// A constructor object.
    pub fn ctor(t: u8, fields: &[u64], scalars: &[u8]) -> Vec<u8> {
        let size = round8(WORD + 8 * fields.len() + scalars.len()).expect("size");
        let mut o = vec![0u8; 4];
        o.extend_from_slice(&(size as u16).to_le_bytes());
        o.push(fields.len() as u8);
        o.push(t);
        for f in fields {
            o.extend_from_slice(&f.to_le_bytes());
        }
        o.extend_from_slice(scalars);
        o.resize(size, 0);
        o
    }

    /// A version 4 file with the objects `objs`: the header, `data_size`, the root pointer, the objects, and the closure count and the library count. The root points to the last object.
    pub fn file4(base: u64, objs: &[Vec<u8>], closures: u32, libs: u32) -> Vec<u8> {
        let mut b = file(base, &[]);
        b[5] = 4;
        b.truncate(88);
        b.extend_from_slice(&[0u8; 16]);
        let mut last = 0;
        for o in objs {
            last = b.len();
            b.extend_from_slice(o);
        }
        let size = (b.len() - 96) as u64;
        b[88..96].copy_from_slice(&size.to_le_bytes());
        b[96..104].copy_from_slice(&(base + last as u64).to_le_bytes());
        b.extend_from_slice(&closures.to_le_bytes());
        b.extend_from_slice(&libs.to_le_bytes());
        b
    }

    #[test]
    fn the_walk_of_version_4_stops_at_the_end_of_the_data() {
        let b = file4(
            0x1000,
            &[ctor(1, &[1], &[]), ctor(0, &[0x1000 + 104], &[7])],
            0,
            0,
        );
        let p = Part::new(b).expect("part");
        assert_eq!(p.objects, 2);
        assert!(p.starts_at(104));
        assert!(p.starts_at(120));
        assert!(!p.starts_at(96));
        assert_eq!(p.root, 0x1000 + 120);
        let mut rg = Region::default();
        rg.push(p).expect("push");
    }

    #[test]
    fn version_4_needs_empty_trailing_sections() {
        let objs = [ctor(1, &[1], &[])];
        let e = Part::new(file4(0x1000, &objs, 1, 0)).expect_err("closures");
        assert_eq!(e.kind, FaultKind::Decline);
        let e = Part::new(file4(0x1000, &objs, 0, 1)).expect_err("libraries");
        assert_eq!(e.kind, FaultKind::Malformed);
        let mut b = file4(0x1000, &objs, 0, 0);
        b.push(0);
        assert_eq!(Part::new(b).expect_err("extra").kind, FaultKind::Malformed);
        let mut b = file4(0x1000, &objs, 0, 0);
        b[88] = 0xff;
        assert_eq!(Part::new(b).expect_err("size").kind, FaultKind::Malformed);
    }

    #[test]
    fn the_walk_finds_each_object() {
        let b = file(0x1000, &[ctor(1, &[1], &[]), ctor(0, &[0x1000 + 96], &[7])]);
        let p = Part::new(b).expect("part");
        assert_eq!(p.objects, 2);
        assert!(p.starts_at(96));
        assert!(p.starts_at(112));
        assert!(!p.starts_at(104));
        assert_eq!(p.root, 0x1000 + 112);
    }

    #[test]
    fn a_reference_count_is_an_error() {
        let mut o = ctor(1, &[1], &[]);
        o[0] = 1;
        assert!(Part::new(file(0x1000, &[o])).is_err());
    }

    #[test]
    fn a_short_object_is_an_error() {
        let mut b = file(0x1000, &[ctor(1, &[1, 1], &[])]);
        b.truncate(b.len() - 8);
        assert!(Part::new(b).is_err());
    }

    #[test]
    fn a_closure_is_an_error() {
        let mut o = ctor(0, &[1], &[]);
        o[7] = 245;
        assert!(Part::new(file(0x1000, &[o])).is_err());
    }

    #[test]
    fn pointers_go_back_only() {
        let base = 0x1000;
        let b = file(base, &[ctor(1, &[1], &[]), ctor(0, &[base + 96], &[])]);
        let mut r = Region::default();
        r.push(Part::new(b).expect("part")).expect("push");
        let second = At { part: 0, off: 112 };
        let first = At { part: 0, off: 96 };
        assert_eq!(
            r.field(second, base + 96).expect("back"),
            Field::Object(first)
        );
        assert!(r.field(first, base + 112).is_err(), "a forward pointer");
        assert!(r.field(first, base + 96).is_err(), "a pointer to itself");
        assert!(r.field(second, base + 104).is_err(), "inside an object");
        assert!(r.field(second, 8).is_err(), "outside the file");
        assert_eq!(r.field(second, 7).expect("scalar"), Field::Scalar(3));
    }

    #[test]
    fn parts_must_not_overlap() {
        let mut r = Region::default();
        r.push(Part::new(file(0x1000, &[ctor(1, &[1], &[])])).expect("part"))
            .expect("push");
        assert!(
            r.push(Part::new(file(0x1008, &[ctor(1, &[1], &[])])).expect("part"))
                .is_err()
        );
        assert!(
            r.push(Part::new(file(0x2000, &[ctor(1, &[1], &[])])).expect("part"))
                .is_ok()
        );
    }

    #[test]
    fn the_shape_is_checked() {
        let b = file(0x1000, &[ctor(1, &[1, 1], &[0; 8])]);
        let mut r = Region::default();
        r.push(Part::new(b).expect("part")).expect("push");
        let at = At { part: 0, off: 96 };
        assert!(r.ctor(at, 1..=2, 2, 8, "name").is_ok());
        assert!(r.ctor(at, 0..=0, 2, 8, "name").is_err());
        assert!(r.ctor(at, 1..=2, 1, 8, "name").is_err());
        assert!(r.ctor(at, 1..=2, 2, 0, "name").is_err());
    }
}
