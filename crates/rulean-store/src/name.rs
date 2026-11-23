//! Strings and names (spec 04.3).
//!
//! A string is a byte string. The store does not check UTF-8. The parser checks it before it interns a string (spec 07.1.2).
//!
//! A name is anonymous, or a string or a number after a prefix name, as `Lean.Name`. `NameId(0)` is the anonymous name.

use crate::hash;
use crate::ids::{NameId, StrId, low, raw};
use crate::table::Probe;
use crate::{Span, Store};

/// A name node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Name {
    /// The anonymous name.
    Anon,
    /// `pre.s` for a string `s`.
    Str(NameId, StrId),
    /// `pre.n` for a number `n`.
    Num(NameId, u64),
}

/// The hash of the anonymous name. It is the value that Lean uses.
const ANON_HASH: u32 = 1723;
const STR_SEED: u32 = 0x5354_5221;
const NAME_STR_SEED: u32 = 0x4e53_5452;
const NAME_NUM_SEED: u32 = 0x4e4e_554d;

impl Store {
    pub(crate) fn init_names(&mut self) {
        self.names.push(Name::Anon);
        self.name_hash.push(ANON_HASH);
        self.name_table.put_new(ANON_HASH, 0);
    }

    /// Interns a byte string.
    pub fn intern_str(&mut self, b: &[u8]) -> StrId {
        let h = hash::bytes(STR_SEED, b);
        let mut pos = self.str_table.start(h);
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.str_table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    if hh == h && self.str_eq(low(v), b) {
                        found = low(v) + 1;
                        walking = false;
                    } else {
                        pos = self.str_table.next(pos);
                    }
                }
            }
        }
        if found != 0 {
            StrId(found - 1)
        } else if self.str_spans.len() >= u32::MAX as usize - 1 {
            self.full = true;
            StrId(0)
        } else {
            let id = self.str_spans.len() as u32;
            let start = self.str_bytes.len();
            let mut i = 0;
            while i < b.len() {
                self.str_bytes.push(b[i]);
                i += 1;
            }
            self.str_spans.push(Span {
                start,
                len: b.len(),
            });
            self.str_hash.push(h);
            self.str_table.put(pos, h, raw(id));
            StrId(id)
        }
    }

    fn str_eq(&self, v: u32, b: &[u8]) -> bool {
        let span = self.str_spans[v as usize];
        let mut eq = span.len == b.len();
        let mut i = 0;
        while eq && i < b.len() {
            eq = self.str_bytes[span.start + i] == b[i];
            i += 1;
        }
        eq
    }

    /// The bytes of a string.
    pub fn str_bytes(&self, s: StrId) -> &[u8] {
        let span = self.str_spans[s.0 as usize];
        &self.str_bytes[span.start..span.start + span.len]
    }

    /// The hash of a string.
    pub fn str_hash(&self, s: StrId) -> u32 {
        self.str_hash[s.0 as usize]
    }

    /// The number of strings.
    pub fn str_count(&self) -> usize {
        self.str_spans.len()
    }

    /// The anonymous name.
    pub fn anon(&self) -> NameId {
        NameId(0)
    }

    /// The name `pre.s`.
    pub fn name_str(&mut self, pre: NameId, s: StrId) -> NameId {
        let h = hash::mix(
            hash::mix(NAME_STR_SEED, self.name_hash(pre)),
            self.str_hash(s),
        );
        self.intern_name(Name::Str(pre, s), hash::finish(h))
    }

    /// The name `pre.s` for a byte string `s`.
    pub fn name_str_bytes(&mut self, pre: NameId, s: &[u8]) -> NameId {
        let sid = self.intern_str(s);
        self.name_str(pre, sid)
    }

    /// The name `pre.n`.
    pub fn name_num(&mut self, pre: NameId, n: u64) -> NameId {
        let h = hash::word64(hash::mix(NAME_NUM_SEED, self.name_hash(pre)), n);
        self.intern_name(Name::Num(pre, n), hash::finish(h))
    }

    fn intern_name(&mut self, node: Name, h: u32) -> NameId {
        let mut pos = self.name_table.start(h);
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.name_table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    if hh == h && self.names[v as usize] == node {
                        found = low(v) + 1;
                        walking = false;
                    } else {
                        pos = self.name_table.next(pos);
                    }
                }
            }
        }
        if found != 0 {
            NameId(found - 1)
        } else if self.names.len() >= u32::MAX as usize - 1 {
            self.full = true;
            NameId(0)
        } else {
            let id = self.names.len() as u32;
            self.names.push(node);
            self.name_hash.push(h);
            self.name_table.put(pos, h, raw(id));
            NameId(id)
        }
    }

    /// The node of a name.
    pub fn name(&self, n: NameId) -> Name {
        self.names[n.0 as usize]
    }

    /// The hash of a name.
    pub fn name_hash(&self, n: NameId) -> u32 {
        self.name_hash[n.0 as usize]
    }

    /// The number of names.
    pub fn name_count(&self) -> usize {
        self.names.len()
    }

    /// The dotted form of a name, for messages. A string part is written as it is, so the result is valid UTF-8 if the parts are.
    pub fn name_text(&self, n: NameId) -> alloc::vec::Vec<u8> {
        // Collect the parts from the last to the first, then write them in order.
        let mut parts: alloc::vec::Vec<NameId> = alloc::vec::Vec::new();
        let mut cur = n;
        let mut more = true;
        while more {
            match self.name(cur) {
                Name::Anon => more = false,
                Name::Str(pre, _) => {
                    parts.push(cur);
                    cur = pre;
                }
                Name::Num(pre, _) => {
                    parts.push(cur);
                    cur = pre;
                }
            }
        }
        let mut out = alloc::vec::Vec::new();
        if parts.len() == 0 {
            push_all(&mut out, b"[anonymous]");
        }
        let mut i = parts.len();
        while i > 0 {
            i -= 1;
            if i + 1 != parts.len() {
                out.push(b'.');
            }
            match self.name(parts[i]) {
                Name::Str(_, s) => push_all(&mut out, self.str_bytes(s)),
                Name::Num(_, k) => push_all(&mut out, &rulean_nat::Nat::from_u64(k).to_decimal()),
                Name::Anon => {}
            }
        }
        out
    }
}

fn push_all(out: &mut alloc::vec::Vec<u8>, b: &[u8]) {
    let mut i = 0;
    while i < b.len() {
        out.push(b[i]);
        i += 1;
    }
}
