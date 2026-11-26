//! Small hash maps for the caches of the checker.
//!
//! The maps use the verified `rulean_store::table::Table` with epochs, so `clear` is O(1) (spec 04.8). The keys are kept in arrays next to the table, and a lookup compares the full key after the hash matches. So a cache never trusts a hash alone (spec 08.5).

use alloc::vec::Vec;
use rulean_store::Raw;
use rulean_store::hash;
use rulean_store::table::{Probe, Table};

const PAIR_SEED: u32 = 0x4d45_4d4f;

fn pair_hash(a: Raw, b: Raw) -> u32 {
    hash::finish(hash::mix_raw(hash::mix_raw(PAIR_SEED, a), b))
}

/// An entry of a `Memo`. The keys and the value are in one record, so a lookup reads one cache line for the entry.
#[derive(Clone, Copy, Debug)]
struct Entry {
    a: Raw,
    b: Raw,
    v: Raw,
}

/// A map from a pair of keys to a value. The keys and the value have the handle type `Raw`, so an `ExprId` fits with the `wide` feature too.
#[derive(Clone, Debug)]
pub struct Memo {
    entries: Vec<Entry>,
    table: Table,
}

impl Default for Memo {
    fn default() -> Memo {
        Memo::new()
    }
}

impl Memo {
    /// An empty map.
    pub fn new() -> Memo {
        Memo {
            entries: Vec::new(),
            table: Table::new(true),
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// The number of bytes of the arrays and the table, without the allocator overhead.
    pub fn bytes(&self) -> usize {
        self.entries.capacity() * core::mem::size_of::<Entry>() + self.table.bytes()
    }

    /// True if the map has no entry.
    pub fn is_empty(&self) -> bool {
        self.entries.len() == 0
    }

    /// The position of the key in the entry arrays plus 1, or 0. The second value is the table position where a walk for the key stopped.
    fn find(&self, a: Raw, b: Raw, h: u32) -> (usize, usize) {
        let mut pos = self.table.start(h);
        let mut found: usize = 0;
        let mut walking = true;
        while walking {
            match self.table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    let i = v as usize;
                    if hh == h
                        && i < self.entries.len()
                        && self.entries[i].a == a
                        && self.entries[i].b == b
                    {
                        found = i + 1;
                        walking = false;
                    } else {
                        pos = self.table.next(pos);
                    }
                }
            }
        }
        (found, pos)
    }

    /// The value of the key, if any.
    pub fn get(&self, a: Raw, b: Raw) -> Option<Raw> {
        let (found, _) = self.find(a, b, pair_hash(a, b));
        if found == 0 {
            None
        } else {
            Some(self.entries[found - 1].v)
        }
    }

    /// True if the map has the key.
    pub fn contains(&self, a: Raw, b: Raw) -> bool {
        let (found, _) = self.find(a, b, pair_hash(a, b));
        found != 0
    }

    /// Sets the value of the key.
    pub fn put(&mut self, a: Raw, b: Raw, v: Raw) {
        let h = pair_hash(a, b);
        let (found, pos) = self.find(a, b, h);
        if found != 0 {
            let k = found - 1;
            self.entries[k].v = v;
        } else {
            let i = self.entries.len() as Raw;
            self.entries.push(Entry { a, b, v });
            self.table.put(pos, h, i);
        }
    }

    /// Removes every entry. This is O(1) for the table.
    pub fn clear(&mut self) {
        self.entries.truncate(0);
        self.table.clear();
    }

    /// Keeps the first `n` entries and removes the others. The table keeps its slots for the removed entries, and `find` skips a slot whose entry index is past the end. A later entry can take the index of a removed entry, but a lookup compares the full key, so a hit is always correct.
    ///
    /// When the table has more than twice as many slots in use as there are entries, the table is made again from the entries. Each slot of a removed entry comes from one `put`, so the cost is O(1) for each `put` on average.
    pub fn truncate(&mut self, n: usize) {
        self.entries.truncate(n);
        if self.table.len() > 2 * self.entries.len() + 1024 {
            self.table.clear();
            let k = self.entries.len();
            let mut j = 0;
            while j < k {
                let e = self.entries[j];
                self.table.put_new(pair_hash(e.a, e.b), j as Raw);
                j += 1;
            }
        }
    }
}

/// The number of index bits of a `Lossy` cache. The cache has 2^13 slots, so it uses 2^13 times the size of a slot (128 KiB with 32-bit ids).
const LOSSY_BITS: u32 = 13;

#[derive(Clone, Copy, Debug)]
struct LossySlot {
    epoch: u32,
    a: Raw,
    b: Raw,
    v: Raw,
}

/// A cache with one slot for each hash value. A new entry replaces the entry in its slot, so `get` can miss a pair that `put` added before.
///
/// The slot keeps the full key, so a hit is always correct (spec 08.5). Use this cache only where a miss gives the same result with more work, as in the memo of `instantiate`. The cache has a fixed size, so its slots stay in the processor cache, and `clear` is O(1) with an epoch.
#[derive(Clone, Debug)]
pub struct Lossy {
    slots: Vec<LossySlot>,
    epoch: u32,
}

impl Default for Lossy {
    fn default() -> Lossy {
        Lossy::new()
    }
}

impl Lossy {
    /// A new empty cache. It allocates its slots at the first `put`, so an unused cache costs no memory.
    pub fn new() -> Lossy {
        Lossy {
            slots: Vec::new(),
            epoch: 1,
        }
    }

    #[inline(always)]
    fn pos(a: Raw, b: Raw) -> usize {
        (pair_hash(a, b) as usize) & ((1usize << LOSSY_BITS) - 1)
    }

    /// The value of the pair `(a, b)`, if its slot keeps it.
    #[inline]
    pub fn get(&self, a: Raw, b: Raw) -> Option<Raw> {
        match self.slots.get(Lossy::pos(a, b)) {
            Some(s) if s.epoch == self.epoch && s.a == a && s.b == b => Some(s.v),
            _ => None,
        }
    }

    /// True if the slot of the pair `(a, b)` keeps it.
    #[inline]
    pub fn contains(&self, a: Raw, b: Raw) -> bool {
        self.get(a, b).is_some()
    }

    /// Puts the value `v` for the pair `(a, b)` in its slot.
    #[inline]
    pub fn put(&mut self, a: Raw, b: Raw, v: Raw) {
        if self.slots.is_empty() {
            let n = 1usize << LOSSY_BITS;
            self.slots = Vec::with_capacity(n);
            while self.slots.len() < n {
                self.slots.push(LossySlot {
                    epoch: 0,
                    a: 0,
                    b: 0,
                    v: 0,
                });
            }
        }
        let epoch = self.epoch;
        self.slots[Lossy::pos(a, b)] = LossySlot { epoch, a, b, v };
    }

    /// The bytes of the slots.
    pub fn bytes(&self) -> usize {
        self.slots.capacity() * core::mem::size_of::<LossySlot>()
    }

    /// Makes the cache empty. This is O(1), except once in 2^32 calls, when it writes each slot.
    pub fn clear(&mut self) {
        if self.epoch < u32::MAX {
            self.epoch += 1;
        } else {
            let mut i = 0;
            while i < self.slots.len() {
                self.slots[i].epoch = 0;
                i += 1;
            }
            self.epoch = 1;
        }
    }
}
