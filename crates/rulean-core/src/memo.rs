//! Small hash maps for the caches of the checker.
//!
//! The maps are open tables with epochs, so `clear` is O(1) (spec 04.8). Each slot keeps the full key, and a lookup compares the full key. So a cache never trusts a hash alone (spec 08.5).

use alloc::vec::Vec;
use rulean_store::Raw;
use rulean_store::hash;

const PAIR_SEED: u32 = 0x4d45_4d4f;

fn pair_hash(a: Raw, b: Raw) -> u32 {
    hash::finish(hash::mix_raw(hash::mix_raw(PAIR_SEED, a), b))
}

/// A slot of a `Memo`. The keys and the value are in the slot, so one step of a walk reads one slot and no other array.
#[derive(Clone, Copy, Debug)]
struct MemoSlot {
    /// The epoch of the slot. The slot is live if this is the epoch of the map, dead if it is the epoch with `DEAD`, and free else.
    epoch: u32,
    a: Raw,
    b: Raw,
    v: Raw,
}

/// The bit of the epoch of a slot whose entry `truncate` removed. A walk goes past a dead slot, but a lookup never gives its value.
const DEAD: u32 = 1 << 31;

/// The first number of slots of a `Memo`.
const MEMO_FIRST: usize = 16;

/// A map from a pair of keys to a value. The keys and the value have the handle type `Raw`, so an `ExprId` fits with the `wide` feature too.
///
/// The map is an open table with linear probing. Each slot keeps the keys and the value, so a lookup reads one place in memory for each step. The array `order` keeps the slot of each entry in the order of the inserts, for `truncate` and for a rebuild of the table.
#[derive(Clone, Debug)]
pub struct Memo {
    slots: Vec<MemoSlot>,
    order: Vec<u32>,
    epoch: u32,
    /// The slots that are live or dead.
    used: usize,
    mask: usize,
}

impl Default for Memo {
    fn default() -> Memo {
        Memo::new()
    }
}

impl Memo {
    /// An empty map.
    pub fn new() -> Memo {
        Memo::with_slots(MEMO_FIRST)
    }

    /// An empty map with `n` slots. `n` must be a power of two.
    fn with_slots(n: usize) -> Memo {
        let mut slots = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            slots.push(MemoSlot {
                epoch: 0,
                a: 0,
                b: 0,
                v: 0,
            });
            i += 1;
        }
        // The slots start in epoch 0, so the live epoch is 1 and every slot is free.
        Memo {
            slots,
            order: Vec::new(),
            epoch: 1,
            used: 0,
            mask: n - 1,
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// The number of bytes of the arrays, without the allocator overhead.
    pub fn bytes(&self) -> usize {
        self.slots.len() * core::mem::size_of::<MemoSlot>() + self.order.capacity() * 4
    }

    /// True if the map has no entry.
    pub fn is_empty(&self) -> bool {
        self.order.len() == 0
    }

    /// The position of the key, or the free position where the walk for the key stopped. The second value is true if the key is at the position.
    fn find(&self, a: Raw, b: Raw) -> (usize, bool) {
        let mut pos = (pair_hash(a, b) as usize) & self.mask;
        let mut found = false;
        let mut walking = true;
        while walking {
            let s = self.slots[pos];
            if s.epoch == self.epoch && s.a == a && s.b == b {
                found = true;
                walking = false;
            } else if s.epoch == self.epoch || s.epoch == (self.epoch | DEAD) {
                pos = (pos + 1) & self.mask;
            } else {
                walking = false;
            }
        }
        (pos, found)
    }

    /// The value of the key, if any.
    pub fn get(&self, a: Raw, b: Raw) -> Option<Raw> {
        let (pos, found) = self.find(a, b);
        if found { Some(self.slots[pos].v) } else { None }
    }

    /// True if the map has the key.
    pub fn contains(&self, a: Raw, b: Raw) -> bool {
        let (_, found) = self.find(a, b);
        found
    }

    /// Puts a new entry in the free slot at `pos`. The table can grow, so the position is not valid after the call.
    fn insert_at(&mut self, pos: usize, a: Raw, b: Raw, v: Raw) {
        self.slots[pos] = MemoSlot {
            epoch: self.epoch,
            a,
            b,
            v,
        };
        self.order.push(pos as u32);
        self.used += 1;
        // The load stays below 1/2, so a walk is short and always reaches a free slot.
        if self.used * 2 > self.slots.len() {
            self.rebuild(self.slots.len() * 2);
        }
    }

    /// Sets the value of the key.
    pub fn put(&mut self, a: Raw, b: Raw, v: Raw) {
        let (pos, found) = self.find(a, b);
        if found {
            self.slots[pos].v = v;
        } else {
            self.insert_at(pos, a, b, v);
        }
    }

    /// The value of the key if the map has the key. If not, this sets the value of the key to `v` and gives `None`. It walks the table one time, but `get` and then `put` walk it two times.
    pub fn get_or_put(&mut self, a: Raw, b: Raw, v: Raw) -> Option<Raw> {
        let (pos, found) = self.find(a, b);
        if found {
            Some(self.slots[pos].v)
        } else {
            self.insert_at(pos, a, b, v);
            None
        }
    }

    /// Makes the table again with `n` slots and puts the entries in it in the order of `order`. Dead slots are not copied.
    fn rebuild(&mut self, n: usize) {
        let old = core::mem::replace(self, Memo::with_slots(n));
        let mut i = 0;
        while i < old.order.len() {
            let s = old.slots[old.order[i] as usize];
            let (pos, _) = self.find(s.a, s.b);
            self.slots[pos] = MemoSlot {
                epoch: self.epoch,
                a: s.a,
                b: s.b,
                v: s.v,
            };
            self.order.push(pos as u32);
            self.used += 1;
            i += 1;
        }
    }

    /// Removes every entry. This is O(1) unless the epoch counter is at its end.
    pub fn clear(&mut self) {
        if self.epoch + 1 < DEAD {
            self.epoch += 1;
        } else {
            let mut i = 0;
            while i < self.slots.len() {
                self.slots[i].epoch = 0;
                i += 1;
            }
            self.epoch = 1;
        }
        self.order.truncate(0);
        self.used = 0;
    }

    /// Keeps the first `n` entries and removes the others. The slot of a removed entry becomes dead, so the walks for the other keys still go past it.
    ///
    /// When more than half of the used slots are dead, the table is made again from the entries. Each dead slot comes from one insert, so the cost is O(1) for each insert on average.
    pub fn truncate(&mut self, n: usize) {
        let mut k = n;
        while k < self.order.len() {
            let pos = self.order[k] as usize;
            self.slots[pos].epoch = self.epoch | DEAD;
            k += 1;
        }
        self.order.truncate(n);
        if self.used > 2 * self.order.len() + 1024 {
            self.rebuild(self.slots.len());
        }
    }
}

/// A slot of an `Intern` table. The key and the value are in the slot, so a lookup reads one slot and no other array.
#[derive(Clone, Copy, Debug)]
struct InternSlot {
    epoch: u32,
    a: Raw,
    b: Raw,
    v: Raw,
}

/// The first number of slots of an `Intern` table.
const INTERN_FIRST: usize = 1 << 10;

/// A map from a pair of keys to a value that has no `truncate`. It keeps the keys and the value in the slots of an open table, so a lookup reads one slot for each step of the walk. A `Memo` reads a table slot and then an entry, so it reads two places. The table uses epochs, so `clear` is O(1).
#[derive(Clone, Debug)]
pub struct Intern {
    slots: Vec<InternSlot>,
    epoch: u32,
    count: usize,
    mask: usize,
}

impl Default for Intern {
    fn default() -> Intern {
        Intern::new()
    }
}

impl Intern {
    /// An empty map.
    pub fn new() -> Intern {
        Intern::with_slots(INTERN_FIRST)
    }

    /// An empty map with `n` slots. `n` must be a power of two.
    fn with_slots(n: usize) -> Intern {
        let mut slots = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            slots.push(InternSlot {
                epoch: 0,
                a: 0,
                b: 0,
                v: 0,
            });
            i += 1;
        }
        // The slots start in epoch 0, so the live epoch is 1 and every slot is free.
        Intern {
            slots,
            epoch: 1,
            count: 0,
            mask: n - 1,
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.count
    }

    /// True if the map has no entry.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// The number of bytes of the slots.
    pub fn bytes(&self) -> usize {
        self.slots.len() * core::mem::size_of::<InternSlot>()
    }

    /// The position of the key, or the free position where the walk for the key stopped. The second value is true if the key is at the position.
    fn find(&self, a: Raw, b: Raw) -> (usize, bool) {
        let mut pos = (pair_hash(a, b) as usize) & self.mask;
        let mut found = false;
        let mut walking = true;
        while walking {
            let s = self.slots[pos];
            if s.epoch != self.epoch {
                walking = false;
            } else if s.a == a && s.b == b {
                found = true;
                walking = false;
            } else {
                pos = (pos + 1) & self.mask;
            }
        }
        (pos, found)
    }

    /// The value of the key if the map has the key. If not, this sets the value of the key to `v` and gives `None`.
    pub fn get_or_put(&mut self, a: Raw, b: Raw, v: Raw) -> Option<Raw> {
        let (pos, found) = self.find(a, b);
        if found {
            Some(self.slots[pos].v)
        } else {
            self.slots[pos] = InternSlot {
                epoch: self.epoch,
                a,
                b,
                v,
            };
            self.count += 1;
            // The load stays below 1/2, so a walk is short and always reaches a free slot.
            if self.count * 2 > self.slots.len() {
                self.grow();
            }
            None
        }
    }

    /// Doubles the number of slots and puts each entry again.
    fn grow(&mut self) {
        let old = core::mem::replace(self, Intern::with_slots(self.slots.len() * 2));
        let mut i = 0;
        while i < old.slots.len() {
            let s = old.slots[i];
            if s.epoch == old.epoch {
                let (pos, _) = self.find(s.a, s.b);
                self.slots[pos] = InternSlot {
                    epoch: self.epoch,
                    a: s.a,
                    b: s.b,
                    v: s.v,
                };
                self.count += 1;
            }
            i += 1;
        }
    }

    /// Removes every entry. This is O(1) unless the epoch counter is at its end.
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
        self.count = 0;
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
    #[inline(always)]
    pub fn put(&mut self, a: Raw, b: Raw, v: Raw) {
        if self.slots.is_empty() {
            self.alloc();
        }
        let epoch = self.epoch;
        self.slots[Lossy::pos(a, b)] = LossySlot { epoch, a, b, v };
    }

    /// Allocates the slots. It is out of line, so the code of `put` stays small and the compiler can inline it.
    #[cold]
    #[inline(never)]
    fn alloc(&mut self) {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memo_keeps_keys_after_truncate_grow_and_clear() {
        let mut m = Memo::new();
        let n: Raw = 5000;
        let mut i: Raw = 0;
        while i < n {
            assert_eq!(m.get_or_put(i, i + 1, i * 3), None);
            i += 1;
        }
        m.truncate(2000);
        assert_eq!(m.len(), 2000);
        i = 0;
        while i < n {
            let want = if i < 2000 { Some(i * 3) } else { None };
            assert_eq!(m.get(i, i + 1), want);
            i += 1;
        }
        i = 2000;
        while i < n {
            m.put(i, i + 1, i);
            i += 1;
        }
        m.truncate(10);
        m.put(3, 4, 7);
        assert_eq!(m.get(3, 4), Some(7));
        assert_eq!(m.get(9, 10), Some(27));
        assert_eq!(m.get(10, 11), None);
        m.clear();
        assert!(m.is_empty());
        assert_eq!(m.get(3, 4), None);
    }

    #[test]
    fn intern_keeps_keys_after_grow_and_clear() {
        let mut m = Intern::new();
        let n: Raw = 5000;
        let mut i: Raw = 0;
        while i < n {
            assert_eq!(m.get_or_put(i, i + 1, i + 16), None);
            i += 1;
        }
        assert_eq!(m.len(), n as usize);
        i = 0;
        while i < n {
            assert_eq!(m.get_or_put(i, i + 1, 0), Some(i + 16));
            i += 1;
        }
        assert_eq!(m.get_or_put(1, 1, 7), None);
        m.clear();
        assert!(m.is_empty());
        assert_eq!(m.get_or_put(3, 4, 9), None);
        assert_eq!(m.get_or_put(3, 4, 0), Some(9));
    }
}
