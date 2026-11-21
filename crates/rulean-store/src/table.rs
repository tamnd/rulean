//! The open-addressing table of spec 04.2.4 and 10.6.
//!
//! A table maps a 32-bit hash to one or more `u32` values. It does not know the keys. The caller walks the probe sequence with `start`, `get` and `next`, compares its own key at each value with the same hash, and calls `put` at the free position where the walk stopped. So the table has no closure and no trait, and a lookup never trusts a hash alone (spec 04.2.3).
//!
//! A table can carry an epoch for each slot. Then `clear` is O(1): it moves to the next epoch, and every slot of an older epoch counts as free (spec 04.8). The frozen tier has no epochs.
//!
//! A typical lookup:
//!
//! ```
//! # use rulean_store::table::{Table, Probe};
//! # let mut t = Table::new(false);
//! # let keys: Vec<u64> = vec![7];
//! # let key = 7u64;
//! # let hash = 7u32;
//! # t.put_new(hash, 0);
//! let mut pos = t.start(hash);
//! let mut found = None;
//! let mut walking = true;
//! while walking {
//!     match t.get(pos) {
//!         Probe::Free => walking = false,
//!         Probe::Full(h, v) => {
//!             if h == hash && keys[v as usize] == key {
//!                 found = Some(v);
//!                 walking = false;
//!             } else {
//!                 pos = t.next(pos);
//!             }
//!         }
//!     }
//! }
//! assert_eq!(found, Some(0));
//! ```

use alloc::vec::Vec;

/// The state of one slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Probe {
    /// The slot is free. A walk stops here.
    Free,
    /// The slot holds a value with this hash.
    Full(u32, u32),
}

/// An open-addressing table from 32-bit hashes to `u32` values, with linear probing.
#[derive(Clone, Debug)]
pub struct Table {
    hashes: Vec<u32>,
    values: Vec<u32>,
    /// The epoch of each slot, or no slots if the table has no epochs.
    epochs: Vec<u32>,
    use_epochs: bool,
    epoch: u32,
    count: usize,
    mask: usize,
}

/// The first capacity of a table. It is a power of two.
const FIRST_CAPACITY: usize = 16;

/// A value that marks a free slot in a table without epochs.
const FREE: u32 = u32::MAX;

impl Table {
    /// A new empty table. With `use_epochs`, `clear` is O(1).
    pub fn new(use_epochs: bool) -> Table {
        Table::with_capacity(FIRST_CAPACITY, use_epochs)
    }

    /// A new empty table with room for at least `n` slots. The capacity is a power of two.
    pub fn with_capacity(n: usize, use_epochs: bool) -> Table {
        let mut cap = FIRST_CAPACITY;
        while cap < n {
            cap *= 2;
        }
        let mut hashes = Vec::with_capacity(cap);
        let mut values = Vec::with_capacity(cap);
        let mut epochs = Vec::with_capacity(if use_epochs { cap } else { 0 });
        let mut i = 0;
        while i < cap {
            hashes.push(0);
            values.push(FREE);
            if use_epochs {
                epochs.push(0);
            }
            i += 1;
        }
        Table {
            hashes,
            values,
            epochs,
            use_epochs,
            // The slots start in epoch 0, so the live epoch is 1 and every slot is free.
            epoch: 1,
            count: 0,
            mask: cap - 1,
        }
    }

    /// The number of values in the table.
    pub fn len(&self) -> usize {
        self.count
    }

    /// True if the table has no value.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// The number of slots.
    pub fn capacity(&self) -> usize {
        self.mask + 1
    }

    /// The number of bytes of the slots.
    pub fn bytes(&self) -> usize {
        let per_slot = if self.use_epochs { 12 } else { 8 };
        self.capacity() * per_slot
    }

    /// The first position of the probe sequence for `hash`.
    pub fn start(&self, hash: u32) -> usize {
        (hash as usize) & self.mask
    }

    /// The position after `pos` in the probe sequence.
    pub fn next(&self, pos: usize) -> usize {
        (pos + 1) & self.mask
    }

    /// The state of the slot at `pos`.
    pub fn get(&self, pos: usize) -> Probe {
        let live = if self.use_epochs {
            self.epochs[pos] == self.epoch
        } else {
            self.values[pos] != FREE
        };
        if live {
            Probe::Full(self.hashes[pos], self.values[pos])
        } else {
            Probe::Free
        }
    }

    /// Puts `value` with `hash` in the free slot at `pos`, which is the slot where a walk for `hash` stopped. The table can grow, so the position is not valid after the call.
    pub fn put(&mut self, pos: usize, hash: u32, value: u32) {
        self.hashes[pos] = hash;
        self.values[pos] = value;
        if self.use_epochs {
            self.epochs[pos] = self.epoch;
        }
        self.count += 1;
        // The load stays below 1/2, so a walk is short and always reaches a free slot.
        if self.count * 2 > self.capacity() {
            self.grow();
        }
    }

    /// Puts `value` with `hash` in the table without a lookup. The caller knows that no equal key is in the table.
    pub fn put_new(&mut self, hash: u32, value: u32) {
        let mut pos = self.start(hash);
        while self.get(pos) != Probe::Free {
            pos = self.next(pos);
        }
        self.put(pos, hash, value);
    }

    /// Makes the table empty. With epochs this is O(1). Without epochs it writes each slot.
    pub fn clear(&mut self) {
        if self.use_epochs && self.epoch < u32::MAX {
            self.epoch += 1;
        } else {
            let mut i = 0;
            while i < self.capacity() {
                self.values[i] = FREE;
                if self.use_epochs {
                    self.epochs[i] = 0;
                }
                i += 1;
            }
            self.epoch = 1;
        }
        self.count = 0;
    }

    /// Doubles the capacity and puts each value again.
    fn grow(&mut self) {
        let old = core::mem::replace(
            self,
            Table::with_capacity(self.capacity() * 2, self.use_epochs),
        );
        let mut i = 0;
        while i < old.capacity() {
            if let Probe::Full(h, v) = old.get(i) {
                self.put_new(h, v);
            }
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn find(t: &Table, keys: &[u64], key: u64, hash: u32) -> (Option<u32>, usize) {
        let mut pos = t.start(hash);
        loop {
            match t.get(pos) {
                Probe::Free => return (None, pos),
                Probe::Full(h, v) if h == hash && keys[v as usize] == key => return (Some(v), pos),
                Probe::Full(..) => pos = t.next(pos),
            }
        }
    }

    #[test]
    fn insert_find_and_grow() {
        for epochs in [false, true] {
            let mut t = Table::new(epochs);
            let mut keys = Vec::new();
            // A bad hash: many keys share a hash, so the walk must compare the keys.
            for k in 0..1000u64 {
                let hash = (k % 7) as u32;
                let (found, pos) = find(&t, &keys, k, hash);
                assert_eq!(found, None);
                keys.push(k);
                t.put(pos, hash, (keys.len() - 1) as u32);
            }
            assert_eq!(t.len(), 1000);
            assert!(t.capacity() >= 2000);
            for k in 0..1000u64 {
                assert_eq!(find(&t, &keys, k, (k % 7) as u32).0, Some(k as u32));
            }
            t.clear();
            assert!(t.is_empty());
            assert_eq!(find(&t, &keys, 3, 3).0, None);
            t.put_new(3, 3);
            assert_eq!(find(&t, &keys, 3, 3).0, Some(3));
        }
    }
}
