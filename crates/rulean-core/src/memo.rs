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

/// A map from a pair of keys to a value. The keys and the value have the handle type `Raw`, so an `ExprId` fits with the `wide` feature too.
#[derive(Clone, Debug)]
pub struct Memo {
    ka: Vec<Raw>,
    kb: Vec<Raw>,
    vals: Vec<Raw>,
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
            ka: Vec::new(),
            kb: Vec::new(),
            vals: Vec::new(),
            table: Table::new(true),
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.vals.len()
    }

    /// True if the map has no entry.
    pub fn is_empty(&self) -> bool {
        self.vals.len() == 0
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
                    if hh == h && self.ka[i] == a && self.kb[i] == b {
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
            Some(self.vals[found - 1])
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
            self.vals[k] = v;
        } else {
            let i = self.vals.len() as Raw;
            self.ka.push(a);
            self.kb.push(b);
            self.vals.push(v);
            self.table.put(pos, h, i);
        }
    }

    /// Removes every entry. This is O(1) for the table.
    pub fn clear(&mut self) {
        self.ka.truncate(0);
        self.kb.truncate(0);
        self.vals.truncate(0);
        self.table.clear();
    }
}
