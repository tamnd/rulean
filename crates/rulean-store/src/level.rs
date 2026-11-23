//! Universe levels and level lists (spec 04.3).
//!
//! The store interns levels as they are. It does not normalize them. The checker has its own level functions (spec 05).

use alloc::vec::Vec;

use crate::hash;
use crate::ids::{LevelId, LevelListId, NameId, low, raw};
use crate::table::Probe;
use crate::{Span, Store};

/// A level node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Zero,
    Succ(LevelId),
    Max(LevelId, LevelId),
    IMax(LevelId, LevelId),
    Param(NameId),
}

const ZERO_SEED: u32 = 2221;
const SUCC_SEED: u32 = 0x4c53_5543;
const MAX_SEED: u32 = 0x4c4d_4158;
const IMAX_SEED: u32 = 0x4c49_4d58;
const PARAM_SEED: u32 = 0x4c50_4152;
const LIST_SEED: u32 = 0x4c4c_5354;

impl Store {
    pub(crate) fn init_levels(&mut self) {
        self.levels.push(Level::Zero);
        self.level_hash.push(ZERO_SEED);
        self.level_param.push(false);
        self.level_table.put_new(ZERO_SEED, 0);
        self.list_spans.push(Span { start: 0, len: 0 });
        self.list_hash.push(LIST_SEED);
        self.list_param.push(false);
        self.list_table.put_new(LIST_SEED, 0);
    }

    /// The level zero.
    pub fn level_zero(&self) -> LevelId {
        LevelId(0)
    }

    /// `succ l`.
    pub fn level_succ(&mut self, l: LevelId) -> LevelId {
        let h = hash::mix(SUCC_SEED, self.level_hash(l));
        let p = self.level_has_param(l);
        self.intern_level(Level::Succ(l), hash::finish(h), p)
    }

    /// `max a b`.
    pub fn level_max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        let h = hash::mix(hash::mix(MAX_SEED, self.level_hash(a)), self.level_hash(b));
        let p = self.level_has_param(a) || self.level_has_param(b);
        self.intern_level(Level::Max(a, b), hash::finish(h), p)
    }

    /// `imax a b`.
    pub fn level_imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        let h = hash::mix(hash::mix(IMAX_SEED, self.level_hash(a)), self.level_hash(b));
        let p = self.level_has_param(a) || self.level_has_param(b);
        self.intern_level(Level::IMax(a, b), hash::finish(h), p)
    }

    /// The level parameter `n`.
    pub fn level_param(&mut self, n: NameId) -> LevelId {
        let h = hash::mix(PARAM_SEED, self.name_hash(n));
        self.intern_level(Level::Param(n), hash::finish(h), true)
    }

    fn intern_level(&mut self, node: Level, h: u32, has_param: bool) -> LevelId {
        let mut pos = self.level_table.start(h);
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.level_table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    if hh == h && self.levels[v as usize] == node {
                        found = low(v) + 1;
                        walking = false;
                    } else {
                        pos = self.level_table.next(pos);
                    }
                }
            }
        }
        if found != 0 {
            LevelId(found - 1)
        } else if self.levels.len() >= u32::MAX as usize - 1 {
            self.full = true;
            LevelId(0)
        } else {
            let id = self.levels.len() as u32;
            self.levels.push(node);
            self.level_hash.push(h);
            self.level_param.push(has_param);
            self.level_table.put(pos, h, raw(id));
            LevelId(id)
        }
    }

    /// The node of a level.
    pub fn level(&self, l: LevelId) -> Level {
        self.levels[l.0 as usize]
    }

    /// The hash of a level.
    pub fn level_hash(&self, l: LevelId) -> u32 {
        self.level_hash[l.0 as usize]
    }

    /// True if the level has a parameter.
    pub fn level_has_param(&self, l: LevelId) -> bool {
        self.level_param[l.0 as usize]
    }

    /// The number of levels.
    pub fn level_count(&self) -> usize {
        self.levels.len()
    }

    /// The empty level list.
    pub fn level_list_empty(&self) -> LevelListId {
        LevelListId(0)
    }

    /// Interns a list of levels.
    pub fn level_list(&mut self, items: &[LevelId]) -> LevelListId {
        let mut h = LIST_SEED;
        let mut p = false;
        let mut i = 0;
        while i < items.len() {
            h = hash::mix(h, self.level_hash(items[i]));
            p = p || self.level_has_param(items[i]);
            i += 1;
        }
        let h = if items.len() == 0 {
            LIST_SEED
        } else {
            hash::finish(h ^ items.len() as u32)
        };
        let mut pos = self.list_table.start(h);
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.list_table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    if hh == h && self.list_eq(low(v), items) {
                        found = low(v) + 1;
                        walking = false;
                    } else {
                        pos = self.list_table.next(pos);
                    }
                }
            }
        }
        if found != 0 {
            LevelListId(found - 1)
        } else if self.list_spans.len() >= u32::MAX as usize - 1 {
            self.full = true;
            LevelListId(0)
        } else {
            let id = self.list_spans.len() as u32;
            let start = self.list_items.len();
            let mut j = 0;
            while j < items.len() {
                self.list_items.push(items[j]);
                j += 1;
            }
            self.list_spans.push(Span {
                start,
                len: items.len(),
            });
            self.list_hash.push(h);
            self.list_param.push(p);
            self.list_table.put(pos, h, raw(id));
            LevelListId(id)
        }
    }

    fn list_eq(&self, v: u32, items: &[LevelId]) -> bool {
        let span = self.list_spans[v as usize];
        let mut eq = span.len == items.len();
        let mut i = 0;
        while eq && i < items.len() {
            eq = self.list_items[span.start + i] == items[i];
            i += 1;
        }
        eq
    }

    /// The items of a level list.
    pub fn level_list_items(&self, l: LevelListId) -> &[LevelId] {
        let span = self.list_spans[l.0 as usize];
        &self.list_items[span.start..span.start + span.len]
    }

    /// A copy of the items of a level list.
    pub fn level_list_vec(&self, l: LevelListId) -> Vec<LevelId> {
        let span = self.list_spans[l.0 as usize];
        let mut v = Vec::with_capacity(span.len);
        let mut i = 0;
        while i < span.len {
            v.push(self.list_items[span.start + i]);
            i += 1;
        }
        v
    }

    /// The hash of a level list.
    pub fn level_list_hash(&self, l: LevelListId) -> u32 {
        self.list_hash[l.0 as usize]
    }

    /// True if a level of the list has a parameter.
    pub fn level_list_has_param(&self, l: LevelListId) -> bool {
        self.list_param[l.0 as usize]
    }
}
