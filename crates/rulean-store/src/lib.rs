//! The term store: handles, per-kind node arrays, interning tables and tiers. See spec section 04.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).
//!
//! The store interns every object: strings, names, levels, level lists, natural number literals and expressions. Two structurally equal objects get the same handle, so the equality of handles is the equality of objects. Each expression node has a side record with its hash, its loose bound variable range and its flags. The store computes them when it makes the node. It never reads them from an input (spec 04.1).
//!
//! **Capacity.** An array of one kind holds at most 2^27 nodes (spec 04.2.1). When an array is full, the store sets a flag and returns a handle to an old node. The result is then wrong, so the driver must check `Store::is_full` and decline before it reports any verdict.

#![no_std]
#![forbid(unsafe_code)]
// The `vec!` macro is outside the modelled `Vec` functions of spec 10.6, so the code uses `with_capacity` and `push`.
#![allow(clippy::vec_init_then_push)]
// `is_empty` is outside the modelled `Vec` functions too.
#![allow(clippy::len_zero)]
// `Vec::clear` is outside the modelled functions too.
#![allow(clippy::manual_clear)]

extern crate alloc;

pub mod expr;
pub mod hash;
pub mod ids;
pub mod level;
pub mod name;
pub mod table;

pub use expr::{Binder, Expr, Flags, LetNode, Literal, ProjNode, SATURATED};
pub use ids::{BinderInfo, ExprId, Kind, LevelId, LevelListId, NameId, NatId, Raw, StrId, Tier};
pub use level::Level;
pub use name::Name;

use alloc::vec::Vec;
use rulean_nat::Nat;
use table::Table;

/// A part of a flat array: the items `start..start + len`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub len: usize,
}

/// The side record of an expression node (spec 04.2.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Side {
    /// The structural hash of the node.
    pub hash: u32,
    /// The loose bound variable range in bits 0..23 and the flags in bits 24..31.
    pub info: u32,
}

/// The store of one run.
#[derive(Clone, Debug)]
pub struct Store {
    // Strings: the bytes of all strings in one array.
    pub(crate) str_bytes: Vec<u8>,
    pub(crate) str_spans: Vec<Span>,
    pub(crate) str_hash: Vec<u32>,
    pub(crate) str_table: Table,
    // Names.
    pub(crate) names: Vec<Name>,
    pub(crate) name_hash: Vec<u32>,
    pub(crate) name_table: Table,
    // Levels.
    pub(crate) levels: Vec<Level>,
    pub(crate) level_hash: Vec<u32>,
    pub(crate) level_param: Vec<bool>,
    pub(crate) level_table: Table,
    // Level lists: the items of all lists in one array.
    pub(crate) list_items: Vec<LevelId>,
    pub(crate) list_spans: Vec<Span>,
    pub(crate) list_hash: Vec<u32>,
    pub(crate) list_param: Vec<bool>,
    pub(crate) list_table: Table,
    // Natural number literals.
    pub(crate) nats: Vec<Nat>,
    pub(crate) nat_hash: Vec<u32>,
    pub(crate) nat_table: Table,
    // Expressions of the frozen tier.
    pub(crate) exprs: expr::Nodes,
    // Expressions of the scratch tier, and true if new nodes go there (spec 04.8).
    pub(crate) scratch: expr::Nodes,
    pub(crate) use_scratch: bool,
    pub(crate) full: bool,
}

impl Default for Store {
    fn default() -> Store {
        Store::new()
    }
}

impl Store {
    /// A new store. It holds the anonymous name, the level zero and the empty level list.
    pub fn new() -> Store {
        let mut s = Store {
            str_bytes: Vec::new(),
            str_spans: Vec::new(),
            str_hash: Vec::new(),
            str_table: Table::new(false),
            names: Vec::new(),
            name_hash: Vec::new(),
            name_table: Table::new(false),
            levels: Vec::new(),
            level_hash: Vec::new(),
            level_param: Vec::new(),
            level_table: Table::new(false),
            list_items: Vec::new(),
            list_spans: Vec::new(),
            list_hash: Vec::new(),
            list_param: Vec::new(),
            list_table: Table::new(false),
            nats: Vec::new(),
            nat_hash: Vec::new(),
            nat_table: Table::new(false),
            exprs: expr::Nodes::new(false),
            scratch: expr::Nodes::new(true),
            use_scratch: false,
            full: false,
        };
        s.init_names();
        s.init_levels();
        s
    }

    /// True if an array of the store was full. Then some handles are wrong, and the driver must decline (see the crate documentation).
    pub fn is_full(&self) -> bool {
        self.full
    }

    /// The number of bytes that the arrays and tables of the store use, without the allocator overhead. This is the measure of spec 04.9.
    pub fn memory(&self) -> Memory {
        let tables = self.str_table.bytes()
            + self.name_table.bytes()
            + self.level_table.bytes()
            + self.list_table.bytes()
            + self.nat_table.bytes()
            + self.exprs.table.bytes()
            + self.scratch.table.bytes();
        let mut nat_bytes = self.nats.capacity() * core::mem::size_of::<Nat>();
        let mut i = 0;
        while i < self.nats.len() {
            if let Nat::Large(v) = &self.nats[i] {
                nat_bytes += v.capacity() * 8;
            }
            i += 1;
        }
        Memory {
            exprs: self.exprs.bytes() + self.scratch.bytes(),
            names: self.names.capacity() * core::mem::size_of::<Name>()
                + self.name_hash.capacity() * 4,
            strings: self.str_bytes.capacity()
                + self.str_spans.capacity() * core::mem::size_of::<Span>()
                + self.str_hash.capacity() * 4,
            levels: self.levels.capacity() * core::mem::size_of::<Level>()
                + self.level_hash.capacity() * 5
                + self.list_items.capacity() * 4
                + self.list_spans.capacity() * core::mem::size_of::<Span>()
                + self.list_hash.capacity() * 5,
            nats: nat_bytes + self.nat_hash.capacity() * 4,
            tables,
        }
    }
}

/// The memory of a store, in bytes, by part.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Memory {
    /// Expression node arrays and side records.
    pub exprs: usize,
    pub names: usize,
    pub strings: usize,
    /// Levels and level lists.
    pub levels: usize,
    pub nats: usize,
    /// The slots of all interning tables.
    pub tables: usize,
}

impl Memory {
    /// The sum of all parts.
    pub fn total(&self) -> usize {
        self.exprs + self.names + self.strings + self.levels + self.nats + self.tables
    }
}
