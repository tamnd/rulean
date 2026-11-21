//! The input formats of the verified core: the lean4export NDJSON scanner and the `.rlb` decoder. See spec section 07.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).
//!
//! The NDJSON parser writes the names, levels and expressions of the input into a `rulean_store::Store` and returns the declarations as a stream of `Decl` values (spec 04.7).
//!
//! ```
//! let input = b"{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n\
//! {\"in\":1,\"str\":{\"pre\":0,\"str\":\"T\"}}\n\
//! {\"ie\":0,\"sort\":0}\n\
//! {\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n";
//! let mut store = rulean_store::Store::new();
//! let decls = rulean_format::parse(&mut store, input).expect("a valid export");
//! assert_eq!(decls.len(), 1);
//! assert_eq!(store.name_text(decls[0].name()), b"T");
//! ```

#![no_std]
#![forbid(unsafe_code)]
// The `vec!` macro and `is_empty` are outside the modelled `Vec` functions of spec 10.6.
#![allow(clippy::vec_init_then_push)]
#![allow(clippy::len_zero)]
// `RangeInclusive::contains` and `Option::is_none` are outside the modelled functions too, so the code compares and matches by hand.
#![allow(clippy::manual_range_contains)]
#![allow(clippy::redundant_pattern_matching)]

extern crate alloc;

pub mod decl;
pub mod error;
pub mod json;
pub mod keys;
pub mod ndjson;

pub use decl::{
    Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Opaque, Quot, QuotKind, Rec, RecRule,
    Safety, Thm,
};
pub use error::{Error, ErrorKind};
pub use ndjson::{Parser, parse};
