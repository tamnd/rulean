//! The term store: handles, per-kind node arrays, interning tables and tiers. See spec section 04.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).

#![no_std]

extern crate alloc;
