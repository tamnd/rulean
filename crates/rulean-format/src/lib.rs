//! The input formats of the verified core: the lean4export NDJSON scanner and the `.rlb` decoder. See spec section 07.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
