//! The type checker. It holds the universe levels, engine F, engine R, inductive types, quotients, declarations and the report. See spec sections 05 and 06.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
