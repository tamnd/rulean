//! The natural number type of the kernel. A small value is a `u64`, a large value is a list of limbs. See spec section 04.6.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
