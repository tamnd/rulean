//! The type checker. It holds the universe levels, engines F and R, inductive types, quotients, declarations and the report. See spec sections 05 and 06.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).

#![no_std]
#![forbid(unsafe_code)]
// The `vec!` macro and `is_empty` are outside the modelled `Vec` functions of spec 10.6.
#![allow(clippy::vec_init_then_push)]
#![allow(clippy::len_zero)]
// `Option` combinators and `?` are outside the subset, so the code matches by hand.
#![allow(clippy::collapsible_if)]
#![allow(clippy::collapsible_match)]
#![allow(clippy::question_mark)]
#![allow(clippy::comparison_chain)]
// `Vec::clear`, `slice::swap` and `checked_sub` are outside the modelled functions too.
#![allow(clippy::manual_clear)]
#![allow(clippy::manual_swap)]
#![allow(clippy::implicit_saturating_sub)]

extern crate alloc;

pub mod defeq;
pub mod env;
pub mod expr;
pub mod level;
pub mod memo;
pub mod tc;
pub mod whnf;
