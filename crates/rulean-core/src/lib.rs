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
// scripts/extract.sh sets `--cfg rulean_extract`. Then Charon reads the `charon::opaque` attribute on the SHA-256 functions, which the proofs do not use.
#![cfg_attr(rulean_extract, feature(register_tool))]
#![cfg_attr(rulean_extract, register_tool(charon))]

extern crate alloc;

pub mod decl;
pub mod defeq;
pub mod env;
pub mod expr;
pub mod inductive;
pub mod level;
pub mod memo;
pub mod names;
pub mod nested;
pub mod pin;
pub mod sha256;
pub mod tc;
pub mod whnf;
