//! The in-process kernel. It reads Lean objects through the Lean ABI and gives the declarations to the verified core. See spec section 09.6.
//!
//! This crate has the first part of the in-process mode: the object model of the Lean runtime (`heap`), the reader of the memory of the process (`live`), and the conversion of a `Declaration` object into the store (`conv`). The exported symbols, the mirror of the environment and the conversion of the results back to Lean objects are not done yet.
//!
//! The conversion makes a declaration of the form that the checker takes from the other readers, so the checker does not know which reader made it. The checker must have `kernel_api` set, because a `Declaration` gives an inductive block without the recursors.
//!
//! ```
//! use rulean_ffi::heap::{OwnedHeap, boxed};
//!
//! // `Declaration.quotDecl` is the boxed scalar 4.
//! let heap = OwnedHeap::new();
//! let mut st = rulean_store::Store::new();
//! let d = rulean_ffi::conv::declaration(&heap, &mut st, boxed(4)).expect("a declaration");
//! assert!(matches!(d, rulean_format::Decl::Quot(_)));
//! ```

#![deny(unsafe_code)]

pub mod conv;
pub mod heap;
pub mod live;

use std::fmt;

/// The class of a conversion error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultKind {
    /// An object does not have the layout of its Lean type.
    Malformed,
    /// The object is valid, but the conversion does not support it, for example a number that does not fit in 32 bits where the store needs a `u32`.
    Decline,
    /// A free variable is in the declaration. The official kernel gives `declHasFVars`.
    FreeVar,
    /// A metavariable is in the declaration. The official kernel gives `declHasMVars`.
    MetaVar,
    /// The term store is full.
    StoreFull,
}

/// A conversion error at the object with address `at`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fault {
    pub kind: FaultKind,
    pub at: u64,
    pub msg: String,
}

impl Fault {
    pub fn new(kind: FaultKind, at: u64, msg: impl Into<String>) -> Fault {
        Fault {
            kind,
            at,
            msg: msg.into(),
        }
    }
}

impl fmt::Display for Fault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "object {:#x}: {}", self.at, self.msg)
    }
}

impl std::error::Error for Fault {}
