//! The in-process kernel. It reads Lean objects through the Lean ABI and gives the declarations to the verified core. See spec section 09.6.
//!
//! This crate has the first part of the in-process mode: the object model of the Lean runtime (`heap`), the reader of the memory of the process (`live`), the conversion of `Declaration`, `ConstantInfo`, `LocalContext` and `Expr` objects into the store (`conv`), the mirror of the environment (`mirror`), the construction of Lean objects from the store (`make`), the functions of the Lean runtime in the process (`rt`, on Linux and macOS), `addDecl` and the term functions on the Lean runtime (`kernel`, on Linux and macOS), and the exported kernel symbols of spec 09.6.2 (`export`, with the feature `export`).
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
#[cfg(all(
    feature = "export",
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
pub mod export;
pub mod heap;
#[cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
pub mod kernel;
pub mod live;
pub mod make;
pub mod mirror;
#[cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
pub mod rt;

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
