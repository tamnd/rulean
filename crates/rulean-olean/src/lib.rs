//! A reader for Lean `.olean` files. It treats each byte as hostile input. See spec section 07.3.
//!
//! The reader loads the import closure of the modules that the caller gives, in import order. For each module it reads the `.olean` file and, for a module of the module system, the `.olean.server` and `.olean.private` files. It decodes the constants of `ModuleData` into a `rulean_store::Store` and returns them as a stream of `rulean_format::Decl` values. This is the same stream that the NDJSON parser gives for an export of the same modules, so the checker does not know which reader made it.
//!
//! The reader supports format version 2, which Lean v4.33 to v4.36 write, with the GMP encoding of big numbers. Another version or encoding is a decline.
//!
//! ```no_run
//! let mut store = rulean_store::Store::new();
//! let search = vec![std::path::PathBuf::from("/path/to/lib/lean")];
//! let loaded = rulean_olean::load(&mut store, &["Init.Prelude".to_owned()], &search).expect("oleans");
//! println!("{} declarations from {} modules", loaded.decls.len(), loaded.modules.len());
//! ```

#![forbid(unsafe_code)]

pub mod decode;
pub mod header;
pub mod lean_hash;
pub mod load;
pub mod region;

pub use load::{Loaded, Module, decode_parts, digest, load, module_path, read_module};

use std::fmt;
use std::path::PathBuf;

/// The class of an error. The command line gives an exit code for each class (spec 09.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FaultKind {
    /// The file breaks a rule of the format.
    Malformed,
    /// The file is valid, but the reader does not support it, for example an unknown format version.
    Decline,
    /// The term store is full.
    StoreFull,
    /// A module of the import closure is not on the search path.
    Missing,
    /// A file cannot be read.
    Io,
}

/// An error in one file. The loader adds the path of the file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fault {
    pub kind: FaultKind,
    /// The byte offset in the file.
    pub offset: u64,
    /// The part of the module, if it is not the part that the loader reads.
    pub part: Option<usize>,
    pub msg: String,
}

impl Fault {
    pub fn new(kind: FaultKind, offset: u64, msg: impl Into<String>) -> Fault {
        Fault {
            kind,
            offset,
            part: None,
            msg: msg.into(),
        }
    }

    /// The same fault in part `p`.
    pub fn in_part(mut self, p: usize) -> Fault {
        self.part = Some(p);
        self
    }
}

/// An error of the loader.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: FaultKind,
    /// The file of the error, if the error is in a file.
    pub file: Option<PathBuf>,
    pub offset: u64,
    pub msg: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.file {
            Some(p) => write!(f, "{}: byte {}: {}", p.display(), self.offset, self.msg),
            None => write!(f, "{}", self.msg),
        }
    }
}

impl std::error::Error for Error {}
