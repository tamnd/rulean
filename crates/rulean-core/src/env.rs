//! The environment: the constants that the checker has added (spec 04.7 and 05.9).
//!
//! The environment is an array indexed by the name handle. The store interns names, so the handles are dense and a lookup is one array access. The fields follow `declaration.h` of the official kernel v4.35.0.

use alloc::vec::Vec;
use rulean_format::{Hints, QuotKind, Safety};
use rulean_store::{ExprId, NameId};

/// The data of an inductive type (`inductive_val`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductInfo {
    pub nparams: u32,
    pub nindices: u32,
    /// The names of the types of the mutual block.
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub nnested: u32,
    pub is_rec: bool,
    pub is_reflexive: bool,
}

/// The data of a constructor (`constructor_val`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CtorInfo {
    pub induct: NameId,
    pub cidx: u32,
    pub nparams: u32,
    pub nfields: u32,
}

/// One rule of a recursor (`recursor_rule`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuleInfo {
    pub ctor: NameId,
    pub nfields: u32,
    pub rhs: ExprId,
}

/// The data of a recursor (`recursor_val`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecInfo {
    pub all: Vec<NameId>,
    pub nparams: u32,
    pub nindices: u32,
    pub nmotives: u32,
    pub nminors: u32,
    pub rules: Vec<RuleInfo>,
    pub k: bool,
}

impl RecInfo {
    /// The position of the major premise (`get_major_idx`).
    pub fn major_idx(&self) -> u32 {
        self.nparams + self.nmotives + self.nminors + self.nindices
    }
}

/// The kind and the kind data of a constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstKind {
    Axiom,
    Defn { value: ExprId, hints: Hints },
    Thm { value: ExprId },
    Opaque { value: ExprId },
    Quot { kind: QuotKind },
    Induct(InductInfo),
    Ctor(CtorInfo),
    Rec(RecInfo),
}

/// A constant of the environment (`constant_info`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstInfo {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    /// The safety. A theorem and a quotient constant are always safe.
    pub safety: Safety,
    pub kind: ConstKind,
}

impl ConstInfo {
    /// True for an unsafe constant (`is_unsafe`). A partial definition is not unsafe.
    pub fn is_unsafe(&self) -> bool {
        self.safety == Safety::Unsafe
    }

    /// True for a partial definition.
    pub fn is_partial_defn(&self) -> bool {
        match self.kind {
            ConstKind::Defn { .. } => self.safety == Safety::Partial,
            _ => false,
        }
    }

    /// The value of a definition or a theorem (`has_value` and `get_value`). Other constants have no value for reduction.
    pub fn value(&self) -> Option<ExprId> {
        match self.kind {
            ConstKind::Defn { value, .. } => Some(value),
            ConstKind::Thm { value } => Some(value),
            _ => None,
        }
    }

    /// The reducibility hint (`get_hints`). A constant that is not a definition is opaque.
    pub fn hints(&self) -> Hints {
        match self.kind {
            ConstKind::Defn { hints, .. } => hints,
            _ => Hints::Opaque,
        }
    }

    /// True for an inductive type.
    pub fn is_induct(&self) -> bool {
        matches!(self.kind, ConstKind::Induct(_))
    }

    /// True for a constructor.
    pub fn is_ctor(&self) -> bool {
        matches!(self.kind, ConstKind::Ctor(_))
    }
}

/// The relative priority of two hints for lazy delta reduction (`compare` of `declaration.cpp`). A negative value means: unfold the first. A positive value means: unfold the second. Zero means: unfold both.
pub fn compare_hints(h1: Hints, h2: Hints) -> i32 {
    match (h1, h2) {
        (Hints::Regular(a), Hints::Regular(b)) => {
            if a == b {
                0
            } else if a > b {
                -1
            } else {
                1
            }
        }
        (Hints::Opaque, Hints::Opaque) => 0,
        (Hints::Abbrev, Hints::Abbrev) => 0,
        (Hints::Opaque, _) => 1,
        (_, Hints::Opaque) => -1,
        (Hints::Abbrev, _) => -1,
        (_, Hints::Abbrev) => 1,
    }
}

/// The constants of a run.
///
/// `slot` maps a name handle to the position of its constant plus 1, or to 0. A lookup returns the slot, and `at` gives the constant of a slot. This keeps references out of the return types (subset rule S10).
#[derive(Clone, Debug, Default)]
pub struct Env {
    consts: Vec<ConstInfo>,
    slot: Vec<u32>,
    quot_init: bool,
}

impl Env {
    /// An empty environment.
    pub fn new() -> Env {
        Env {
            consts: Vec::new(),
            slot: Vec::new(),
            quot_init: false,
        }
    }

    /// The number of constants.
    pub fn len(&self) -> usize {
        self.consts.len()
    }

    /// True if there is no constant.
    pub fn is_empty(&self) -> bool {
        self.consts.len() == 0
    }

    /// The slot of the constant with the name, or 0 if there is none (`find`).
    pub fn find(&self, n: NameId) -> u32 {
        let i = n.0 as usize;
        if i < self.slot.len() { self.slot[i] } else { 0 }
    }

    /// True if the environment has a constant with the name.
    pub fn contains(&self, n: NameId) -> bool {
        self.find(n) != 0
    }

    /// The constant of a slot that `find` returned. The slot must not be 0.
    pub fn at(&self, s: u32) -> &ConstInfo {
        let i = (s - 1) as usize;
        &self.consts[i]
    }

    /// Adds the constant. A constant with the same name is replaced (`add_core`). The callers check the name first.
    pub fn add(&mut self, c: ConstInfo) {
        let i = c.name.0 as usize;
        while self.slot.len() <= i {
            self.slot.push(0);
        }
        let s = self.slot[i];
        if s == 0 {
            self.consts.push(c);
            let n = self.consts.len() as u32;
            self.slot[i] = n;
        } else {
            let k = (s - 1) as usize;
            self.consts[k] = c;
        }
    }

    /// Removes the constants after the first `n`, so the environment is as it was when it had `n` constants. A check that fails after it added constants uses this.
    pub fn truncate(&mut self, n: usize) {
        while self.consts.len() > n {
            let i = self.consts.len() - 1;
            let k = self.consts[i].name.0 as usize;
            self.slot[k] = 0;
            self.consts.pop();
        }
    }

    /// True if the quotient constants were added (`is_quot_initialized`).
    pub fn quot_initialized(&self) -> bool {
        self.quot_init
    }

    /// Records that the quotient constants were added.
    pub fn mark_quot_initialized(&mut self) {
        self.quot_init = true;
    }
}
