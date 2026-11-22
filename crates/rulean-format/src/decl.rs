//! The declaration stream (spec 04.7).
//!
//! All input formats decode to the type `Decl`. The handles in a `Decl` refer to the frozen tier of the store that the parser wrote into.
//!
//! The parser keeps every field of the input. Some fields are values that the checker computes again, for example the recursor of an inductive type. The checker compares them with its own values and never trusts them (spec 06.1).

use alloc::vec::Vec;
use rulean_store::{ExprId, NameId};

/// The safety of a declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Safety {
    Safe,
    Unsafe,
    Partial,
}

/// The reducibility hint of a definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hints {
    Opaque,
    Abbrev,
    /// A regular definition with its height.
    Regular(u32),
}

/// The kind of a quotient constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuotKind {
    /// `Quot`.
    Type,
    /// `Quot.mk`.
    Ctor,
    /// `Quot.lift`.
    Lift,
    /// `Quot.ind`.
    Ind,
}

/// An axiom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Axiom {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub safety: Safety,
}

/// A definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Defn {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub value: ExprId,
    pub hints: Hints,
    pub safety: Safety,
    /// The names of the mutual block.
    pub all: Vec<NameId>,
}

/// A theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Thm {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub value: ExprId,
    pub all: Vec<NameId>,
}

/// An opaque constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opaque {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub value: ExprId,
    pub safety: Safety,
    pub all: Vec<NameId>,
}

/// A quotient constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quot {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub kind: QuotKind,
}

/// One type of an inductive block, as the input gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductType {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: u32,
    pub is_rec: bool,
    pub is_reflexive: bool,
    pub safety: Safety,
}

/// One constructor of an inductive block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctor {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub induct: NameId,
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub safety: Safety,
}

/// One rule of an exported recursor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecRule {
    pub ctor: NameId,
    pub nfields: u32,
    pub rhs: ExprId,
}

/// One exported recursor. The checker makes its own recursor and compares the two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rec {
    pub name: NameId,
    pub lparams: Vec<NameId>,
    pub ty: ExprId,
    pub all: Vec<NameId>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub k: bool,
    pub rules: Vec<RecRule>,
    pub safety: Safety,
}

/// An inductive block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Induct {
    pub types: Vec<InductType>,
    pub ctors: Vec<Ctor>,
    pub recs: Vec<Rec>,
}

/// One declaration of the stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Axiom(Axiom),
    Defn(Defn),
    Thm(Thm),
    Opaque(Opaque),
    Quot(Quot),
    Induct(Induct),
    /// A block of unsafe or partial definitions that can refer to each other, as the `mutualDefnDecl` declaration of Lean. The checker adds it with `add_mutual`. The NDJSON format has no form for it, and the `.olean` reader gives it (spec 07.3.4).
    Mutual(Vec<Defn>),
}

impl Decl {
    /// The name of the declaration. For an inductive block, it is the name of the first type, and for a mutual block the name of the first definition. For an empty block it is the anonymous name.
    pub fn name(&self) -> NameId {
        match self {
            Decl::Axiom(d) => d.name,
            Decl::Defn(d) => d.name,
            Decl::Thm(d) => d.name,
            Decl::Opaque(d) => d.name,
            Decl::Quot(d) => d.name,
            Decl::Induct(d) => {
                if d.types.len() == 0 {
                    NameId(0)
                } else {
                    d.types[0].name
                }
            }
            Decl::Mutual(ds) => {
                if ds.len() == 0 {
                    NameId(0)
                } else {
                    ds[0].name
                }
            }
        }
    }
}
