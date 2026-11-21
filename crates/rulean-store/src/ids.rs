//! The handles of the store (spec 04.2.1 and 04.3).
//!
//! Every object of the store is a `u32` handle. Equal handles mean equal objects, because each table interns its objects.

/// A handle to an interned byte string.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StrId(pub u32);

/// A handle to a name. `NameId(0)` is the anonymous name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NameId(pub u32);

/// A handle to a universe level. `LevelId(0)` is the level zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LevelId(pub u32);

/// A handle to a list of levels. `LevelListId(0)` is the empty list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LevelListId(pub u32);

/// A handle to an interned natural number literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NatId(pub u32);

/// The kind of an expression node. The value is the 4-bit kind field of an `ExprId`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    BVar = 0,
    Sort = 1,
    Const = 2,
    App = 3,
    Lam = 4,
    Pi = 5,
    Let = 6,
    Lit = 7,
    Proj = 8,
    FVar = 9,
}

/// The number of expression kinds.
pub const KIND_COUNT: usize = 10;

/// The tier of an expression (spec 04.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tier {
    /// Input terms and the environment. It lives for the whole run.
    Frozen,
    /// Terms that a worker makes while it checks one declaration.
    Scratch,
}

/// The number of bits of the index field of an `ExprId`.
pub const INDEX_BITS: u32 = 27;

/// The largest number of nodes of one kind in one tier: 2^27.
pub const MAX_INDEX: u32 = 1 << INDEX_BITS;

/// A handle to an expression.
///
/// ```text
/// bit 31      : tier (0 = frozen, 1 = scratch)
/// bits 27..30 : kind
/// bits 0..26  : index into the array of that kind in that tier
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExprId(pub u32);

impl ExprId {
    /// The handle of node `index` of `kind` in `tier`. The caller makes sure that `index < MAX_INDEX`.
    pub fn new(tier: Tier, kind: Kind, index: u32) -> ExprId {
        let t: u32 = match tier {
            Tier::Frozen => 0,
            Tier::Scratch => 1,
        };
        ExprId((t << 31) | ((kind as u32) << INDEX_BITS) | index)
    }

    /// The kind of the node. It needs no memory load.
    pub fn kind(self) -> Kind {
        kind_of_bits((self.0 >> INDEX_BITS) & 0xf)
    }

    /// The tier of the node.
    pub fn tier(self) -> Tier {
        if self.0 >> 31 == 0 {
            Tier::Frozen
        } else {
            Tier::Scratch
        }
    }

    /// The index of the node in the array of its kind.
    pub fn index(self) -> usize {
        (self.0 & (MAX_INDEX - 1)) as usize
    }
}

/// The kind for the 4-bit kind field. A value above 9 is not made by `ExprId::new`, and it reads as `FVar`.
fn kind_of_bits(k: u32) -> Kind {
    match k {
        0 => Kind::BVar,
        1 => Kind::Sort,
        2 => Kind::Const,
        3 => Kind::App,
        4 => Kind::Lam,
        5 => Kind::Pi,
        6 => Kind::Let,
        7 => Kind::Lit,
        8 => Kind::Proj,
        _ => Kind::FVar,
    }
}

/// The binder information of a `lam` or a `pi` node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinderInfo {
    Default = 0,
    Implicit = 1,
    StrictImplicit = 2,
    InstImplicit = 3,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_fields() {
        let e = ExprId::new(Tier::Scratch, Kind::Proj, MAX_INDEX - 1);
        assert_eq!(e.kind(), Kind::Proj);
        assert_eq!(e.tier(), Tier::Scratch);
        assert_eq!(e.index(), (MAX_INDEX - 1) as usize);
        let f = ExprId::new(Tier::Frozen, Kind::FVar, 0);
        assert_eq!(
            (f.kind(), f.tier(), f.index()),
            (Kind::FVar, Tier::Frozen, 0)
        );
    }
}
