//! Expression nodes, side records and literals (spec 04.2).
//!
//! Each kind has its own node array, and each node has a side record of 8 bytes in a parallel array. One open-addressing table interns the nodes of all kinds. The hash of a node is structural: it mixes the kind seed with the hashes of the fields, not with their handles. So equal terms in two stores have equal hashes.

use alloc::vec::Vec;
use rulean_nat::Nat;

use crate::hash;
use crate::ids::{
    BinderInfo, ExprId, KIND_COUNT, Kind, LevelId, LevelListId, MAX_INDEX, NameId, NatId, StrId,
    Tier,
};
use crate::table::{Probe, Table};
use crate::{Side, Store};

/// The value of a saturated loose bound variable range (spec 04.2.2). A node with this range can have loose bound variables at any index, so a user must not skip it by its range.
pub const SATURATED: u32 = (1 << 24) - 1;

/// The flags of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Flags(pub u8);

impl Flags {
    /// The node has a free variable.
    pub const HAS_FVAR: u8 = 1;
    /// The node has a level parameter.
    pub const HAS_LEVEL_PARAM: u8 = 2;
    /// The node has a `let`.
    pub const HAS_LET: u8 = 4;
    /// The node has a literal.
    pub const HAS_LIT: u8 = 8;
    /// The node has a projection.
    pub const HAS_PROJ: u8 = 16;

    /// True if every flag of `mask` is set.
    pub fn has(self, mask: u8) -> bool {
        self.0 & mask == mask
    }
}

/// The fields of a `lam` or a `pi` node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Binder {
    pub name: NameId,
    pub info: BinderInfo,
    pub dom: ExprId,
    pub body: ExprId,
}

/// The fields of a `let` node. The `nondep` flag of the export has no effect on checking, so the store does not keep it (spec 07.1.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LetNode {
    pub name: NameId,
    pub ty: ExprId,
    pub value: ExprId,
    pub body: ExprId,
}

/// The fields of a `proj` node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProjNode {
    pub struct_name: NameId,
    pub index: u32,
    pub expr: ExprId,
}

/// A literal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Literal {
    Nat(NatId),
    Str(StrId),
}

/// An expression node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expr {
    BVar(u32),
    Sort(LevelId),
    Const(NameId, LevelListId),
    App(ExprId, ExprId),
    Lam(Binder),
    Pi(Binder),
    Let(LetNode),
    Lit(Literal),
    Proj(ProjNode),
    /// A free variable: its de Bruijn level and its type (spec 04.4).
    FVar(u32, ExprId),
}

impl Expr {
    /// The kind of the node.
    pub fn kind(&self) -> Kind {
        match self {
            Expr::BVar(_) => Kind::BVar,
            Expr::Sort(_) => Kind::Sort,
            Expr::Const(..) => Kind::Const,
            Expr::App(..) => Kind::App,
            Expr::Lam(_) => Kind::Lam,
            Expr::Pi(_) => Kind::Pi,
            Expr::Let(_) => Kind::Let,
            Expr::Lit(_) => Kind::Lit,
            Expr::Proj(_) => Kind::Proj,
            Expr::FVar(..) => Kind::FVar,
        }
    }
}

/// The node arrays and the table of one tier.
#[derive(Debug)]
pub(crate) struct Nodes {
    bvar: Vec<u32>,
    sort: Vec<LevelId>,
    cnst: Vec<(NameId, LevelListId)>,
    app: Vec<(ExprId, ExprId)>,
    lam: Vec<Binder>,
    pi: Vec<Binder>,
    let_: Vec<LetNode>,
    lit: Vec<Literal>,
    proj: Vec<ProjNode>,
    fvar: Vec<(u32, ExprId)>,
    sides: [Vec<Side>; KIND_COUNT],
    pub(crate) table: Table,
}

impl Nodes {
    pub(crate) fn new() -> Nodes {
        Nodes {
            bvar: Vec::new(),
            sort: Vec::new(),
            cnst: Vec::new(),
            app: Vec::new(),
            lam: Vec::new(),
            pi: Vec::new(),
            let_: Vec::new(),
            lit: Vec::new(),
            proj: Vec::new(),
            fvar: Vec::new(),
            sides: [
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ],
            table: Table::new(false),
        }
    }

    fn get(&self, kind: Kind, i: usize) -> Expr {
        match kind {
            Kind::BVar => Expr::BVar(self.bvar[i]),
            Kind::Sort => Expr::Sort(self.sort[i]),
            Kind::Const => Expr::Const(self.cnst[i].0, self.cnst[i].1),
            Kind::App => Expr::App(self.app[i].0, self.app[i].1),
            Kind::Lam => Expr::Lam(self.lam[i]),
            Kind::Pi => Expr::Pi(self.pi[i]),
            Kind::Let => Expr::Let(self.let_[i]),
            Kind::Lit => Expr::Lit(self.lit[i]),
            Kind::Proj => Expr::Proj(self.proj[i]),
            Kind::FVar => Expr::FVar(self.fvar[i].0, self.fvar[i].1),
        }
    }

    fn push(&mut self, node: Expr) {
        match node {
            Expr::BVar(i) => self.bvar.push(i),
            Expr::Sort(l) => self.sort.push(l),
            Expr::Const(n, ls) => self.cnst.push((n, ls)),
            Expr::App(f, a) => self.app.push((f, a)),
            Expr::Lam(b) => self.lam.push(b),
            Expr::Pi(b) => self.pi.push(b),
            Expr::Let(l) => self.let_.push(l),
            Expr::Lit(l) => self.lit.push(l),
            Expr::Proj(p) => self.proj.push(p),
            Expr::FVar(l, t) => self.fvar.push((l, t)),
        }
    }

    fn count(&self, kind: Kind) -> usize {
        self.sides[kind as usize].len()
    }

    /// The bytes of the node arrays and the side records.
    pub(crate) fn bytes(&self) -> usize {
        let mut sides = 0;
        let mut k = 0;
        while k < KIND_COUNT {
            sides += self.sides[k].capacity() * 8;
            k += 1;
        }
        sides
            + self.bvar.capacity() * 4
            + self.sort.capacity() * 4
            + self.cnst.capacity() * 8
            + self.app.capacity() * 8
            + self.lam.capacity() * 16
            + self.pi.capacity() * 16
            + self.let_.capacity() * 16
            + self.lit.capacity() * 8
            + self.proj.capacity() * 12
            + self.fvar.capacity() * 8
    }
}

const NAT_SEED: u32 = 0x4e41_5421;

/// The hash seed of each kind.
fn seed(kind: Kind) -> u32 {
    match kind {
        Kind::BVar => 0x0b0a_0001,
        Kind::Sort => 0x0b0a_0002,
        Kind::Const => 0x0b0a_0003,
        Kind::App => 0x0b0a_0004,
        Kind::Lam => 0x0b0a_0005,
        Kind::Pi => 0x0b0a_0006,
        Kind::Let => 0x0b0a_0007,
        Kind::Lit => 0x0b0a_0008,
        Kind::Proj => 0x0b0a_0009,
        Kind::FVar => 0x0b0a_000a,
    }
}

/// `r + 1`, saturated.
fn range_succ(r: u32) -> u32 {
    if r >= SATURATED - 1 { SATURATED } else { r + 1 }
}

/// The range of a body under one binder: `r - 1`, but a saturated range stays saturated.
fn range_under(r: u32) -> u32 {
    if r == SATURATED || r == 0 { r } else { r - 1 }
}

fn max32(a: u32, b: u32) -> u32 {
    if a > b { a } else { b }
}

fn pack(range: u32, flags: u8) -> u32 {
    range | (flags as u32) << 24
}

impl Store {
    /// The node of an expression.
    pub fn node(&self, e: ExprId) -> Expr {
        self.exprs.get(e.kind(), e.index())
    }

    /// The side record of an expression.
    pub fn side(&self, e: ExprId) -> Side {
        self.exprs.sides[e.kind() as usize][e.index()]
    }

    /// The structural hash of an expression.
    pub fn hash(&self, e: ExprId) -> u32 {
        self.side(e).hash
    }

    /// The loose bound variable range: every loose bound variable of the term has an index below it. It is `SATURATED` if it does not fit in 24 bits.
    pub fn loose_range(&self, e: ExprId) -> u32 {
        self.side(e).info & SATURATED
    }

    /// True if the term has no loose bound variable.
    pub fn is_closed(&self, e: ExprId) -> bool {
        self.loose_range(e) == 0
    }

    /// The flags of an expression.
    pub fn flags(&self, e: ExprId) -> Flags {
        Flags((self.side(e).info >> 24) as u8)
    }

    /// The number of expression nodes of a kind.
    pub fn expr_count(&self, kind: Kind) -> usize {
        self.exprs.count(kind)
    }

    /// The number of expression nodes of all kinds.
    pub fn expr_total(&self) -> usize {
        let mut n = 0;
        let mut k = 0;
        while k < KIND_COUNT {
            n += self.exprs.sides[k].len();
            k += 1;
        }
        n
    }

    fn intern_expr(&mut self, node: Expr, h: u32, info: u32) -> ExprId {
        let kind = node.kind();
        let mut pos = self.exprs.table.start(h);
        // `ExprId(0)` is a valid handle (bound variable node 0), so a flag says if the walk found the node.
        let mut hit = false;
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.exprs.table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    let id = ExprId(v);
                    if hh == h && id.kind() == kind && self.exprs.get(kind, id.index()) == node {
                        hit = true;
                        found = v;
                        walking = false;
                    } else {
                        pos = self.exprs.table.next(pos);
                    }
                }
            }
        }
        if hit {
            ExprId(found)
        } else if self.exprs.count(kind) >= MAX_INDEX as usize {
            self.full = true;
            ExprId::new(Tier::Frozen, kind, 0)
        } else {
            let id = ExprId::new(Tier::Frozen, kind, self.exprs.count(kind) as u32);
            self.exprs.push(node);
            self.exprs.sides[kind as usize].push(Side { hash: h, info });
            self.exprs.table.put(pos, h, id.0);
            id
        }
    }

    /// The bound variable with de Bruijn index `i`.
    pub fn mk_bvar(&mut self, i: u32) -> ExprId {
        let h = hash::finish(hash::mix(seed(Kind::BVar), i));
        self.intern_expr(Expr::BVar(i), h, pack(range_succ(i), 0))
    }

    /// `Sort l`.
    pub fn mk_sort(&mut self, l: LevelId) -> ExprId {
        let h = hash::finish(hash::mix(seed(Kind::Sort), self.level_hash(l)));
        let f = if self.level_has_param(l) {
            Flags::HAS_LEVEL_PARAM
        } else {
            0
        };
        self.intern_expr(Expr::Sort(l), h, pack(0, f))
    }

    /// The constant `n` with the level arguments `ls`.
    pub fn mk_const(&mut self, n: NameId, ls: LevelListId) -> ExprId {
        let h = hash::mix(
            hash::mix(seed(Kind::Const), self.name_hash(n)),
            self.level_list_hash(ls),
        );
        let f = if self.level_list_has_param(ls) {
            Flags::HAS_LEVEL_PARAM
        } else {
            0
        };
        self.intern_expr(Expr::Const(n, ls), hash::finish(h), pack(0, f))
    }

    /// The application `f a`.
    pub fn mk_app(&mut self, f: ExprId, a: ExprId) -> ExprId {
        let sf = self.side(f);
        let sa = self.side(a);
        let h = hash::mix(hash::mix(seed(Kind::App), sf.hash), sa.hash);
        let range = max32(sf.info & SATURATED, sa.info & SATURATED);
        let flags = ((sf.info | sa.info) >> 24) as u8;
        self.intern_expr(Expr::App(f, a), hash::finish(h), pack(range, flags))
    }

    /// The application of `f` to each argument, from the first to the last.
    pub fn mk_apps(&mut self, f: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = f;
        let mut i = 0;
        while i < args.len() {
            e = self.mk_app(e, args[i]);
            i += 1;
        }
        e
    }

    fn binder_side(&self, kind: Kind, b: Binder) -> (u32, u32) {
        let sd = self.side(b.dom);
        let sb = self.side(b.body);
        let mut h = hash::mix(seed(kind), self.name_hash(b.name));
        h = hash::mix(h, b.info as u32);
        h = hash::mix(hash::mix(h, sd.hash), sb.hash);
        let range = max32(sd.info & SATURATED, range_under(sb.info & SATURATED));
        let flags = ((sd.info | sb.info) >> 24) as u8;
        (hash::finish(h), pack(range, flags))
    }

    /// `fun (name : dom) => body`.
    pub fn mk_lam(&mut self, name: NameId, info: BinderInfo, dom: ExprId, body: ExprId) -> ExprId {
        let b = Binder {
            name,
            info,
            dom,
            body,
        };
        let (h, i) = self.binder_side(Kind::Lam, b);
        self.intern_expr(Expr::Lam(b), h, i)
    }

    /// `(name : dom) -> body`.
    pub fn mk_pi(&mut self, name: NameId, info: BinderInfo, dom: ExprId, body: ExprId) -> ExprId {
        let b = Binder {
            name,
            info,
            dom,
            body,
        };
        let (h, i) = self.binder_side(Kind::Pi, b);
        self.intern_expr(Expr::Pi(b), h, i)
    }

    /// `let name : ty := value; body`.
    pub fn mk_let(&mut self, name: NameId, ty: ExprId, value: ExprId, body: ExprId) -> ExprId {
        let st = self.side(ty);
        let sv = self.side(value);
        let sb = self.side(body);
        let mut h = hash::mix(seed(Kind::Let), self.name_hash(name));
        h = hash::mix(hash::mix(hash::mix(h, st.hash), sv.hash), sb.hash);
        let range = max32(
            max32(st.info & SATURATED, sv.info & SATURATED),
            range_under(sb.info & SATURATED),
        );
        let flags = ((st.info | sv.info | sb.info) >> 24) as u8 | Flags::HAS_LET;
        let node = LetNode {
            name,
            ty,
            value,
            body,
        };
        self.intern_expr(Expr::Let(node), hash::finish(h), pack(range, flags))
    }

    /// The natural number literal `n`.
    pub fn mk_nat_lit(&mut self, n: NatId) -> ExprId {
        let h = hash::finish(hash::mix(hash::mix(seed(Kind::Lit), 0), self.nat_hash(n)));
        self.intern_expr(Expr::Lit(Literal::Nat(n)), h, pack(0, Flags::HAS_LIT))
    }

    /// The string literal `s`. The caller checks that `s` is valid UTF-8.
    pub fn mk_str_lit(&mut self, s: StrId) -> ExprId {
        let h = hash::finish(hash::mix(hash::mix(seed(Kind::Lit), 1), self.str_hash(s)));
        self.intern_expr(Expr::Lit(Literal::Str(s)), h, pack(0, Flags::HAS_LIT))
    }

    /// The projection of field `index` of `expr`, which has the structure type `struct_name`.
    pub fn mk_proj(&mut self, struct_name: NameId, index: u32, expr: ExprId) -> ExprId {
        let se = self.side(expr);
        let mut h = hash::mix(seed(Kind::Proj), self.name_hash(struct_name));
        h = hash::mix(hash::mix(h, index), se.hash);
        let flags = (se.info >> 24) as u8 | Flags::HAS_PROJ;
        let node = ProjNode {
            struct_name,
            index,
            expr,
        };
        self.intern_expr(
            Expr::Proj(node),
            hash::finish(h),
            pack(se.info & SATURATED, flags),
        )
    }

    /// The free variable with de Bruijn level `level` and type `ty` (spec 04.4).
    pub fn mk_fvar(&mut self, level: u32, ty: ExprId) -> ExprId {
        let st = self.side(ty);
        let h = hash::mix(hash::mix(seed(Kind::FVar), level), st.hash);
        let flags = (st.info >> 24) as u8 | Flags::HAS_FVAR;
        self.intern_expr(
            Expr::FVar(level, ty),
            hash::finish(h),
            pack(st.info & SATURATED, flags),
        )
    }

    /// Interns a natural number literal. The hash covers every limb (spec 04.2.3).
    pub fn intern_nat(&mut self, n: Nat) -> NatId {
        let count = n.limb_count();
        let mut h = hash::mix(NAT_SEED, count as u32);
        let mut i = 0;
        while i < count {
            h = hash::word64(h, n.limb(i));
            i += 1;
        }
        let h = hash::finish(h);
        let mut pos = self.nat_table.start(h);
        let mut found: u32 = 0;
        let mut walking = true;
        while walking {
            match self.nat_table.get(pos) {
                Probe::Free => walking = false,
                Probe::Full(hh, v) => {
                    if hh == h && self.nats[v as usize] == n {
                        found = v + 1;
                        walking = false;
                    } else {
                        pos = self.nat_table.next(pos);
                    }
                }
            }
        }
        if found != 0 {
            NatId(found - 1)
        } else if self.nats.len() >= u32::MAX as usize - 1 {
            self.full = true;
            NatId(0)
        } else {
            let id = self.nats.len() as u32;
            self.nats.push(n);
            self.nat_hash.push(h);
            self.nat_table.put(pos, h, id);
            NatId(id)
        }
    }

    /// The value of a natural number literal.
    pub fn nat(&self, n: NatId) -> &Nat {
        &self.nats[n.0 as usize]
    }

    /// The hash of a natural number literal.
    pub fn nat_hash(&self, n: NatId) -> u32 {
        self.nat_hash[n.0 as usize]
    }
}
