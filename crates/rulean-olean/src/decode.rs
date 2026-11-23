//! The typed decoder (spec 07.3.3).
//!
//! The decoder knows the Lean type at each position. It checks the tag, the field count and the size of each object against the constructor of that type. It writes the names, levels and expressions into the store, and it does not read the cached data: `Name.hash`, `Level.Data` and `Expr.Data`. The store computes its own hashes.
//!
//! Names, levels and expressions are shared in the file, so the decoder keeps a table from position to handle, with the type of the position. A position that is read as two different types is an error. The decoder uses an explicit stack and no recursion, so a deep term cannot overflow the thread stack. Each pointer goes to an earlier object (`Region::field`), so the decode always ends.

use rulean_format::ndjson::MAX_NAT_BITS;
use rulean_format::{
    Axiom, Ctor, Decl, Defn, Hints, InductType, Opaque, Quot, QuotKind, Rec, RecRule, Safety, Thm,
};
use rulean_nat::Nat;
use std::collections::{BTreeMap, BTreeSet};

use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, ExprId, LevelId, Name, NameId, Raw, Store};

use crate::region::{self, At, Field, Region, WORD, tag};
use crate::{Fault, FaultKind, lean_hash};

/// The types that the position table records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Ty {
    Name = 1,
    Level = 2,
    Expr = 3,
}

/// One constant of `ModuleData.constants`. The loader puts the inductive types, the constructors and the recursors into blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Decl(Decl),
    Type(InductType),
    Ctor(Ctor),
    Rec(Rec),
}

impl Item {
    /// The name of the constant.
    pub fn name(&self) -> NameId {
        match self {
            Item::Decl(d) => d.name(),
            Item::Type(t) => t.name,
            Item::Ctor(c) => c.name,
            Item::Rec(r) => r.name,
        }
    }
}

/// The fields of `ModuleData` that the reader takes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<NameId>,
    pub constants: Vec<Item>,
}

/// The decoder of one module.
pub struct Decoder<'a> {
    rg: &'a Region,
    st: &'a mut Store,
    /// For each part and each word of the part: the handle plus one, or zero.
    ids: Vec<Vec<Raw>>,
    /// For each part and each word of the part: the `Ty` of the position, or zero.
    tys: Vec<Vec<u8>>,
}

impl core::fmt::Debug for Decoder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Decoder")
            .field("parts", &self.ids.len())
            .finish_non_exhaustive()
    }
}

/// An error at `at`.
fn bad(at: At, msg: impl Into<String>) -> Fault {
    Fault::new(FaultKind::Malformed, at.off as u64, msg).in_part(at.part)
}

/// A value that the reader does not support, at `at`.
fn decline(at: At, msg: impl Into<String>) -> Fault {
    Fault::new(FaultKind::Decline, at.off as u64, msg).in_part(at.part)
}

impl<'a> Decoder<'a> {
    pub fn new(rg: &'a Region, st: &'a mut Store) -> Decoder<'a> {
        let ids = rg
            .parts
            .iter()
            .map(|p| vec![0; p.bytes.len() / WORD])
            .collect();
        let tys = rg
            .parts
            .iter()
            .map(|p| vec![0u8; p.bytes.len() / WORD])
            .collect();
        Decoder { rg, st, ids, tys }
    }

    /// The handle of `at` if the decoder has read it as `ty`. A position that has a different type is an error.
    fn seen(&self, at: At, ty: Ty) -> Result<Option<Raw>, Fault> {
        let i = at.off / WORD;
        let t = self.tys[at.part][i];
        if t == 0 {
            Ok(None)
        } else if t != ty as u8 {
            Err(bad(at, "an object is read as two different types"))
        } else {
            Ok(Some(self.ids[at.part][i] - 1))
        }
    }

    fn record(&mut self, at: At, ty: Ty, id: Raw) -> Result<(), Fault> {
        if self.st.is_full() {
            return Err(Fault::new(
                FaultKind::StoreFull,
                at.off as u64,
                "the term store is full",
            )
            .in_part(at.part));
        }
        let i = at.off / WORD;
        self.tys[at.part][i] = ty as u8;
        self.ids[at.part][i] = id + 1;
        Ok(())
    }

    /// The object that field `i` of `from` points to. A boxed scalar is an error.
    fn object(&self, from: At, i: usize) -> Result<At, Fault> {
        match self.rg.field(from, self.rg.ptr(from, i))? {
            Field::Object(at) => Ok(at),
            Field::Scalar(_) => Err(bad(
                from,
                "a field holds a scalar where an object is expected",
            )),
        }
    }

    /// The bytes of the string that field `i` of `from` points to. The string must be UTF-8, and its stored length and character count must be correct.
    fn string(&self, from: At, i: usize) -> Result<&'a [u8], Fault> {
        let at = self.object(from, i)?;
        let b: &'a [u8] = self.rg.bytes(at.part);
        if b[at.off + 7] != tag::STRING {
            return Err(bad(at, "the object is not a string"));
        }
        let size = region::word(b, at.off + WORD) as usize;
        let chars = region::word(b, at.off + 3 * WORD);
        let data = at.off + 4 * WORD;
        // The walk checked that the capacity is in the file, and that the size is at most the capacity.
        if size == 0 || b[data + size - 1] != 0 {
            return Err(bad(at, "a string has no zero byte at its end"));
        }
        let s = &b[data..data + size - 1];
        match core::str::from_utf8(s) {
            Ok(t) if t.chars().count() as u64 == chars => Ok(s),
            Ok(_) => Err(bad(at, "a string has a wrong character count")),
            Err(_) => Err(bad(at, "a string is not UTF-8")),
        }
    }

    /// The natural number that field `i` of `from` holds: a boxed scalar or a big number in the GMP encoding.
    fn nat(&self, from: At, i: usize) -> Result<Nat, Fault> {
        let at = match self.rg.field(from, self.rg.ptr(from, i))? {
            Field::Scalar(n) => return Ok(Nat::from_u64(n)),
            Field::Object(at) => at,
        };
        let b = self.rg.bytes(at.part);
        let cs = u16::from_le_bytes([b[at.off + 4], b[at.off + 5]]) as usize;
        if b[at.off + 7] != tag::MPZ || cs < 3 * WORD {
            return Err(bad(at, "the object is not a natural number"));
        }
        let alloc =
            i32::from_le_bytes([b[at.off + 8], b[at.off + 9], b[at.off + 10], b[at.off + 11]]);
        let size = i32::from_le_bytes([
            b[at.off + 12],
            b[at.off + 13],
            b[at.off + 14],
            b[at.off + 15],
        ]);
        let limbs = region::word(b, at.off + 2 * WORD);
        let want = self.rg.parts[at.part].header.base + (at.off + 3 * WORD) as u64;
        if size <= 0 || alloc < size || limbs != want || cs != 3 * WORD + size as usize * WORD {
            return Err(bad(at, "a big number has a bad GMP header"));
        }
        let v: Vec<u64> = (0..size as usize)
            .map(|k| region::word(b, at.off + 3 * WORD + k * WORD))
            .collect();
        let top = v[v.len() - 1];
        if top == 0 {
            return Err(bad(at, "a big number has a leading zero limb"));
        }
        if v.len() == 1 && top >> 63 == 0 {
            return Err(bad(at, "a big number is small enough to be a boxed scalar"));
        }
        let n = Nat::from_limbs(v);
        if n.bits() > MAX_NAT_BITS {
            return Err(decline(at, "a natural number is too large"));
        }
        Ok(n)
    }

    /// The natural number of field `i` as a `u32`. A larger value is a decline.
    fn small(&self, from: At, i: usize) -> Result<u32, Fault> {
        let n = self.nat(from, i)?;
        match n.to_u64().and_then(|x| u32::try_from(x).ok()) {
            Some(x) => Ok(x),
            None => Err(decline(from, "a count or an index does not fit in 32 bits")),
        }
    }

    /// The name that field `i` of `from` points to.
    pub fn name(&mut self, from: At, i: usize) -> Result<NameId, Fault> {
        let p = self.rg.ptr(from, i);
        self.name_ptr(from, p)
    }

    /// The name that the pointer `p` of `from` points to.
    fn name_ptr(&mut self, from: At, p: u64) -> Result<NameId, Fault> {
        let mut cur = match self.rg.field(from, p)? {
            Field::Scalar(0) => return Ok(self.st.anon()),
            Field::Scalar(_) => {
                return Err(bad(
                    from,
                    "a name is a scalar that is not the anonymous name",
                ));
            }
            Field::Object(at) => at,
        };
        // Walk down the prefixes to a name that is known, then make the names from the bottom up.
        let mut chain = Vec::new();
        let mut id = self.st.anon();
        loop {
            if let Some(k) = self.seen(cur, Ty::Name)? {
                id = NameId(low(k));
                break;
            }
            self.rg.ctor(cur, 1..=2, 2, 8, "name")?;
            chain.push(cur);
            match self.rg.field(cur, self.rg.ptr(cur, 0))? {
                Field::Scalar(0) => break,
                Field::Scalar(_) => {
                    return Err(bad(
                        cur,
                        "a name prefix is a scalar that is not the anonymous name",
                    ));
                }
                Field::Object(at) => cur = at,
            }
        }
        while let Some(at) = chain.pop() {
            id = if self.rg.tag(at) == 1 {
                let s = self.string(at, 1)?;
                self.st.name_str_bytes(id, s)
            } else {
                let n = self.nat(at, 1)?;
                match n.to_u64() {
                    Some(x) => self.st.name_num(id, x),
                    None => return Err(decline(at, "a number in a name does not fit in 64 bits")),
                }
            };
            self.record(at, Ty::Name, raw(id.0))?;
        }
        Ok(id)
    }

    /// The level that field `i` of `from` points to.
    pub fn level(&mut self, from: At, i: usize) -> Result<LevelId, Fault> {
        let Some(root) = self.level_field(from, i)? else {
            return Ok(self.st.level_zero());
        };
        let mut stack = vec![(root, false)];
        while let Some((at, ready)) = stack.pop() {
            if self.seen(at, Ty::Level)?.is_some() {
                continue;
            }
            let c = self.level_shape(at)?;
            let kids = match c.tag {
                1 => 1,
                2 | 3 => 2,
                _ => 0,
            };
            if !ready {
                stack.push((at, true));
                for k in 0..kids {
                    if let Some(child) = self.level_field(at, k)?
                        && self.seen(child, Ty::Level)?.is_none()
                    {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let id = match c.tag {
                0 => self.st.level_zero(),
                1 => {
                    let a = self.done_level(at, 0)?;
                    self.st.level_succ(a)
                }
                2 | 3 => {
                    let a = self.done_level(at, 0)?;
                    let b = self.done_level(at, 1)?;
                    if c.tag == 2 {
                        self.st.level_max(a, b)
                    } else {
                        self.st.level_imax(a, b)
                    }
                }
                4 => {
                    let n = self.name(at, 0)?;
                    self.st.level_param(n)
                }
                _ => {
                    return Err(bad(
                        at,
                        "a level metavariable cannot be in a kernel declaration",
                    ));
                }
            };
            self.record(at, Ty::Level, raw(id.0))?;
        }
        match self.seen(root, Ty::Level)? {
            Some(k) => Ok(LevelId(low(k))),
            None => Err(bad(root, "a level is not decoded")),
        }
    }

    /// The shape of a level constructor: its object fields and the 8 bytes of `Level.Data`.
    fn level_shape(&self, at: At) -> Result<region::Ctor, Fault> {
        let objs = match self.rg.tag(at) {
            0 => 0,
            1 | 4 | 5 => 1,
            _ => 2,
        };
        self.rg.ctor(at, 0..=5, objs, 8, "level")
    }

    /// The object of the level in field `i` of `from`, or `None` for the boxed scalar 0. Lean stores `Level.zero` as the boxed scalar 0, as it does for each constructor without fields.
    fn level_field(&self, from: At, i: usize) -> Result<Option<At>, Fault> {
        match self.rg.field(from, self.rg.ptr(from, i))? {
            Field::Scalar(0) => Ok(None),
            Field::Scalar(_) => Err(bad(from, "a level is a scalar that is not `Level.zero`")),
            Field::Object(at) => Ok(Some(at)),
        }
    }

    /// The level of field `i` of `at`, which the stack has decoded.
    fn done_level(&self, at: At, i: usize) -> Result<LevelId, Fault> {
        let Some(child) = self.level_field(at, i)? else {
            return Ok(LevelId(0));
        };
        match self.seen(child, Ty::Level)? {
            Some(k) => Ok(LevelId(low(k))),
            None => Err(bad(child, "a level is not decoded")),
        }
    }

    /// The list of levels that field `i` of `from` points to.
    fn level_list(&mut self, from: At, i: usize) -> Result<rulean_store::LevelListId, Fault> {
        let cells = self.list(from, i)?;
        let mut ls = Vec::with_capacity(cells.len());
        for c in cells {
            ls.push(self.level(c, 0)?);
        }
        Ok(self.st.level_list(&ls))
    }

    /// The cons cells of the list that field `i` of `from` points to. The head of each cell is its field 0.
    fn list(&self, from: At, i: usize) -> Result<Vec<At>, Fault> {
        let mut out = Vec::new();
        let mut cur = from;
        let mut k = i;
        loop {
            match self.rg.field(cur, self.rg.ptr(cur, k))? {
                Field::Scalar(0) => return Ok(out),
                Field::Scalar(_) => {
                    return Err(bad(
                        cur,
                        "a list ends with a scalar that is not the empty list",
                    ));
                }
                Field::Object(at) => {
                    self.rg.ctor(at, 1..=1, 2, 0, "list cell")?;
                    out.push(at);
                    cur = at;
                    k = 1;
                }
            }
        }
    }

    /// The names of the list that field `i` of `from` points to.
    fn names(&mut self, from: At, i: usize) -> Result<Vec<NameId>, Fault> {
        let cells = self.list(from, i)?;
        let mut out = Vec::with_capacity(cells.len());
        for c in cells {
            out.push(self.name(c, 0)?);
        }
        Ok(out)
    }

    /// The position of the array that field `i` of `from` points to, and the pointers of its elements.
    fn array(&self, from: At, i: usize) -> Result<(At, Vec<u64>), Fault> {
        let at = self.object(from, i)?;
        let b = self.rg.bytes(at.part);
        if b[at.off + 7] != tag::ARRAY || b[at.off + 6] & 0x7f != 0 {
            return Err(bad(at, "the object is not an array"));
        }
        let n = region::word(b, at.off + WORD) as usize;
        let out = (0..n)
            .map(|k| region::word(b, at.off + 3 * WORD + k * WORD))
            .collect();
        Ok((at, out))
    }

    /// The elements of the array that field `i` of `from` points to. Each element must be an object.
    fn objects(&self, from: At, i: usize) -> Result<Vec<At>, Fault> {
        let (at, ps) = self.array(from, i)?;
        let mut out = Vec::with_capacity(ps.len());
        for p in ps {
            match self.rg.field(at, p)? {
                Field::Object(e) => out.push(e),
                Field::Scalar(_) => {
                    return Err(bad(
                        at,
                        "an array element is a scalar where an object is expected",
                    ));
                }
            }
        }
        Ok(out)
    }

    /// The expression that field `i` of `from` points to.
    pub fn expr(&mut self, from: At, i: usize) -> Result<ExprId, Fault> {
        let root = self.object(from, i)?;
        let mut stack = vec![(root, false)];
        while let Some((at, ready)) = stack.pop() {
            if self.seen(at, Ty::Expr)?.is_some() {
                continue;
            }
            let t = self.rg.tag(at);
            // The object fields of each constructor, the scalar bytes, and the fields that are expressions.
            let (objs, scalars, kids): (usize, usize, &[usize]) = match t {
                0 | 3 | 9 => (1, 8, &[]),
                4 => (2, 8, &[]),
                5 => (2, 8, &[0, 1]),
                6 | 7 => (3, 9, &[1, 2]),
                8 => (4, 9, &[1, 2, 3]),
                10 => (2, 8, &[1]),
                11 => (3, 8, &[2]),
                1 | 2 => {
                    return Err(bad(
                        at,
                        "a free variable or a metavariable cannot be in a kernel declaration",
                    ));
                }
                _ => return Err(bad(at, format!("the object is not an expression: tag {t}"))),
            };
            self.rg.ctor(at, t..=t, objs, scalars, "expression")?;
            if !ready {
                stack.push((at, true));
                for &k in kids {
                    let child = self.object(at, k)?;
                    if self.seen(child, Ty::Expr)?.is_none() {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let id = self.expr_node(at, t)?;
            self.record(at, Ty::Expr, id.0)?;
        }
        match self.seen(root, Ty::Expr)? {
            Some(k) => Ok(ExprId(k)),
            None => Err(bad(root, "an expression is not decoded")),
        }
    }

    /// The expression of field `i` of `at`, which the stack has decoded.
    fn done_expr(&self, at: At, i: usize) -> Result<ExprId, Fault> {
        let child = self.object(at, i)?;
        match self.seen(child, Ty::Expr)? {
            Some(k) => Ok(ExprId(k)),
            None => Err(bad(child, "an expression is not decoded")),
        }
    }

    /// Makes the node of the expression at `at` with tag `t`. The expressions of its fields are decoded.
    fn expr_node(&mut self, at: At, t: u8) -> Result<ExprId, Fault> {
        let c = region::Ctor {
            at,
            tag: t,
            objs: 0,
        };
        Ok(match t {
            0 => {
                let i = self.small(at, 0)?;
                self.st.mk_bvar(i)
            }
            3 => {
                let l = self.level(at, 0)?;
                self.st.mk_sort(l)
            }
            4 => {
                let n = self.name(at, 0)?;
                let ls = self.level_list(at, 1)?;
                self.st.mk_const(n, ls)
            }
            5 => {
                let f = self.done_expr(at, 0)?;
                let a = self.done_expr(at, 1)?;
                self.st.mk_app(f, a)
            }
            6 | 7 => {
                let n = self.name(at, 0)?;
                let dom = self.done_expr(at, 1)?;
                let body = self.done_expr(at, 2)?;
                let info = match self.rg.u8_at(region::Ctor { objs: 3, ..c }, 8) {
                    0 => BinderInfo::Default,
                    1 => BinderInfo::Implicit,
                    2 => BinderInfo::StrictImplicit,
                    3 => BinderInfo::InstImplicit,
                    v => return Err(bad(at, format!("a binder has the binder info {v}"))),
                };
                if t == 6 {
                    self.st.mk_lam(n, info, dom, body)
                } else {
                    self.st.mk_pi(n, info, dom, body)
                }
            }
            8 => {
                let n = self.name(at, 0)?;
                let ty = self.done_expr(at, 1)?;
                let v = self.done_expr(at, 2)?;
                let body = self.done_expr(at, 3)?;
                // `nondep` has no effect on checking (spec 07.1.2), but it must be a boolean.
                self.rg.bool_at(region::Ctor { objs: 4, ..c }, 8)?;
                self.st.mk_let(n, ty, v, body)
            }
            9 => {
                let lit = self.object(at, 0)?;
                let l = self.rg.ctor(lit, 0..=1, 1, 0, "literal")?;
                if l.tag == 0 {
                    let n = self.nat(lit, 0)?;
                    let id = self.st.intern_nat(n);
                    self.st.mk_nat_lit(id)
                } else {
                    let s = self.string(lit, 0)?;
                    let id = self.st.intern_str(s);
                    self.st.mk_str_lit(id)
                }
            }
            10 => {
                // `mdata`: the kernel ignores the data, so the reader checks only that the pointer is valid, and takes the inner expression.
                self.object(at, 0)?;
                self.done_expr(at, 1)?
            }
            _ => {
                let n = self.name(at, 0)?;
                let i = self.small(at, 1)?;
                let e = self.done_expr(at, 2)?;
                self.st.mk_proj(n, i, e)
            }
        })
    }

    /// The `ConstantVal` that field 0 of `val` points to: the name, the level parameters and the type.
    fn cval(&mut self, val: At) -> Result<(NameId, Vec<NameId>, ExprId), Fault> {
        let at = self.object(val, 0)?;
        self.rg.ctor(at, 0..=0, 3, 0, "ConstantVal")?;
        let name = self.name(at, 0)?;
        let lparams = self.names(at, 1)?;
        let ty = self.expr(at, 2)?;
        Ok((name, lparams, ty))
    }

    /// A boolean `isUnsafe` field as a safety.
    fn unsafe_flag(&self, c: region::Ctor, k: usize) -> Result<Safety, Fault> {
        Ok(if self.rg.bool_at(c, k)? {
            Safety::Unsafe
        } else {
            Safety::Safe
        })
    }

    /// The `ConstantInfo` at `at`.
    pub fn constant(&mut self, at: At) -> Result<Item, Fault> {
        let ci = self.rg.ctor(at, 0..=7, 1, 0, "ConstantInfo")?;
        let v = self.object(at, 0)?;
        Ok(match ci.tag {
            0 => {
                let c = self.rg.ctor(v, 0..=0, 1, 1, "AxiomVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let safety = self.unsafe_flag(c, 0)?;
                Item::Decl(Decl::Axiom(Axiom {
                    name,
                    lparams,
                    ty,
                    safety,
                }))
            }
            1 => {
                let c = self.rg.ctor(v, 0..=0, 4, 1, "DefinitionVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let value = self.expr(v, 1)?;
                let hints = self.hints(v, 2)?;
                let safety = match self.rg.u8_at(c, 0) {
                    0 => Safety::Unsafe,
                    1 => Safety::Safe,
                    2 => Safety::Partial,
                    s => return Err(bad(v, format!("a definition has the safety {s}"))),
                };
                let all = self.names(v, 3)?;
                Item::Decl(Decl::Defn(Defn {
                    name,
                    lparams,
                    ty,
                    value,
                    hints,
                    safety,
                    all,
                }))
            }
            2 => {
                self.rg.ctor(v, 0..=0, 3, 0, "TheoremVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let value = self.expr(v, 1)?;
                let all = self.names(v, 2)?;
                Item::Decl(Decl::Thm(Thm {
                    name,
                    lparams,
                    ty,
                    value,
                    all,
                }))
            }
            3 => {
                let c = self.rg.ctor(v, 0..=0, 3, 1, "OpaqueVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let value = self.expr(v, 1)?;
                let safety = self.unsafe_flag(c, 0)?;
                let all = self.names(v, 2)?;
                Item::Decl(Decl::Opaque(Opaque {
                    name,
                    lparams,
                    ty,
                    value,
                    safety,
                    all,
                }))
            }
            4 => {
                let c = self.rg.ctor(v, 0..=0, 1, 1, "QuotVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let kind = match self.rg.u8_at(c, 0) {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    k => return Err(bad(v, format!("a quotient has the kind {k}"))),
                };
                Item::Decl(Decl::Quot(Quot {
                    name,
                    lparams,
                    ty,
                    kind,
                }))
            }
            5 => {
                let c = self.rg.ctor(v, 0..=0, 6, 3, "InductiveVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                Item::Type(InductType {
                    name,
                    lparams,
                    ty,
                    num_params: self.small(v, 1)?,
                    num_indices: self.small(v, 2)?,
                    all: self.names(v, 3)?,
                    ctors: self.names(v, 4)?,
                    num_nested: self.small(v, 5)?,
                    is_rec: self.rg.bool_at(c, 0)?,
                    safety: self.unsafe_flag(c, 1)?,
                    is_reflexive: self.rg.bool_at(c, 2)?,
                })
            }
            6 => {
                let c = self.rg.ctor(v, 0..=0, 5, 1, "ConstructorVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                Item::Ctor(Ctor {
                    name,
                    lparams,
                    ty,
                    induct: self.name(v, 1)?,
                    cidx: self.small(v, 2)?,
                    num_params: self.small(v, 3)?,
                    num_fields: self.small(v, 4)?,
                    safety: self.unsafe_flag(c, 0)?,
                })
            }
            _ => {
                let c = self.rg.ctor(v, 0..=0, 7, 2, "RecursorVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let all = self.names(v, 1)?;
                let num_params = self.small(v, 2)?;
                let num_indices = self.small(v, 3)?;
                let num_motives = self.small(v, 4)?;
                let num_minors = self.small(v, 5)?;
                let mut rules = Vec::new();
                for cell in self.list(v, 6)? {
                    let r = self.object(cell, 0)?;
                    self.rg.ctor(r, 0..=0, 3, 0, "RecursorRule")?;
                    rules.push(RecRule {
                        ctor: self.name(r, 0)?,
                        nfields: self.small(r, 1)?,
                        rhs: self.expr(r, 2)?,
                    });
                }
                Item::Rec(Rec {
                    name,
                    lparams,
                    ty,
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    k: self.rg.bool_at(c, 0)?,
                    rules,
                    safety: self.unsafe_flag(c, 1)?,
                })
            }
        })
    }

    /// The reducibility hints of field `i` of `v`.
    fn hints(&self, v: At, i: usize) -> Result<Hints, Fault> {
        match self.rg.field(v, self.rg.ptr(v, i))? {
            Field::Scalar(0) => Ok(Hints::Opaque),
            Field::Scalar(1) => Ok(Hints::Abbrev),
            Field::Scalar(s) => Err(bad(v, format!("the reducibility hints have the value {s}"))),
            Field::Object(at) => {
                let c = self.rg.ctor(at, 2..=2, 0, 4, "ReducibilityHints")?;
                Ok(Hints::Regular(self.rg.u32_at(c, 0)))
            }
        }
    }

    /// Checks the constant trie of a version 4 module (spec 07.3.3). Lean finds the imported constants in the trie and not in `constants`, so the trie must map each key of `keys` to the same constant object, and it must have no other value. Lean finds a child by binary search on the cached hash of its key and then compares the last component. So the reader checks that each key extends the key of its parent by one component, that each cached hash is the hash that Lean computes, that the children are sorted by hash and that no two children have the same key. Then the search of Lean finds exactly the keys of the trie. A trie is a tree, so a node that occurs two times is an error.
    fn const_trie(&mut self, root: At, keys: Vec<(NameId, At)>) -> Result<(), Fault> {
        let mut want: BTreeMap<NameId, At> = BTreeMap::new();
        for (n, ci) in keys {
            if want.insert(n, ci).is_some() {
                return Err(bad(ci, "constNames has a name two times"));
            }
        }
        let mut seen: BTreeSet<At> = BTreeSet::new();
        let mut found = 0usize;
        let anon = self.st.anon();
        let mut stack = vec![(root, anon)];
        while let Some((node, parent)) = stack.pop() {
            if !seen.insert(node) {
                return Err(bad(node, "a node of the constant trie occurs two times"));
            }
            let (objs, val, kids) = match self.rg.tag(node) {
                0 => (2, Some(1), None),
                1 => (2, None, Some(1)),
                2 => (3, Some(1), Some(2)),
                t => {
                    return Err(bad(
                        node,
                        format!("a node of the constant trie has the tag {t}"),
                    ));
                }
            };
            self.rg.ctor(node, 0..=2, objs, 0, "ConstTrie")?;
            let key = self.name(node, 0)?;
            if node == root {
                if key != anon || val.is_some() {
                    return Err(bad(
                        node,
                        "the root of the constant trie is not an anonymous node without a value",
                    ));
                }
            } else {
                let pre = match self.st.name(key) {
                    Name::Str(p, _) | Name::Num(p, _) => p,
                    Name::Anon => anon,
                };
                if key == anon || pre != parent {
                    return Err(bad(
                        node,
                        "a key of the constant trie does not extend the key of its parent",
                    ));
                }
            }
            if let Some(v) = val {
                let ci = self.object(node, v)?;
                if want.get(&key) != Some(&ci) {
                    return Err(bad(
                        node,
                        format!(
                            "the constant trie maps {} to a constant that is not in constants",
                            String::from_utf8_lossy(&self.st.name_text(key))
                        ),
                    ));
                }
                found += 1;
            }
            if let Some(k) = kids {
                // The children are sorted by hash, and two equal keys have the same hash. So two children with the same key are in one run of children with equal hashes, and the reader compares each child with the run before it.
                let mut run_hash: Option<u64> = None;
                let mut run: Vec<NameId> = Vec::new();
                for c in self.objects(node, k)? {
                    let key_at = match self.rg.field(c, self.rg.ptr(c, 0))? {
                        Field::Object(o) => o,
                        Field::Scalar(_) => {
                            return Err(bad(
                                c,
                                "a child of the constant trie has the anonymous key",
                            ));
                        }
                    };
                    let ck = self.name(c, 0)?;
                    let cached = region::word(self.rg.bytes(key_at.part), key_at.off + 3 * WORD);
                    if cached != lean_hash::name(self.st, ck) {
                        return Err(bad(
                            key_at,
                            "the cached hash of a key of the constant trie is not the hash of the name",
                        ));
                    }
                    if run_hash.is_some_and(|h| cached < h) {
                        return Err(bad(
                            c,
                            "the children of a node of the constant trie are not sorted by hash",
                        ));
                    }
                    if run_hash != Some(cached) {
                        run.clear();
                        run_hash = Some(cached);
                    }
                    if run.contains(&ck) {
                        return Err(bad(
                            c,
                            "two children of a node of the constant trie have the same key",
                        ));
                    }
                    run.push(ck);
                    stack.push((c, key));
                }
            }
        }
        if found != want.len() {
            return Err(bad(
                root,
                "the constant trie does not have each constant of constants",
            ));
        }
        Ok(())
    }

    /// The `ModuleData` at the root of part `part`.
    pub fn module_data(&mut self, part: usize) -> Result<ModuleData, Fault> {
        let p = &self.rg.parts[part];
        let root = p.root;
        // The root pointer is outside all objects, so it is read as a field of a position after the last object.
        let after = At {
            part,
            off: p.bytes.len(),
        };
        let at = match self.rg.field(after, root)? {
            Field::Object(at) => at,
            Field::Scalar(_) => return Err(bad(after, "the root is a scalar")),
        };
        // The root can be in an earlier part. Lean writes a private part without objects when the private data is the same as the public data, and its root is the root of the public part.
        // Version 4 adds the fields `constTrie?` and `extraConstTrie?`.
        let v4 = self.rg.parts[part].header.version >= 4;
        let c = self
            .rg
            .ctor(at, 0..=0, if v4 { 7 } else { 5 }, 1, "ModuleData")?;
        let is_module = self.rg.bool_at(c, 0)?;
        let mut imports = Vec::new();
        for i in self.objects(at, 0)? {
            self.rg.ctor(i, 0..=0, 1, 3, "Import")?;
            imports.push(self.name(i, 0)?);
        }
        let (names_at, names) = self.array(at, 1)?;
        let consts = self.objects(at, 2)?;
        if names.len() != consts.len() {
            return Err(bad(at, "constNames and constants have different lengths"));
        }
        let mut constants = Vec::with_capacity(consts.len());
        let mut keys = Vec::with_capacity(consts.len());
        for (k, ci) in consts.iter().copied().enumerate() {
            let item = self.constant(ci)?;
            let n = self.name_ptr(names_at, names[k])?;
            if n != item.name() {
                return Err(bad(ci, "constNames does not agree with constants"));
            }
            keys.push((n, ci));
            constants.push(item);
        }
        // `extraConstNames` and `entries` are environment data. The reader checks only that the pointers are valid (spec 07.3.3).
        self.object(at, 3)?;
        self.object(at, 4)?;
        if v4 {
            let trie = match self.rg.field(at, self.rg.ptr(at, 5))? {
                Field::Object(o) => o,
                Field::Scalar(_) => return Err(bad(at, "the module data has no constant trie")),
            };
            self.rg.ctor(trie, 1..=1, 1, 0, "Option.some")?;
            let root = self.object(trie, 0)?;
            self.const_trie(root, keys)?;
            self.rg.field(at, self.rg.ptr(at, 6))?;
        }
        Ok(ModuleData {
            is_module,
            imports,
            constants,
        })
    }
}
