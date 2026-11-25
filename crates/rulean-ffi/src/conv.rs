//! The conversion of a Lean `Declaration` object into the store (spec 09.6.3).
//!
//! The conversion knows the Lean type at each address. It checks the tag and the number of object fields of each constructor object against the constructor of that type, and it reads the scalar fields at the offsets that the layout of the constructor gives. It does not read the cached data: `Name.hash`, `Level.Data` and `Expr.Data`. The store computes its own hashes.
//!
//! Names, levels and expressions are shared in the Lean heap, so the conversion keeps a table from address to handle for each type. It uses an explicit stack and no recursion, so a deep term cannot overflow the thread stack.
//!
//! The layouts are those of Lean v4.36.0 (appendix D, sections 1.3 and 3). A `Declaration` is one of these constructors:
//!
//! | Tag | Constructor | Object fields | Scalar fields |
//! |---|---|---|---|
//! | 0 | `axiomDecl` | `AxiomVal` | |
//! | 1 | `defnDecl` | `DefinitionVal` | |
//! | 2 | `thmDecl` | `TheoremVal` | |
//! | 3 | `opaqueDecl` | `OpaqueVal` | |
//! | 4 | `quotDecl` | none, so the value is the boxed scalar 4 | |
//! | 5 | `mutualDefnDecl` | `List DefinitionVal` | |
//! | 6 | `inductDecl` | `List Name`, `Nat`, `List InductiveType` | `isUnsafe` |
//!
//! A `ConstantInfo` is a constructor with one object field, the value of the constant. The tags are `axiomInfo` 0, `defnInfo` 1, `thmInfo` 2, `opaqueInfo` 3, `quotInfo` 4, `inductInfo` 5, `ctorInfo` 6 and `recInfo` 7. The layouts of the values are the same as in a `.olean` file (spec 07.3).

use std::collections::{HashMap, HashSet};

use rulean_core::env::{ConstInfo, ConstKind, CtorInfo, InductInfo, RecInfo, RuleInfo};
use rulean_format::ndjson::MAX_NAT_BITS;
use rulean_format::{
    Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Opaque, Quot, QuotKind, Safety, Thm,
};
use rulean_nat::Nat;
use rulean_store::{BinderInfo, ExprId, LevelId, LevelListId, NameId, Store};

use crate::heap::{Heap, WORD, tag};
use crate::{Fault, FaultKind};

/// A word of an object field: a boxed scalar or the address of an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Field {
    Scalar(u64),
    Object(u64),
}

/// The largest value of a boxed natural number (`LEAN_MAX_SMALL_NAT` on a 64-bit target).
const MAX_SMALL_NAT: u64 = u64::MAX >> 1;

/// Converts the `Declaration` object at `decl` into a declaration of the store.
///
/// An inductive declaration gives a block with the types and the constructors only. The counts that the checker computes are zero, and the block has no recursors, so the checker must have `kernel_api` set (see `rulean_core::tc::Checker`). A quotient declaration gives the constant `Quot` of the kind `Type`, and the checker adds the four reference constants.
pub fn declaration<H: Heap>(h: &H, st: &mut Store, decl: u64) -> Result<Decl, Fault> {
    Converter::new(h, st).declaration(decl)
}

/// The first part of the `Declaration` object at `decl` that has a metavariable or a free variable, in the order in which the C++ kernel checks the parts. The result has `FaultKind::MetaVar` or `FaultKind::FreeVar`, the `Name` object of the constant and the `Expr` object of the part. The two objects are borrowed. The C++ kernel gives `declHasMVars` if the term has a metavariable of a term or of a level, and else `declHasFVars` if the term has a free variable.
///
/// The C++ kernel checks the type of each constant of the declaration before it checks a value. For an inductive declaration, it checks the type of each inductive type before the type of a constructor. A declaration without such a part gives `None`.
pub fn decl_vars<H: Heap>(h: &H, decl: u64) -> Result<Option<(FaultKind, u64, u64)>, Fault> {
    let mut st = Store::new();
    let c = Conv::new(h, &mut st);
    for (name, e) in c.decl_parts(decl)? {
        match c.scan_vars(e)? {
            (true, _) => return Ok(Some((FaultKind::MetaVar, name, e))),
            (false, true) => return Ok(Some((FaultKind::FreeVar, name, e))),
            (false, false) => {}
        }
    }
    Ok(None)
}

/// A conversion of several objects. The objects share names, levels and expressions, so the converter keeps its tables from address to handle between the calls. The objects must stay alive while the converter exists, because the runtime can give the address of a freed object to a new object.
pub struct Converter<'a, H: Heap> {
    c: Conv<'a, H>,
}

impl<H: Heap> core::fmt::Debug for Converter<'_, H> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Converter")
            .field("names", &self.c.names.len())
            .field("levels", &self.c.levels.len())
            .field("exprs", &self.c.exprs.len())
            .finish()
    }
}

impl<'a, H: Heap> Converter<'a, H> {
    pub fn new(h: &'a H, st: &'a mut Store) -> Converter<'a, H> {
        Converter {
            c: Conv::new(h, st),
        }
    }

    /// Converts the `Declaration` object at `decl`. See `declaration`.
    pub fn declaration(&mut self, decl: u64) -> Result<Decl, Fault> {
        let d = self.c.declaration(decl)?;
        self.full(decl)?;
        Ok(d)
    }

    /// Converts the `ConstantInfo` object at `ci` into a constant of the environment of the checker. The constant is not checked. The mirror of the environment uses this for the constants that Lean has already added.
    pub fn constant(&mut self, ci: u64) -> Result<ConstInfo, Fault> {
        let k = self.c.constant(ci)?;
        self.full(ci)?;
        Ok(k)
    }

    /// Converts the `LocalContext` object at `lctx`. The result has the local declarations in the order of their index. The free variable of the declaration `i` is the free variable of the store with the level `i` and the type of the declaration. After this call, `expr` converts each `Expr.fvar` of the context to its free variable.
    ///
    /// The conversion reads the field `decls`, a `PersistentArray (Option LocalDecl)`, and skips the entries `none`. The C++ kernel finds a declaration in the field `fvarIdToDecl`, a map with the same declarations, so the conversion does not read the map.
    pub fn local_context(&mut self, lctx: u64) -> Result<Vec<Local>, Fault> {
        let locals = self.c.local_context(lctx)?;
        self.full(lctx)?;
        Ok(locals)
    }

    /// The level metavariables of the local context and the terms. After `local_context`, the conversion gives a level parameter for each level metavariable, with the name `_rulean_lmvar.N`, and the same parameter for each `Level.mvar` object of one metavariable. The result has the parameter and the first `Level.mvar` object of the metavariable. The objects are borrowed. `Encoder::with_level_mvars` writes each parameter as its object again.
    pub fn level_mvars(&self) -> Vec<(NameId, u64)> {
        self.c.lmvars.values().copied().collect()
    }

    /// Converts the `Expr` object at `e`. A free variable must be in the local context of `local_context`.
    pub fn expr(&mut self, e: u64) -> Result<ExprId, Fault> {
        let id = self.c.expr_at(e)?;
        self.full(e)?;
        Ok(id)
    }

    fn full(&self, at: u64) -> Result<(), Fault> {
        if self.c.st.is_full() {
            return Err(Fault::new(
                FaultKind::StoreFull,
                at,
                "the term store is full",
            ));
        }
        Ok(())
    }
}

/// A local declaration of a `LocalContext` in the store.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Local {
    /// The name of the `FVarId`.
    pub fvar: NameId,
    /// The name that the user sees.
    pub user_name: NameId,
    /// The binder info. A `let` declaration has the default binder info, as in Lean.
    pub info: BinderInfo,
    pub ty: ExprId,
    /// The value of a `let` declaration.
    pub value: Option<ExprId>,
    /// The free variable of the store for this declaration.
    pub e: ExprId,
}

/// The state of one conversion.
struct Conv<'a, H: Heap> {
    h: &'a H,
    st: &'a mut Store,
    names: HashMap<u64, NameId>,
    levels: HashMap<u64, LevelId>,
    exprs: HashMap<u64, ExprId>,
    /// The free variables of a local context, by the name of their `FVarId`. `None` for a kernel declaration, which cannot have free variables.
    fvars: Option<HashMap<u32, ExprId>>,
    /// The local declarations that `local_context` skips, by the name of their `FVarId`, with the fault of the declaration.
    skipped: HashMap<u32, Fault>,
    /// The level metavariables of a term, by the name of their `LMVarId`: the level parameter that stands for the metavariable and the first `Level.mvar` object. See `Converter::level_mvars`.
    lmvars: HashMap<u32, (NameId, u64)>,
}

fn bad(at: u64, msg: impl Into<String>) -> Fault {
    Fault::new(FaultKind::Malformed, at, msg)
}

fn decline(at: u64, msg: impl Into<String>) -> Fault {
    Fault::new(FaultKind::Decline, at, msg)
}

/// The `BinderInfo` with the value `v`, in the object at `at`.
fn binder_info(at: u64, v: u8) -> Result<BinderInfo, Fault> {
    Ok(match v {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        v => return Err(bad(at, format!("a binder has the binder info {v}"))),
    })
}

/// The first part of the name of the level parameter that stands for a level metavariable of a term. Lean does not give this name to a level parameter.
const LMVAR_PREFIX: &[u8] = b"_rulean_lmvar";

/// The largest depth of the tree of a `PersistentArray`. The tree has 32 children for each node, so this depth is more than the depth of any array that fits in memory.
const MAX_PARRAY_DEPTH: u32 = 16;

impl<'a, H: Heap> Conv<'a, H> {
    fn new(h: &'a H, st: &'a mut Store) -> Conv<'a, H> {
        Conv {
            h,
            st,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            fvars: None,
            skipped: HashMap::new(),
            lmvars: HashMap::new(),
        }
    }

    // The words and the bytes of objects.

    fn bytes<const N: usize>(&self, addr: u64) -> Result<[u8; N], Fault> {
        let mut b = [0u8; N];
        if self.h.read(addr, &mut b) {
            Ok(b)
        } else {
            Err(bad(addr, "the address cannot be read"))
        }
    }

    fn word(&self, addr: u64) -> Result<u64, Fault> {
        Ok(u64::from_le_bytes(self.bytes::<8>(addr)?))
    }

    /// The tag and the value of `m_other` of the object at `p`.
    fn head(&self, p: u64) -> Result<(u8, u8), Fault> {
        let b = self.bytes::<8>(p)?;
        Ok((b[7], b[6]))
    }

    /// The address of object field `i` of the object at `p`.
    fn slot(p: u64, i: u64) -> u64 {
        p.wrapping_add(WORD * (1 + i))
    }

    /// Object field `i` of the constructor object at `p`.
    fn field(&self, p: u64, i: u64) -> Result<Field, Fault> {
        let w = self.word(Self::slot(p, i))?;
        if w & 1 == 1 {
            Ok(Field::Scalar(w >> 1))
        } else if w == 0 || !w.is_multiple_of(WORD) {
            Err(bad(
                p,
                format!("field {i} is not a scalar and not an object address"),
            ))
        } else {
            Ok(Field::Object(w))
        }
    }

    /// Object field `i` of `p`, which must be an object.
    fn object(&self, p: u64, i: u64) -> Result<u64, Fault> {
        match self.field(p, i)? {
            Field::Object(q) => Ok(q),
            Field::Scalar(_) => Err(bad(
                p,
                format!("field {i} is a scalar where an object is expected"),
            )),
        }
    }

    /// Checks that the object at `p` is a constructor object with a tag in `tags` and `objs` object fields, and gives the tag.
    fn ctor(
        &self,
        p: u64,
        tags: core::ops::RangeInclusive<u8>,
        objs: u8,
        what: &str,
    ) -> Result<u8, Fault> {
        let (t, other) = self.head(p)?;
        if !tags.contains(&t) || t > tag::MAX_CTOR {
            return Err(bad(p, format!("the object is not a {what}: tag {t}")));
        }
        if other != objs {
            return Err(bad(
                p,
                format!("a {what} has {other} object fields, not {objs}"),
            ));
        }
        Ok(t)
    }

    /// Scalar byte `k` of the constructor object at `p` with `objs` object fields.
    fn u8_at(&self, p: u64, objs: u64, k: u64) -> Result<u8, Fault> {
        Ok(self.bytes::<1>(Self::slot(p, objs).wrapping_add(k))?[0])
    }

    fn u32_at(&self, p: u64, objs: u64, k: u64) -> Result<u32, Fault> {
        Ok(u32::from_le_bytes(
            self.bytes::<4>(Self::slot(p, objs).wrapping_add(k))?,
        ))
    }

    fn bool_at(&self, p: u64, objs: u64, k: u64) -> Result<bool, Fault> {
        match self.u8_at(p, objs, k)? {
            0 => Ok(false),
            1 => Ok(true),
            v => Err(bad(p, format!("a boolean field has the value {v}"))),
        }
    }

    fn unsafe_flag(&self, p: u64, objs: u64, k: u64) -> Result<Safety, Fault> {
        Ok(if self.bool_at(p, objs, k)? {
            Safety::Unsafe
        } else {
            Safety::Safe
        })
    }

    // Strings and natural numbers.

    /// The bytes of the string that field `i` of `p` points to.
    fn string(&self, p: u64, i: u64) -> Result<Vec<u8>, Fault> {
        let s = self.object(p, i)?;
        let (t, _) = self.head(s)?;
        if t != tag::STRING {
            return Err(bad(s, "the object is not a string"));
        }
        let size = self.word(s.wrapping_add(WORD))?;
        let chars = self.word(s.wrapping_add(3 * WORD))?;
        if size == 0 {
            return Err(bad(s, "a string has the size 0"));
        }
        if size > MAX_NAT_BITS / 8 {
            return Err(decline(s, "a string is too large"));
        }
        let mut b = vec![0u8; size as usize];
        if !self.h.read(s.wrapping_add(4 * WORD), &mut b) {
            return Err(bad(s, "the bytes of a string cannot be read"));
        }
        if b.pop() != Some(0) {
            return Err(bad(s, "a string has no zero byte at its end"));
        }
        match core::str::from_utf8(&b) {
            Ok(t) if t.chars().count() as u64 == chars => Ok(b),
            Ok(_) => Err(bad(s, "a string has a wrong character count")),
            Err(_) => Err(bad(s, "a string is not UTF-8")),
        }
    }

    /// The natural number of field `i` of `p`: a boxed scalar or a big number in the GMP encoding. In the runtime, the limbs of a big number are in a separate buffer.
    fn nat(&self, p: u64, i: u64) -> Result<Nat, Fault> {
        let m = match self.field(p, i)? {
            Field::Scalar(n) => return Ok(Nat::from_u64(n)),
            Field::Object(m) => m,
        };
        let (t, _) = self.head(m)?;
        if t != tag::MPZ {
            return Err(bad(m, "the object is not a natural number"));
        }
        let b = self.bytes::<8>(m.wrapping_add(WORD))?;
        let alloc = i32::from_le_bytes([b[0], b[1], b[2], b[3]]);
        let size = i32::from_le_bytes([b[4], b[5], b[6], b[7]]);
        let d = self.word(m.wrapping_add(2 * WORD))?;
        if size <= 0 || alloc < size {
            return Err(bad(m, "a big number has a bad GMP header"));
        }
        let n = size as u64;
        if n > MAX_NAT_BITS / 64 {
            return Err(decline(m, "a natural number is too large"));
        }
        let mut v = Vec::with_capacity(n as usize);
        for k in 0..n {
            v.push(self.word(d.wrapping_add(k * WORD))?);
        }
        let top = v[v.len() - 1];
        if top == 0 {
            return Err(bad(m, "a big number has a leading zero limb"));
        }
        if v.len() == 1 && top <= MAX_SMALL_NAT {
            return Err(bad(m, "a big number is small enough to be a boxed scalar"));
        }
        Ok(Nat::from_limbs(v))
    }

    /// The natural number of field `i` of `p` as a `u32`. A larger value is a decline.
    fn small(&self, p: u64, i: u64) -> Result<u32, Fault> {
        let n = self.nat(p, i)?;
        match n.to_u64().and_then(|x| u32::try_from(x).ok()) {
            Some(x) => Ok(x),
            None => Err(decline(p, "a count or an index does not fit in 32 bits")),
        }
    }

    // Lists.

    /// The heads of the list that field `i` of `p` points to.
    fn list(&self, p: u64, i: u64) -> Result<Vec<Field>, Fault> {
        let mut out = Vec::new();
        let mut cur = self.field(p, i)?;
        loop {
            match cur {
                Field::Scalar(0) => return Ok(out),
                Field::Scalar(_) => {
                    return Err(bad(
                        p,
                        "a list ends with a scalar that is not the empty list",
                    ));
                }
                Field::Object(c) => {
                    self.ctor(c, 1..=1, 2, "list cell")?;
                    out.push(self.field(c, 0)?);
                    cur = self.field(c, 1)?;
                }
            }
        }
    }

    /// The objects of the list that field `i` of `p` points to.
    fn list_objects(&self, p: u64, i: u64) -> Result<Vec<u64>, Fault> {
        let mut out = Vec::new();
        for f in self.list(p, i)? {
            match f {
                Field::Object(q) => out.push(q),
                Field::Scalar(_) => {
                    return Err(bad(p, "a list has a scalar where an object is expected"));
                }
            }
        }
        Ok(out)
    }

    // Names.

    fn name(&mut self, p: u64, i: u64) -> Result<NameId, Fault> {
        let f = self.field(p, i)?;
        self.name_field(p, f)
    }

    fn name_field(&mut self, from: u64, f: Field) -> Result<NameId, Fault> {
        let mut cur = match f {
            Field::Scalar(0) => return Ok(self.st.anon()),
            Field::Scalar(_) => {
                return Err(bad(
                    from,
                    "a name is a scalar that is not the anonymous name",
                ));
            }
            Field::Object(q) => q,
        };
        // Walk down the prefixes to a name that is known, then make the names from the bottom up.
        let mut chain = Vec::new();
        let mut id = self.st.anon();
        loop {
            if let Some(&k) = self.names.get(&cur) {
                id = k;
                break;
            }
            self.ctor(cur, 1..=2, 2, "name")?;
            chain.push(cur);
            match self.field(cur, 0)? {
                Field::Scalar(0) => break,
                Field::Scalar(_) => {
                    return Err(bad(
                        cur,
                        "a name prefix is a scalar that is not the anonymous name",
                    ));
                }
                Field::Object(q) => cur = q,
            }
        }
        while let Some(q) = chain.pop() {
            let (t, _) = self.head(q)?;
            id = if t == 1 {
                let s = self.string(q, 1)?;
                self.st.name_str_bytes(id, &s)
            } else {
                let n = self.nat(q, 1)?;
                match n.to_u64() {
                    Some(x) => self.st.name_num(id, x),
                    None => return Err(decline(q, "a number in a name does not fit in 64 bits")),
                }
            };
            self.names.insert(q, id);
        }
        Ok(id)
    }

    fn names(&mut self, p: u64, i: u64) -> Result<Vec<NameId>, Fault> {
        let fs = self.list(p, i)?;
        let mut out = Vec::with_capacity(fs.len());
        for f in fs {
            out.push(self.name_field(p, f)?);
        }
        Ok(out)
    }

    // Levels.

    /// The object of a level field, or `None` for `Level.zero` as the boxed scalar 0.
    fn level_object(&self, from: u64, f: Field) -> Result<Option<u64>, Fault> {
        match f {
            Field::Scalar(0) => Ok(None),
            Field::Scalar(_) => Err(bad(from, "a level is a scalar that is not `Level.zero`")),
            Field::Object(q) => Ok(Some(q)),
        }
    }

    /// The number of object fields of the level constructor with tag `t`.
    fn level_objs(t: u8) -> u8 {
        match t {
            0 => 0,
            1 | 4 | 5 => 1,
            _ => 2,
        }
    }

    fn level_field(&mut self, from: u64, f: Field) -> Result<LevelId, Fault> {
        let Some(root) = self.level_object(from, f)? else {
            return Ok(self.st.level_zero());
        };
        let mut stack = vec![(root, false)];
        while let Some((q, ready)) = stack.pop() {
            if self.levels.contains_key(&q) {
                continue;
            }
            let (t, _) = self.head(q)?;
            self.ctor(q, 0..=5, Self::level_objs(t), "level")?;
            if t == 5 && self.fvars.is_some() {
                // A term of a term function can have a level metavariable. The C++ kernel compares it as an atom, as a level parameter. The conversion gives a new level parameter for each metavariable.
                let n = self.name(q, 0)?;
                let k = self.lmvars.len() as u64;
                let p = match self.lmvars.get(&n.0) {
                    Some(&(p, _)) => p,
                    None => {
                        let anon = self.st.anon();
                        let pre = self.st.name_str_bytes(anon, LMVAR_PREFIX);
                        let p = self.st.name_num(pre, k);
                        self.lmvars.insert(n.0, (p, q));
                        p
                    }
                };
                let id = self.st.level_param(p);
                self.levels.insert(q, id);
                continue;
            }
            if t == 5 {
                return Err(Fault::new(
                    FaultKind::MetaVar,
                    q,
                    "a level metavariable cannot be in a kernel declaration",
                ));
            }
            let kids: u64 = match t {
                1 => 1,
                2 | 3 => 2,
                _ => 0,
            };
            if !ready {
                stack.push((q, true));
                for k in 0..kids {
                    let fk = self.field(q, k)?;
                    if let Some(c) = self.level_object(q, fk)?
                        && !self.levels.contains_key(&c)
                    {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            let id = match t {
                0 => self.st.level_zero(),
                1 => {
                    let a = self.done_level(q, 0)?;
                    self.st.level_succ(a)
                }
                2 | 3 => {
                    let a = self.done_level(q, 0)?;
                    let b = self.done_level(q, 1)?;
                    if t == 2 {
                        self.st.level_max(a, b)
                    } else {
                        self.st.level_imax(a, b)
                    }
                }
                _ => {
                    let n = self.name(q, 0)?;
                    self.st.level_param(n)
                }
            };
            self.levels.insert(q, id);
        }
        match self.levels.get(&root) {
            Some(&id) => Ok(id),
            None => Err(bad(root, "a level is not converted")),
        }
    }

    fn done_level(&self, q: u64, i: u64) -> Result<LevelId, Fault> {
        let f = self.field(q, i)?;
        match self.level_object(q, f)? {
            None => Ok(self.st.level_zero()),
            Some(c) => match self.levels.get(&c) {
                Some(&id) => Ok(id),
                None => Err(bad(c, "a level is not converted")),
            },
        }
    }

    fn level_list(&mut self, p: u64, i: u64) -> Result<LevelListId, Fault> {
        let fs = self.list(p, i)?;
        let mut ls = Vec::with_capacity(fs.len());
        for f in fs {
            ls.push(self.level_field(p, f)?);
        }
        Ok(self.st.level_list(&ls))
    }

    // Local contexts.

    /// The elements of the `Array` object at `a`.
    fn array(&self, a: u64) -> Result<Vec<Field>, Fault> {
        let (t, _) = self.head(a)?;
        if t != tag::ARRAY {
            return Err(bad(a, "the object is not an array"));
        }
        let size = self.word(a.wrapping_add(WORD))?;
        let cap = self.word(a.wrapping_add(2 * WORD))?;
        if size > cap || size > u64::from(u32::MAX) {
            return Err(bad(a, "an array has a bad size"));
        }
        let mut out = Vec::with_capacity(size as usize);
        for k in 0..size {
            // The elements start after the header, the size and the capacity.
            out.push(self.field(a, 2 + k)?);
        }
        Ok(out)
    }

    /// The elements of the `PersistentArray` object at `pa`, in order: the elements of the tree, then the elements of the tail.
    fn parray(&self, pa: u64) -> Result<Vec<Field>, Fault> {
        // The object fields are `root`, `tail`, `size` and `tailOff`. `shift` is a `USize` scalar.
        self.ctor(pa, 0..=0, 4, "PersistentArray")?;
        let mut out = Vec::new();
        let mut stack = vec![(self.object(pa, 0)?, 0u32)];
        while let Some((node, depth)) = stack.pop() {
            if depth > MAX_PARRAY_DEPTH {
                return Err(bad(node, "a persistent array is too deep"));
            }
            // `node` has the tag 0 and an array of nodes. `leaf` has the tag 1 and an array of elements.
            let t = self.ctor(node, 0..=1, 1, "PersistentArrayNode")?;
            let items = self.array(self.object(node, 0)?)?;
            if t == 1 {
                out.extend(items);
                continue;
            }
            for f in items.into_iter().rev() {
                match f {
                    Field::Object(c) => stack.push((c, depth + 1)),
                    Field::Scalar(_) => {
                        return Err(bad(node, "a persistent array node has a scalar child"));
                    }
                }
            }
        }
        out.extend(self.array(self.object(pa, 1)?)?);
        let size = self.nat(pa, 2)?;
        if size.to_u64() != Some(out.len() as u64) {
            return Err(bad(pa, "a persistent array has a wrong size"));
        }
        Ok(out)
    }

    fn local_context(&mut self, lctx: u64) -> Result<Vec<Local>, Fault> {
        // The object fields are `fvarIdToDecl`, `decls` and `auxDeclToFullName`.
        self.ctor(lctx, 0..=0, 3, "LocalContext")?;
        let decls = self.parray(self.object(lctx, 1)?)?;
        self.fvars = Some(HashMap::new());
        let mut out: Vec<Local> = Vec::new();
        for f in decls {
            // `Option.none` is the boxed scalar 0, and `Option.some` has the tag 1.
            let o = match f {
                Field::Scalar(0) => continue,
                Field::Scalar(_) => return Err(bad(lctx, "a local declaration is a scalar")),
                Field::Object(o) => o,
            };
            self.ctor(o, 1..=1, 1, "Option")?;
            let d = self.object(o, 0)?;
            // `cdecl` has the tag 0 and the object fields `index`, `fvarId`, `userName` and `type`, then the scalars `bi` and `kind`. `ldecl` has the tag 1 and the object field `value` after `type`, then the scalars `nonDep` and `kind`.
            let (t, _) = self.head(d)?;
            let objs = if t == 1 { 5 } else { 4 };
            self.ctor(d, 0..=1, objs, "LocalDecl")?;
            let fvar = self.name(d, 1)?;
            let user_name = self.name(d, 2)?;
            let info = if t == 0 {
                binder_info(d, self.u8_at(d, 4, 0)?)?
            } else {
                self.bool_at(d, 5, 0)?;
                BinderInfo::Default
            };
            // The C++ kernel reads a local declaration only when a term refers to it. The elaborator gives local declarations with metavariables, for example the auxiliary declaration of the definition that it elaborates. The conversion skips such a declaration and a declaration that refers to a skipped declaration. A term that refers to a skipped declaration gets the fault of the declaration.
            let parts = self.expr(d, 3).and_then(|ty| {
                let value = if t == 1 { Some(self.expr(d, 4)?) } else { None };
                Ok((ty, value))
            });
            let (ty, value) = match parts {
                Ok(x) => x,
                Err(f) if matches!(f.kind, FaultKind::MetaVar | FaultKind::FreeVar) => {
                    self.skipped.insert(fvar.0, f);
                    continue;
                }
                Err(f) => return Err(f),
            };
            let level = u32::try_from(out.len())
                .map_err(|_| decline(lctx, "a local context is too large"))?;
            let e = self.st.mk_fvar(level, ty);
            let map = self.fvars.get_or_insert_default();
            if map.insert(fvar.0, e).is_some() || self.skipped.contains_key(&fvar.0) {
                return Err(bad(d, "two local declarations have the same free variable"));
            }
            out.push(Local {
                fvar,
                user_name,
                info,
                ty,
                value,
                e,
            });
        }
        Ok(out)
    }

    // Expressions.

    /// The object fields of the expression constructor with tag `t`, and the fields that are expressions.
    fn expr_shape(t: u8) -> (u8, &'static [u64]) {
        match t {
            0..=3 | 9 => (1, &[]),
            4 => (2, &[]),
            5 => (2, &[0, 1]),
            6 | 7 => (3, &[1, 2]),
            8 => (4, &[1, 2, 3]),
            10 => (2, &[1]),
            _ => (3, &[2]),
        }
    }

    fn expr(&mut self, p: u64, i: u64) -> Result<ExprId, Fault> {
        let root = self.object(p, i)?;
        self.expr_at(root)
    }

    /// The expression at the address `root`.
    fn expr_at(&mut self, root: u64) -> Result<ExprId, Fault> {
        let mut stack = vec![(root, false)];
        while let Some((q, ready)) = stack.pop() {
            if self.exprs.contains_key(&q) {
                continue;
            }
            let (t, _) = self.head(q)?;
            if t > 11 {
                return Err(bad(q, format!("the object is not an expression: tag {t}")));
            }
            let (objs, kids) = Self::expr_shape(t);
            self.ctor(q, t..=t, objs, "expression")?;
            if t == 1 {
                // `Expr.fvar` has the `FVarId` in field 0, and an `FVarId` is its name.
                let n = self.name(q, 0)?;
                let found = self.fvars.as_ref().map(|m| m.get(&n.0).copied());
                match found {
                    Some(Some(id)) => {
                        self.exprs.insert(q, id);
                        continue;
                    }
                    Some(None) => {
                        if let Some(f) = self.skipped.get(&n.0) {
                            return Err(f.clone());
                        }
                        return Err(Fault::new(FaultKind::FreeVar, q, "unknown free variable"));
                    }
                    None => {
                        return Err(Fault::new(
                            FaultKind::FreeVar,
                            q,
                            "a free variable cannot be in a kernel declaration",
                        ));
                    }
                }
            }
            if t == 2 {
                return Err(Fault::new(
                    FaultKind::MetaVar,
                    q,
                    "a metavariable cannot be in a kernel declaration",
                ));
            }
            if !ready {
                stack.push((q, true));
                for &k in kids {
                    let c = self.object(q, k)?;
                    if !self.exprs.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            let id = self.expr_node(q, t)?;
            self.exprs.insert(q, id);
        }
        match self.exprs.get(&root) {
            Some(&id) => Ok(id),
            None => Err(bad(root, "an expression is not converted")),
        }
    }

    fn done_expr(&self, q: u64, i: u64) -> Result<ExprId, Fault> {
        let c = self.object(q, i)?;
        match self.exprs.get(&c) {
            Some(&id) => Ok(id),
            None => Err(bad(c, "an expression is not converted")),
        }
    }

    /// Makes the node of the expression at `q` with tag `t`. The expressions of its fields are converted.
    fn expr_node(&mut self, q: u64, t: u8) -> Result<ExprId, Fault> {
        Ok(match t {
            0 => {
                let i = self.small(q, 0)?;
                self.st.mk_bvar(i)
            }
            3 => {
                let f = self.field(q, 0)?;
                let l = self.level_field(q, f)?;
                self.st.mk_sort(l)
            }
            4 => {
                let n = self.name(q, 0)?;
                let ls = self.level_list(q, 1)?;
                self.st.mk_const(n, ls)
            }
            5 => {
                let f = self.done_expr(q, 0)?;
                let a = self.done_expr(q, 1)?;
                self.st.mk_app(f, a)
            }
            6 | 7 => {
                let n = self.name(q, 0)?;
                let dom = self.done_expr(q, 1)?;
                let body = self.done_expr(q, 2)?;
                // The scalar area starts with `Expr.Data` (8 bytes), and `binderInfo` follows it.
                let info = binder_info(q, self.u8_at(q, 3, 8)?)?;
                if t == 6 {
                    self.st.mk_lam(n, info, dom, body)
                } else {
                    self.st.mk_pi(n, info, dom, body)
                }
            }
            8 => {
                let n = self.name(q, 0)?;
                let ty = self.done_expr(q, 1)?;
                let v = self.done_expr(q, 2)?;
                let body = self.done_expr(q, 3)?;
                // `nonDep` has no effect on checking (spec 07.1.2), but it must be a boolean.
                self.bool_at(q, 4, 8)?;
                self.st.mk_let(n, ty, v, body)
            }
            9 => {
                let lit = self.object(q, 0)?;
                if self.ctor(lit, 0..=1, 1, "literal")? == 0 {
                    let n = self.nat(lit, 0)?;
                    if n.bits() > MAX_NAT_BITS {
                        return Err(decline(lit, "a natural number is too large"));
                    }
                    let id = self.st.intern_nat(n);
                    self.st.mk_nat_lit(id)
                } else {
                    let s = self.string(lit, 0)?;
                    let id = self.st.intern_str(&s);
                    self.st.mk_str_lit(id)
                }
            }
            10 => {
                // `mdata`: the kernel ignores the data, so the conversion checks only that the field is a valid word, and takes the inner expression. `KVMap` is a structure with one field, so its value is the list of entries, and the empty list is the boxed scalar 0.
                self.field(q, 0)?;
                self.done_expr(q, 1)?
            }
            _ => {
                let n = self.name(q, 0)?;
                let i = self.small(q, 1)?;
                let e = self.done_expr(q, 2)?;
                self.st.mk_proj(n, i, e)
            }
        })
    }

    // Declarations.

    /// The `ConstantVal` that field 0 of `v` points to: the name, the level parameters and the type.
    fn cval(&mut self, v: u64) -> Result<(NameId, Vec<NameId>, ExprId), Fault> {
        let c = self.object(v, 0)?;
        self.ctor(c, 0..=0, 3, "ConstantVal")?;
        let name = self.name(c, 0)?;
        let lparams = self.names(c, 1)?;
        let ty = self.expr(c, 2)?;
        Ok((name, lparams, ty))
    }

    fn hints(&self, v: u64, i: u64) -> Result<Hints, Fault> {
        match self.field(v, i)? {
            Field::Scalar(0) => Ok(Hints::Opaque),
            Field::Scalar(1) => Ok(Hints::Abbrev),
            Field::Scalar(s) => Err(bad(v, format!("the reducibility hints have the value {s}"))),
            Field::Object(q) => {
                self.ctor(q, 2..=2, 0, "ReducibilityHints")?;
                Ok(Hints::Regular(self.u32_at(q, 0, 0)?))
            }
        }
    }

    /// The `DefinitionVal` at `v`.
    fn definition(&mut self, v: u64) -> Result<Defn, Fault> {
        self.ctor(v, 0..=0, 4, "DefinitionVal")?;
        let (name, lparams, ty) = self.cval(v)?;
        let value = self.expr(v, 1)?;
        let hints = self.hints(v, 2)?;
        let safety = match self.u8_at(v, 4, 0)? {
            0 => Safety::Unsafe,
            1 => Safety::Safe,
            2 => Safety::Partial,
            s => return Err(bad(v, format!("a definition has the safety {s}"))),
        };
        let all = self.names(v, 3)?;
        Ok(Defn {
            name,
            lparams,
            ty,
            value,
            hints,
            safety,
            all,
        })
    }

    fn declaration(&mut self, d: u64) -> Result<Decl, Fault> {
        let p = match self.field_of_root(d)? {
            Field::Scalar(4) => return Ok(self.quot()),
            Field::Scalar(s) => return Err(bad(d, format!("a declaration is the scalar {s}"))),
            Field::Object(p) => p,
        };
        let (t, _) = self.head(p)?;
        if t == 6 {
            return self.inductive(p);
        }
        self.ctor(p, 0..=5, 1, "declaration")?;
        let v = self.object(p, 0)?;
        Ok(match t {
            0 => {
                self.ctor(v, 0..=0, 1, "AxiomVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let safety = self.unsafe_flag(v, 1, 0)?;
                Decl::Axiom(Axiom {
                    name,
                    lparams,
                    ty,
                    safety,
                })
            }
            1 => Decl::Defn(self.definition(v)?),
            2 => {
                self.ctor(v, 0..=0, 3, "TheoremVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let value = self.expr(v, 1)?;
                let all = self.names(v, 2)?;
                Decl::Thm(Thm {
                    name,
                    lparams,
                    ty,
                    value,
                    all,
                })
            }
            3 => {
                self.ctor(v, 0..=0, 3, "OpaqueVal")?;
                let (name, lparams, ty) = self.cval(v)?;
                let value = self.expr(v, 1)?;
                let safety = self.unsafe_flag(v, 3, 0)?;
                let all = self.names(v, 2)?;
                Decl::Opaque(Opaque {
                    name,
                    lparams,
                    ty,
                    value,
                    safety,
                    all,
                })
            }
            4 => return Err(bad(p, "`quotDecl` is an object and not the boxed scalar 4")),
            _ => {
                // `mutualDefnDecl`: field 0 is the list of definitions, not one value.
                let mut ds = Vec::new();
                for q in self.list_objects(p, 0)? {
                    ds.push(self.definition(q)?);
                }
                Decl::Mutual(ds)
            }
        })
    }

    /// The `ConstantInfo` at `ci`.
    fn constant(&mut self, ci: u64) -> Result<ConstInfo, Fault> {
        let p = match self.field_of_root(ci)? {
            Field::Object(p) => p,
            Field::Scalar(s) => return Err(bad(ci, format!("a constant is the scalar {s}"))),
        };
        let t = self.ctor(p, 0..=7, 1, "ConstantInfo")?;
        let v = self.object(p, 0)?;
        // The number of object fields of the value of each constructor.
        let (objs, what) = match t {
            0 => (1, "AxiomVal"),
            1 => (4, "DefinitionVal"),
            2 => (3, "TheoremVal"),
            3 => (3, "OpaqueVal"),
            4 => (1, "QuotVal"),
            5 => (6, "InductiveVal"),
            6 => (5, "ConstructorVal"),
            _ => (7, "RecursorVal"),
        };
        self.ctor(v, 0..=0, objs, what)?;
        let (name, lparams, ty) = self.cval(v)?;
        let o = u64::from(objs);
        let (safety, kind) = match t {
            0 => (self.unsafe_flag(v, o, 0)?, ConstKind::Axiom),
            1 => {
                let d = self.definition(v)?;
                (
                    d.safety,
                    ConstKind::Defn {
                        value: d.value,
                        hints: d.hints,
                    },
                )
            }
            2 => (
                Safety::Safe,
                ConstKind::Thm {
                    value: self.expr(v, 1)?,
                },
            ),
            3 => (
                self.unsafe_flag(v, o, 0)?,
                ConstKind::Opaque {
                    value: self.expr(v, 1)?,
                },
            ),
            4 => {
                let kind = match self.u8_at(v, o, 0)? {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    k => return Err(bad(v, format!("a quotient has the kind {k}"))),
                };
                (Safety::Safe, ConstKind::Quot { kind })
            }
            5 => (
                self.unsafe_flag(v, o, 1)?,
                ConstKind::Induct(InductInfo {
                    nparams: self.small(v, 1)?,
                    nindices: self.small(v, 2)?,
                    all: self.names(v, 3)?,
                    ctors: self.names(v, 4)?,
                    nnested: self.small(v, 5)?,
                    is_rec: self.bool_at(v, o, 0)?,
                    is_reflexive: self.bool_at(v, o, 2)?,
                }),
            ),
            6 => (
                self.unsafe_flag(v, o, 0)?,
                ConstKind::Ctor(CtorInfo {
                    induct: self.name(v, 1)?,
                    cidx: self.small(v, 2)?,
                    nparams: self.small(v, 3)?,
                    nfields: self.small(v, 4)?,
                }),
            ),
            _ => {
                let mut rules = Vec::new();
                for r in self.list_objects(v, 6)? {
                    self.ctor(r, 0..=0, 3, "RecursorRule")?;
                    rules.push(RuleInfo {
                        ctor: self.name(r, 0)?,
                        nfields: self.small(r, 1)?,
                        rhs: self.expr(r, 2)?,
                    });
                }
                (
                    self.unsafe_flag(v, o, 1)?,
                    ConstKind::Rec(RecInfo {
                        all: self.names(v, 1)?,
                        nparams: self.small(v, 2)?,
                        nindices: self.small(v, 3)?,
                        nmotives: self.small(v, 4)?,
                        nminors: self.small(v, 5)?,
                        rules,
                        k: self.bool_at(v, o, 0)?,
                    }),
                )
            }
        };
        Ok(ConstInfo {
            name,
            lparams,
            ty,
            safety,
            kind,
        })
    }

    /// The root word as a field. The root is a value, not a field of an object, so it is checked here.
    fn field_of_root(&self, d: u64) -> Result<Field, Fault> {
        if d & 1 == 1 {
            Ok(Field::Scalar(d >> 1))
        } else if d == 0 || !d.is_multiple_of(WORD) {
            Err(bad(
                d,
                "the declaration is not a scalar and not an object address",
            ))
        } else {
            Ok(Field::Object(d))
        }
    }

    /// The word of a field: the boxed scalar or the address.
    fn word_of(f: Field) -> u64 {
        match f {
            Field::Scalar(v) => (v << 1) | 1,
            Field::Object(o) => o,
        }
    }

    /// The `Name` word and the type of the `ConstantVal` in field 0 of `v`.
    fn cval_part(&self, v: u64) -> Result<(u64, u64), Fault> {
        let c = self.object(v, 0)?;
        self.ctor(c, 0..=0, 3, "ConstantVal")?;
        Ok((Self::word_of(self.field(c, 0)?), self.object(c, 2)?))
    }

    /// The name and the term of each part of the declaration at `d`, in the order of the checks of the C++ kernel. See `decl_vars`.
    fn decl_parts(&self, d: u64) -> Result<Vec<(u64, u64)>, Fault> {
        let Field::Object(p) = self.field_of_root(d)? else {
            return Ok(Vec::new());
        };
        let (t, _) = self.head(p)?;
        let mut types = Vec::new();
        let mut values = Vec::new();
        match t {
            0..=3 => {
                let v = self.object(p, 0)?;
                let (name, ty) = self.cval_part(v)?;
                types.push((name, ty));
                if t != 0 {
                    values.push((name, self.object(v, 1)?));
                }
            }
            5 => {
                for v in self.list_objects(p, 0)? {
                    let (name, ty) = self.cval_part(v)?;
                    types.push((name, ty));
                    values.push((name, self.object(v, 1)?));
                }
            }
            6 => {
                for q in self.list_objects(p, 2)? {
                    self.ctor(q, 0..=0, 3, "InductiveType")?;
                    types.push((Self::word_of(self.field(q, 0)?), self.object(q, 1)?));
                    for c in self.list_objects(q, 2)? {
                        self.ctor(c, 0..=0, 2, "Constructor")?;
                        values.push((Self::word_of(self.field(c, 0)?), self.object(c, 1)?));
                    }
                }
            }
            _ => return Err(bad(p, format!("a declaration has the tag {t}"))),
        }
        types.extend(values);
        Ok(types)
    }

    /// If the term at `root` has a metavariable, and if it has a free variable. The scan stops at the first metavariable.
    fn scan_vars(&self, root: u64) -> Result<(bool, bool), Fault> {
        let mut seen = HashSet::new();
        let mut levels = HashSet::new();
        let mut stack = vec![root];
        let mut free = false;
        while let Some(q) = stack.pop() {
            if !seen.insert(q) {
                continue;
            }
            let (t, _) = self.head(q)?;
            if t > 11 {
                return Err(bad(q, format!("the object is not an expression: tag {t}")));
            }
            let (objs, kids) = Self::expr_shape(t);
            self.ctor(q, t..=t, objs, "expression")?;
            let level_mvar = match t {
                1 => {
                    free = true;
                    false
                }
                2 => true,
                3 => self.level_has_mvar(self.field(q, 0)?, &mut levels)?,
                4 => {
                    let mut any = false;
                    for f in self.list(q, 1)? {
                        any = any || self.level_has_mvar(f, &mut levels)?;
                    }
                    any
                }
                _ => false,
            };
            if level_mvar {
                return Ok((true, free));
            }
            for &k in kids {
                stack.push(self.object(q, k)?);
            }
        }
        Ok((false, free))
    }

    /// If the level of the field `f` has a level metavariable. `seen` has the levels without one.
    fn level_has_mvar(&self, f: Field, seen: &mut HashSet<u64>) -> Result<bool, Fault> {
        let mut stack = vec![f];
        while let Some(f) = stack.pop() {
            let Some(q) = self.level_object(0, f)? else {
                continue;
            };
            if !seen.insert(q) {
                continue;
            }
            let (t, _) = self.head(q)?;
            if t > 5 {
                return Err(bad(q, format!("the object is not a level: tag {t}")));
            }
            self.ctor(q, t..=t, Self::level_objs(t), "level")?;
            match t {
                5 => return Ok(true),
                1 => stack.push(self.field(q, 0)?),
                2 | 3 => {
                    stack.push(self.field(q, 0)?);
                    stack.push(self.field(q, 1)?);
                }
                _ => {}
            }
        }
        Ok(false)
    }

    /// `quotDecl`. The checker adds the four reference constants, so the type is only the position of a fault.
    fn quot(&mut self) -> Decl {
        let anon = self.st.anon();
        let name = self.st.name_str_bytes(anon, b"Quot");
        let z = self.st.level_zero();
        let ty = self.st.mk_sort(z);
        Decl::Quot(Quot {
            name,
            lparams: Vec::new(),
            ty,
            kind: QuotKind::Type,
        })
    }

    /// `inductDecl lparams nparams types isUnsafe`.
    fn inductive(&mut self, p: u64) -> Result<Decl, Fault> {
        self.ctor(p, 6..=6, 3, "inductive declaration")?;
        let lparams = self.names(p, 0)?;
        let nparams = self.small(p, 1)?;
        let safety = self.unsafe_flag(p, 3, 0)?;
        let mut types = Vec::new();
        let mut ctors = Vec::new();
        let tys = self.list_objects(p, 2)?;
        let mut all = Vec::with_capacity(tys.len());
        for &q in &tys {
            self.ctor(q, 0..=0, 3, "InductiveType")?;
            all.push(self.name(q, 0)?);
        }
        for (k, &q) in tys.iter().enumerate() {
            let ty = self.expr(q, 1)?;
            let mut names = Vec::new();
            for (j, c) in self.list_objects(q, 2)?.into_iter().enumerate() {
                self.ctor(c, 0..=0, 2, "Constructor")?;
                let name = self.name(c, 0)?;
                let cty = self.expr(c, 1)?;
                names.push(name);
                ctors.push(Ctor {
                    name,
                    lparams: lparams.clone(),
                    ty: cty,
                    induct: all[k],
                    cidx: u32::try_from(j).map_err(|_| decline(c, "too many constructors"))?,
                    num_params: nparams,
                    num_fields: 0,
                    safety,
                });
            }
            types.push(InductType {
                name: all[k],
                lparams: lparams.clone(),
                ty,
                num_params: nparams,
                num_indices: 0,
                all: all.clone(),
                ctors: names,
                num_nested: 0,
                is_rec: false,
                is_reflexive: false,
                safety,
            });
        }
        Ok(Decl::Induct(Induct {
            types,
            ctors,
            recs: Vec::new(),
        }))
    }
}
