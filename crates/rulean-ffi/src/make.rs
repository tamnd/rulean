//! The construction of Lean objects from the store (spec 09.6.3). This is the direction from rulean to Lean: the constants that the checker adds and the terms of an error go back to Lean as objects.
//!
//! The trait `Make` has the constructors of the Lean types. `OwnedHeap` implements it with objects that it owns, and the tests read these objects back with the conversion. In a Lean process, an implementation calls the constructors that Lean exports (`lean_expr_mk_app`, `lean_level_mk_succ`, `lean_name_mk_string` and the others). These compute the cached data (`Name.hash`, `Level.Data` and `Expr.Data`) in Lean, so rulean does not compute them.
//!
//! Each constructor of `Make` consumes one reference to each object argument, as the Lean functions do, and gives one reference to the new object. The encoder keeps one reference to each object in its tables and takes a new reference with `Make::inc` each time that it gives the object to a constructor. When the encoder is dropped, it gives back the references of its tables with `Make::dec`.

use std::collections::HashMap;

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_core::expr::FAR_FVAR;
use rulean_format::{Decl, Hints, QuotKind, Safety};
use rulean_nat::Nat;
use rulean_store::{BinderInfo, Expr, ExprId, Level, LevelId, Literal, Name, NameId, Store};

use crate::heap::{OwnedHeap, boxed};
use crate::{Fault, FaultKind};

/// The largest value of a boxed natural number (`LEAN_MAX_SMALL_NAT` on a 64-bit target).
const MAX_SMALL_NAT: u64 = u64::MAX >> 1;

/// The constructors of Lean objects. Each object argument is consumed, and the result is a new reference.
pub trait Make {
    fn name_str(&mut self, pre: u64, s: u64) -> u64;
    fn name_num(&mut self, pre: u64, n: u64) -> u64;
    fn level_zero(&mut self) -> u64;
    fn level_succ(&mut self, l: u64) -> u64;
    fn level_max(&mut self, a: u64, b: u64) -> u64;
    fn level_imax(&mut self, a: u64, b: u64) -> u64;
    fn level_param(&mut self, n: u64) -> u64;
    fn expr_bvar(&mut self, idx: u64) -> u64;
    fn expr_fvar(&mut self, id: u64) -> u64;
    fn expr_sort(&mut self, l: u64) -> u64;
    fn expr_const(&mut self, n: u64, ls: u64) -> u64;
    fn expr_app(&mut self, f: u64, a: u64) -> u64;
    fn expr_lambda(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64;
    fn expr_forall(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64;
    fn expr_let(&mut self, n: u64, ty: u64, value: u64, body: u64, nondep: bool) -> u64;
    fn expr_lit(&mut self, lit: u64) -> u64;
    fn expr_proj(&mut self, n: u64, idx: u64, e: u64) -> u64;
    /// A natural number: a boxed scalar if it is small, else a big number object.
    fn nat(&mut self, n: &Nat) -> u64;
    /// A string object with the UTF-8 bytes `s`.
    fn string(&mut self, s: &[u8]) -> u64;
    /// A constructor object with the tag `t`, the object fields `objs` and the scalar bytes `scalars`.
    fn ctor(&mut self, t: u8, objs: &[u64], scalars: &[u8]) -> u64;
    /// Takes one more reference to the object `o`. A boxed scalar has no reference count.
    fn inc(&mut self, o: u64);
    /// Gives back one reference to the object `o`.
    fn dec(&mut self, o: u64);
}

/// The table key of an expression handle. The handle has 32 bits, or 64 bits with the feature `wide` of the store.
#[allow(clippy::useless_conversion)]
fn key(e: ExprId) -> u64 {
    u64::from(e.0)
}

/// The cached data of a name, a level or an expression in an `OwnedHeap`. The conversion does not read it.
const NO_DATA: [u8; 8] = [0; 8];

fn data_and(b: u8) -> [u8; 9] {
    let mut v = [0; 9];
    v[8] = b;
    v
}

impl Make for OwnedHeap {
    fn name_str(&mut self, pre: u64, s: u64) -> u64 {
        self.ctor(1, &[pre, s], &NO_DATA)
    }
    fn name_num(&mut self, pre: u64, n: u64) -> u64 {
        self.ctor(2, &[pre, n], &NO_DATA)
    }
    fn level_zero(&mut self) -> u64 {
        // The runtime makes `Level.zero` as a constructor object, because it has the field `data`.
        self.ctor(0, &[], &NO_DATA)
    }
    fn level_succ(&mut self, l: u64) -> u64 {
        self.ctor(1, &[l], &NO_DATA)
    }
    fn level_max(&mut self, a: u64, b: u64) -> u64 {
        self.ctor(2, &[a, b], &NO_DATA)
    }
    fn level_imax(&mut self, a: u64, b: u64) -> u64 {
        self.ctor(3, &[a, b], &NO_DATA)
    }
    fn level_param(&mut self, n: u64) -> u64 {
        self.ctor(4, &[n], &NO_DATA)
    }
    fn expr_bvar(&mut self, idx: u64) -> u64 {
        self.ctor(0, &[idx], &NO_DATA)
    }
    fn expr_fvar(&mut self, id: u64) -> u64 {
        self.ctor(1, &[id], &NO_DATA)
    }
    fn expr_sort(&mut self, l: u64) -> u64 {
        self.ctor(3, &[l], &NO_DATA)
    }
    fn expr_const(&mut self, n: u64, ls: u64) -> u64 {
        self.ctor(4, &[n, ls], &NO_DATA)
    }
    fn expr_app(&mut self, f: u64, a: u64) -> u64 {
        self.ctor(5, &[f, a], &NO_DATA)
    }
    fn expr_lambda(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64 {
        self.ctor(6, &[n, dom, body], &data_and(bi as u8))
    }
    fn expr_forall(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64 {
        self.ctor(7, &[n, dom, body], &data_and(bi as u8))
    }
    fn expr_let(&mut self, n: u64, ty: u64, value: u64, body: u64, nondep: bool) -> u64 {
        self.ctor(8, &[n, ty, value, body], &data_and(u8::from(nondep)))
    }
    fn expr_lit(&mut self, lit: u64) -> u64 {
        self.ctor(9, &[lit], &NO_DATA)
    }
    fn expr_proj(&mut self, n: u64, idx: u64, e: u64) -> u64 {
        self.ctor(11, &[n, idx, e], &NO_DATA)
    }
    fn nat(&mut self, n: &Nat) -> u64 {
        match n.to_u64() {
            Some(x) if x <= MAX_SMALL_NAT => boxed(x),
            _ => {
                let limbs: Vec<u64> = (0..n.limb_count()).map(|i| n.limb(i)).collect();
                self.mpz(&limbs)
            }
        }
    }
    fn string(&mut self, s: &[u8]) -> u64 {
        self.string_bytes(s)
    }
    fn ctor(&mut self, t: u8, objs: &[u64], scalars: &[u8]) -> u64 {
        OwnedHeap::ctor(self, t, objs, scalars)
    }
    fn inc(&mut self, _o: u64) {}
    fn dec(&mut self, _o: u64) {}
}

/// The encoder of the terms of a store as Lean objects. It keeps a table from handle to object for each type, so a term that occurs two times is one object. It uses an explicit stack and no recursion, so a deep term cannot overflow the thread stack.
pub struct Encoder<'a, M: Make> {
    m: &'a mut M,
    st: &'a Store,
    /// The tables are keyed by the index of the handle. An expression handle has 64 bits with the feature `wide` of the store, so its table has `u64` keys.
    names: HashMap<u32, u64>,
    levels: HashMap<u32, u64>,
    exprs: HashMap<u64, u64>,
    /// The `FVarId` name of each free variable of the store, by its level. See `with_fvars`.
    fvars: Vec<NameId>,
    /// The `FVarId` name of each far free variable of the store, by its number. See `with_far_fvars`.
    far: Vec<NameId>,
    /// The `Level.mvar` object of each level parameter that stands for a level metavariable. See `with_level_mvars`.
    lmvars: HashMap<u32, u64>,
}

impl<M: Make> core::fmt::Debug for Encoder<'_, M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Encoder")
            .field("names", &self.names.len())
            .field("levels", &self.levels.len())
            .field("exprs", &self.exprs.len())
            .finish()
    }
}

impl<M: Make> Drop for Encoder<'_, M> {
    fn drop(&mut self) {
        let all: Vec<u64> = self
            .names
            .values()
            .chain(self.levels.values())
            .chain(self.exprs.values())
            .copied()
            .collect();
        for o in all {
            self.m.dec(o);
        }
    }
}

impl<'a, M: Make> Encoder<'a, M> {
    pub fn new(m: &'a mut M, st: &'a Store) -> Encoder<'a, M> {
        Encoder {
            m,
            st,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            fvars: Vec::new(),
            far: Vec::new(),
            lmvars: HashMap::new(),
        }
    }

    /// Gives the `FVarId` name of each free variable of the store, by its level. The encoder writes the free variable of level `i` as `Expr.fvar` with the name `fvars[i]`. Without this call, a free variable is a fault.
    pub fn with_fvars(mut self, fvars: Vec<NameId>) -> Encoder<'a, M> {
        self.fvars = fvars;
        self
    }

    /// Gives the `FVarId` name of each far free variable, as `Converter::far_fvars` gives them. The encoder writes the far free variable with the number `k` as `Expr.fvar` with the name `far[k]`.
    pub fn with_far_fvars(mut self, far: Vec<NameId>) -> Encoder<'a, M> {
        self.far = far;
        self
    }

    /// The `FVarId` name of the free variable with the level `l`, if the encoder has one.
    fn fvar_name(&self, l: u32) -> Option<NameId> {
        if l >= FAR_FVAR {
            self.far.get((l - FAR_FVAR) as usize).copied()
        } else {
            self.fvars.get(l as usize).copied()
        }
    }

    /// Gives the level parameters that stand for level metavariables, with the `Level.mvar` object of each one, as `Converter::level_mvars` gives them. The encoder writes each of these parameters as a new reference to its object. The objects must stay alive while the encoder exists.
    pub fn with_level_mvars(mut self, lmvars: &[(NameId, u64)]) -> Encoder<'a, M> {
        self.lmvars = lmvars.iter().map(|&(p, o)| (p.0, o)).collect();
        self
    }

    /// A new reference to the object `o` of a table.
    fn take(&mut self, o: u64) -> u64 {
        self.m.inc(o);
        o
    }

    /// The name `n`. The result is a new reference.
    pub fn name(&mut self, n: NameId) -> u64 {
        let o = self.name_ref(n);
        self.take(o)
    }

    /// The object of `n` in the table. The table keeps the reference.
    fn name_ref(&mut self, n: NameId) -> u64 {
        // The prefixes from `n` to the first one that has an object.
        let mut chain = Vec::new();
        let mut p = n;
        let mut base = loop {
            if let Some(&o) = self.names.get(&p.0) {
                break o;
            }
            match self.st.name(p) {
                Name::Anon => break boxed(0),
                Name::Str(pre, _) | Name::Num(pre, _) => {
                    chain.push(p);
                    p = pre;
                }
            }
        };
        while let Some(q) = chain.pop() {
            let pre = self.take(base);
            base = match self.st.name(q) {
                Name::Str(_, s) => {
                    let s = self.m.string(self.st.str_bytes(s));
                    self.m.name_str(pre, s)
                }
                Name::Num(_, k) => {
                    let k = self.m.nat(&Nat::from_u64(k));
                    self.m.name_num(pre, k)
                }
                Name::Anon => pre,
            };
            self.names.insert(q.0, base);
        }
        base
    }

    /// The list of the names `ns`. The result is a new reference.
    pub fn names(&mut self, ns: &[NameId]) -> u64 {
        let mut l = boxed(0);
        for &n in ns.iter().rev() {
            let h = self.name(n);
            l = self.m.ctor(1, &[h, l], &[]);
        }
        l
    }

    /// The level `l`. The result is a new reference.
    pub fn level(&mut self, l: LevelId) -> u64 {
        let o = self.level_ref(l);
        self.take(o)
    }

    fn level_ref(&mut self, l: LevelId) -> u64 {
        let mut stack = vec![(l, false)];
        while let Some((x, done)) = stack.pop() {
            if self.levels.contains_key(&x.0) {
                continue;
            }
            let node = self.st.level(x);
            if !done {
                stack.push((x, true));
                match node {
                    Level::Succ(a) => stack.push((a, false)),
                    Level::Max(a, b) | Level::IMax(a, b) => {
                        stack.push((b, false));
                        stack.push((a, false));
                    }
                    Level::Zero | Level::Param(_) => {}
                }
                continue;
            }
            let o = match node {
                Level::Zero => self.m.level_zero(),
                Level::Succ(a) => {
                    let a = self.level_done(a);
                    self.m.level_succ(a)
                }
                Level::Max(a, b) => {
                    let a = self.level_done(a);
                    let b = self.level_done(b);
                    self.m.level_max(a, b)
                }
                Level::IMax(a, b) => {
                    let a = self.level_done(a);
                    let b = self.level_done(b);
                    self.m.level_imax(a, b)
                }
                Level::Param(n) => match self.lmvars.get(&n.0) {
                    Some(&o) => self.take(o),
                    None => {
                        let n = self.name(n);
                        self.m.level_param(n)
                    }
                },
            };
            self.levels.insert(x.0, o);
        }
        self.levels[&l.0]
    }

    /// A new reference to a level that the stack has done.
    fn level_done(&mut self, l: LevelId) -> u64 {
        let o = self.levels[&l.0];
        self.take(o)
    }

    /// The expression `e`. The result is a new reference. A free variable of the store has no Lean object, so it is a fault.
    pub fn expr(&mut self, e: ExprId) -> Result<u64, Fault> {
        let o = self.expr_ref(e)?;
        Ok(self.take(o))
    }

    fn expr_ref(&mut self, e: ExprId) -> Result<u64, Fault> {
        let mut stack = vec![(e, false)];
        while let Some((x, done)) = stack.pop() {
            if self.exprs.contains_key(&key(x)) {
                continue;
            }
            let node = self.st.node(x);
            if !done {
                stack.push((x, true));
                match node {
                    Expr::App(f, a) => {
                        stack.push((a, false));
                        stack.push((f, false));
                    }
                    Expr::Lam(b) | Expr::Pi(b) => {
                        stack.push((b.body, false));
                        stack.push((b.dom, false));
                    }
                    Expr::Let(l) => {
                        stack.push((l.body, false));
                        stack.push((l.value, false));
                        stack.push((l.ty, false));
                    }
                    Expr::Proj(p) => stack.push((p.expr, false)),
                    Expr::FVar(l, _) => {
                        if self.fvar_name(l).is_none() {
                            return Err(Fault::new(
                                FaultKind::FreeVar,
                                key(x),
                                "a free variable of the store has no Lean object",
                            ));
                        }
                    }
                    Expr::BVar(_) | Expr::Sort(_) | Expr::Const(..) | Expr::Lit(_) => {}
                }
                continue;
            }
            let o = match node {
                Expr::BVar(i) => {
                    let i = self.m.nat(&Nat::from_u64(u64::from(i)));
                    self.m.expr_bvar(i)
                }
                Expr::Sort(l) => {
                    let l = self.level(l);
                    self.m.expr_sort(l)
                }
                Expr::Const(n, ls) => {
                    let n = self.name(n);
                    let items = self.st.level_list_vec(ls);
                    let mut l = boxed(0);
                    for &x in items.iter().rev() {
                        let h = self.level(x);
                        l = self.m.ctor(1, &[h, l], &[]);
                    }
                    self.m.expr_const(n, l)
                }
                Expr::App(f, a) => {
                    let f = self.expr_done(f);
                    let a = self.expr_done(a);
                    self.m.expr_app(f, a)
                }
                Expr::Lam(b) => {
                    let n = self.name(b.name);
                    let d = self.expr_done(b.dom);
                    let body = self.expr_done(b.body);
                    self.m.expr_lambda(n, d, body, b.info)
                }
                Expr::Pi(b) => {
                    let n = self.name(b.name);
                    let d = self.expr_done(b.dom);
                    let body = self.expr_done(b.body);
                    self.m.expr_forall(n, d, body, b.info)
                }
                Expr::Let(l) => {
                    let n = self.name(l.name);
                    let t = self.expr_done(l.ty);
                    let v = self.expr_done(l.value);
                    let b = self.expr_done(l.body);
                    // The store does not keep `nonDep`, and the check does not need it (spec 07.1.2).
                    self.m.expr_let(n, t, v, b, false)
                }
                Expr::Lit(Literal::Nat(k)) => {
                    let k = self.m.nat(self.st.nat(k));
                    let lit = self.m.ctor(0, &[k], &[]);
                    self.m.expr_lit(lit)
                }
                Expr::Lit(Literal::Str(s)) => {
                    let s = self.m.string(self.st.str_bytes(s));
                    let lit = self.m.ctor(1, &[s], &[]);
                    self.m.expr_lit(lit)
                }
                Expr::Proj(p) => {
                    let n = self.name(p.struct_name);
                    let i = self.m.nat(&Nat::from_u64(u64::from(p.index)));
                    let s = self.expr_done(p.expr);
                    self.m.expr_proj(n, i, s)
                }
                Expr::FVar(l, _) => {
                    let Some(f) = self.fvar_name(l) else {
                        unreachable!("the first pass checks each free variable")
                    };
                    let n = self.name(f);
                    self.m.expr_fvar(n)
                }
            };
            self.exprs.insert(key(x), o);
        }
        Ok(self.exprs[&key(e)])
    }

    fn expr_done(&mut self, e: ExprId) -> u64 {
        let o = self.exprs[&key(e)];
        self.take(o)
    }

    /// Writes each term of `es` into the table. After this, `expr` of these terms cannot fail, so a caller that makes objects after it does not lose them on a fault.
    fn prepare(&mut self, es: &[ExprId]) -> Result<(), Fault> {
        for &e in es {
            self.expr_ref(e)?;
        }
        Ok(())
    }

    /// The `ConstantVal` of a constant: its name, its level parameters and its type.
    fn cval(&mut self, name: NameId, lparams: &[NameId], ty: ExprId) -> Result<u64, Fault> {
        let n = self.name(name);
        let l = self.names(lparams);
        let t = self.expr(ty)?;
        Ok(self.m.ctor(0, &[n, l, t], &[]))
    }

    fn hints(&mut self, h: Hints) -> u64 {
        match h {
            Hints::Opaque => boxed(0),
            Hints::Abbrev => boxed(1),
            Hints::Regular(h) => self.m.ctor(2, &[], &h.to_le_bytes()),
        }
    }

    /// The `DefinitionVal` of a definition.
    #[allow(clippy::too_many_arguments)]
    fn defn_val(
        &mut self,
        name: NameId,
        lparams: &[NameId],
        ty: ExprId,
        value: ExprId,
        hints: Hints,
        safety: Safety,
        all: &[NameId],
    ) -> Result<u64, Fault> {
        let cv = self.cval(name, lparams, ty)?;
        let value = self.expr(value)?;
        let hints = self.hints(hints);
        let all = self.names(all);
        let safety = match safety {
            Safety::Unsafe => 0,
            Safety::Safe => 1,
            Safety::Partial => 2,
        };
        Ok(self.m.ctor(0, &[cv, value, hints, all], &[safety]))
    }

    /// The `TheoremVal` of a theorem.
    fn thm_val(
        &mut self,
        name: NameId,
        lparams: &[NameId],
        ty: ExprId,
        value: ExprId,
        all: &[NameId],
    ) -> Result<u64, Fault> {
        let cv = self.cval(name, lparams, ty)?;
        let value = self.expr(value)?;
        let all = self.names(all);
        Ok(self.m.ctor(0, &[cv, value, all], &[]))
    }

    /// The `OpaqueVal` of an opaque constant.
    fn opaque_val(
        &mut self,
        name: NameId,
        lparams: &[NameId],
        ty: ExprId,
        value: ExprId,
        unsafe_: bool,
        all: &[NameId],
    ) -> Result<u64, Fault> {
        let cv = self.cval(name, lparams, ty)?;
        let value = self.expr(value)?;
        let all = self.names(all);
        Ok(self.m.ctor(0, &[cv, value, all], &[u8::from(unsafe_)]))
    }

    /// The `List` of the objects `items`. It consumes the references of `items`.
    fn list(&mut self, items: &[u64]) -> u64 {
        let mut l = boxed(0);
        for &x in items.iter().rev() {
            l = self.m.ctor(1, &[x, l], &[]);
        }
        l
    }

    /// The `ConstantInfo` object of `k`. The result is a new reference.
    ///
    /// `all` is the field `all` of a definition, a theorem or an opaque constant. The environment of the checker does not keep this field for these kinds, so the caller gives it, for example from the declaration. For the other kinds, the call does not use it.
    pub fn constant(&mut self, k: &ConstInfo, all: &[NameId]) -> Result<u64, Fault> {
        let mut es = vec![k.ty];
        match &k.kind {
            ConstKind::Defn { value, .. }
            | ConstKind::Thm { value }
            | ConstKind::Opaque { value } => es.push(*value),
            ConstKind::Rec(r) => es.extend(r.rules.iter().map(|rule| rule.rhs)),
            _ => {}
        }
        self.prepare(&es)?;
        let uns = u8::from(k.safety == Safety::Unsafe);
        let (t, v) = match &k.kind {
            ConstKind::Axiom => {
                let cv = self.cval(k.name, &k.lparams, k.ty)?;
                (0, self.m.ctor(0, &[cv], &[uns]))
            }
            ConstKind::Defn { value, hints } => (
                1,
                self.defn_val(k.name, &k.lparams, k.ty, *value, *hints, k.safety, all)?,
            ),
            ConstKind::Thm { value } => (2, self.thm_val(k.name, &k.lparams, k.ty, *value, all)?),
            ConstKind::Opaque { value } => (
                3,
                self.opaque_val(k.name, &k.lparams, k.ty, *value, uns == 1, all)?,
            ),
            ConstKind::Quot { kind } => {
                let cv = self.cval(k.name, &k.lparams, k.ty)?;
                let q = match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                };
                (4, self.m.ctor(0, &[cv], &[q]))
            }
            ConstKind::Induct(i) => {
                let cv = self.cval(k.name, &k.lparams, k.ty)?;
                let all = self.names(&i.all);
                let ctors = self.names(&i.ctors);
                let objs = [
                    cv,
                    boxed(u64::from(i.nparams)),
                    boxed(u64::from(i.nindices)),
                    all,
                    ctors,
                    boxed(u64::from(i.nnested)),
                ];
                let sc = [u8::from(i.is_rec), uns, u8::from(i.is_reflexive)];
                (5, self.m.ctor(0, &objs, &sc))
            }
            ConstKind::Ctor(c) => {
                let cv = self.cval(k.name, &k.lparams, k.ty)?;
                let induct = self.name(c.induct);
                let objs = [
                    cv,
                    induct,
                    boxed(u64::from(c.cidx)),
                    boxed(u64::from(c.nparams)),
                    boxed(u64::from(c.nfields)),
                ];
                (6, self.m.ctor(0, &objs, &[uns]))
            }
            ConstKind::Rec(r) => {
                let cv = self.cval(k.name, &k.lparams, k.ty)?;
                let all = self.names(&r.all);
                let mut rules = Vec::with_capacity(r.rules.len());
                for rule in &r.rules {
                    let c = self.name(rule.ctor);
                    let rhs = self.expr(rule.rhs)?;
                    rules.push(
                        self.m
                            .ctor(0, &[c, boxed(u64::from(rule.nfields)), rhs], &[]),
                    );
                }
                let list = self.list(&rules);
                let objs = [
                    cv,
                    all,
                    boxed(u64::from(r.nparams)),
                    boxed(u64::from(r.nindices)),
                    boxed(u64::from(r.nmotives)),
                    boxed(u64::from(r.nminors)),
                    list,
                ];
                (7, self.m.ctor(0, &objs, &[u8::from(r.k), uns]))
            }
        };
        Ok(self.m.ctor(t, &[v], &[]))
    }

    /// The `Declaration` object of `d`. The result is a new reference.
    ///
    /// A `quotDecl` is the boxed scalar 4. An inductive block gives an `inductDecl` with its types and their constructors, and without its recursors, because the kernel makes them. The constructors of a type are the constructors of the block with that type in their field `induct`, in the order of `cidx`. The level parameters, the number of parameters and the safety of the block are those of its first type.
    pub fn declaration(&mut self, d: &Decl) -> Result<u64, Fault> {
        let es: Vec<ExprId> = match d {
            Decl::Axiom(a) => vec![a.ty],
            Decl::Defn(x) => vec![x.ty, x.value],
            Decl::Thm(x) => vec![x.ty, x.value],
            Decl::Opaque(x) => vec![x.ty, x.value],
            Decl::Quot(_) => Vec::new(),
            Decl::Mutual(ds) => ds.iter().flat_map(|x| [x.ty, x.value]).collect(),
            Decl::Induct(b) => b
                .types
                .iter()
                .map(|t| t.ty)
                .chain(b.ctors.iter().map(|c| c.ty))
                .collect(),
        };
        self.prepare(&es)?;
        Ok(match d {
            Decl::Axiom(a) => {
                let cv = self.cval(a.name, &a.lparams, a.ty)?;
                let v = self
                    .m
                    .ctor(0, &[cv], &[u8::from(a.safety == Safety::Unsafe)]);
                self.m.ctor(0, &[v], &[])
            }
            Decl::Defn(x) => {
                let v =
                    self.defn_val(x.name, &x.lparams, x.ty, x.value, x.hints, x.safety, &x.all)?;
                self.m.ctor(1, &[v], &[])
            }
            Decl::Thm(x) => {
                let v = self.thm_val(x.name, &x.lparams, x.ty, x.value, &x.all)?;
                self.m.ctor(2, &[v], &[])
            }
            Decl::Opaque(x) => {
                let v = self.opaque_val(
                    x.name,
                    &x.lparams,
                    x.ty,
                    x.value,
                    x.safety == Safety::Unsafe,
                    &x.all,
                )?;
                self.m.ctor(3, &[v], &[])
            }
            Decl::Quot(_) => boxed(4),
            Decl::Mutual(ds) => {
                let mut vals = Vec::with_capacity(ds.len());
                for x in ds {
                    vals.push(
                        self.defn_val(
                            x.name, &x.lparams, x.ty, x.value, x.hints, x.safety, &x.all,
                        )?,
                    );
                }
                let l = self.list(&vals);
                self.m.ctor(5, &[l], &[])
            }
            Decl::Induct(b) => {
                let first = b.types.first();
                let lps = self.names(first.map_or(&[][..], |t| &t.lparams[..]));
                let nparams = boxed(first.map_or(0, |t| u64::from(t.num_params)));
                let uns = u8::from(first.is_some_and(|t| t.safety == Safety::Unsafe));
                let mut types = Vec::with_capacity(b.types.len());
                for t in &b.types {
                    let mut cs: Vec<_> = b.ctors.iter().filter(|c| c.induct == t.name).collect();
                    cs.sort_by_key(|c| c.cidx);
                    let mut objs = Vec::with_capacity(cs.len());
                    for c in cs {
                        let n = self.name(c.name);
                        let ty = self.expr(c.ty)?;
                        objs.push(self.m.ctor(0, &[n, ty], &[]));
                    }
                    let ctors = self.list(&objs);
                    let n = self.name(t.name);
                    let ty = self.expr(t.ty)?;
                    types.push(self.m.ctor(0, &[n, ty, ctors], &[]));
                }
                let types = self.list(&types);
                self.m.ctor(6, &[lps, nparams, types], &[uns])
            }
        })
    }
}
