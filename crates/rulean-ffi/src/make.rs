//! The construction of Lean objects from the store (spec 09.6.3). This is the direction from rulean to Lean: the constants that the checker adds and the terms of an error go back to Lean as objects.
//!
//! The trait `Make` has the constructors of the Lean types. `OwnedHeap` implements it with objects that it owns, and the tests read these objects back with the conversion. In a Lean process, an implementation calls the constructors that Lean exports (`lean_expr_mk_app`, `lean_level_mk_succ`, `lean_name_mk_string` and the others). These compute the cached data (`Name.hash`, `Level.Data` and `Expr.Data`) in Lean, so rulean does not compute them.
//!
//! Each constructor of `Make` consumes one reference to each object argument, as the Lean functions do, and gives one reference to the new object. The encoder keeps one reference to each object in its tables and takes a new reference with `Make::inc` each time that it gives the object to a constructor. When the encoder is dropped, it gives back the references of its tables with `Make::dec`.

use std::collections::HashMap;

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_format::{Hints, QuotKind, Safety};
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
        }
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
                Level::Param(n) => {
                    let n = self.name(n);
                    self.m.level_param(n)
                }
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
                    Expr::FVar(..) => {
                        return Err(Fault::new(
                            FaultKind::FreeVar,
                            key(x),
                            "a free variable of the store has no Lean object",
                        ));
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
                Expr::FVar(..) => unreachable!("the first visit gives the fault"),
            };
            self.exprs.insert(key(x), o);
        }
        Ok(self.exprs[&key(e)])
    }

    fn expr_done(&mut self, e: ExprId) -> u64 {
        let o = self.exprs[&key(e)];
        self.take(o)
    }

    fn cval(&mut self, k: &ConstInfo) -> Result<u64, Fault> {
        let n = self.name(k.name);
        let l = self.names(&k.lparams);
        let t = self.expr(k.ty)?;
        Ok(self.m.ctor(0, &[n, l, t], &[]))
    }

    /// The `ConstantInfo` object of `k`. The result is a new reference.
    ///
    /// `all` is the field `all` of a definition, a theorem or an opaque constant. The environment of the checker does not keep this field for these kinds, so the caller gives it, for example from the declaration. For the other kinds, the call does not use it.
    pub fn constant(&mut self, k: &ConstInfo, all: &[NameId]) -> Result<u64, Fault> {
        let cv = self.cval(k)?;
        let uns = u8::from(k.safety == Safety::Unsafe);
        let (t, v) = match &k.kind {
            ConstKind::Axiom => (0, self.m.ctor(0, &[cv], &[uns])),
            ConstKind::Defn { value, hints } => {
                let value = self.expr(*value)?;
                let hints = match hints {
                    Hints::Opaque => boxed(0),
                    Hints::Abbrev => boxed(1),
                    Hints::Regular(h) => self.m.ctor(2, &[], &h.to_le_bytes()),
                };
                let all = self.names(all);
                let safety = match k.safety {
                    Safety::Unsafe => 0,
                    Safety::Safe => 1,
                    Safety::Partial => 2,
                };
                (1, self.m.ctor(0, &[cv, value, hints, all], &[safety]))
            }
            ConstKind::Thm { value } => {
                let value = self.expr(*value)?;
                let all = self.names(all);
                (2, self.m.ctor(0, &[cv, value, all], &[]))
            }
            ConstKind::Opaque { value } => {
                let value = self.expr(*value)?;
                let all = self.names(all);
                (3, self.m.ctor(0, &[cv, value, all], &[uns]))
            }
            ConstKind::Quot { kind } => {
                let q = match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                };
                (4, self.m.ctor(0, &[cv], &[q]))
            }
            ConstKind::Induct(i) => {
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
                let mut list = boxed(0);
                for &x in rules.iter().rev() {
                    list = self.m.ctor(1, &[x, list], &[]);
                }
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
}
