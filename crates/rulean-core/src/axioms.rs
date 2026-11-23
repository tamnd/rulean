//! The axioms that each constant depends on (spec 09.4, and T4 of spec 10.1).
//!
//! The sets follow `#print axioms` of the official `CollectAxioms`. An axiom depends on itself, and its type is not visited. A definition, a theorem and an opaque constant depend on the axioms of the constants in their type and their value. A constructor and a recursor depend on the axioms of the constants in their type. An inductive type depends on the axioms of the constants in its type and on those of its constructors. A quotient constant depends on no axiom.
//!
//! The checker adds the declarations in input order, so the constants that a new constant uses are already in the environment, except the other members of the same inductive group. `update` computes the sets of the new constants from the sets of the old ones, and then joins the sets of the new constants that use each other until no set changes.

use alloc::vec::Vec;
use rulean_store::ids::{low, raw};
use rulean_store::{Expr, ExprId, NameId, Store};

use crate::env::{ConstKind, Env};
use crate::memo::Memo;

/// The axiom sets of the constants of an environment.
///
/// Each set is a list of names with no duplicates, sorted by handle. Set 0 is the empty set. Two constants with the same set often share one entry, because the union of a set with a subset of it is the first set.
#[derive(Clone, Debug)]
pub struct Axioms {
    sets: Vec<Vec<NameId>>,
    /// The set of each slot of the environment. Entry 0 is not used, because slot 0 means "no constant".
    of_slot: Vec<u32>,
    /// The union of two sets, at key (smaller set, larger set).
    unions: Memo,
    /// The set `{a}` of the axiom `a`, at key (a, 0).
    singles: Memo,
    /// The nodes that the current walk of an expression has visited.
    seen: Memo,
}

impl Default for Axioms {
    fn default() -> Axioms {
        Axioms::new()
    }
}

impl Axioms {
    /// No constants.
    pub fn new() -> Axioms {
        let mut sets = Vec::new();
        sets.push(Vec::new());
        let mut of_slot = Vec::new();
        of_slot.push(0);
        Axioms {
            sets,
            of_slot,
            unions: Memo::new(),
            singles: Memo::new(),
            seen: Memo::new(),
        }
    }

    /// The axioms of the constant in the slot `s` of the environment, sorted by handle. A slot that `update` did not see gives the empty list.
    pub fn of_slot(&self, s: u32) -> &[NameId] {
        let i = s as usize;
        if i >= self.of_slot.len() {
            return &self.sets[0];
        }
        &self.sets[self.of_slot[i] as usize]
    }

    /// The axioms of the constant `n`, or the empty list if `n` is not in the environment.
    pub fn of_const(&self, env: &Env, n: NameId) -> &[NameId] {
        self.of_slot(env.find(n))
    }

    /// The union of the sets of all constants that `update` saw, sorted by handle.
    pub fn all(&self) -> Vec<NameId> {
        let mut acc: Vec<NameId> = Vec::new();
        let mut i = 1;
        while i < self.of_slot.len() {
            let s = self.of_slot[i] as usize;
            acc = merge(&acc, &self.sets[s]);
            i += 1;
        }
        acc
    }

    /// Computes the sets of the constants that were added to the environment after the last call. If the environment became shorter, the sets of the removed slots are removed first.
    pub fn update(&mut self, st: &Store, env: &Env) {
        let n = env.len();
        if self.of_slot.len() > n + 1 {
            self.of_slot.truncate(n + 1);
        }
        let first = self.of_slot.len() as u32;
        let mut edges: Vec<(u32, u32)> = Vec::new();
        let mut s = first;
        while (s as usize) <= n {
            let set = self.direct(st, env, s, first, &mut edges);
            self.of_slot.push(set);
            s += 1;
        }
        let mut changed = !edges.is_empty();
        while changed {
            changed = false;
            let mut i = 0;
            while i < edges.len() {
                let (a, b) = edges[i];
                let sa = self.of_slot[a as usize];
                let sb = self.of_slot[b as usize];
                let u = self.union(sa, sb);
                if u != sa {
                    self.of_slot[a as usize] = u;
                    changed = true;
                }
                i += 1;
            }
        }
    }

    /// The set of the slot `s` from the constants of the old slots. A use of a new slot, at or after `first`, adds an edge, and the join step of `update` adds its set later.
    fn direct(
        &mut self,
        st: &Store,
        env: &Env,
        s: u32,
        first: u32,
        edges: &mut Vec<(u32, u32)>,
    ) -> u32 {
        let ci = env.at(s);
        match &ci.kind {
            ConstKind::Axiom => self.single(ci.name),
            ConstKind::Quot { .. } => 0,
            ConstKind::Defn { value, .. }
            | ConstKind::Thm { value }
            | ConstKind::Opaque { value } => {
                let a = self.of_expr(st, env, ci.ty, s, first, edges);
                let b = self.of_expr(st, env, *value, s, first, edges);
                self.union(a, b)
            }
            ConstKind::Ctor(_) | ConstKind::Rec(_) => self.of_expr(st, env, ci.ty, s, first, edges),
            ConstKind::Induct(info) => {
                let mut acc = self.of_expr(st, env, ci.ty, s, first, edges);
                let mut i = 0;
                while i < info.ctors.len() {
                    let x = self.use_const(env, info.ctors[i], s, first, edges);
                    acc = self.union(acc, x);
                    i += 1;
                }
                acc
            }
        }
    }

    /// The set of a constant that the slot `s` uses. An unknown constant gives the empty set.
    fn use_const(
        &mut self,
        env: &Env,
        c: NameId,
        s: u32,
        first: u32,
        edges: &mut Vec<(u32, u32)>,
    ) -> u32 {
        let slot = env.find(c);
        if slot == 0 {
            0
        } else if slot >= first {
            if slot != s {
                edges.push((s, slot));
            }
            0
        } else {
            self.of_slot[slot as usize]
        }
    }

    /// The union of the sets of the constants in `e`. The walk visits each node of the expression once.
    fn of_expr(
        &mut self,
        st: &Store,
        env: &Env,
        e: ExprId,
        s: u32,
        first: u32,
        edges: &mut Vec<(u32, u32)>,
    ) -> u32 {
        self.seen.clear();
        let mut acc = 0;
        let mut stack: Vec<ExprId> = Vec::new();
        stack.push(e);
        while !stack.is_empty() {
            let x = stack[stack.len() - 1];
            stack.pop();
            if !self.seen.contains(x.0, 0) {
                self.seen.put(x.0, 0, 1);
                match st.node(x) {
                    Expr::Const(c, _) => {
                        let y = self.use_const(env, c, s, first, edges);
                        acc = self.union(acc, y);
                    }
                    Expr::App(f, a) => {
                        stack.push(a);
                        stack.push(f);
                    }
                    Expr::Lam(b) | Expr::Pi(b) => {
                        stack.push(b.body);
                        stack.push(b.dom);
                    }
                    Expr::Let(l) => {
                        stack.push(l.body);
                        stack.push(l.value);
                        stack.push(l.ty);
                    }
                    Expr::Proj(p) => stack.push(p.expr),
                    Expr::FVar(_, ty) => stack.push(ty),
                    Expr::BVar(_) | Expr::Sort(_) | Expr::Lit(_) => {}
                }
            }
        }
        acc
    }

    /// The set `{a}`.
    fn single(&mut self, a: NameId) -> u32 {
        if let Some(x) = self.singles.get(raw(a.0), 0) {
            return low(x);
        }
        let mut v = Vec::new();
        v.push(a);
        let id = self.sets.len() as u32;
        self.sets.push(v);
        self.singles.put(raw(a.0), 0, raw(id));
        id
    }

    /// The union of two sets. If one set has every name of the other, the result is that set.
    fn union(&mut self, a: u32, b: u32) -> u32 {
        if a == b || b == 0 {
            return a;
        }
        if a == 0 {
            return b;
        }
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };
        if let Some(x) = self.unions.get(raw(lo), raw(hi)) {
            return low(x);
        }
        let m = merge(&self.sets[a as usize], &self.sets[b as usize]);
        let r = if m.len() == self.sets[a as usize].len() {
            a
        } else if m.len() == self.sets[b as usize].len() {
            b
        } else {
            let id = self.sets.len() as u32;
            self.sets.push(m);
            id
        };
        self.unions.put(raw(lo), raw(hi), raw(r));
        r
    }
}

/// The merge of two sorted lists with no duplicates.
fn merge(x: &[NameId], y: &[NameId]) -> Vec<NameId> {
    let mut out: Vec<NameId> = Vec::with_capacity(x.len() + y.len());
    let mut i = 0;
    let mut j = 0;
    while i < x.len() || j < y.len() {
        if j >= y.len() || (i < x.len() && x[i].0 < y[j].0) {
            out.push(x[i]);
            i += 1;
        } else if i >= x.len() || y[j].0 < x[i].0 {
            out.push(y[j]);
            j += 1;
        } else {
            out.push(x[i]);
            i += 1;
            j += 1;
        }
    }
    out
}
