//! The session of a worker: cached judgments on frozen closed terms that stay across declarations (spec 08.4).
//!
//! The caches of `type_checker::state` are cleared at the start of each declaration. The session keeps some of their entries for the whole run. An entry has a key of frozen closed terms, a frozen value and a stamp.
//!
//! - **Closed terms only.** A key has no free variable, because the handle of a free variable names a level of the local context of one declaration.
//! - **Stamp rule.** The stamp of an entry is the length of the environment when the entry was written. Each constant that the derivation used has a smaller index. A lookup uses the entry only if the stamp is not above the cut of the current job. When the checker runs the declarations in order, the cut is the length of the environment, so each entry is valid.
//! - **Commit on accept.** The entries of a declaration are kept in a pending list. They go into the session only when the declaration is accepted. So an entry never comes from a declaration that failed, and never names a constant that was removed again.
//! - **Promotion.** A pending value in the scratch tier is copied into the frozen tier before the scratch tier is cleared (spec 04.8). The copies of one declaration make at most 10% of its scratch nodes. A value that does not fit is dropped.
//! - **Size.** The table has a fixed largest number of slots. The slots are in buckets of 4. When a full bucket gets a new entry, a CLOCK step evicts one entry of the bucket. Eviction is always safe.
//!
//! Lemma 10.4.4 `model_extend` gives the safety of the stamp rule: a judgment that holds in an environment holds in each extension of it. A defeq failure does not have this property, so the session keeps no failures.

use crate::expr;
use crate::memo::Memo;
use crate::tc::{Checker, Fault};
use alloc::vec::Vec;
use rulean_store::{Expr, ExprId, Literal, Raw, Tier, hash};

/// The tag of an `infer` entry in infer-only mode. The key is (term, 0).
pub(crate) const S_INFER: u8 = 1;
/// The tag of a `whnf_core` entry. The key is (term, 0).
pub(crate) const S_WHNF_CORE: u8 = 2;
/// The tag of a `whnf` entry. The key is (term, 0).
pub(crate) const S_WHNF: u8 = 3;
/// The tag of a defeq success. The key is the ordered pair, and the value is 1.
pub(crate) const S_SUCCESS: u8 = 4;
/// The tag of an unfolding of a constant with its level list. The key is (constant term, 0).
pub(crate) const S_UNFOLD: u8 = 5;

/// The bytes of one slot: the tag, two keys, the value, the stamp and the reference bit.
const SLOT_BYTES: usize = 6 + 3 * (Raw::BITS as usize / 8);
const WAYS: usize = 4;
const FIRST_SLOTS: usize = 1 << 12;
const SEED: u32 = 0x5345_5353;

/// The default largest size of a session, 128 MiB (spec 08.4).
pub const DEFAULT_BYTES: usize = 128 << 20;

/// The counts of a session since the checker was made.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SessionStats {
    /// The lookups that found a valid entry.
    pub hits: u64,
    /// The entries that went into the table.
    pub stores: u64,
    /// The pending entries that were dropped, because a value did not fit in the promotion budget.
    pub drops: u64,
    /// The entries that a CLOCK step removed.
    pub evictions: u64,
    /// The scratch nodes that promotion copied into the frozen tier.
    pub promoted: u64,
}

/// The session table of one worker.
#[derive(Clone, Debug)]
pub struct Session {
    /// True if the checker uses the session.
    pub on: bool,
    tag: Vec<u8>,
    ka: Vec<Raw>,
    kb: Vec<Raw>,
    val: Vec<Raw>,
    stamp: Vec<u32>,
    refd: Vec<u8>,
    len: usize,
    max_slots: usize,
    hand: usize,
    /// The entries of the current declaration: tag, key, key, value.
    pub(crate) pending: Vec<(u8, Raw, Raw, Raw)>,
    /// The counts.
    pub stats: SessionStats,
}

impl Default for Session {
    fn default() -> Session {
        Session::new(DEFAULT_BYTES)
    }
}

fn slot_hash(tag: u8, a: Raw, b: Raw) -> u32 {
    hash::finish(hash::mix_raw(
        hash::mix_raw(hash::mix(SEED, tag as u32), a),
        b,
    ))
}

/// The largest power of two of slots that fits in `bytes`, and at least one bucket.
fn slots_for(bytes: usize) -> usize {
    let mut n = WAYS;
    while n * 2 * SLOT_BYTES <= bytes {
        n *= 2;
    }
    n
}

impl Session {
    /// An empty session that uses at most `bytes` bytes for its table. It is on.
    pub fn new(bytes: usize) -> Session {
        Session {
            on: true,
            tag: Vec::new(),
            ka: Vec::new(),
            kb: Vec::new(),
            val: Vec::new(),
            stamp: Vec::new(),
            refd: Vec::new(),
            len: 0,
            max_slots: slots_for(bytes),
            hand: 0,
            pending: Vec::new(),
            stats: SessionStats::default(),
        }
    }

    /// A new empty session with the same size limit and the same `on` flag. The counts are zero.
    pub fn fresh(&self) -> Session {
        let mut s = Session::new(0);
        s.max_slots = self.max_slots;
        s.on = self.on;
        s
    }

    /// The number of entries in the table.
    pub fn len(&self) -> usize {
        self.len
    }

    /// The number of bytes of the table and the pending entries, without the allocator overhead.
    pub fn bytes(&self) -> usize {
        let raw = core::mem::size_of::<Raw>();
        self.tag.capacity()
            + (self.ka.capacity() + self.kb.capacity() + self.val.capacity()) * raw
            + self.stamp.capacity() * 4
            + self.refd.capacity()
            + self.pending.capacity() * core::mem::size_of::<(u8, Raw, Raw, Raw)>()
    }

    /// True if the table has no entry.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all entries and all pending entries. The counts stay.
    pub fn clear(&mut self) {
        let mut i = 0;
        while i < self.tag.len() {
            self.tag[i] = 0;
            i += 1;
        }
        self.len = 0;
        self.pending.truncate(0);
    }

    fn bucket(&self, tag: u8, a: Raw, b: Raw) -> usize {
        let mask = self.tag.len() - 1;
        (slot_hash(tag, a, b) as usize & mask) & !(WAYS - 1)
    }

    /// The value of an entry whose stamp is not above `cut`.
    pub fn get(&mut self, tag: u8, a: Raw, b: Raw, cut: u32) -> Option<Raw> {
        if self.len == 0 {
            return None;
        }
        let i = self.find(tag, a, b);
        if i == usize::MAX || self.stamp[i] > cut {
            return None;
        }
        self.refd[i] = 1;
        self.stats.hits += 1;
        Some(self.val[i])
    }

    /// The slot of the key, or `usize::MAX`.
    fn find(&self, tag: u8, a: Raw, b: Raw) -> usize {
        let start = self.bucket(tag, a, b);
        let mut found = usize::MAX;
        let mut i = start;
        while i < start + WAYS && found == usize::MAX {
            if self.tag[i] == tag && self.ka[i] == a && self.kb[i] == b {
                found = i;
            }
            i += 1;
        }
        found
    }

    /// Adds a pending entry of the current declaration.
    pub(crate) fn note(&mut self, tag: u8, a: Raw, b: Raw, v: Raw) {
        self.pending.push((tag, a, b, v));
    }

    /// Doubles the table, or makes the first table.
    fn grow(&mut self) {
        let n = if self.tag.is_empty() {
            let mut f = FIRST_SLOTS;
            if f > self.max_slots {
                f = self.max_slots;
            }
            f
        } else {
            self.tag.len() * 2
        };
        let old_tag = core::mem::take(&mut self.tag);
        let old_ka = core::mem::take(&mut self.ka);
        let old_kb = core::mem::take(&mut self.kb);
        let old_val = core::mem::take(&mut self.val);
        let old_stamp = core::mem::take(&mut self.stamp);
        self.tag = zeros_u8(n);
        self.ka = zeros_raw(n);
        self.kb = zeros_raw(n);
        self.val = zeros_raw(n);
        self.stamp = zeros_u32(n);
        self.refd = zeros_u8(n);
        self.len = 0;
        let mut i = 0;
        while i < old_tag.len() {
            if old_tag[i] != 0 {
                self.put(old_tag[i], old_ka[i], old_kb[i], old_val[i], old_stamp[i]);
            }
            i += 1;
        }
    }

    /// Writes an entry. An entry with the same key gets the new value and the smaller stamp. In a full bucket a CLOCK step evicts one entry.
    pub(crate) fn store(&mut self, tag: u8, a: Raw, b: Raw, v: Raw, stamp: u32) {
        if self.tag.is_empty() || (self.len * 2 > self.tag.len() && self.tag.len() < self.max_slots)
        {
            self.grow();
        }
        if self.put(tag, a, b, v, stamp) {
            self.stats.stores += 1;
        }
    }

    /// The work of `store` without the growth and the count of stores. It gives true for a new entry.
    fn put(&mut self, tag: u8, a: Raw, b: Raw, v: Raw, stamp: u32) -> bool {
        let old = self.find(tag, a, b);
        if old != usize::MAX {
            if stamp < self.stamp[old] {
                self.val[old] = v;
                self.stamp[old] = stamp;
            }
            return false;
        }
        let start = self.bucket(tag, a, b);
        let mut free = usize::MAX;
        let mut i = start;
        while i < start + WAYS {
            if self.tag[i] == 0 && free == usize::MAX {
                free = i;
            }
            i += 1;
        }
        if free == usize::MAX {
            // CLOCK: the hand goes round the bucket, clears the reference bits, and stops at the first entry without one.
            let mut k = 0;
            while free == usize::MAX {
                let j = start + (self.hand + k) % WAYS;
                if self.refd[j] == 0 {
                    free = j;
                } else {
                    self.refd[j] = 0;
                }
                k += 1;
            }
            self.hand = (self.hand + k) % WAYS;
            self.len -= 1;
            self.stats.evictions += 1;
        }
        self.tag[free] = tag;
        self.ka[free] = a;
        self.kb[free] = b;
        self.val[free] = v;
        self.stamp[free] = stamp;
        self.refd[free] = 0;
        self.len += 1;
        true
    }
}

/// A vector of `n` zeros of the handle type.
fn zeros_raw(n: usize) -> Vec<Raw> {
    let mut v: Vec<Raw> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

/// A vector of `n` zeros.
fn zeros_u32(n: usize) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

/// A vector of `n` zeros.
fn zeros_u8(n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

/// The frozen copy of a field: the field itself if it is frozen, or its copy in `map`.
fn copied(map: &Memo, y: ExprId) -> ExprId {
    if y.tier() == Tier::Frozen {
        return y;
    }
    match map.get(y.0, 0) {
        Some(r) => ExprId(r),
        None => y,
    }
}

/// The tag of a pending entry whose value is a term.
fn value_is_term(tag: u8) -> bool {
    tag != S_SUCCESS
}

impl Checker {
    /// True if `e` can be a key of the session: the session is on, and `e` is a frozen term without free variables. The session is not used with `rulean explain` and with `--confirm all`, because a hit skips the rules and the confirmation.
    #[inline]
    pub(crate) fn sess_key(&self, e: ExprId) -> bool {
        self.sess.on
            && !self.trace_on
            && !self.confirm_all
            && e.tier() == Tier::Frozen
            && !expr::has_fvar(&self.st, e)
    }

    /// The cut of the current job: the length of the environment.
    #[inline]
    pub(crate) fn sess_cut(&self) -> u32 {
        self.env.len() as u32
    }

    /// Looks up a session entry.
    #[inline]
    pub(crate) fn sess_get(&mut self, tag: u8, a: Raw, b: Raw) -> Option<Raw> {
        let cut = self.sess_cut();
        self.sess.get(tag, a, b, cut)
    }

    /// Removes the pending entries. The checker calls it at the start of each declaration.
    pub(crate) fn sess_start(&mut self) {
        self.sess.pending.truncate(0);
    }

    /// Puts the pending entries of an accepted declaration into the session. A value in the scratch tier is copied into the frozen tier first. The copies use at most 10% of the scratch nodes (spec 04.8). The caller then clears the scratch tier.
    pub(crate) fn sess_commit(&mut self) {
        if self.sess.pending.is_empty() {
            return;
        }
        let pending = core::mem::take(&mut self.sess.pending);
        let stamp = self.sess_cut();
        let mut budget = self.st.scratch_total() / 10;
        let mut map = Memo::new();
        let saved = self.st.uses_scratch();
        self.st.set_scratch(false);
        let mut i = 0;
        while i < pending.len() {
            let (tag, a, b, v) = pending[i];
            let v2 = if value_is_term(tag) && ExprId(v).tier() == Tier::Scratch {
                self.promote(ExprId(v), &mut map, &mut budget, false)
            } else {
                Some(ExprId(v))
            };
            match v2 {
                Some(v2) => self.sess.store(tag, a, b, v2.0, stamp),
                None => self.sess.stats.drops += 1,
            }
            i += 1;
        }
        self.st.set_scratch(saved);
        let mut pending = pending;
        pending.truncate(0);
        self.sess.pending = pending;
    }

    /// Copies the terms of the fault `f` and the types and the values of the local context into the frozen tier. The caller then clears the scratch tier. A term that cannot be copied becomes the dummy term. The copies have no budget, because this runs only for a rejection.
    pub(crate) fn keep_fault(&mut self, f: Fault) -> Fault {
        let mut map = Memo::new();
        let mut budget = usize::MAX;
        let saved = self.st.uses_scratch();
        self.st.set_scratch(false);
        let at = self.keep(f.at, &mut map, &mut budget);
        let ty1 = self.keep(f.ty1, &mut map, &mut budget);
        let ty2 = self.keep(f.ty2, &mut map, &mut budget);
        let mut i = 0;
        while i < self.lctx_ty.len() {
            let t = self.lctx_ty[i];
            self.lctx_ty[i] = self.keep(t, &mut map, &mut budget);
            if let Some(v) = self.lctx_val[i] {
                self.lctx_val[i] = Some(self.keep(v, &mut map, &mut budget));
            }
            i += 1;
        }
        self.st.set_scratch(saved);
        Fault {
            kind: f.kind,
            at,
            ty1,
            ty2,
        }
    }

    /// A frozen copy of `e` with its free variables, or the dummy term.
    fn keep(&mut self, e: ExprId, map: &mut Memo, budget: &mut usize) -> ExprId {
        if e.tier() != Tier::Scratch {
            return e;
        }
        match self.promote(e, map, budget, true) {
            Some(c) => c,
            None => self.dummy,
        }
    }

    /// A frozen copy of the scratch term `e`, or `None` if the copy needs more than `budget` new nodes, if the store is full, or if `e` has a free variable and `fvars` is false. `map` has the copies made so far.
    fn promote(
        &mut self,
        e: ExprId,
        map: &mut Memo,
        budget: &mut usize,
        fvars: bool,
    ) -> Option<ExprId> {
        // An explicit stack, because a term can be deep. A node is pushed once to copy its fields and once more to build it.
        let mut stack: Vec<(ExprId, bool)> = Vec::new();
        stack.push((e, false));
        let mut ok = true;
        while ok && stack.len() > 0 {
            let (x, ready) = match stack.pop() {
                Some(top) => top,
                None => (e, true),
            };
            if x.tier() == Tier::Scratch && !map.contains(x.0, 0) {
                if ready {
                    ok = self.promote_node(x, map, budget, fvars);
                } else {
                    ok = self.promote_push(x, &mut stack, fvars);
                }
            }
        }
        if !ok {
            return None;
        }
        Some(copied(map, e))
    }

    /// Pushes the node `x` to build it later, and its fields to copy them first. It gives false for a free variable if `fvars` is false.
    fn promote_push(&mut self, x: ExprId, stack: &mut Vec<(ExprId, bool)>, fvars: bool) -> bool {
        stack.push((x, true));
        match self.st.node(x) {
            Expr::App(f, a) => {
                stack.push((a, false));
                stack.push((f, false));
            }
            Expr::Lam(bd) | Expr::Pi(bd) => {
                stack.push((bd.body, false));
                stack.push((bd.dom, false));
            }
            Expr::Let(l) => {
                stack.push((l.body, false));
                stack.push((l.value, false));
                stack.push((l.ty, false));
            }
            Expr::Proj(p) => stack.push((p.expr, false)),
            Expr::FVar(_, t) => {
                if !fvars {
                    return false;
                }
                stack.push((t, false));
            }
            Expr::BVar(_) | Expr::Sort(_) | Expr::Const(_, _) | Expr::Lit(_) => {}
        }
        true
    }

    /// Builds the frozen copy of the node `x`, whose fields are frozen or in `map`. It gives false if the budget is used, if the store is full, or for a free variable if `fvars` is false.
    fn promote_node(&mut self, x: ExprId, map: &mut Memo, budget: &mut usize, fvars: bool) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        let r = match self.st.node(x) {
            Expr::BVar(i) => self.st.mk_bvar(i),
            Expr::Sort(l) => self.st.mk_sort(l),
            Expr::Const(n, ls) => self.st.mk_const(n, ls),
            Expr::App(g, a) => {
                let (g, a) = (copied(map, g), copied(map, a));
                self.st.mk_app(g, a)
            }
            Expr::Lam(bd) => {
                let (d, b) = (copied(map, bd.dom), copied(map, bd.body));
                self.st.mk_lam(bd.name, bd.info, d, b)
            }
            Expr::Pi(bd) => {
                let (d, b) = (copied(map, bd.dom), copied(map, bd.body));
                self.st.mk_pi(bd.name, bd.info, d, b)
            }
            Expr::Let(l) => {
                let t = copied(map, l.ty);
                let v = copied(map, l.value);
                let b = copied(map, l.body);
                self.st.mk_let(l.name, t, v, b)
            }
            Expr::Lit(Literal::Nat(n)) => self.st.mk_nat_lit(n),
            Expr::Lit(Literal::Str(s)) => self.st.mk_str_lit(s),
            Expr::Proj(p) => {
                let y = copied(map, p.expr);
                self.st.mk_proj(p.struct_name, p.index, y)
            }
            Expr::FVar(l, t) => {
                if !fvars {
                    return false;
                }
                let t = copied(map, t);
                self.st.mk_fvar(l, t)
            }
        };
        if self.st.is_full() || r.tier() != Tier::Frozen {
            return false;
        }
        if !fvars {
            self.sess.stats.promoted += 1;
        }
        map.put(x.0, 0, r.0);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_after_insert() {
        let mut s = Session::new(1 << 16);
        assert_eq!(s.get(S_WHNF, 1, 0, 10), None);
        s.store(S_WHNF, 1, 0, 7, 5);
        assert_eq!(s.get(S_WHNF, 1, 0, 10), Some(7));
        assert_eq!(s.get(S_INFER, 1, 0, 10), None);
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn stamp_above_cut_is_not_used() {
        let mut s = Session::new(1 << 16);
        s.store(S_SUCCESS, 3, 4, 1, 9);
        assert_eq!(s.get(S_SUCCESS, 3, 4, 8), None);
        assert_eq!(s.get(S_SUCCESS, 3, 4, 9), Some(1));
    }

    #[test]
    fn smaller_stamp_wins() {
        let mut s = Session::new(1 << 16);
        s.store(S_WHNF, 1, 0, 7, 9);
        s.store(S_WHNF, 1, 0, 8, 4);
        s.store(S_WHNF, 1, 0, 6, 6);
        assert_eq!(s.get(S_WHNF, 1, 0, 5), Some(8));
    }

    #[test]
    fn bounded_size_evicts() {
        // 4096 bytes give 128 slots.
        let mut s = Session::new(4096);
        let mut i = 0;
        while i < 10_000 {
            s.store(S_WHNF, i, 0, i, 0);
            i += 1;
        }
        assert!(s.len() <= 128);
        assert!(s.stats.evictions > 0);
        assert_eq!(s.get(S_WHNF, 9_999, 0, 0), Some(9_999));
    }

    /// A checker with a frozen key, and `fillers` scratch nodes that set the promotion budget.
    fn checker_with_scratch(fillers: u32) -> (Checker, ExprId) {
        let mut c = Checker::new(rulean_store::Store::new());
        let key = c.st.mk_bvar(1_000_000);
        c.st.set_scratch(true);
        let mut i = 0;
        while i < fillers {
            c.st.mk_bvar(2_000_000 + i);
            i += 1;
        }
        (c, key)
    }

    #[test]
    fn commit_promotes_a_scratch_value() {
        let (mut c, key) = checker_with_scratch(100);
        let n = c.st.anon();
        let (a, b) = (c.st.mk_bvar(7), c.st.mk_bvar(8));
        let v = c.st.mk_lam(n, rulean_store::BinderInfo::Default, a, b);
        assert_eq!(v.tier(), Tier::Scratch);
        c.sess.note(S_WHNF, key.0, 0, v.0);
        c.sess_commit();
        c.st.clear_scratch();
        let got = ExprId(c.sess.get(S_WHNF, key.0, 0, c.sess_cut()).expect("kept"));
        assert_eq!(got.tier(), Tier::Frozen);
        assert_eq!(c.sess.stats.promoted, 3);
        match c.st.node(got) {
            Expr::Lam(bd) => {
                assert_eq!(c.st.node(bd.dom), Expr::BVar(7));
                assert_eq!(c.st.node(bd.body), Expr::BVar(8));
            }
            _ => panic!("not a lambda"),
        }
    }

    #[test]
    fn commit_drops_a_value_over_the_budget() {
        // 10 scratch nodes give a budget of 1 node, and the value needs 3.
        let (mut c, key) = checker_with_scratch(7);
        let n = c.st.anon();
        let (a, b) = (c.st.mk_bvar(7), c.st.mk_bvar(8));
        let v = c.st.mk_lam(n, rulean_store::BinderInfo::Default, a, b);
        c.sess.note(S_WHNF, key.0, 0, v.0);
        c.sess_commit();
        assert_eq!(c.sess.stats.drops, 1);
        assert!(c.sess.is_empty());
    }

    #[test]
    fn commit_keeps_no_free_variable() {
        let (mut c, key) = checker_with_scratch(100);
        let ty = c.st.mk_bvar(9);
        let x = c.st.mk_fvar(0, ty);
        c.sess.note(S_WHNF, key.0, 0, x.0);
        c.sess_commit();
        assert_eq!(c.sess.stats.drops, 1);
    }

    #[test]
    fn clear_removes_entries() {
        let mut s = Session::new(1 << 16);
        s.store(S_WHNF, 1, 0, 7, 0);
        s.note(S_WHNF, 2, 0, 8);
        s.clear();
        assert_eq!(s.get(S_WHNF, 1, 0, 0), None);
        assert!(s.pending.is_empty());
        assert!(s.is_empty());
    }
}
