//! Universe levels (spec 05.6).
//!
//! This module is a transcription of `level.cpp` of the official kernel, v4.35.0. The functions keep the order of the cases and the simplifications of the official code, because the shape of a level can change the result of `is_geq`, and the official kernel is the reference for the result.
//!
//! The store interns levels, so two levels are structurally equal if and only if their handles are equal. The official code compares levels with `==`, which is structural. This module compares handles.

use alloc::vec::Vec;
use rulean_store::{Level, LevelId, Name, NameId, Store};

/// The cache of `normalize` for one run (spec 05.6). It holds one slot for each level handle. A slot is 0 if the level is not normalized yet, else the handle of the normal form plus 1.
#[derive(Debug, Default)]
pub struct LevelCache {
    norm: Vec<u32>,
}

impl LevelCache {
    /// An empty cache.
    pub fn new() -> LevelCache {
        LevelCache { norm: Vec::new() }
    }

    fn get(&self, l: LevelId) -> u32 {
        let i = l.0 as usize;
        if i < self.norm.len() { self.norm[i] } else { 0 }
    }

    fn put(&mut self, l: LevelId, r: LevelId) {
        let i = l.0 as usize;
        while self.norm.len() <= i {
            self.norm.push(0);
        }
        // The sum is a separate statement, because Charon cannot remove the overflow check of a sum that is followed by an `IndexMut` call.
        let v = r.0 + 1;
        self.norm[i] = v;
    }
}

/// The rank of a level kind in the order of the official kernel: zero, succ, max, imax, param.
fn rank(l: Level) -> u32 {
    match l {
        Level::Zero => 0,
        Level::Succ(_) => 1,
        Level::Max(_, _) => 2,
        Level::IMax(_, _) => 3,
        Level::Param(_) => 4,
    }
}

/// True if `l` is the level zero.
pub fn is_zero(st: &Store, l: LevelId) -> bool {
    l == st.level_zero()
}

/// True if `l` is `succ zero`.
pub fn is_one(st: &Store, l: LevelId) -> bool {
    match st.level(l) {
        Level::Succ(a) => is_zero(st, a),
        _ => false,
    }
}

/// Splits `succ^k b` into `(b, k)`, where `b` is not a succ.
pub fn to_offset(st: &Store, l: LevelId) -> (LevelId, u32) {
    let mut cur = l;
    let mut k: u32 = 0;
    let mut walking = true;
    while walking {
        match st.level(cur) {
            Level::Succ(a) => {
                cur = a;
                k = k.wrapping_add(1);
            }
            _ => walking = false,
        }
    }
    (cur, k)
}

/// True if `l` is `succ^k zero` for some `k`.
pub fn is_explicit(st: &Store, l: LevelId) -> bool {
    let (b, _) = to_offset(st, l);
    is_zero(st, b)
}

/// `succ^k l`.
pub fn mk_succ_n(st: &mut Store, l: LevelId, k: u32) -> LevelId {
    let mut r = l;
    let mut i = 0;
    while i < k {
        r = st.level_succ(r);
        i += 1;
    }
    r
}

/// True if `l` is `max a b` and `x` is `a` or `b`.
fn is_max_with(st: &Store, l: LevelId, x: LevelId) -> bool {
    match st.level(l) {
        Level::Max(a, b) => a == x || b == x,
        _ => false,
    }
}

/// `max l1 l2` with the simplifications of `mk_max` of the official kernel.
pub fn mk_max(st: &mut Store, l1: LevelId, l2: LevelId) -> LevelId {
    if is_explicit(st, l1) && is_explicit(st, l2) {
        let (_, k1) = to_offset(st, l1);
        let (_, k2) = to_offset(st, l2);
        return if k1 >= k2 { l1 } else { l2 };
    }
    if l1 == l2 {
        return l1;
    }
    if is_zero(st, l1) {
        return l2;
    }
    if is_zero(st, l2) {
        return l1;
    }
    // max l1 (max l1 l') is max l1 l'.
    if is_max_with(st, l2, l1) {
        return l2;
    }
    if is_max_with(st, l1, l2) {
        return l1;
    }
    let (b1, k1) = to_offset(st, l1);
    let (b2, k2) = to_offset(st, l2);
    if b1 == b2 {
        return if k1 > k2 { l1 } else { l2 };
    }
    st.level_max(l1, l2)
}

/// `imax l1 l2` with the simplifications of `mk_imax` of the official kernel.
pub fn mk_imax(st: &mut Store, l1: LevelId, l2: LevelId) -> LevelId {
    if is_not_zero(st, l2) {
        return mk_max(st, l1, l2);
    }
    // imax u 0 is 0.
    if is_zero(st, l2) {
        return l2;
    }
    // imax 0 u and imax 1 u are u.
    if is_zero(st, l1) || is_one(st, l1) {
        return l2;
    }
    if l1 == l2 {
        return l1;
    }
    st.level_imax(l1, l2)
}

/// True if `l` is not zero for all values of the parameters.
pub fn is_not_zero(st: &Store, l: LevelId) -> bool {
    match st.level(l) {
        Level::Zero => false,
        Level::Param(_) => false,
        Level::Succ(_) => true,
        Level::Max(a, b) => is_not_zero(st, a) || is_not_zero(st, b),
        Level::IMax(_, b) => is_not_zero(st, b),
    }
}

/// True if `l` normalizes to zero. `is_prop` and the Prop inductive check use it.
pub fn normalizes_to_zero(st: &Store, l: LevelId) -> bool {
    match st.level(l) {
        Level::Zero => true,
        Level::Param(_) => false,
        Level::Succ(_) => false,
        Level::Max(a, b) => normalizes_to_zero(st, a) && normalizes_to_zero(st, b),
        // `mk_imax` gives its right side when that side is zero.
        Level::IMax(_, b) => normalizes_to_zero(st, b),
    }
}

/// The components of a name from the root, for example `[A, b, 1]` for `A.b.1`.
fn name_limbs(st: &Store, n: NameId) -> Vec<NameId> {
    let mut rev: Vec<NameId> = Vec::new();
    let mut cur = n;
    let mut walking = true;
    while walking {
        match st.name(cur) {
            Name::Anon => walking = false,
            Name::Str(pre, _) => {
                rev.push(cur);
                cur = pre;
            }
            Name::Num(pre, _) => {
                rev.push(cur);
                cur = pre;
            }
        }
    }
    let mut out: Vec<NameId> = Vec::with_capacity(rev.len());
    let mut i = rev.len();
    while i > 0 {
        i -= 1;
        out.push(rev[i]);
    }
    out
}

/// Compares two byte strings as `strcmp` does on strings without a zero byte.
fn bytes_cmp(a: &[u8], b: &[u8]) -> i32 {
    let mut r: i32 = 0;
    let mut i = 0;
    while r == 0 && i < a.len() && i < b.len() {
        if a[i] < b[i] {
            r = -1;
        } else if a[i] > b[i] {
            r = 1;
        }
        i += 1;
    }
    if r == 0 && a.len() != b.len() {
        r = if a.len() < b.len() { -1 } else { 1 };
    }
    r
}

/// Compares two components of the same position. A number is less than a string.
fn limb_cmp(st: &Store, a: NameId, b: NameId) -> i32 {
    match (st.name(a), st.name(b)) {
        (Name::Str(_, x), Name::Str(_, y)) => bytes_cmp(st.str_bytes(x), st.str_bytes(y)),
        (Name::Num(_, x), Name::Num(_, y)) => {
            if x < y {
                -1
            } else if x > y {
                1
            } else {
                0
            }
        }
        (Name::Num(_, _), _) => -1,
        (Name::Str(_, _), _) => 1,
        _ => 0,
    }
}

/// The total order on names of the official kernel (`name::cmp`). It compares the components from the root. A name that is a prefix of the other name is less.
pub fn name_cmp(st: &Store, a: NameId, b: NameId) -> i32 {
    if a == b {
        return 0;
    }
    // The fast path makes no vector (spec perf/04.3 A9). Names are hash-consed, so two names with the same parent and different ids differ in the last component.
    let da = name_depth(st, a);
    let db = name_depth(st, b);
    let mut x = name_up(st, a, da.saturating_sub(db));
    let mut y = name_up(st, b, db.saturating_sub(da));
    if x == y {
        return if da < db { -1 } else { 1 };
    }
    let mut px = name_up(st, x, 1);
    let mut py = name_up(st, y, 1);
    while px != py {
        x = px;
        y = py;
        px = name_up(st, x, 1);
        py = name_up(st, y, 1);
    }
    let r = limb_cmp(st, x, y);
    if r != 0 {
        return r;
    }
    name_cmp_slow(st, a, b)
}

/// The number of components of `n`.
fn name_depth(st: &Store, n: NameId) -> usize {
    let mut d = 0;
    let mut cur = n;
    let mut walking = true;
    while walking {
        match st.name(cur) {
            Name::Anon => walking = false,
            Name::Str(pre, _) | Name::Num(pre, _) => {
                d += 1;
                cur = pre;
            }
        }
    }
    d
}

/// The ancestor of `n` that is `k` components up.
fn name_up(st: &Store, n: NameId, k: usize) -> NameId {
    let mut cur = n;
    let mut i = 0;
    while i < k {
        match st.name(cur) {
            Name::Anon => i = k,
            Name::Str(pre, _) | Name::Num(pre, _) => {
                cur = pre;
                i += 1;
            }
        }
    }
    cur
}

/// `name_cmp` with vectors of the components. It is used only when two different ids have equal components.
fn name_cmp_slow(st: &Store, a: NameId, b: NameId) -> i32 {
    let la = name_limbs(st, a);
    let lb = name_limbs(st, b);
    let mut r: i32 = 0;
    let mut i = 0;
    while r == 0 && i < la.len() && i < lb.len() {
        if la[i] != lb[i] {
            r = limb_cmp(st, la[i], lb[i]);
        }
        i += 1;
    }
    if r == 0 && la.len() != lb.len() {
        r = if la.len() < lb.len() { -1 } else { 1 };
    }
    r
}

/// The total order of the normalization (`is_norm_lt`). Zero is the least element, and `succ l` comes right after `l`.
pub fn is_norm_lt(st: &Store, a: LevelId, b: LevelId) -> bool {
    if a == b {
        return false;
    }
    let (l1, k1) = to_offset(st, a);
    let (l2, k2) = to_offset(st, b);
    if l1 == l2 {
        return k1 < k2;
    }
    let n1 = st.level(l1);
    let n2 = st.level(l2);
    if rank(n1) != rank(n2) {
        return rank(n1) < rank(n2);
    }
    match (n1, n2) {
        (Level::Param(x), Level::Param(y)) => name_cmp(st, x, y) < 0,
        (Level::Max(a1, b1), Level::Max(a2, b2)) => pair_lt(st, a1, b1, a2, b2),
        (Level::IMax(a1, b1), Level::IMax(a2, b2)) => pair_lt(st, a1, b1, a2, b2),
        _ => false,
    }
}

fn pair_lt(st: &Store, a1: LevelId, b1: LevelId, a2: LevelId, b2: LevelId) -> bool {
    if a1 != a2 {
        is_norm_lt(st, a1, a2)
    } else {
        is_norm_lt(st, b1, b2)
    }
}

/// Appends the arguments of a nest of `max` nodes to `out`.
fn push_max_args(st: &Store, l: LevelId, out: &mut Vec<LevelId>) {
    match st.level(l) {
        Level::Max(a, b) => {
            push_max_args(st, a, out);
            push_max_args(st, b, out);
        }
        _ => out.push(l),
    }
}

/// `max a0 (max a1 (... an))` with the simplifications of `mk_max`. The slice must not be empty.
fn mk_max_list(st: &mut Store, args: &[LevelId]) -> LevelId {
    let n = args.len();
    if n == 0 {
        return st.level_zero();
    }
    if n == 1 {
        return args[0];
    }
    let mut r = mk_max(st, args[n - 2], args[n - 1]);
    let mut i = n - 2;
    while i > 0 {
        i -= 1;
        r = mk_max(st, args[i], r);
    }
    r
}

/// Sorts the levels by `is_norm_lt` with an insertion sort. Equal levels have equal handles, so the result does not depend on the sort algorithm. Each loop is in its own function and the vector moves by value, because Aeneas cannot translate a nested loop that changes a borrowed slice.
fn sort_levels(st: &Store, v: Vec<LevelId>) -> Vec<LevelId> {
    let mut v = v;
    let mut i = 1;
    while i < v.len() {
        v = sift_down(st, v, i);
        i += 1;
    }
    v
}

/// Moves `v[i]` down to its place in the sorted prefix `v[0..i]`.
fn sift_down(st: &Store, v: Vec<LevelId>, i: usize) -> Vec<LevelId> {
    let mut v = v;
    let x = v[i];
    let mut j = i;
    while sift_more(st, &v, j, x) {
        let k = j - 1;
        let y = v[k];
        v[j] = y;
        j = k;
    }
    v[j] = x;
    v
}

/// True if `x` must go before `v[j - 1]`.
fn sift_more(st: &Store, v: &[LevelId], j: usize, x: LevelId) -> bool {
    if j == 0 {
        return false;
    }
    is_norm_lt(st, x, v[j - 1])
}

/// The normal form of a level (`normalize`). The result is cached.
pub fn normalize(st: &mut Store, cache: &mut LevelCache, l: LevelId) -> LevelId {
    let c = cache.get(l);
    if c != 0 {
        return LevelId(c - 1);
    }
    let r = normalize_core(st, cache, l);
    cache.put(l, r);
    r
}

fn normalize_core(st: &mut Store, cache: &mut LevelCache, l: LevelId) -> LevelId {
    let (r, k) = to_offset(st, l);
    match st.level(r) {
        Level::Zero => l,
        Level::Param(_) => l,
        Level::Succ(_) => l,
        Level::IMax(a, b) => {
            let l1 = normalize(st, cache, a);
            let l2 = normalize(st, cache, b);
            let m = mk_imax(st, l1, l2);
            mk_succ_n(st, m, k)
        }
        Level::Max(_, _) => normalize_max(st, cache, r, k),
    }
}

/// The `max` case of `normalize`: flatten, sort, keep the largest offset for each base, and drop an explicit level that a larger offset covers.
fn normalize_max(st: &mut Store, cache: &mut LevelCache, r: LevelId, k: u32) -> LevelId {
    let mut todo: Vec<LevelId> = Vec::new();
    push_max_args(st, r, &mut todo);
    let mut args: Vec<LevelId> = Vec::new();
    let mut t = 0;
    while t < todo.len() {
        let n = normalize(st, cache, todo[t]);
        push_max_args(st, n, &mut args);
        t += 1;
    }
    let args = sort_levels(st, args);
    let len = args.len();
    let mut i = 0;
    if is_explicit(st, args[0]) {
        // Find the largest explicit level.
        while i + 1 < len && is_explicit(st, args[i + 1]) {
            i += 1;
        }
        let (_, kk) = to_offset(st, args[i]);
        // An explicit level k is covered by succ^k' l for k' >= k.
        let mut j = i + 1;
        let mut covered = false;
        while !covered && j < len {
            let (_, kj) = to_offset(st, args[j]);
            if kj >= kk {
                covered = true;
            } else {
                j += 1;
            }
        }
        if covered {
            i += 1;
        }
    }
    let mut rargs: Vec<LevelId> = Vec::new();
    rargs.push(args[i]);
    let mut prev = to_offset(st, args[i]);
    i += 1;
    while i < len {
        let curr = to_offset(st, args[i]);
        if prev.0 == curr.0 {
            if prev.1 < curr.1 {
                prev = curr;
                rargs.pop();
                rargs.push(args[i]);
            }
        } else {
            prev = curr;
            rargs.push(args[i]);
        }
        i += 1;
    }
    let mut a = 0;
    while a < rargs.len() {
        rargs[a] = mk_succ_n(st, rargs[a], k);
        a += 1;
    }
    mk_max_list(st, &rargs)
}

/// True if the levels are equal after normalization (`is_equivalent`). This is incomplete by design (spec 05.6).
pub fn is_equivalent(st: &mut Store, cache: &mut LevelCache, l1: LevelId, l2: LevelId) -> bool {
    if l1 == l2 {
        return true;
    }
    let n1 = normalize(st, cache, l1);
    let n2 = normalize(st, cache, l2);
    n1 == n2
}

/// True if the level lists have the same length and equivalent items.
pub fn is_equivalent_list(
    st: &mut Store,
    cache: &mut LevelCache,
    a: &[LevelId],
    b: &[LevelId],
) -> bool {
    let mut ok = a.len() == b.len();
    let mut i = 0;
    while ok && i < a.len() {
        ok = is_equivalent(st, cache, a[i], b[i]);
        i += 1;
    }
    ok
}

/// True if `l1 >= l2` for all values of the parameters, by the structural algorithm of the official kernel (`is_geq`).
pub fn is_geq(st: &mut Store, cache: &mut LevelCache, l1: LevelId, l2: LevelId) -> bool {
    let n1 = normalize(st, cache, l1);
    let n2 = normalize(st, cache, l2);
    is_geq_core(st, cache, n1, n2)
}

fn is_geq_core(st: &mut Store, cache: &mut LevelCache, l1: LevelId, l2: LevelId) -> bool {
    if l1 == l2 || is_zero(st, l2) {
        return true;
    }
    if let Level::Max(a, b) = st.level(l2) {
        return is_geq(st, cache, l1, a) && is_geq(st, cache, l1, b);
    }
    if let Level::Max(a, b) = st.level(l1) {
        if is_geq(st, cache, a, l2) || is_geq(st, cache, b, l2) {
            return true;
        }
    }
    if let Level::IMax(a, b) = st.level(l2) {
        return is_geq(st, cache, l1, a) && is_geq(st, cache, l1, b);
    }
    if let Level::IMax(_, b) = st.level(l1) {
        return is_geq(st, cache, b, l2);
    }
    let (b1, k1) = to_offset(st, l1);
    let (b2, k2) = to_offset(st, l2);
    if b1 == b2 || is_zero(st, b2) {
        return k1 >= k2;
    }
    if k1 == k2 && k1 > 0 {
        return is_geq(st, cache, b1, b2);
    }
    false
}

/// Replaces each parameter `ps[i]` with `ls[i]` (`instantiate`). A changed `max` or `imax` node is made again with `mk_max` or `mk_imax`, so the result has the simplifications of the official kernel.
pub fn instantiate(st: &mut Store, l: LevelId, ps: &[NameId], ls: &[LevelId]) -> LevelId {
    if !st.level_has_param(l) {
        return l;
    }
    match st.level(l) {
        Level::Zero => l,
        Level::Param(n) => {
            let mut r = l;
            let mut found = false;
            let mut i = 0;
            while !found && i < ps.len() && i < ls.len() {
                if ps[i] == n {
                    r = ls[i];
                    found = true;
                }
                i += 1;
            }
            r
        }
        Level::Succ(a) => {
            let a2 = instantiate(st, a, ps, ls);
            if a2 == a { l } else { st.level_succ(a2) }
        }
        Level::Max(a, b) => {
            let a2 = instantiate(st, a, ps, ls);
            let b2 = instantiate(st, b, ps, ls);
            if a2 == a && b2 == b {
                l
            } else {
                mk_max(st, a2, b2)
            }
        }
        Level::IMax(a, b) => {
            let a2 = instantiate(st, a, ps, ls);
            let b2 = instantiate(st, b, ps, ls);
            if a2 == a && b2 == b {
                l
            } else {
                mk_imax(st, a2, b2)
            }
        }
    }
}

/// The first parameter of `l` that is not in `ps`, as a name plus 1, or 0 if there is none (`get_undef_param`).
pub fn undef_param(st: &Store, l: LevelId, ps: &[NameId]) -> u32 {
    if !st.level_has_param(l) {
        return 0;
    }
    match st.level(l) {
        Level::Zero => 0,
        Level::Param(n) => {
            let mut found = false;
            let mut i = 0;
            while !found && i < ps.len() {
                found = ps[i] == n;
                i += 1;
            }
            if found { 0 } else { n.0 + 1 }
        }
        Level::Succ(a) => undef_param(st, a, ps),
        Level::Max(a, b) => {
            let r = undef_param(st, a, ps);
            if r != 0 { r } else { undef_param(st, b, ps) }
        }
        Level::IMax(a, b) => {
            let r = undef_param(st, a, ps);
            if r != 0 { r } else { undef_param(st, b, ps) }
        }
    }
}
