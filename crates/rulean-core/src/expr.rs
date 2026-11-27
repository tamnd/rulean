//! Operations on expressions: instantiation, abstraction, lifting, level instantiation, application spines, beta reduction and alpha-equality.
//!
//! This module is a transcription of `instantiate.cpp`, `abstract.cpp`, the loose bound variable part of `expr.cpp` and `expr_eq_fn.cpp` of the official kernel v4.35.0.
//!
//! The official functions use `replace` with a cache for shared nodes. Here each function has its own recursion and a `Lossy` cache keyed by the node and the binder offset. A miss of this cache only costs more work, because the result of a node does not depend on the order of the visits. A free variable is an atom: the functions do not go into its type.

use alloc::vec::Vec;
use rulean_store::ids::raw;
use rulean_store::{Expr, ExprId, Flags, LevelId, NameId, SATURATED, Store};

use crate::level;
use crate::memo::Lossy;

/// The first level of the far free variables. A far free variable is a free variable of a term that is not in the local context. The C++ kernel accepts such a term, and it gives "unknown free variable" only when it must read the declaration of the variable. The checker gives the fault `UnknownFVar` when it infers the type of a far free variable, and `whnf` keeps the variable. The local context of the checker cannot have this number of declarations.
pub const FAR_FVAR: u32 = 1 << 31;

/// The far free variable with the number `k`. Its level is `FAR_FVAR + k`, and its type is `Sort 0`. The type is only a placeholder, because the checker does not read the type of a far free variable.
pub fn far_fvar(st: &mut Store, k: u32) -> ExprId {
    let z = st.level_zero();
    let t = st.mk_sort(z);
    st.mk_fvar(FAR_FVAR.saturating_add(k), t)
}

/// The scratch maps of the expression operations. Each operation clears its own map when it starts.
#[derive(Debug, Default)]
pub struct Scratch {
    inst: Lossy,
    lift: Lossy,
    abs: Lossy,
    occ: Lossy,
    lps: Lossy,
    eq: Lossy,
}

impl Scratch {
    /// New empty maps.
    pub fn new() -> Scratch {
        Scratch {
            inst: Lossy::new(),
            lift: Lossy::new(),
            abs: Lossy::new(),
            occ: Lossy::new(),
            lps: Lossy::new(),
            eq: Lossy::new(),
        }
    }
}

/// True if `e` has no loose bound variable with an index `k` or more. A saturated range can hide any index, so it never gives true.
pub fn no_loose_from(st: &Store, e: ExprId, k: u64) -> bool {
    let r = st.loose_range(e);
    r != SATURATED && k >= r as u64
}

/// True if `e` has a loose bound variable.
pub fn has_loose_bvars(st: &Store, e: ExprId) -> bool {
    st.loose_range(e) != 0
}

/// True if `e` has a free variable.
pub fn has_fvar(st: &Store, e: ExprId) -> bool {
    st.flags(e).has(Flags::HAS_FVAR)
}

/// True if `e` has a `lam`, a `pi` or a `let`.
pub fn has_binder(st: &Store, e: ExprId) -> bool {
    st.flags(e).has(Flags::HAS_BINDER)
}

/// True if `e` has a level parameter.
pub fn has_level_param(st: &Store, e: ExprId) -> bool {
    st.flags(e).has(Flags::HAS_LEVEL_PARAM)
}

/// The bound variable `i`, or the largest index if `i` is too large for `u32`.
fn bvar_at(st: &mut Store, i: u64) -> ExprId {
    let k = if i > u32::MAX as u64 {
        u32::MAX
    } else {
        i as u32
    };
    st.mk_bvar(k)
}

// Instantiation.

/// Replaces the loose bound variable `i` with `subst[i]` for `i < n`, and lowers the other loose bound variables by `n` (`instantiate(e, n, s)`).
pub fn instantiate(st: &mut Store, x: &mut Scratch, e: ExprId, subst: &[ExprId]) -> ExprId {
    instantiate_from(st, x, e, 0, subst)
}

/// `instantiate(e, s, n, subst)` of the official kernel: replaces the loose bound variable `s + i` with `subst[i]`.
pub fn instantiate_from(
    st: &mut Store,
    x: &mut Scratch,
    e: ExprId,
    s: u32,
    subst: &[ExprId],
) -> ExprId {
    if subst.len() == 0 || no_loose_from(st, e, s as u64) {
        return e;
    }
    x.inst.clear();
    inst_rec(st, x, e, 0, s, subst, false)
}

/// `instantiate(e, v)`: replaces the loose bound variable 0 with `v`.
pub fn instantiate1(st: &mut Store, x: &mut Scratch, e: ExprId, v: ExprId) -> ExprId {
    instantiate(st, x, e, &[v])
}

/// Replaces the loose bound variable `i` with `subst[n - i - 1]` for `i < n` (`instantiate_rev`). The last item of `subst` is the innermost binder.
pub fn instantiate_rev(st: &mut Store, x: &mut Scratch, e: ExprId, subst: &[ExprId]) -> ExprId {
    if subst.len() == 0 || !has_loose_bvars(st, e) {
        return e;
    }
    x.inst.clear();
    inst_rec(st, x, e, 0, 0, subst, true)
}

#[allow(clippy::too_many_arguments)]
fn inst_rec(
    st: &mut Store,
    x: &mut Scratch,
    e: ExprId,
    offset: u32,
    s: u32,
    subst: &[ExprId],
    rev: bool,
) -> ExprId {
    let s1 = s as u64 + offset as u64;
    if no_loose_from(st, e, s1) {
        return e;
    }
    let n = subst.len() as u64;
    if let Expr::BVar(i) = st.node(e) {
        let iv = i as u64;
        if iv < s1 {
            return e;
        }
        if iv < s1 + n {
            let k = (iv - s1) as usize;
            let v = if rev {
                subst[subst.len() - k - 1]
            } else {
                subst[k]
            };
            return lift_loose_bvars(st, x, v, 0, offset);
        }
        return bvar_at(st, iv - n);
    }
    match x.inst.get(e.0, raw(offset)) {
        Some(r) => ExprId(r),
        None => {
            let r = inst_node(st, x, e, offset, s, subst, rev);
            x.inst.put(e.0, raw(offset), r.0);
            r
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn inst_node(
    st: &mut Store,
    x: &mut Scratch,
    e: ExprId,
    offset: u32,
    s: u32,
    subst: &[ExprId],
    rev: bool,
) -> ExprId {
    match st.node(e) {
        Expr::App(f, a) => {
            let f2 = inst_rec(st, x, f, offset, s, subst, rev);
            let a2 = inst_rec(st, x, a, offset, s, subst, rev);
            if f2 == f && a2 == a {
                e
            } else {
                st.mk_app(f2, a2)
            }
        }
        Expr::Lam(b) => {
            let d = inst_rec(st, x, b.dom, offset, s, subst, rev);
            let body = inst_rec(st, x, b.body, offset + 1, s, subst, rev);
            st.mk_lam(b.name, b.info, d, body)
        }
        Expr::Pi(b) => {
            let d = inst_rec(st, x, b.dom, offset, s, subst, rev);
            let body = inst_rec(st, x, b.body, offset + 1, s, subst, rev);
            st.mk_pi(b.name, b.info, d, body)
        }
        Expr::Let(l) => {
            let t = inst_rec(st, x, l.ty, offset, s, subst, rev);
            let v = inst_rec(st, x, l.value, offset, s, subst, rev);
            let body = inst_rec(st, x, l.body, offset + 1, s, subst, rev);
            st.mk_let(l.name, t, v, body)
        }
        Expr::Proj(p) => {
            let a = inst_rec(st, x, p.expr, offset, s, subst, rev);
            st.mk_proj(p.struct_name, p.index, a)
        }
        _ => e,
    }
}

// Lifting and lowering.

/// Adds `d` to each loose bound variable with an index `s` or more (`lift_loose_bvars(e, s, d)`).
pub fn lift_loose_bvars(st: &mut Store, x: &mut Scratch, e: ExprId, s: u32, d: u32) -> ExprId {
    if d == 0 || no_loose_from(st, e, s as u64) {
        return e;
    }
    x.lift.clear();
    shift_rec(st, &mut x.lift, e, 0, s, d, true)
}

/// Subtracts `d` from each loose bound variable with an index `s` or more (`lower_loose_bvars(e, s, d)`). The caller makes sure that `s >= d` and that no loose bound variable has an index in `s - d .. s`.
pub fn lower_loose_bvars(st: &mut Store, x: &mut Scratch, e: ExprId, s: u32, d: u32) -> ExprId {
    if d == 0 || no_loose_from(st, e, s as u64) {
        return e;
    }
    x.lift.clear();
    shift_rec(st, &mut x.lift, e, 0, s, d, false)
}

fn shift_rec(
    st: &mut Store,
    m: &mut Lossy,
    e: ExprId,
    offset: u32,
    s: u32,
    d: u32,
    up: bool,
) -> ExprId {
    let s1 = s as u64 + offset as u64;
    if no_loose_from(st, e, s1) {
        return e;
    }
    if let Expr::BVar(i) = st.node(e) {
        let iv = i as u64;
        if iv < s1 {
            return e;
        }
        let k = if up {
            iv + d as u64
        } else if iv >= d as u64 {
            iv - d as u64
        } else {
            0
        };
        return bvar_at(st, k);
    }
    match m.get(e.0, raw(offset)) {
        Some(r) => ExprId(r),
        None => {
            let r = shift_node(st, m, e, offset, s, d, up);
            m.put(e.0, raw(offset), r.0);
            r
        }
    }
}

fn shift_node(
    st: &mut Store,
    m: &mut Lossy,
    e: ExprId,
    offset: u32,
    s: u32,
    d: u32,
    up: bool,
) -> ExprId {
    match st.node(e) {
        Expr::App(f, a) => {
            let f2 = shift_rec(st, m, f, offset, s, d, up);
            let a2 = shift_rec(st, m, a, offset, s, d, up);
            st.mk_app(f2, a2)
        }
        Expr::Lam(b) => {
            let dm = shift_rec(st, m, b.dom, offset, s, d, up);
            let body = shift_rec(st, m, b.body, offset + 1, s, d, up);
            st.mk_lam(b.name, b.info, dm, body)
        }
        Expr::Pi(b) => {
            let dm = shift_rec(st, m, b.dom, offset, s, d, up);
            let body = shift_rec(st, m, b.body, offset + 1, s, d, up);
            st.mk_pi(b.name, b.info, dm, body)
        }
        Expr::Let(l) => {
            let t = shift_rec(st, m, l.ty, offset, s, d, up);
            let v = shift_rec(st, m, l.value, offset, s, d, up);
            let body = shift_rec(st, m, l.body, offset + 1, s, d, up);
            st.mk_let(l.name, t, v, body)
        }
        Expr::Proj(p) => {
            let a = shift_rec(st, m, p.expr, offset, s, d, up);
            st.mk_proj(p.struct_name, p.index, a)
        }
        _ => e,
    }
}

// Abstraction.

/// Replaces the free variable `fvars[i]` with the bound variable `n - i - 1`, under the binders of `e` (`abstract(e, n, subst)`). The last item of `fvars` becomes the bound variable 0.
pub fn abstract_fvars(st: &mut Store, x: &mut Scratch, e: ExprId, fvars: &[ExprId]) -> ExprId {
    if fvars.len() == 0 || !has_fvar(st, e) {
        return e;
    }
    x.abs.clear();
    abs_rec(st, x, e, 0, fvars)
}

fn abs_rec(st: &mut Store, x: &mut Scratch, e: ExprId, offset: u32, fvars: &[ExprId]) -> ExprId {
    if !has_fvar(st, e) {
        return e;
    }
    if let Expr::FVar(_, _) = st.node(e) {
        let n = fvars.len();
        let mut i = n;
        let mut hit = n;
        while hit == n && i > 0 {
            i -= 1;
            if fvars[i] == e {
                hit = i;
            }
        }
        if hit == n {
            return e;
        }
        return bvar_at(st, offset as u64 + (n - hit - 1) as u64);
    }
    match x.abs.get(e.0, raw(offset)) {
        Some(r) => ExprId(r),
        None => {
            let r = abs_node(st, x, e, offset, fvars);
            x.abs.put(e.0, raw(offset), r.0);
            r
        }
    }
}

fn abs_node(st: &mut Store, x: &mut Scratch, e: ExprId, offset: u32, fvars: &[ExprId]) -> ExprId {
    match st.node(e) {
        Expr::App(f, a) => {
            let f2 = abs_rec(st, x, f, offset, fvars);
            let a2 = abs_rec(st, x, a, offset, fvars);
            st.mk_app(f2, a2)
        }
        Expr::Lam(b) => {
            let d = abs_rec(st, x, b.dom, offset, fvars);
            let body = abs_rec(st, x, b.body, offset + 1, fvars);
            st.mk_lam(b.name, b.info, d, body)
        }
        Expr::Pi(b) => {
            let d = abs_rec(st, x, b.dom, offset, fvars);
            let body = abs_rec(st, x, b.body, offset + 1, fvars);
            st.mk_pi(b.name, b.info, d, body)
        }
        Expr::Let(l) => {
            let t = abs_rec(st, x, l.ty, offset, fvars);
            let v = abs_rec(st, x, l.value, offset, fvars);
            let body = abs_rec(st, x, l.body, offset + 1, fvars);
            st.mk_let(l.name, t, v, body)
        }
        Expr::Proj(p) => {
            let a = abs_rec(st, x, p.expr, offset, fvars);
            st.mk_proj(p.struct_name, p.index, a)
        }
        _ => e,
    }
}

// Occurrence of a bound variable.

/// True if `e` has the loose bound variable `i` (`has_loose_bvar`).
pub fn has_loose_bvar(st: &Store, x: &mut Scratch, e: ExprId, i: u32) -> bool {
    if !has_loose_bvars(st, e) {
        return false;
    }
    x.occ.clear();
    occ_rec(st, &mut x.occ, e, i as u64, 0)
}

fn occ_rec(st: &Store, m: &mut Lossy, e: ExprId, i: u64, offset: u32) -> bool {
    let k = i + offset as u64;
    if no_loose_from(st, e, k) {
        return false;
    }
    if let Expr::BVar(j) = st.node(e) {
        return j as u64 == k;
    }
    // A node seen before at this offset did not have the variable, else the walk would have stopped.
    if m.contains(e.0, raw(offset)) {
        return false;
    }
    m.put(e.0, raw(offset), 1);
    match st.node(e) {
        Expr::App(f, a) => occ_rec(st, m, f, i, offset) || occ_rec(st, m, a, i, offset),
        Expr::Lam(b) => occ_rec(st, m, b.dom, i, offset) || occ_rec(st, m, b.body, i, offset + 1),
        Expr::Pi(b) => occ_rec(st, m, b.dom, i, offset) || occ_rec(st, m, b.body, i, offset + 1),
        Expr::Let(l) => {
            occ_rec(st, m, l.ty, i, offset)
                || occ_rec(st, m, l.value, i, offset)
                || occ_rec(st, m, l.body, i, offset + 1)
        }
        Expr::Proj(p) => occ_rec(st, m, p.expr, i, offset),
        _ => false,
    }
}

// Level instantiation.

/// Replaces the level parameters `ps[i]` with `ls[i]` in the sorts and constants of `e` (`instantiate_lparams`).
pub fn instantiate_lparams(
    st: &mut Store,
    x: &mut Scratch,
    e: ExprId,
    ps: &[NameId],
    ls: &[LevelId],
) -> ExprId {
    if ps.len() == 0 || !has_level_param(st, e) {
        return e;
    }
    x.lps.clear();
    lps_rec(st, x, e, ps, ls)
}

fn lps_rec(st: &mut Store, x: &mut Scratch, e: ExprId, ps: &[NameId], ls: &[LevelId]) -> ExprId {
    if !has_level_param(st, e) {
        return e;
    }
    match x.lps.get(e.0, 0) {
        Some(r) => ExprId(r),
        None => {
            let r = lps_node(st, x, e, ps, ls);
            x.lps.put(e.0, 0, r.0);
            r
        }
    }
}

fn lps_node(st: &mut Store, x: &mut Scratch, e: ExprId, ps: &[NameId], ls: &[LevelId]) -> ExprId {
    match st.node(e) {
        Expr::Sort(l) => {
            let l2 = level::instantiate(st, l, ps, ls);
            if l2 == l { e } else { st.mk_sort(l2) }
        }
        Expr::Const(n, list) => {
            let items = st.level_list_vec(list);
            let mut out: Vec<LevelId> = Vec::with_capacity(items.len());
            let mut changed = false;
            let mut i = 0;
            while i < items.len() {
                let l2 = level::instantiate(st, items[i], ps, ls);
                changed = changed || l2 != items[i];
                out.push(l2);
                i += 1;
            }
            if changed {
                let list2 = st.level_list(&out);
                st.mk_const(n, list2)
            } else {
                e
            }
        }
        Expr::App(f, a) => {
            let f2 = lps_rec(st, x, f, ps, ls);
            let a2 = lps_rec(st, x, a, ps, ls);
            st.mk_app(f2, a2)
        }
        Expr::Lam(b) => {
            let d = lps_rec(st, x, b.dom, ps, ls);
            let body = lps_rec(st, x, b.body, ps, ls);
            st.mk_lam(b.name, b.info, d, body)
        }
        Expr::Pi(b) => {
            let d = lps_rec(st, x, b.dom, ps, ls);
            let body = lps_rec(st, x, b.body, ps, ls);
            st.mk_pi(b.name, b.info, d, body)
        }
        Expr::Let(l) => {
            let t = lps_rec(st, x, l.ty, ps, ls);
            let v = lps_rec(st, x, l.value, ps, ls);
            let body = lps_rec(st, x, l.body, ps, ls);
            st.mk_let(l.name, t, v, body)
        }
        Expr::Proj(p) => {
            let a = lps_rec(st, x, p.expr, ps, ls);
            st.mk_proj(p.struct_name, p.index, a)
        }
        _ => e,
    }
}

// Application spines.

/// The head of an application spine (`get_app_fn`).
pub fn app_fn(st: &Store, e: ExprId) -> ExprId {
    let mut cur = e;
    let mut walking = true;
    while walking {
        match st.node(cur) {
            Expr::App(f, _) => cur = f,
            _ => walking = false,
        }
    }
    cur
}

/// The number of arguments of an application spine.
pub fn app_num_args(st: &Store, e: ExprId) -> usize {
    let mut cur = e;
    let mut n = 0;
    let mut walking = true;
    while walking {
        match st.node(cur) {
            Expr::App(f, _) => {
                cur = f;
                n += 1;
            }
            _ => walking = false,
        }
    }
    n
}

/// Writes the arguments of an application spine to `out`, from the last to the first, and gives the head (`get_app_rev_args`). `out` is cleared first.
pub fn app_rev_args(st: &Store, e: ExprId, out: &mut Vec<ExprId>) -> ExprId {
    out.truncate(0);
    let mut cur = e;
    let mut walking = true;
    while walking {
        match st.node(cur) {
            Expr::App(f, a) => {
                out.push(a);
                cur = f;
            }
            _ => walking = false,
        }
    }
    cur
}

/// Writes the arguments of an application spine to `out`, from the first to the last, and gives the head (`get_app_args`). `out` is cleared first.
pub fn app_args(st: &Store, e: ExprId, out: &mut Vec<ExprId>) -> ExprId {
    let head = app_rev_args(st, e, out);
    reverse(out);
    head
}

/// Reverses the items of `v` in place. The two indices are separate statements, because Charon cannot remove the overflow check of an index sum that is followed by an `IndexMut` call.
pub fn reverse(v: &mut [ExprId]) {
    let n = v.len();
    let mut i = 0;
    while i < n / 2 {
        let j = n - 1 - i;
        let a = v[i];
        let b = v[j];
        v[i] = b;
        v[j] = a;
        i += 1;
    }
}

/// `app_rev_args` that keeps the entries of `out` and pushes the arguments after them, last argument first. The head is the result.
pub fn app_rev_args_push(st: &Store, e: ExprId, out: &mut Vec<ExprId>) -> ExprId {
    let mut cur = e;
    let mut walking = true;
    while walking {
        match st.node(cur) {
            Expr::App(f, a) => {
                out.push(a);
                cur = f;
            }
            _ => walking = false,
        }
    }
    cur
}

/// The application of `f` to the arguments in reverse order: `f rev[n-1] ... rev[0]` (`mk_rev_app`).
pub fn mk_rev_app(st: &mut Store, f: ExprId, rev: &[ExprId]) -> ExprId {
    let mut r = f;
    let mut i = rev.len();
    while i > 0 {
        i -= 1;
        r = st.mk_app(r, rev[i]);
    }
    r
}

// Beta reduction.

/// True if `e` is an application with a lambda head (`is_head_beta`).
pub fn is_head_beta(st: &Store, e: ExprId) -> bool {
    match st.node(e) {
        Expr::App(_, _) => matches!(st.node(app_fn(st, e)), Expr::Lam(_)),
        _ => false,
    }
}

/// Applies `f` to the arguments `rev` in reverse order and beta-reduces the lambdas at the head (`apply_beta` without zeta).
pub fn apply_beta(st: &mut Store, x: &mut Scratch, f: ExprId, rev: &[ExprId]) -> ExprId {
    let num = rev.len();
    if num == 0 {
        return f;
    }
    let mut e = f;
    let mut i = 0;
    let mut walking = true;
    while walking && i + 1 < num {
        match st.node(e) {
            Expr::Lam(b) => {
                e = b.body;
                i += 1;
            }
            _ => walking = false,
        }
    }
    if walking {
        if let Expr::Lam(b) = st.node(e) {
            return instantiate(st, x, b.body, rev);
        }
    }
    let n = num - i;
    let body = instantiate(st, x, e, &rev[n..]);
    mk_rev_app(st, body, &rev[..n])
}

/// Beta-reduces at the head until the head is not a lambda (`head_beta_reduce`).
pub fn head_beta(st: &mut Store, x: &mut Scratch, e: ExprId) -> ExprId {
    let mut cur = e;
    let mut rev: Vec<ExprId> = Vec::new();
    while is_head_beta(st, cur) {
        let f = app_rev_args(st, cur, &mut rev);
        cur = apply_beta(st, x, f, &rev);
    }
    cur
}

/// Beta-reduces at the head only when the result is cheap: the body after the lambdas is closed or is a bound variable (`cheap_beta_reduce`).
pub fn cheap_beta_reduce(st: &mut Store, e: ExprId) -> ExprId {
    if !matches!(st.node(e), Expr::App(_, _)) {
        return e;
    }
    let mut f = app_fn(st, e);
    if !matches!(st.node(f), Expr::Lam(_)) {
        return e;
    }
    let mut args: Vec<ExprId> = Vec::new();
    app_args(st, e, &mut args);
    let mut i = 0;
    let mut walking = true;
    while walking && i < args.len() {
        match st.node(f) {
            Expr::Lam(b) => {
                f = b.body;
                i += 1;
            }
            _ => walking = false,
        }
    }
    if !has_loose_bvars(st, f) {
        return st.mk_apps(f, &args[i..]);
    }
    if let Expr::BVar(j) = st.node(f) {
        let j = j as usize;
        if j < i {
            let h = args[i - j - 1];
            return st.mk_apps(h, &args[i..]);
        }
    }
    e
}

// Alpha-equality.

/// True if the terms are equal up to binder names and binder info (`is_equal`, the `==` of the official kernel). The store hash does not mix binder names or binder info, so unequal hashes mean unequal terms.
pub fn expr_equal(st: &Store, x: &mut Scratch, a: ExprId, b: ExprId) -> bool {
    if a == b {
        return true;
    }
    // Without a binder, alpha-equal terms are the same node (spec perf/11.17).
    if !has_binder(st, a) || !has_binder(st, b) {
        return false;
    }
    x.eq.clear();
    eq_rec(st, &mut x.eq, a, b)
}

fn eq_rec(st: &Store, m: &mut Lossy, a: ExprId, b: ExprId) -> bool {
    if a == b {
        return true;
    }
    if st.hash(a) != st.hash(b) || a.kind() != b.kind() || !has_binder(st, a) {
        return false;
    }
    // A pair seen before is equal or the whole walk is already false (the cache of `expr_eq_fn`).
    if m.contains(a.0, b.0) {
        return true;
    }
    m.put(a.0, b.0, 1);
    match (st.node(a), st.node(b)) {
        (Expr::App(f1, a1), Expr::App(f2, a2)) => eq_rec(st, m, a1, a2) && eq_rec(st, m, f1, f2),
        (Expr::Lam(b1), Expr::Lam(b2)) => {
            eq_rec(st, m, b1.dom, b2.dom) && eq_rec(st, m, b1.body, b2.body)
        }
        (Expr::Pi(b1), Expr::Pi(b2)) => {
            eq_rec(st, m, b1.dom, b2.dom) && eq_rec(st, m, b1.body, b2.body)
        }
        (Expr::Let(l1), Expr::Let(l2)) => {
            eq_rec(st, m, l1.ty, l2.ty)
                && eq_rec(st, m, l1.value, l2.value)
                && eq_rec(st, m, l1.body, l2.body)
        }
        (Expr::Proj(p1), Expr::Proj(p2)) => {
            p1.struct_name == p2.struct_name
                && p1.index == p2.index
                && eq_rec(st, m, p1.expr, p2.expr)
        }
        // The other kinds are atoms. The store interns them, so unequal handles mean unequal atoms.
        _ => false,
    }
}
