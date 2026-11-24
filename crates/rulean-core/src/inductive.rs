//! Inductive declarations: `environment::add_inductive` and `add_inductive_fn` of `inductive.cpp` of the official kernel v4.35.0 (spec 06.2, 06.4 and 06.6).
//!
//! The checker makes the inductive types, the constructors and the recursors of a block from the types and the constructor types of the export. Then it compares the other fields of the export with the values that it made (spec 06.1). The environment gets the values that the checker made. A block with a nested occurrence goes through `nested.rs` first.

use alloc::vec::Vec;
use rulean_format::{Induct, Safety};
use rulean_store::ids::raw;
use rulean_store::{BinderInfo, Expr, ExprId, LevelId, LevelListId, NameId, Store};

use crate::env::{ConstInfo, ConstKind, CtorInfo, InductInfo, RecInfo, RuleInfo};
use crate::expr;
use crate::level;
use crate::memo::Memo;
use crate::names;
use crate::tc::{Checker, ErrorKind, Fault};

/// The kinds of search of `find`. Each kind has its own second key in the `occ` cache.
const FIND_IND: u32 = 0;
const FIND_AUX: u32 = 1;

/// The state of `add_inductive_fn` for one block.
#[derive(Debug)]
pub struct Ind {
    pub(crate) lparams: Vec<NameId>,
    /// The level parameters as levels (`m_levels`).
    pub(crate) levels: LevelListId,
    pub(crate) nparams: u32,
    pub(crate) safety: Safety,
    pub(crate) is_unsafe: bool,
    /// The names and the types of the inductive types, in block order.
    pub(crate) names: Vec<NameId>,
    pub(crate) types: Vec<ExprId>,
    /// The constructors of all types, in block order. The constructors of type `k` are at `cstart[k]` to `cstart[k + 1]`.
    pub(crate) cnames: Vec<NameId>,
    pub(crate) ctypes: Vec<ExprId>,
    pub(crate) cstart: Vec<usize>,
    /// The type of each constructor, and its position in the `ctors` array of the export.
    pub(crate) cowner: Vec<usize>,
    pub(crate) cexport: Vec<usize>,
    pub(crate) nfields: Vec<u32>,
    pub(crate) nindices: Vec<u32>,
    pub(crate) result_level: LevelId,
    pub(crate) is_not_zero: bool,
    /// A free variable for each parameter (`m_params`).
    pub(crate) params: Vec<ExprId>,
    /// A constant for each inductive type (`m_ind_cnsts`).
    pub(crate) consts: Vec<ExprId>,
    pub(crate) elim_level: LevelId,
    /// The name of the level parameter of the motives, if the recursor has one.
    pub(crate) elim_param: Option<NameId>,
    pub(crate) k_target: bool,
    pub(crate) is_rec: bool,
    pub(crate) is_reflexive: bool,
    /// The fields of `m_rec_infos`. The index variables of type `k` are at `istart[k]` to `istart[k + 1]`. The minor premises are in constructor order.
    pub(crate) motives: Vec<ExprId>,
    pub(crate) majors: Vec<ExprId>,
    pub(crate) idx: Vec<ExprId>,
    pub(crate) istart: Vec<usize>,
    pub(crate) minors: Vec<ExprId>,
    /// The reserved prefix `_nested`.
    pub(crate) nested: NameId,
    /// The results of `find`, keyed by the term and the kind of search.
    pub(crate) occ: Memo,
    /// The terms and binder offsets that `check_uniform_ind_occs` visited.
    pub(crate) seen: Memo,
    /// The number of types and of constructors of the export. The auxiliary types of `elim_nested_inductive_fn` come after them.
    pub(crate) norig: usize,
    pub(crate) nctors: usize,
    /// The parameters of `elim_nested_inductive_fn` (`m_params`).
    pub(crate) eparams: Vec<ExprId>,
    /// The nested occurrence `I Ds` of each auxiliary type, with the free variables of `eparams` (`m_nested_aux`).
    pub(crate) aux_nested: Vec<ExprId>,
    /// The next index of `mk_unique_name`.
    pub(crate) next_idx: u64,
    /// The parameter locals of the term that `replace_all_nested` or `restore_nested` changes.
    pub(crate) cur: Vec<ExprId>,
    /// The results of `replace_all_nested` and `restore_nested` for the current term.
    pub(crate) rep: Memo,
}

/// The position of `n` in `ns`, or the length of `ns`.
fn position(ns: &[NameId], n: NameId) -> usize {
    let mut i = 0;
    while i < ns.len() && ns[i] != n {
        i += 1;
    }
    i
}

/// The position of the constructor with the name `n` in `cs`, or the length of `cs`.
fn ctor_position(cs: &[rulean_format::Ctor], n: NameId) -> usize {
    let mut i = 0;
    while i < cs.len() && cs[i].name != n {
        i += 1;
    }
    i
}

/// The position of the recursor with the name `n` in `rs`, or the length of `rs`.
fn rec_position(rs: &[rulean_format::Rec], n: NameId) -> usize {
    let mut i = 0;
    while i < rs.len() && rs[i].name != n {
        i += 1;
    }
    i
}

/// True if the two name lists are equal.
fn names_eq(a: &[NameId], b: &[NameId]) -> bool {
    let mut i = 0;
    while i < a.len() && i < b.len() && a[i] == b[i] {
        i += 1;
    }
    a.len() == b.len() && i == a.len()
}

/// The names at the positions `a` to `b` of `v`.
fn copy_names(v: &[NameId], a: usize, b: usize) -> Vec<NameId> {
    let mut out = Vec::with_capacity(b - a);
    let mut i = a;
    while i < b {
        out.push(v[i]);
        i += 1;
    }
    out
}

/// The terms at the positions `a` to `b` of `v`.
fn copy_exprs(v: &[ExprId], a: usize, b: usize) -> Vec<ExprId> {
    let mut out = Vec::with_capacity(b - a);
    let mut i = a;
    while i < b {
        out.push(v[i]);
        i += 1;
    }
    out
}

/// True if `e` is the bound variable `k`.
fn is_bvar(st: &Store, e: ExprId, k: u32) -> bool {
    match st.node(e) {
        Expr::BVar(j) => j == k,
        _ => false,
    }
}

/// True if `args[i]` is the bound variable `offset - 1 - i` for each `i`. The caller makes sure that `offset` is at least the length of `args`.
fn params_are_bvars(st: &Store, args: &[ExprId], offset: u32) -> bool {
    let mut i = 0;
    while i < args.len() && is_bvar(st, args[i], offset - 1 - i as u32) {
        i += 1;
    }
    i == args.len()
}

/// The type of a free variable, or `e`.
fn fvar_type(st: &Store, e: ExprId) -> ExprId {
    match st.node(e) {
        Expr::FVar(_, ty) => ty,
        _ => e,
    }
}

/// The number of leading `pi` binders of `t`.
fn pi_arity(st: &Store, t0: ExprId) -> u32 {
    let mut t = t0;
    let mut n = 0;
    let mut go = true;
    while go {
        match st.node(t) {
            Expr::Pi(b) => {
                t = b.body;
                n += 1;
            }
            _ => go = false,
        }
    }
    n
}

impl Checker {
    /// `environment::add_inductive`. With `kernel_api`, the block has no recursors and the fields that the checker computes are not compared.
    pub fn add_inductive(&mut self, d: &Induct) -> Option<Fault> {
        let saved = self.env.len();
        let mut s = self.new_ind(d);
        let safety = if s.is_unsafe {
            Safety::Unsafe
        } else {
            Safety::Safe
        };
        self.begin(s.lparams.clone(), safety);
        if d.types.len() == 0 {
            let at = self.dummy;
            self.fail(ErrorKind::BadInductive, at);
        }
        if !self.bad() {
            self.read_block(&mut s, d);
        }
        self.inductive_core(&mut s);
        if !self.bad() && s.aux_nested.len() > 0 {
            self.restore_block(&mut s, saved);
        }
        if !self.bad() && !self.kernel_api {
            self.compare_export(&mut s, d);
        }
        if self.bad() {
            self.env.truncate(saved);
        }
        self.fault()
    }

    fn new_ind(&mut self, d: &Induct) -> Ind {
        let mut lparams = Vec::new();
        let mut nparams = 0;
        let mut safety = Safety::Safe;
        if d.types.len() > 0 {
            lparams = d.types[0].lparams.clone();
            nparams = d.types[0].num_params;
            safety = d.types[0].safety;
        }
        let levels = self.param_levels(&lparams);
        let anon = self.st.anon();
        let nested = self.st.name_str_bytes(anon, b"_nested");
        let zero = self.st.level_zero();
        Ind {
            lparams,
            levels,
            nparams,
            safety,
            is_unsafe: safety == Safety::Unsafe,
            names: Vec::new(),
            types: Vec::new(),
            cnames: Vec::new(),
            ctypes: Vec::new(),
            cstart: Vec::new(),
            cowner: Vec::new(),
            cexport: Vec::new(),
            nfields: Vec::new(),
            nindices: Vec::new(),
            result_level: zero,
            is_not_zero: false,
            params: Vec::new(),
            consts: Vec::new(),
            elim_level: zero,
            elim_param: None,
            k_target: false,
            is_rec: false,
            is_reflexive: false,
            motives: Vec::new(),
            majors: Vec::new(),
            idx: Vec::new(),
            istart: Vec::new(),
            minors: Vec::new(),
            nested,
            occ: Memo::new(),
            seen: Memo::new(),
            norig: 0,
            nctors: 0,
            eparams: Vec::new(),
            aux_nested: Vec::new(),
            next_idx: 1,
            cur: Vec::new(),
            rep: Memo::new(),
        }
    }

    /// `lparams_to_levels`.
    fn param_levels(&mut self, ps: &[NameId]) -> LevelListId {
        let mut ls = Vec::with_capacity(ps.len());
        let mut i = 0;
        while i < ps.len() {
            ls.push(self.st.level_param(ps[i]));
            i += 1;
        }
        self.st.level_list(&ls)
    }

    // The block of the export.

    /// Reads the types and the constructors of the block. The types of one block must have the same level parameters, parameter count and safety, and each constructor must be in the `ctors` array once.
    fn read_block(&mut self, s: &mut Ind, d: &Induct) {
        let mut k = 0;
        while k < d.types.len() && !self.bad() {
            self.read_type(s, d, k);
            k += 1;
        }
        s.cstart.push(s.cnames.len());
        if !self.bad() && s.cnames.len() != d.ctors.len() {
            let at = s.types[0];
            self.fail(ErrorKind::ExportMismatch, at);
        }
    }

    fn read_type(&mut self, s: &mut Ind, d: &Induct, k: usize) {
        let ty = d.types[k].ty;
        if !names_eq(&d.types[k].lparams, &s.lparams)
            || d.types[k].num_params != s.nparams
            || d.types[k].safety != s.safety
        {
            self.fail(ErrorKind::ExportMismatch, ty);
            return;
        }
        s.names.push(d.types[k].name);
        s.types.push(ty);
        s.cstart.push(s.cnames.len());
        let mut j = 0;
        while j < d.types[k].ctors.len() && !self.bad() {
            let n = d.types[k].ctors[j];
            self.read_ctor(s, d, k, n);
            j += 1;
        }
    }

    fn read_ctor(&mut self, s: &mut Ind, d: &Induct, k: usize, n: NameId) {
        let i = ctor_position(&d.ctors, n);
        if i == d.ctors.len() {
            let at = s.types[k];
            self.fail(ErrorKind::ExportMismatch, at);
            return;
        }
        let ty = d.ctors[i].ty;
        if !names_eq(&d.ctors[i].lparams, &s.lparams) || d.ctors[i].safety != s.safety {
            self.fail(ErrorKind::ExportMismatch, ty);
            return;
        }
        s.cnames.push(n);
        s.ctypes.push(ty);
        s.cowner.push(k);
        s.cexport.push(i);
    }

    /// The steps of `environment::add_inductive` and of `add_inductive_fn::operator()`.
    fn inductive_core(&mut self, s: &mut Ind) {
        if !self.bad() {
            self.check_block_terms(s);
        }
        if !self.bad() {
            self.check_uniform_ind_occs(s);
        }
        if !self.bad() {
            self.elim_nested(s);
        }
        if !self.bad() {
            let ls = s.lparams.clone();
            let at = s.types[0];
            self.check_duplicated_univ_params(&ls, at);
        }
        if !self.bad() {
            self.check_inductive_types(s);
        }
        if !self.bad() {
            self.declare_inductive_types(s);
        }
        if !self.bad() {
            self.check_constructors(s);
        }
        if !self.bad() {
            self.declare_constructors(s);
        }
        if !self.bad() {
            self.init_elim_level(s);
        }
        if !self.bad() {
            self.init_k_target(s);
        }
        if !self.bad() {
            self.mk_rec_infos(s);
        }
        if !self.bad() {
            self.declare_recursors(s);
        }
        if !self.bad() {
            self.check_recursors(s);
        }
    }

    // Searches in terms.

    /// `find` of `find_fn.h` for one kind of search. A free variable is a leaf.
    fn find(&mut self, s: &mut Ind, e: ExprId, what: u32) -> bool {
        match s.occ.get(e.0, raw(what)) {
            Some(v) => v == 1,
            None => self.find_core(s, e, what),
        }
    }

    fn find_core(&mut self, s: &mut Ind, e: ExprId, what: u32) -> bool {
        if !self.enter(e) {
            return false;
        }
        let mut r = self.find_here(s, e, what);
        if !r {
            r = self.find_children(s, e, what);
        }
        self.leave();
        s.occ.put(e.0, raw(what), if r { 1 } else { 2 });
        r
    }

    fn find_children(&mut self, s: &mut Ind, e: ExprId, what: u32) -> bool {
        match self.st.node(e) {
            Expr::App(f, a) => self.find(s, f, what) || self.find(s, a, what),
            Expr::Lam(b) => self.find(s, b.dom, what) || self.find(s, b.body, what),
            Expr::Pi(b) => self.find(s, b.dom, what) || self.find(s, b.body, what),
            Expr::Let(l) => {
                self.find(s, l.ty, what)
                    || self.find(s, l.value, what)
                    || self.find(s, l.body, what)
            }
            Expr::Proj(p) => self.find(s, p.expr, what),
            _ => false,
        }
    }

    fn find_here(&mut self, s: &mut Ind, e: ExprId, what: u32) -> bool {
        if what == FIND_IND {
            self.is_ind_occ(s, e)
        } else {
            self.is_aux_ref(s, e)
        }
    }

    /// `is_ind_occ`: `e` is a constant of the block.
    fn is_ind_occ(&self, s: &Ind, e: ExprId) -> bool {
        match self.st.node(e) {
            Expr::Const(n, _) => position(&s.names, n) < s.names.len(),
            _ => false,
        }
    }

    /// The test of `check_no_nested_aux`: a constant or a projection with a name under `_nested`.
    fn is_aux_ref(&self, s: &Ind, e: ExprId) -> bool {
        match self.st.node(e) {
            Expr::Const(n, _) => names::is_prefix_of(&self.st, s.nested, n),
            Expr::Proj(p) => names::is_prefix_of(&self.st, s.nested, p.struct_name),
            _ => false,
        }
    }

    /// `has_ind_occ`.
    pub(crate) fn has_ind_occ(&mut self, s: &mut Ind, e: ExprId) -> bool {
        self.find(s, e, FIND_IND)
    }

    // The checks of `environment::add_inductive`.

    /// `check_no_metavar_no_fvar` and `check_no_nested_aux` on each type and on each constructor type.
    fn check_block_terms(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            let ty = s.types[k];
            self.check_term_refs(s, ty);
            self.check_ctor_refs(s, k);
            k += 1;
        }
    }

    fn check_ctor_refs(&mut self, s: &mut Ind, k: usize) {
        let mut c = s.cstart[k];
        while c < s.cstart[k + 1] && !self.bad() {
            let t = s.ctypes[c];
            self.check_term_refs(s, t);
            c += 1;
        }
    }

    fn check_term_refs(&mut self, s: &mut Ind, e: ExprId) {
        self.check_no_fvar(e);
        if !self.bad() && self.find(s, e, FIND_AUX) {
            self.fail(ErrorKind::NestedPrefix, e);
        }
    }

    /// `check_uniform_ind_occs`: each occurrence of a type of the block in a constructor type has the levels of the block and the parameters as arguments.
    fn check_uniform_ind_occs(&mut self, s: &mut Ind) {
        let mut c = 0;
        while c < s.ctypes.len() && !self.bad() {
            let t = s.ctypes[c];
            self.uniform_occs(s, t, 0);
            c += 1;
        }
    }

    fn uniform_occs(&mut self, s: &mut Ind, e: ExprId, offset: u32) {
        if self.bad() || s.seen.contains(e.0, raw(offset)) {
            return;
        }
        s.seen.put(e.0, raw(offset), 1);
        if !self.enter(e) {
            return;
        }
        if self.uniform_occ_at(s, e, offset) {
            self.uniform_children(s, e, offset);
        }
        self.leave();
    }

    fn uniform_children(&mut self, s: &mut Ind, e: ExprId, offset: u32) {
        match self.st.node(e) {
            Expr::App(f, a) => {
                self.uniform_occs(s, f, offset);
                self.uniform_occs(s, a, offset);
            }
            Expr::Lam(b) => {
                self.uniform_occs(s, b.dom, offset);
                self.uniform_occs(s, b.body, offset + 1);
            }
            Expr::Pi(b) => {
                self.uniform_occs(s, b.dom, offset);
                self.uniform_occs(s, b.body, offset + 1);
            }
            Expr::Let(l) => {
                self.uniform_occs(s, l.ty, offset);
                self.uniform_occs(s, l.value, offset);
                self.uniform_occs(s, l.body, offset + 1);
            }
            Expr::Proj(p) => self.uniform_occs(s, p.expr, offset),
            _ => {}
        }
    }

    /// The function of `check_uniform_ind_occs` for one term. It gives true if the search must go into the children of `e`.
    fn uniform_occ_at(&mut self, s: &Ind, e: ExprId, offset: u32) -> bool {
        let f = expr::app_fn(&self.st, e);
        let (n, ls) = match self.st.node(f) {
            Expr::Const(n, ls) => (n, ls),
            _ => (self.st.anon(), s.levels),
        };
        if !self.is_constant(f) || position(&s.names, n) == s.names.len() {
            return true;
        }
        let mut args = Vec::new();
        expr::app_args(&self.st, e, &mut args);
        let np = s.nparams as usize;
        if args.len() > np {
            return true;
        }
        let ok = args.len() == np
            && offset as usize >= np
            && ls == s.levels
            && params_are_bvars(&self.st, &args, offset);
        if !ok {
            self.fail(ErrorKind::NonUniformOcc, e);
        }
        false
    }

    // Local declarations.

    /// The argument of a type annotation (`isOptParam`, `isAutoParam`, `isOutParam` and `isSemiOutParam`), if `e` is one.
    fn annotation_arg(&self, e: ExprId) -> Option<ExprId> {
        match self.st.node(e) {
            Expr::App(f, a) => match self.st.node(f) {
                Expr::Const(n, _) if n == self.b.out_param || n == self.b.semi_out_param => Some(a),
                Expr::App(g, a1) => match self.st.node(g) {
                    Expr::Const(n, _) if n == self.b.opt_param || n == self.b.auto_param => {
                        Some(a1)
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// `consumeTypeAnnotations`.
    pub(crate) fn consume_type_annotations(&self, e0: ExprId) -> ExprId {
        let mut e = e0;
        let mut go = true;
        while go {
            match self.annotation_arg(e) {
                Some(a) => e = a,
                None => go = false,
            }
        }
        e
    }

    /// `mk_local_decl_for`: a local for the binder of the `pi` term `t`, with the type annotations of the domain removed.
    fn local_for(&mut self, t: ExprId) -> ExprId {
        match self.st.node(t) {
            Expr::Pi(b) => {
                let ty = self.consume_type_annotations(b.dom);
                self.mk_local(b.name, b.info, ty, None)
            }
            _ => t,
        }
    }

    /// `mk_local_decl` with the default binder information.
    fn local_named(&mut self, n: NameId, ty: ExprId) -> ExprId {
        let t = self.consume_type_annotations(ty);
        self.mk_local(n, BinderInfo::Default, t, None)
    }

    /// The user name of a local.
    fn local_name(&self, x: ExprId) -> NameId {
        match self.st.node(x) {
            Expr::FVar(l, _) => self.lctx_name[l as usize],
            _ => self.st.anon(),
        }
    }

    /// The name `pre.s` with an anonymous `pre`.
    fn simple_name(&mut self, s: &[u8]) -> NameId {
        let anon = self.st.anon();
        self.st.name_str_bytes(anon, s)
    }

    /// Takes the `pi` binders of `whnf(t0)` with locals, with `whnf` after each binder. The locals go to `xs`.
    fn whnf_telescope(&mut self, t0: ExprId, xs: &mut Vec<ExprId>) -> ExprId {
        let mut t = self.whnf(t0);
        while self.is_pi(t) && !self.bad() {
            let x = self.local_for(t);
            xs.push(x);
            let b = self.binding(t).1;
            let bi = self.instantiate1(b, x);
            t = self.whnf(bi);
        }
        t
    }

    // `check_inductive_types`.

    fn check_inductive_types(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.check_inductive_type(s, k);
            k += 1;
        }
    }

    fn check_inductive_type(&mut self, s: &mut Ind, k: usize) {
        let n = s.names[k];
        let ty = s.types[k];
        self.check_name(n, ty);
        let rn = names::rec_name(&mut self.st, n);
        self.check_name(rn, ty);
        self.check_no_fvar(ty);
        if self.bad() {
            return;
        }
        self.check(ty);
        if self.bad() {
            return;
        }
        let (t, i, nidx) = self.type_telescope(s, k, ty);
        if self.bad() {
            return;
        }
        if i != s.nparams {
            self.fail(ErrorKind::BadInductive, ty);
            return;
        }
        let srt = self.ensure_sort(t, t);
        if self.bad() {
            return;
        }
        let l = self.sort_level(srt);
        if k == 0 {
            s.result_level = l;
            s.is_not_zero = level::is_not_zero(&self.st, l);
        } else if !level::is_equivalent(&mut self.st, &mut self.lc, l, s.result_level) {
            self.fail(ErrorKind::UniverseMismatch, ty);
            return;
        }
        s.nindices.push(nidx);
        let c = self.st.mk_const(n, s.levels);
        s.consts.push(c);
    }

    /// The `pi` binders of the type of type `k`, with `whnf` after each binder. It gives the result, the parameter count and the index count.
    fn type_telescope(&mut self, s: &mut Ind, k: usize, ty: ExprId) -> (ExprId, u32, u32) {
        let mut t = self.whnf(ty);
        let mut i: u32 = 0;
        let mut nidx: u32 = 0;
        while self.is_pi(t) && !self.bad() {
            let b = self.type_step(s, k, t, i);
            if i < s.nparams {
                i += 1;
            } else {
                nidx += 1;
            }
            t = self.whnf(b);
        }
        (t, i, nidx)
    }

    fn type_step(&mut self, s: &mut Ind, k: usize, t: ExprId, i: u32) -> ExprId {
        let (dom, body) = self.binding(t);
        if i >= s.nparams {
            let x = self.local_for(t);
            return self.instantiate1(body, x);
        }
        if k == 0 {
            let p = self.local_for(t);
            s.params.push(p);
            return self.instantiate1(body, p);
        }
        let p = s.params[i as usize];
        let pt = fvar_type(&self.st, p);
        if !self.is_def_eq(dom, pt) && !self.bad() {
            self.fail(ErrorKind::BadInductive, t);
        }
        self.instantiate1(body, p)
    }

    // `declare_inductive_types`.

    fn declare_inductive_types(&mut self, s: &mut Ind) {
        s.is_rec = self.block_is_rec(s);
        s.is_reflexive = self.block_is_reflexive(s);
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.declare_type(s, k);
            k += 1;
        }
    }

    /// `is_rec`: a constructor has a field whose type has a type of the block.
    fn block_is_rec(&mut self, s: &mut Ind) -> bool {
        let mut c = 0;
        while c < s.ctypes.len() && !self.ctor_is_rec(s, c, false) {
            c += 1;
        }
        c < s.ctypes.len()
    }

    /// `is_reflexive`: a constructor has a field whose type is a `pi` term with a type of the block.
    fn block_is_reflexive(&mut self, s: &mut Ind) -> bool {
        let mut c = 0;
        while c < s.ctypes.len() && !self.ctor_is_rec(s, c, true) {
            c += 1;
        }
        c < s.ctypes.len()
    }

    /// The test of `is_rec`, or of `is_reflexive` if `pi_only` is true, for one constructor. The official kernel puts locals in the binders for `is_reflexive`. The test reads only the constants and the head of the domains, so the result is the same without locals.
    fn ctor_is_rec(&mut self, s: &mut Ind, c: usize, pi_only: bool) -> bool {
        let mut t = s.ctypes[c];
        let mut found = false;
        while !found && self.is_pi(t) {
            let (dom, body) = self.binding(t);
            found = (!pi_only || self.is_pi(dom)) && self.has_ind_occ(s, dom);
            t = body;
        }
        found
    }

    fn declare_type(&mut self, s: &mut Ind, k: usize) {
        let n = s.names[k];
        let ty = s.types[k];
        self.check_name(n, ty);
        if self.bad() {
            return;
        }
        let info = InductInfo {
            nparams: s.nparams,
            nindices: s.nindices[k],
            all: s.names.clone(),
            ctors: copy_names(&s.cnames, s.cstart[k], s.cstart[k + 1]),
            nnested: s.aux_nested.len() as u32,
            is_rec: s.is_rec,
            is_reflexive: s.is_reflexive,
        };
        self.add_const(n, s.lparams.clone(), ty, s.safety, ConstKind::Induct(info));
    }

    // `check_constructors`.

    /// `is_valid_ind_app(t, k)`: `t` is `I As is` where `I` is the type `k`, `As` are the parameters and `is` has no type of the block.
    fn is_valid_ind_app(&mut self, s: &mut Ind, t: ExprId, k: usize) -> bool {
        let mut args = Vec::new();
        let f = expr::app_args(&self.st, t, &mut args);
        let c = s.consts[k];
        if !self.eq(f, c) || args.len() != (s.nparams + s.nindices[k]) as usize {
            return false;
        }
        self.params_match(s, &args) && self.indices_clean(s, &args)
    }

    fn params_match(&mut self, s: &Ind, args: &[ExprId]) -> bool {
        let n = s.params.len();
        let mut i = 0;
        while i < n && self.eq(s.params[i], args[i]) {
            i += 1;
        }
        i == n
    }

    fn indices_clean(&mut self, s: &mut Ind, args: &[ExprId]) -> bool {
        let mut i = s.nparams as usize;
        while i < args.len() && !self.has_ind_occ(s, args[i]) {
            i += 1;
        }
        i == args.len()
    }

    /// `is_valid_ind_app(t)`: the type `k` for which `t` is a valid application, or the number of types.
    fn valid_ind_app_index(&mut self, s: &mut Ind, t: ExprId) -> usize {
        let n = s.names.len();
        let mut k = 0;
        while k < n && !self.is_valid_ind_app(s, t, k) {
            k += 1;
        }
        k
    }

    /// `is_rec_argument`.
    fn is_rec_argument(&mut self, s: &mut Ind, t0: ExprId) -> bool {
        let mut xs = Vec::new();
        let t = self.whnf_telescope(t0, &mut xs);
        !self.bad() && self.valid_ind_app_index(s, t) < s.names.len()
    }

    /// `check_positivity`.
    fn check_positivity(&mut self, s: &mut Ind, t0: ExprId) {
        if !self.enter(t0) {
            return;
        }
        let t = self.whnf(t0);
        if !self.bad() && self.has_ind_occ(s, t) {
            self.positivity_occ(s, t);
        }
        self.leave();
    }

    fn positivity_occ(&mut self, s: &mut Ind, t: ExprId) {
        if self.is_pi(t) {
            let (dom, body) = self.binding(t);
            if self.has_ind_occ(s, dom) {
                self.fail(ErrorKind::NonPositive, t);
                return;
            }
            let x = self.local_for(t);
            let b = self.instantiate1(body, x);
            self.check_positivity(s, b);
        } else if self.valid_ind_app_index(s, t) == s.names.len() && !self.bad() {
            self.fail(ErrorKind::NonPositive, t);
        }
    }

    fn check_constructors(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.check_ctors_of(s, k);
            k += 1;
        }
    }

    fn check_ctors_of(&mut self, s: &mut Ind, k: usize) {
        let mut c = s.cstart[k];
        while c < s.cstart[k + 1] && !self.bad() {
            self.check_ctor(s, k, c);
            c += 1;
        }
    }

    fn check_ctor(&mut self, s: &mut Ind, k: usize, c: usize) {
        let n = s.cnames[c];
        let t = s.ctypes[c];
        let first = s.cstart[k];
        if position(&s.cnames[first..c], n) < c - first {
            self.fail(ErrorKind::BadCtor, t);
            return;
        }
        self.check_name(n, t);
        self.check_no_fvar(t);
        if self.bad() {
            return;
        }
        self.check(t);
        if self.bad() {
            return;
        }
        let r = self.ctor_telescope(s, t);
        if !self.bad() && !self.is_valid_ind_app(s, r, k) {
            self.fail(ErrorKind::BadCtor, t);
        }
    }

    /// The `pi` binders of a constructor type, with no reduction, and the checks of each binder.
    fn ctor_telescope(&mut self, s: &mut Ind, t0: ExprId) -> ExprId {
        let mut t = t0;
        let mut i: u32 = 0;
        while self.is_pi(t) && !self.bad() {
            t = self.ctor_step(s, t, i);
            i += 1;
        }
        t
    }

    fn ctor_step(&mut self, s: &mut Ind, t: ExprId, i: u32) -> ExprId {
        let (dom, body) = self.binding(t);
        if i < s.nparams {
            let p = s.params[i as usize];
            let pt = fvar_type(&self.st, p);
            if !self.is_def_eq(dom, pt) && !self.bad() {
                self.fail(ErrorKind::CtorParamMismatch, t);
            }
            return self.instantiate1(body, p);
        }
        let ty = self.infer(dom);
        let srt = self.ensure_sort(ty, dom);
        if self.bad() {
            return t;
        }
        let l = self.sort_level(srt);
        let r = s.result_level;
        let fits = level::is_geq(&mut self.st, &mut self.lc, r, l)
            || level::normalizes_to_zero(&self.st, r);
        if !fits {
            self.fail(ErrorKind::UniverseTooBig, t);
            return t;
        }
        if !s.is_unsafe {
            self.check_positivity(s, dom);
        }
        let x = self.local_for(t);
        self.instantiate1(body, x)
    }

    // `declare_constructors`.

    fn declare_constructors(&mut self, s: &mut Ind) {
        let mut c = 0;
        while c < s.ctypes.len() && !self.bad() {
            self.declare_ctor(s, c);
            c += 1;
        }
    }

    fn declare_ctor(&mut self, s: &mut Ind, c: usize) {
        let n = s.cnames[c];
        let t = s.ctypes[c];
        let k = s.cowner[c];
        let arity = pi_arity(&self.st, t);
        let nfields = if arity >= s.nparams {
            arity - s.nparams
        } else {
            0
        };
        s.nfields.push(nfields);
        self.check_name(n, t);
        if self.bad() {
            return;
        }
        let info = CtorInfo {
            induct: s.names[k],
            cidx: (c - s.cstart[k]) as u32,
            nparams: s.nparams,
            nfields,
        };
        self.add_const(n, s.lparams.clone(), t, s.safety, ConstKind::Ctor(info));
    }

    // `init_elim_level` and `init_K_target`.

    fn init_elim_level(&mut self, s: &mut Ind) {
        let zero_only = self.elim_only_at_universe_zero(s);
        if self.bad() {
            return;
        }
        if zero_only {
            s.elim_level = self.st.level_zero();
            s.elim_param = None;
        } else {
            let u = self.fresh_univ(s);
            s.elim_level = self.st.level_param(u);
            s.elim_param = Some(u);
        }
    }

    /// The name of the level parameter of the motives: `u`, or `u_1`, `u_2` and so on if `u` is a level parameter of the block.
    fn fresh_univ(&mut self, s: &Ind) -> NameId {
        let base = self.simple_name(b"u");
        let mut u = base;
        let mut i: u64 = 1;
        while position(&s.lparams, u) < s.lparams.len() {
            u = names::append_index(&mut self.st, base, i);
            i += 1;
        }
        u
    }

    /// `elim_only_at_universe_zero`.
    fn elim_only_at_universe_zero(&mut self, s: &mut Ind) -> bool {
        if s.is_not_zero {
            return false;
        }
        if s.names.len() > 1 {
            return true;
        }
        let n = s.cstart[1] - s.cstart[0];
        if n != 1 {
            return n > 1;
        }
        let mut to_check = Vec::new();
        let t = self.non_prop_fields(s, &mut to_check);
        if self.bad() {
            return false;
        }
        let mut args = Vec::new();
        expr::app_args(&self.st, t, &mut args);
        !self.all_occur(&to_check, &args)
    }

    /// The fields of the only constructor whose type is not a proposition. Each binder gets a new local, the parameters too.
    fn non_prop_fields(&mut self, s: &Ind, out: &mut Vec<ExprId>) -> ExprId {
        let mut t = s.ctypes[0];
        let mut i: u32 = 0;
        while self.is_pi(t) && !self.bad() {
            t = self.non_prop_step(s, t, i, out);
            i += 1;
        }
        t
    }

    fn non_prop_step(&mut self, s: &Ind, t: ExprId, i: u32, out: &mut Vec<ExprId>) -> ExprId {
        let (dom, body) = self.binding(t);
        let x = self.local_for(t);
        if i >= s.nparams {
            let ty = self.infer(dom);
            let srt = self.ensure_sort(ty, dom);
            if !self.bad() {
                let l = self.sort_level(srt);
                if !level::normalizes_to_zero(&self.st, l) {
                    out.push(x);
                }
            }
        }
        self.instantiate1(body, x)
    }

    /// True if each term of `xs` is one of `args`.
    fn all_occur(&mut self, xs: &[ExprId], args: &[ExprId]) -> bool {
        let mut i = 0;
        while i < xs.len() && self.occurs_in(xs[i], args) {
            i += 1;
        }
        i == xs.len()
    }

    fn occurs_in(&mut self, x: ExprId, args: &[ExprId]) -> bool {
        let mut j = 0;
        while j < args.len() && !self.eq(args[j], x) {
            j += 1;
        }
        j < args.len()
    }

    /// `init_K_target`: one type, a proposition, one constructor and no fields.
    fn init_k_target(&mut self, s: &mut Ind) {
        let r = s.result_level;
        s.k_target = s.names.len() == 1
            && level::normalizes_to_zero(&self.st, r)
            && s.cstart[1] - s.cstart[0] == 1
            && pi_arity(&self.st, s.ctypes[0]) <= s.nparams;
    }

    // `mk_rec_infos`.

    fn mk_rec_infos(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.mk_motive(s, k);
            k += 1;
        }
        s.istart.push(s.idx.len());
        let mut c = 0;
        while c < s.ctypes.len() && !self.bad() {
            self.mk_minor(s, c);
            c += 1;
        }
    }

    /// The indices, the major premise and the motive of type `k`.
    fn mk_motive(&mut self, s: &mut Ind, k: usize) {
        s.istart.push(s.idx.len());
        let ty = s.types[k];
        self.index_telescope(s, ty);
        if self.bad() {
            return;
        }
        let first = s.istart[k];
        let indices = copy_exprs(&s.idx, first, s.idx.len());
        let a = self.st.mk_apps(s.consts[k], &s.params);
        let it = self.st.mk_apps(a, &indices);
        let tname = self.simple_name(b"t");
        let major = self.local_named(tname, it);
        let srt = self.st.mk_sort(s.elim_level);
        let c1 = self.mk_binding(&[major], srt, false, false);
        let cty = self.mk_binding(&indices, c1, false, false);
        let mut cname = self.simple_name(b"motive");
        if s.names.len() > 1 {
            cname = names::append_index(&mut self.st, cname, (k + 1) as u64);
        }
        let m = self.local_named(cname, cty);
        s.majors.push(major);
        s.motives.push(m);
    }

    /// The `pi` binders of the type of an inductive type, with `whnf` after each binder. The parameters get the parameter locals, and the indices get new locals in `s.idx`.
    fn index_telescope(&mut self, s: &mut Ind, ty: ExprId) {
        let mut t = self.whnf(ty);
        let mut i: u32 = 0;
        while self.is_pi(t) && !self.bad() {
            let b = self.index_step(s, t, i);
            i += 1;
            t = self.whnf(b);
        }
    }

    fn index_step(&mut self, s: &mut Ind, t: ExprId, i: u32) -> ExprId {
        let body = self.binding(t).1;
        if i < s.nparams {
            let p = s.params[i as usize];
            return self.instantiate1(body, p);
        }
        let x = self.local_for(t);
        s.idx.push(x);
        self.instantiate1(body, x)
    }

    /// The fields `b_u` of constructor `c`, and the recursive fields `u` if `want_u` is true. It gives the result type of the constructor with the parameter locals and the field locals.
    fn ctor_fields(
        &mut self,
        s: &mut Ind,
        c: usize,
        b_u: &mut Vec<ExprId>,
        u: &mut Vec<ExprId>,
        want_u: bool,
    ) -> ExprId {
        let mut t = s.ctypes[c];
        let mut i: u32 = 0;
        while self.is_pi(t) && !self.bad() {
            t = self.field_step(s, t, i, b_u, u, want_u);
            i += 1;
        }
        t
    }

    fn field_step(
        &mut self,
        s: &mut Ind,
        t: ExprId,
        i: u32,
        b_u: &mut Vec<ExprId>,
        u: &mut Vec<ExprId>,
        want_u: bool,
    ) -> ExprId {
        let (dom, body) = self.binding(t);
        if i < s.nparams {
            let p = s.params[i as usize];
            return self.instantiate1(body, p);
        }
        let x = self.local_for(t);
        b_u.push(x);
        if want_u && self.is_rec_argument(s, dom) {
            u.push(x);
        }
        self.instantiate1(body, x)
    }

    /// `get_I_indices`: the type of the block that `t` is an application of, with its indices in `out`.
    fn get_i_indices(&mut self, s: &mut Ind, t: ExprId, out: &mut Vec<ExprId>) -> usize {
        let k = self.valid_ind_app_index(s, t);
        if k == s.names.len() {
            self.fail(ErrorKind::BadInductive, t);
            return 0;
        }
        let mut args = Vec::new();
        expr::app_args(&self.st, t, &mut args);
        let mut i = s.nparams as usize;
        while i < args.len() {
            out.push(args[i]);
            i += 1;
        }
        k
    }

    /// The `pi` binders of the type of the recursive field `ui`. The binder locals go to `xs` and the indices of the result to `it_indices`. It gives the type of the block of the result.
    fn rec_arg_telescope(
        &mut self,
        s: &mut Ind,
        ui: ExprId,
        xs: &mut Vec<ExprId>,
        it_indices: &mut Vec<ExprId>,
    ) -> usize {
        let ty = self.infer(ui);
        let t = self.whnf_telescope(ty, xs);
        if self.bad() {
            return 0;
        }
        self.get_i_indices(s, t, it_indices)
    }

    /// `C it_indices (c As b_u)` for constructor `c`.
    fn intro_app(&mut self, s: &Ind, c: usize, b_u: &[ExprId]) -> ExprId {
        let f = self.st.mk_const(s.cnames[c], s.levels);
        let a = self.st.mk_apps(f, &s.params);
        self.st.mk_apps(a, b_u)
    }

    /// The minor premise of constructor `c`.
    fn mk_minor(&mut self, s: &mut Ind, c: usize) {
        let mut b_u = Vec::new();
        let mut u = Vec::new();
        let t = self.ctor_fields(s, c, &mut b_u, &mut u, true);
        let mut it_indices = Vec::new();
        let it = self.get_i_indices(s, t, &mut it_indices);
        if self.bad() {
            return;
        }
        let c0 = self.st.mk_apps(s.motives[it], &it_indices);
        let intro = self.intro_app(s, c, &b_u);
        let capp = self.st.mk_app(c0, intro);
        let mut v = Vec::new();
        self.mk_ihs(s, &u, &mut v);
        if self.bad() {
            return;
        }
        let inner = self.mk_binding(&v, capp, false, false);
        let mty = self.mk_binding(&b_u, inner, false, false);
        let k = s.cowner[c];
        let anon = self.st.anon();
        let mname = names::replace_prefix(&mut self.st, s.cnames[c], s.names[k], anon);
        let m = self.local_named(mname, mty);
        s.minors.push(m);
    }

    fn mk_ihs(&mut self, s: &mut Ind, u: &[ExprId], v: &mut Vec<ExprId>) {
        let mut i = 0;
        while i < u.len() && !self.bad() {
            let ih = self.mk_ih(s, u[i]);
            v.push(ih);
            i += 1;
        }
    }

    /// The induction hypothesis of the recursive field `ui`: a local of type `Π xs, C it_indices (ui xs)`.
    fn mk_ih(&mut self, s: &mut Ind, ui: ExprId) -> ExprId {
        let mut xs = Vec::new();
        let mut it_indices = Vec::new();
        let it = self.rec_arg_telescope(s, ui, &mut xs, &mut it_indices);
        if self.bad() {
            return self.dummy;
        }
        let c0 = self.st.mk_apps(s.motives[it], &it_indices);
        let uapp = self.st.mk_apps(ui, &xs);
        let capp = self.st.mk_app(c0, uapp);
        let vty = self.mk_binding(&xs, capp, false, false);
        let un = self.local_name(ui);
        let ihn = names::append_after(&mut self.st, un, b"_ih");
        self.local_named(ihn, vty)
    }

    // `declare_recursors`.

    /// `get_rec_levels`.
    fn rec_levels(&mut self, s: &Ind) -> LevelListId {
        if s.elim_param.is_none() {
            return s.levels;
        }
        let items = self.st.level_list_vec(s.levels);
        let mut ls = Vec::with_capacity(items.len() + 1);
        ls.push(s.elim_level);
        let mut i = 0;
        while i < items.len() {
            ls.push(items[i]);
            i += 1;
        }
        self.st.level_list(&ls)
    }

    /// `get_rec_lparams`.
    fn rec_lparams(s: &Ind) -> Vec<NameId> {
        match s.elim_param {
            Some(u) => {
                let mut ps = Vec::with_capacity(s.lparams.len() + 1);
                ps.push(u);
                let mut i = 0;
                while i < s.lparams.len() {
                    ps.push(s.lparams[i]);
                    i += 1;
                }
                ps
            }
            None => s.lparams.clone(),
        }
    }

    fn declare_recursors(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.declare_rec(s, k);
            k += 1;
        }
    }

    fn declare_rec(&mut self, s: &mut Ind, k: usize) {
        let indices = copy_exprs(&s.idx, s.istart[k], s.istart[k + 1]);
        let major = s.majors[k];
        let c0 = self.st.mk_apps(s.motives[k], &indices);
        let capp = self.st.mk_app(c0, major);
        let r1 = self.mk_binding(&[major], capp, false, false);
        let r2 = self.mk_binding(&indices, r1, false, false);
        let r3 = self.mk_binding(&s.minors, r2, false, false);
        let r4 = self.mk_binding(&s.motives, r3, false, false);
        let r5 = self.mk_binding(&s.params, r4, false, false);
        let rec_ty = self.infer_implicit(r5);
        let mut rules = Vec::new();
        self.mk_rec_rules(s, k, &mut rules);
        let rn = names::rec_name(&mut self.st, s.names[k]);
        self.check_name(rn, rec_ty);
        if self.bad() {
            return;
        }
        let info = RecInfo {
            all: s.names.clone(),
            nparams: s.nparams,
            nindices: s.nindices[k],
            nmotives: s.motives.len() as u32,
            nminors: s.minors.len() as u32,
            rules,
            k: s.k_target,
        };
        let lps = Checker::rec_lparams(s);
        self.add_const(rn, lps, rec_ty, s.safety, ConstKind::Rec(info));
    }

    /// `infer_implicit(t, true)` of the C++ kernel. A binder with the default binder information becomes implicit when its variable occurs in the domain of a later explicit binder. An occurrence in the domain of a later implicit binder also counts when the variable of that binder occurs in the same way. The body after the last binder does not count. The binder information has no effect on the check, but the elaborator reads it from the recursor in the in-process mode (spec 09.6).
    fn infer_implicit(&mut self, t: ExprId) -> ExprId {
        let mut bs = Vec::new();
        let mut e = t;
        while let Expr::Pi(b) = self.st.node(e) {
            bs.push(b);
            e = b.body;
        }
        let n = bs.len();
        // `reach[q]` is true when the variable of binder `q` occurs in the domain of a later explicit binder, directly or through implicit binders.
        let mut reach = alloc::vec![false; n];
        let mut q = n;
        while q > 0 {
            q -= 1;
            let mut r = q + 1;
            while r < n && !reach[q] {
                let shift = (r - q - 1) as u32;
                if (bs[r].info == BinderInfo::Default || reach[r])
                    && expr::has_loose_bvar(&self.st, &mut self.x, bs[r].dom, shift)
                {
                    reach[q] = true;
                }
                r += 1;
            }
            if bs[q].info == BinderInfo::Default && reach[q] {
                bs[q].info = BinderInfo::Implicit;
            }
        }
        let mut q = n;
        while q > 0 {
            q -= 1;
            let b = bs[q];
            e = self.st.mk_pi(b.name, b.info, b.dom, e);
        }
        e
    }

    /// `mk_rec_rules`. The minor premise of constructor `c` is `s.minors[c]`.
    fn mk_rec_rules(&mut self, s: &mut Ind, k: usize, rules: &mut Vec<RuleInfo>) {
        let lvls = self.rec_levels(s);
        let mut c = s.cstart[k];
        while c < s.cstart[k + 1] && !self.bad() {
            let r = self.mk_rec_rule(s, c, lvls);
            rules.push(r);
            c += 1;
        }
    }

    fn mk_rec_rule(&mut self, s: &mut Ind, c: usize, lvls: LevelListId) -> RuleInfo {
        let mut b_u = Vec::new();
        let mut u = Vec::new();
        self.ctor_fields(s, c, &mut b_u, &mut u, true);
        let mut v = Vec::new();
        self.mk_rec_calls(s, &u, lvls, &mut v);
        let e0 = self.st.mk_apps(s.minors[c], &b_u);
        let e_app = self.st.mk_apps(e0, &v);
        let r1 = self.mk_binding(&b_u, e_app, true, false);
        let r2 = self.mk_binding(&s.minors, r1, true, false);
        let r3 = self.mk_binding(&s.motives, r2, true, false);
        let rhs = self.mk_binding(&s.params, r3, true, false);
        RuleInfo {
            ctor: s.cnames[c],
            nfields: b_u.len() as u32,
            rhs,
        }
    }

    fn mk_rec_calls(&mut self, s: &mut Ind, u: &[ExprId], lvls: LevelListId, v: &mut Vec<ExprId>) {
        let mut i = 0;
        while i < u.len() && !self.bad() {
            let r = self.mk_rec_call(s, u[i], lvls);
            v.push(r);
            i += 1;
        }
    }

    /// `λ xs, I.rec As Cs minors it_indices (ui xs)` for the recursive field `ui`.
    fn mk_rec_call(&mut self, s: &mut Ind, ui: ExprId, lvls: LevelListId) -> ExprId {
        let mut xs = Vec::new();
        let mut it_indices = Vec::new();
        let it = self.rec_arg_telescope(s, ui, &mut xs, &mut it_indices);
        if self.bad() {
            return self.dummy;
        }
        let rn = names::rec_name(&mut self.st, s.names[it]);
        let f = self.st.mk_const(rn, lvls);
        let a1 = self.st.mk_apps(f, &s.params);
        let a2 = self.st.mk_apps(a1, &s.motives);
        let a3 = self.st.mk_apps(a2, &s.minors);
        let a4 = self.st.mk_apps(a3, &it_indices);
        let uapp = self.st.mk_apps(ui, &xs);
        let app = self.st.mk_app(a4, uapp);
        self.mk_binding(&xs, app, true, false)
    }

    // `check_recursors`.

    fn check_recursors(&mut self, s: &mut Ind) {
        let mut k = 0;
        while k < s.names.len() && !self.bad() {
            self.check_rec(s, k);
            k += 1;
        }
    }

    fn check_rec(&mut self, s: &mut Ind, k: usize) {
        let rn = names::rec_name(&mut self.st, s.names[k]);
        let slot = self.env.find(rn);
        if slot == 0 {
            let at = s.types[k];
            self.fail(ErrorKind::BadInductive, at);
            return;
        }
        let ty = self.env.at(slot).ty;
        let saved = self.lparams.clone();
        self.lparams = Checker::rec_lparams(s);
        self.check(ty);
        self.lparams = saved;
        if self.bad() {
            return;
        }
        let lvls = self.rec_levels(s);
        let f = self.st.mk_const(rn, lvls);
        let a1 = self.st.mk_apps(f, &s.params);
        let a2 = self.st.mk_apps(a1, &s.motives);
        let pre = self.st.mk_apps(a2, &s.minors);
        let mut c = s.cstart[k];
        while c < s.cstart[k + 1] && !self.bad() {
            self.check_rec_rule(s, pre, c);
            c += 1;
        }
    }

    /// The computation rule of constructor `c` keeps the type: the type of `whnf(lhs)` is the type of `lhs`.
    fn check_rec_rule(&mut self, s: &mut Ind, pre: ExprId, c: usize) {
        let mut b_u = Vec::new();
        let mut u = Vec::new();
        let t = self.ctor_fields(s, c, &mut b_u, &mut u, false);
        let mut it_indices = Vec::new();
        self.get_i_indices(s, t, &mut it_indices);
        if self.bad() {
            return;
        }
        let intro = self.intro_app(s, c, &b_u);
        let a = self.st.mk_apps(pre, &it_indices);
        let lhs = self.st.mk_app(a, intro);
        let expected = self.infer(lhs);
        let reduct = self.whnf(lhs);
        let actual = self.infer(reduct);
        if !self.bad() && !self.is_def_eq(actual, expected) && !self.bad() {
            self.fail(ErrorKind::BadRecRule, lhs);
        }
    }

    // The comparison with the export (spec 06.1).

    /// The comparison of the export with the declarations in the environment. The export must have the types and the constructors of the block, and a recursor for each type and each auxiliary type.
    fn compare_export(&mut self, s: &mut Ind, d: &Induct) {
        let mut k = 0;
        while k < s.norig && !self.bad() {
            self.compare_type(s, d, k);
            k += 1;
        }
        let mut c = 0;
        while c < s.nctors && !self.bad() {
            self.compare_ctor(s, d, c);
            c += 1;
        }
        if !self.bad() && d.recs.len() != s.names.len() {
            let at = s.types[0];
            self.fail(ErrorKind::ExportMismatch, at);
        }
        let mut j = 0;
        while j < s.names.len() && !self.bad() {
            let rn = self.block_rec_name(s, j);
            self.compare_rec(s, d, j, rn);
            j += 1;
        }
    }

    /// The name of recursor `j` of the block: `I.rec` for a type `I`, and `main.rec_i` for auxiliary type `i`.
    fn block_rec_name(&mut self, s: &Ind, j: usize) -> NameId {
        if j < s.norig {
            return names::rec_name(&mut self.st, s.names[j]);
        }
        let main = names::rec_name(&mut self.st, s.names[0]);
        names::append_index(&mut self.st, main, (j - s.norig + 1) as u64)
    }

    fn compare_type(&mut self, s: &Ind, d: &Induct, k: usize) {
        let ok = d.types[k].num_indices == s.nindices[k]
            && names_eq(&d.types[k].all, &s.names[..s.norig])
            && d.types[k].num_nested as usize == s.aux_nested.len()
            && d.types[k].is_rec == s.is_rec
            && d.types[k].is_reflexive == s.is_reflexive;
        if !ok {
            let at = s.types[k];
            self.fail(ErrorKind::ExportMismatch, at);
        }
    }

    fn compare_ctor(&mut self, s: &Ind, d: &Induct, c: usize) {
        let i = s.cexport[c];
        let k = s.cowner[c];
        let slot = self.env.find(s.cnames[c]);
        let ours = if slot == 0 {
            self.dummy
        } else {
            self.env.at(slot).ty
        };
        let ok = d.ctors[i].induct == s.names[k]
            && d.ctors[i].cidx == (c - s.cstart[k]) as u32
            && d.ctors[i].num_params == s.nparams
            && d.ctors[i].num_fields == s.nfields[c]
            && slot != 0
            && self.eq(d.ctors[i].ty, ours);
        if !ok {
            let at = d.ctors[i].ty;
            self.fail(ErrorKind::ExportMismatch, at);
        }
    }

    fn compare_rec(&mut self, s: &Ind, d: &Induct, k: usize, rn: NameId) {
        let i = rec_position(&d.recs, rn);
        let slot = self.env.find(rn);
        if i == d.recs.len() || slot == 0 {
            let at = s.types[k];
            self.fail(ErrorKind::ExportMismatch, at);
            return;
        }
        let ours: ConstInfo = self.env.at(slot).clone();
        let at = d.recs[i].ty;
        let ok = match ours.kind {
            ConstKind::Rec(r) => {
                self.rec_matches(d, i, &r) && names_eq(&d.recs[i].lparams, &ours.lparams)
            }
            _ => false,
        };
        if !ok || d.recs[i].safety != s.safety || !self.eq(d.recs[i].ty, ours.ty) {
            self.fail(ErrorKind::ExportMismatch, at);
        }
    }

    fn rec_matches(&mut self, d: &Induct, i: usize, r: &RecInfo) -> bool {
        let ok = names_eq(&d.recs[i].all, &r.all)
            && d.recs[i].num_params == r.nparams
            && d.recs[i].num_indices == r.nindices
            && d.recs[i].num_motives == r.nmotives
            && d.recs[i].num_minors == r.nminors
            && d.recs[i].k == r.k
            && d.recs[i].rules.len() == r.rules.len();
        ok && self.rules_match(&d.recs[i].rules, &r.rules)
    }

    fn rules_match(&mut self, ex: &[rulean_format::RecRule], ours: &[RuleInfo]) -> bool {
        let mut j = 0;
        while j < ex.len()
            && ex[j].ctor == ours[j].ctor
            && ex[j].nfields == ours[j].nfields
            && self.eq(ex[j].rhs, ours[j].rhs)
        {
            j += 1;
        }
        j == ex.len()
    }
}
