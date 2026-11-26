//! Engine R: weak head normal form (spec 05.5 and 05.8).
//!
//! This module is a transcription of the reduction part of `type_checker.cpp`, of `inductive_reduce_rec` and its helpers in `inductive.h` and `inductive.cpp`, and of `quot_reduce_rec` in `quot.h`, of the official kernel v4.35.0.

use alloc::vec::Vec;
use rulean_format::Hints;
use rulean_nat::Nat;
use rulean_store::{Expr, ExprId, LevelListId, Literal, NameId, NatId};

use crate::env::{ConstKind, RuleInfo};
use crate::expr;
use crate::pin::{PIN_NAT, PIN_STRING};
use crate::session::{S_UNFOLD, S_WHNF, S_WHNF_CORE};
use crate::tc::{
    Checker, ErrorKind, NAT_ADD, NAT_BEQ, NAT_BLE, NAT_DIV, NAT_GCD, NAT_LAND, NAT_LOR, NAT_MOD,
    NAT_MUL, NAT_POW, NAT_SHL, NAT_SHR, NAT_SUB, NAT_XOR,
};
use crate::trace::Rule;

/// The data of a recursor that `inductive_reduce_rec` needs.
#[derive(Clone, Copy)]
pub(crate) struct RecShape {
    pub(crate) major_idx: u32,
    /// The number of parameters, motives and minor premises.
    pub(crate) nprefix: u32,
    pub(crate) nparams: u32,
    pub(crate) k: bool,
}

/// Decodes UTF-8 bytes into code points (`utf8_decode`). The parser has checked the bytes, so a bad sequence does not occur. A bad byte gives its own value.
pub fn utf8_decode(b: &[u8]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(b.len());
    let mut i = 0;
    while i < b.len() {
        let c = b[i] as u32;
        let (n, first) = if c < 0x80 {
            (0, c)
        } else if c >= 0xf0 {
            (3, c & 0x07)
        } else if c >= 0xe0 {
            (2, c & 0x0f)
        } else if c >= 0xc0 {
            (1, c & 0x1f)
        } else {
            (0, c)
        };
        let mut v = first;
        let mut k = 0;
        while k < n && i + 1 + k < b.len() {
            v = (v << 6) | (b[i + 1 + k] as u32 & 0x3f);
            k += 1;
        }
        out.push(v);
        i += 1 + k;
    }
    out
}

/// The result of `nat_lit_id`.
#[derive(Clone, Copy)]
enum NatArg {
    /// A literal: its handle, or `None` for `Nat.zero`.
    Lit(Option<NatId>),
    /// The term is not a literal.
    NotLit,
}

/// The result of a binary `Nat` operation of `nat_bin`, before it goes into the store.
enum NatOut {
    /// A value whose size `check_nat_size` checks.
    Sized(Nat),
    /// A value with no size check.
    Value(Nat),
    Bool(bool),
    None,
}

impl Checker {
    // Literals as constructors.

    /// `nat_lit_to_constructor`: `0` is `Nat.zero` and `n+1` is `Nat.succ n`.
    pub(crate) fn nat_lit_to_constructor(&mut self, v: &Nat) -> ExprId {
        if v.is_zero() {
            return self.b.e_nat_zero;
        }
        let p = v.sub(&Nat::from_u64(1));
        let id = self.st.intern_nat(p);
        let lit = self.st.mk_nat_lit(id);
        self.st.mk_app(self.b.e_nat_succ, lit)
    }

    /// `string_lit_to_constructor`: `String.ofList [Char.ofNat c1, ..., Char.ofNat cn]`.
    pub(crate) fn string_lit_to_constructor(&mut self, s: rulean_store::StrId) -> ExprId {
        let cs = utf8_decode(self.st.str_bytes(s));
        let mut r = self.b.e_list_nil_char;
        let mut i = cs.len();
        while i > 0 {
            i -= 1;
            let id = self.st.intern_nat(Nat::from_u64(cs[i] as u64));
            let lit = self.st.mk_nat_lit(id);
            let ch = self.st.mk_app(self.b.e_char_of_nat, lit);
            let cons = self.st.mk_app(self.b.e_list_cons_char, ch);
            r = self.st.mk_app(cons, r);
        }
        self.st.mk_app(self.b.e_string_of_list, r)
    }

    /// The string of a string literal, if `e` is one.
    pub(crate) fn string_lit(&self, e: ExprId) -> Option<rulean_store::StrId> {
        match self.st.node(e) {
            Expr::Lit(Literal::Str(s)) => Some(s),
            _ => None,
        }
    }

    // Environment queries of `inductive.cpp`.

    /// `is_non_rec_structure`: an inductive type with one constructor, no indices and no recursion. An unknown name is a fault, as `environment::get` throws.
    pub(crate) fn is_non_rec_structure(&mut self, n: NameId, at: ExprId) -> bool {
        let s = self.get_const(n, at);
        if s == 0 {
            return false;
        }
        match &self.env.at(s).kind {
            ConstKind::Induct(i) => i.ctors.len() == 1 && i.nindices == 0 && !i.is_rec,
            _ => false,
        }
    }

    /// `get_first_cnstr`: the first constructor of an inductive type, if any.
    pub(crate) fn first_ctor(&mut self, n: NameId, at: ExprId) -> Option<NameId> {
        let s = self.get_const(n, at);
        if s == 0 {
            return None;
        }
        match &self.env.at(s).kind {
            ConstKind::Induct(i) => {
                if i.ctors.len() > 0 {
                    Some(i.ctors[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// The induct, the number of parameters and the number of fields of a constructor. A name that is not a constructor gives `None`.
    pub(crate) fn ctor_shape(&mut self, n: NameId) -> Option<(NameId, u32, u32)> {
        let s = self.env.find(n);
        if s == 0 {
            return None;
        }
        match &self.env.at(s).kind {
            ConstKind::Ctor(c) => Some((c.induct, c.nparams, c.nfields)),
            _ => None,
        }
    }

    /// `is_constructor_app`.
    fn is_constructor_app(&mut self, e: ExprId) -> bool {
        let f = expr::app_fn(&self.st, e);
        match self.st.node(f) {
            Expr::Const(n, _) => self.ctor_shape(n).is_some(),
            _ => false,
        }
    }

    /// `mk_nullary_cnstr`: the first constructor of the head of `ty`, applied to the first `nparams` arguments of `ty`.
    fn mk_nullary_cnstr(&mut self, ty: ExprId, nparams: u32) -> Option<ExprId> {
        let mut args: Vec<ExprId> = Vec::new();
        let d = expr::app_args(&self.st, ty, &mut args);
        let (dn, dls) = match self.st.node(d) {
            Expr::Const(n, ls) => (n, ls),
            _ => return None,
        };
        let c = match self.first_ctor(dn, ty) {
            Some(c) => c,
            None => return None,
        };
        args.truncate(nparams as usize);
        let k = self.st.mk_const(c, dls);
        Some(self.st.mk_apps(k, &args))
    }

    /// `expand_eta_struct`: `mk e.1 ... e.n` for a term `e` of type `e_type`.
    fn expand_eta_struct(&mut self, e_type: ExprId, e: ExprId) -> ExprId {
        let mut args: Vec<ExprId> = Vec::new();
        let i_fn = expr::app_args(&self.st, e_type, &mut args);
        let (i_name, i_levels) = match self.st.node(i_fn) {
            Expr::Const(n, ls) => (n, ls),
            _ => return e,
        };
        let c = match self.first_ctor(i_name, e) {
            Some(c) => c,
            None => return e,
        };
        let (nparams, nfields) = match self.ctor_shape(c) {
            Some((_, p, f)) => (p, f),
            None => return self.fail(ErrorKind::BadConst, e),
        };
        args.truncate(nparams as usize);
        let k = self.st.mk_const(c, i_levels);
        let mut r = self.st.mk_apps(k, &args);
        let mut i = 0;
        while i < nfields {
            let p = self.st.mk_proj(i_name, i, e);
            r = self.st.mk_app(r, p);
            i += 1;
        }
        r
    }

    /// The reduction that `inductive_reduce_rec` gets as its `whnf` argument.
    fn rec_whnf(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> ExprId {
        if cheap_rec {
            self.whnf_core(e, cheap_rec, cheap_proj)
        } else {
            self.whnf(e)
        }
    }

    /// `to_cnstr_when_K` of the official kernel.
    pub(crate) fn cnstr_when_k(
        &mut self,
        major_induct: NameId,
        nparams: u32,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> ExprId {
        let t = self.infer(e);
        let app_type = self.rec_whnf(t, cheap_rec, cheap_proj);
        if self.bad() {
            return e;
        }
        let i_fn = expr::app_fn(&self.st, app_type);
        if !self.is_constant_named(i_fn, major_induct) {
            return e;
        }
        let new_c = match self.mk_nullary_cnstr(app_type, nparams) {
            Some(c) => c,
            None => return e,
        };
        let new_type = self.infer(new_c);
        if self.bad() || !self.is_def_eq(app_type, new_type) {
            return e;
        }
        new_c
    }

    /// `to_cnstr_when_structure` of the official kernel.
    pub(crate) fn cnstr_when_structure(
        &mut self,
        rec_slot: u32,
        induct: NameId,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> ExprId {
        if !self.is_non_rec_structure(induct, e) || self.is_constructor_app(e) {
            return e;
        }
        let t = self.infer(e);
        let e_type = self.rec_whnf(t, cheap_rec, cheap_proj);
        if self.bad() {
            return e;
        }
        let f = expr::app_fn(&self.st, e_type);
        if !self.is_constant_named(f, induct) {
            return e;
        }
        // With `eta_subsingleton_major` (lean4#15371), the test is on the recursor and not on the type: a recursor that has no extra universe parameter eliminates only into `Prop`, and its major premise does not get eta. A structure in `Prop` with large elimination, such as `And`, now gets eta.
        let no_eta = if self.flags.eta_subsingleton_major {
            self.rec_into_prop_only(rec_slot)
        } else {
            self.is_prop(e_type)
        };
        if no_eta || self.bad() {
            return e;
        }
        self.expand_eta_struct(e_type, e)
    }

    /// True if the recursor of the slot has the same number of universe parameters as the first type of its group, so its motive is in `Prop` only. A missing type gives true, so the caller does no eta.
    fn rec_into_prop_only(&mut self, rec_slot: u32) -> bool {
        let c = self.env.at(rec_slot);
        let first = match &c.kind {
            ConstKind::Rec(r) => r.all.first().copied(),
            _ => None,
        };
        let params = c.lparams.len();
        let s = match first {
            Some(n) => self.env.find(n),
            None => 0,
        };
        s == 0 || params == self.env.at(s).lparams.len()
    }

    /// `recursor_val::get_major_induct`: the head of the domain of the major premise in the type of the recursor.
    pub(crate) fn major_induct(&self, slot: u32, major_idx: u32) -> NameId {
        let mut t = self.env.at(slot).ty;
        let mut i = 0;
        while i < major_idx {
            let (_, body) = self.binding(t);
            t = body;
            i += 1;
        }
        let (dom, _) = self.binding(t);
        let f = expr::app_fn(&self.st, dom);
        self.const_name(f)
    }

    /// The recursor data of a slot, if the constant is a recursor.
    pub(crate) fn rec_shape(&self, slot: u32) -> Option<RecShape> {
        match &self.env.at(slot).kind {
            ConstKind::Rec(r) => Some(RecShape {
                major_idx: r.major_idx(),
                nprefix: r.nparams + r.nmotives + r.nminors,
                nparams: r.nparams,
                k: r.k,
            }),
            _ => None,
        }
    }

    /// `get_rec_rule_for`.
    fn rec_rule_for(&self, slot: u32, major: ExprId) -> Option<RuleInfo> {
        let f = expr::app_fn(&self.st, major);
        let n = match self.st.node(f) {
            Expr::Const(n, _) => n,
            _ => return None,
        };
        match &self.env.at(slot).kind {
            ConstKind::Rec(r) => find_rule(&r.rules, n),
            _ => None,
        }
    }

    /// `inductive_reduce_rec`.
    fn inductive_reduce_rec(
        &mut self,
        e: ExprId,
        cheap_rec: bool,
        cheap_proj: bool,
    ) -> Option<ExprId> {
        let rec_fn = expr::app_fn(&self.st, e);
        let (rn, rls) = match self.st.node(rec_fn) {
            Expr::Const(n, ls) => (n, ls),
            _ => return None,
        };
        let slot = self.env.find(rn);
        if slot == 0 {
            return None;
        }
        let r = match self.rec_shape(slot) {
            Some(r) => r,
            None => return None,
        };
        let mut rec_args: Vec<ExprId> = Vec::new();
        expr::app_args(&self.st, e, &mut rec_args);
        let major_idx = r.major_idx as usize;
        if major_idx >= rec_args.len() {
            return None;
        }
        let induct = self.major_induct(slot, r.major_idx);
        let mut major = rec_args[major_idx];
        if r.k {
            major = self.cnstr_when_k(induct, r.nparams, major, cheap_rec, cheap_proj);
        }
        // With `no_whnf_prop_major` (lean4#15371), a major premise that is a proof does not get `whnf`. Proof irrelevance makes such a step not needed, and the step can be slow.
        let whnf_major = if self.flags.no_whnf_prop_major {
            let ty = self.infer(major);
            !self.bad() && !self.is_prop(ty)
        } else {
            true
        };
        if whnf_major {
            major = self.rec_whnf(major, cheap_rec, cheap_proj);
        }
        if self.bad() {
            return None;
        }
        major = match self.st.node(major) {
            Expr::Lit(Literal::Nat(n)) if self.pin_on(PIN_NAT) => {
                let v = self.st.nat(n).clone();
                self.nat_lit_to_constructor(&v)
            }
            Expr::Lit(Literal::Str(s)) if self.pin_on(PIN_STRING) => {
                let c = self.string_lit_to_constructor(s);
                self.rec_whnf(c, cheap_rec, cheap_proj)
            }
            _ => self.cnstr_when_structure(slot, induct, major, cheap_rec, cheap_proj),
        };
        if self.bad() {
            return None;
        }
        let rule = match self.rec_rule_for(slot, major) {
            Some(x) => x,
            None => return None,
        };
        let mut major_args: Vec<ExprId> = Vec::new();
        expr::app_args(&self.st, major, &mut major_args);
        let nfields = rule.nfields as usize;
        if nfields > major_args.len() {
            return None;
        }
        if self.st.level_list_items(rls).len() != self.env.at(slot).lparams.len() {
            return None;
        }
        let mut rhs = self.inst_lps_cached(slot, rule.rhs, rls);
        let np = r.nprefix as usize;
        rhs = self.st.mk_apps(rhs, &rec_args[..np]);
        let nparams = major_args.len() - nfields;
        rhs = self.st.mk_apps(rhs, &major_args[nparams..]);
        if rec_args.len() > major_idx + 1 {
            rhs = self.st.mk_apps(rhs, &rec_args[major_idx + 1..]);
        }
        Some(rhs)
    }

    /// `quot_reduce_rec`: `Quot.lift f h (Quot.mk r a)` is `f a`, and `Quot.ind h (Quot.mk r a)` is `h a`.
    fn quot_reduce_rec(&mut self, e: ExprId) -> Option<ExprId> {
        let f = expr::app_fn(&self.st, e);
        let n = match self.st.node(f) {
            Expr::Const(n, _) => n,
            _ => return None,
        };
        let mk_pos: usize = if n == self.b.quot_lift {
            5
        } else if n == self.b.quot_ind {
            4
        } else {
            return None;
        };
        let arg_pos: usize = 3;
        let mut args: Vec<ExprId> = Vec::new();
        expr::app_args(&self.st, e, &mut args);
        if args.len() <= mk_pos {
            return None;
        }
        let mk = self.whnf(args[mk_pos]);
        if self.bad() {
            return None;
        }
        let mk_fn = expr::app_fn(&self.st, mk);
        if !self.is_constant_named(mk_fn, self.b.quot_mk) || expr::app_num_args(&self.st, mk) != 3 {
            return None;
        }
        let a = self.app_arg(mk);
        let mut r = self.st.mk_app(args[arg_pos], a);
        let elim_arity = mk_pos + 1;
        if args.len() > elim_arity {
            r = self.st.mk_apps(r, &args[elim_arity..]);
        }
        Some(r)
    }

    /// `reduce_recursor`.
    fn reduce_recursor(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> Option<ExprId> {
        if self.env.quot_initialized() {
            let r = self.quot_reduce_rec(e);
            if r.is_some() {
                self.note_head(Rule::Quot, e);
            }
            if r.is_some() || self.bad() {
                return r;
            }
        }
        let r = self.inductive_reduce_rec(e, cheap_rec, cheap_proj);
        if r.is_some() {
            self.note_head(Rule::Iota, e);
        }
        r
    }

    /// `whnf_fvar`: zeta-reduction of a `let` free variable.
    fn whnf_fvar(&mut self, e: ExprId, lvl: u32, cheap_rec: bool, cheap_proj: bool) -> ExprId {
        match self.fvar_value(lvl) {
            Some(v) => self.whnf_core(v, cheap_rec, cheap_proj),
            None => e,
        }
    }

    /// `reduce_proj_core`.
    pub(crate) fn reduce_proj_core(
        &mut self,
        c0: ExprId,
        sname: NameId,
        idx: u32,
    ) -> Option<ExprId> {
        let mut c = c0;
        if let Some(s) = self.string_lit(c)
            && self.pin_on(PIN_STRING)
        {
            let k = self.string_lit_to_constructor(s);
            c = self.whnf(k);
            if self.bad() {
                return None;
            }
        }
        let mut args: Vec<ExprId> = Vec::new();
        let mk = expr::app_args(&self.st, c, &mut args);
        let n = match self.st.node(mk) {
            Expr::Const(n, _) => n,
            _ => return None,
        };
        if self.get_const(n, c) == 0 {
            return None;
        }
        let (induct, nparams, _) = match self.ctor_shape(n) {
            Some(x) => x,
            None => return None,
        };
        if induct != sname {
            return None;
        }
        let i = nparams as usize + idx as usize;
        if i < args.len() { Some(args[i]) } else { None }
    }

    /// `reduce_proj`.
    fn reduce_proj(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> Option<ExprId> {
        let (sname, idx, s) = match self.st.node(e) {
            Expr::Proj(p) => (p.struct_name, p.index, p.expr),
            _ => return None,
        };
        let c = if cheap_proj {
            self.whnf_core(s, cheap_rec, cheap_proj)
        } else {
            self.whnf(s)
        };
        if self.bad() {
            return None;
        }
        self.reduce_proj_core(c, sname, idx)
    }

    /// `whnf_core`: weak head normal form without delta reduction and without the `Nat` extension. The cache is used only when `cheap_rec` and `cheap_proj` are false.
    pub fn whnf_core(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> ExprId {
        if self.bad() {
            return self.dummy;
        }
        match self.st.node(e) {
            Expr::BVar(_)
            | Expr::Sort(_)
            | Expr::Pi(_)
            | Expr::Const(_, _)
            | Expr::Lam(_)
            | Expr::Lit(_) => return e,
            Expr::FVar(_, _) => {
                if !self.is_let_fvar(e) {
                    return e;
                }
            }
            Expr::App(_, _) | Expr::Let(_) | Expr::Proj(_) => {}
        }
        let k = self.canon(e);
        if let Some(r) = self.c_whnf_core.get(k.0, 0) {
            return ExprId(r);
        }
        let key = !cheap_rec && !cheap_proj && self.sess_key(e);
        if key {
            if let Some(r) = self.sess_get(S_WHNF_CORE, e.0, 0) {
                self.c_whnf_core.put(k.0, 0, r);
                return ExprId(r);
            }
        }
        if !self.enter_beat(e) {
            return self.dummy;
        }
        let (r, cache) = self.whnf_core_node(e, cheap_rec, cheap_proj);
        self.leave_beat();
        if cache && !cheap_rec && !cheap_proj && !self.bad() {
            self.c_whnf_core.put(k.0, 0, r.0);
            if key {
                self.sess.note(S_WHNF_CORE, e.0, 0, r.0);
            }
        }
        r
    }

    /// The work of `whnf_core`. The flag is false where the official function returns before it writes the cache.
    fn whnf_core_node(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> (ExprId, bool) {
        match self.st.node(e) {
            Expr::FVar(lvl, _) => (self.whnf_fvar(e, lvl, cheap_rec, cheap_proj), false),
            Expr::Proj(_) => match self.reduce_proj(e, cheap_rec, cheap_proj) {
                Some(m) => (self.whnf_core(m, cheap_rec, cheap_proj), true),
                None => (e, true),
            },
            Expr::App(_, _) => self.whnf_core_app(e, cheap_rec, cheap_proj),
            Expr::Let(l) => {
                let b = self.instantiate1(l.body, l.value);
                (self.whnf_core(b, cheap_rec, cheap_proj), true)
            }
            _ => (e, false),
        }
    }

    /// The application case of `whnf_core`: beta reduction, then the recursors.
    fn whnf_core_app(&mut self, e: ExprId, cheap_rec: bool, cheap_proj: bool) -> (ExprId, bool) {
        let mut rev: Vec<ExprId> = Vec::new();
        let f0 = expr::app_rev_args(&self.st, e, &mut rev);
        let f = self.whnf_core(f0, cheap_rec, cheap_proj);
        if self.bad() {
            return (self.dummy, false);
        }
        if self.is_lambda(f) {
            let num_args = rev.len();
            let mut g = f;
            let mut m = 1;
            let mut walking = true;
            while walking && m < num_args {
                let (_, body) = self.binding(g);
                if self.is_lambda(body) {
                    g = body;
                    m += 1;
                } else {
                    walking = false;
                }
            }
            let (_, body) = self.binding(g);
            let inst = expr::instantiate(&mut self.st, &mut self.x, body, &rev[num_args - m..]);
            let r = expr::mk_rev_app(&mut self.st, inst, &rev[..num_args - m]);
            (self.whnf_core(r, cheap_rec, cheap_proj), true)
        } else if self.eq(f, f0) {
            match self.reduce_recursor(e, cheap_rec, cheap_proj) {
                Some(r) => (self.whnf_core(r, cheap_rec, cheap_proj), false),
                None => (e, false),
            }
        } else {
            let r = expr::mk_rev_app(&mut self.st, f, &rev);
            (self.whnf_core(r, cheap_rec, cheap_proj), true)
        }
    }

    // Delta reduction.

    /// `is_delta`: the slot of the definition or theorem at the head of `e`, if its number of levels is right, or 0.
    pub(crate) fn is_delta(&mut self, e: ExprId) -> u32 {
        let f = expr::app_fn(&self.st, e);
        match self.st.node(f) {
            Expr::Const(n, ls) => self.is_delta_const(n, ls),
            _ => 0,
        }
    }

    /// `is_delta` for the constant `n` with the levels `ls`.
    pub(crate) fn is_delta_const(&mut self, n: NameId, ls: LevelListId) -> u32 {
        let s = self.env.find(n);
        if s == 0 {
            return 0;
        }
        let c = self.env.at(s);
        if c.value().is_some() && self.st.level_list_items(ls).len() == c.lparams.len() {
            s
        } else {
            0
        }
    }

    /// The hint of the constant of a slot.
    pub(crate) fn hints(&self, slot: u32) -> Hints {
        self.env.at(slot).hints()
    }

    /// `unfold_definition_core`. The cache is used only for a constant with levels.
    pub(crate) fn unfold_definition_core(&mut self, e: ExprId) -> Option<ExprId> {
        let list = match self.st.node(e) {
            Expr::Const(_, list) => list,
            _ => return None,
        };
        let d = self.is_delta(e);
        if d == 0 {
            return None;
        }
        self.note_head(Rule::Delta, e);
        let ls = self.st.level_list_vec(list);
        if ls.len() > 0 {
            if let Some(r) = self.c_unfold.get(e.0, 0) {
                return Some(ExprId(r));
            }
            let key = self.sess_key(e);
            if key {
                if let Some(r) = self.sess_get(S_UNFOLD, e.0, 0) {
                    self.c_unfold.put(e.0, 0, r);
                    return Some(ExprId(r));
                }
            }
            let r = self.instantiate_value_lparams(d, &ls);
            self.c_unfold.put(e.0, 0, r.0);
            if key && !self.bad() {
                self.sess.note(S_UNFOLD, e.0, 0, r.0);
            }
            Some(r)
        } else {
            Some(self.instantiate_value_lparams(d, &ls))
        }
    }

    /// `unfold_definition`: unfolds the head constant and applies the result to the arguments.
    pub(crate) fn unfold_definition(&mut self, e: ExprId) -> Option<ExprId> {
        if self.is_app(e) {
            let f0 = expr::app_fn(&self.st, e);
            match self.unfold_definition_core(f0) {
                Some(f) => {
                    let mut rev: Vec<ExprId> = Vec::new();
                    expr::app_rev_args(&self.st, e, &mut rev);
                    Some(expr::mk_rev_app(&mut self.st, f, &rev))
                }
                None => None,
            }
        } else {
            self.unfold_definition_core(e)
        }
    }

    // The `Nat` extension.

    pub(crate) fn mk_nat(&mut self, v: Nat) -> ExprId {
        let id = self.st.intern_nat(v);
        self.st.mk_nat_lit(id)
    }

    fn mk_bool(&self, b: bool) -> ExprId {
        if b {
            self.b.e_bool_true
        } else {
            self.b.e_bool_false
        }
    }

    /// The literal of `e` as a handle of the store, with `None` for `Nat.zero`, or `NotLit` (`is_nat_lit_ext`). The value stays in the store, so a large value is not copied.
    fn nat_lit_id(&self, e: ExprId) -> NatArg {
        if e == self.b.e_nat_zero {
            return NatArg::Lit(None);
        }
        match self.st.node(e) {
            Expr::Lit(Literal::Nat(n)) => NatArg::Lit(Some(n)),
            _ => NatArg::NotLit,
        }
    }

    /// The value of a literal of `nat_lit_id`. `zero` is the value for `None`.
    pub(crate) fn nat_ref<'a>(&'a self, n: Option<NatId>, zero: &'a Nat) -> &'a Nat {
        match n {
            Some(id) => self.st.nat(id),
            None => zero,
        }
    }

    /// The two arguments of a binary `Nat` operation after `whnf`, if both are literals, as in `nat_lit_id`.
    fn nat_args(&mut self, e: ExprId) -> Option<(Option<NatId>, Option<NatId>)> {
        let f = self.app_fn1(e);
        let a1 = self.app_arg(f);
        let w1 = self.whnf(a1);
        let v1 = match self.nat_lit_id(w1) {
            NatArg::Lit(v) => v,
            NatArg::NotLit => return None,
        };
        let a2 = self.app_arg(e);
        let w2 = self.whnf(a2);
        let v2 = match self.nat_lit_id(w2) {
            NatArg::Lit(v) => v,
            NatArg::NotLit => return None,
        };
        if self.bad() {
            return None;
        }
        Some((v1, v2))
    }

    /// The second argument of `Nat.pow` or `Nat.shiftLeft` as a count (`get_count_arg`).
    fn count_arg(&mut self, v: &Nat, e: ExprId) -> Option<u64> {
        match v.to_u64() {
            Some(k) if k <= u32::MAX as u64 => Some(k),
            _ => {
                self.fail(ErrorKind::CountTooLarge, e);
                None
            }
        }
    }

    /// `reduce_pow`.
    fn reduce_pow(&mut self, e: ExprId, base: &Nat, exp: &Nat) -> Option<ExprId> {
        let k = match self.count_arg(exp, e) {
            Some(k) => k,
            None => return None,
        };
        let one = Nat::from_u64(1);
        if base.compare(&one) == core::cmp::Ordering::Greater
            && k != 0
            && Checker::nat_size(base) > self.nat_max / k
        {
            self.fail(ErrorKind::NatTooLarge, e);
            return None;
        }
        let r = base.pow(k);
        Some(self.mk_nat(r))
    }

    /// `reduce_shiftLeft`.
    fn reduce_shift_left(&mut self, e: ExprId, v: &Nat, shift: &Nat) -> Option<ExprId> {
        if v.is_zero() {
            return Some(self.mk_nat(Nat::zero()));
        }
        let k = match self.count_arg(shift, e) {
            Some(k) => k,
            None => return None,
        };
        if !self.check_nat_size(Checker::nat_size(v) + k / 8 + 1, e) {
            return None;
        }
        let r = v.shift_left(k);
        Some(self.mk_nat(r))
    }

    /// A binary operation that checks the size of its result (`reduce_bin_nat_op` with `check_size`).
    pub(crate) fn sized(&mut self, e: ExprId, r: Nat) -> Option<ExprId> {
        if !self.check_nat_size(Checker::nat_size(&r), e) {
            return None;
        }
        Some(self.mk_nat(r))
    }

    /// The binary operation `op` of `reduce_nat` on the literals `n1` and `n2` of `nat_args`. The operation reads the values in the store and does not copy them. `Nat.pow` and `Nat.shiftLeft` check a count before the operation, so they copy the values.
    pub(crate) fn nat_bin(
        &mut self,
        e: ExprId,
        op: usize,
        n1: Option<NatId>,
        n2: Option<NatId>,
    ) -> Option<ExprId> {
        let zero = Nat::zero();
        if op == NAT_POW || op == NAT_SHL {
            let v1 = self.nat_ref(n1, &zero).clone();
            let v2 = self.nat_ref(n2, &zero).clone();
            if op == NAT_POW {
                return self.reduce_pow(e, &v1, &v2);
            }
            return self.reduce_shift_left(e, &v1, &v2);
        }
        let v1 = self.nat_ref(n1, &zero);
        let v2 = self.nat_ref(n2, &zero);
        let r = match op {
            NAT_ADD => NatOut::Sized(v1.add(v2)),
            NAT_SUB => NatOut::Sized(v1.sub(v2)),
            NAT_MUL => NatOut::Sized(v1.mul(v2)),
            NAT_GCD => NatOut::Value(v1.gcd(v2)),
            NAT_MOD => NatOut::Value(v1.rem(v2)),
            NAT_DIV => NatOut::Value(v1.div(v2)),
            NAT_BEQ => NatOut::Bool(v1.beq(v2)),
            NAT_BLE => NatOut::Bool(v1.ble(v2)),
            NAT_LAND => NatOut::Value(v1.land(v2)),
            NAT_LOR => NatOut::Value(v1.lor(v2)),
            NAT_XOR => NatOut::Value(v1.xor(v2)),
            NAT_SHR => NatOut::Value(v1.shift_right_nat(v2)),
            _ => NatOut::None,
        };
        match r {
            NatOut::Sized(v) => self.sized(e, v),
            NatOut::Value(v) => Some(self.mk_nat(v)),
            NatOut::Bool(b) => Some(self.mk_bool(b)),
            NatOut::None => None,
        }
    }

    /// The index of the binary operation `f` in the `nat_ops` table, or the length of the table.
    pub(crate) fn nat_op_index(&self, f: ExprId) -> usize {
        let ops = &self.b.nat_ops;
        let mut i = 0;
        while i < ops.len() && ops[i] != f {
            i += 1;
        }
        i
    }

    /// `reduce_nat`: the 15 built-in operations on literals (spec 05.8).
    pub(crate) fn reduce_nat(&mut self, e: ExprId) -> Option<ExprId> {
        let r = self.reduce_nat_body(e);
        if r.is_some() {
            self.note_head(Rule::Nat, e);
        }
        r
    }

    fn reduce_nat_body(&mut self, e: ExprId) -> Option<ExprId> {
        if !self.pin_on(PIN_NAT) {
            return None;
        }
        let nargs = expr::app_num_args(&self.st, e);
        if nargs == 1 {
            let f = self.app_fn1(e);
            if f == self.b.e_nat_succ {
                let a = self.app_arg(e);
                let w = self.whnf(a);
                let n = match self.nat_lit_id(w) {
                    NatArg::Lit(n) => n,
                    NatArg::NotLit => return None,
                };
                let zero = Nat::zero();
                let v = self.nat_ref(n, &zero).succ();
                return self.sized(e, v);
            }
        } else if nargs == 2 {
            let f1 = self.app_fn1(e);
            let f = self.app_fn1(f1);
            if !self.is_constant(f) {
                return None;
            }
            let op = self.nat_op_index(f);
            if op >= self.b.nat_ops.len() || !self.pin_on(1 << op) {
                return None;
            }
            let (n1, n2) = match self.nat_args(e) {
                Some(x) => x,
                None => return None,
            };
            return self.nat_bin(e, op, n1, n2);
        }
        None
    }

    /// `whnf`: weak head normal form with delta reduction and the `Nat` extension.
    pub fn whnf(&mut self, e: ExprId) -> ExprId {
        if self.bad() {
            return self.dummy;
        }
        match self.st.node(e) {
            Expr::BVar(_) | Expr::Sort(_) | Expr::Pi(_) | Expr::Lit(_) => return e,
            Expr::FVar(_, _) => {
                if !self.is_let_fvar(e) {
                    return e;
                }
            }
            _ => {}
        }
        let k = self.canon(e);
        if let Some(r) = self.c_whnf.get(k.0, 0) {
            return ExprId(r);
        }
        let key = self.sess_key(e);
        if key {
            if let Some(r) = self.sess_get(S_WHNF, e.0, 0) {
                self.c_whnf.put(k.0, 0, r);
                return ExprId(r);
            }
        }
        let r = self.whnf_loop(e);
        if !self.bad() {
            self.c_whnf.put(k.0, 0, r.0);
            if key {
                self.sess.note(S_WHNF, e.0, 0, r.0);
            }
        }
        r
    }

    /// The loop of `whnf`: `whnf_core`, then the `Nat` extension, then one delta step.
    fn whnf_loop(&mut self, e: ExprId) -> ExprId {
        let mut t = e;
        let mut r = e;
        let mut done = false;
        while !done && !self.bad() {
            let t1 = self.whnf_core(t, false, false);
            match self.reduce_nat(t1) {
                Some(v) => {
                    r = v;
                    done = true;
                }
                None => match self.unfold_definition(t1) {
                    Some(n) => t = n,
                    None => {
                        r = t1;
                        done = true;
                    }
                },
            }
        }
        r
    }
}

/// The rule of the constructor `n` in `rules`, if there is one.
pub(crate) fn find_rule(rules: &[RuleInfo], n: NameId) -> Option<RuleInfo> {
    let mut i = 0;
    while i < rules.len() && rules[i].ctor != n {
        i += 1;
    }
    if i < rules.len() {
        Some(rules[i])
    } else {
        None
    }
}
