//! Nested inductive types: `elim_nested_inductive_fn`, `elim_nested_inductive_result::restore_nested` and the restore steps of `environment::add_inductive` of `inductive.cpp` of the official kernel v4.35.0 (spec 06.3).
//!
//! The checker changes each nested occurrence `I Ds is` in a constructor type to `Iaux As is`, where `Iaux` is a new auxiliary type of the block. Then it checks the block with the auxiliary types. Then it removes the auxiliary declarations, changes the auxiliary types back to the nested occurrences in the constructors and the recursors, and adds the restored declarations.

use alloc::vec::Vec;
use rulean_store::ids::raw;
use rulean_store::{Expr, ExprId, LevelListId, NameId};

use crate::env::{ConstInfo, ConstKind, InductInfo, RecInfo, RuleInfo};
use crate::expr;
use crate::inductive::Ind;
use crate::names;
use crate::tc::{Checker, ErrorKind};

/// The kinds of change of `map_term`. Each kind has its own second key in the `rep` cache.
const REPLACE: u32 = 0;
const RESTORE: u32 = 1;

/// The position of `n` in `ns`, or the length of `ns`.
fn position(ns: &[NameId], n: NameId) -> usize {
    let mut i = 0;
    while i < ns.len() && ns[i] != n {
        i += 1;
    }
    i
}

/// The position of the constant with the name `n` in `cs`, or the length of `cs`.
fn const_position(cs: &[ConstInfo], n: NameId) -> usize {
    let mut i = 0;
    while i < cs.len() && cs[i].name != n {
        i += 1;
    }
    i
}

/// The terms of `v` from position `a`.
fn tail(v: &[ExprId], a: usize) -> Vec<ExprId> {
    let mut out = Vec::new();
    let mut i = a;
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}

impl Checker {
    // `elim_nested_inductive_fn`.

    /// `elim_nested_inductive_fn::operator()`. It adds the auxiliary types to `s` and changes the constructor types. The queue is the list of types of `s`, so the auxiliary types are processed too.
    pub(crate) fn elim_nested(&mut self, s: &mut Ind) {
        s.norig = s.names.len();
        s.nctors = s.cnames.len();
        let t0 = s.types[0];
        let mut ps = Vec::new();
        self.get_params(s, t0, &mut ps);
        s.eparams = ps;
        let mut q = 0;
        while q < s.names.len() && !self.bad() {
            self.elim_type(s, q);
            q += 1;
        }
    }

    /// `get_params`: a local for each of the first `nparams` binders of `t0`, with the binder domain as its type. It gives the body.
    fn get_params(&mut self, s: &Ind, t0: ExprId, ps: &mut Vec<ExprId>) -> ExprId {
        let mut t = t0;
        while (ps.len() as u32) < s.nparams && self.is_pi(t) {
            let x = match self.st.node(t) {
                Expr::Pi(b) => self.mk_local(b.name, b.info, b.dom, None),
                _ => t,
            };
            ps.push(x);
            let body = self.binding(t).1;
            t = self.instantiate1(body, x);
        }
        if (ps.len() as u32) < s.nparams {
            self.fail(ErrorKind::BadInductive, t0);
        }
        t
    }

    fn elim_type(&mut self, s: &mut Ind, q: usize) {
        let mut c = s.cstart[q];
        let end = s.cstart[q + 1];
        while c < end && !self.bad() {
            let t = s.ctypes[c];
            let r = self.elim_ctor(s, t);
            s.ctypes[c] = r;
            c += 1;
        }
    }

    /// One constructor of the main loop: new parameter locals `As`, `replace_all_nested` on the body, and the `pi` binders of `As` again.
    fn elim_ctor(&mut self, s: &mut Ind, t: ExprId) -> ExprId {
        let mut xs = Vec::new();
        let body = self.get_params(s, t, &mut xs);
        if self.bad() {
            return t;
        }
        s.cur = xs.clone();
        s.rep.clear();
        let r = self.map_term(s, body, REPLACE);
        if self.bad() || r == body {
            return t;
        }
        self.mk_binding(&xs, r, false, false)
    }

    /// `replace` of `replace_fn.h` with `replace_if_nested` or with the function of `restore_nested`. The traversal goes into the function before the argument and into the domain before the body.
    fn map_term(&mut self, s: &mut Ind, e: ExprId, mode: u32) -> ExprId {
        match s.rep.get(e.0, raw(mode)) {
            Some(v) => ExprId(v),
            None => self.map_core(s, e, mode),
        }
    }

    fn map_core(&mut self, s: &mut Ind, e: ExprId, mode: u32) -> ExprId {
        if !self.enter(e) {
            return e;
        }
        let here = if mode == REPLACE {
            self.replace_if_nested(s, e)
        } else {
            self.restore_here(s, e)
        };
        let r = match here {
            Some(v) => v,
            None => self.map_children(s, e, mode),
        };
        self.leave();
        s.rep.put(e.0, raw(mode), r.0);
        r
    }

    fn map_children(&mut self, s: &mut Ind, e: ExprId, mode: u32) -> ExprId {
        if self.bad() {
            return e;
        }
        match self.st.node(e) {
            Expr::App(f, a) => {
                let f2 = self.map_term(s, f, mode);
                let a2 = self.map_term(s, a, mode);
                if f2 == f && a2 == a {
                    e
                } else {
                    self.st.mk_app(f2, a2)
                }
            }
            Expr::Lam(b) => {
                let d = self.map_term(s, b.dom, mode);
                let x = self.map_term(s, b.body, mode);
                if d == b.dom && x == b.body {
                    e
                } else {
                    self.st.mk_lam(b.name, b.info, d, x)
                }
            }
            Expr::Pi(b) => {
                let d = self.map_term(s, b.dom, mode);
                let x = self.map_term(s, b.body, mode);
                if d == b.dom && x == b.body {
                    e
                } else {
                    self.st.mk_pi(b.name, b.info, d, x)
                }
            }
            Expr::Let(l) => {
                let t = self.map_term(s, l.ty, mode);
                let v = self.map_term(s, l.value, mode);
                let x = self.map_term(s, l.body, mode);
                if t == l.ty && v == l.value && x == l.body {
                    e
                } else {
                    self.st.mk_let(l.name, t, v, x)
                }
            }
            Expr::Proj(p) => {
                let x = self.map_term(s, p.expr, mode);
                if x == p.expr {
                    e
                } else {
                    self.st.mk_proj(p.struct_name, p.index, x)
                }
            }
            _ => e,
        }
    }

    /// `is_nested_inductive_app`: the parameter count of `I` if `e` is `I Ds is`, `I` is an inductive type of the environment and `Ds` has a type of the block. A `Ds` with a loose bound variable gives a fault.
    fn nested_app_params(&mut self, s: &mut Ind, e: ExprId, args: &[ExprId]) -> Option<usize> {
        let f = expr::app_fn(&self.st, e);
        if !self.is_app(e) || !self.is_constant(f) {
            return None;
        }
        let n = self.const_name(f);
        let slot = self.env.find(n);
        if slot == 0 {
            return None;
        }
        let np = match self.induct_shape(slot) {
            Some((np, _, _, _)) => np as usize,
            None => return None,
        };
        if np > args.len() {
            return None;
        }
        let mut nested = false;
        let mut loose = false;
        let mut i = 0;
        while i < np {
            loose = loose || expr::has_loose_bvars(&self.st, args[i]);
            nested = nested || self.has_ind_occ(s, args[i]);
            i += 1;
        }
        if nested && loose {
            self.fail(ErrorKind::BadNested, e);
        }
        if nested && !loose { Some(np) } else { None }
    }

    /// `replace_params`: the free variables `As` of `e` changed to the parameters of `elim_nested_inductive_fn`.
    fn replace_params(&mut self, s: &Ind, e: ExprId) -> ExprId {
        let a = expr::abstract_fvars(&mut self.st, &mut self.x, e, &s.cur);
        self.instantiate_rev(a, &s.eparams)
    }

    /// `replace_if_nested`: `Iaux As is` for a nested occurrence `I Ds is`.
    fn replace_if_nested(&mut self, s: &mut Ind, e: ExprId) -> Option<ExprId> {
        let mut args = Vec::new();
        let f = expr::app_args(&self.st, e, &mut args);
        let np = match self.nested_app_params(s, e, &args) {
            Some(np) => np,
            None => return None,
        };
        let ias = self.st.mk_apps(f, &args[..np]);
        let key = self.replace_params(s, ias);
        let mut j = 0;
        while j < s.aux_nested.len() && !self.eq(s.aux_nested[j], key) {
            j += 1;
        }
        if j == s.aux_nested.len() {
            j = self.add_aux_types(s, f, &args, np);
        }
        if self.bad() {
            return None;
        }
        let an = s.names[s.norig + j];
        let aux = self.st.mk_const(an, s.levels);
        let a1 = self.st.mk_apps(aux, &s.cur);
        let rest = tail(&args, np);
        Some(self.st.mk_apps(a1, &rest))
    }

    /// `mk_unique_name`: `n_i` for the next index `i` with no constant of that name.
    fn unique_name(&mut self, s: &mut Ind, n: NameId) -> NameId {
        let mut r = names::append_index(&mut self.st, n, s.next_idx);
        s.next_idx += 1;
        while self.env.contains(r) {
            r = names::append_index(&mut self.st, n, s.next_idx);
            s.next_idx += 1;
        }
        r
    }

    /// The `else` part of `replace_if_nested`: an auxiliary type for each type `J` of the block of `I`, with the parameters `Ds`. It gives the position of the auxiliary type of `I` in `aux_nested`.
    fn add_aux_types(&mut self, s: &mut Ind, f: ExprId, args: &[ExprId], np: usize) -> usize {
        let (iname, ilvls) = match self.st.node(f) {
            Expr::Const(n, ls) => (n, ls),
            _ => (self.st.anon(), s.levels),
        };
        let slot = self.env.find(iname);
        let all = match &self.env.at(slot).kind {
            ConstKind::Induct(i) => i.all.clone(),
            _ => Vec::new(),
        };
        let mut result = s.aux_nested.len();
        let mut i = 0;
        while i < all.len() && !self.bad() {
            if all[i] == iname {
                result = s.aux_nested.len();
            }
            self.add_aux_type(s, all[i], ilvls, args, np);
            i += 1;
        }
        result
    }

    /// The auxiliary type of one type `J` of the block of the nested type, with its constructors.
    fn add_aux_type(
        &mut self,
        s: &mut Ind,
        jname: NameId,
        ilvls: LevelListId,
        args: &[ExprId],
        np: usize,
    ) {
        let jslot = self.env.find(jname);
        if jslot == 0 {
            let at = s.types[0];
            self.fail(ErrorKind::BadNested, at);
            return;
        }
        let ctors = match &self.env.at(jslot).kind {
            ConstKind::Induct(i) => i.ctors.clone(),
            _ => Vec::new(),
        };
        let jc = self.st.mk_const(jname, ilvls);
        let jas = self.st.mk_apps(jc, &args[..np]);
        let pre = names::concat(&mut self.st, s.nested, jname);
        let aux_name = self.unique_name(s, pre);
        let aux_type = self.aux_term(s, jslot, ilvls, args, np);
        let key = self.replace_params(s, jas);
        s.aux_nested.push(key);
        let k = s.names.len();
        s.names.push(aux_name);
        s.types.push(aux_type);
        let mut c = 0;
        while c < ctors.len() && !self.bad() {
            let cslot = self.env.find(ctors[c]);
            let cn = names::replace_prefix(&mut self.st, ctors[c], jname, aux_name);
            let ct = self.aux_term(s, cslot, ilvls, args, np);
            s.cnames.push(cn);
            s.ctypes.push(ct);
            s.cowner.push(k);
            s.cexport.push(0);
            c += 1;
        }
        s.cstart.push(s.cnames.len());
    }

    /// The type of the constant of `slot` with the levels `ilvls`, the parameters `Ds` and the `pi` binders of `As` (`instantiate_pi_params` and `mk_pi`).
    fn aux_term(
        &mut self,
        s: &Ind,
        slot: u32,
        ilvls: LevelListId,
        args: &[ExprId],
        np: usize,
    ) -> ExprId {
        let ls = self.st.level_list_vec(ilvls);
        let t0 = self.instantiate_type_lparams(slot, &ls);
        let mut t = t0;
        let mut i = 0;
        while i < np && self.is_pi(t) {
            t = self.binding(t).1;
            i += 1;
        }
        if i < np {
            self.fail(ErrorKind::BadNested, t0);
            return t0;
        }
        let b = self.instantiate_rev(t, &args[..np]);
        self.mk_binding(&s.cur, b, false, false)
    }

    // `restore_nested`.

    /// `restore_nested`: new locals for the parameter binders of `e`, the function of `restore_nested` on the body, and the binders again.
    fn restore_term(&mut self, s: &mut Ind, e0: ExprId) -> ExprId {
        let pi = self.is_pi(e0);
        let mut e = e0;
        let mut xs = Vec::new();
        while xs.len() < s.eparams.len() && (self.is_pi(e) || self.is_lambda(e)) {
            let x = match self.st.node(e) {
                Expr::Pi(b) => self.mk_local(b.name, b.info, b.dom, None),
                Expr::Lam(b) => self.mk_local(b.name, b.info, b.dom, None),
                _ => e,
            };
            xs.push(x);
            let body = self.binding(e).1;
            e = self.instantiate1(body, x);
        }
        if xs.len() < s.eparams.len() {
            self.fail(ErrorKind::BadNested, e0);
            return e0;
        }
        s.cur = xs.clone();
        s.rep.clear();
        let r = self.map_term(s, e, RESTORE);
        self.mk_binding(&xs, r, !pi, false)
    }

    /// The nested occurrence of auxiliary type `j`, with the locals `As` of the current term for the parameters.
    fn nested_with_cur(&mut self, s: &Ind, j: usize) -> ExprId {
        let a = expr::abstract_fvars(&mut self.st, &mut self.x, s.aux_nested[j], &s.eparams);
        self.instantiate_rev(a, &s.cur)
    }

    /// The name of the recursor of `main.rec_i` for an auxiliary recursor `n`, or `n`.
    fn new_rec_name(&mut self, s: &Ind, n: NameId) -> NameId {
        let mut k = s.norig;
        let mut r = n;
        while k < s.names.len() {
            let old = names::rec_name(&mut self.st, s.names[k]);
            if old == n {
                let main = names::rec_name(&mut self.st, s.names[0]);
                r = names::append_index(&mut self.st, main, (k - s.norig + 1) as u64);
            }
            k += 1;
        }
        r
    }

    /// The function of `restore_nested` for one term.
    fn restore_here(&mut self, s: &mut Ind, t: ExprId) -> Option<ExprId> {
        if let Expr::Const(n, ls) = self.st.node(t) {
            let r = self.new_rec_name(s, n);
            if r != n {
                return Some(self.st.mk_const(r, ls));
            }
        }
        let mut args = Vec::new();
        let f = expr::app_args(&self.st, t, &mut args);
        let n = match self.st.node(f) {
            Expr::Const(n, _) => n,
            _ => return None,
        };
        let k = position(&s.names, n);
        if k >= s.norig && k < s.names.len() {
            return self.restore_aux_app(s, t, k - s.norig, &args);
        }
        let c = position(&s.cnames, n);
        if c >= s.nctors && c < s.cnames.len() {
            return self.restore_aux_ctor_app(s, t, c, &args);
        }
        None
    }

    /// An auxiliary type applied to `args`: the nested occurrence applied to the arguments after the parameters.
    fn restore_aux_app(&mut self, s: &Ind, t: ExprId, j: usize, args: &[ExprId]) -> Option<ExprId> {
        let np = s.eparams.len();
        if args.len() < np {
            self.fail(ErrorKind::BadNested, t);
            return None;
        }
        let nt = self.nested_with_cur(s, j);
        let rest = tail(args, np);
        Some(self.st.mk_apps(nt, &rest))
    }

    /// A constructor of an auxiliary type applied to `args`: the constructor of the nested type, applied to the parameters of the nested occurrence and to the arguments after the parameters.
    fn restore_aux_ctor_app(
        &mut self,
        s: &Ind,
        t: ExprId,
        c: usize,
        args: &[ExprId],
    ) -> Option<ExprId> {
        let np = s.eparams.len();
        if args.len() < np {
            self.fail(ErrorKind::BadNested, t);
            return None;
        }
        let k = s.cowner[c];
        let nt = self.nested_with_cur(s, k - s.norig);
        let mut iargs = Vec::new();
        let i = expr::app_args(&self.st, nt, &mut iargs);
        let (iname, ils) = match self.st.node(i) {
            Expr::Const(n, ls) => (n, ls),
            _ => {
                self.fail(ErrorKind::BadNested, t);
                return None;
            }
        };
        let fname = names::replace_prefix(&mut self.st, s.cnames[c], s.names[k], iname);
        let fc = self.st.mk_const(fname, ils);
        let a1 = self.st.mk_apps(fc, &iargs);
        let rest = tail(args, np);
        Some(self.st.mk_apps(a1, &rest))
    }

    /// `restore_constructor_name`.
    fn restore_ctor_name(&mut self, s: &mut Ind, n: NameId) -> NameId {
        let c = position(&s.cnames, n);
        if c < s.nctors || c == s.cnames.len() {
            let at = s.types[0];
            self.fail(ErrorKind::BadNested, at);
            return n;
        }
        let k = s.cowner[c];
        s.cur = s.eparams.clone();
        let nt = self.nested_with_cur(s, k - s.norig);
        let i = expr::app_fn(&self.st, nt);
        match self.st.node(i) {
            Expr::Const(iname, _) => names::replace_prefix(&mut self.st, n, s.names[k], iname),
            _ => {
                self.fail(ErrorKind::BadNested, nt);
                n
            }
        }
    }

    // The restore steps of `environment::add_inductive`.

    /// Removes the declarations of the auxiliary block from the environment, then adds the restored declarations and checks them. `saved` is the size of the environment before the block.
    pub(crate) fn restore_block(&mut self, s: &mut Ind, saved: usize) {
        let mut aux: Vec<ConstInfo> = Vec::new();
        let mut i = saved;
        while i < self.env.len() {
            aux.push(self.env.at((i + 1) as u32).clone());
            i += 1;
        }
        self.env.truncate(saved);
        self.clear_caches();
        let all: Vec<NameId> = s.names[..s.norig].to_vec();
        let mut recs: Vec<NameId> = Vec::new();
        let mut k = 0;
        while k < s.norig && !self.bad() {
            self.restore_type(s, &aux, &all, k, &mut recs);
            k += 1;
        }
        while k < s.names.len() && !self.bad() {
            let rn = names::rec_name(&mut self.st, s.names[k]);
            self.restore_rec(s, &aux, &all, rn, &mut recs);
            k += 1;
        }
        if !self.bad() {
            self.check_nested_apps(s);
        }
        if !self.bad() {
            self.recheck_block(s, &recs);
        }
    }

    /// The type `k`, its constructors with restored types, and its recursor.
    fn restore_type(
        &mut self,
        s: &mut Ind,
        aux: &[ConstInfo],
        all: &[NameId],
        k: usize,
        recs: &mut Vec<NameId>,
    ) {
        let n = s.names[k];
        let p = const_position(aux, n);
        if p == aux.len() {
            let at = s.types[k];
            self.fail(ErrorKind::BadNested, at);
            return;
        }
        let mut ty_info = aux[p].clone();
        if let ConstKind::Induct(i) = &ty_info.kind {
            let mut ii: InductInfo = i.clone();
            ii.all = all.to_vec();
            ty_info.kind = ConstKind::Induct(ii);
        }
        self.check_name(n, ty_info.ty);
        if self.bad() {
            return;
        }
        self.env.add(ty_info);
        let mut c = s.cstart[k];
        while c < s.cstart[k + 1] && !self.bad() {
            self.restore_ctor(s, aux, c);
            c += 1;
        }
        let rn = names::rec_name(&mut self.st, n);
        if !self.bad() {
            self.restore_rec(s, aux, all, rn, recs);
        }
    }

    fn restore_ctor(&mut self, s: &mut Ind, aux: &[ConstInfo], c: usize) {
        let n = s.cnames[c];
        let p = const_position(aux, n);
        if p == aux.len() {
            let at = s.ctypes[c];
            self.fail(ErrorKind::BadNested, at);
            return;
        }
        let mut info = aux[p].clone();
        info.ty = self.restore_term(s, info.ty);
        self.check_name(n, info.ty);
        if !self.bad() {
            self.env.add(info);
        }
    }

    /// `process_rec`: the recursor `rn` of the auxiliary block with a restored type, restored rules and the name `main.rec_i` for an auxiliary recursor.
    fn restore_rec(
        &mut self,
        s: &mut Ind,
        aux: &[ConstInfo],
        all: &[NameId],
        rn: NameId,
        recs: &mut Vec<NameId>,
    ) {
        let p = const_position(aux, rn);
        if p == aux.len() {
            let at = s.types[0];
            self.fail(ErrorKind::BadNested, at);
            return;
        }
        let new_name = self.new_rec_name(s, rn);
        let mut info = aux[p].clone();
        info.name = new_name;
        info.ty = self.restore_term(s, info.ty);
        let r: RecInfo = match &info.kind {
            ConstKind::Rec(r) => r.clone(),
            _ => {
                let at = info.ty;
                self.fail(ErrorKind::BadNested, at);
                return;
            }
        };
        let mut rules: Vec<RuleInfo> = Vec::new();
        let mut j = 0;
        while j < r.rules.len() && !self.bad() {
            let rhs = self.restore_term(s, r.rules[j].rhs);
            let mut ctor = r.rules[j].ctor;
            if new_name != rn {
                ctor = self.restore_ctor_name(s, ctor);
            }
            rules.push(RuleInfo {
                ctor,
                nfields: r.rules[j].nfields,
                rhs,
            });
            j += 1;
        }
        let mut nr = r;
        nr.all = all.to_vec();
        nr.rules = rules;
        info.kind = ConstKind::Rec(nr);
        self.check_name(new_name, info.ty);
        if !self.bad() {
            self.env.add(info);
            recs.push(new_name);
        }
    }

    /// The check of each nested occurrence `I Ds` in the context of the parameters of `elim_nested_inductive_fn`. The parameters `Ds` are not in the auxiliary block, so the other checks do not see them.
    fn check_nested_apps(&mut self, s: &Ind) {
        let mut j = 0;
        while j < s.aux_nested.len() && !self.bad() {
            let e = s.aux_nested[j];
            self.check(e);
            j += 1;
        }
    }

    /// The checks of the restored constructor types and of the types and the rules of the restored recursors.
    fn recheck_block(&mut self, s: &Ind, recs: &[NameId]) {
        let mut c = 0;
        while c < s.nctors && !self.bad() {
            let slot = self.env.find(s.cnames[c]);
            let ty = self.env.at(slot).ty;
            self.check(ty);
            c += 1;
        }
        let mut i = 0;
        while i < recs.len() && !self.bad() {
            self.recheck_rec(recs[i]);
            i += 1;
        }
    }

    fn recheck_rec(&mut self, rn: NameId) {
        let slot = self.env.find(rn);
        let info = self.env.at(slot).clone();
        let saved = self.lparams.clone();
        self.lparams = info.lparams.clone();
        self.check(info.ty);
        if let ConstKind::Rec(r) = &info.kind {
            let mut j = 0;
            while j < r.rules.len() && !self.bad() {
                self.check(r.rules[j].rhs);
                j += 1;
            }
        }
        self.lparams = saved;
    }
}
