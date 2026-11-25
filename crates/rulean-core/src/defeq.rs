//! Engine R: definitional equality (spec 05.7).
//!
//! This module is a transcription of `is_def_eq_core` and its helpers in `type_checker.cpp` of the official kernel v4.35.0. The order of the steps is the same as the order in the official function, because the order changes which terms the checker unfolds.

use alloc::vec::Vec;
use rulean_store::{Expr, ExprId, LevelListId, Literal, NameId};

use crate::conv::Engine;
use crate::env::{ConstKind, compare_hints};
use crate::expr;
use crate::level;
use crate::pin::{PIN_NAT, PIN_STRING};
use crate::session::S_SUCCESS;
use crate::tc::{Checker, LBool, to_lbool};
use crate::trace::Rule;
use rulean_format::Hints;

/// The result of one step of lazy delta reduction (`reduction_status`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Continue,
    Unknown,
    Equal,
    Diff,
}

impl Checker {
    // The caches. The key is the pair in the order of the hashes, as in the official kernel.

    fn pair_seen(&self, success: bool, t: ExprId, s: ExprId) -> bool {
        let m = if success {
            &self.c_success
        } else {
            &self.c_failure
        };
        let ht = self.st.hash(t);
        let hs = self.st.hash(s);
        if ht < hs {
            m.contains(t.0, s.0)
        } else if ht > hs {
            m.contains(s.0, t.0)
        } else {
            m.contains(t.0, s.0) || m.contains(s.0, t.0)
        }
    }

    /// True if the session has the success of the pair. A hit also goes into the success cache of the declaration.
    fn sess_seen(&mut self, t: ExprId, s: ExprId) -> bool {
        if !self.sess_key(t) || !self.sess_key(s) {
            return false;
        }
        let ht = self.st.hash(t);
        let hs = self.st.hash(s);
        let found = if ht < hs {
            self.sess_get(S_SUCCESS, t.0, s.0).is_some()
        } else if ht > hs {
            self.sess_get(S_SUCCESS, s.0, t.0).is_some()
        } else {
            self.sess_get(S_SUCCESS, t.0, s.0).is_some()
                || self.sess_get(S_SUCCESS, s.0, t.0).is_some()
        };
        if found {
            let (a, b) = if ht <= hs { (t, s) } else { (s, t) };
            self.c_success.put(a.0, b.0, 1);
        }
        found
    }

    fn pair_put(&mut self, success: bool, t: ExprId, s: ExprId) {
        let (a, b) = if self.st.hash(t) <= self.st.hash(s) {
            (t, s)
        } else {
            (s, t)
        };
        if success {
            self.c_success.put(a.0, b.0, 1);
            if !self.bad() && self.sess_key(a) && self.sess_key(b) {
                self.sess.note(S_SUCCESS, a.0, b.0, 1);
            }
        } else {
            self.c_failure.put(a.0, b.0, 1);
        }
    }

    // Levels.

    /// `is_def_eq` on two level lists: the same length and equivalent items.
    pub(crate) fn is_def_eq_levels(&mut self, a: LevelListId, b: LevelListId) -> bool {
        let la = self.st.level_list_vec(a);
        let lb = self.st.level_list_vec(b);
        level::is_equivalent_list(&mut self.st, &mut self.lc, &la, &lb)
    }

    /// The level list of a constant. The caller has checked that `e` is a constant.
    fn const_levels(&self, e: ExprId) -> LevelListId {
        match self.st.node(e) {
            Expr::Const(_, ls) => ls,
            _ => self.st.level_list_empty(),
        }
    }

    // The easy cases.

    /// One binder of `is_def_eq_binding`. It checks the domains, pushes the free variable or the placeholder, and gives the bodies. The first value is false if the domains are not equal.
    fn binding_step(
        &mut self,
        t: ExprId,
        s: ExprId,
        subst: &mut Vec<ExprId>,
    ) -> (bool, ExprId, ExprId) {
        let pair = match (self.st.node(t), self.st.node(s)) {
            (Expr::Lam(a), Expr::Lam(b)) => (a, b),
            (Expr::Pi(a), Expr::Pi(b)) => (a, b),
            _ => return (false, t, s),
        };
        let (tb, sb) = pair;
        let mut var_s_type: Option<ExprId> = None;
        if !self.eq(tb.dom, sb.dom) {
            let vs = self.instantiate_rev(sb.dom, subst);
            let vt = self.instantiate_rev(tb.dom, subst);
            var_s_type = Some(vs);
            if !self.is_def_eq(vt, vs) {
                return (false, t, s);
            }
        }
        if expr::has_loose_bvars(&self.st, tb.body) || expr::has_loose_bvars(&self.st, sb.body) {
            let ty = match var_s_type {
                Some(v) => v,
                None => self.instantiate_rev(sb.dom, subst),
            };
            let fv = self.mk_local(sb.name, sb.info, ty, None);
            subst.push(fv);
        } else {
            subst.push(self.dummy);
        }
        (true, tb.body, sb.body)
    }

    /// `is_def_eq_binding`: the domains and the bodies of two binders of the same kind, for all the binders of that kind at the head.
    fn is_def_eq_binding(&mut self, t0: ExprId, s0: ExprId) -> bool {
        let mark = self.enter_scope();
        let r = self.is_def_eq_binding_in(t0, s0);
        self.leave_scope(mark);
        r
    }

    /// The body of `is_def_eq_binding`. The free variables that it makes stay in scope.
    fn is_def_eq_binding_in(&mut self, t0: ExprId, s0: ExprId) -> bool {
        let lam = self.is_lambda(t0);
        let mut t = t0;
        let mut s = s0;
        let mut subst: Vec<ExprId> = Vec::new();
        let mut ok = true;
        let mut walking = true;
        while ok && walking && !self.bad() {
            let (k, t1, s1) = self.binding_step(t, s, &mut subst);
            ok = k;
            t = t1;
            s = s1;
            walking = if lam {
                self.is_lambda(t) && self.is_lambda(s)
            } else {
                self.is_pi(t) && self.is_pi(s)
            };
        }
        if !ok || self.bad() {
            return false;
        }
        let ti = self.instantiate_rev(t, &subst);
        let si = self.instantiate_rev(s, &subst);
        self.is_def_eq(ti, si)
    }

    /// `quick_is_def_eq`.
    fn quick_is_def_eq(&mut self, t: ExprId, s: ExprId) -> LBool {
        if self.eq(t, s) || self.pair_seen(true, t, s) || self.sess_seen(t, s) {
            return LBool::True;
        }
        match (self.st.node(t), self.st.node(s)) {
            (Expr::Lam(_), Expr::Lam(_)) | (Expr::Pi(_), Expr::Pi(_)) => {
                to_lbool(self.is_def_eq_binding(t, s))
            }
            (Expr::Sort(a), Expr::Sort(b)) => {
                to_lbool(level::is_equivalent(&mut self.st, &mut self.lc, a, b))
            }
            (Expr::Lit(a), Expr::Lit(b)) => to_lbool(self.lit_eq(a, b)),
            _ => LBool::Undef,
        }
    }

    fn lit_eq(&self, a: Literal, b: Literal) -> bool {
        match (a, b) {
            (Literal::Nat(x), Literal::Nat(y)) => x == y || self.st.nat(x).beq(self.st.nat(y)),
            (Literal::Str(x), Literal::Str(y)) => {
                x == y || self.st.str_bytes(x) == self.st.str_bytes(y)
            }
            _ => false,
        }
    }

    /// `is_def_eq_args`: the arguments from the last one to the first one.
    fn is_def_eq_args(&mut self, t0: ExprId, s0: ExprId) -> bool {
        let mut t = t0;
        let mut s = s0;
        let mut ok = true;
        while ok && self.is_app(t) && self.is_app(s) {
            let a = self.app_arg(t);
            let b = self.app_arg(s);
            if self.is_def_eq(a, b) {
                t = self.app_fn1(t);
                s = self.app_fn1(s);
            } else {
                ok = false;
            }
        }
        ok && !self.is_app(t) && !self.is_app(s)
    }

    // Eta.

    /// `try_eta_expansion_core`: `fun x => b =?= s` by `fun x => s x`.
    fn try_eta_expansion_core(&mut self, t: ExprId, s: ExprId) -> bool {
        if !self.is_lambda(t) || self.is_lambda(s) {
            return false;
        }
        let ty = self.infer(s);
        let s_type = self.whnf(ty);
        if self.bad() {
            return false;
        }
        let b = match self.st.node(s_type) {
            Expr::Pi(b) => b,
            _ => return false,
        };
        let v = self.st.mk_bvar(0);
        let sv = self.st.mk_app(s, v);
        let new_s = self.st.mk_lam(b.name, b.info, b.dom, sv);
        self.is_def_eq(t, new_s)
    }

    fn try_eta_expansion(&mut self, t: ExprId, s: ExprId) -> bool {
        self.try_eta_expansion_core(t, s) || self.try_eta_expansion_core(s, t)
    }

    /// `try_eta_struct_core`: `t =?= mk t.1 ... t.n`.
    fn try_eta_struct_core(&mut self, t: ExprId, s: ExprId) -> bool {
        let f = expr::app_fn(&self.st, s);
        let n = match self.st.node(f) {
            Expr::Const(n, _) => n,
            _ => return false,
        };
        if self.get_const(n, s) == 0 {
            return false;
        }
        let (induct, nparams, nfields) = match self.ctor_shape(n) {
            Some(x) => x,
            None => return false,
        };
        let mut s_args: Vec<ExprId> = Vec::new();
        expr::app_args(&self.st, s, &mut s_args);
        let nargs = (nparams + nfields) as usize;
        // With `eta_partial_ctor` (lean4#15373), a constructor application with too few arguments is also allowed.
        if s_args.len() > nargs || (s_args.len() < nargs && !self.flags.eta_partial_ctor) {
            return false;
        }
        if !self.is_non_rec_structure(induct, s) {
            return false;
        }
        let tt = self.infer(t);
        let st = self.infer(s);
        if self.bad() || !self.is_def_eq(tt, st) {
            return false;
        }
        // The type of a partial constructor application is the rest of the constructor type, so it is a pi type with no `whnf`. Each binder gets a free variable, and both sides are applied to it.
        let mut t = t;
        let mut s_type = st;
        let mut more = true;
        while more && s_args.len() < nargs && !self.bad() {
            if let Expr::Pi(b) = self.st.node(s_type) {
                let x = self.mk_local(b.name, b.info, b.dom, None);
                t = self.st.mk_app(t, x);
                s_args.push(x);
                s_type = self.instantiate1(b.body, x);
            } else {
                more = false;
            }
        }
        if s_args.len() != nargs || self.bad() {
            return false;
        }
        let mut ok = true;
        let mut i = nparams as usize;
        while ok && i < s_args.len() {
            let p = self.st.mk_proj(induct, (i - nparams as usize) as u32, t);
            ok = self.is_def_eq(p, s_args[i]);
            i += 1;
        }
        ok
    }

    fn try_eta_struct(&mut self, t: ExprId, s: ExprId) -> bool {
        self.try_eta_struct_core(t, s) || self.try_eta_struct_core(s, t)
    }

    /// `is_def_eq_app`: the same head and the same arguments.
    fn is_def_eq_app(&mut self, t: ExprId, s: ExprId) -> bool {
        if !self.is_app(t) || !self.is_app(s) {
            return false;
        }
        let mut t_args: Vec<ExprId> = Vec::new();
        let mut s_args: Vec<ExprId> = Vec::new();
        let tf = expr::app_args(&self.st, t, &mut t_args);
        let sf = expr::app_args(&self.st, s, &mut s_args);
        if !self.is_def_eq(tf, sf) || t_args.len() != s_args.len() {
            return false;
        }
        let mut ok = true;
        let mut i = 0;
        while ok && i < t_args.len() {
            ok = self.is_def_eq(t_args[i], s_args[i]);
            i += 1;
        }
        ok
    }

    /// `is_def_eq_proof_irrel`: two proofs of the same proposition are equal.
    pub(crate) fn is_def_eq_proof_irrel(&mut self, t: ExprId, s: ExprId) -> LBool {
        let t_type = self.infer(t);
        if self.bad() || !self.is_prop(t_type) {
            return LBool::Undef;
        }
        let s_type = self.infer(s);
        if self.bad() {
            return LBool::Undef;
        }
        to_lbool(self.is_def_eq(t_type, s_type))
    }

    /// The proof irrelevance step of `is_def_eq_core`, with the trace note of an equal answer.
    fn proof_irrel_step(&mut self, t: ExprId, s: ExprId) -> LBool {
        let r = self.is_def_eq_proof_irrel(t, s);
        if r == LBool::True {
            let anon = self.st.anon();
            self.note(Rule::ProofIrrel, anon);
        }
        r
    }

    // Lazy delta reduction.

    /// `try_unfold_proj_app`.
    fn try_unfold_proj_app(&mut self, e: ExprId) -> Option<ExprId> {
        let f = expr::app_fn(&self.st, e);
        match self.st.node(f) {
            Expr::Proj(_) => {
                let n = self.whnf_core(e, false, false);
                if self.eq(n, e) { None } else { Some(n) }
            }
            _ => None,
        }
    }

    /// One delta step: `whnf_core(unfold_definition(e), false, true)`.
    fn delta_step(&mut self, e: ExprId) -> ExprId {
        match self.unfold_definition(e) {
            Some(u) => self.whnf_core(u, false, true),
            None => e,
        }
    }

    /// The unfold step of `lazy_delta_reduction_step` when both sides are delta terms.
    fn lazy_delta_both(
        &mut self,
        t: ExprId,
        s: ExprId,
        dt: u32,
        ds: u32,
    ) -> (Status, ExprId, ExprId) {
        let c = compare_hints(self.hints(dt), self.hints(ds));
        if c < 0 {
            return (Status::Continue, self.delta_step(t), s);
        }
        if c > 0 {
            return (Status::Continue, t, self.delta_step(s));
        }
        let regular = matches!(self.hints(dt), Hints::Regular(_));
        if self.is_app(t) && self.is_app(s) && dt == ds && regular && !self.pair_seen(false, t, s) {
            let tf = expr::app_fn(&self.st, t);
            let sf = expr::app_fn(&self.st, s);
            let tl = self.const_levels(tf);
            let sl = self.const_levels(sf);
            if self.is_def_eq_levels(tl, sl) && self.is_def_eq_args(t, s) {
                return (Status::Equal, t, s);
            }
            self.pair_put(false, t, s);
        }
        let t1 = self.delta_step(t);
        let s1 = self.delta_step(s);
        (Status::Continue, t1, s1)
    }

    /// `lazy_delta_reduction_step`. It returns the status and the new terms.
    fn lazy_delta_reduction_step(&mut self, t0: ExprId, s0: ExprId) -> (Status, ExprId, ExprId) {
        let dt = self.is_delta(t0);
        let ds = self.is_delta(s0);
        let (st, t, s) = if dt == 0 && ds == 0 {
            (Status::Unknown, t0, s0)
        } else if dt != 0 && ds == 0 {
            match self.try_unfold_proj_app(s0) {
                Some(s1) => (Status::Continue, t0, s1),
                None => (Status::Continue, self.delta_step(t0), s0),
            }
        } else if dt == 0 {
            match self.try_unfold_proj_app(t0) {
                Some(t1) => (Status::Continue, t1, s0),
                None => (Status::Continue, t0, self.delta_step(s0)),
            }
        } else {
            self.lazy_delta_both(t0, s0, dt, ds)
        };
        if st != Status::Continue || self.bad() {
            return (st, t, s);
        }
        match self.quick_is_def_eq(t, s) {
            LBool::True => (Status::Equal, t, s),
            LBool::False => (Status::Diff, t, s),
            LBool::Undef => (Status::Continue, t, s),
        }
    }

    /// `is_nat_zero`.
    fn is_nat_zero(&self, t: ExprId) -> bool {
        if t == self.b.e_nat_zero {
            return true;
        }
        match self.st.node(t) {
            Expr::Lit(Literal::Nat(n)) => self.st.nat(n).is_zero(),
            _ => false,
        }
    }

    /// `is_nat_succ`: the predecessor of a non-zero literal or of `Nat.succ x`.
    fn is_nat_succ(&mut self, t: ExprId) -> Option<ExprId> {
        if let Expr::Lit(Literal::Nat(n)) = self.st.node(t) {
            let v = self.st.nat(n).clone();
            if !v.is_zero() {
                let p = v.sub(&rulean_nat::Nat::from_u64(1));
                let id = self.st.intern_nat(p);
                return Some(self.st.mk_nat_lit(id));
            }
        }
        let f = expr::app_fn(&self.st, t);
        if f == self.b.e_nat_succ && expr::app_num_args(&self.st, t) == 1 {
            return Some(self.app_arg(t));
        }
        None
    }

    /// `is_def_eq_offset`.
    fn is_def_eq_offset(&mut self, t: ExprId, s: ExprId) -> LBool {
        if !self.pin_on(PIN_NAT) {
            return LBool::Undef;
        }
        if self.is_nat_zero(t) && self.is_nat_zero(s) {
            return LBool::True;
        }
        let pt = self.is_nat_succ(t);
        let ps = self.is_nat_succ(s);
        match (pt, ps) {
            (Some(a), Some(b)) => to_lbool(self.is_def_eq_core(a, b)),
            _ => LBool::Undef,
        }
    }

    /// One round of `lazy_delta_reduction` before the delta step: the offsets and the `Nat` extension. `Undef` means that the loop goes on.
    fn lazy_delta_nat(&mut self, t: ExprId, s: ExprId) -> LBool {
        let r = self.is_def_eq_offset(t, s);
        if r != LBool::Undef {
            return r;
        }
        let no_fvar = !expr::has_fvar(&self.st, t) && !expr::has_fvar(&self.st, s);
        if no_fvar || self.eager {
            if let Some(tv) = self.reduce_nat(t) {
                return to_lbool(self.is_def_eq_core(tv, s));
            }
            if self.bad() {
                return LBool::False;
            }
            if let Some(sv) = self.reduce_nat(s) {
                return to_lbool(self.is_def_eq_core(t, sv));
            }
        }
        LBool::Undef
    }

    /// `lazy_delta_reduction`. It returns the result and the last terms, because the caller uses them when the result is `Undef`.
    fn lazy_delta_reduction(&mut self, t0: ExprId, s0: ExprId) -> (LBool, ExprId, ExprId) {
        let mut t = t0;
        let mut s = s0;
        let mut r = LBool::Undef;
        let mut done = false;
        while !done && !self.bad() {
            let n = self.lazy_delta_nat(t, s);
            if n != LBool::Undef {
                r = n;
                done = true;
            } else {
                let (st, t1, s1) = self.lazy_delta_reduction_step(t, s);
                t = t1;
                s = s1;
                match st {
                    Status::Continue => {}
                    Status::Unknown => done = true,
                    Status::Equal => {
                        r = LBool::True;
                        done = true;
                    }
                    Status::Diff => {
                        r = LBool::False;
                        done = true;
                    }
                }
            }
        }
        if self.bad() {
            return (LBool::False, t, s);
        }
        (r, t, s)
    }

    /// `lazy_delta_proj_reduction`: `t.i =?= s.i` by lazy unfolding of `t` and `s`.
    fn lazy_delta_proj_reduction(
        &mut self,
        t0: ExprId,
        s0: ExprId,
        sname: NameId,
        idx: u32,
    ) -> bool {
        let mut t = t0;
        let mut s = s0;
        let mut equal = false;
        let mut done = false;
        while !done && !self.bad() {
            let (r, t1, s1) = self.lazy_delta_reduction_step(t, s);
            t = t1;
            s = s1;
            match r {
                Status::Continue => {}
                Status::Equal => {
                    equal = true;
                    done = true;
                }
                Status::Unknown | Status::Diff => done = true,
            }
        }
        if self.bad() {
            return false;
        }
        if equal {
            return true;
        }
        let tp = self.reduce_proj_core(t, sname, idx);
        let sp = match tp {
            Some(_) => self.reduce_proj_core(s, sname, idx),
            None => None,
        };
        match (tp, sp) {
            (Some(a), Some(b)) => self.is_def_eq_core(a, b),
            _ => self.is_def_eq_core(t, s),
        }
    }

    // The other extensions.

    /// `try_string_lit_expansion_core`.
    fn try_string_lit_expansion_core(&mut self, t: ExprId, s: ExprId) -> LBool {
        let lit = match self.string_lit(t) {
            Some(x) => x,
            None => return LBool::Undef,
        };
        if !self.is_app(s) || self.app_fn1(s) != self.b.e_string_of_list {
            return LBool::Undef;
        }
        let c = self.string_lit_to_constructor(lit);
        let w = self.whnf(c);
        to_lbool(self.is_def_eq_core(w, s))
    }

    fn try_string_lit_expansion(&mut self, t: ExprId, s: ExprId) -> LBool {
        if !self.pin_on(PIN_STRING) {
            return LBool::Undef;
        }
        let r = self.try_string_lit_expansion_core(t, s);
        if r != LBool::Undef {
            return r;
        }
        self.try_string_lit_expansion_core(s, t)
    }

    /// `is_def_eq_unit_like`: two terms of a structure with one constructor and no fields.
    fn is_def_eq_unit_like(&mut self, t: ExprId, s: ExprId) -> bool {
        let ty = self.infer(t);
        let t_type = self.whnf(ty);
        if self.bad() {
            return false;
        }
        let i = expr::app_fn(&self.st, t_type);
        let n = match self.st.node(i) {
            Expr::Const(n, _) => n,
            _ => return false,
        };
        if !self.is_non_rec_structure(n, t) {
            return false;
        }
        let c = match self.first_ctor(n, t) {
            Some(c) => c,
            None => return false,
        };
        let cs = self.get_const(c, t);
        if cs == 0 {
            return false;
        }
        let nfields = match &self.env.at(cs).kind {
            ConstKind::Ctor(k) => k.nfields,
            _ => return false,
        };
        if nfields != 0 {
            return false;
        }
        let s_type = self.infer(s);
        if self.bad() {
            return false;
        }
        self.is_def_eq_core(t_type, s_type)
    }

    // The main function.

    /// `is_def_eq_core` with the depth guard.
    pub(crate) fn is_def_eq_core(&mut self, t: ExprId, s: ExprId) -> bool {
        if self.bad() {
            return false;
        }
        if !self.enter_beat(t) {
            return false;
        }
        let r = self.is_def_eq_core_body(t, s);
        self.leave_beat();
        r && !self.bad()
    }

    /// The steps of `is_def_eq_core` up to lazy delta reduction.
    fn is_def_eq_core_body(&mut self, t: ExprId, s: ExprId) -> bool {
        let r = self.quick_is_def_eq(t, s);
        if r != LBool::Undef {
            return r == LBool::True;
        }
        // Proofs by reflection: `t =?= Bool.true` with `t` closed.
        if (!expr::has_fvar(&self.st, t) || self.eager)
            && self.is_constant_named(s, self.b.bool_true)
        {
            let w = self.whnf(t);
            if self.is_constant_named(w, self.b.bool_true) {
                return true;
            }
        }
        // With `proof_irrel_first` (lean4#15103), proof irrelevance comes before `whnf_core`, so a proof is not reduced.
        if self.flags.proof_irrel_first {
            let r = self.proof_irrel_step(t, s);
            if r != LBool::Undef {
                return r == LBool::True;
            }
        }
        let t_n = self.whnf_core(t, false, true);
        let s_n = self.whnf_core(s, false, true);
        if self.bad() {
            return false;
        }
        if t_n != t || s_n != s {
            let r = self.quick_is_def_eq(t_n, s_n);
            if r != LBool::Undef {
                return r == LBool::True;
            }
        }
        if !self.flags.proof_irrel_first {
            let r = self.proof_irrel_step(t_n, s_n);
            if r != LBool::Undef {
                return r == LBool::True;
            }
        }
        let (r, t_n, s_n) = self.lazy_delta_reduction(t_n, s_n);
        if r != LBool::Undef {
            return r == LBool::True;
        }
        self.is_def_eq_whnf(t_n, s_n)
    }

    /// The steps of `is_def_eq_core` after lazy delta reduction.
    fn is_def_eq_whnf(&mut self, t_n: ExprId, s_n: ExprId) -> bool {
        match (self.st.node(t_n), self.st.node(s_n)) {
            (Expr::Const(a, la), Expr::Const(b, lb)) => {
                if a == b && self.is_def_eq_levels(la, lb) {
                    return true;
                }
            }
            (Expr::FVar(a, _), Expr::FVar(b, _)) => {
                if a == b {
                    return true;
                }
            }
            (Expr::Proj(a), Expr::Proj(b)) => {
                if a.struct_name == b.struct_name
                    && a.index == b.index
                    && self.lazy_delta_proj_reduction(a.expr, b.expr, a.struct_name, a.index)
                {
                    return true;
                }
            }
            _ => {}
        }
        if self.bad() {
            return false;
        }
        let t_nn = self.whnf_core(t_n, false, false);
        let s_nn = self.whnf_core(s_n, false, false);
        if self.bad() {
            return false;
        }
        if t_nn != t_n || s_nn != s_n {
            return self.is_def_eq_core(t_nn, s_nn);
        }
        let anon = self.st.anon();
        if self.is_def_eq_app(t_n, s_n) {
            return true;
        }
        if self.try_eta_expansion(t_n, s_n) {
            self.note(Rule::EtaFn, anon);
            return true;
        }
        if self.try_eta_struct(t_n, s_n) {
            self.note(Rule::EtaStruct, anon);
            return true;
        }
        let r = self.try_string_lit_expansion(t_n, s_n);
        if r != LBool::Undef {
            self.note(Rule::StringLit, anon);
            return r == LBool::True;
        }
        let u = self.is_def_eq_unit_like(t_n, s_n);
        if u {
            self.note(Rule::UnitLike, anon);
        }
        u
    }

    /// `is_def_eq`: definitional equality. With `Engine::F`, engine F tries the query first (spec 05.1). A true result goes into the success cache.
    pub fn is_def_eq(&mut self, t: ExprId, s: ExprId) -> bool {
        // Engine F does not read the success caches, so a known success is found here first. Engine R finds it in `quick_is_def_eq`.
        if self.engine == Engine::F
            && self.eq_depth == 0
            && (self.pair_seen(true, t, s) || self.sess_seen(t, s))
        {
            return true;
        }
        let r = self.is_def_eq_shared(t, s);
        if r {
            self.pair_put(true, t, s);
        }
        r
    }
}
