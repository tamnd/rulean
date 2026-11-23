//! Declarations: the checks of `environment.cpp` and `quot.cpp` of the official kernel v4.35.0 (spec 05.9 and 06.5).
//!
//! Each `add_*` function checks one declaration and adds it to the environment. It returns the first fault, or `None` if the declaration is accepted. A rejected declaration is not added.

use alloc::vec::Vec;
use rulean_format::{Axiom, Decl, Defn, Opaque, Quot, QuotKind, Safety, Thm};
use rulean_store::{BinderInfo, ExprId, LevelId, NameId, Tier};

use crate::env::{ConstInfo, ConstKind};
use crate::expr;
use crate::tc::{Checker, ErrorKind, Fault};

/// The safety of the checker for a declaration that is not unsafe. The official kernel checks a partial definition with a safe checker too.
fn checker_safety(s: Safety) -> Safety {
    if s == Safety::Unsafe {
        Safety::Unsafe
    } else {
        Safety::Safe
    }
}

/// True if the two name lists are equal.
fn names_eq(a: &[NameId], b: &[NameId]) -> bool {
    let mut ok = a.len() == b.len();
    let mut i = 0;
    while ok && i < a.len() {
        ok = a[i] == b[i];
        i += 1;
    }
    ok
}

/// The position of the first definition with the name `n` in `ds`, or the length of `ds`.
fn defn_index(ds: &[Defn], n: NameId) -> usize {
    let mut i = 0;
    while i < ds.len() && ds[i].name != n {
        i += 1;
    }
    i
}

/// The position of `n` in `ns`, or the length of `ns`.
fn index_of(ns: &[NameId], n: NameId) -> usize {
    let mut i = 0;
    while i < ns.len() && ns[i] != n {
        i += 1;
    }
    i
}

impl Checker {
    /// Records a fault at `at` and gives it back.
    pub(crate) fn reject(&mut self, kind: ErrorKind, at: ExprId) -> Option<Fault> {
        self.fail(kind, at);
        self.fault()
    }

    /// `check_name`: the name is not declared.
    pub(crate) fn check_name(&mut self, n: NameId, at: ExprId) {
        if self.env.contains(n) {
            self.fail(ErrorKind::AlreadyDeclared, at);
        }
    }

    /// `check_duplicated_univ_params`.
    pub(crate) fn check_duplicated_univ_params(&mut self, ls: &[NameId], at: ExprId) {
        let mut i = 0;
        while i < ls.len() && !self.bad() {
            if index_of(&ls[i + 1..], ls[i]) < ls.len() - i - 1 {
                self.fail(ErrorKind::DuplicateLevelParam, at);
            }
            i += 1;
        }
    }

    /// `check_no_metavar_no_fvar`. The store has no metavariables.
    pub(crate) fn check_no_fvar(&mut self, e: ExprId) {
        if !self.bad() && expr::has_fvar(&self.st, e) {
            self.fail(ErrorKind::FreeVar, e);
        }
    }

    /// `check_constant_val`: the name, the level parameters and the type of a constant. The caller has called `begin`. Engine F tries the type check first, as in `check_value`.
    fn check_constant_val(&mut self, n: NameId, lparams: &[NameId], ty: ExprId) {
        self.check_name(n, ty);
        self.check_duplicated_univ_params(lparams, ty);
        self.check_no_fvar(ty);
        if self.bad() {
            return;
        }
        let f = self.f_check_type(ty);
        if f && !self.confirm_all {
            return;
        }
        let sort = self.check(ty);
        self.ensure_sort(sort, ty);
        if f && self.bad() {
            self.f_stats.disagree += 1;
        }
    }

    /// The value check of a definition, a theorem or an opaque constant: `check(value)` and `is_def_eq(type of value, type)`. Engine F tries it first (spec 05.4.5). If engine F does not accept, engine R does the check. With `--confirm all`, engine R also does the check after engine F accepts, and a reject of engine R then counts as a disagreement.
    fn check_value(&mut self, value: ExprId, ty: ExprId) {
        self.check_no_fvar(value);
        if self.bad() {
            return;
        }
        let f = self.f_check_value(value, ty);
        if f && !self.confirm_all {
            return;
        }
        self.check_value_r(value, ty);
        if f && self.bad() {
            self.f_stats.disagree += 1;
        }
    }

    /// The value check of engine R.
    fn check_value_r(&mut self, value: ExprId, ty: ExprId) {
        let val_type = self.check(value);
        if self.bad() {
            return;
        }
        if !self.is_def_eq(val_type, ty) && !self.bad() {
            self.fail(ErrorKind::DefTypeMismatch, value);
        }
    }

    pub(crate) fn add_const(
        &mut self,
        name: NameId,
        lparams: Vec<NameId>,
        ty: ExprId,
        safety: Safety,
        kind: ConstKind,
    ) {
        // A scratch term is removed at the end of the declaration, so the environment must not keep one. The kinds that use the scratch tier keep only input terms, so this is a check of that rule.
        let value = match &kind {
            ConstKind::Defn { value, hints: _ } => *value,
            ConstKind::Thm { value } => *value,
            ConstKind::Opaque { value } => *value,
            _ => ty,
        };
        if ty.tier() == Tier::Scratch || value.tier() == Tier::Scratch {
            self.fail(ErrorKind::Unsupported, ty);
            return;
        }
        self.env.add(ConstInfo {
            name,
            lparams,
            ty,
            safety,
            kind,
        });
    }

    /// `add_axiom`.
    pub fn add_axiom(&mut self, d: &Axiom) -> Option<Fault> {
        self.begin(d.lparams.clone(), checker_safety(d.safety));
        self.check_constant_val(d.name, &d.lparams, d.ty);
        if self.bad() {
            return self.fault();
        }
        self.add_const(d.name, d.lparams.clone(), d.ty, d.safety, ConstKind::Axiom);
        None
    }

    fn defn_kind(d: &Defn) -> ConstKind {
        ConstKind::Defn {
            value: d.value,
            hints: d.hints,
        }
    }

    /// `add_definition`. An unsafe definition may refer to itself, so its header is added before its value is checked.
    pub fn add_definition(&mut self, d: &Defn) -> Option<Fault> {
        if d.safety == Safety::Unsafe {
            self.begin(d.lparams.clone(), Safety::Unsafe);
            self.check_constant_val(d.name, &d.lparams, d.ty);
            if self.bad() {
                return self.fault();
            }
            self.add_const(
                d.name,
                d.lparams.clone(),
                d.ty,
                d.safety,
                Checker::defn_kind(d),
            );
            self.begin(d.lparams.clone(), Safety::Unsafe);
            self.check_value(d.value, d.ty);
            if self.bad() {
                // The official kernel throws, so the new environment with the header is dropped.
                let n = self.env.len() - 1;
                self.env.truncate(n);
                return self.fault();
            }
            return None;
        }
        self.begin(d.lparams.clone(), Safety::Safe);
        self.check_constant_val(d.name, &d.lparams, d.ty);
        self.check_value(d.value, d.ty);
        if self.bad() {
            return self.fault();
        }
        self.add_const(
            d.name,
            d.lparams.clone(),
            d.ty,
            d.safety,
            Checker::defn_kind(d),
        );
        None
    }

    /// `add_theorem`: the type must be a proposition.
    pub fn add_theorem(&mut self, d: &Thm) -> Option<Fault> {
        self.begin(d.lparams.clone(), Safety::Safe);
        self.check_constant_val(d.name, &d.lparams, d.ty);
        if self.bad() {
            return self.fault();
        }
        if !self.is_prop(d.ty) {
            if !self.bad() {
                self.fail(ErrorKind::TheoremNotProp, d.ty);
            }
            return self.fault();
        }
        self.check_value(d.value, d.ty);
        if self.bad() {
            return self.fault();
        }
        self.add_const(
            d.name,
            d.lparams.clone(),
            d.ty,
            Safety::Safe,
            ConstKind::Thm { value: d.value },
        );
        None
    }

    /// `add_opaque`.
    pub fn add_opaque(&mut self, d: &Opaque) -> Option<Fault> {
        self.begin(d.lparams.clone(), Safety::Safe);
        self.check_constant_val(d.name, &d.lparams, d.ty);
        self.check_value(d.value, d.ty);
        if self.bad() {
            return self.fault();
        }
        self.add_const(
            d.name,
            d.lparams.clone(),
            d.ty,
            d.safety,
            ConstKind::Opaque { value: d.value },
        );
        None
    }

    /// The header checks of `add_mutual` for one member.
    fn check_mutual_header(&mut self, ds: &[Defn], i: usize) {
        let name = ds[i].name;
        let ty = ds[i].ty;
        let lparams = ds[i].lparams.clone();
        if ds[i].safety != ds[0].safety || !names_eq(&lparams, &ds[0].lparams) {
            self.fail(ErrorKind::BadMutual, ty);
            return;
        }
        if defn_index(ds, name) < i {
            self.fail(ErrorKind::BadMutual, ty);
            return;
        }
        self.check_constant_val(name, &lparams, ty);
    }

    /// `add_mutual`: a block of unsafe or partial definitions that may refer to each other. The headers are checked first, then all the members are added, then the values are checked.
    pub fn add_mutual(&mut self, ds: &[Defn]) -> Option<Fault> {
        if ds.len() == 0 {
            let at = self.dummy;
            return self.reject(ErrorKind::BadMutual, at);
        }
        let safety = ds[0].safety;
        self.begin(ds[0].lparams.clone(), safety);
        if safety == Safety::Safe {
            let at = ds[0].ty;
            return self.reject(ErrorKind::BadMutual, at);
        }
        let mut i = 0;
        while i < ds.len() && !self.bad() {
            self.check_mutual_header(ds, i);
            i += 1;
        }
        if self.bad() {
            return self.fault();
        }
        let saved = self.env.len();
        let mut i = 0;
        while i < ds.len() {
            let d = &ds[i];
            let kind = Checker::defn_kind(d);
            let (name, ty, s) = (d.name, d.ty, d.safety);
            let lparams = d.lparams.clone();
            self.add_const(name, lparams, ty, s, kind);
            i += 1;
        }
        self.begin(ds[0].lparams.clone(), safety);
        let mut i = 0;
        while i < ds.len() && !self.bad() {
            let (v, t) = (ds[i].value, ds[i].ty);
            self.check_value(v, t);
            i += 1;
        }
        if self.bad() {
            self.env.truncate(saved);
            return self.fault();
        }
        None
    }

    // Quotients.

    /// `Sort u` for a level parameter name.
    fn sort_param(&mut self, n: NameId) -> (LevelId, ExprId) {
        let l = self.st.level_param(n);
        (l, self.st.mk_sort(l))
    }

    fn prop(&mut self) -> ExprId {
        let z = self.st.level_zero();
        self.st.mk_sort(z)
    }

    fn arrow(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let n = self.st.anon();
        self.st.mk_pi(n, BinderInfo::Default, a, b)
    }

    fn pi(&mut self, a: ExprId, b: ExprId) -> ExprId {
        self.arrow(a, b)
    }

    fn bv(&mut self, i: u32) -> ExprId {
        self.st.mk_bvar(i)
    }

    fn const1(&mut self, n: NameId, l: LevelId) -> ExprId {
        let ls = self.st.level_list(&[l]);
        self.st.mk_const(n, ls)
    }

    /// `α → α → Prop`, where `α` is the bound variable `k` at the binder of the relation.
    fn relation(&mut self, k: u32) -> ExprId {
        let p = self.prop();
        let a1 = self.bv(k + 1);
        let inner = self.arrow(a1, p);
        let a0 = self.bv(k);
        self.arrow(a0, inner)
    }

    /// `check_eq_type`: `Eq.{u} : {α : Sort u} → α → α → Prop` with one constructor `Eq.refl.{u} : {α : Sort u} → (a : α) → Eq a a`.
    fn check_eq_type(&mut self, at: ExprId) {
        let s = self.get_const(self.b.eq, at);
        if s == 0 {
            return;
        }
        let (eq_ty, eq_lps, ctors) = match &self.env.at(s).kind {
            ConstKind::Induct(i) => (
                self.env.at(s).ty,
                self.env.at(s).lparams.clone(),
                i.ctors.clone(),
            ),
            _ => {
                self.fail(ErrorKind::BadQuot, at);
                return;
            }
        };
        if eq_lps.len() != 1 || ctors.len() != 1 {
            self.fail(ErrorKind::BadQuot, at);
            return;
        }
        let (_, su) = self.sort_param(eq_lps[0]);
        let rel = self.relation(0);
        let want = self.pi(su, rel);
        if !self.eq(want, eq_ty) {
            self.fail(ErrorKind::BadQuot, at);
            return;
        }
        let rs = self.get_const(ctors[0], at);
        if rs == 0 {
            return;
        }
        let refl_ty = self.env.at(rs).ty;
        let refl_lps = self.env.at(rs).lparams.clone();
        if refl_lps.len() == 0 {
            self.fail(ErrorKind::BadQuot, at);
            return;
        }
        let (u, su) = self.sort_param(refl_lps[0]);
        let eq_c = self.const1(self.b.eq, u);
        let (b0, b1) = (self.bv(0), self.bv(1));
        let body = self.st.mk_apps(eq_c, &[b1, b0, b0]);
        let inner = self.pi(b0, body);
        let want = self.pi(su, inner);
        if !self.eq(want, refl_ty) {
            self.fail(ErrorKind::BadQuot, at);
        }
    }

    /// The reference type of `Quot.{u}`.
    fn quot_type(&mut self, un: NameId) -> ExprId {
        let (_, su) = self.sort_param(un);
        let rel = self.relation(0);
        let (_, su2) = self.sort_param(un);
        let inner = self.pi(rel, su2);
        self.pi(su, inner)
    }

    /// The reference type of `Quot.mk.{u}`.
    fn quot_mk_type(&mut self, un: NameId) -> ExprId {
        let (u, su) = self.sort_param(un);
        let rel = self.relation(0);
        let q = self.const1(self.b.quot, u);
        let (b1, b2) = (self.bv(1), self.bv(2));
        let qr = self.st.mk_apps(q, &[b2, b1]);
        let a = self.pi(b1, qr);
        let r = self.pi(rel, a);
        self.pi(su, r)
    }

    /// The reference type of `Quot.lift.{u, v}`.
    fn quot_lift_type(&mut self, un: NameId, vn: NameId) -> ExprId {
        let (u, su) = self.sort_param(un);
        let (v, sv) = self.sort_param(vn);
        let rel = self.relation(0);
        // f : α → β at depth 3.
        let (b1, b2) = (self.bv(1), self.bv(2));
        let f_ty = self.arrow(b2, b1);
        // The sanity condition at depth 4: ∀ a b : α, r a b → f a = f b.
        let eq_c = self.const1(self.b.eq, v);
        let (b0, b3, b4) = (self.bv(0), self.bv(3), self.bv(4));
        let fa = self.st.mk_app(b3, b2);
        let fb = self.st.mk_app(b3, b1);
        let eq_ab = self.st.mk_apps(eq_c, &[b4, fa, fb]);
        let rab = self.st.mk_apps(b4, &[b1, b0]);
        let h = self.arrow(rab, eq_ab);
        let b_dom = self.bv(4);
        let all_b = self.pi(b_dom, h);
        let a_dom = self.bv(3);
        let sanity = self.pi(a_dom, all_b);
        // Quot r → β at depth 5.
        let q = self.const1(self.b.quot, u);
        let qr = self.st.mk_apps(q, &[b4, b3]);
        let beta = self.bv(3);
        let last = self.arrow(qr, beta);
        let s = self.arrow(sanity, last);
        let f = self.pi(f_ty, s);
        let b = self.pi(sv, f);
        let r = self.pi(rel, b);
        self.pi(su, r)
    }

    /// The reference type of `Quot.ind.{u}`.
    fn quot_ind_type(&mut self, un: NameId) -> ExprId {
        let (u, su) = self.sort_param(un);
        let rel = self.relation(0);
        let q = self.const1(self.b.quot, u);
        let mk = self.const1(self.b.quot_mk, u);
        let (b0, b1, b2, b3) = (self.bv(0), self.bv(1), self.bv(2), self.bv(3));
        // β : Quot r → Prop at depth 2.
        let q2 = self.st.mk_apps(q, &[b1, b0]);
        let p = self.prop();
        let beta_ty = self.arrow(q2, p);
        // mk : ∀ a : α, β (Quot.mk r a) at depth 3.
        let mka = self.st.mk_apps(mk, &[b3, b2, b0]);
        let body = self.st.mk_app(b1, mka);
        let mk_ty = self.pi(b2, body);
        // ∀ q : Quot r, β q at depth 4.
        let q4 = self.st.mk_apps(q, &[b3, b2]);
        let bq = self.st.mk_app(b2, b0);
        let all_q = self.pi(q4, bq);
        let m = self.pi(mk_ty, all_q);
        let b = self.pi(beta_ty, m);
        let r = self.pi(rel, b);
        self.pi(su, r)
    }

    /// The level parameter names and the reference type of a quotient constant.
    fn quot_reference(&mut self, kind: QuotKind) -> (NameId, Vec<NameId>, ExprId) {
        let root = self.st.anon();
        let u = self.st.name_str_bytes(root, b"u");
        let v = self.st.name_str_bytes(root, b"v");
        let mut lps: Vec<NameId> = Vec::new();
        lps.push(u);
        match kind {
            QuotKind::Type => (self.b.quot, lps, self.quot_type(u)),
            QuotKind::Ctor => (self.b.quot_mk, lps, self.quot_mk_type(u)),
            QuotKind::Lift => {
                lps.push(v);
                (self.b.quot_lift, lps, self.quot_lift_type(u, v))
            }
            QuotKind::Ind => (self.b.quot_ind, lps, self.quot_ind_type(u)),
        }
    }

    /// `add_quot`. The first quotient declaration adds all four constants with the reference types, as the official kernel does. Each exported quotient declaration must then be the reference constant of its kind (spec 06.5).
    pub fn add_quot(&mut self, d: &Quot) -> Option<Fault> {
        self.begin(Vec::new(), Safety::Safe);
        if !self.env.quot_initialized() {
            self.check_eq_type(d.ty);
            let names = [
                self.b.quot,
                self.b.quot_mk,
                self.b.quot_lift,
                self.b.quot_ind,
            ];
            let mut i = 0;
            while i < names.len() && !self.bad() {
                self.check_name(names[i], d.ty);
                i += 1;
            }
            if self.bad() {
                return self.fault();
            }
            let kinds = [
                QuotKind::Type,
                QuotKind::Ctor,
                QuotKind::Lift,
                QuotKind::Ind,
            ];
            let mut i = 0;
            while i < kinds.len() {
                let (n, lps, ty) = self.quot_reference(kinds[i]);
                self.add_const(n, lps, ty, Safety::Safe, ConstKind::Quot { kind: kinds[i] });
                i += 1;
            }
            self.env.mark_quot_initialized();
        }
        let (n, lps, ty) = self.quot_reference(d.kind);
        if d.name != n || !names_eq(&d.lparams, &lps) || !self.eq(d.ty, ty) {
            return self.reject(ErrorKind::BadQuot, d.ty);
        }
        None
    }

    /// Checks one declaration of the stream and adds it to the environment. Then it compares the new primitives with their references (spec 05.8).
    ///
    /// The terms that the check of an axiom, a definition, a theorem, an opaque constant or a mutual block makes go to the scratch tier of the store, and the call removes them at the end (spec 04.8). These constants keep only input terms in the environment, so no scratch handle stays. An inductive or a quotient declaration adds terms that the checker makes, such as the recursor rules, so it uses the frozen tier. If the fault is at a scratch term, `Fault::at` is the dummy term after the call.
    pub fn add_decl(&mut self, d: &Decl) -> Option<Fault> {
        self.sess_start();
        let r0 = match d {
            Decl::Axiom(a) => {
                self.st.set_scratch(true);
                self.add_axiom(a)
            }
            Decl::Defn(x) => {
                self.st.set_scratch(true);
                self.add_definition(x)
            }
            Decl::Thm(t) => {
                self.st.set_scratch(true);
                self.add_theorem(t)
            }
            Decl::Opaque(o) => {
                self.st.set_scratch(true);
                self.add_opaque(o)
            }
            Decl::Quot(q) => self.add_quot(q),
            Decl::Induct(i) => self.add_inductive(i),
            Decl::Mutual(ds) => {
                self.st.set_scratch(true);
                self.add_mutual(ds)
            }
        };
        let r = if r0.is_none() { self.fault() } else { r0 };
        if r.is_none() {
            self.check_pins();
        }
        if r.is_none() && self.st.uses_scratch() {
            // Only an axiom, a definition, a theorem, an opaque constant or a mutual block checks in the scratch tier. The other declarations add temporary constants, so their entries are not kept.
            self.sess_commit();
        }
        self.st.clear_scratch();
        match r {
            Some(f) => {
                if f.at.tier() == Tier::Scratch {
                    Some(Fault {
                        kind: f.kind,
                        at: self.dummy,
                    })
                } else {
                    Some(f)
                }
            }
            None => None,
        }
    }
}
