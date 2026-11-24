//! The Lean object builder of the tests. Each test file uses a part of it.

#![allow(dead_code)]

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_ffi::heap::{OwnedHeap, boxed};
use rulean_format::{Hints, QuotKind, Safety};
use rulean_store::{Expr, ExprId, Level, LevelId, Name, NameId, Store};

/// The 8 bytes of `Expr.Data` or `Level.Data`. The conversion does not read them, so the tests put a value that is not a valid hash.
pub const DATA: [u8; 8] = [0xee; 8];

pub fn data_and(b: u8) -> Vec<u8> {
    let mut v = DATA.to_vec();
    v.push(b);
    v
}

/// The Lean object builder of the tests.
pub struct B {
    pub h: OwnedHeap,
}

impl B {
    pub fn new() -> B {
        B {
            h: OwnedHeap::new(),
        }
    }

    pub fn name(&mut self, s: &str) -> u64 {
        let mut n = boxed(0);
        for part in s.split('.') {
            let str = self.h.string(part);
            n = self.h.ctor(1, &[n, str], &DATA);
        }
        n
    }

    pub fn list(&mut self, items: &[u64]) -> u64 {
        let mut l = boxed(0);
        for &x in items.iter().rev() {
            l = self.h.ctor(1, &[x, l], &[]);
        }
        l
    }

    pub fn succ(&mut self, l: u64) -> u64 {
        self.h.ctor(1, &[l], &DATA)
    }

    pub fn param(&mut self, s: &str) -> u64 {
        let n = self.name(s);
        self.h.ctor(4, &[n], &DATA)
    }

    pub fn bvar(&mut self, i: u64) -> u64 {
        self.h.ctor(0, &[boxed(i)], &DATA)
    }

    pub fn sort(&mut self, l: u64) -> u64 {
        self.h.ctor(3, &[l], &DATA)
    }

    pub fn cnst(&mut self, s: &str, ls: &[u64]) -> u64 {
        let n = self.name(s);
        let l = self.list(ls);
        self.h.ctor(4, &[n, l], &DATA)
    }

    pub fn app(&mut self, f: u64, a: u64) -> u64 {
        self.h.ctor(5, &[f, a], &DATA)
    }

    pub fn binder(&mut self, t: u8, s: &str, info: u8, dom: u64, body: u64) -> u64 {
        let n = self.name(s);
        self.h.ctor(t, &[n, dom, body], &data_and(info))
    }

    pub fn lam(&mut self, s: &str, info: u8, dom: u64, body: u64) -> u64 {
        self.binder(6, s, info, dom, body)
    }

    pub fn pi(&mut self, s: &str, info: u8, dom: u64, body: u64) -> u64 {
        self.binder(7, s, info, dom, body)
    }

    pub fn cval(&mut self, s: &str, lps: &[&str], ty: u64) -> u64 {
        let n = self.name(s);
        let ps: Vec<u64> = lps.iter().map(|p| self.name(p)).collect();
        let l = self.list(&ps);
        self.h.ctor(0, &[n, l, ty], &[])
    }

    pub fn axiom(&mut self, s: &str, ty: u64) -> u64 {
        let cv = self.cval(s, &[], ty);
        let v = self.h.ctor(0, &[cv], &[0]);
        self.h.ctor(0, &[v], &[])
    }

    /// A `DefinitionVal` with regular hints of height `height`.
    pub fn defn_val(
        &mut self,
        s: &str,
        lps: &[&str],
        ty: u64,
        value: u64,
        height: u32,
        safety: u8,
    ) -> u64 {
        let cv = self.cval(s, lps, ty);
        let hints = self.h.ctor(2, &[], &height.to_le_bytes());
        let n = self.name(s);
        let all = self.list(&[n]);
        self.h.ctor(0, &[cv, value, hints, all], &[safety])
    }

    /// `Type`.
    pub fn ty(&mut self) -> u64 {
        let one = self.succ(boxed(0));
        self.sort(one)
    }
}

/// The name `s` in the store.
pub fn name(st: &mut Store, s: &str) -> NameId {
    let mut n = st.anon();
    for part in s.split('.') {
        n = st.name_str_bytes(n, part.as_bytes());
    }
    n
}

pub fn ty(st: &mut Store) -> ExprId {
    let z = st.level_zero();
    let one = st.level_succ(z);
    st.mk_sort(one)
}

/// `inductive N | z : N | s : N → N`, as an `inductDecl`.
pub fn nat_like(b: &mut B) -> u64 {
    let t = b.ty();
    let n = b.name("N");
    let z_ty = b.cnst("N", &[]);
    let z_name = b.name("N.z");
    let z = b.h.ctor(0, &[z_name, z_ty], &[]);
    let dom = b.cnst("N", &[]);
    let cod = b.cnst("N", &[]);
    let s_ty = b.pi("n", 0, dom, cod);
    let s_name = b.name("N.s");
    let s = b.h.ctor(0, &[s_name, s_ty], &[]);
    let ctors = b.list(&[z, s]);
    let it = b.h.ctor(0, &[n, t, ctors], &[]);
    let lps = b.list(&[]);
    let types = b.list(&[it]);
    b.h.ctor(6, &[lps, boxed(0), types], &[0])
}

/// The encoder of the tests: it writes the terms of a store as Lean objects. It uses recursion, so it is only for small terms.
impl B {
    pub fn enc_name(&mut self, st: &Store, n: NameId) -> u64 {
        match st.name(n) {
            Name::Anon => boxed(0),
            Name::Str(pre, s) => {
                let p = self.enc_name(st, pre);
                let text = String::from_utf8(st.str_bytes(s).to_vec()).expect("a UTF-8 name");
                let str = self.h.string(&text);
                self.h.ctor(1, &[p, str], &DATA)
            }
            Name::Num(pre, k) => {
                let p = self.enc_name(st, pre);
                self.h.ctor(2, &[p, boxed(k)], &DATA)
            }
        }
    }

    pub fn enc_names(&mut self, st: &Store, ns: &[NameId]) -> u64 {
        let v: Vec<u64> = ns.iter().map(|&n| self.enc_name(st, n)).collect();
        self.list(&v)
    }

    pub fn enc_level(&mut self, st: &Store, l: LevelId) -> u64 {
        match st.level(l) {
            Level::Zero => boxed(0),
            Level::Succ(a) => {
                let a = self.enc_level(st, a);
                self.h.ctor(1, &[a], &DATA)
            }
            Level::Max(a, b) => {
                let a = self.enc_level(st, a);
                let b = self.enc_level(st, b);
                self.h.ctor(2, &[a, b], &DATA)
            }
            Level::IMax(a, b) => {
                let a = self.enc_level(st, a);
                let b = self.enc_level(st, b);
                self.h.ctor(3, &[a, b], &DATA)
            }
            Level::Param(n) => {
                let n = self.enc_name(st, n);
                self.h.ctor(4, &[n], &DATA)
            }
        }
    }

    pub fn enc_expr(&mut self, st: &Store, e: ExprId) -> u64 {
        match st.node(e) {
            Expr::BVar(i) => self.bvar(u64::from(i)),
            Expr::Sort(l) => {
                let l = self.enc_level(st, l);
                self.sort(l)
            }
            Expr::Const(n, ls) => {
                let n = self.enc_name(st, n);
                let v: Vec<u64> = st
                    .level_list_vec(ls)
                    .into_iter()
                    .map(|l| self.enc_level(st, l))
                    .collect();
                let l = self.list(&v);
                self.h.ctor(4, &[n, l], &DATA)
            }
            Expr::App(f, a) => {
                let f = self.enc_expr(st, f);
                let a = self.enc_expr(st, a);
                self.app(f, a)
            }
            Expr::Lam(bd) | Expr::Pi(bd) => {
                let t = if matches!(st.node(e), Expr::Lam(_)) {
                    6
                } else {
                    7
                };
                let n = self.enc_name(st, bd.name);
                let dom = self.enc_expr(st, bd.dom);
                let body = self.enc_expr(st, bd.body);
                self.h.ctor(t, &[n, dom, body], &data_and(bd.info as u8))
            }
            other => panic!("the test encoder does not write {other:?}"),
        }
    }

    fn enc_cval(&mut self, st: &Store, k: &ConstInfo) -> u64 {
        let n = self.enc_name(st, k.name);
        let l = self.enc_names(st, &k.lparams);
        let t = self.enc_expr(st, k.ty);
        self.h.ctor(0, &[n, l, t], &[])
    }

    /// The `ConstantInfo` object of `k`.
    pub fn enc_const(&mut self, st: &Store, k: &ConstInfo) -> u64 {
        let cv = self.enc_cval(st, k);
        let uns = u8::from(k.safety == Safety::Unsafe);
        let (t, v) = match &k.kind {
            ConstKind::Axiom => (0, self.h.ctor(0, &[cv], &[uns])),
            ConstKind::Defn { value, hints } => {
                let value = self.enc_expr(st, *value);
                let hints = match hints {
                    Hints::Opaque => boxed(0),
                    Hints::Abbrev => boxed(1),
                    Hints::Regular(h) => self.h.ctor(2, &[], &h.to_le_bytes()),
                };
                let all = self.enc_names(st, &[k.name]);
                let safety = match k.safety {
                    Safety::Unsafe => 0,
                    Safety::Safe => 1,
                    Safety::Partial => 2,
                };
                (1, self.h.ctor(0, &[cv, value, hints, all], &[safety]))
            }
            ConstKind::Thm { value } => {
                let value = self.enc_expr(st, *value);
                let all = self.enc_names(st, &[k.name]);
                (2, self.h.ctor(0, &[cv, value, all], &[]))
            }
            ConstKind::Opaque { value } => {
                let value = self.enc_expr(st, *value);
                let all = self.enc_names(st, &[k.name]);
                (3, self.h.ctor(0, &[cv, value, all], &[uns]))
            }
            ConstKind::Quot { kind } => {
                let q = match kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                };
                (4, self.h.ctor(0, &[cv], &[q]))
            }
            ConstKind::Induct(i) => {
                let all = self.enc_names(st, &i.all);
                let ctors = self.enc_names(st, &i.ctors);
                let objs = [
                    cv,
                    boxed(u64::from(i.nparams)),
                    boxed(u64::from(i.nindices)),
                    all,
                    ctors,
                    boxed(u64::from(i.nnested)),
                ];
                let sc = [u8::from(i.is_rec), uns, u8::from(i.is_reflexive)];
                (5, self.h.ctor(0, &objs, &sc))
            }
            ConstKind::Ctor(c) => {
                let induct = self.enc_name(st, c.induct);
                let objs = [
                    cv,
                    induct,
                    boxed(u64::from(c.cidx)),
                    boxed(u64::from(c.nparams)),
                    boxed(u64::from(c.nfields)),
                ];
                (6, self.h.ctor(0, &objs, &[uns]))
            }
            ConstKind::Rec(r) => {
                let all = self.enc_names(st, &r.all);
                let mut rules = Vec::new();
                for rule in &r.rules {
                    let c = self.enc_name(st, rule.ctor);
                    let rhs = self.enc_expr(st, rule.rhs);
                    rules.push(
                        self.h
                            .ctor(0, &[c, boxed(u64::from(rule.nfields)), rhs], &[]),
                    );
                }
                let rules = self.list(&rules);
                let objs = [
                    cv,
                    all,
                    boxed(u64::from(r.nparams)),
                    boxed(u64::from(r.nindices)),
                    boxed(u64::from(r.nmotives)),
                    boxed(u64::from(r.nminors)),
                    rules,
                ];
                (7, self.h.ctor(0, &objs, &[u8::from(r.k), uns]))
            }
        };
        self.h.ctor(t, &[v], &[])
    }
}
