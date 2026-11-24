//! The Lean object builder of the tests. Each test file uses a part of it.

#![allow(dead_code)]

use rulean_ffi::heap::{OwnedHeap, boxed};
use rulean_store::{ExprId, NameId, Store};

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
