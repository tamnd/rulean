//! Tests of the level functions. The expected values follow `level.cpp` of the official kernel, v4.35.0.

use rulean_core::level::{
    LevelCache, instantiate, is_equivalent, is_geq, is_not_zero, mk_imax, mk_max, name_cmp,
    normalize, normalizes_to_zero, undef_param,
};
use rulean_store::{LevelId, NameId, Store};

struct T {
    st: Store,
    c: LevelCache,
}

impl T {
    fn new() -> T {
        T {
            st: Store::new(),
            c: LevelCache::new(),
        }
    }
    fn name(&mut self, s: &str) -> NameId {
        let mut n = self.st.anon();
        for part in s.split('.') {
            n = match part.parse::<u64>() {
                Ok(k) => self.st.name_num(n, k),
                Err(_) => self.st.name_str_bytes(n, part.as_bytes()),
            };
        }
        n
    }
    fn p(&mut self, s: &str) -> LevelId {
        let n = self.name(s);
        self.st.level_param(n)
    }
    fn z(&self) -> LevelId {
        self.st.level_zero()
    }
    fn s(&mut self, l: LevelId) -> LevelId {
        self.st.level_succ(l)
    }
    fn n(&mut self, k: u32) -> LevelId {
        let mut l = self.z();
        for _ in 0..k {
            l = self.s(l);
        }
        l
    }
    fn max(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.st.level_max(a, b)
    }
    fn imax(&mut self, a: LevelId, b: LevelId) -> LevelId {
        self.st.level_imax(a, b)
    }
    fn norm(&mut self, l: LevelId) -> LevelId {
        normalize(&mut self.st, &mut self.c, l)
    }
    fn eqv(&mut self, a: LevelId, b: LevelId) -> bool {
        is_equivalent(&mut self.st, &mut self.c, a, b)
    }
    fn geq(&mut self, a: LevelId, b: LevelId) -> bool {
        is_geq(&mut self.st, &mut self.c, a, b)
    }
}

#[test]
fn mk_max_simplifies() {
    let mut t = T::new();
    let (u, v, one, two) = (t.p("u"), t.p("v"), t.n(1), t.n(2));
    let z = t.z();
    assert_eq!(mk_max(&mut t.st, one, two), two);
    assert_eq!(mk_max(&mut t.st, two, one), two);
    assert_eq!(mk_max(&mut t.st, u, z), u);
    assert_eq!(mk_max(&mut t.st, z, u), u);
    assert_eq!(mk_max(&mut t.st, u, u), u);
    let uv = t.max(u, v);
    assert_eq!(mk_max(&mut t.st, u, uv), uv);
    assert_eq!(mk_max(&mut t.st, uv, v), uv);
    let su = t.s(u);
    assert_eq!(mk_max(&mut t.st, su, u), su);
    assert_eq!(mk_max(&mut t.st, u, su), su);
    assert_eq!(mk_max(&mut t.st, u, v), uv);
}

#[test]
fn mk_imax_simplifies() {
    let mut t = T::new();
    let (u, v, one) = (t.p("u"), t.p("v"), t.n(1));
    let z = t.z();
    let u1 = t.max(u, one);
    assert_eq!(mk_imax(&mut t.st, u, one), u1);
    assert_eq!(mk_imax(&mut t.st, u, z), z);
    assert_eq!(mk_imax(&mut t.st, z, v), v);
    assert_eq!(mk_imax(&mut t.st, one, v), v);
    assert_eq!(mk_imax(&mut t.st, u, u), u);
    let uv = t.imax(u, v);
    assert_eq!(mk_imax(&mut t.st, u, v), uv);
}

#[test]
fn normalize_sorts_and_merges() {
    let mut t = T::new();
    let (u, v) = (t.p("u"), t.p("v"));
    let uv = t.max(u, v);
    let vu = t.max(v, u);
    assert_eq!(t.norm(vu), uv);
    let su = t.s(u);
    let usu = t.max(u, su);
    assert_eq!(t.norm(usu), su);
    // The explicit level 1 is covered by succ u.
    let one = t.n(1);
    let one_su = t.max(one, su);
    assert_eq!(t.norm(one_su), su);
    // The explicit level 2 is not covered by succ u.
    let two = t.n(2);
    let two_su = t.max(two, su);
    assert_eq!(t.norm(two_su), two_su);
    // succ (max u v) is max (succ u) (succ v).
    let s_uv = t.s(uv);
    let sv = t.s(v);
    let su_sv = t.max(su, sv);
    assert_eq!(t.norm(s_uv), su_sv);
    // max (max u 1) (max 0 v) is max 1 (max u v).
    let z = t.z();
    let a = t.max(u, one);
    let b = t.max(z, v);
    let ab = t.max(a, b);
    let want = t.max(one, uv);
    assert_eq!(t.norm(ab), want);
    // The cache gives the same handle.
    assert_eq!(t.norm(ab), want);
}

#[test]
fn equivalence() {
    let mut t = T::new();
    let (u, v) = (t.p("u"), t.p("v"));
    let uv = t.max(u, v);
    let vu = t.max(v, u);
    assert!(t.eqv(uv, vu));
    let iuv = t.imax(u, v);
    assert!(!t.eqv(iuv, uv));
    let sv = t.s(v);
    let iusv = t.imax(u, sv);
    let musv = t.max(u, sv);
    assert!(t.eqv(iusv, musv));
    assert!(!t.eqv(u, v));
}

#[test]
fn greater_or_equal() {
    let mut t = T::new();
    let (u, v) = (t.p("u"), t.p("v"));
    let z = t.z();
    let su = t.s(u);
    assert!(t.geq(su, u));
    assert!(!t.geq(u, su));
    let uv = t.max(u, v);
    assert!(t.geq(uv, u));
    assert!(!t.geq(u, uv));
    assert!(t.geq(u, z));
    let iuv = t.imax(u, v);
    assert!(t.geq(iuv, v));
    let s_uv = t.s(uv);
    assert!(t.geq(s_uv, su));
    let (one, two) = (t.n(1), t.n(2));
    assert!(t.geq(two, one));
    assert!(!t.geq(one, two));
}

#[test]
fn zero_tests() {
    let mut t = T::new();
    let u = t.p("u");
    let z = t.z();
    let iu0 = t.imax(u, z);
    assert!(normalizes_to_zero(&t.st, iu0));
    let zz = t.max(z, z);
    assert!(normalizes_to_zero(&t.st, zz));
    let uz = t.max(u, z);
    assert!(!normalizes_to_zero(&t.st, uz));
    let su = t.s(u);
    assert!(is_not_zero(&t.st, su));
    assert!(!is_not_zero(&t.st, u));
    let isu = t.imax(u, su);
    assert!(is_not_zero(&t.st, isu));
}

#[test]
fn instantiation() {
    let mut t = T::new();
    let (nu, nv) = (t.name("u"), t.name("v"));
    let (u, v, w) = (t.p("u"), t.p("v"), t.p("w"));
    let (z, one) = (t.z(), t.n(1));
    let uv = t.max(u, v);
    assert_eq!(instantiate(&mut t.st, uv, &[nu, nv], &[z, one]), one);
    let iuv = t.imax(u, v);
    assert_eq!(instantiate(&mut t.st, iuv, &[nv], &[z]), z);
    let su = t.s(u);
    let sv = t.s(v);
    assert_eq!(instantiate(&mut t.st, su, &[nu], &[v]), sv);
    assert_eq!(instantiate(&mut t.st, w, &[nu, nv], &[z, z]), w);
    // An unchanged node keeps its handle and is not simplified.
    let ww = t.max(w, w);
    assert_eq!(instantiate(&mut t.st, ww, &[nu], &[z]), ww);
}

#[test]
fn undefined_parameter() {
    let mut t = T::new();
    let (nu, nv) = (t.name("u"), t.name("v"));
    let (u, v) = (t.p("u"), t.p("v"));
    let uv = t.max(u, v);
    assert_eq!(undef_param(&t.st, uv, &[nu, nv]), 0);
    assert_eq!(undef_param(&t.st, uv, &[nu]), nv.0 + 1);
    let z = t.z();
    assert_eq!(undef_param(&t.st, z, &[]), 0);
}

#[test]
fn name_order() {
    let mut t = T::new();
    let a = t.name("a");
    let b = t.name("b");
    let ab = t.name("a.b");
    let a1 = t.name("a.1");
    let a2 = t.name("a.2");
    let a10 = t.name("a.10");
    let aa = t.name("aa");
    assert_eq!(name_cmp(&t.st, a, a), 0);
    assert_eq!(name_cmp(&t.st, a, b), -1);
    assert_eq!(name_cmp(&t.st, b, a), 1);
    assert_eq!(name_cmp(&t.st, a, ab), -1);
    assert_eq!(name_cmp(&t.st, a1, ab), -1);
    assert_eq!(name_cmp(&t.st, a2, a10), -1);
    assert_eq!(name_cmp(&t.st, a, aa), -1);
    assert_eq!(name_cmp(&t.st, ab, b), -1);
}
