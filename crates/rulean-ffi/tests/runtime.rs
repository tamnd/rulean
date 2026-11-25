//! Tests with the Lean runtime of the toolchain (spec 09.6.3).
//!
//! The test loads `libleanshared` of Lean v4.36.0, writes terms of the store with `LeanMake`, and gives the objects to functions of Lean. The variable `RULEAN_LEAN_LIB` gives the path of the library. If it is not set, the test uses the library of the elan toolchain `leanprover--lean4---v4.36.0` if it is there, and else it does nothing. If `RULEAN_LEAN_LIB` is set, a library that does not load is a failure.
//!
//! The Lean runtime is initialized one time in a process, and its objects stay on one thread, so all the checks are in one test.

#![cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
#![allow(unsafe_code)]

mod common;

use std::ffi::{CStr, c_void};
use std::path::PathBuf;

use common::{qname, sample};
use rulean_ffi::conv::{Cache, Converter};
use rulean_ffi::heap::Heap;
use rulean_ffi::live::LiveHeap;
use rulean_ffi::make::Encoder;
use rulean_ffi::rt::{LeanMake, Runtime};
use rulean_store::{BinderInfo, Store};

/// The library of the toolchain, or `None` if the test has no library.
fn library() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("RULEAN_LEAN_LIB") {
        return Some(PathBuf::from(p));
    }
    let home = std::env::var_os("HOME")?;
    let ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let p = PathBuf::from(home)
        .join(".elan/toolchains/leanprover--lean4---v4.36.0/lib/lean")
        .join(format!("libleanshared.{ext}"));
    p.exists().then_some(p)
}

/// The function `name` of the runtime with the type `F`.
///
/// # Safety
///
/// `F` is the type of the Lean function, as a function pointer.
unsafe fn func<F: Copy>(rt: &Runtime, name: &CStr) -> F {
    let p = rt
        .symbol(name)
        .unwrap_or_else(|| panic!("the runtime has no {name:?}"));
    assert_eq!(size_of::<F>(), size_of::<*mut c_void>());
    // SAFETY: the caller gives the type of the function, and a function pointer has the size of a data pointer.
    unsafe { core::mem::transmute_copy::<*mut c_void, F>(&p.as_ptr()) }
}

fn word(h: &LiveHeap, a: u64) -> u64 {
    let mut b = [0u8; 8];
    assert!(h.read(a, &mut b));
    u64::from_le_bytes(b)
}

/// The reference count of the object `o`.
fn rc(h: &LiveHeap, o: u64) -> i32 {
    word(h, o) as u32 as i32
}

/// The bytes of the Lean string `s`, without its zero byte.
fn string(h: &LiveHeap, s: u64) -> String {
    let size = word(h, s + 8) as usize;
    let mut b = vec![0u8; size - 1];
    assert!(h.read(s + 32, &mut b));
    String::from_utf8(b).expect("UTF-8")
}

#[test]
fn terms_made_with_the_lean_runtime() {
    let Some(lib) = library() else {
        eprintln!("no Lean v4.36.0 library: set RULEAN_LEAN_LIB to run this test");
        return;
    };
    // SAFETY: the library is the `libleanshared` of Lean v4.36.0, and this test is the only code of the process that uses Lean.
    let rt = unsafe { Runtime::open(&lib) }.expect("the Lean runtime");
    // SAFETY: the objects are made by the Lean runtime and stay alive while `h` is used.
    let h = unsafe { LiveHeap::new() };
    // SAFETY: these are the types of the Lean functions of v4.36.0. `Expr.dbgToString` and `Expr.equal` borrow their arguments.
    let (to_string, equal) = unsafe {
        (
            func::<unsafe extern "C" fn(u64) -> u64>(&rt, c"lean_expr_dbg_to_string"),
            func::<unsafe extern "C" fn(u64, u64) -> u8>(&rt, c"lean_expr_equal"),
        )
    };

    // Each kind of term and constant goes to Lean and back with the same handles.
    let mut st = Store::new();
    let k = sample(&mut st);
    let o = {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(&rt) };
        Encoder::new(&mut m, &st)
            .constant(&k, &[k.name])
            .expect("an object")
    };
    let got = Converter::new(&h, &mut st).constant(o).expect("a constant");
    assert_eq!(got, k);
    assert_eq!(rc(&h, o), 1, "the caller has the only reference");
    // SAFETY: the test owns `o`, and does not use it again.
    unsafe { rt.dec(o) };

    // A term in Lean: `fun (x : Prop) => f x x`, where `f x` is one object two times.
    let x = qname(&mut st, "x");
    let f = qname(&mut st, "f");
    let z = st.level_zero();
    let prop = st.mk_sort(z);
    let none = st.level_list(&[]);
    let fc = st.mk_const(f, none);
    let b0 = st.mk_bvar(0);
    let fx = st.mk_app(fc, b0);
    let body = st.mk_app(fx, b0);
    let lam = st.mk_lam(x, BinderInfo::Default, prop, body);
    let make = || {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(&rt) };
        Encoder::new(&mut m, &st).expr(lam).expect("an object")
    };
    let a = make();
    let b = make();
    assert_ne!(a, b, "two encoders make two objects");
    // SAFETY: `a` and `b` are live expressions, and the two functions borrow them.
    unsafe {
        let s = to_string(a);
        assert_eq!(string(&h, s), "fun (x : Prop) => f x x");
        rt.dec(s);
        assert_eq!(equal(a, b), 1);
    }
    // Lean computed the `Expr.Data` of each node: the word after the three fields of `lam`. Its low 32 bits are the hash.
    assert_eq!(word(&h, a + 32), word(&h, b + 32));
    assert_ne!(word(&h, a + 32) as u32, 0);
    // The body `app (app f x) x`: the encoder dropped its own references, so each count is the number of parents.
    let body_o = word(&h, a + 24);
    let fx_o = word(&h, body_o + 8);
    let x_o = word(&h, body_o + 16);
    assert_eq!(word(&h, fx_o + 16), x_o, "`x` is one object");
    assert_eq!(rc(&h, a), 1);
    assert_eq!(rc(&h, body_o), 1);
    assert_eq!(rc(&h, x_o), 2);
    // SAFETY: the test owns `a` and `b`, and does not use them again. The runtime frees them.
    unsafe {
        rt.dec(a);
        rt.dec(b);
    }

    // The cache of a store keeps the handles of the persistent objects, and only of these objects (spec 09.6.3).
    // SAFETY: this is the type of the Lean function of v4.36.0.
    let mark_persistent =
        unsafe { func::<unsafe extern "C" fn(u64)>(&rt, c"lean_mark_persistent") };
    let p = make();
    let q = make();
    // SAFETY: `p` is a live object of this thread. The call gives each object of `p` the count 0, so the runtime does not free it.
    unsafe { mark_persistent(p) };
    assert_eq!(rc(&h, p), 0);
    let mut cache = Cache::default();
    let got = Converter::with_cache(&h, &mut st, &mut cache).expr(p);
    assert_eq!(got.expect("a term"), lam);
    let n = cache.len();
    assert!(n > 0, "the cache has the objects of `p`");
    let got = Converter::with_cache(&h, &mut st, &mut cache).expr(q);
    assert_eq!(got.expect("a term"), lam);
    assert_eq!(cache.len(), n, "the objects of `q` are not persistent");
    let got = Converter::with_cache(&h, &mut st, &mut cache).expr(p);
    assert_eq!(got.expect("a term"), lam);
    assert_eq!(cache.len(), n);
    // With the scratch tier, the converter does not use the cache, and it leaves the cache as it is.
    st.set_scratch(true);
    let got = Converter::with_cache(&h, &mut st, &mut cache).expr(p);
    assert_eq!(got.expect("a term"), lam);
    assert_eq!(cache.len(), n);
    st.clear_scratch();
    // A local context turns the cache off, and the converter does not change the cache.
    let lctx = {
        // SAFETY: this is the type of the Lean function of v4.36.0.
        let mk =
            unsafe { func::<unsafe extern "C" fn(u64) -> u64>(&rt, c"lean_mk_empty_local_ctx") };
        // SAFETY: the argument is a boxed unit.
        unsafe { mk(1) }
    };
    {
        let mut c = Converter::with_cache(&h, &mut st, &mut cache);
        c.local_context(lctx).expect("a local context");
        assert_eq!(c.expr(p).expect("a term"), lam);
    }
    assert_eq!(cache.len(), n);
    // SAFETY: the test owns `q` and `lctx`, and does not use them again.
    unsafe {
        rt.dec(q);
        rt.dec(lctx);
    }

    // A deep term goes to Lean and is freed without a stack overflow.
    let mut t = fc;
    for _ in 0..100_000 {
        t = st.mk_app(t, t);
    }
    let d = {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(&rt) };
        Encoder::new(&mut m, &st).expr(t).expect("an object")
    };
    let top = word(&h, d + 8);
    assert_eq!(top, word(&h, d + 16));
    assert_eq!(rc(&h, top), 2);
    // SAFETY: the test owns `d`, and does not use it again.
    unsafe { rt.dec(d) };
}
