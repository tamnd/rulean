//! The dual-kernel test (spec 09.6.5 and 11.3). Each declaration goes to the C++ kernel of Lean v4.36.0 and to rulean in one process, and the two verdicts must be the same.
//!
//! The test writes each declaration as a Lean `Declaration` object with `LeanMake`. The C++ kernel gets the object through `lean_add_decl`. rulean gets the same object through `conv::declaration`, as in the in-process mode. After the declarations, the test reads the constants of the C++ environment with `lean_environment_find` and compares them with the constants of rulean, so the recursors that the two kernels make must also be the same.
//!
//! Each declaration also goes to `Kernel::add_decl`, the `addDecl` of rulean on the Lean runtime, with the same environment as the C++ kernel. The verdict must be the same. For an accepted declaration, the new constants of the two result environments must be the same. For a rejection, the two `Kernel.Exception` objects must have the same constructor, if `Kernel::add_decl` maps the kind.
//!
//! Each declaration also goes to `lean_add_decl_without_checking` of the C++ kernel and to `Kernel::add_decl_without_checking`, with the same environment. The verdicts and the declared constants must be the same. These results are not used for the next declaration.
//!
//! With the feature `export`, each declaration also goes to the exported symbols `lean_add_decl` and `lean_add_decl_without_checking` of rulean, and the results must be the results of `Kernel::add_decl` and `Kernel::add_decl_without_checking`.
//!
//! For each accepted declaration, the test finds the heartbeats of the C++ kernel and of `Kernel::add_decl`: the smallest limit with which the kernel accepts. A smaller limit must give `deterministicTimeout`. The count of rulean must not be above the count of the C++ kernel (spec 09.6.4). The test sets the heartbeats of the thread to 0 with `lean::reset_heartbeat` before each call.
//!
//! After the declarations, the test gives terms in a local context to `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check` of the C++ kernel and to `Kernel::is_def_eq`, `Kernel::whnf` and `Kernel::check`, with the final environment. The results must be the same. With the feature `export`, the exported symbols of rulean must give the same results.
//!
//! The library comes from `RULEAN_LEAN_LIB` or the elan toolchain, as in `tests/runtime.rs`.

#![cfg(all(
    any(target_os = "linux", target_os = "macos"),
    target_pointer_width = "64"
))]
#![allow(unsafe_code)]

mod common;

use std::ffi::{CStr, c_void};
use std::path::PathBuf;

use common::qname;
use rulean_core::env::ConstInfo;
use rulean_core::tc::Checker;
use rulean_ffi::conv::{self, Converter};
use rulean_ffi::heap::{Heap, boxed};
use rulean_ffi::kernel::Kernel;
use rulean_ffi::live::LiveHeap;
use rulean_ffi::make::{Encoder, Make};
use rulean_ffi::rt::{LeanMake, Runtime};
use rulean_format::{
    Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Quot, QuotKind, Safety, Thm,
};
use rulean_store::{BinderInfo, ExprId, NameId, Store};

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

/// # Safety
///
/// `F` is the type of the Lean function, as a function pointer.
unsafe fn func<F: Copy>(rt: &Runtime, name: &CStr) -> F {
    let p = rt
        .symbol(name)
        .unwrap_or_else(|| panic!("the runtime has no {name:?}"));
    assert_eq!(size_of::<F>(), size_of::<*mut c_void>());
    // SAFETY: the caller gives the type of the function.
    unsafe { core::mem::transmute_copy::<*mut c_void, F>(&p.as_ptr()) }
}

fn word(h: &LiveHeap, a: u64) -> u64 {
    let mut b = [0u8; 8];
    assert!(h.read(a, &mut b));
    u64::from_le_bytes(b)
}

/// The tag of the object `o`.
fn tag(h: &LiveHeap, o: u64) -> u8 {
    (word(h, o) >> 56) as u8
}

type AddDecl = unsafe extern "C" fn(u64, usize, usize, u64, u64) -> u64;
type AddUnchecked = unsafe extern "C" fn(u64, u64) -> u64;
type Find = unsafe extern "C" fn(u64, u64) -> u64;
type Reset = unsafe extern "C" fn();

/// The tag of `Kernel.Exception.deterministicTimeout`.
const TIMEOUT: u64 = 13;

/// The tag of `Kernel.Exception.interrupted`.
const INTERRUPTED: u64 = 16;

/// The two kernels and their environments.
struct Dual<'a> {
    rt: &'a Runtime,
    h: LiveHeap,
    add_decl: AddDecl,
    /// `lean_add_decl_without_checking` of the C++ kernel.
    unchecked: AddUnchecked,
    find: Find,
    /// `lean::reset_heartbeat` of the C++ runtime. It sets the heartbeats of the thread to 0.
    reset: Reset,
    /// The in-process kernel of rulean on the Lean runtime.
    kernel: Kernel<'a>,
    /// Two `Option IO.CancelToken` objects: `some` of a set token and `some` of a token that is not set. The test owns one reference to each.
    cancel: (u64, u64),
    /// The C++ kernel environment. The test owns one reference.
    env: u64,
    chk: Checker,
}

/// The verdicts of one declaration.
struct Verdicts {
    /// The C++ kernel accepts.
    cpp: bool,
    /// The checker of rulean, with the environment of the earlier declarations, accepts.
    ours: bool,
    /// `Kernel::add_decl` on the Lean environment accepts.
    kernel: bool,
    /// For a rejection, the tags of the `Kernel.Exception` of the C++ kernel and of `Kernel::add_decl`.
    tags: Option<(u64, u64)>,
    /// For a rejection with a local context, the number of declarations of the context of the C++ kernel and of `Kernel::add_decl`.
    locals: (Option<u64>, Option<u64>),
    /// For an accepted declaration, the heartbeats of the C++ kernel and of `Kernel::add_decl`.
    beats: Option<(u64, u64)>,
    /// For an accepted declaration, true if the C++ kernel gives `interrupted` with a set cancel token.
    cancel: Option<bool>,
}

/// The tag of a `Kernel.Exception`. A constructor without fields is a boxed scalar.
fn exc_tag(h: &LiveHeap, x: u64) -> u64 {
    if x & 1 == 1 { x >> 1 } else { tag(h, x) as u64 }
}

/// For a `Kernel.Exception` with a local context (the tags 5 to 10), the number of declarations of the context. The context is the second field.
fn exc_locals(rt: &Runtime, h: &LiveHeap, x: u64) -> Option<u64> {
    if !(5..=10).contains(&exc_tag(h, x)) {
        return None;
    }
    // SAFETY: `LocalContext.numIndices` consumes its argument and gives a small `Nat`, so the test gives it a new reference.
    unsafe {
        let num = func::<unsafe extern "C" fn(u64) -> u64>(rt, c"lean_local_ctx_num_indices");
        let lctx = word(h, x + 16);
        rt.inc(lctx);
        Some(num(lctx) >> 1)
    }
}

/// Requires that two exceptions with the tag `tag` have local contexts that agree. `a` and `b` are the numbers of declarations of the contexts of the C++ kernel and of rulean. The context of rulean must have at least the declarations of the C++ context. The C++ kernel removes the free variables of a binder at the end of its scope, and rulean keeps each free variable of the check, so its context can have more.
fn same_locals(tag: u64, a: Option<u64>, b: Option<u64>, what: &str) {
    eprintln!("exception of {what}: tag {tag}, local declarations {a:?} (C++) and {b:?} (rulean)");
    assert_eq!(
        a.is_some(),
        b.is_some(),
        "one exception of {what} has no local context"
    );
    assert!(b >= a, "the local context of rulean is smaller on {what}");
}

impl Dual<'_> {
    /// Gives `d` of the store `st` to the C++ kernel, to the checker of rulean, and to `Kernel::add_decl`. For an accepted declaration, it requires that the C++ kernel and `Kernel::add_decl` add the same constants. The C++ environment is the environment of the next declaration.
    fn add(&mut self, st: &Store, d: &Decl) -> Verdicts {
        let o = {
            // SAFETY: the encoder gives the maker only objects that it made.
            let mut m = unsafe { LeanMake::new(self.rt) };
            Encoder::new(&mut m, st).declaration(d).expect("an object")
        };
        // The two `addDecl` functions consume the environment, so the test gives each a new reference and keeps its own. They borrow the declaration and the cancel token.
        // SAFETY: `env` and `o` are live objects, and the functions have the type of `addDeclCore`.
        let (r, r2) = unsafe {
            self.rt.inc(self.env);
            let r = (self.add_decl)(self.env, 0, 512, o, boxed(0));
            self.rt.inc(self.env);
            let r2 = self.kernel.add_decl(self.env, 0, 512, o, boxed(0));
            (r, r2)
        };
        let before = self.chk.env.len();
        let got = conv::declaration(&self.h, &mut self.chk.st, o).expect("a declaration");
        let ours = self.chk.add_decl(&got).is_none();
        self.same_unchecked(&got, o);
        // `Except.error` has the tag 0 and `Except.ok` has the tag 1.
        let cpp = tag(&self.h, r) == 1;
        let kernel = tag(&self.h, r2) == 1;
        let new_cpp = word(&self.h, r + 8);
        let new_ours = word(&self.h, r2 + 8);
        let mut tags = None;
        let mut locals = (None, None);
        if cpp && kernel {
            for slot in before + 1..=self.chk.env.len() {
                let n = self.chk.env.at(slot as u32).name;
                let a = self.constant(new_cpp, n);
                let b = self.constant(new_ours, n);
                assert!(a.is_some(), "the C++ kernel has no {n:?}");
                assert_eq!(a, b, "the two environments differ at {n:?}");
            }
        } else if !cpp && !kernel {
            tags = Some((exc_tag(&self.h, new_cpp), exc_tag(&self.h, new_ours)));
            locals = (
                exc_locals(self.rt, &self.h, new_cpp),
                exc_locals(self.rt, &self.h, new_ours),
            );
        }
        // The comparison of the dual-kernel build (spec 11.3) must find no difference when the verdicts and the constructors are the same. A C++ result that is not the same verdict must be a difference.
        let agree = cpp == kernel && tags.is_none_or(|(a, b)| a == b);
        // SAFETY: `o`, `r` and `r2` are live, and `r` and `r2` have a `Kernel.Environment`.
        let diff = unsafe { self.kernel.compare_add(o, r, r2, false) };
        assert_eq!(
            diff.is_none(),
            agree,
            "compare_add on {:?}: {diff:?}",
            d.name()
        );
        if kernel {
            // SAFETY: the maker makes `Except.error (Kernel.Exception.other "x")`, and the test owns it.
            unsafe {
                let mut m = LeanMake::new(self.rt);
                let msg = m.string(b"x");
                let exc = m.ctor(12, &[msg], &[]);
                let err = m.ctor(0, &[exc], &[]);
                assert!(
                    self.kernel.compare_add(o, err, r2, false).is_some(),
                    "compare_add accepts an error and a success"
                );
                self.rt.dec(err);
            }
        }
        #[cfg(feature = "export")]
        self.same_as_export(d, o, r2, before);
        let beats = (cpp && kernel).then(|| self.same_heartbeats(d, o));
        let cancel = (cpp && kernel).then(|| self.same_cancel(d, o));
        if cpp {
            // SAFETY: `new_cpp` is a field of `r`, which the test owns. The test takes a reference to it and gives back the old environment.
            unsafe {
                self.rt.inc(new_cpp);
                self.rt.dec(self.env);
            }
            self.env = new_cpp;
        }
        // SAFETY: the test owns `r`, `r2` and `o`.
        unsafe {
            self.rt.dec(r);
            self.rt.dec(r2);
            self.rt.dec(o);
        }
        Verdicts {
            cpp,
            ours,
            kernel,
            tags,
            locals,
            beats,
            cancel,
        }
    }

    /// Gives the accepted declaration `o` to the C++ kernel and to `Kernel::add_decl` with each cancel token. With the token that is not set, the two kernels must accept. With the set token, `Kernel::add_decl` must give `interrupted`, and the result tells if the C++ kernel gives it too. The C++ kernel reads the token only at a heartbeat, so a declaration that it checks without a heartbeat is accepted.
    fn same_cancel(&mut self, d: &Decl, o: u64) -> bool {
        let (set, unset) = self.cancel;
        // The result of a kernel and a token: `None` if the kernel accepts, or the tag of the exception.
        let run = |cpp: bool, tk: u64| -> Option<u64> {
            // SAFETY: `env`, `o` and `tk` are live objects. The functions consume the environment, so the test gives each call a new reference. They borrow the declaration and the token.
            let r = unsafe {
                self.rt.inc(self.env);
                if cpp {
                    (self.add_decl)(self.env, 0, 512, o, tk)
                } else {
                    self.kernel.add_decl(self.env, 0, 512, o, tk)
                }
            };
            let x = (tag(&self.h, r) == 0).then(|| exc_tag(&self.h, word(&self.h, r + 8)));
            // SAFETY: the test owns `r`.
            unsafe { self.rt.dec(r) };
            x
        };
        assert_eq!(
            run(true, unset),
            None,
            "the C++ kernel with a token that is not set rejects {d:?}"
        );
        assert_eq!(
            run(false, unset),
            None,
            "add_decl with a token that is not set rejects {d:?}"
        );
        assert_eq!(
            run(false, set),
            Some(INTERRUPTED),
            "add_decl with a set token on {d:?}"
        );
        #[cfg(feature = "export")]
        {
            // SAFETY: as for `run`. The symbol consumes the environment and borrows the declaration and the token.
            let r = unsafe {
                self.rt.inc(self.env);
                rulean_ffi::export::lean_add_decl(self.env, 0, 512, o, set)
            };
            assert_eq!(
                tag(&self.h, r),
                0,
                "the exported symbol with a set token accepts {d:?}"
            );
            assert_eq!(exc_tag(&self.h, word(&self.h, r + 8)), INTERRUPTED);
            // SAFETY: the test owns `r`.
            unsafe { self.rt.dec(r) };
        }
        match run(true, set) {
            None => false,
            Some(x) => {
                assert_eq!(x, INTERRUPTED, "the C++ kernel with a set token on {d:?}");
                true
            }
        }
    }

    /// Finds the heartbeats of the C++ kernel and of `Kernel::add_decl` for the accepted declaration `o`. The count is the smallest limit with which the kernel accepts, and the kernel must give `deterministicTimeout` with a smaller limit. The count of rulean must not be above the count of the C++ kernel (spec 09.6.4).
    fn same_heartbeats(&mut self, d: &Decl, o: u64) -> (u64, u64) {
        let cpp = self.heartbeats(o, true);
        let ours = self.heartbeats(o, false);
        assert!(
            ours <= cpp,
            "rulean counts {ours} heartbeats and the C++ kernel counts {cpp} for {d:?}"
        );
        (cpp, ours)
    }

    /// The smallest heartbeat limit with which the C++ kernel (`cpp`) or `Kernel::add_decl` accepts `o`. A limit of 0 is no limit, so the search starts at 1.
    fn heartbeats(&mut self, o: u64, cpp: bool) -> u64 {
        // The result of a limit: true if the kernel accepts. A rejection must be `deterministicTimeout`.
        let accepts = |max: u64| -> bool {
            // SAFETY: `env` and `o` are live objects. The functions consume the environment, so the test gives each call a new reference. `reset` has no arguments.
            let r = unsafe {
                self.rt.inc(self.env);
                (self.reset)();
                if cpp {
                    (self.add_decl)(self.env, max as usize, 512, o, boxed(0))
                } else {
                    self.kernel
                        .add_decl(self.env, max as usize, 512, o, boxed(0))
                }
            };
            let ok = tag(&self.h, r) == 1;
            if !ok {
                assert_eq!(
                    exc_tag(&self.h, word(&self.h, r + 8)),
                    TIMEOUT,
                    "a rejection with the limit {max} is not a timeout"
                );
            }
            // SAFETY: the test owns `r`.
            unsafe { self.rt.dec(r) };
            ok
        };
        let mut hi = 1;
        while !accepts(hi) {
            hi *= 2;
            assert!(hi < 1 << 40, "no heartbeat limit is sufficient");
        }
        let mut lo = hi / 2;
        // The kernel rejects with `lo` (or `lo` is 0) and accepts with `hi`.
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            if accepts(mid) { hi = mid } else { lo = mid }
        }
        hi
    }

    /// Gives the declaration object `o` to the exported `lean_add_decl` and requires the result of `Kernel::add_decl`, which is `r2`: the same verdict, the same new constants, or the same `Kernel.Exception` constructor.
    #[cfg(feature = "export")]
    fn same_as_export(&mut self, d: &Decl, o: u64, r2: u64, before: usize) {
        // SAFETY: `env` and `o` are live objects, and the process has the Lean runtime. The symbol consumes the environment, so the test gives it a new reference.
        let r3 = unsafe {
            self.rt.inc(self.env);
            rulean_ffi::export::lean_add_decl(self.env, 0, 512, o, boxed(0))
        };
        let ok = tag(&self.h, r2) == 1;
        assert_eq!(
            tag(&self.h, r3) == 1,
            ok,
            "the exported symbol gives a different verdict for {d:?}"
        );
        let a = word(&self.h, r2 + 8);
        let b = word(&self.h, r3 + 8);
        if ok {
            let names: Vec<NameId> = (before + 1..=self.chk.env.len())
                .map(|slot| self.chk.env.at(slot as u32).name)
                .collect();
            for n in names {
                assert_eq!(
                    self.constant(a, n),
                    self.constant(b, n),
                    "the exported symbol adds a different {n:?}"
                );
            }
        } else {
            assert_eq!(
                exc_tag(&self.h, a),
                exc_tag(&self.h, b),
                "the exported symbol gives a different exception for {d:?}"
            );
        }
        // SAFETY: the test owns `r3`.
        unsafe { self.rt.dec(r3) };
    }

    /// Gives the declaration object `o` to `lean_add_decl_without_checking` of the C++ kernel and to `Kernel::add_decl_without_checking`, with the current environment. The verdicts must be the same. For an accepted declaration, the constants that `d` declares must be the same in the two result environments. With the feature `export`, the exported symbol must give the result of `Kernel::add_decl_without_checking`.
    fn same_unchecked(&mut self, d: &Decl, o: u64) {
        // SAFETY: `env` and `o` are live objects. The two functions consume the environment, so the test gives each a new reference.
        let (r, r2) = unsafe {
            self.rt.inc(self.env);
            let r = (self.unchecked)(self.env, o);
            self.rt.inc(self.env);
            let r2 = self.kernel.add_decl_without_checking(self.env, o);
            (r, r2)
        };
        let ok = tag(&self.h, r) == 1;
        assert_eq!(
            tag(&self.h, r2) == 1,
            ok,
            "the unchecked add of rulean and the C++ kernel differ on {d:?}"
        );
        let a = word(&self.h, r + 8);
        let b = word(&self.h, r2 + 8);
        if ok {
            for n in declared(d) {
                let x = self.constant(a, n);
                assert!(
                    x.is_some(),
                    "the unchecked add of the C++ kernel has no {n:?}"
                );
                assert_eq!(
                    x,
                    self.constant(b, n),
                    "the unchecked add of the two kernels differs at {n:?}"
                );
            }
        } else if exc_tag(&self.h, b) != 12 {
            assert_eq!(
                exc_tag(&self.h, a),
                exc_tag(&self.h, b),
                "the unchecked add gives a different exception for {d:?}"
            );
        }
        #[cfg(feature = "export")]
        {
            // SAFETY: `env` and `o` are live objects, and the process has the Lean runtime. The symbol consumes the environment, so the test gives it a new reference.
            let r3 = unsafe {
                self.rt.inc(self.env);
                rulean_ffi::export::lean_add_decl_without_checking(self.env, o)
            };
            assert_eq!(
                tag(&self.h, r3) == 1,
                ok,
                "the exported unchecked add gives a different verdict for {d:?}"
            );
            let c = word(&self.h, r3 + 8);
            if ok {
                for n in declared(d) {
                    assert_eq!(
                        self.constant(b, n),
                        self.constant(c, n),
                        "the exported unchecked add differs at {n:?}"
                    );
                }
            } else {
                assert_eq!(
                    exc_tag(&self.h, b),
                    exc_tag(&self.h, c),
                    "the exported unchecked add gives a different exception for {d:?}"
                );
            }
            // SAFETY: the test owns `r3`.
            unsafe { self.rt.dec(r3) };
        }
        // SAFETY: the test owns `r` and `r2`.
        unsafe {
            self.rt.dec(r);
            self.rt.dec(r2);
        }
    }

    /// The constant `n` of the Lean environment `env`, converted into the store of the checker.
    fn constant(&mut self, env: u64, n: NameId) -> Option<ConstInfo> {
        let name = {
            // SAFETY: the encoder gives the maker only objects that it made.
            let mut m = unsafe { LeanMake::new(self.rt) };
            Encoder::new(&mut m, &self.chk.st).name(n)
        };
        // SAFETY: `find?` consumes the environment and the name, so the test gives it a new reference to the environment.
        let r = unsafe {
            self.rt.inc(env);
            (self.find)(env, name)
        };
        // `Option.some` has the tag 1, and `Option.none` is the boxed scalar 0.
        if r == boxed(0) {
            return None;
        }
        let ci = word(&self.h, r + 8);
        let k = Converter::new(&self.h, &mut self.chk.st)
            .constant(ci)
            .expect("a constant");
        // SAFETY: the test owns `r`.
        unsafe { self.rt.dec(r) };
        Some(k)
    }

    /// Reads the constant `s` of the C++ environment and compares it with the constant of rulean.
    fn same_constant(&mut self, s: &str) {
        let n = qname(&mut self.chk.st, s);
        let slot = self.chk.env.find(n);
        assert_ne!(slot, 0, "rulean has no {s}");
        let ours = self.chk.env.at(slot).clone();
        let theirs = self.constant(self.env, n);
        assert_eq!(theirs, Some(ours), "{s} is not the same in the two kernels");
    }
}

/// The names of the constants that `d` declares, without the names that the check of an inductive block makes. The quotient gives no names, because the check of `Quot` is the same in the two kinds of add.
fn declared(d: &Decl) -> Vec<NameId> {
    match d {
        Decl::Axiom(a) => vec![a.name],
        Decl::Defn(x) => vec![x.name],
        Decl::Thm(t) => vec![t.name],
        Decl::Opaque(o) => vec![o.name],
        Decl::Mutual(ds) => ds.iter().map(|x| x.name).collect(),
        Decl::Induct(b) => b
            .types
            .iter()
            .map(|t| t.name)
            .chain(b.ctors.iter().map(|c| c.name))
            .collect(),
        Decl::Quot(_) => Vec::new(),
    }
}

/// The terms of the test declarations.
struct T<'a> {
    st: &'a mut Store,
}

impl T<'_> {
    fn n(&mut self, s: &str) -> NameId {
        qname(self.st, s)
    }
    fn c(&mut self, s: &str) -> ExprId {
        let n = self.n(s);
        let l = self.st.level_list(&[]);
        self.st.mk_const(n, l)
    }
    fn c1(&mut self, s: &str) -> ExprId {
        let n = self.n(s);
        let z = self.st.level_zero();
        let one = self.st.level_succ(z);
        let l = self.st.level_list(&[one]);
        self.st.mk_const(n, l)
    }
    fn prop(&mut self) -> ExprId {
        let z = self.st.level_zero();
        self.st.mk_sort(z)
    }
    fn ty(&mut self) -> ExprId {
        let z = self.st.level_zero();
        let one = self.st.level_succ(z);
        self.st.mk_sort(one)
    }
    fn pi(&mut self, s: &str, dom: ExprId, body: ExprId) -> ExprId {
        let n = self.n(s);
        self.st.mk_pi(n, BinderInfo::Default, dom, body)
    }
    fn lam(&mut self, s: &str, dom: ExprId, body: ExprId) -> ExprId {
        let n = self.n(s);
        self.st.mk_lam(n, BinderInfo::Default, dom, body)
    }
    fn app(&mut self, f: ExprId, args: &[ExprId]) -> ExprId {
        self.st.mk_apps(f, args)
    }
    fn defn(&mut self, s: &str, ty: ExprId, value: ExprId, safety: Safety) -> Decl {
        let name = self.n(s);
        Decl::Defn(Defn {
            name,
            lparams: Vec::new(),
            ty,
            value,
            hints: Hints::Regular(1),
            safety,
            all: vec![name],
        })
    }
    fn ind_type(&mut self, s: &str, ty: ExprId, ctors: &[&str]) -> InductType {
        let name = self.n(s);
        let ctors = ctors.iter().map(|c| self.n(c)).collect();
        InductType {
            name,
            lparams: Vec::new(),
            ty,
            num_params: 0,
            num_indices: 0,
            all: vec![name],
            ctors,
            num_nested: 0,
            is_rec: false,
            is_reflexive: false,
            safety: Safety::Safe,
        }
    }
    fn ctor(&mut self, s: &str, induct: &str, cidx: u32, ty: ExprId) -> Ctor {
        Ctor {
            name: self.n(s),
            lparams: Vec::new(),
            ty,
            induct: self.n(induct),
            cidx,
            num_params: 0,
            num_fields: 0,
            safety: Safety::Safe,
        }
    }
}

#[test]
fn the_two_kernels_give_the_same_verdicts() {
    let Some(lib) = library() else {
        eprintln!("no Lean v4.36.0 library: set RULEAN_LEAN_LIB to run this test");
        return;
    };
    // SAFETY: the library is the `libleanshared` of Lean v4.36.0, and this test is the only code of the process that uses Lean.
    let rt = unsafe { Runtime::open(&lib) }.expect("the Lean runtime");
    // SAFETY: these are the types of the Lean functions of v4.36.0.
    let (mk_env, to_kernel, add_decl, unchecked, find, update_base, reset) = unsafe {
        (
            func::<unsafe extern "C" fn(u32, u64) -> u64>(&rt, c"l_Lean_mkEmptyEnvironment"),
            func::<unsafe extern "C" fn(u64) -> u64>(&rt, c"lean_elab_environment_to_kernel_env"),
            func::<AddDecl>(&rt, c"lean_add_decl"),
            func::<AddUnchecked>(&rt, c"lean_add_decl_without_checking"),
            func::<Find>(&rt, c"lean_environment_find"),
            func::<unsafe extern "C" fn(u64, u64) -> u64>(
                &rt,
                c"lean_elab_environment_update_base_after_kernel_add",
            ),
            // `lean::reset_heartbeat()`, a C++ function without arguments. The name is the mangled name of the Itanium ABI.
            func::<Reset>(&rt, c"_ZN4lean15reset_heartbeatEv"),
        )
    };
    // SAFETY: the objects are made by the Lean runtime and stay alive while the test uses them.
    let h = unsafe { LiveHeap::new() };
    // `mkEmptyEnvironment 0` in `IO`. The world is the boxed scalar 0, and `EStateM.Result.ok` has the tag 0.
    // SAFETY: the functions have these types, and the test owns each result.
    let (elab, env) = unsafe {
        let r = mk_env(0, boxed(0));
        assert_eq!(tag(&h, r), 0, "mkEmptyEnvironment failed");
        let e = word(&h, r + 8);
        rt.inc(e);
        rt.inc(e);
        rt.dec(r);
        (e, to_kernel(e))
    };
    // The empty kernel environment, for the test of the mirror. The test owns one reference.
    // SAFETY: `env` is a live environment.
    let base = unsafe {
        rt.inc(env);
        env
    };
    let mut chk = Checker::new(Store::new());
    chk.kernel_api = true;
    // SAFETY: the runtime is Lean v4.36.0, and the test gives `add_decl` live objects.
    let kernel = unsafe { Kernel::new(&rt) }.expect("the kernel functions");
    let mut dual = Dual {
        rt: &rt,
        h,
        add_decl,
        unchecked,
        find,
        reset,
        kernel,
        // SAFETY: the runtime is Lean v4.36.0.
        cancel: unsafe { (cancel_token(&rt, true), cancel_token(&rt, false)) },
        env,
        chk,
    };

    let mut st = Store::new();
    let mut t = T { st: &mut st };
    let mut cases: Vec<(&str, Decl, bool)> = Vec::new();

    // inductive N | z : N | s : N → N
    let ty = t.ty();
    let n = t.c("N");
    let s_ty = t.pi("n", n, n);
    let nt = t.ind_type("N", ty, &["N.z", "N.s"]);
    let cz = t.ctor("N.z", "N", 0, n);
    let mut cs = t.ctor("N.s", "N", 1, s_ty);
    cs.num_fields = 1;
    let mut nt = nt;
    nt.is_rec = true;
    cases.push((
        "N",
        Decl::Induct(Induct {
            types: vec![nt],
            ctors: vec![cz, cs],
            recs: Vec::new(),
        }),
        true,
    ));

    // inductive Eq.{u} {α : Sort u} (a : α) : α → Prop | refl : Eq a a. The quotient needs it.
    let p = t.prop();
    let u_n = t.n("u");
    let u = t.st.level_param(u_n);
    let sort_u = t.st.mk_sort(u);
    let us = t.st.level_list(&[u]);
    let eq_n = t.n("Eq");
    let eq_c = t.st.mk_const(eq_n, us);
    let alpha = t.n("α");
    let b0 = t.st.mk_bvar(0);
    let b1 = t.st.mk_bvar(1);
    let eq_ty = {
        let last = t.pi("b", b1, p);
        let mid = t.pi("a", b0, last);
        t.st.mk_pi(alpha, BinderInfo::Implicit, sort_u, mid)
    };
    let refl_ty = {
        let body = t.app(eq_c, &[b1, b0, b0]);
        let mid = t.pi("a", b0, body);
        t.st.mk_pi(alpha, BinderInfo::Implicit, sort_u, mid)
    };
    let mut et = t.ind_type("Eq", eq_ty, &["Eq.refl"]);
    et.lparams = vec![u_n];
    et.num_params = 2;
    et.num_indices = 1;
    let mut refl = t.ctor("Eq.refl", "Eq", 0, refl_ty);
    refl.lparams = vec![u_n];
    refl.num_params = 2;
    cases.push((
        "Eq",
        Decl::Induct(Induct {
            types: vec![et],
            ctors: vec![refl],
            recs: Vec::new(),
        }),
        true,
    ));

    // The quotient. The encoder writes `quotDecl` and does not read the fields.
    let anon = t.st.anon();
    cases.push((
        "Quot",
        Decl::Quot(Quot {
            name: anon,
            lparams: Vec::new(),
            ty: p,
            kind: QuotKind::Type,
        }),
        true,
    ));

    // def two : N := N.s (N.s N.z)
    let z = t.c("N.z");
    let s = t.c("N.s");
    let one = t.app(s, &[z]);
    let two_v = t.app(s, &[one]);
    let d = t.defn("two", n, two_v, Safety::Safe);
    cases.push(("two", d.clone(), true));
    cases.push(("two again", d, false));

    // def pred : N → N := fun n => @N.rec.{1} (fun _ => N) N.z (fun m _ => m) n
    let pred_ty = t.pi("n", n, n);
    let rec = t.c1("N.rec");
    let motive = t.lam("x", n, n);
    let b0 = t.st.mk_bvar(0);
    let b1 = t.st.mk_bvar(1);
    let step_in = t.lam("ih", n, b1);
    let step = t.lam("m", n, step_in);
    let body = t.app(rec, &[motive, z, step, b0]);
    let pred_v = t.lam("n", n, body);
    let d = t.defn("pred", pred_ty, pred_v, Safety::Safe);
    cases.push(("pred", d, true));

    // inductive V : N → Type | mk : V (N.s N.z)
    let v_ty = t.pi("i", n, ty);
    let v = t.c("V");
    let mk_ty = t.app(v, &[one]);
    let mut vt = t.ind_type("V", v_ty, &["V.mk"]);
    vt.num_indices = 1;
    let vmk = t.ctor("V.mk", "V", 0, mk_ty);
    cases.push((
        "V",
        Decl::Induct(Induct {
            types: vec![vt],
            ctors: vec![vmk],
            recs: Vec::new(),
        }),
        true,
    ));

    // def w : V (pred two) := V.mk needs an iota step of `N.rec`.
    let pred = t.c("pred");
    let two = t.c("two");
    let pt = t.app(pred, &[two]);
    let w_ty = t.app(v, &[pt]);
    let vmk_c = t.c("V.mk");
    let d = t.defn("w", w_ty, vmk_c, Safety::Safe);
    cases.push(("w", d, true));

    // def w2 : V two := V.mk is false, because `two` is not `N.s N.z`.
    let w2_ty = t.app(v, &[two]);
    let d = t.defn("w2", w2_ty, vmk_c, Safety::Safe);
    cases.push(("w2", d, false));

    // theorem bad : N := N.z. The type of a theorem must be a proposition.
    let name = t.n("bad");
    cases.push((
        "bad",
        Decl::Thm(Thm {
            name,
            lparams: Vec::new(),
            ty: n,
            value: z,
            all: vec![name],
        }),
        false,
    ));

    // def bad2 : Prop := N.z
    let d = t.defn("bad2", p, z, Safety::Safe);
    cases.push(("bad2", d, false));

    // axiom ax : Missing
    let missing = t.c("Missing");
    let name = t.n("ax");
    cases.push((
        "ax",
        Decl::Axiom(Axiom {
            name,
            lparams: Vec::new(),
            ty: missing,
            safety: Safety::Safe,
        }),
        false,
    ));

    // unsafe def loop : N := loop, as a mutual block of one definition.
    let lp = t.c("loop");
    let Decl::Defn(d) = t.defn("loop", n, lp, Safety::Unsafe) else {
        unreachable!()
    };
    cases.push(("loop", Decl::Mutual(vec![d]), true));

    // def bad3 : N := N.s Prop gives `appTypeMismatch`.
    let s_prop = t.app(s, &[p]);
    let d = t.defn("bad3", n, s_prop, Safety::Safe);
    cases.push(("bad3", d, false));

    // def bad4 : N.z := N.z gives `typeExpected`.
    let d = t.defn("bad4", z, z, Safety::Safe);
    cases.push(("bad4", d, false));

    // def bad5 : N := let x : N := Prop; x gives `letTypeMismatch`.
    let x_n = t.n("x");
    let b0 = t.st.mk_bvar(0);
    let let_v = t.st.mk_let(x_n, n, p, b0);
    let d = t.defn("bad5", n, let_v, Safety::Safe);
    cases.push(("bad5", d, false));

    // def bad6 : N → N := fun n => n n gives `funExpected` in a local context with `n`.
    let nn = t.app(b0, &[b0]);
    let lam = t.lam("n", n, nn);
    let n_to_n = t.pi("n", n, n);
    let d = t.defn("bad6", n_to_n, lam, Safety::Safe);
    cases.push(("bad6", d, false));

    // def bad7 : N := N.z.1 gives `invalidProj`, because `N` is not a structure.
    let n_name = t.n("N");
    let pj = t.st.mk_proj(n_name, 0, z);
    let d = t.defn("bad7", n, pj, Safety::Safe);
    cases.push(("bad7", d, false));

    let mut same_tags = 0;
    let mut beats = Vec::new();
    let mut interrupted = Vec::new();
    for (what, d, want) in &cases {
        let v = dual.add(&st, d);
        if let Some((cpp, ours)) = v.beats {
            eprintln!("heartbeats of {what}: C++ {cpp}, rulean {ours}");
            beats.push((cpp, ours));
        }
        if let Some(c) = v.cancel {
            interrupted.push((*what, c));
        }
        assert_eq!(v.cpp, *want, "the C++ kernel on {what}");
        assert_eq!(v.ours, v.cpp, "rulean and the C++ kernel differ on {what}");
        assert_eq!(
            v.kernel, v.cpp,
            "add_decl of rulean and the C++ kernel differ on {what}"
        );
        if let Some((a, b)) = v.tags {
            assert_eq!(a, b, "the exceptions differ on {what}");
            same_locals(a, v.locals.0, v.locals.1, what);
            same_tags += 1;
        }
    }
    // Each rejection gives the exception of the C++ kernel, and none gives `other`.
    assert_eq!(same_tags, cases.iter().filter(|c| !c.2).count());
    assert_eq!(same_tags, 10);
    // Each accepted declaration has a count, and most of them need more than one heartbeat, so the search finds a real limit.
    assert_eq!(beats.len(), 8);
    assert!(beats.iter().all(|&(cpp, ours)| ours <= cpp));
    assert!(beats.iter().filter(|&&(_, ours)| ours > 1).count() >= 6);
    // With a set cancel token, the C++ kernel gives `interrupted` at its first heartbeat. The check of the quotient has no heartbeat, so the C++ kernel accepts it. The search of the heartbeats starts at 1, so the count of the quotient is 1. `Kernel::add_decl` gives `interrupted` for all eight.
    eprintln!("interrupted by the C++ kernel: {interrupted:?}");
    assert_eq!(interrupted.len(), 8);
    assert!(interrupted.iter().all(|&(what, c)| c == (what != "Quot")));

    for s in [
        "N",
        "N.z",
        "N.s",
        "N.rec",
        "Eq",
        "Eq.refl",
        "Eq.rec",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
        "two",
        "pred",
        "V",
        "V.mk",
        "V.rec",
        "w",
        "loop",
    ] {
        dual.same_constant(s);
    }
    same_vars(&dual);

    same_with_mirror(&dual, base, &mut st, &cases);

    // The term functions. The elaborator environment has the final kernel environment of the C++ kernel.
    // SAFETY: `updateBaseAfterKernelAdd` consumes its arguments, so the test gives it a new reference to the kernel environment.
    let elab = unsafe {
        rt.inc(dual.env);
        update_base(elab, dual.env)
    };
    // The local context `(x : N) (y : N := N.s x)`.
    let mut t = T { st: &mut st };
    let n = t.c("N");
    let s = t.c("N.s");
    let z = t.c("N.z");
    let x = t.st.mk_fvar(0, n);
    let y = t.st.mk_fvar(1, n);
    let sx = t.app(s, &[x]);
    let fvars = vec![t.n("_fx"), t.n("_fy")];
    let locals = [
        (fvars[0], t.n("x"), n, None),
        (fvars[1], t.n("y"), n, Some(sx)),
    ];
    let pred = t.c("pred");
    let two = t.c("two");
    let pred_two = t.app(pred, &[two]);
    let pred_x = t.app(pred, &[x]);
    let pred_y = t.app(pred, &[y]);
    let sz = t.app(s, &[z]);
    let z_z = t.app(z, &[z]);
    let szz = t.app(s, &[z, z]);
    let missing = t.c("Missing");
    let b0 = t.st.mk_bvar(0);
    let id_n = t.lam("n", n, b0);
    let prop = t.prop();
    let s_prop = t.app(s, &[prop]);
    let nn = t.app(b0, &[b0]);
    let self_app = t.lam("n", n, nn);
    let u_n = t.n("u");
    let u = t.st.level_param(u_n);
    let sort_u = t.st.mk_sort(u);
    let qs: Vec<(&str, Q, Want)> = vec![
        ("y = N.s x", Q::DefEq(y, sx), Want::Bool(true)),
        ("x = N.z", Q::DefEq(x, z), Want::Bool(false)),
        ("pred y = x", Q::DefEq(pred_y, x), Want::Bool(true)),
        (
            "pred two = N.s N.z",
            Q::DefEq(pred_two, sz),
            Want::Bool(true),
        ),
        ("whnf (pred two)", Q::Whnf(pred_two), Want::Ok),
        ("whnf y", Q::Whnf(y), Want::Ok),
        ("whnf x", Q::Whnf(x), Want::Ok),
        ("whnf (pred y)", Q::Whnf(pred_y), Want::Ok),
        ("check (pred x)", Q::Check(pred_x), Want::Ok),
        ("check y", Q::Check(y), Want::Ok),
        ("check (fun n => n)", Q::Check(id_n), Want::Ok),
        ("check (Sort u)", Q::Check(sort_u), Want::Ok),
        ("check (N.z N.z)", Q::Check(z_z), Want::Err),
        ("check (N.s N.z N.z)", Q::Check(szz), Want::Err),
        ("check Missing", Q::Check(missing), Want::Err),
        ("check (N.s Prop)", Q::Check(s_prop), Want::Err),
        ("check (fun n => n n)", Q::Check(self_app), Want::Err),
    ];
    // SAFETY: the runtime is Lean v4.36.0.
    let mut terms = unsafe { Terms::new(&rt, &st, fvars, &locals) };
    // The elaborator gives local declarations with metavariables. The local `(m : ?m)` comes after `x` and `y`, and no term refers to it. The C++ kernel does not read it, and rulean must skip it. The local `(h : Sort ?u)` comes after `m`, and the terms refer to it. Its free variable has the level 2 in rulean, because rulean skips `m`.
    let mut t = T { st: &mut st };
    let (m_id, m_user, m_mvar) = (t.n("_fm"), t.n("m"), t.n("_mm"));
    let (h_id, h_user, h_lmvar) = (t.n("_fh"), t.n("h"), t.n("_mu"));
    // SAFETY: the runtime is Lean v4.36.0.
    unsafe {
        terms.push_mvar_local(&st, m_id, m_user, Hole::Expr(m_mvar));
        terms.push_mvar_local(&st, h_id, h_user, Hole::Sort(h_lmvar));
    }
    terms.fvars.push(h_id);
    let prop = st.mk_sort(st.level_zero());
    let h = st.mk_fvar(2, prop);
    let hs: Vec<(&str, Q, Want)> = vec![
        ("h = h", Q::DefEq(h, h), Want::Bool(true)),
        ("h = x", Q::DefEq(h, x), Want::Bool(false)),
        ("whnf h", Q::Whnf(h), Want::Ok),
        ("check h", Q::Check(h), Want::Ok),
    ];
    // The free variable `w` is not in the local context. The C++ kernel gives "unknown free variable" only when it infers the type of `w`, and rulean converts `w` to a far free variable.
    let w_id = st.name_str_bytes(st.anon(), b"_fw");
    terms.far.push(w_id);
    let w = rulean_core::expr::far_fvar(&mut st, 0);
    let mut t = T { st: &mut st };
    let pred = t.c("pred");
    let s = t.c("N.s");
    let sw = t.app(s, &[w]);
    let pred_sw = t.app(pred, &[sw]);
    let ws: Vec<(&str, Q, Want)> = vec![
        ("w = w", Q::DefEq(w, w), Want::Bool(true)),
        ("pred (N.s w) = w", Q::DefEq(pred_sw, w), Want::Bool(true)),
        ("whnf (pred (N.s w))", Q::Whnf(pred_sw), Want::Ok),
        ("whnf w", Q::Whnf(w), Want::Ok),
        ("w = x", Q::DefEq(w, x), Want::Err),
        ("check w", Q::Check(w), Want::Err),
        ("check (N.s w)", Q::Check(sw), Want::Err),
    ];
    let mut same_tags = 0;
    for (what, q, want) in qs.iter().chain(&hs).chain(&ws) {
        same_tags += terms.same(&dual, &st, elab, what, q, *want);
    }
    // `check Missing` gives `unknownConstant`, the two checks with too many arguments and `check (fun n => n n)` give `funExpected`, `check (N.s Prop)` gives `appTypeMismatch`, and the three queries that infer the type of `w` give "unknown free variable".
    assert_eq!(same_tags, 8);

    // The functions that the elaborator calls. `e1` is correct, the value of `e2` has the wrong type, and `e3` is `e2` without the check.
    let mut t = T { st: &mut st };
    let n = t.c("N");
    let z = t.c("N.z");
    let prop = t.prop();
    let elab_cases = vec![
        ("e1", t.defn("e1", n, z, Safety::Safe), true, true),
        ("e2", t.defn("e2", n, prop, Safety::Safe), true, false),
        ("e3", t.defn("e3", n, prop, Safety::Safe), false, true),
    ];
    // SAFETY: these are the types of the Lean functions of v4.36.0.
    let cpp_elab = unsafe {
        (
            func::<AddDecl>(&rt, c"lean_elab_add_decl"),
            func::<AddUnchecked>(&rt, c"lean_elab_add_decl_without_checking"),
        )
    };
    for (name, d, check, want) in &elab_cases {
        same_elab(
            &mut dual, elab, &st, cpp_elab, to_kernel, name, d, *check, *want,
        );
    }
    // SAFETY: the test owns the environments and the local context.
    unsafe {
        rt.dec(terms.lctx);
        rt.dec(elab);
        rt.dec(dual.env);
        rt.dec(dual.cancel.0);
        rt.dec(dual.cancel.1);
    }
}

/// Gives the declaration `d` with the name `name` to `lean_elab_add_decl` of the C++ kernel and to `Kernel::elab_add_decl` with the elaborator environment `elab`, or to the functions without the check if `check` is false. With the feature `export`, the exported symbol of rulean also gets it. Each result must be `Except.ok` if `want` is true. The new environments must have the same constant, and the exceptions must have the same tag. The call borrows `elab`.
#[allow(clippy::too_many_arguments)]
fn same_elab(
    dual: &mut Dual,
    elab: u64,
    st: &Store,
    cpp: (AddDecl, AddUnchecked),
    to_kernel: unsafe extern "C" fn(u64) -> u64,
    name: &str,
    d: &Decl,
    check: bool,
    want: bool,
) {
    let rt = dual.rt;
    let o = {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(rt) };
        Encoder::new(&mut m, st).declaration(d).expect("an object")
    };
    let mut rs = Vec::new();
    // The functions consume the environment, so the test gives each a new reference. They borrow the declaration and the cancel token.
    // SAFETY: `elab` and `o` are live objects, and the functions have these types.
    unsafe {
        rt.inc(elab);
        rs.push(if check {
            (cpp.0)(elab, 0, 512, o, boxed(0))
        } else {
            (cpp.1)(elab, o)
        });
        rt.inc(elab);
        rs.push(if check {
            dual.kernel.elab_add_decl(elab, 0, 512, o, boxed(0))
        } else {
            dual.kernel.elab_add_decl_without_checking(elab, o)
        });
        #[cfg(feature = "export")]
        {
            rt.inc(elab);
            rs.push(if check {
                rulean_ffi::export::lean_elab_add_decl(elab, 0, 512, o, boxed(0))
            } else {
                rulean_ffi::export::lean_elab_add_decl_without_checking(elab, o)
            });
        }
    }
    let mut seen = Vec::new();
    for &r in &rs {
        // `Except.error` has the tag 0 and `Except.ok` has the tag 1.
        assert_eq!(
            tag(&dual.h, r) == 1,
            want,
            "the verdict of {name} (check {check})"
        );
        let x = word(&dual.h, r + 8);
        if want {
            // SAFETY: `toKernelEnv` consumes its argument, so the test gives it a new reference.
            let kenv = unsafe {
                rt.inc(x);
                to_kernel(x)
            };
            let n = qname(&mut dual.chk.st, name);
            let c = dual.constant(kenv, n);
            assert!(c.is_some(), "the new environment has no {name}");
            seen.push(format!("{c:?}"));
            // SAFETY: the test owns `kenv`.
            unsafe { rt.dec(kenv) };
        } else {
            seen.push(format!("tag {}", exc_tag(&dual.h, x)));
        }
    }
    assert!(
        seen.iter().all(|s| *s == seen[0]),
        "{name} (check {check}): {seen:?}"
    );
    eprintln!(
        "elab {name} check {check}: {}",
        seen[0].chars().take(60).collect::<String>()
    );
    // SAFETY: the test owns the results and the declaration.
    unsafe {
        for r in rs {
            rt.dec(r);
        }
        rt.dec(o);
    }
}

/// The result of `addDecl` of a kernel: the new environment, or the tag of the exception.
type Added = Result<u64, u64>;

/// Gives `d` to the C++ kernel (`cpp`) or to the kernel `k` on the environment `env` with the heartbeat limit `max`. The call borrows `env`.
fn add_with(
    dual: &Dual,
    k: &Kernel,
    cpp: bool,
    env: u64,
    st: &Store,
    d: &Decl,
    max: usize,
) -> Added {
    let o = {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(dual.rt) };
        Encoder::new(&mut m, st).declaration(d).expect("an object")
    };
    // SAFETY: `env` and `o` are live objects. The functions consume the environment, so the call gives them a new reference.
    let r = unsafe {
        dual.rt.inc(env);
        if cpp {
            (dual.add_decl)(env, max, 512, o, boxed(0))
        } else {
            k.add_decl(env, max, 512, o, boxed(0))
        }
    };
    let v = word(&dual.h, r + 8);
    let out = if tag(&dual.h, r) == 1 {
        // SAFETY: `v` is a field of `r`. The caller gets a new reference to it.
        unsafe { dual.rt.inc(v) };
        Ok(v)
    } else {
        Err(exc_tag(&dual.h, v))
    };
    // SAFETY: the call owns `r` and `o`.
    unsafe {
        dual.rt.dec(r);
        dual.rt.dec(o);
    }
    out
}

/// The test of the mirror of `Kernel::add_decl` (spec 09.6.3). A new kernel checks the declarations of `cases` on its own environments from `base`, so each call can use the constants of the mirror. Then two environments get a constant `c` with different values, and a definition that uses `c` must have the verdict of the C++ kernel on each environment.
/// Gives declarations with metavariables and free variables to the C++ kernel and to `Kernel::add_decl`. The conversion of rulean declines these terms, so the test makes the objects with the functions of the runtime. The two kernels must give the same exception, `declHasMVars` (3) or `declHasFVars` (4), with the same name and the same term. The C++ kernel checks the type of a constant before its value, and the type of an inductive type before the type of a constructor. If a term has a metavariable and a free variable, the exception is `declHasMVars`.
fn same_vars(dual: &Dual) {
    type Mk1 = unsafe extern "C" fn(u64) -> u64;
    type Mk2 = unsafe extern "C" fn(u64, u64) -> u64;
    type Mk4 = unsafe extern "C" fn(u64, u64, u64, u8) -> u64;
    type Eq2 = unsafe extern "C" fn(u64, u64) -> u8;
    let rt = dual.rt;
    // SAFETY: these are the types of the Lean functions of v4.36.0. The `mk` functions consume their object arguments, and the two equalities borrow them.
    let (mk_str, mk_string, mvar, lmvar, fvar, sort, zero, forall, name_eq, expr_eqv) = unsafe {
        (
            func::<Mk2>(rt, c"lean_name_mk_string"),
            func::<unsafe extern "C" fn(*const std::ffi::c_char) -> u64>(rt, c"lean_mk_string"),
            func::<Mk1>(rt, c"l_Lean_mkMVar"),
            func::<Mk1>(rt, c"l_Lean_mkLevelMVar"),
            func::<Mk1>(rt, c"lean_expr_mk_fvar"),
            func::<Mk1>(rt, c"lean_expr_mk_sort"),
            func::<unsafe extern "C" fn(u64) -> u64>(rt, c"lean_level_mk_zero"),
            func::<Mk4>(rt, c"lean_expr_mk_forall"),
            func::<Eq2>(rt, c"lean_name_eq"),
            func::<Eq2>(rt, c"lean_expr_eqv"),
        )
    };
    // SAFETY: the functions get new objects, and the test owns each result.
    let name = |s: &CStr| unsafe { mk_str(boxed(0), mk_string(s.as_ptr())) };
    // SAFETY: the test gives the maker only objects of the runtime.
    let mut m = unsafe { LeanMake::new(rt) };
    // SAFETY: as for `name`.
    let prop = || unsafe { sort(zero(boxed(0))) };
    // SAFETY: as for `name`.
    let hole = |s: &CStr| unsafe { mvar(name(s)) };
    // SAFETY: as for `name`.
    let free = |s: &CStr| unsafe { fvar(name(s)) };
    // SAFETY: as for `name`.
    let sort_mvar = |s: &CStr| unsafe { sort(lmvar(name(s))) };
    let cons = |m: &mut LeanMake, x: u64| m.ctor(1, &[x, boxed(0)], &[]);
    // The `ConstantVal` of `n : ty` without universe parameters.
    let cval = |m: &mut LeanMake, n: u64, ty: u64| m.ctor(0, &[n, boxed(0), ty], &[]);
    let axiom = |m: &mut LeanMake, s: &CStr, ty: u64| {
        let c = cval(m, name(s), ty);
        let v = m.ctor(0, &[c], &[0]);
        m.ctor(0, &[v], &[])
    };
    // A safe definition with the hints `opaque`. The safety `safe` is the scalar 1.
    let defn = |m: &mut LeanMake, s: &CStr, ty: u64, value: u64| {
        let c = cval(m, name(s), ty);
        let all = cons(m, name(s));
        let v = m.ctor(0, &[c, value, boxed(0), all], &[1]);
        m.ctor(1, &[v], &[])
    };
    let thm = |m: &mut LeanMake, s: &CStr, ty: u64, value: u64| {
        let c = cval(m, name(s), ty);
        let all = cons(m, name(s));
        let v = m.ctor(0, &[c, value, all], &[]);
        m.ctor(2, &[v], &[])
    };
    // inductive `s : Prop` with one constructor `c : cty`.
    let induct = |m: &mut LeanMake, s: &CStr, c: &CStr, cty: u64| {
        let k = m.ctor(0, &[name(c), cty], &[]);
        let ks = cons(m, k);
        let it = m.ctor(0, &[name(s), prop(), ks], &[]);
        let its = cons(m, it);
        m.ctor(6, &[boxed(0), boxed(0), its], &[0])
    };
    // SAFETY: the binder name is a new object and the binder info `default` is 0.
    let arrow = |a: u64, b: u64| unsafe { forall(name(c"_a"), a, b, 0) };
    let cases: Vec<(&str, u64, u64, &CStr)> = vec![
        (
            "an axiom with ?m",
            axiom(&mut m, c"vx_a1", hole(c"_m1")),
            3,
            c"vx_a1",
        ),
        (
            "a value with ?m",
            defn(&mut m, c"vx_d1", prop(), hole(c"_m2")),
            3,
            c"vx_d1",
        ),
        (
            "a theorem with Sort ?u",
            thm(&mut m, c"vx_t1", sort_mvar(c"_u1"), hole(c"_m3")),
            3,
            c"vx_t1",
        ),
        (
            "an axiom with a free variable",
            axiom(&mut m, c"vx_a2", free(c"_f1")),
            4,
            c"vx_a2",
        ),
        (
            "an axiom with a free variable and ?m",
            axiom(&mut m, c"vx_a3", arrow(free(c"_f2"), hole(c"_m4"))),
            3,
            c"vx_a3",
        ),
        (
            "a type with a free variable and a value with ?m",
            defn(&mut m, c"vx_d2", free(c"_f3"), hole(c"_m5")),
            4,
            c"vx_d2",
        ),
        (
            "a constructor with ?m",
            induct(&mut m, c"vx_I", c"vx_I.mk", hole(c"_m6")),
            3,
            c"vx_I.mk",
        ),
    ];
    for (what, o, want, n) in cases {
        // SAFETY: `env` and `o` are live objects. The functions consume the environment and borrow the declaration and the cancel token.
        let (r, r2) = unsafe {
            rt.inc(dual.env);
            let r = (dual.add_decl)(dual.env, 0, 512, o, boxed(0));
            rt.inc(dual.env);
            let r2 = dual.kernel.add_decl(dual.env, 0, 512, o, boxed(0));
            (r, r2)
        };
        assert_eq!(tag(&dual.h, r), 0, "the C++ kernel accepts {what}");
        assert_eq!(tag(&dual.h, r2), 0, "add_decl accepts {what}");
        let (x, x2) = (word(&dual.h, r + 8), word(&dual.h, r2 + 8));
        assert_eq!(
            exc_tag(&dual.h, x),
            want,
            "the exception of the C++ kernel on {what}"
        );
        assert_eq!(
            exc_tag(&dual.h, x2),
            want,
            "the exception of add_decl on {what}"
        );
        let want_name = name(n);
        // SAFETY: the fields are live, and the equalities borrow their arguments. The test owns `r`, `r2`, `o` and `want_name`.
        unsafe {
            assert_eq!(
                name_eq(word(&dual.h, x + 16), want_name),
                1,
                "the name of the C++ exception on {what}"
            );
            assert_eq!(
                name_eq(word(&dual.h, x2 + 16), want_name),
                1,
                "the name of the rulean exception on {what}"
            );
            assert_eq!(
                expr_eqv(word(&dual.h, x + 24), word(&dual.h, x2 + 24)),
                1,
                "the terms of the exceptions differ on {what}"
            );
            rt.dec(want_name);
            rt.dec(r);
            rt.dec(r2);
            rt.dec(o);
        }
    }
}

fn same_with_mirror(dual: &Dual, base: u64, st: &mut Store, cases: &[(&str, Decl, bool)]) {
    // SAFETY: the runtime is Lean v4.36.0.
    let k = unsafe { Kernel::new(dual.rt) }.expect("the kernel functions");
    let mut env = base;
    let mut steps = Vec::new();
    for (what, d, want) in cases {
        let before = k.mirror_stats();
        match add_with(dual, &k, false, env, st, d, 0) {
            Ok(e) => {
                assert!(*want, "the kernel with the mirror accepts {what}");
                // SAFETY: the test owns `env`.
                unsafe { dual.rt.dec(env) };
                env = e;
            }
            Err(x) => {
                assert!(!*want, "the kernel with the mirror rejects {what} with {x}");
            }
        }
        let after = k.mirror_stats();
        steps.push((
            *what,
            after.converted - before.converted,
            after.reused - before.reused,
        ));
    }
    eprintln!("mirror (declaration, converted, reused): {steps:?}");
    // The environments come from the kernel, so the mirror has each constant with the same object.
    assert_eq!(k.mirror_stats().rebuilds, 0);
    // `N` and `Eq` refer to no earlier constant. Each declaration after them uses constants from the mirror.
    assert!(steps.iter().skip(2).all(|&(_, _, reused)| reused > 0));
    // The mirror converts no constant of the Lean environment, because each one comes from a check of the kernel.
    assert_eq!(k.mirror_stats().converted, 0);

    // The heartbeats of a declaration do not depend on the mirror. A new kernel finds the count of `w3 : V (pred two) := V.mk`, and the kernel with the full mirror must reject it with one heartbeat less and accept it with the count. A rejection keeps the mirror, so the two checks use it.
    let mut t = T { st: &mut *st };
    let v = t.c("V");
    let pred = t.c("pred");
    let two = t.c("two");
    let pt = t.app(pred, &[two]);
    let w3_ty = t.app(v, &[pt]);
    let vmk = t.c("V.mk");
    let w3 = t.defn("w3", w3_ty, vmk, Safety::Safe);
    // SAFETY: the runtime is Lean v4.36.0.
    let fresh = unsafe { Kernel::new(dual.rt) }.expect("the kernel functions");
    let accepts = |k: &Kernel, max: usize| match add_with(dual, k, false, env, st, &w3, max) {
        Ok(e) => {
            // SAFETY: the test owns `e`.
            unsafe { dual.rt.dec(e) };
            true
        }
        Err(x) => {
            assert_eq!(x, TIMEOUT, "a rejection of w3 is not a timeout");
            false
        }
    };
    let mut count = 1;
    while !accepts(&fresh, count) {
        count += 1;
        assert!(count < 1000, "no heartbeat limit is sufficient for w3");
    }
    assert!(count > 1);
    let warm = k.mirror_stats();
    assert!(
        !accepts(&k, count - 1),
        "the mirror accepts w3 with fewer heartbeats"
    );
    assert!(
        accepts(&k, count),
        "the mirror rejects w3 with the count of a new kernel"
    );
    let used = k.mirror_stats();
    assert_eq!(used.rebuilds, warm.rebuilds);
    assert_eq!(used.converted, warm.converted);
    eprintln!("heartbeats of w3: {count}, with a new kernel and with the mirror");

    // Two environments with `c : N`: `N.z` in `a` and `N.s N.z` in `b`. `V.mk : V (N.s N.z)`, so `t : V c := V.mk` is correct only in `b`.
    let mut t = T { st };
    let n = t.c("N");
    let z = t.c("N.z");
    let s = t.c("N.s");
    let sz = t.app(s, &[z]);
    let c_a = t.defn("c", n, z, Safety::Safe);
    let c_b = t.defn("c", n, sz, Safety::Safe);
    let v = t.c("V");
    let c = t.c("c");
    let vc = t.app(v, &[c]);
    let vmk = t.c("V.mk");
    let use_c = t.defn("t", vc, vmk, Safety::Safe);
    let st = &*t.st;
    let a = add_with(dual, &k, false, env, st, &c_a, 0).expect("c in a");
    let b = add_with(dual, &k, false, env, st, &c_b, 0).expect("c in b");
    // The mirror has `c` of `a`, and the environment `b` has a different `c`.
    let rebuilds = k.mirror_stats().rebuilds;
    assert_eq!(rebuilds, 1);
    for (e, want) in [(b, true), (a, false), (b, true), (b, true), (a, false)] {
        let cpp = add_with(dual, &k, true, e, st, &use_c, 0);
        let ours = add_with(dual, &k, false, e, st, &use_c, 0);
        assert_eq!(cpp.is_ok(), want, "the C++ kernel on t");
        assert_eq!(ours.is_ok(), want, "the kernel with the mirror on t");
        for x in [cpp, ours].into_iter().flatten() {
            // SAFETY: the test owns `x`.
            unsafe { dual.rt.dec(x) };
        }
    }
    let stats = k.mirror_stats();
    eprintln!("mirror after the two environments: {stats:?}");
    // Each change between `a` and `b` makes a new mirror. After `t` is accepted on `b`, the mirror has the `t` of the new environment, and `b` does not have it. Thus the second check of `t` on `b` makes a new mirror too.
    assert_eq!(stats.rebuilds, rebuilds + 4);
    // SAFETY: the test owns the environments.
    unsafe {
        dual.rt.dec(a);
        dual.rt.dec(b);
        dual.rt.dec(env);
    }
}

/// An `Option IO.CancelToken` object: `some` of a token with the flag `set`. `IO.CancelToken` has the fields `promise` and `setRef`. The kernels read only `setRef`, so the promise is the boxed scalar 0.
///
/// # Safety
///
/// `rt` is the runtime of Lean v4.36.0.
unsafe fn cancel_token(rt: &Runtime, set: bool) -> u64 {
    // SAFETY: `lean_st_mk_ref` consumes its argument and gives a new `IO.Ref`. The `ST` state has no object, so the result is the reference.
    let mk_ref = unsafe { func::<unsafe extern "C" fn(u64) -> u64>(rt, c"lean_st_mk_ref") };
    // SAFETY: a `Bool` is a boxed scalar.
    let r = unsafe { mk_ref(boxed(u64::from(set))) };
    // SAFETY: the maker gives the objects to the token, and the token to the option.
    let mut m = unsafe { LeanMake::new(rt) };
    let tk = m.ctor(0, &[boxed(0), r], &[]);
    m.ctor(1, &[tk], &[])
}

/// A query of a term function.
#[derive(Clone, Copy)]
enum Q {
    DefEq(ExprId, ExprId),
    Whnf(ExprId),
    Check(ExprId),
}

/// The result that the C++ kernel must give.
#[derive(Clone, Copy, Debug)]
enum Want {
    Bool(bool),
    Ok,
    Err,
}

type MkLocal = unsafe extern "C" fn(u64, u64, u64, u64, u8) -> u64;
type MkLet = unsafe extern "C" fn(u64, u64, u64, u64, u64, u8) -> u64;
type DefEqFn = unsafe extern "C" fn(u64, u64, u64, u64) -> u64;
type TermFn = unsafe extern "C" fn(u64, u64, u64) -> u64;
type Equal = unsafe extern "C" fn(u64, u64) -> u8;

/// The metavariable in the type of a local declaration of `Terms::push_mvar_local`, by the name of its `MVarId` or `LMVarId`.
#[derive(Clone, Copy)]
enum Hole {
    Expr(NameId),
    Sort(NameId),
}

/// The terms of the term functions and their local context.
struct Terms<'a> {
    rt: &'a Runtime,
    /// The names of the `FVarId` of the local declarations, by level.
    fvars: Vec<NameId>,
    /// The names of the `FVarId` of the far free variables, by number. These free variables are not in the local context.
    far: Vec<NameId>,
    /// The `LocalContext` object. The test owns one reference.
    lctx: u64,
    is_def_eq: DefEqFn,
    whnf: TermFn,
    check: TermFn,
    equal: Equal,
}

impl<'a> Terms<'a> {
    /// Makes the `LocalContext` object with the declarations `locals`: the `FVarId`, the user name, the type and the value of a `let`.
    ///
    /// # Safety
    ///
    /// `rt` is the runtime of Lean v4.36.0.
    unsafe fn new(
        rt: &'a Runtime,
        st: &Store,
        fvars: Vec<NameId>,
        locals: &[(NameId, NameId, ExprId, Option<ExprId>)],
    ) -> Terms<'a> {
        // SAFETY: these are the types of the Lean functions of v4.36.0. The functions consume their object arguments.
        unsafe {
            let empty = func::<unsafe extern "C" fn(u64) -> u64>(rt, c"lean_mk_empty_local_ctx");
            let mk_local = func::<MkLocal>(rt, c"lean_local_ctx_mk_local_decl");
            let mk_let = func::<MkLet>(rt, c"lean_local_ctx_mk_let_decl");
            let mut lctx = empty(boxed(0));
            for &(id, user, ty, val) in locals {
                let mut m = LeanMake::new(rt);
                let mut enc = Encoder::new(&mut m, st).with_fvars(fvars.clone());
                let (id, user) = (enc.name(id), enc.name(user));
                let ty = enc.expr(ty).expect("a type");
                lctx = match val {
                    // `BinderInfo.default` is 0.
                    None => mk_local(lctx, id, user, ty, 0),
                    Some(v) => {
                        let v = enc.expr(v).expect("a value");
                        mk_let(lctx, id, user, ty, v, 0)
                    }
                };
            }
            Terms {
                rt,
                fvars,
                far: Vec::new(),
                lctx,
                is_def_eq: func::<DefEqFn>(rt, c"lean_kernel_is_def_eq"),
                whnf: func::<TermFn>(rt, c"lean_kernel_whnf"),
                check: func::<TermFn>(rt, c"lean_kernel_check"),
                equal: func::<Equal>(rt, c"lean_expr_equal"),
            }
        }
    }

    /// Adds a local declaration with a metavariable to the local context: `(user : ?mvar)` for `Hole::Expr(mvar)` and `(user : Sort ?mvar)` for `Hole::Sort(mvar)`. The `FVarId` is `id`. The store cannot have these types, so the caller adds `id` to `fvars` if a term refers to the declaration.
    ///
    /// # Safety
    ///
    /// The runtime is Lean v4.36.0.
    unsafe fn push_mvar_local(&mut self, st: &Store, id: NameId, user: NameId, hole: Hole) {
        type Mk = unsafe extern "C" fn(u64) -> u64;
        // SAFETY: these are the types of the Lean functions of v4.36.0. The functions consume their object arguments.
        unsafe {
            let mk_local = func::<MkLocal>(self.rt, c"lean_local_ctx_mk_local_decl");
            let mut m = LeanMake::new(self.rt);
            let mut enc = Encoder::new(&mut m, st);
            let (id, user) = (enc.name(id), enc.name(user));
            let ty = match hole {
                Hole::Expr(n) => func::<Mk>(self.rt, c"l_Lean_mkMVar")(enc.name(n)),
                Hole::Sort(n) => {
                    let l = func::<Mk>(self.rt, c"l_Lean_mkLevelMVar")(enc.name(n));
                    func::<Mk>(self.rt, c"lean_expr_mk_sort")(l)
                }
            };
            self.lctx = mk_local(self.lctx, id, user, ty, 0);
        }
    }

    /// Gives the query `q` to the C++ kernel, to `Kernel` and, with the feature `export`, to the exported symbol of rulean. The C++ kernel must give `want`, and the results must be the same. A rejection must give the exception of the C++ kernel. The result is 1 for a rejection, and 0 if not.
    fn same(&self, dual: &Dual, st: &Store, elab: u64, what: &str, q: &Q, want: Want) -> usize {
        let es: Vec<ExprId> = match *q {
            Q::DefEq(a, b) => vec![a, b],
            Q::Whnf(e) | Q::Check(e) => vec![e],
        };
        let objs: Vec<u64> = es
            .iter()
            .map(|&e| {
                // SAFETY: the encoder gives the maker only objects that it made.
                let mut m = unsafe { LeanMake::new(self.rt) };
                Encoder::new(&mut m, st)
                    .with_fvars(self.fvars.clone())
                    .with_far_fvars(self.far.clone())
                    .expr(e)
                    .expect("a term")
            })
            .collect();
        // `who` is 0 for the C++ kernel, 1 for `Kernel` and 2 for the exported symbol. Each function consumes its arguments, so the test gives each call new references.
        let call = |who: u8| -> u64 {
            // SAFETY: the objects are live, and the functions have these types.
            unsafe {
                self.rt.inc(elab);
                self.rt.inc(self.lctx);
                for &o in &objs {
                    self.rt.inc(o);
                }
                let k = &dual.kernel;
                match (*q, who) {
                    (Q::DefEq(..), 0) => (self.is_def_eq)(elab, self.lctx, objs[0], objs[1]),
                    (Q::DefEq(..), 1) => k.is_def_eq(elab, self.lctx, objs[0], objs[1]),
                    (Q::Whnf(_), 0) => (self.whnf)(elab, self.lctx, objs[0]),
                    (Q::Whnf(_), 1) => k.whnf(elab, self.lctx, objs[0]),
                    (Q::Check(_), 0) => (self.check)(elab, self.lctx, objs[0]),
                    (Q::Check(_), 1) => k.check(elab, self.lctx, objs[0]),
                    #[cfg(feature = "export")]
                    (Q::DefEq(..), _) => {
                        rulean_ffi::export::lean_kernel_is_def_eq(elab, self.lctx, objs[0], objs[1])
                    }
                    #[cfg(feature = "export")]
                    (Q::Whnf(_), _) => {
                        rulean_ffi::export::lean_kernel_whnf(elab, self.lctx, objs[0])
                    }
                    #[cfg(feature = "export")]
                    (Q::Check(_), _) => {
                        rulean_ffi::export::lean_kernel_check(elab, self.lctx, objs[0])
                    }
                    #[cfg(not(feature = "export"))]
                    _ => unreachable!("the exported symbols need the feature export"),
                }
            }
        };
        let h = &dual.h;
        let cpp = call(0);
        let cpp_ok = tag(h, cpp) == 1;
        let cv = word(h, cpp + 8);
        match want {
            Want::Bool(b) => {
                assert!(cpp_ok, "the C++ kernel rejects {what}");
                assert_eq!(cv, boxed(u64::from(b)), "the C++ kernel on {what}");
            }
            Want::Ok => assert!(cpp_ok, "the C++ kernel rejects {what}"),
            Want::Err => assert!(!cpp_ok, "the C++ kernel accepts {what}"),
        }
        let mut whos = vec![1u8];
        if cfg!(feature = "export") {
            whos.push(2);
        }
        let mut same_tag = 0;
        for who in whos {
            let r = call(who);
            assert_eq!(
                tag(h, r) == 1,
                cpp_ok,
                "rulean ({who}) and the C++ kernel differ on {what}"
            );
            let v = word(h, r + 8);
            let is_bool = matches!(q, Q::DefEq(..));
            let diff = dual.kernel.compare_term(cpp, r, is_bool);
            assert!(diff.is_none(), "compare_term on {what}: {diff:?}");
            if is_bool && cpp_ok && who == 1 {
                // SAFETY: the maker makes `Except.ok` with the other `Bool`, and the test owns it.
                unsafe {
                    let mut m = LeanMake::new(self.rt);
                    let flip = m.ctor(1, &[boxed(u64::from(cv != boxed(1)))], &[]);
                    assert!(
                        dual.kernel.compare_term(cpp, flip, true).is_some(),
                        "compare_term accepts two different results on {what}"
                    );
                    self.rt.dec(flip);
                }
            }
            if cpp_ok {
                let same = match q {
                    Q::DefEq(..) => v == cv,
                    // SAFETY: `equal` borrows its arguments, and the two results are live.
                    _ => (unsafe { (self.equal)(cv, v) }) != 0,
                };
                assert!(
                    same,
                    "rulean ({who}) and the C++ kernel give different results on {what}"
                );
            } else {
                assert_eq!(
                    exc_tag(h, cv),
                    exc_tag(h, v),
                    "the exceptions differ on {what}"
                );
                let (a, b) = (exc_locals(self.rt, h, cv), exc_locals(self.rt, h, v));
                same_locals(exc_tag(h, cv), a, b, what);
                if who == 1 {
                    same_tag = 1;
                }
            }
            // SAFETY: the test owns `r`.
            unsafe { self.rt.dec(r) };
        }
        // SAFETY: the test owns `cpp` and the term objects.
        unsafe {
            self.rt.dec(cpp);
            for o in objs {
                self.rt.dec(o);
            }
        }
        same_tag
    }
}
