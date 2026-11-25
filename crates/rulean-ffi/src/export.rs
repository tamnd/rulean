//! The symbols that a build of Lean with rulean as its kernel links (spec 09.6.2).
//!
//! The feature `export` enables this module. The command `cargo rustc -p rulean-ffi --release --features export --crate-type staticlib` makes the static library. The library exports `lean_add_decl`, `lean_add_decl_without_checking`, `lean_elab_add_decl`, `lean_elab_add_decl_without_checking`, `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check` with the signatures of the C++ kernel of Lean v4.36.0, so it can replace the objects of Lean that have these symbols.
//!
//! Each thread that calls a symbol gets its own `Kernel`. The `Kernel` finds the functions of the Lean runtime in the images of the process, on the first call of the thread. The `Runtime` of the thread stays alive until the process stops.
//!
//! The process must not have two definitions of a symbol that Lean can call. A test binary with this feature can load `libleanshared` with `dlopen`, because the test finds the symbols of the C++ kernel through the handle of the library.
//!
//! With the feature `dual`, each symbol also calls the C++ function with the suffix `_cpp` and compares the two results (spec 11.3). If they differ, the call writes the difference to the standard error and stops the process. Otherwise the result is the result of rulean. `Kernel::compare_add` and `Kernel::compare_term` tell which results agree.
//!
//! If the environment variable `RULEAN_FFI_TIMING` has a path, the process appends the times of `kernel::timing` to the file at the path when it stops, as one line (spec 09.6.3). The line is not written to the standard error, so the output of `lean` does not change.
//!
//! This module, `rt`, `live` and `kernel` are the only modules of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use std::cell::OnceCell;
use std::sync::Once;

use crate::kernel::{Kernel, MirrorPool};
use crate::rt::Runtime;

/// The types of the C++ functions of the dual-kernel build (spec 11.3).
#[cfg(feature = "dual")]
type AddFn = unsafe extern "C" fn(u64, usize, usize, u64, u64) -> u64;
#[cfg(feature = "dual")]
type AddUncheckedFn = unsafe extern "C" fn(u64, u64) -> u64;
#[cfg(feature = "dual")]
type DefEqFn = unsafe extern "C" fn(u64, u64, u64, u64) -> u64;
#[cfg(feature = "dual")]
type TermFn = unsafe extern "C" fn(u64, u64, u64) -> u64;

/// The C++ function `name` of the dual-kernel build, with the type `F`. `scripts/lean-build.sh --dual` renames the functions of the C++ kernel with the suffix `_cpp`, and the binary exports them. The call finds the function when the program runs, so a test binary with the feature `dual` links without these symbols. If the process has no such function, the call stops the process.
///
/// # Safety
///
/// `F` is the type of the C++ function `name` of Lean v4.36.0.
#[cfg(feature = "dual")]
unsafe fn cpp<F: Copy>(k: &Kernel<'static>, name: &std::ffi::CStr) -> F {
    match k.runtime().symbol(name) {
        // SAFETY: the address is the function `name`, and the caller gives its type. A function pointer has the size of a data pointer on the supported targets.
        Some(p) => unsafe { core::mem::transmute_copy::<*mut core::ffi::c_void, F>(&p.as_ptr()) },
        None => {
            eprintln!(
                "rulean dual: the process has no function {}, build it with scripts/lean-build.sh --dual",
                name.to_string_lossy()
            );
            std::process::abort()
        }
    }
}

unsafe extern "C" {
    /// `atexit` of the C library.
    fn atexit(f: extern "C" fn()) -> core::ffi::c_int;
}

/// Appends the line of `kernel::timing` to the file of `RULEAN_FFI_TIMING`. An error is ignored, because the process stops.
extern "C" fn write_timing() {
    use std::io::Write;
    if let Some(path) = std::env::var_os("RULEAN_FFI_TIMING") {
        let line = crate::kernel::timing().report();
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path);
        if let Ok(mut f) = file {
            let _ = writeln!(f, "{line}");
        }
    }
}

/// Registers `write_timing` with `atexit` once, if `RULEAN_FFI_TIMING` is set.
fn register_timing() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        if std::env::var_os("RULEAN_FFI_TIMING").is_some() {
            // SAFETY: `write_timing` is a function without arguments that does not unwind, as `atexit` requires.
            let _ = unsafe { atexit(write_timing) };
        }
    });
}

/// The mirrors of `add_decl` that the kernels of all the threads share.
static MIRRORS: MirrorPool = MirrorPool::new();

thread_local! {
    /// The kernel of this thread, or the reason that the process has no Lean runtime.
    static KERNEL: OnceCell<Result<Kernel<'static>, String>> = const { OnceCell::new() };
}

/// The kernel of this thread.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized.
unsafe fn with_kernel<R>(f: impl FnOnce(&Kernel<'static>) -> R) -> R {
    KERNEL.with(|k| {
        let k = k.get_or_init(|| {
            register_timing();
            // SAFETY: the contract of the function. The `Runtime` stays on this thread, because the thread-local value owns the `Kernel`.
            let rt = unsafe { Runtime::process() }?;
            let rt: &'static Runtime = Box::leak(Box::new(rt));
            // SAFETY: `rt` is the runtime of Lean v4.36.0, and the callers of the symbols keep their objects alive during the call.
            let mut k = unsafe { Kernel::new(rt) }?;
            k.share_mirrors(&MIRRORS);
            Ok(k)
        });
        match k {
            Ok(k) => f(k),
            Err(msg) => {
                // A process without the Lean runtime cannot make a `Kernel.Exception` object, so the only safe result is to stop.
                eprintln!("rulean: the process has no Lean runtime: {msg}");
                std::process::abort()
            }
        }
    })
}

/// `Lean.Kernel.Environment.addDeclCore` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::add_decl`: the call consumes `env` and borrows `decl` and `cancel`, and it gives a new `Except Kernel.Exception Kernel.Environment` object.
///
/// The object arguments are pointers to Lean objects. A `u64` has the size and the calling convention of a pointer on the supported targets.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Kernel.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_add_decl(
    env: u64,
    max_heartbeat: usize,
    max_rec_depth: usize,
    decl: u64,
    cancel: u64,
) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::add_decl`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_add(
                env,
                decl,
                false,
                "lean_add_decl",
                |e| {
                    cpp::<AddFn>(k, c"lean_add_decl_cpp")(
                        e,
                        max_heartbeat,
                        max_rec_depth,
                        decl,
                        cancel,
                    )
                },
                |e| k.add_decl(e, max_heartbeat, max_rec_depth, decl, cancel),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.add_decl(env, max_heartbeat, max_rec_depth, decl, cancel);
            r
        })
    }
}

/// `Lean.Kernel.Environment.addDeclWithoutChecking` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::add_decl_without_checking`: the call consumes `env` and borrows `decl`, and it gives a new `Except Kernel.Exception Kernel.Environment` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Kernel.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_add_decl_without_checking(env: u64, decl: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::add_decl_without_checking`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_add(
                env,
                decl,
                false,
                "lean_add_decl_without_checking",
                |e| cpp::<AddUncheckedFn>(k, c"lean_add_decl_without_checking_cpp")(e, decl),
                |e| k.add_decl_without_checking(e, decl),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.add_decl_without_checking(env, decl);
            r
        })
    }
}

/// `Lean.Environment.addDeclCore` of Lean v4.36.0 with `doCheck`, with rulean as the kernel. The elaborator calls this function for each declaration. It has the contract of `Kernel::elab_add_decl`: the call consumes `env` and borrows `decl` and `cancel`, and it gives a new `Except Kernel.Exception Lean.Environment` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_elab_add_decl(
    env: u64,
    max_heartbeat: usize,
    max_rec_depth: usize,
    decl: u64,
    cancel: u64,
) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::elab_add_decl`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_add(
                env,
                decl,
                true,
                "lean_elab_add_decl",
                |e| {
                    cpp::<AddFn>(k, c"lean_elab_add_decl_cpp")(
                        e,
                        max_heartbeat,
                        max_rec_depth,
                        decl,
                        cancel,
                    )
                },
                |e| k.elab_add_decl(e, max_heartbeat, max_rec_depth, decl, cancel),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.elab_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel);
            r
        })
    }
}

/// `Lean.Environment.addDeclCore` of Lean v4.36.0 without `doCheck`, with rulean as the kernel. It has the contract of `Kernel::elab_add_decl_without_checking`: the call consumes `env` and borrows `decl`, and it gives a new `Except Kernel.Exception Lean.Environment` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_elab_add_decl_without_checking(env: u64, decl: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::elab_add_decl_without_checking`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_add(
                env,
                decl,
                true,
                "lean_elab_add_decl_without_checking",
                |e| cpp::<AddUncheckedFn>(k, c"lean_elab_add_decl_without_checking_cpp")(e, decl),
                |e| k.elab_add_decl_without_checking(e, decl),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.elab_add_decl_without_checking(env, decl);
            r
        })
    }
}

/// `Lean.Kernel.isDefEq` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::is_def_eq`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Bool` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `a` and `b` are `Expr` objects.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_is_def_eq(env: u64, lctx: u64, a: u64, b: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::is_def_eq`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_term(
                &[env, lctx, a, b],
                true,
                "lean_kernel_is_def_eq",
                || cpp::<DefEqFn>(k, c"lean_kernel_is_def_eq_cpp")(env, lctx, a, b),
                || k.is_def_eq(env, lctx, a, b),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.is_def_eq(env, lctx, a, b);
            r
        })
    }
}

/// `Lean.Kernel.whnf` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::whnf`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Expr` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_whnf(env: u64, lctx: u64, e: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::whnf`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_term(
                &[env, lctx, e],
                false,
                "lean_kernel_whnf",
                || cpp::<TermFn>(k, c"lean_kernel_whnf_cpp")(env, lctx, e),
                || k.whnf(env, lctx, e),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.whnf(env, lctx, e);
            r
        })
    }
}

/// `Lean.Kernel.check` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::check`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Expr` object with the type of `e`.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_check(env: u64, lctx: u64, e: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::check`.
    unsafe {
        with_kernel(|k| {
            #[cfg(feature = "dual")]
            let r = k.dual_term(
                &[env, lctx, e],
                false,
                "lean_kernel_check",
                || cpp::<TermFn>(k, c"lean_kernel_check_cpp")(env, lctx, e),
                || k.check(env, lctx, e),
            );
            #[cfg(not(feature = "dual"))]
            let r = k.check(env, lctx, e);
            r
        })
    }
}
