//! The symbols that a build of Lean with rulean as its kernel links (spec 09.6.2).
//!
//! The feature `export` enables this module. The command `cargo rustc -p rulean-ffi --release --features export --crate-type staticlib` makes the static library. The library exports `lean_add_decl`, `lean_add_decl_without_checking`, `lean_elab_add_decl`, `lean_elab_add_decl_without_checking`, `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check` with the signatures of the C++ kernel of Lean v4.36.0, so it can replace the objects of Lean that have these symbols.
//!
//! Each thread that calls a symbol gets its own `Kernel`. The `Kernel` finds the functions of the Lean runtime in the images of the process, on the first call of the thread. The `Runtime` of the thread stays alive until the process stops.
//!
//! The process must not have two definitions of a symbol that Lean can call. A test binary with this feature can load `libleanshared` with `dlopen`, because the test finds the symbols of the C++ kernel through the handle of the library.
//!
//! This module, `rt`, `live` and `kernel` are the only modules of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use std::cell::OnceCell;

use crate::kernel::Kernel;
use crate::rt::Runtime;

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
            // SAFETY: the contract of the function. The `Runtime` stays on this thread, because the thread-local value owns the `Kernel`.
            let rt = unsafe { Runtime::process() }?;
            let rt: &'static Runtime = Box::leak(Box::new(rt));
            // SAFETY: `rt` is the runtime of Lean v4.36.0, and the callers of the symbols keep their objects alive during the call.
            unsafe { Kernel::new(rt) }
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
    unsafe { with_kernel(|k| k.add_decl(env, max_heartbeat, max_rec_depth, decl, cancel)) }
}

/// `Lean.Kernel.Environment.addDeclWithoutChecking` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::add_decl_without_checking`: the call consumes `env` and borrows `decl`, and it gives a new `Except Kernel.Exception Kernel.Environment` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Kernel.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_add_decl_without_checking(env: u64, decl: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::add_decl_without_checking`.
    unsafe { with_kernel(|k| k.add_decl_without_checking(env, decl)) }
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
    unsafe { with_kernel(|k| k.elab_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel)) }
}

/// `Lean.Environment.addDeclCore` of Lean v4.36.0 without `doCheck`, with rulean as the kernel. It has the contract of `Kernel::elab_add_decl_without_checking`: the call consumes `env` and borrows `decl`, and it gives a new `Except Kernel.Exception Lean.Environment` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object and `decl` is a `Declaration` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_elab_add_decl_without_checking(env: u64, decl: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::elab_add_decl_without_checking`.
    unsafe { with_kernel(|k| k.elab_add_decl_without_checking(env, decl)) }
}

/// `Lean.Kernel.isDefEq` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::is_def_eq`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Bool` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `a` and `b` are `Expr` objects.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_is_def_eq(env: u64, lctx: u64, a: u64, b: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::is_def_eq`.
    unsafe { with_kernel(|k| k.is_def_eq(env, lctx, a, b)) }
}

/// `Lean.Kernel.whnf` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::whnf`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Expr` object.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_whnf(env: u64, lctx: u64, e: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::whnf`.
    unsafe { with_kernel(|k| k.whnf(env, lctx, e)) }
}

/// `Lean.Kernel.check` of Lean v4.36.0, with rulean as the kernel. It has the contract of `Kernel::check`: the call consumes all its arguments, and it gives a new `Except Kernel.Exception Expr` object with the type of `e`.
///
/// # Safety
///
/// The process has Lean v4.36.0 in it, and Lean is initialized. `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_kernel_check(env: u64, lctx: u64, e: u64) -> u64 {
    // SAFETY: the contract of the function is the contract of `with_kernel` and of `Kernel::check`.
    unsafe { with_kernel(|k| k.check(env, lctx, e)) }
}
