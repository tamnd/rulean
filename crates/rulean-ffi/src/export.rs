//! The symbols that a build of Lean with rulean as its kernel links (spec 09.6.2).
//!
//! The feature `export` enables this module. The command `cargo rustc -p rulean-ffi --release --features export --crate-type staticlib` makes the static library. The library exports `lean_add_decl` with the signature of the C++ kernel of Lean v4.36.0, so it can replace the object of `src/kernel` that has this symbol. The other symbols of spec 09.6.2 are not done yet.
//!
//! Each thread that calls a symbol gets its own `Kernel`. The `Kernel` finds the functions of the Lean runtime in the images of the process, on the first call of the thread. The `Runtime` of the thread stays alive until the process stops.
//!
//! The process must not have two definitions of `lean_add_decl` that Lean can call. A test binary with this feature can load `libleanshared` with `dlopen`, because the test finds the symbol of the C++ kernel through the handle of the library.
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
