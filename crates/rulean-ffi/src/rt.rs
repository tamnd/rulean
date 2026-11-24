//! The Lean runtime in the process (spec 09.6.3). This module finds the functions that the shared library of Lean v4.36.0 exports, and `LeanMake` uses them to make Lean objects.
//!
//! The module finds the functions with `dlsym` when the program runs, and the crate has no link-time dependency on Lean. `dlopen` and `dlsym` are in the platform library (libSystem on macOS, the C library on Linux), so the no-C rule of spec 13.3.1 does not change. There are two ways to get a `Runtime`:
//!
//! - `Runtime::open` loads `libleanshared` from a path and initializes the Lean modules one time in the process. The tests use it with the library of the Lean toolchain.
//! - `Runtime::process` finds the functions in the process. A Lean process that has rulean in it uses it, because Lean is then loaded and initialized.
//!
//! `LeanMake` calls `lean_expr_mk_app`, `lean_level_mk_succ`, `lean_name_mk_string` and the other exports of Lean, so Lean computes the cached data of each object. For the other constructors, `LeanMake` does what `lean_alloc_ctor` of `lean.h` does. The reference counts follow the rules of `lean_inc_ref` and `lean_dec_ref` in `lean.h` of v4.36.0, with the sticky range of thread-shared counts.
//!
//! This module, `live`, `kernel` and `export` are the only modules of the crate with `unsafe` code (spec 12). The module is only on Linux and macOS with 64-bit pointers.

#![allow(unsafe_code)]

use core::ffi::{c_char, c_void};
use core::marker::PhantomData;
use core::sync::atomic::{AtomicI32, Ordering};
use std::ffi::{CStr, CString};
use std::path::Path;
use std::sync::Once;

use rulean_nat::Nat;
use rulean_store::BinderInfo;

use crate::heap::boxed;
use crate::make::Make;

/// A pointer to a Lean object or a boxed scalar.
type Obj = *mut c_void;

/// The largest value of a boxed natural number (`LEAN_MAX_SMALL_NAT`).
const MAX_SMALL_NAT: u64 = u64::MAX >> 1;

/// The largest size of a small object of mimalloc (`MI_SMALL_SIZE_MAX`). The Lean release of v4.36.0 has `LEAN_MIMALLOC` in `config.h`.
const MAX_SMALL_SIZE: usize = 128 * 8;

/// `LEAN_RC_STICKY`. A thread-shared count at or below this value does not change.
const RC_STICKY: i32 = i32::MIN + 0x1000_0000;

mod dl {
    use core::ffi::{c_char, c_int, c_void};

    unsafe extern "C" {
        pub fn dlopen(path: *const c_char, mode: c_int) -> *mut c_void;
        pub fn dlsym(handle: *mut c_void, name: *const c_char) -> *mut c_void;
        pub fn dlerror() -> *mut c_char;
    }

    pub const RTLD_NOW: c_int = 2;
    #[cfg(target_os = "macos")]
    pub const RTLD_GLOBAL: c_int = 8;
    #[cfg(not(target_os = "macos"))]
    pub const RTLD_GLOBAL: c_int = 0x100;

    /// `RTLD_DEFAULT`: find the symbol in all the images of the process.
    pub fn rtld_default() -> *mut c_void {
        if cfg!(target_os = "macos") {
            core::ptr::without_provenance_mut(usize::MAX - 1)
        } else {
            core::ptr::null_mut()
        }
    }
}

/// The text of the last error of `dlopen` or `dlsym`.
fn dl_error() -> String {
    // SAFETY: `dlerror` gives a null pointer or a pointer to a C string that stays valid until the next call on this thread.
    unsafe {
        let p = dl::dlerror();
        if p.is_null() {
            "no error text".to_owned()
        } else {
            CStr::from_ptr(p).to_string_lossy().into_owned()
        }
    }
}

macro_rules! exports {
    ($($field:ident : $sym:literal => fn($($arg:ty),*) $(-> $ret:ty)?;)*) => {
        /// The functions of the Lean runtime that rulean calls.
        #[derive(Clone, Copy)]
        struct Fns {
            $($field: unsafe extern "C" fn($($arg),*) $(-> $ret)?,)*
        }

        impl Fns {
            /// Finds each function in `handle`.
            ///
            /// # Safety
            ///
            /// `handle` is a handle of `dlopen` or `RTLD_DEFAULT`, and each symbol that it has is the function of Lean v4.36.0 with the type of its field.
            unsafe fn find(handle: *mut c_void) -> Result<Fns, String> {
                Ok(Fns {
                    $($field: {
                        let name = concat!($sym, "\0");
                        // SAFETY: `name` is a C string, and `handle` is valid by the contract of the function.
                        let p = unsafe { dl::dlsym(handle, name.as_ptr().cast::<c_char>()) };
                        if p.is_null() {
                            return Err(format!("the Lean runtime has no symbol `{}`: {}", $sym, dl_error()));
                        }
                        // SAFETY: the symbol is the function of this type by the contract of the function. A function pointer and a data pointer have the same size on the supported targets.
                        unsafe { core::mem::transmute::<*mut c_void, unsafe extern "C" fn($($arg),*) $(-> $ret)?>(p) }
                    },)*
                })
            }
        }
    };
}

exports! {
    initialize: "lean_initialize" => fn();
    mark_end_initialization: "lean_io_mark_end_initialization" => fn();
    alloc_small_object_core: "lean_alloc_small_object_core" => fn(u32) -> Obj;
    dec_ref_cold: "lean_dec_ref_cold" => fn(Obj);
    mk_string_from_bytes: "lean_mk_string_from_bytes" => fn(*const c_char, usize) -> Obj;
    cstr_to_nat: "lean_cstr_to_nat" => fn(*const c_char) -> Obj;
    name_mk_string: "lean_name_mk_string" => fn(Obj, Obj) -> Obj;
    name_mk_numeral: "lean_name_mk_numeral" => fn(Obj, Obj) -> Obj;
    level_mk_zero: "lean_level_mk_zero" => fn(Obj) -> Obj;
    level_mk_succ: "lean_level_mk_succ" => fn(Obj) -> Obj;
    level_mk_max: "lean_level_mk_max" => fn(Obj, Obj) -> Obj;
    level_mk_imax: "lean_level_mk_imax" => fn(Obj, Obj) -> Obj;
    level_mk_param: "lean_level_mk_param" => fn(Obj) -> Obj;
    expr_mk_bvar: "lean_expr_mk_bvar" => fn(Obj) -> Obj;
    expr_mk_fvar: "lean_expr_mk_fvar" => fn(Obj) -> Obj;
    expr_mk_sort: "lean_expr_mk_sort" => fn(Obj) -> Obj;
    expr_mk_const: "lean_expr_mk_const" => fn(Obj, Obj) -> Obj;
    expr_mk_app: "lean_expr_mk_app" => fn(Obj, Obj) -> Obj;
    expr_mk_lambda: "lean_expr_mk_lambda" => fn(Obj, Obj, Obj, u8) -> Obj;
    expr_mk_forall: "lean_expr_mk_forall" => fn(Obj, Obj, Obj, u8) -> Obj;
    expr_mk_let: "lean_expr_mk_let" => fn(Obj, Obj, Obj, Obj, u8) -> Obj;
    expr_mk_lit: "lean_expr_mk_lit" => fn(Obj) -> Obj;
    expr_mk_proj: "lean_expr_mk_proj" => fn(Obj, Obj, Obj) -> Obj;
}

/// The Lean modules are initialized one time in the process.
static INIT: Once = Once::new();

/// The functions of the Lean runtime in the process.
///
/// The objects of Lean have counts that only one thread changes, so a `Runtime` stays on the thread that made it.
pub struct Runtime {
    f: Fns,
    handle: *mut c_void,
    _one_thread: PhantomData<*mut ()>,
}

impl core::fmt::Debug for Runtime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Runtime").finish_non_exhaustive()
    }
}

impl Runtime {
    /// Loads the shared library of Lean at `path`, finds its functions, and initializes the Lean modules if this is the first `open` of the process.
    ///
    /// # Safety
    ///
    /// `path` is the `libleanshared` of Lean v4.36.0. The load runs the initializers of the library, and the first call runs `lean_initialize`. No other code of the process uses Lean, and the caller uses the Lean objects only on this thread.
    pub unsafe fn open(path: &Path) -> Result<Runtime, String> {
        let c = CString::new(path.as_os_str().as_encoded_bytes())
            .map_err(|_| format!("the path {} has a zero byte", path.display()))?;
        // SAFETY: `c` is a C string. The contract of the function makes the library a valid Lean library.
        let h = unsafe { dl::dlopen(c.as_ptr(), dl::RTLD_NOW | dl::RTLD_GLOBAL) };
        if h.is_null() {
            return Err(format!("cannot load {}: {}", path.display(), dl_error()));
        }
        // SAFETY: `h` is a handle of `dlopen`, and the library is Lean v4.36.0.
        let f = unsafe { Fns::find(h)? };
        INIT.call_once(|| {
            // SAFETY: this runs one time in the process, before any other call into Lean, as `lean.h` requires.
            unsafe {
                (f.initialize)();
                (f.mark_end_initialization)();
            }
        });
        Ok(Runtime {
            f,
            handle: h,
            _one_thread: PhantomData,
        })
    }

    /// Finds the functions of the Lean runtime in the images of the process.
    ///
    /// # Safety
    ///
    /// The process has Lean v4.36.0 in it, and Lean is initialized. The caller uses the Lean objects only on this thread.
    pub unsafe fn process() -> Result<Runtime, String> {
        // SAFETY: `RTLD_DEFAULT` is a valid handle, and the contract of the function makes the symbols the functions of Lean v4.36.0.
        let f = unsafe { Fns::find(dl::rtld_default())? };
        Ok(Runtime {
            f,
            handle: dl::rtld_default(),
            _one_thread: PhantomData,
        })
    }

    /// The address of the symbol `name` of the Lean runtime, or `None` if there is no such symbol. A call through the address is `unsafe`, and the caller must give it the type of the Lean function.
    pub fn symbol(&self, name: &CStr) -> Option<core::ptr::NonNull<c_void>> {
        // SAFETY: `handle` is a handle of `dlopen` or `RTLD_DEFAULT`, and `name` is a C string.
        core::ptr::NonNull::new(unsafe { dl::dlsym(self.handle, name.as_ptr()) })
    }

    /// Gives back one reference to `o`, as `lean_dec` does.
    ///
    /// # Safety
    ///
    /// `o` is a boxed scalar or a live Lean object, and the caller owns one reference to it.
    pub unsafe fn dec(&self, o: u64) {
        if o & 1 == 1 {
            return;
        }
        let p = obj(o);
        // SAFETY: `o` is a live object by the contract of the function, and its count is the first 4 bytes, aligned to 4.
        let rc = unsafe { AtomicI32::from_ptr(p.cast::<i32>()) };
        let v = rc.load(Ordering::Relaxed);
        if v > 1 {
            rc.store(v - 1, Ordering::Relaxed);
        } else if v != 0 {
            // SAFETY: this is the call of `lean_dec_ref` for a count of 1 or a thread-shared count.
            unsafe { (self.f.dec_ref_cold)(p) };
        }
    }

    /// Takes one more reference to `o`, as `lean_inc` does.
    ///
    /// # Safety
    ///
    /// `o` is a boxed scalar or a live Lean object.
    pub unsafe fn inc(&self, o: u64) {
        if o & 1 == 1 {
            return;
        }
        // SAFETY: `o` is a live object by the contract of the function.
        let rc = unsafe { AtomicI32::from_ptr(obj(o).cast::<i32>()) };
        let v = rc.load(Ordering::Relaxed);
        if v > 0 {
            // A count of one thread. It wraps into the sticky range on overflow, as `lean_internal_add_rc` does.
            rc.store(v.wrapping_add(1), Ordering::Relaxed);
        } else if (v as u32) > (RC_STICKY as u32) {
            // A thread-shared count that is not stuck. These counts are negative, so an increment subtracts.
            rc.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

fn obj(o: u64) -> Obj {
    core::ptr::with_exposed_provenance_mut(o as usize)
}

fn addr(p: Obj) -> u64 {
    p.expose_provenance() as u64
}

/// The constructors of `Make` with the functions of the Lean runtime.
#[derive(Debug)]
pub struct LeanMake<'a> {
    rt: &'a Runtime,
}

impl<'a> LeanMake<'a> {
    /// A maker of Lean objects with the runtime `rt`.
    ///
    /// # Safety
    ///
    /// Each object argument of a constructor is a boxed scalar or a live Lean object, and the caller gives one reference to it. `Encoder` obeys this rule: it gives only objects that the maker made, and it takes a reference with `Make::inc` for each use.
    pub unsafe fn new(rt: &'a Runtime) -> LeanMake<'a> {
        LeanMake { rt }
    }
}

macro_rules! call {
    ($self:ident . $f:ident ( $($a:expr),* )) => {
        // SAFETY: the contract of `LeanMake::new` makes each argument an object that the call can consume, and the function is the export of Lean of this type.
        addr(unsafe { ($self.rt.f.$f)($($a),*) })
    };
}

impl Make for LeanMake<'_> {
    fn name_str(&mut self, pre: u64, s: u64) -> u64 {
        call!(self.name_mk_string(obj(pre), obj(s)))
    }
    fn name_num(&mut self, pre: u64, n: u64) -> u64 {
        call!(self.name_mk_numeral(obj(pre), obj(n)))
    }
    fn level_zero(&mut self) -> u64 {
        call!(self.level_mk_zero(obj(boxed(0))))
    }
    fn level_succ(&mut self, l: u64) -> u64 {
        call!(self.level_mk_succ(obj(l)))
    }
    fn level_max(&mut self, a: u64, b: u64) -> u64 {
        call!(self.level_mk_max(obj(a), obj(b)))
    }
    fn level_imax(&mut self, a: u64, b: u64) -> u64 {
        call!(self.level_mk_imax(obj(a), obj(b)))
    }
    fn level_param(&mut self, n: u64) -> u64 {
        call!(self.level_mk_param(obj(n)))
    }
    fn expr_bvar(&mut self, idx: u64) -> u64 {
        call!(self.expr_mk_bvar(obj(idx)))
    }
    fn expr_fvar(&mut self, id: u64) -> u64 {
        call!(self.expr_mk_fvar(obj(id)))
    }
    fn expr_sort(&mut self, l: u64) -> u64 {
        call!(self.expr_mk_sort(obj(l)))
    }
    fn expr_const(&mut self, n: u64, ls: u64) -> u64 {
        call!(self.expr_mk_const(obj(n), obj(ls)))
    }
    fn expr_app(&mut self, f: u64, a: u64) -> u64 {
        call!(self.expr_mk_app(obj(f), obj(a)))
    }
    fn expr_lambda(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64 {
        call!(self.expr_mk_lambda(obj(n), obj(dom), obj(body), bi as u8))
    }
    fn expr_forall(&mut self, n: u64, dom: u64, body: u64, bi: BinderInfo) -> u64 {
        call!(self.expr_mk_forall(obj(n), obj(dom), obj(body), bi as u8))
    }
    fn expr_let(&mut self, n: u64, ty: u64, value: u64, body: u64, nondep: bool) -> u64 {
        call!(self.expr_mk_let(obj(n), obj(ty), obj(value), obj(body), u8::from(nondep)))
    }
    fn expr_lit(&mut self, lit: u64) -> u64 {
        call!(self.expr_mk_lit(obj(lit)))
    }
    fn expr_proj(&mut self, n: u64, idx: u64, e: u64) -> u64 {
        call!(self.expr_mk_proj(obj(n), obj(idx), obj(e)))
    }
    fn nat(&mut self, n: &Nat) -> u64 {
        match n.to_u64() {
            Some(x) if x <= MAX_SMALL_NAT => boxed(x),
            _ => {
                let mut d = n.to_decimal();
                d.push(0);
                call!(self.cstr_to_nat(d.as_ptr().cast::<c_char>()))
            }
        }
    }
    fn string(&mut self, s: &[u8]) -> u64 {
        call!(self.mk_string_from_bytes(s.as_ptr().cast::<c_char>(), s.len()))
    }
    fn ctor(&mut self, t: u8, objs: &[u64], scalars: &[u8]) -> u64 {
        // This is `lean_alloc_ctor` and `lean_ctor_set` of `lean.h` with `LEAN_MIMALLOC`.
        let fields = 8 * objs.len();
        let sz = 8 + fields + scalars.len();
        let sz1 = sz.next_multiple_of(8);
        assert!(
            objs.len() < 256 && sz1 <= MAX_SMALL_SIZE,
            "a constructor of {} fields and {} scalar bytes is too large",
            objs.len(),
            scalars.len()
        );
        // SAFETY: `sz1` is a positive multiple of 8 and at most `MI_SMALL_SIZE_MAX`, as `lean_alloc_small_object_core` requires. It sets `m_cs_sz` and gives `sz1` bytes, aligned to 8.
        let p = unsafe { (self.rt.f.alloc_small_object_core)(sz1 as u32) }.cast::<u8>();
        // SAFETY: each write is in the `sz1` bytes of the new object, and the words are aligned to 8.
        unsafe {
            if sz1 > sz {
                p.add(sz1 - 8).cast::<u64>().write(0);
            }
            p.cast::<i32>().write(1);
            p.add(6).write(objs.len() as u8);
            p.add(7).write(t);
            for (i, &o) in objs.iter().enumerate() {
                p.add(8 + 8 * i).cast::<u64>().write(o);
            }
            core::ptr::copy_nonoverlapping(scalars.as_ptr(), p.add(8 + fields), scalars.len());
        }
        addr(p.cast::<c_void>())
    }
    fn inc(&mut self, o: u64) {
        // SAFETY: the contract of `LeanMake::new` makes `o` a live object.
        unsafe { self.rt.inc(o) }
    }
    fn dec(&mut self, o: u64) {
        // SAFETY: the contract of `LeanMake::new` makes `o` a live object that the caller owns.
        unsafe { self.rt.dec(o) }
    }
}
