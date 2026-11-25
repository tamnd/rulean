//! The `addDecl` and the term functions of the in-process kernel (spec 09.6.2 and 09.6.4).
//!
//! `Kernel::add_decl` has the contract of `lean_add_decl` of the C++ kernel. It takes a Lean `Kernel.Environment` and a `Declaration` object, checks the declaration with rulean, and gives an `Except Kernel.Exception Kernel.Environment` object. It uses only the functions that Lean exports, so it works with the Lean runtime of `rt`.
//!
//! The call makes a new checker. It mirrors the constants that the check can use from the Lean environment (`lean_environment_find`): the constants that the declaration refers to, the constants that their types and values refer to, the families of the inductive types, and the constants that the checker knows by name. A partial mirror is not sound, because a check can accept a declaration when a constant that it needs is not there. For example, a positivity check cannot see an occurrence behind a definition that it cannot unfold.
//!
//! The kernel keeps the mirror between the calls of a thread (spec 09.6.3). Each constant of the mirror keeps a reference to its `ConstantInfo` object, so the runtime cannot free the object or change it in place, and an object at the same address is the same constant. Each call walks the constants that the check can use and finds each one in the Lean environment. A constant with the same object is not converted again. If a constant that the walk finds is in the mirror and is not the same constant in the Lean environment, or if only the mirror has the quotient, the call makes a new mirror. The checker of the mirror has no session, so the heartbeats of a declaration do not depend on the earlier calls.
//!
//! If rulean accepts the declaration, the call adds the new constants to the Lean environment with `lean_environment_add`. If rulean rejects it, the call gives the `Kernel.Exception` constructor of the C++ kernel (spec 09.6.4). A declaration with a metavariable or a free variable gives `declHasMVars` or `declHasFVars`. The kind `exprTypeMismatch` gives `other` with a message, and so do the errors that the C++ kernel gives as `other`. An exception with a local context has the free variables of the checker. A free variable that the check makes gets the name `_kernel_fresh.N`.
//!
//! `max_heartbeat` is the heartbeat limit of the checker (spec 09.6.4). The C++ kernel counts one heartbeat for each call of `infer_type_core`, `whnf_core` and `is_def_eq_core`, and the checker counts one at the same functions. The C++ count is for each thread and starts at 0 at the start of a task, but the count of rulean starts at 0 for each declaration. The term functions have no limit, because the C++ functions use the limit of the thread and Lean does not export it. The recursion limit has no effect yet.
//!
//! With a cancel token, the check runs on a new thread, and the calling thread reads the token each millisecond (spec 09.6.4). If the token is set, the call gives `interrupted` at once. The check continues on its thread until it stops, and its result is discarded. The C++ kernel reads the token at each heartbeat, so it can stop in the middle of a check, but the checker of rulean has no point at which it can stop. Without a token, the check runs on the calling thread.
//!
//! `Kernel::elab_add_decl` and `Kernel::elab_add_decl_without_checking` have the contracts of `lean_elab_add_decl` and `lean_elab_add_decl_without_checking`, which the elaborator calls. They take a `Lean.Environment`, use `add_decl` or `add_decl_without_checking` on its kernel environment, and give the new kernel environment to `updateBaseAfterKernelAdd`, as the C++ functions do.
//!
//! `Kernel::is_def_eq`, `Kernel::whnf` and `Kernel::check` have the contracts of `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check`. They take a `Lean.Environment`, a `LocalContext` and terms. The call converts the local context and the terms, mirrors the constants that they refer to, and runs the checker in the local context. A result term goes back to Lean with the `FVarId` of each free variable.
//!
//! This module, `rt`, `live` and `export` are the only modules of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::CStr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_core::tc::{Checker, ErrorKind, Fault};
use rulean_format::{Decl, Safety};
use rulean_store::{BinderInfo, Expr, ExprId, NameId, Store};

use crate::conv::{self, Converter};
use crate::heap::{Heap, boxed};
use crate::live::LiveHeap;
use crate::make::{Encoder, Make};
use crate::rt::{LeanMake, Runtime};
use crate::{Fault as ConvFault, FaultKind};

type Find = unsafe extern "C" fn(u64, u64) -> u64;
type Add = unsafe extern "C" fn(u64, u64) -> u64;
type QuotInit = unsafe extern "C" fn(u64) -> u8;
type MarkQuot = unsafe extern "C" fn(u64) -> u64;
type ToKernel = unsafe extern "C" fn(u64) -> u64;
type UpdateBase = unsafe extern "C" fn(u64, u64) -> u64;

/// The operation of a term function.
#[derive(Clone, Copy)]
enum TermOp {
    IsDefEq,
    Whnf,
    Check,
}

/// The result of a term function, before it is an object.
enum Out {
    Bool(bool),
    Expr(ExprId),
}

/// The tags of `Kernel.Exception` of Lean v4.36.0.
const UNKNOWN_CONSTANT: u8 = 0;
const ALREADY_DECLARED: u8 = 1;
const DECL_TYPE_MISMATCH: u8 = 2;
const DECL_HAS_MVARS: u8 = 3;
const DECL_HAS_FVARS: u8 = 4;
const FUN_EXPECTED: u8 = 5;
const TYPE_EXPECTED: u8 = 6;
const LET_TYPE_MISMATCH: u8 = 7;
const APP_TYPE_MISMATCH: u8 = 9;
const INVALID_PROJ: u8 = 10;
const THM_TYPE_IS_NOT_PROP: u8 = 11;
const OTHER: u8 = 12;
const DETERMINISTIC_TIMEOUT: u64 = 13;
const EXCESSIVE_MEMORY: u64 = 14;
const DEEP_RECURSION: u64 = 15;
const INTERRUPTED: u64 = 16;

/// The stack size of the thread of a check with a cancel token. A check of a large term goes deep, and the command line tool gives its threads the same size.
const CHECK_STACK_BYTES: usize = 1 << 30;

/// The interval at which the calling thread reads the cancel token during a check.
const POLL: Duration = Duration::from_millis(1);

/// The level metavariables of a term call, as `Converter::level_mvars` gives them, and the far free variables of the call, as `Converter::far_fvars` gives them.
type TermVars = (Vec<(NameId, u64)>, Vec<NameId>);

/// A rejection, before it is a `Kernel.Exception` object.
enum Exc {
    Unknown(NameId),
    Already(NameId),
    ThmNotProp(NameId, ExprId),
    /// `declTypeMismatch`: the `Declaration` object of the call, which the call borrows, and the type of the value. The exception takes a new reference to the object.
    DeclType(u64, ExprId),
    /// `declHasMVars` or `declHasFVars`: the tag, and the `Name` object and the `Expr` object of the part of the declaration, which the call borrows. The exception takes a new reference to each object.
    DeclVars(u8, u64, u64),
    /// A kind with a local context: the tag, the name of the `let` for `letTypeMismatch`, the terms of the other fields, and the local context of the checker. For a term function, `base` is the `LocalContext` object of the call, which the call borrows, and the number of declarations of `locals` that come from it. The local context of the exception is then `base` with the other declarations of `locals`, so it keeps the declarations that the conversion skips.
    Lctx {
        tag: u8,
        name: Option<NameId>,
        terms: Vec<ExprId>,
        locals: Vec<Local>,
        base: Option<(u64, usize)>,
        /// The level metavariables and the far free variables of the call. The box keeps `Exc` small.
        vars: Box<TermVars>,
    },
    Timeout,
    Memory,
    DeepRecursion,
    Interrupted,
    Other(String),
}

/// A free variable of the local context of an exception.
struct Local {
    /// The `FVarId`.
    id: NameId,
    user: NameId,
    info: BinderInfo,
    ty: ExprId,
    value: Option<ExprId>,
}

/// A part of an exception that the encoder makes.
#[derive(Clone, Copy)]
enum Part {
    Name(NameId),
    Term(ExprId),
}

/// The largest memory of a mirror in bytes. Above it, the next call makes a new mirror, because the store keeps the terms of each declaration.
const MAX_MIRROR_BYTES: usize = 2 << 30;

/// A constant of the mirror: the `ConstantInfo` object of the Lean environment and the constants that it refers to. The entry owns one reference to the object, so the runtime cannot free the object or change it in place. Thus an object at the same address is the same constant.
#[derive(Debug)]
struct Entry {
    ci: u64,
    refs: Vec<NameId>,
}

/// The mirror of the kernel environment (spec 09.6.3): a checker and the origin of each constant of its environment, by the index of its name. The checker has no session, so a check does not depend on the earlier checks, and the heartbeats of a declaration are always the same.
#[derive(Debug)]
struct Mirror {
    chk: Checker,
    origin: BTreeMap<u32, Entry>,
}

impl Mirror {
    fn new() -> Mirror {
        let mut chk = Checker::new(Store::new());
        chk.kernel_api = true;
        chk.sess.on = false;
        Mirror {
            chk,
            origin: BTreeMap::new(),
        }
    }
}

/// The reason that the mirror cannot be used.
enum Miss {
    /// A constant of the mirror is not the constant of the Lean environment.
    Stale,
    /// A constant of the Lean environment cannot be converted.
    Fault(String),
}

/// The counts of the mirror of a kernel.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MirrorStats {
    /// The constants that the mirror converted from Lean objects.
    pub converted: u64,
    /// The constants that the mirror had already, with the same object.
    pub reused: u64,
    /// The times that the kernel made a new mirror, because a constant of the mirror was not the constant of the Lean environment.
    pub rebuilds: u64,
}

/// The in-process kernel on a Lean runtime.
#[derive(Debug)]
pub struct Kernel<'a> {
    rt: &'a Runtime,
    h: LiveHeap,
    find: Find,
    add: Add,
    quot_init: QuotInit,
    mark_quot: MarkQuot,
    to_kernel: ToKernel,
    update_base: UpdateBase,
    /// The mirror of `add_decl`. A call takes it and puts it back.
    cache: RefCell<Option<Mirror>>,
    stats: Cell<MirrorStats>,
}

/// The function `name` of the runtime with the type `F`.
///
/// # Safety
///
/// `F` is the type of the Lean function, as a function pointer.
unsafe fn func<F: Copy>(rt: &Runtime, name: &CStr) -> Result<F, String> {
    let p = rt
        .symbol(name)
        .ok_or_else(|| format!("the Lean runtime has no {name:?}"))?;
    assert_eq!(size_of::<F>(), size_of::<*mut std::ffi::c_void>());
    // SAFETY: the caller gives the type of the function, and a function pointer has the size of a data pointer.
    Ok(unsafe { std::mem::transmute_copy::<*mut std::ffi::c_void, F>(&p.as_ptr()) })
}

impl<'a> Kernel<'a> {
    /// Finds the environment functions of the runtime.
    ///
    /// # Safety
    ///
    /// `rt` is the runtime of Lean v4.36.0, and the objects that the caller gives to `add_decl` stay alive during the call.
    pub unsafe fn new(rt: &'a Runtime) -> Result<Kernel<'a>, String> {
        // SAFETY: these are the types of the exported Lean functions of v4.36.0. An exported function consumes its object arguments.
        unsafe {
            Ok(Kernel {
                rt,
                h: LiveHeap::new(),
                find: func(rt, c"lean_environment_find")?,
                add: func(rt, c"lean_environment_add")?,
                quot_init: func(rt, c"lean_environment_quot_init")?,
                mark_quot: func(rt, c"lean_environment_mark_quot_init")?,
                to_kernel: func(rt, c"lean_elab_environment_to_kernel_env")?,
                update_base: func(rt, c"lean_elab_environment_update_base_after_kernel_add")?,
                cache: RefCell::new(None),
                stats: Cell::new(MirrorStats::default()),
            })
        }
    }

    /// `Lean.Kernel.Environment.addDeclCore`. The call consumes `env` and borrows `decl` and `cancel`, as `lean_add_decl` does. The result is a new `Except Kernel.Exception Kernel.Environment` object.
    ///
    /// The call uses the mirror of the kernel (spec 09.6.3). It converts only the constants that the mirror does not have. If a constant of the mirror is not the constant of `env`, the call makes a new mirror.
    ///
    /// # Safety
    ///
    /// `env` is a `Kernel.Environment` object and `decl` is a `Declaration` object of the runtime.
    pub unsafe fn add_decl(
        &self,
        env: u64,
        max_heartbeat: usize,
        _max_rec_depth: usize,
        decl: u64,
        cancel: u64,
    ) -> u64 {
        let mut m = self.cache.borrow_mut().take().unwrap_or_else(Mirror::new);
        if m.chk.memory() > MAX_MIRROR_BYTES {
            // SAFETY: the mirror owns its references.
            unsafe { self.release(m) };
            m = Mirror::new();
        }
        // SAFETY: the caller gives `env` and `decl`.
        let d = match unsafe { self.convert_and_mirror(env, &mut m, decl) } {
            Ok(d) => d,
            Err(x) => {
                // SAFETY: the caller gives `env`.
                let r = unsafe { self.error(env, &m.chk.st, x) };
                self.put(m);
                return r;
            }
        };
        // `convert_and_mirror` can make a new mirror with the default limit, so the call sets the limit after it.
        m.chk.max_heartbeat = max_heartbeat as u64;
        let Mirror { chk, mut origin } = m;
        let before = chk.env.len();
        // SAFETY: the caller gives `cancel`, and the call borrows it.
        let (mut chk, d, fault) = match unsafe { token(cancel) } {
            None => {
                let mut chk = chk;
                let f = chk.add_decl(&d);
                (chk, d, f)
            }
            // SAFETY: the caller gives `env` and `cancel`.
            Some(tk) => match unsafe { check_with_token(chk, d, tk) } {
                Ok(r) => r,
                Err(x) => {
                    // The checker of the mirror is on the thread of the check, so the call drops the mirror.
                    // SAFETY: the mirror owns the references of `origin`.
                    unsafe { self.release_origin(&mut origin) };
                    // SAFETY: the caller gives `env`. The exception has no `Store` objects, so an empty `Store` is sufficient.
                    return unsafe { self.error(env, &Store::new(), x) };
                }
            },
        };
        if let Some(f) = fault {
            let exc = exception(&mut chk, &d, f, decl);
            // SAFETY: the caller gives `env`.
            let r = unsafe { self.error(env, &chk.st, exc) };
            // A failed check adds no constant to the Lean environment, so the mirror must not keep one.
            chk.env.truncate(before);
            self.put(Mirror { chk, origin });
            return r;
        }
        // SAFETY: the caller gives `env` and `decl`.
        let r = unsafe { self.add_new(env, &chk, &d, before, decl) };
        let m = Mirror { chk, origin };
        match r {
            Ok(e) => {
                let mut m = m;
                // SAFETY: `e` is the new environment, and the call owns it. The mirror then has the origin of each new constant.
                let ok = unsafe { self.record_new(e, &mut m, before) };
                if ok {
                    self.put(m);
                } else {
                    // SAFETY: the mirror owns its references.
                    unsafe { self.release(m) };
                }
                // SAFETY: the maker makes `Except.ok e`, and the result owns `e`.
                unsafe { LeanMake::new(self.rt) }.ctor(1, &[e], &[])
            }
            Err(r) => {
                // The Lean environment does not have the new constants, so the call drops the mirror.
                // SAFETY: the mirror owns its references.
                unsafe { self.release(m) };
                r
            }
        }
    }

    /// Converts `decl` into the store of the mirror `m`, and mirrors the constants of `env` that its check can use. If a constant of the mirror is not the constant of `env`, the call puts a new mirror into `m` and converts again.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object and `decl` is a live `Declaration` object. The call does not consume them.
    unsafe fn convert_and_mirror(&self, env: u64, m: &mut Mirror, decl: u64) -> Result<Decl, Exc> {
        for _ in 0..2 {
            let d = conv::declaration(&self.h, &mut m.chk.st, decl)
                .map_err(|f| self.conversion_exception(decl, f))?;
            let names = declared_names(&m.chk, &d);
            // SAFETY: the caller gives `env`.
            match unsafe { self.mirror_from(env, m, names, &decl_terms(&d)) } {
                Ok(()) => return Ok(d),
                Err(Miss::Fault(msg)) => return Err(Exc::Other(msg)),
                Err(Miss::Stale) => {
                    self.stats.set(MirrorStats {
                        rebuilds: self.stats.get().rebuilds + 1,
                        ..self.stats.get()
                    });
                    let old = std::mem::replace(m, Mirror::new());
                    // SAFETY: the mirror owns its references.
                    unsafe { self.release(old) };
                }
            }
        }
        // A new mirror has no constant, so its mirror cannot be stale.
        Err(Exc::Other("rulean: the new mirror is stale".to_string()))
    }

    /// The exception for the fault `f` of the conversion of the `Declaration` object `decl`. The conversion stops at a metavariable or a free variable, and the C++ kernel gives `declHasMVars` or `declHasFVars` with the first part of the declaration that has one (`conv::decl_vars`). The other faults give `other` with the reason.
    ///
    /// The C++ kernel checks a part only after the checks of the parts before it, for example the type of a definition before its value. rulean gives the exception before these checks, so a declaration with two errors can get another exception than in the C++ kernel.
    fn conversion_exception(&self, decl: u64, f: ConvFault) -> Exc {
        if matches!(f.kind, FaultKind::MetaVar | FaultKind::FreeVar)
            && let Ok(Some((kind, name, e))) = conv::decl_vars(&self.h, decl)
        {
            let tag = if kind == FaultKind::MetaVar {
                DECL_HAS_MVARS
            } else {
                DECL_HAS_FVARS
            };
            return Exc::DeclVars(tag, name, e);
        }
        Exc::Other(f.to_string())
    }

    /// Adds the new constants of the checker, the slots after `before`, to `env`. The result is the new environment, or the `Except.error` object of the call.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object, and the call consumes it. `decl` is a live `Declaration` object.
    unsafe fn add_new(
        &self,
        env: u64,
        chk: &Checker,
        d: &Decl,
        before: usize,
        decl: u64,
    ) -> Result<u64, u64> {
        let mut e = env;
        // SAFETY: the caller gives `decl`.
        if let Some(infos) = unsafe { self.shared_infos(decl) } {
            for n in declared_names(chk, d) {
                // SAFETY: `e` is a live environment.
                if let Some(ci) = unsafe { self.lookup(e, &chk.st, n) } {
                    // SAFETY: the call owns `ci` and each object of `infos`.
                    unsafe {
                        self.rt.dec(ci);
                        for i in infos {
                            self.rt.dec(i);
                        }
                        return Err(self.error(e, &chk.st, Exc::Already(n)));
                    }
                }
            }
            for ci in infos {
                // SAFETY: `add` consumes the environment and the constant, and gives a new environment.
                e = unsafe { (self.add)(e, ci) };
            }
            return Ok(e);
        }
        for s in before + 1..=chk.env.len() {
            let k = chk.env.at(s as u32).clone();
            // SAFETY: `e` is a live environment.
            if let Some(ci) = unsafe { self.lookup(e, &chk.st, k.name) } {
                // SAFETY: the test owns `ci`. A name that the mirror does not have, such as a name that the check of a nested inductive makes, can be in the Lean environment.
                unsafe {
                    self.rt.dec(ci);
                    return Err(self.error(e, &chk.st, Exc::Already(k.name)));
                }
            }
            let all = all_of(d, k.name);
            let ci = {
                // SAFETY: the encoder gives the maker only objects that it made.
                let mut m = unsafe { LeanMake::new(self.rt) };
                Encoder::new(&mut m, &chk.st).constant(&k, &all)
            };
            match ci {
                // SAFETY: `add` consumes the environment and the constant, and gives a new environment.
                Ok(ci) => e = unsafe { (self.add)(e, ci) },
                // SAFETY: `e` is a live environment.
                Err(f) => return Err(unsafe { self.error(e, &chk.st, Exc::Other(f.to_string())) }),
            }
        }
        if matches!(d, Decl::Quot(_)) {
            // SAFETY: `e` is a live environment. `quot_init` consumes it, so the call gives it a new reference.
            let init = unsafe {
                self.rt.inc(e);
                (self.quot_init)(e)
            };
            if init == 0 {
                // SAFETY: `mark_quot` consumes `e` and gives a new environment.
                e = unsafe { (self.mark_quot)(e) };
            }
        }
        Ok(e)
    }

    /// Records the origin of each new constant of the mirror, the slots after `before`: the `ConstantInfo` object of `e` and the constants that it refers to. The result is false if `e` does not have a new constant, and the mirror is then not correct.
    ///
    /// # Safety
    ///
    /// `e` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn record_new(&self, e: u64, m: &mut Mirror, before: usize) -> bool {
        for s in before + 1..=m.chk.env.len() {
            let k = m.chk.env.at(s as u32);
            // SAFETY: the caller gives `e`.
            let Some(ci) = (unsafe { self.lookup(e, &m.chk.st, k.name) }) else {
                return false;
            };
            let refs = direct_refs(&m.chk.st, k);
            if let Some(old) = m.origin.insert(k.name.0, Entry { ci, refs }) {
                // SAFETY: the mirror owned the reference of the old entry.
                unsafe { self.rt.dec(old.ci) };
            }
        }
        true
    }

    /// Drops the mirror `m` and its references to the `ConstantInfo` objects.
    ///
    /// # Safety
    ///
    /// The mirror owns one reference to the object of each entry.
    unsafe fn release(&self, m: Mirror) {
        let mut origin = m.origin;
        // SAFETY: the contract of the function.
        unsafe { self.release_origin(&mut origin) };
    }

    /// Gives back the references of the entries of `origin` and removes the entries.
    ///
    /// # Safety
    ///
    /// The map owns one reference to the object of each entry.
    unsafe fn release_origin(&self, origin: &mut BTreeMap<u32, Entry>) {
        for (_, e) in std::mem::take(origin) {
            // SAFETY: the contract of the function.
            unsafe { self.rt.dec(e.ci) };
        }
    }

    /// Keeps the mirror `m` for the next call.
    fn put(&self, m: Mirror) {
        if let Some(old) = self.cache.replace(Some(m)) {
            // A call takes the mirror first, so no other mirror is there.
            // SAFETY: the mirror owns its references.
            unsafe { self.release(old) };
        }
    }

    /// The counts of the mirror of this kernel since it was made.
    pub fn mirror_stats(&self) -> MirrorStats {
        self.stats.get()
    }

    /// `Lean.Kernel.Environment.addDeclWithoutChecking`. The call consumes `env` and borrows `decl`, as `lean_add_decl_without_checking` does. The result is a new `Except Kernel.Exception Kernel.Environment` object.
    ///
    /// The call does what the C++ kernel does when `check` is false. An axiom, a definition, a theorem and an opaque constant get no check. A mutual block must not be empty and must be unsafe or partial, and its members get no other check. An inductive block and the quotient get the full check of `add_decl`, because the C++ kernel always checks them.
    ///
    /// # Safety
    ///
    /// `env` is a `Kernel.Environment` object and `decl` is a `Declaration` object of the runtime.
    pub unsafe fn add_decl_without_checking(&self, env: u64, decl: u64) -> u64 {
        let mut st = Store::new();
        let d = match conv::declaration(&self.h, &mut st, decl) {
            Ok(d) => d,
            // SAFETY: the caller gives `env`.
            Err(f) => return unsafe { self.error(env, &st, Exc::Other(f.to_string())) },
        };
        let bad_mutual = match &d {
            Decl::Quot(_) | Decl::Induct(_) => {
                // SAFETY: the caller gives `env` and `decl`.
                return unsafe { self.add_decl(env, 0, 0, decl, boxed(0)) };
            }
            Decl::Mutual(ds) if ds.is_empty() => Some("invalid empty mutual definition"),
            Decl::Mutual(ds) if ds[0].safety == Safety::Safe => {
                Some("invalid mutual definition, declaration is not tagged as unsafe/partial")
            }
            _ => None,
        };
        if let Some(msg) = bad_mutual {
            // SAFETY: the caller gives `env`.
            return unsafe { self.error(env, &st, Exc::Other(format!("{msg} (rulean)"))) };
        }
        // SAFETY: the caller gives `decl`, and the conversion found a kind without recursors.
        let infos = unsafe { self.shared_infos(decl) }.expect("a declaration without recursors");
        let mut e = env;
        for ci in infos {
            // SAFETY: `add` consumes the environment and the constant, and gives a new environment.
            e = unsafe { (self.add)(e, ci) };
        }
        // SAFETY: the maker makes `Except.ok e`, and the result owns `e`.
        unsafe { LeanMake::new(self.rt) }.ctor(1, &[e], &[])
    }

    /// `Lean.Environment.addDeclCore` with `doCheck`, which is `lean_elab_add_decl` of Lean v4.36.0. The call consumes `env` and borrows `decl` and `cancel`. The result is a new `Except Kernel.Exception Lean.Environment` object.
    ///
    /// The C++ function makes the kernel environment of `env`, adds the declaration to it with the C++ kernel, and gives the new kernel environment to `updateBaseAfterKernelAdd`. This call does the same with `add_decl`. The exception of a rejected declaration has the kernel environment, as the C++ exception has.
    ///
    /// # Safety
    ///
    /// `env` is a `Lean.Environment` object and `decl` is a `Declaration` object of the runtime.
    pub unsafe fn elab_add_decl(
        &self,
        env: u64,
        max_heartbeat: usize,
        max_rec_depth: usize,
        decl: u64,
        cancel: u64,
    ) -> u64 {
        // SAFETY: the caller gives `env`, `decl` and `cancel`, and `add_decl` consumes the kernel environment.
        unsafe {
            self.elab(env, |k| {
                self.add_decl(k, max_heartbeat, max_rec_depth, decl, cancel)
            })
        }
    }

    /// `Lean.Environment.addDeclCore` without `doCheck`, which is `lean_elab_add_decl_without_checking` of Lean v4.36.0. The call consumes `env` and borrows `decl`. The result is a new `Except Kernel.Exception Lean.Environment` object.
    ///
    /// # Safety
    ///
    /// `env` is a `Lean.Environment` object and `decl` is a `Declaration` object of the runtime.
    pub unsafe fn elab_add_decl_without_checking(&self, env: u64, decl: u64) -> u64 {
        // SAFETY: the caller gives `env` and `decl`, and `add_decl_without_checking` consumes the kernel environment.
        unsafe { self.elab(env, |k| self.add_decl_without_checking(k, decl)) }
    }

    /// Runs `add` on the kernel environment of the `Lean.Environment` object `env`, and gives the result for `env`. `add` consumes the kernel environment and gives an `Except Kernel.Exception Kernel.Environment` object. The call consumes `env`.
    ///
    /// # Safety
    ///
    /// `env` is a live `Lean.Environment` object, and `add` has the contract above.
    unsafe fn elab(&self, env: u64, add: impl FnOnce(u64) -> u64) -> u64 {
        // SAFETY: `toKernelEnv` consumes its argument, so the call gives it a new reference to `env`.
        let kenv = unsafe {
            self.rt.inc(env);
            (self.to_kernel)(env)
        };
        let r = add(kenv);
        // `Except.error` has the tag 0 and `Except.ok` has the tag 1. The two `Except` types have the same exception.
        if self.word(r) >> 56 != 1 {
            // SAFETY: the call owns `env`, and the exception does not keep it.
            unsafe { self.rt.dec(env) };
            return r;
        }
        // SAFETY: `r` is `Except.ok` with the new kernel environment, and `updateBaseAfterKernelAdd` consumes its arguments.
        let e = unsafe {
            let k = self.field(r, 0);
            self.rt.inc(k);
            self.rt.dec(r);
            (self.update_base)(env, k)
        };
        // SAFETY: the maker makes `Except.ok e`, and the result owns `e`.
        unsafe { LeanMake::new(self.rt) }.ctor(1, &[e], &[])
    }

    /// `Lean.Kernel.isDefEq`. The call consumes `env`, `lctx`, `a` and `b`, as `lean_kernel_is_def_eq` does. The result is a new `Except Kernel.Exception Bool` object.
    ///
    /// # Safety
    ///
    /// `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `a` and `b` are `Expr` objects of the runtime.
    pub unsafe fn is_def_eq(&self, env: u64, lctx: u64, a: u64, b: u64) -> u64 {
        // SAFETY: the contract of the function.
        unsafe { self.term(env, lctx, &[a, b], TermOp::IsDefEq) }
    }

    /// `Lean.Kernel.whnf`. The call consumes `env`, `lctx` and `e`, as `lean_kernel_whnf` does. The result is a new `Except Kernel.Exception Expr` object.
    ///
    /// # Safety
    ///
    /// `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object of the runtime.
    pub unsafe fn whnf(&self, env: u64, lctx: u64, e: u64) -> u64 {
        // SAFETY: the contract of the function.
        unsafe { self.term(env, lctx, &[e], TermOp::Whnf) }
    }

    /// `Lean.Kernel.check`. The call consumes `env`, `lctx` and `e`, as `lean_kernel_check` does. The result is a new `Except Kernel.Exception Expr` object with the type of `e`.
    ///
    /// The check does not look at the universe level parameters of `e`, as `type_checker::check` without parameters does.
    ///
    /// # Safety
    ///
    /// `env` is a `Lean.Environment` object, `lctx` is a `LocalContext` object, and `e` is an `Expr` object of the runtime.
    pub unsafe fn check(&self, env: u64, lctx: u64, e: u64) -> u64 {
        // SAFETY: the contract of the function.
        unsafe { self.term(env, lctx, &[e], TermOp::Check) }
    }

    /// The common part of the term functions. The C++ kernel makes `type_checker(env.to_kernel_env(), local_ctx(lctx))`, which is safe and has no level parameters, and the call does the same.
    ///
    /// # Safety
    ///
    /// The contract of the term functions. The call consumes `env`, `lctx` and each object of `terms`.
    unsafe fn term(&self, env: u64, lctx: u64, terms: &[u64], op: TermOp) -> u64 {
        // SAFETY: `toKernelEnv` consumes the `Lean.Environment` and gives a new `Kernel.Environment`.
        let kenv = unsafe { (self.to_kernel)(env) };
        // SAFETY: `kenv` is a live environment, and the caller gives `lctx` and `terms`.
        let r = unsafe { self.term_core(kenv, lctx, terms, op) };
        // SAFETY: the call owns `lctx` and `terms`, and the result does not keep them.
        unsafe {
            self.rt.dec(lctx);
            for &t in terms {
                self.rt.dec(t);
            }
        }
        r
    }

    /// The term function `op` on `terms` in the kernel environment `kenv`. The call consumes `kenv` and borrows `lctx` and `terms`.
    ///
    /// # Safety
    ///
    /// `kenv` is a live `Kernel.Environment` object, `lctx` is a `LocalContext` object, and `terms` are `Expr` objects.
    unsafe fn term_core(&self, kenv: u64, lctx: u64, terms: &[u64], op: TermOp) -> u64 {
        let mut m = Mirror::new();
        let conv = {
            let mut c = Converter::new(&self.h, &mut m.chk.st);
            c.local_context(lctx).and_then(|locals| {
                let ids = terms
                    .iter()
                    .map(|&t| c.expr(t))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((locals, ids, c.level_mvars(), c.far_fvars()))
            })
        };
        let (locals, ids, lmvars, far) = match conv {
            Ok(x) => x,
            // SAFETY: the caller gives `kenv`.
            Err(f) => return unsafe { self.error(kenv, &m.chk.st, Exc::Other(f.to_string())) },
        };
        let mut start: Vec<ExprId> = Vec::new();
        for l in &locals {
            start.push(l.ty);
            start.extend(l.value);
        }
        start.extend_from_slice(&ids);
        // SAFETY: the caller gives `kenv`.
        let mirrored = unsafe { self.mirror_from(kenv, &mut m, Vec::new(), &start) };
        // The term functions do not keep the mirror.
        let Mirror {
            mut chk,
            mut origin,
        } = m;
        // SAFETY: the map owns its references.
        unsafe { self.release_origin(&mut origin) };
        if let Err(x) = mirrored {
            let msg = match x {
                Miss::Fault(msg) => msg,
                Miss::Stale => "rulean: a new mirror is stale".to_string(),
            };
            // SAFETY: the caller gives `kenv`.
            return unsafe { self.error(kenv, &chk.st, Exc::Other(msg)) };
        }
        chk.begin(Vec::new(), Safety::Safe);
        for l in &locals {
            let e = chk.mk_local(l.user_name, l.info, l.ty, l.value);
            if e != l.e {
                // The conversion and the checker must give the same free variable to a declaration, because the terms refer to the free variables of the conversion.
                let msg = "rulean: the local context of the checker is not the local context of the conversion";
                // SAFETY: the caller gives `kenv`.
                return unsafe { self.error(kenv, &chk.st, Exc::Other(msg.into())) };
            }
        }
        let out = match op {
            TermOp::IsDefEq => Out::Bool(chk.is_def_eq(ids[0], ids[1])),
            TermOp::Whnf => Out::Expr(chk.whnf(ids[0])),
            TermOp::Check => Out::Expr(chk.check_ignore_undefined_universes(ids[0])),
        };
        if let Some(f) = chk.fault() {
            let known: Vec<NameId> = locals.iter().map(|l| l.fvar).collect();
            let exc = term_exception(&mut chk, &start, f, &known, (lctx, &lmvars, &far));
            // SAFETY: the caller gives `kenv`.
            return unsafe { self.error(kenv, &chk.st, exc) };
        }
        let v = match out {
            Out::Bool(b) => Ok(boxed(u64::from(b))),
            Out::Expr(e) => {
                let fvars = locals.iter().map(|l| l.fvar).collect();
                // SAFETY: the encoder gives the maker only objects that it made.
                let mut m = unsafe { LeanMake::new(self.rt) };
                Encoder::new(&mut m, &chk.st)
                    .with_fvars(fvars)
                    .with_far_fvars(far)
                    .with_level_mvars(&lmvars)
                    .expr(e)
            }
        };
        match v {
            Ok(v) => {
                // SAFETY: the call owns `kenv`, and a result without an exception does not keep it.
                unsafe { self.rt.dec(kenv) };
                // SAFETY: the maker makes `Except.ok v`, and the result owns `v`.
                unsafe { LeanMake::new(self.rt) }.ctor(1, &[v], &[])
            }
            // SAFETY: the caller gives `kenv`.
            Err(f) => unsafe { self.error(kenv, &chk.st, Exc::Other(f.to_string())) },
        }
    }

    /// The `ConstantInfo` objects that the C++ kernel adds for an axiom, a definition, a theorem, an opaque constant or a mutual block, as new references, or `None` for the other kinds.
    ///
    /// The C++ kernel puts the `*Val` object of the declaration into the `ConstantInfo` (`constant_info(d)` in `environment.cpp`), so the call does the same. The terms keep their `mdata`, which the conversion into the store removes. The constructors `axiomDecl`, `defnDecl`, `thmDecl` and `opaqueDecl` have the tags 0 to 3, and so do `axiomInfo`, `defnInfo`, `thmInfo` and `opaqueInfo`. `mutualDefnDecl` has the tag 5 and a list of `DefinitionVal`.
    ///
    /// # Safety
    ///
    /// `decl` is a live `Declaration` object. The call does not consume it.
    unsafe fn shared_infos(&self, decl: u64) -> Option<Vec<u64>> {
        if decl & 1 == 1 {
            return None;
        }
        let tag = (self.word(decl) >> 56) as u8;
        // SAFETY: the maker gets only objects of the runtime.
        let mut m = unsafe { LeanMake::new(self.rt) };
        let mut vals = Vec::new();
        match tag {
            0..=3 => vals.push(self.field(decl, 0)),
            5 => {
                let mut l = self.field(decl, 0);
                while l & 1 == 0 {
                    vals.push(self.field(l, 0));
                    l = self.field(l, 1);
                }
            }
            _ => return None,
        }
        let info = if tag == 5 { 1 } else { tag };
        let infos = vals
            .into_iter()
            .map(|v| {
                // SAFETY: `v` is a field of `decl`, which is live. The constructor consumes the new reference.
                unsafe { self.rt.inc(v) };
                m.ctor(info, &[v], &[])
            })
            .collect();
        Some(infos)
    }

    /// The `ConstantInfo` object of the constant `n` of `env`, as a new reference, or `None`.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn lookup(&self, env: u64, st: &Store, n: NameId) -> Option<u64> {
        let name = {
            // SAFETY: the encoder gives the maker only objects that it made.
            let mut m = unsafe { LeanMake::new(self.rt) };
            Encoder::new(&mut m, st).name(n)
        };
        // SAFETY: `find?` consumes the environment and the name, so the call gives it a new reference to the environment. The result is an `Option ConstantInfo` that the call owns.
        unsafe {
            self.rt.inc(env);
            let r = (self.find)(env, name);
            if r == boxed(0) {
                return None;
            }
            let ci = self.field(r, 0);
            self.rt.inc(ci);
            self.rt.dec(r);
            Some(ci)
        }
    }

    /// The object field `i` of the constructor object `o`.
    fn field(&self, o: u64, i: u64) -> u64 {
        self.word(o + 8 + 8 * i)
    }

    /// The word at the address `a`. The word at the address of an object is its header, and the tag is the high byte.
    fn word(&self, a: u64) -> u64 {
        let mut b = [0u8; 8];
        let ok = self.h.read(a, &mut b);
        assert!(ok, "a field of a Lean object is not readable");
        u64::from_le_bytes(b)
    }

    /// Adds to the mirror each constant of `env` that a check can use when it starts with the constants `names` and the terms `terms`, without a check. A constant that the mirror has with the same object is not converted again. The result is `Miss::Stale` if a constant that the check can use is in the mirror and is not the same constant in `env`, or if only the mirror has the quotient.
    ///
    /// The walk finds each constant that the check can use, so a constant of the mirror that the walk does not find has no effect on the check.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn mirror_from(
        &self,
        env: u64,
        m: &mut Mirror,
        names: Vec<NameId>,
        terms: &[ExprId],
    ) -> Result<(), Miss> {
        let Mirror { chk, origin } = m;
        let mut queue = names;
        const_refs(&chk.st, terms, &mut BTreeSet::new(), &mut queue);
        let b = &chk.b;
        queue.extend([
            b.nat,
            b.nat_zero,
            b.nat_succ,
            b.string,
            b.string_of_list,
            b.char_,
            b.char_of_nat,
            b.list_nil,
            b.list_cons,
            b.bool_true,
            b.bool_false,
            b.eager_reduce,
            b.quot,
            b.quot_mk,
            b.quot_lift,
            b.quot_ind,
            b.eq,
            b.opt_param,
            b.auto_param,
            b.out_param,
            b.semi_out_param,
        ]);
        queue.extend(b.pin_names.iter().copied());
        let ops = b.nat_ops.clone();
        const_refs(&chk.st, &ops, &mut BTreeSet::new(), &mut queue);
        let mut stats = self.stats.get();
        let mut seen = BTreeSet::new();
        while let Some(n) = queue.pop() {
            if !seen.insert(n) {
                continue;
            }
            // SAFETY: the caller gives `env`.
            let ci = unsafe { self.lookup(env, &chk.st, n) };
            match (ci, origin.get(&n.0)) {
                (None, None) => {
                    if chk.env.contains(n) {
                        return Err(Miss::Stale);
                    }
                }
                (None, Some(_)) => return Err(Miss::Stale),
                (Some(ci), Some(e)) => {
                    let same = e.ci == ci;
                    // SAFETY: the call owns `ci`.
                    unsafe { self.rt.dec(ci) };
                    if !same {
                        return Err(Miss::Stale);
                    }
                    queue.extend_from_slice(&e.refs);
                    stats.reused += 1;
                }
                (Some(ci), None) => {
                    if chk.env.contains(n) {
                        // SAFETY: the call owns `ci`.
                        unsafe { self.rt.dec(ci) };
                        return Err(Miss::Stale);
                    }
                    let k = match Converter::new(&self.h, &mut chk.st).constant(ci) {
                        Ok(k) => k,
                        Err(f) => {
                            // SAFETY: the call owns `ci`.
                            unsafe { self.rt.dec(ci) };
                            return Err(Miss::Fault(f.to_string()));
                        }
                    };
                    let refs = direct_refs(&chk.st, &k);
                    queue.extend_from_slice(&refs);
                    chk.env.add(k);
                    // The entry keeps the reference of `ci`.
                    origin.insert(n.0, Entry { ci, refs });
                    stats.converted += 1;
                }
            }
        }
        self.stats.set(stats);
        // SAFETY: `quot_init` consumes the environment, so the call gives it a new reference.
        let init = unsafe {
            self.rt.inc(env);
            (self.quot_init)(env)
        };
        if init != 0 {
            chk.env.mark_quot_initialized();
        } else if chk.env.quot_initialized() {
            return Err(Miss::Stale);
        }
        chk.check_pins();
        Ok(())
    }

    /// Gives `Except.error` with the exception `x`. The call consumes `env`: the exception keeps it, or the call gives it back.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object.
    unsafe fn error(&self, env: u64, st: &Store, x: Exc) -> u64 {
        // SAFETY: the encoder gives the maker only objects that it made.
        let mut m = unsafe { LeanMake::new(self.rt) };
        let with_env = |m: &mut LeanMake, tag: u8, rest: &[u64]| {
            let mut objs = vec![env];
            objs.extend_from_slice(rest);
            m.ctor(tag, &objs, &[])
        };
        let o = match x {
            Exc::Unknown(n) => {
                let no = Encoder::new(&mut m, st).name(n);
                with_env(&mut m, UNKNOWN_CONSTANT, &[no])
            }
            Exc::Already(n) => {
                let no = Encoder::new(&mut m, st).name(n);
                with_env(&mut m, ALREADY_DECLARED, &[no])
            }
            Exc::ThmNotProp(n, ty) => {
                let (no, to) = {
                    let mut enc = Encoder::new(&mut m, st);
                    (enc.name(n), enc.expr(ty))
                };
                match to {
                    Ok(to) => with_env(&mut m, THM_TYPE_IS_NOT_PROP, &[no, to]),
                    Err(f) => {
                        m.dec(no);
                        m.dec(env);
                        let s = m.string(f.to_string().as_bytes());
                        m.ctor(OTHER, &[s], &[])
                    }
                }
            }
            Exc::DeclType(decl, given) => {
                let to = Encoder::new(&mut m, st).expr(given);
                match to {
                    Ok(to) => {
                        m.inc(decl);
                        with_env(&mut m, DECL_TYPE_MISMATCH, &[decl, to])
                    }
                    Err(f) => {
                        m.dec(env);
                        let s = m.string(f.to_string().as_bytes());
                        m.ctor(OTHER, &[s], &[])
                    }
                }
            }
            Exc::DeclVars(tag, name, e) => {
                m.inc(name);
                m.inc(e);
                with_env(&mut m, tag, &[name, e])
            }
            Exc::Lctx {
                tag,
                name,
                terms,
                locals,
                base,
                vars,
            } => match lctx_fields(&mut m, st, name, &terms, &locals, base, (&vars.0, &vars.1)) {
                Ok(objs) => with_env(&mut m, tag, &objs),
                Err(msg) => {
                    m.dec(env);
                    let s = m.string(msg.as_bytes());
                    m.ctor(OTHER, &[s], &[])
                }
            },
            Exc::Timeout | Exc::Memory | Exc::DeepRecursion | Exc::Interrupted | Exc::Other(_) => {
                m.dec(env);
                match x {
                    Exc::Timeout => boxed(DETERMINISTIC_TIMEOUT),
                    Exc::Interrupted => boxed(INTERRUPTED),
                    Exc::Memory => boxed(EXCESSIVE_MEMORY),
                    Exc::DeepRecursion => boxed(DEEP_RECURSION),
                    Exc::Other(msg) => {
                        let s = m.string(msg.as_bytes());
                        m.ctor(OTHER, &[s], &[])
                    }
                    _ => unreachable!(),
                }
            }
        };
        m.ctor(0, &[o], &[])
    }
}

/// The `IO.CancelToken` object of `cancel`, an `Option IO.CancelToken` object, or `None` for `none`.
///
/// # Safety
///
/// `cancel` is a live `Option IO.CancelToken` object.
unsafe fn token(cancel: u64) -> Option<u64> {
    if cancel & 1 == 1 {
        return None;
    }
    // SAFETY: `some` has one object field, at the offset 8.
    Some(unsafe { read_word(cancel + 8) })
}

/// Reads the word at `addr`. Another thread can write the word, so the read is atomic.
///
/// # Safety
///
/// `addr` is the address of an aligned word of a live Lean object.
unsafe fn read_word(addr: u64) -> u64 {
    let p = core::ptr::with_exposed_provenance_mut::<u64>(addr as usize);
    // SAFETY: the contract of the function. Lean writes the word with a store of one word, so an atomic read sees the old or the new value.
    unsafe { AtomicU64::from_ptr(p) }.load(Ordering::Acquire)
}

/// Tells if the cancel token `tk` is set. The C++ kernel reads the flag in the same way: `IO.CancelToken` has the fields `promise` and `setRef`, and `setRef` is an `IO.Ref Bool` with the value at the offset 8.
///
/// # Safety
///
/// `tk` is a live `IO.CancelToken` object.
unsafe fn is_set(tk: u64) -> bool {
    // SAFETY: the field `setRef` is at the offset 16, and the value of a reference is at the offset 8.
    let v = unsafe { read_word(read_word(tk + 16) + 8) };
    // A `Bool` is a boxed scalar: `false` is 1 and `true` is 3.
    v >> 1 != 0
}

/// Checks `d` on a new thread and reads the cancel token `tk` on the calling thread until the check stops. The result is `Exc::Interrupted` if the token is set first. The check then continues on its thread until it stops, and the call discards its result. The check uses no Lean object, so it is safe after the call returns.
///
/// If the process cannot make a thread, the result is `Exc::Other` with the reason.
///
/// # Safety
///
/// `tk` is a live `IO.CancelToken` object during the call.
unsafe fn check_with_token(
    mut chk: Checker,
    d: Decl,
    tk: u64,
) -> Result<(Checker, Decl, Option<Fault>), Exc> {
    // SAFETY: the contract of the function.
    if unsafe { is_set(tk) } {
        return Err(Exc::Interrupted);
    }
    let (tx, rx) = mpsc::channel();
    let job = std::thread::Builder::new()
        .name("rulean-check".to_string())
        .stack_size(CHECK_STACK_BYTES)
        .spawn(move || {
            let f = chk.add_decl(&d);
            // The receiver is gone if the token was set. The result is then not necessary.
            let _ = tx.send((chk, d, f));
        });
    if let Err(e) = job {
        return Err(Exc::Other(format!(
            "cannot make the thread of the check: {e}"
        )));
    }
    loop {
        match rx.recv_timeout(POLL) {
            Ok(r) => return Ok(r),
            Err(RecvTimeoutError::Timeout) => {
                // SAFETY: the contract of the function.
                if unsafe { is_set(tk) } {
                    return Err(Exc::Interrupted);
                }
            }
            // The thread stopped without a result, because the check panicked. The call stops in the same way.
            Err(RecvTimeoutError::Disconnected) => panic!("the check of the declaration panicked"),
        }
    }
}

/// The exception of the fault `f` of the declaration `d`. `decl` is the `Declaration` object of `d`.
fn exception(chk: &mut Checker, d: &Decl, f: Fault, decl: u64) -> Exc {
    let kind = f.kind;
    match kind {
        ErrorKind::UnknownConst => {
            let mut names = Vec::new();
            const_refs(&chk.st, &decl_terms(d), &mut BTreeSet::new(), &mut names);
            match names.into_iter().find(|&n| !chk.env.contains(n)) {
                Some(n) => Exc::Unknown(n),
                None => Exc::Other(message(kind)),
            }
        }
        ErrorKind::AlreadyDeclared => match declared_names(chk, d)
            .into_iter()
            .find(|&n| chk.env.contains(n))
        {
            Some(n) => Exc::Already(n),
            None => Exc::Other(message(kind)),
        },
        ErrorKind::TheoremNotProp => match d {
            Decl::Thm(t) => Exc::ThmNotProp(t.name, t.ty),
            _ => Exc::Other(message(kind)),
        },
        // The C++ kernel gives the declaration and the type of the value. `Fault::at` is the value of the declaration. The fault of a `let` has its expected type in `Fault::ty2`.
        ErrorKind::DefTypeMismatch
            if f.ty2 == chk.dummy() && f.ty1 != chk.dummy() && decl_values(d).contains(&f.at) =>
        {
            Exc::DeclType(decl, f.ty1)
        }
        ErrorKind::Heartbeat => Exc::Timeout,
        ErrorKind::MemoryLimit => Exc::Memory,
        ErrorKind::DeepRecursion => Exc::DeepRecursion,
        _ => lctx_exception(chk, f, &[], None, (&[], &[]))
            .unwrap_or_else(|| Exc::Other(message(kind))),
    }
}

/// The exception of a term function that fails with the fault `f`. `terms` are the types and the values of the local context and the terms of the call. `known` is the `FVarId` of each free variable of the local context of the call.
fn term_exception(
    chk: &mut Checker,
    terms: &[ExprId],
    f: Fault,
    known: &[NameId],
    (lctx, lmvars, far): (u64, &[(NameId, u64)], &[NameId]),
) -> Exc {
    let kind = f.kind;
    match kind {
        ErrorKind::UnknownConst => {
            let mut names = Vec::new();
            const_refs(&chk.st, terms, &mut BTreeSet::new(), &mut names);
            match names.into_iter().find(|&n| !chk.env.contains(n)) {
                Some(n) => Exc::Unknown(n),
                None => Exc::Other(message(kind)),
            }
        }
        ErrorKind::Heartbeat => Exc::Timeout,
        ErrorKind::MemoryLimit => Exc::Memory,
        ErrorKind::DeepRecursion => Exc::DeepRecursion,
        _ => lctx_exception(chk, f, known, Some(lctx), (lmvars, far))
            .unwrap_or_else(|| Exc::Other(message(kind))),
    }
}

/// The exception of a kind with a local context, as the C++ kernel gives it: `typeExpected`, `funExpected`, `appTypeMismatch`, `letTypeMismatch` or `invalidProj`. It is `None` for the other kinds, and if the fault does not have a term that the exception needs. `known` is the `FVarId` of each free variable of the local context of the call, and `lctx` is the `LocalContext` object of the call, if there is one. `lmvars` has the level metavariables of the call, as `Converter::level_mvars` gives them, and `far` has the far free variables of the call, as `Converter::far_fvars` gives them.
fn lctx_exception(
    chk: &mut Checker,
    f: Fault,
    known: &[NameId],
    lctx: Option<u64>,
    (lmvars, far): (&[(NameId, u64)], &[NameId]),
) -> Option<Exc> {
    let (tag, name, terms) = match f.kind {
        ErrorKind::TypeExpected => (TYPE_EXPECTED, None, vec![f.at]),
        ErrorKind::FunctionExpected => (FUN_EXPECTED, None, vec![f.at]),
        ErrorKind::InvalidProj => (INVALID_PROJ, None, vec![f.at]),
        ErrorKind::AppTypeMismatch => (APP_TYPE_MISMATCH, None, vec![f.at, f.ty1, f.ty2]),
        // The fault of a `let` is at the `let` term, and it has the type of the value and the expected type.
        ErrorKind::DefTypeMismatch => match chk.st.node(f.at) {
            Expr::Let(l) => (LET_TYPE_MISMATCH, Some(l.name), vec![f.ty1, f.ty2]),
            _ => return None,
        },
        _ => return None,
    };
    if terms.contains(&chk.dummy()) {
        return None;
    }
    Some(Exc::Lctx {
        tag,
        name,
        terms,
        locals: local_context(chk, known),
        base: lctx.map(|o| (o, known.len())),
        vars: Box::new((lmvars.to_vec(), far.to_vec())),
    })
}

/// The local context of the checker. The free variables of the levels below `known.len()` have the `FVarId` of `known`. The checker made the other free variables, and they get the names `_kernel_fresh.N`, as the C++ kernel gives them.
fn local_context(chk: &mut Checker, known: &[NameId]) -> Vec<Local> {
    let anon = chk.st.anon();
    let fresh = chk.st.name_str_bytes(anon, b"_kernel_fresh");
    (0..chk.local_count())
        .map(|i| {
            let (user, info, ty, value) = chk.local(i);
            let id = match known.get(i) {
                Some(&n) => n,
                None => chk.st.name_num(fresh, (i - known.len()) as u64),
            };
            Local {
                id,
                user,
                info,
                ty,
                value,
            }
        })
        .collect()
}

/// The fields after the environment of an exception with a local context: the `LocalContext` object, the name if there is one, and the terms. The `LocalContext` object is `base` with the other declarations of `locals`, or the declarations of `locals` if there is no `base`. The result has new references. `lmvars` and `far` are the level metavariables and the far free variables of the call. If a term cannot be encoded, the result is the message.
fn lctx_fields(
    m: &mut LeanMake,
    st: &Store,
    name: Option<NameId>,
    terms: &[ExprId],
    locals: &[Local],
    base: Option<(u64, usize)>,
    (lmvars, far): (&[(NameId, u64)], &[NameId]),
) -> Result<Vec<u64>, String> {
    let skip = base.map_or(0, |(_, n)| n);
    let mut parts = Vec::new();
    for l in &locals[skip..] {
        parts.extend([Part::Name(l.id), Part::Name(l.user), Part::Term(l.ty)]);
        parts.extend(l.value.map(Part::Term));
    }
    parts.extend(name.map(Part::Name));
    parts.extend(terms.iter().map(|&t| Part::Term(t)));
    let mut objs = Vec::with_capacity(parts.len());
    let mut fault = None;
    {
        let fvars = locals.iter().map(|l| l.id).collect();
        let mut enc = Encoder::new(m, st)
            .with_fvars(fvars)
            .with_far_fvars(far.to_vec())
            .with_level_mvars(lmvars);
        for p in parts {
            match p {
                Part::Name(n) => objs.push(enc.name(n)),
                Part::Term(t) => match enc.expr(t) {
                    Ok(o) => objs.push(o),
                    Err(f) => {
                        fault = Some(f.to_string());
                        break;
                    }
                },
            }
        }
    }
    if let Some(msg) = fault {
        for o in objs {
            m.dec(o);
        }
        return Err(msg);
    }
    let mut it = objs.into_iter();
    let mut next = || it.next().expect("an object for each part");
    let mut lctx = match base {
        Some((o, _)) => {
            m.inc(o);
            o
        }
        None => m.local_ctx_empty(),
    };
    for l in &locals[skip..] {
        let (id, user, ty) = (next(), next(), next());
        lctx = match l.value {
            Some(_) => {
                let v = next();
                m.local_ctx_let(lctx, id, user, ty, v)
            }
            None => m.local_ctx_local(lctx, id, user, ty, l.info),
        };
    }
    let mut out = vec![lctx];
    out.extend(it);
    Ok(out)
}

/// The message of `other` for a rejection of the kind `kind`. The elaborator writes `(kernel)` before it.
fn message(kind: ErrorKind) -> String {
    let s = match kind {
        ErrorKind::LooseBVar => "type checker does not support loose bound variables",
        ErrorKind::UnknownConst => "unknown constant",
        ErrorKind::UnknownFVar => "unknown free variable",
        ErrorKind::LevelCount => "incorrect number of universe levels parameters",
        ErrorKind::UnsafeUse => "invalid declaration, it uses unsafe declaration",
        ErrorKind::PartialUse => "safe declaration must not contain partial declaration",
        ErrorKind::UndefLevelParam => "invalid reference to undefined universe level parameter",
        ErrorKind::TypeExpected => "type expected",
        ErrorKind::FunctionExpected => "function expected",
        ErrorKind::AppTypeMismatch => "application type mismatch",
        ErrorKind::DefTypeMismatch => "declaration type mismatch",
        ErrorKind::InvalidProj => "invalid projection",
        ErrorKind::AlreadyDeclared => "already declared",
        ErrorKind::DuplicateLevelParam => "duplicate universe level parameter",
        ErrorKind::FreeVar => "declaration has free variables",
        ErrorKind::TheoremNotProp => "type of theorem is not a proposition",
        ErrorKind::BadMutual => "invalid mutual definition",
        ErrorKind::BadQuot => "failed to initialize quot module",
        _ => return format!("rulean rejects the declaration ({kind:?})"),
    };
    format!("{s} (rulean)")
}

/// The names of the constants that `d` declares, before the names that the check makes.
fn declared_names(chk: &Checker, d: &Decl) -> Vec<NameId> {
    match d {
        Decl::Axiom(a) => vec![a.name],
        Decl::Defn(x) => vec![x.name],
        Decl::Thm(t) => vec![t.name],
        Decl::Opaque(o) => vec![o.name],
        Decl::Quot(_) => vec![chk.b.quot, chk.b.quot_mk, chk.b.quot_lift, chk.b.quot_ind],
        Decl::Induct(b) => b
            .types
            .iter()
            .map(|t| t.name)
            .chain(b.ctors.iter().map(|c| c.name))
            .collect(),
        Decl::Mutual(ds) => ds.iter().map(|x| x.name).collect(),
    }
}

/// The values of the definitions, the theorems and the opaque constants of `d`.
fn decl_values(d: &Decl) -> Vec<ExprId> {
    match d {
        Decl::Defn(x) => vec![x.value],
        Decl::Thm(t) => vec![t.value],
        Decl::Opaque(o) => vec![o.value],
        Decl::Mutual(ds) => ds.iter().map(|x| x.value).collect(),
        Decl::Axiom(_) | Decl::Quot(_) | Decl::Induct(_) => Vec::new(),
    }
}

/// The terms of `d`.
fn decl_terms(d: &Decl) -> Vec<ExprId> {
    match d {
        Decl::Axiom(a) => vec![a.ty],
        Decl::Defn(x) => vec![x.ty, x.value],
        Decl::Thm(t) => vec![t.ty, t.value],
        Decl::Opaque(o) => vec![o.ty, o.value],
        Decl::Quot(_) => Vec::new(),
        Decl::Induct(b) => b
            .types
            .iter()
            .map(|t| t.ty)
            .chain(b.ctors.iter().map(|c| c.ty))
            .collect(),
        Decl::Mutual(ds) => ds.iter().flat_map(|x| [x.ty, x.value]).collect(),
    }
}

/// The field `all` of the constant `n` that `d` declares.
fn all_of(d: &Decl, n: NameId) -> Vec<NameId> {
    match d {
        Decl::Defn(x) => x.all.clone(),
        Decl::Thm(t) => t.all.clone(),
        Decl::Opaque(o) => o.all.clone(),
        Decl::Mutual(ds) => ds
            .iter()
            .find(|x| x.name == n)
            .map(|x| x.all.clone())
            .unwrap_or_default(),
        _ => Vec::new(),
    }
}

/// The constants that the constant `k` refers to, each one time.
fn direct_refs(st: &Store, k: &ConstInfo) -> Vec<NameId> {
    let mut out = Vec::new();
    const_info_refs(st, k, &mut BTreeSet::new(), &mut out);
    out.sort_by_key(|n| n.0);
    out.dedup();
    out
}

/// Pushes the names of the constants that `k` refers to.
fn const_info_refs(st: &Store, k: &ConstInfo, seen: &mut BTreeSet<ExprId>, out: &mut Vec<NameId>) {
    let mut es = vec![k.ty];
    match &k.kind {
        ConstKind::Defn { value, .. } | ConstKind::Thm { value } | ConstKind::Opaque { value } => {
            es.push(*value)
        }
        ConstKind::Axiom | ConstKind::Quot { .. } => {}
        ConstKind::Induct(i) => {
            out.extend(i.all.iter().copied());
            out.extend(i.ctors.iter().copied());
        }
        ConstKind::Ctor(c) => out.push(c.induct),
        ConstKind::Rec(r) => {
            out.extend(r.all.iter().copied());
            for rule in &r.rules {
                out.push(rule.ctor);
                es.push(rule.rhs);
            }
        }
    }
    const_refs(st, &es, seen, out);
}

/// Pushes the names of the constants and the projection structures in the terms `es`. A term in `seen` is not visited again.
fn const_refs(st: &Store, es: &[ExprId], seen: &mut BTreeSet<ExprId>, out: &mut Vec<NameId>) {
    let mut stack: Vec<ExprId> = es.to_vec();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) {
            continue;
        }
        match st.node(e) {
            Expr::Const(n, _) => out.push(n),
            Expr::App(f, a) => stack.extend([f, a]),
            Expr::Lam(b) | Expr::Pi(b) => stack.extend([b.dom, b.body]),
            Expr::Let(l) => stack.extend([l.ty, l.value, l.body]),
            Expr::Proj(p) => {
                out.push(p.struct_name);
                stack.push(p.expr);
            }
            Expr::FVar(_, ty) => stack.push(ty),
            Expr::BVar(_) | Expr::Sort(_) | Expr::Lit(_) => {}
        }
    }
}
