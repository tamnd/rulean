//! The `addDecl` and the term functions of the in-process kernel (spec 09.6.2 and 09.6.4).
//!
//! `Kernel::add_decl` has the contract of `lean_add_decl` of the C++ kernel. It takes a Lean `Kernel.Environment` and a `Declaration` object, checks the declaration with rulean, and gives an `Except Kernel.Exception Kernel.Environment` object. It uses only the functions that Lean exports, so it works with the Lean runtime of `rt`.
//!
//! The call makes a new checker. It mirrors the constants that the check can use from the Lean environment (`lean_environment_find`): the constants that the declaration refers to, the constants that their types and values refer to, the families of the inductive types, and the constants that the checker knows by name. A partial mirror is not sound, because a check can accept a declaration when a constant that it needs is not there. For example, a positivity check cannot see an occurrence behind a definition that it cannot unfold. The mirror is not kept between calls yet (spec 09.6.3 asks for a cache).
//!
//! If rulean accepts the declaration, the call adds the new constants to the Lean environment with `lean_environment_add`. If rulean rejects it, the call gives a `Kernel.Exception`. The kinds `unknownConstant`, `alreadyDeclared`, `thmTypeIsNotProp`, `deterministicTimeout`, `excessiveMemory` and `deepRecursion` have the constructors of the C++ kernel. The other kinds give `other` with a message.
//!
//! `max_heartbeat` is the heartbeat limit of the checker (spec 09.6.4). The C++ kernel counts one heartbeat for each call of `infer_type_core`, `whnf_core` and `is_def_eq_core`, and the checker counts one at the same functions. The C++ count is for each thread and starts at 0 at the start of a task, but the count of rulean starts at 0 for each declaration. The term functions have no limit, because the C++ functions use the limit of the thread and Lean does not export it. The recursion limit and the cancel token have no effect yet.
//!
//! `Kernel::is_def_eq`, `Kernel::whnf` and `Kernel::check` have the contracts of `lean_kernel_is_def_eq`, `lean_kernel_whnf` and `lean_kernel_check`. They take a `Lean.Environment`, a `LocalContext` and terms. The call converts the local context and the terms, mirrors the constants that they refer to, and runs the checker in the local context. A result term goes back to Lean with the `FVarId` of each free variable.
//!
//! This module, `rt`, `live` and `export` are the only modules of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use std::collections::BTreeSet;
use std::ffi::CStr;

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::{Decl, Safety};
use rulean_store::{Expr, ExprId, NameId, Store};

use crate::conv::{self, Converter};
use crate::heap::{Heap, boxed};
use crate::live::LiveHeap;
use crate::make::{Encoder, Make};
use crate::rt::{LeanMake, Runtime};

type Find = unsafe extern "C" fn(u64, u64) -> u64;
type Add = unsafe extern "C" fn(u64, u64) -> u64;
type QuotInit = unsafe extern "C" fn(u64) -> u8;
type MarkQuot = unsafe extern "C" fn(u64) -> u64;
type ToKernel = unsafe extern "C" fn(u64) -> u64;

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
const THM_TYPE_IS_NOT_PROP: u8 = 11;
const OTHER: u8 = 12;
const DETERMINISTIC_TIMEOUT: u64 = 13;
const EXCESSIVE_MEMORY: u64 = 14;
const DEEP_RECURSION: u64 = 15;

/// A rejection, before it is a `Kernel.Exception` object.
enum Exc {
    Unknown(NameId),
    Already(NameId),
    ThmNotProp(NameId, ExprId),
    Timeout,
    Memory,
    DeepRecursion,
    Other(String),
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
            })
        }
    }

    /// `Lean.Kernel.Environment.addDeclCore`. The call consumes `env` and borrows `decl` and `cancel`, as `lean_add_decl` does. The result is a new `Except Kernel.Exception Kernel.Environment` object.
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
        _cancel: u64,
    ) -> u64 {
        let mut chk = Checker::new(Store::new());
        chk.kernel_api = true;
        chk.max_heartbeat = max_heartbeat as u64;
        let d = match conv::declaration(&self.h, &mut chk.st, decl) {
            Ok(d) => d,
            // SAFETY: the caller gives `env`.
            Err(f) => return unsafe { self.error(env, &chk.st, Exc::Other(f.to_string())) },
        };
        // SAFETY: the caller gives `env`.
        if let Err(msg) = unsafe { self.mirror(env, &mut chk, &d) } {
            // SAFETY: the caller gives `env`.
            return unsafe { self.error(env, &chk.st, Exc::Other(msg)) };
        }
        let before = chk.env.len();
        if let Some(f) = chk.add_decl(&d) {
            let exc = exception(&chk, &d, f.kind);
            // SAFETY: the caller gives `env`.
            return unsafe { self.error(env, &chk.st, exc) };
        }
        let mut e = env;
        // SAFETY: the caller gives `decl`.
        if let Some(infos) = unsafe { self.shared_infos(decl) } {
            for n in declared_names(&chk, &d) {
                // SAFETY: `e` is a live environment.
                if let Some(ci) = unsafe { self.lookup(e, &chk.st, n) } {
                    // SAFETY: the call owns `ci` and each object of `infos`.
                    unsafe {
                        self.rt.dec(ci);
                        for i in infos {
                            self.rt.dec(i);
                        }
                        return self.error(e, &chk.st, Exc::Already(n));
                    }
                }
            }
            for ci in infos {
                // SAFETY: `add` consumes the environment and the constant, and gives a new environment.
                e = unsafe { (self.add)(e, ci) };
            }
            // SAFETY: the maker makes `Except.ok e`, and the result owns `e`.
            return unsafe { LeanMake::new(self.rt) }.ctor(1, &[e], &[]);
        }
        for s in before + 1..=chk.env.len() {
            let k = chk.env.at(s as u32).clone();
            // SAFETY: `e` is a live environment.
            if let Some(ci) = unsafe { self.lookup(e, &chk.st, k.name) } {
                // SAFETY: the test owns `ci`. A name that the mirror does not have, such as a name that the check of a nested inductive makes, can be in the Lean environment.
                unsafe {
                    self.rt.dec(ci);
                    return self.error(e, &chk.st, Exc::Already(k.name));
                }
            }
            let all = all_of(&d, k.name);
            let ci = {
                // SAFETY: the encoder gives the maker only objects that it made.
                let mut m = unsafe { LeanMake::new(self.rt) };
                Encoder::new(&mut m, &chk.st).constant(&k, &all)
            };
            match ci {
                // SAFETY: `add` consumes the environment and the constant, and gives a new environment.
                Ok(ci) => e = unsafe { (self.add)(e, ci) },
                // SAFETY: `e` is a live environment.
                Err(f) => return unsafe { self.error(e, &chk.st, Exc::Other(f.to_string())) },
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
        // SAFETY: the maker makes `Except.ok e`, and the result owns `e`.
        unsafe { LeanMake::new(self.rt) }.ctor(1, &[e], &[])
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
        let mut chk = Checker::new(Store::new());
        chk.kernel_api = true;
        let conv = {
            let mut c = Converter::new(&self.h, &mut chk.st);
            c.local_context(lctx).and_then(|locals| {
                let ids = terms
                    .iter()
                    .map(|&t| c.expr(t))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((locals, ids))
            })
        };
        let (locals, ids) = match conv {
            Ok(x) => x,
            // SAFETY: the caller gives `kenv`.
            Err(f) => return unsafe { self.error(kenv, &chk.st, Exc::Other(f.to_string())) },
        };
        let mut start: Vec<ExprId> = Vec::new();
        for l in &locals {
            start.push(l.ty);
            start.extend(l.value);
        }
        start.extend_from_slice(&ids);
        // SAFETY: the caller gives `kenv`.
        if let Err(msg) = unsafe { self.mirror_from(kenv, &mut chk, Vec::new(), &start) } {
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
            let exc = term_exception(&chk, &start, f.kind);
            // SAFETY: the caller gives `kenv`.
            return unsafe { self.error(kenv, &chk.st, exc) };
        }
        let v = match out {
            Out::Bool(b) => Ok(boxed(u64::from(b))),
            Out::Expr(e) => {
                let fvars = locals.iter().map(|l| l.fvar).collect();
                // SAFETY: the encoder gives the maker only objects that it made.
                let mut m = unsafe { LeanMake::new(self.rt) };
                Encoder::new(&mut m, &chk.st).with_fvars(fvars).expr(e)
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

    /// Adds to the checker each constant of `env` that the check of `d` can use, without a check.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn mirror(&self, env: u64, chk: &mut Checker, d: &Decl) -> Result<(), String> {
        let names = declared_names(chk, d);
        // SAFETY: the caller gives `env`.
        unsafe { self.mirror_from(env, chk, names, &decl_terms(d)) }
    }

    /// Adds to the checker each constant of `env` that a check can use when it starts with the constants `names` and the terms `terms`, without a check.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn mirror_from(
        &self,
        env: u64,
        chk: &mut Checker,
        names: Vec<NameId>,
        terms: &[ExprId],
    ) -> Result<(), String> {
        let mut queue = names;
        let mut seen_e = BTreeSet::new();
        const_refs(&chk.st, terms, &mut seen_e, &mut queue);
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
        const_refs(&chk.st, &ops, &mut seen_e, &mut queue);
        let mut seen = BTreeSet::new();
        while let Some(n) = queue.pop() {
            if !seen.insert(n) || chk.env.contains(n) {
                continue;
            }
            // SAFETY: the caller gives `env`.
            let Some(ci) = (unsafe { self.lookup(env, &chk.st, n) }) else {
                continue;
            };
            let k = Converter::new(&self.h, &mut chk.st).constant(ci);
            // SAFETY: the call owns `ci`, and the conversion does not keep it.
            unsafe { self.rt.dec(ci) };
            let k = k.map_err(|f| f.to_string())?;
            const_info_refs(&chk.st, &k, &mut seen_e, &mut queue);
            chk.env.add(k);
        }
        // SAFETY: `quot_init` consumes the environment, so the call gives it a new reference.
        let init = unsafe {
            self.rt.inc(env);
            (self.quot_init)(env)
        };
        if init != 0 {
            chk.env.mark_quot_initialized();
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
            Exc::Timeout | Exc::Memory | Exc::DeepRecursion | Exc::Other(_) => {
                m.dec(env);
                match x {
                    Exc::Timeout => boxed(DETERMINISTIC_TIMEOUT),
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

/// The exception of a rejection of `d` with the kind `kind`.
fn exception(chk: &Checker, d: &Decl, kind: ErrorKind) -> Exc {
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
        ErrorKind::Heartbeat => Exc::Timeout,
        ErrorKind::MemoryLimit => Exc::Memory,
        ErrorKind::DeepRecursion => Exc::DeepRecursion,
        _ => Exc::Other(message(kind)),
    }
}

/// The exception of a term function that fails with the kind `kind`. `terms` are the types and the values of the local context and the terms of the call.
fn term_exception(chk: &Checker, terms: &[ExprId], kind: ErrorKind) -> Exc {
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
        _ => Exc::Other(message(kind)),
    }
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
