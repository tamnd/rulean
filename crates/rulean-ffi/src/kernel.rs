//! The `addDecl` of the in-process kernel (spec 09.6.2 and 09.6.4).
//!
//! `Kernel::add_decl` has the contract of `lean_add_decl` of the C++ kernel. It takes a Lean `Kernel.Environment` and a `Declaration` object, checks the declaration with rulean, and gives an `Except Kernel.Exception Kernel.Environment` object. It uses only the functions that Lean exports, so it works with the Lean runtime of `rt`.
//!
//! The call makes a new checker. It mirrors the constants that the check can use from the Lean environment (`lean_environment_find`): the constants that the declaration refers to, the constants that their types and values refer to, the families of the inductive types, and the constants that the checker knows by name. A partial mirror is not sound, because a check can accept a declaration when a constant that it needs is not there. For example, a positivity check cannot see an occurrence behind a definition that it cannot unfold. The mirror is not kept between calls yet (spec 09.6.3 asks for a cache).
//!
//! If rulean accepts the declaration, the call adds the new constants to the Lean environment with `lean_environment_add`. If rulean rejects it, the call gives a `Kernel.Exception`. The kinds `unknownConstant`, `alreadyDeclared`, `thmTypeIsNotProp`, `excessiveMemory` and `deepRecursion` have the constructors of the C++ kernel. The other kinds give `other` with a message. The heartbeat limit, the recursion limit and the cancel token have no effect yet.
//!
//! This module, `rt` and `live` are the only modules of the crate with `unsafe` code (spec 12).

#![allow(unsafe_code)]

use std::collections::BTreeSet;
use std::ffi::CStr;

use rulean_core::env::{ConstInfo, ConstKind};
use rulean_core::tc::{Checker, ErrorKind};
use rulean_format::Decl;
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

/// The tags of `Kernel.Exception` of Lean v4.36.0.
const UNKNOWN_CONSTANT: u8 = 0;
const ALREADY_DECLARED: u8 = 1;
const THM_TYPE_IS_NOT_PROP: u8 = 11;
const OTHER: u8 = 12;
const EXCESSIVE_MEMORY: u64 = 14;
const DEEP_RECURSION: u64 = 15;

/// A rejection, before it is a `Kernel.Exception` object.
enum Exc {
    Unknown(NameId),
    Already(NameId),
    ThmNotProp(NameId, ExprId),
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
        _max_heartbeat: usize,
        _max_rec_depth: usize,
        decl: u64,
        _cancel: u64,
    ) -> u64 {
        let mut chk = Checker::new(Store::new());
        chk.kernel_api = true;
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
        let mut b = [0u8; 8];
        let ok = self.h.read(o + 8 + 8 * i, &mut b);
        assert!(ok, "a field of a Lean object is not readable");
        u64::from_le_bytes(b)
    }

    /// Adds to the checker each constant of `env` that the check of `d` can use, without a check.
    ///
    /// # Safety
    ///
    /// `env` is a live `Kernel.Environment` object. The call does not consume it.
    unsafe fn mirror(&self, env: u64, chk: &mut Checker, d: &Decl) -> Result<(), String> {
        let mut queue = declared_names(chk, d);
        let mut seen_e = BTreeSet::new();
        const_refs(&chk.st, &decl_terms(d), &mut seen_e, &mut queue);
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
            Exc::Memory | Exc::DeepRecursion | Exc::Other(_) => {
                m.dec(env);
                match x {
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
