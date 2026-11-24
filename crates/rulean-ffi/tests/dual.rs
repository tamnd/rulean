//! The dual-kernel test (spec 09.6.5 and 11.3). Each declaration goes to the C++ kernel of Lean v4.36.0 and to rulean in one process, and the two verdicts must be the same.
//!
//! The test writes each declaration as a Lean `Declaration` object with `LeanMake`. The C++ kernel gets the object through `lean_add_decl`. rulean gets the same object through `conv::declaration`, as in the in-process mode. After the declarations, the test reads the constants of the C++ environment with `lean_environment_find` and compares them with the constants of rulean, so the recursors that the two kernels make must also be the same.
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
use rulean_core::tc::Checker;
use rulean_ffi::conv::{self, Converter};
use rulean_ffi::heap::{Heap, boxed};
use rulean_ffi::live::LiveHeap;
use rulean_ffi::make::Encoder;
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
type Find = unsafe extern "C" fn(u64, u64) -> u64;

/// The two kernels and their environments.
struct Dual<'a> {
    rt: &'a Runtime,
    h: LiveHeap,
    add_decl: AddDecl,
    find: Find,
    /// The C++ kernel environment. The test owns one reference.
    env: u64,
    chk: Checker,
}

impl Dual<'_> {
    /// Gives `d` of the store `st` to the two kernels, and gives the verdict of the C++ kernel and of rulean.
    fn add(&mut self, st: &Store, d: &Decl) -> (bool, bool) {
        let o = {
            // SAFETY: the encoder gives the maker only objects that it made.
            let mut m = unsafe { LeanMake::new(self.rt) };
            Encoder::new(&mut m, st).declaration(d).expect("an object")
        };
        // `lean_add_decl` consumes the environment, so the test gives it a new reference and keeps its own for a rejection. It borrows the declaration and the cancel token.
        // SAFETY: `env` and `o` are live objects, and the function has the type of `addDeclCore`.
        let r = unsafe {
            self.rt.inc(self.env);
            (self.add_decl)(self.env, 0, 512, o, boxed(0))
        };
        // `Except.error` has the tag 0 and `Except.ok` has the tag 1.
        let cpp = tag(&self.h, r) == 1;
        if cpp {
            let new = word(&self.h, r + 8);
            // SAFETY: `new` is a field of `r`, which the test owns. The test takes a reference to it and gives back `r` and the old environment.
            unsafe {
                self.rt.inc(new);
                self.rt.dec(r);
                self.rt.dec(self.env);
            }
            self.env = new;
        } else {
            // SAFETY: the test owns `r`.
            unsafe { self.rt.dec(r) };
        }
        let got = conv::declaration(&self.h, &mut self.chk.st, o).expect("a declaration");
        let ours = self.chk.add_decl(&got).is_none();
        // SAFETY: the test owns `o`.
        unsafe { self.rt.dec(o) };
        (cpp, ours)
    }

    /// Reads the constant `s` of the C++ environment and compares it with the constant of rulean.
    fn same_constant(&mut self, s: &str) {
        let n = qname(&mut self.chk.st, s);
        let slot = self.chk.env.find(n);
        assert_ne!(slot, 0, "rulean has no {s}");
        let ours = self.chk.env.at(slot).clone();
        let name = {
            // SAFETY: the encoder gives the maker only objects that it made.
            let mut m = unsafe { LeanMake::new(self.rt) };
            Encoder::new(&mut m, &self.chk.st).name(n)
        };
        // SAFETY: `find?` consumes the environment and the name, so the test gives it a new reference to the environment.
        let r = unsafe {
            self.rt.inc(self.env);
            (self.find)(self.env, name)
        };
        // `Option.some` has the tag 1, and `Option.none` is the boxed scalar 0.
        assert_ne!(r, boxed(0), "the C++ kernel has no {s}");
        let ci = word(&self.h, r + 8);
        let theirs = Converter::new(&self.h, &mut self.chk.st)
            .constant(ci)
            .expect("a constant");
        assert_eq!(theirs, ours, "{s} is not the same in the two kernels");
        // SAFETY: the test owns `r`.
        unsafe { self.rt.dec(r) };
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
    let (mk_env, to_kernel, add_decl, find) = unsafe {
        (
            func::<unsafe extern "C" fn(u32, u64) -> u64>(&rt, c"l_Lean_mkEmptyEnvironment"),
            func::<unsafe extern "C" fn(u64) -> u64>(&rt, c"lean_elab_environment_to_kernel_env"),
            func::<AddDecl>(&rt, c"lean_add_decl"),
            func::<Find>(&rt, c"lean_environment_find"),
        )
    };
    // SAFETY: the objects are made by the Lean runtime and stay alive while the test uses them.
    let h = unsafe { LiveHeap::new() };
    // `mkEmptyEnvironment 0` in `IO`. The world is the boxed scalar 0, and `EStateM.Result.ok` has the tag 0.
    // SAFETY: the functions have these types, and the test owns each result.
    let env = unsafe {
        let r = mk_env(0, boxed(0));
        assert_eq!(tag(&h, r), 0, "mkEmptyEnvironment failed");
        let e = word(&h, r + 8);
        rt.inc(e);
        rt.dec(r);
        to_kernel(e)
    };
    let mut chk = Checker::new(Store::new());
    chk.kernel_api = true;
    let mut dual = Dual {
        rt: &rt,
        h,
        add_decl,
        find,
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

    for (what, d, want) in &cases {
        let (cpp, ours) = dual.add(&st, d);
        assert_eq!(cpp, *want, "the C++ kernel on {what}");
        assert_eq!(ours, cpp, "rulean and the C++ kernel differ on {what}");
    }

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
    // SAFETY: the test owns the environment.
    unsafe { rt.dec(dual.env) };
}
