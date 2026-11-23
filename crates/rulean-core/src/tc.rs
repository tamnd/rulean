//! Engine R: the reference transcription of the type checker (spec 05.5).
//!
//! This module has the state of the checker, the local context and type inference. It is a transcription of `type_checker.cpp` and `local_ctx.cpp` of the official kernel v4.35.0. `whnf.rs` has the reduction functions and `defeq.rs` has definitional equality. Each function has the name of the official function.
//!
//! The official kernel throws a C++ exception on an error. Here an error sets a sticky fault: the first fault is kept, the functions return a dummy value after it, and each caller checks `bad` before it uses a result. So the first error is the error that the official kernel throws.
//!
//! A free variable is the store node `FVar(level, type)`. The level is a counter for each declaration, so a level is never used twice in a declaration. The caches are cleared for each declaration, as the official kernel makes a new `type_checker` for each declaration.

use alloc::vec::Vec;
use rulean_format::Safety;
use rulean_nat::Nat;
use rulean_store::ids::raw;
use rulean_store::{BinderInfo, Expr, ExprId, LevelId, Literal, NameId, Store};

use crate::conv::{Engine, FStats};
use crate::env::{ConstKind, Env};
use crate::expr::{self, Scratch};
use crate::level::{self, LevelCache};
use crate::memo::Memo;
use crate::pin;
use crate::profile::{Flags, Profile};
use crate::session::{S_INFER, Session};
use crate::trace::Trace;
use crate::value::Arena;

/// The upper bound in bytes of a `Nat` literal (`LEAN_NAT_MAX_SIZE_DEFAULT`). This is semantics and not a resource limit (spec 05.11).
pub const NAT_MAX_BYTES: u64 = 128 * 1024 * 1024;

/// The default bound of the call depth: 4 times 16 times the default `maxRecDepth` of 512 (spec 05.5 and 05.11).
pub const MAX_DEPTH: u32 = 4 * 16 * 512;

/// The kind of an error. Each kind is one exception of `kernel_exception.h` or one message of `type_checker.cpp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// "type checker does not support loose bound variables".
    LooseBVar,
    /// "unknown constant" (`environment::get`).
    UnknownConst,
    /// "unknown free variable".
    UnknownFVar,
    /// "incorrect number of universe levels parameters".
    LevelCount,
    /// "invalid declaration, it uses unsafe declaration".
    UnsafeUse,
    /// "safe declaration must not contain partial declaration".
    PartialUse,
    /// "invalid reference to undefined universe level parameter".
    UndefLevelParam,
    /// `type_expected_exception`.
    TypeExpected,
    /// `function_expected_exception`.
    FunctionExpected,
    /// `app_type_mismatch_exception`.
    AppTypeMismatch,
    /// `def_type_mismatch_exception` of a `let` or of a declaration.
    DefTypeMismatch,
    /// `invalid_proj_exception`.
    InvalidProj,
    /// "the kernel refused a `Nat` numeral because its size exceeds the maximum".
    NatTooLarge,
    /// "its second argument does not fit in a 32-bit unsigned integer".
    CountTooLarge,
    /// The call depth is above the bound. This is a resource failure and not a verdict (spec 05.11).
    DeepRecursion,
    /// The value arena of engine F is full (spec 04.5). This is a resource failure and not a verdict.
    ArenaFull,
    /// A constant of the environment does not have the expected kind. The official kernel fails with an assertion here.
    BadConst,
    /// `already_declared_exception`.
    AlreadyDeclared,
    /// "duplicate universe level parameter".
    DuplicateLevelParam,
    /// `declaration_has_free_vars_exception`.
    FreeVar,
    /// `theorem_type_is_not_prop`.
    TheoremNotProp,
    /// One of the "invalid mutual definition" messages of `add_mutual`.
    BadMutual,
    /// One of the "failed to initialize quot module" messages of `add_quot`, or an exported quotient type that is not the reference type (spec 06.5).
    BadQuot,
    /// A declaration kind that this version of rulean does not check yet.
    Unsupported,
    /// An inductive block that is not well formed: no type, types with different level parameters or parameter counts, "number of parameters mismatch" or "parameters of all inductive datatypes must match".
    BadInductive,
    /// "mutually inductive types must live in the same universe".
    UniverseMismatch,
    /// "invalid occurrence of datatype being declared" (`check_uniform_ind_occs`).
    NonUniformOcc,
    /// "does not match inductive datatypes parameters" of a constructor.
    CtorParamMismatch,
    /// "universe level of type_of(arg) is too big for the corresponding inductive datatype".
    UniverseTooBig,
    /// "has a non positive occurrence" or "contains a non valid occurrence" of the datatypes being declared.
    NonPositive,
    /// "invalid return type" of a constructor, or "duplicate constructor name".
    BadCtor,
    /// "generated recursor computation rule is not type-preserving".
    BadRecRule,
    /// A declaration uses the reserved prefix `_nested`.
    NestedPrefix,
    /// One of the "invalid nested inductive datatype" or "failed to restore nested inductive types" messages of `elim_nested_inductive_fn`.
    BadNested,
    /// An exported field that rulean recomputes does not match the recomputed value (spec 06.1).
    ExportMismatch,
}

/// The first error of a declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fault {
    pub kind: ErrorKind,
    /// The term where the error was found.
    pub at: ExprId,
}

/// The binary `Nat` operations of `reduce_nat`, in the order of the `nat_ops` table.
pub(crate) const NAT_ADD: usize = 0;
pub(crate) const NAT_SUB: usize = 1;
pub(crate) const NAT_MUL: usize = 2;
pub(crate) const NAT_POW: usize = 3;
pub(crate) const NAT_GCD: usize = 4;
pub(crate) const NAT_MOD: usize = 5;
pub(crate) const NAT_DIV: usize = 6;
pub(crate) const NAT_BEQ: usize = 7;
pub(crate) const NAT_BLE: usize = 8;
pub(crate) const NAT_LAND: usize = 9;
pub(crate) const NAT_LOR: usize = 10;
pub(crate) const NAT_XOR: usize = 11;
pub(crate) const NAT_SHL: usize = 12;
pub(crate) const NAT_SHR: usize = 13;

/// The names and the constant terms that the kernel knows by name.
#[derive(Clone, Debug)]
pub struct Builtins {
    pub nat: NameId,
    pub nat_zero: NameId,
    pub nat_succ: NameId,
    pub string: NameId,
    pub string_of_list: NameId,
    pub char_: NameId,
    pub char_of_nat: NameId,
    pub list_nil: NameId,
    pub list_cons: NameId,
    pub bool_true: NameId,
    pub bool_false: NameId,
    pub eager_reduce: NameId,
    pub quot: NameId,
    pub quot_mk: NameId,
    pub quot_lift: NameId,
    pub quot_ind: NameId,
    pub eq: NameId,
    /// The type annotations that `consume_type_annotations` removes.
    pub opt_param: NameId,
    pub auto_param: NameId,
    pub out_param: NameId,
    pub semi_out_param: NameId,
    /// `Nat`, `String`, `Nat.zero`, `Nat.succ`, `Bool.true`, `Bool.false` and `String.ofList` as constants with no levels.
    pub e_nat: ExprId,
    pub e_string: ExprId,
    pub e_nat_zero: ExprId,
    pub e_nat_succ: ExprId,
    pub e_bool_true: ExprId,
    pub e_bool_false: ExprId,
    pub e_string_of_list: ExprId,
    /// `Char.ofNat`, `List.cons.{0} Char` and `List.nil.{0} Char`.
    pub e_char_of_nat: ExprId,
    pub e_list_cons_char: ExprId,
    pub e_list_nil_char: ExprId,
    /// The binary operations of `reduce_nat` as constants with no levels, in the order of the `NAT_*` indices.
    pub nat_ops: Vec<ExprId>,
    /// The names of the pinned primitives, in the order of `pin::TARGET_REF`.
    pub pin_names: Vec<NameId>,
}

fn name2(st: &mut Store, a: &[u8], b: &[u8]) -> NameId {
    let r = st.anon();
    let p = st.name_str_bytes(r, a);
    st.name_str_bytes(p, b)
}

fn name1(st: &mut Store, a: &[u8]) -> NameId {
    let r = st.anon();
    st.name_str_bytes(r, a)
}

fn nat_op(st: &mut Store, out: &mut Vec<ExprId>, op: &[u8]) {
    let n = name2(st, b"Nat", op);
    let c = const0(st, n);
    out.push(c);
}

/// The name with the parts of `b`, separated by a dot.
pub(crate) fn dotted_name(st: &mut Store, b: &[u8]) -> NameId {
    let mut n = st.anon();
    let mut part: Vec<u8> = Vec::new();
    let mut i = 0;
    while i <= b.len() {
        if i == b.len() || b[i] == b'.' {
            n = st.name_str_bytes(n, &part);
            part.truncate(0);
        } else {
            part.push(b[i]);
        }
        i += 1;
    }
    n
}

fn const0(st: &mut Store, n: NameId) -> ExprId {
    let ls = st.level_list_empty();
    st.mk_const(n, ls)
}

impl Builtins {
    /// Interns the names and the terms.
    pub fn new(st: &mut Store) -> Builtins {
        let nat = name1(st, b"Nat");
        let nat_zero = name2(st, b"Nat", b"zero");
        let nat_succ = name2(st, b"Nat", b"succ");
        let string = name1(st, b"String");
        let string_of_list = name2(st, b"String", b"ofList");
        let char_ = name1(st, b"Char");
        let char_of_nat = name2(st, b"Char", b"ofNat");
        let list_nil = name2(st, b"List", b"nil");
        let list_cons = name2(st, b"List", b"cons");
        let bool_true = name2(st, b"Bool", b"true");
        let bool_false = name2(st, b"Bool", b"false");
        let eager_reduce = name1(st, b"eagerReduce");
        let quot = name1(st, b"Quot");
        let quot_mk = name2(st, b"Quot", b"mk");
        let quot_lift = name2(st, b"Quot", b"lift");
        let quot_ind = name2(st, b"Quot", b"ind");
        let eq = name1(st, b"Eq");
        let opt_param = name1(st, b"optParam");
        let auto_param = name1(st, b"autoParam");
        let out_param = name1(st, b"outParam");
        let semi_out_param = name1(st, b"semiOutParam");
        let e_nat = const0(st, nat);
        let e_string = const0(st, string);
        let e_nat_zero = const0(st, nat_zero);
        let e_nat_succ = const0(st, nat_succ);
        let e_bool_true = const0(st, bool_true);
        let e_bool_false = const0(st, bool_false);
        let e_string_of_list = const0(st, string_of_list);
        let e_char_of_nat = const0(st, char_of_nat);
        let e_char = const0(st, char_);
        let z = st.level_zero();
        let l0 = st.level_list(&[z]);
        let cons = st.mk_const(list_cons, l0);
        let e_list_cons_char = st.mk_app(cons, e_char);
        let nil = st.mk_const(list_nil, l0);
        let e_list_nil_char = st.mk_app(nil, e_char);
        let mut nat_ops = Vec::with_capacity(14);
        nat_op(st, &mut nat_ops, b"add");
        nat_op(st, &mut nat_ops, b"sub");
        nat_op(st, &mut nat_ops, b"mul");
        nat_op(st, &mut nat_ops, b"pow");
        nat_op(st, &mut nat_ops, b"gcd");
        nat_op(st, &mut nat_ops, b"mod");
        nat_op(st, &mut nat_ops, b"div");
        nat_op(st, &mut nat_ops, b"beq");
        nat_op(st, &mut nat_ops, b"ble");
        nat_op(st, &mut nat_ops, b"land");
        nat_op(st, &mut nat_ops, b"lor");
        nat_op(st, &mut nat_ops, b"xor");
        nat_op(st, &mut nat_ops, b"shiftLeft");
        nat_op(st, &mut nat_ops, b"shiftRight");
        let pin_names = pin::target_names(st);
        Builtins {
            nat,
            nat_zero,
            nat_succ,
            string,
            string_of_list,
            char_,
            char_of_nat,
            list_nil,
            list_cons,
            bool_true,
            bool_false,
            eager_reduce,
            quot,
            quot_mk,
            quot_lift,
            quot_ind,
            eq,
            opt_param,
            auto_param,
            out_param,
            semi_out_param,
            e_nat,
            e_string,
            e_nat_zero,
            e_nat_succ,
            e_bool_true,
            e_bool_false,
            e_string_of_list,
            e_char_of_nat,
            e_list_cons_char,
            e_list_nil_char,
            nat_ops,
            pin_names,
        }
    }
}

/// A three-valued result (`lbool`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LBool {
    True,
    False,
    Undef,
}

pub(crate) fn to_lbool(b: bool) -> LBool {
    if b { LBool::True } else { LBool::False }
}

/// The type checker of engine R.
#[derive(Debug)]
pub struct Checker {
    pub st: Store,
    pub env: Env,
    pub b: Builtins,
    pub(crate) lc: LevelCache,
    pub(crate) x: Scratch,
    /// The value arena of engine F. It is cleared at the start of each declaration.
    pub(crate) va: Arena,
    /// The number of binders that `quote` of engine F has opened. Their free variables are not in the local context.
    pub(crate) f_under: u32,
    /// The engine of the definitional equality queries (`--engine`).
    pub engine: Engine,
    /// `--confirm all`: engine R confirms each "equal" answer of engine F.
    pub confirm_all: bool,
    /// The counts of engine F since the checker was made.
    pub f_stats: FStats,
    /// The rules that the current engine F query used, as the bits `F_DELTA` and `F_TYPED`.
    pub(crate) f_bits: u32,
    /// The number of open definitional equality queries. Engine F answers only a query that is not inside another query.
    pub(crate) eq_depth: u32,
    /// `rulean explain`: write the rules that the checker applies into `trace`.
    pub trace_on: bool,
    /// The rule trace, when `trace_on` is true.
    pub trace: Trace,
    /// The level parameters of the declaration (`m_lparams`). They are checked only if `check_lparams` is true.
    pub(crate) lparams: Vec<NameId>,
    pub(crate) check_lparams: bool,
    /// The safety of the declaration (`m_definition_safety`).
    pub(crate) safety: Safety,
    // The local context, indexed by the level of the free variable.
    pub(crate) lctx_name: Vec<NameId>,
    pub(crate) lctx_info: Vec<BinderInfo>,
    pub(crate) lctx_ty: Vec<ExprId>,
    pub(crate) lctx_val: Vec<Option<ExprId>>,
    // The caches of `type_checker::state`. `infer` has the mode in the second key.
    pub(crate) c_infer: Memo,
    pub(crate) c_whnf_core: Memo,
    pub(crate) c_whnf: Memo,
    pub(crate) c_unfold: Memo,
    pub(crate) c_success: Memo,
    pub(crate) c_failure: Memo,
    /// Engine F: the pairs of values that `conv` found not equal in the current top-level query.
    pub(crate) c_conv_failure: Memo,
    /// Engine F: the pairs of values that `conv` found equal in the current top-level query (row O2 of spec 05.7.3).
    pub(crate) c_conv_success: Memo,
    /// Engine F: the result of `force` of a value at key (value, 0), and of `force_core` at key (value, 1). It is cleared together with the arena.
    pub(crate) c_force: Memo,
    /// Engine F: `const_never_proof` of a constant at key (constant, 0), 1 for true and 2 for false.
    pub(crate) c_never_proof: Memo,
    /// The session: judgments on frozen closed terms that stay across declarations (spec 08.4).
    pub sess: Session,
    /// `m_eager_reduce`.
    pub(crate) eager: bool,
    pub(crate) depth: u32,
    pub max_depth: u32,
    pub(crate) fault: Option<Fault>,
    /// The extension bits that primitive pinning turned off (spec 05.8).
    pub(crate) pin_off: u32,
    /// The targets that are compared, one bit for each target.
    pub(crate) pin_done: u32,
    /// The targets whose declaration is not equal to the reference, in the order of the comparison.
    pub pin_mismatch: Vec<NameId>,
    /// `--trust-primitives-by-name`: keep the extensions on after a mismatch, as the official kernel does.
    pub trust_primitives: bool,
    /// The flags of the semantics profile (spec 05.2).
    pub flags: Flags,
    /// The value that a function returns after a fault.
    pub(crate) dummy: ExprId,
}

impl Checker {
    /// A checker over the store, with an empty environment.
    pub fn new(st: Store) -> Checker {
        let mut st = st;
        let b = Builtins::new(&mut st);
        let dummy = b.e_nat_zero;
        Checker {
            st,
            env: Env::new(),
            b,
            lc: LevelCache::new(),
            x: Scratch::new(),
            va: Arena::new(),
            f_under: 0,
            engine: Engine::R,
            confirm_all: false,
            f_stats: FStats::default(),
            f_bits: 0,
            eq_depth: 0,
            trace_on: false,
            trace: Trace::new(),
            lparams: Vec::new(),
            check_lparams: false,
            safety: Safety::Safe,
            lctx_name: Vec::new(),
            lctx_info: Vec::new(),
            lctx_ty: Vec::new(),
            lctx_val: Vec::new(),
            c_infer: Memo::new(),
            c_whnf_core: Memo::new(),
            c_whnf: Memo::new(),
            c_unfold: Memo::new(),
            c_success: Memo::new(),
            c_failure: Memo::new(),
            c_conv_failure: Memo::new(),
            c_conv_success: Memo::new(),
            c_force: Memo::new(),
            c_never_proof: Memo::new(),
            sess: Session::default(),
            eager: false,
            depth: 0,
            max_depth: MAX_DEPTH,
            fault: None,
            pin_off: 0,
            pin_done: 0,
            pin_mismatch: Vec::new(),
            trust_primitives: false,
            flags: Profile::V4_35.flags(),
            dummy,
        }
    }

    /// Starts a declaration: clears the caches, the local context and the fault, and sets the level parameters and the safety (`type_checker(env, lctx, safety)`).
    pub fn begin(&mut self, lparams: Vec<NameId>, safety: Safety) {
        self.lparams = lparams;
        self.check_lparams = true;
        self.safety = safety;
        self.lctx_name.truncate(0);
        self.lctx_info.truncate(0);
        self.lctx_ty.truncate(0);
        self.lctx_val.truncate(0);
        self.clear_caches();
        self.va.reset();
        self.f_under = 0;
        self.f_bits = 0;
        self.eq_depth = 0;
        self.eager = false;
        self.depth = 0;
        self.fault = None;
    }

    /// Clears the caches of inference, reduction and definitional equality. The local context stays.
    pub(crate) fn clear_caches(&mut self) {
        self.c_infer.clear();
        self.c_whnf_core.clear();
        self.c_whnf.clear();
        self.c_unfold.clear();
        self.c_success.clear();
        self.c_failure.clear();
        self.c_conv_failure.clear();
        self.c_conv_success.clear();
        self.c_force.clear();
        self.c_never_proof.clear();
    }

    /// The first error since `begin`, if any.
    pub fn fault(&self) -> Option<Fault> {
        self.fault
    }

    /// True if there is a fault.
    pub fn bad(&self) -> bool {
        self.fault.is_some()
    }

    /// Records an error and returns the dummy value. Only the first error is kept.
    pub(crate) fn fail(&mut self, kind: ErrorKind, at: ExprId) -> ExprId {
        if self.fault.is_none() {
            self.fault = Some(Fault { kind, at });
        }
        self.dummy
    }

    /// Counts one call level (`scope_rec_depth`). It gives false and records a fault if the depth is above the bound.
    pub(crate) fn enter(&mut self, at: ExprId) -> bool {
        if self.bad() {
            return false;
        }
        if self.depth >= self.max_depth {
            self.fail(ErrorKind::DeepRecursion, at);
            return false;
        }
        self.depth += 1;
        true
    }

    pub(crate) fn leave(&mut self) {
        if self.depth > 0 {
            self.depth -= 1;
        }
    }

    // The local context.

    /// Adds a local declaration and returns its free variable (`mk_local_decl`).
    pub(crate) fn mk_local(
        &mut self,
        name: NameId,
        info: BinderInfo,
        ty: ExprId,
        val: Option<ExprId>,
    ) -> ExprId {
        let lvl = self.lctx_ty.len() as u32;
        self.lctx_name.push(name);
        self.lctx_info.push(info);
        self.lctx_ty.push(ty);
        self.lctx_val.push(val);
        self.st.mk_fvar(lvl, ty)
    }

    /// The value of a `let` free variable, if any.
    pub(crate) fn fvar_value(&self, lvl: u32) -> Option<ExprId> {
        let i = lvl as usize;
        if i < self.lctx_val.len() {
            self.lctx_val[i]
        } else {
            None
        }
    }

    /// True if `e` is a free variable with a value (`is_let_fvar`).
    pub(crate) fn is_let_fvar(&self, e: ExprId) -> bool {
        match self.st.node(e) {
            Expr::FVar(lvl, _) => self.fvar_value(lvl).is_some(),
            _ => false,
        }
    }

    /// Abstracts the free variables of `b` and binds them, from the last one to the first one (`local_ctx::mk_binding`).
    pub(crate) fn mk_binding(
        &mut self,
        fvars: &[ExprId],
        b: ExprId,
        is_lambda: bool,
        remove_dead_let: bool,
    ) -> ExprId {
        let mut r = expr::abstract_fvars(&mut self.st, &mut self.x, b, fvars);
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            let lvl = match self.st.node(fvars[i]) {
                Expr::FVar(l, _) => l as usize,
                _ => 0,
            };
            let name = self.lctx_name[lvl];
            let info = self.lctx_info[lvl];
            let ty0 = self.lctx_ty[lvl];
            let ty = expr::abstract_fvars(&mut self.st, &mut self.x, ty0, &fvars[..i]);
            match self.lctx_val[lvl] {
                Some(v0) => {
                    if !remove_dead_let || expr::has_loose_bvar(&self.st, &mut self.x, r, 0) {
                        let v = expr::abstract_fvars(&mut self.st, &mut self.x, v0, &fvars[..i]);
                        r = self.st.mk_let(name, ty, v, r);
                    } else {
                        r = expr::lower_loose_bvars(&mut self.st, &mut self.x, r, 1, 1);
                    }
                }
                None => {
                    if is_lambda {
                        r = self.st.mk_lam(name, info, ty, r);
                    } else {
                        r = self.st.mk_pi(name, info, ty, r);
                    }
                }
            }
        }
        r
    }

    // Helpers for terms.

    pub(crate) fn sort_level(&self, e: ExprId) -> LevelId {
        match self.st.node(e) {
            Expr::Sort(l) => l,
            _ => self.st.level_zero(),
        }
    }

    pub(crate) fn is_sort(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), Expr::Sort(_))
    }

    pub(crate) fn is_pi(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), Expr::Pi(_))
    }

    pub(crate) fn is_lambda(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), Expr::Lam(_))
    }

    pub(crate) fn is_app(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), Expr::App(_, _))
    }

    /// The name of a constant, or the anonymous name.
    pub(crate) fn const_name(&self, e: ExprId) -> NameId {
        match self.st.node(e) {
            Expr::Const(n, _) => n,
            _ => self.st.anon(),
        }
    }

    pub(crate) fn is_constant(&self, e: ExprId) -> bool {
        matches!(self.st.node(e), Expr::Const(_, _))
    }

    /// True if `e` is the constant `n` with any levels (`is_constant(e, n)`).
    pub(crate) fn is_constant_named(&self, e: ExprId, n: NameId) -> bool {
        match self.st.node(e) {
            Expr::Const(m, _) => m == n,
            _ => false,
        }
    }

    /// The argument of an application, or `e`.
    pub(crate) fn app_arg(&self, e: ExprId) -> ExprId {
        match self.st.node(e) {
            Expr::App(_, a) => a,
            _ => e,
        }
    }

    /// The function of an application, or `e`.
    pub(crate) fn app_fn1(&self, e: ExprId) -> ExprId {
        match self.st.node(e) {
            Expr::App(f, _) => f,
            _ => e,
        }
    }

    /// The domain and the body of a binder, or `e` twice.
    pub(crate) fn binding(&self, e: ExprId) -> (ExprId, ExprId) {
        match self.st.node(e) {
            Expr::Pi(b) => (b.dom, b.body),
            Expr::Lam(b) => (b.dom, b.body),
            _ => (e, e),
        }
    }

    /// The alpha-equality of the official kernel (`operator==` on `expr`).
    pub(crate) fn eq(&mut self, a: ExprId, b: ExprId) -> bool {
        expr::expr_equal(&self.st, &mut self.x, a, b)
    }

    pub(crate) fn instantiate1(&mut self, e: ExprId, v: ExprId) -> ExprId {
        expr::instantiate1(&mut self.st, &mut self.x, e, v)
    }

    pub(crate) fn instantiate_rev(&mut self, e: ExprId, subst: &[ExprId]) -> ExprId {
        expr::instantiate_rev(&mut self.st, &mut self.x, e, subst)
    }

    /// The level parameters of the constant of a slot, as a vector.
    pub(crate) fn const_lparams(&self, slot: u32) -> Vec<NameId> {
        self.env.at(slot).lparams.clone()
    }

    /// The type of the constant of the slot with the levels for its parameters (`instantiate_type_lparams`).
    pub(crate) fn instantiate_type_lparams(&mut self, slot: u32, ls: &[LevelId]) -> ExprId {
        let c = self.env.at(slot);
        let ty = c.ty;
        expr::instantiate_lparams(&mut self.st, &mut self.x, ty, &c.lparams, ls)
    }

    /// The value of the constant of the slot with the levels for its parameters (`instantiate_value_lparams`).
    pub(crate) fn instantiate_value_lparams(&mut self, slot: u32, ls: &[LevelId]) -> ExprId {
        let c = self.env.at(slot);
        let v = match c.value() {
            Some(v) => v,
            None => self.dummy,
        };
        expr::instantiate_lparams(&mut self.st, &mut self.x, v, &c.lparams, ls)
    }

    /// The slot of the constant, or a fault (`environment::get`).
    pub(crate) fn get_const(&mut self, n: NameId, at: ExprId) -> u32 {
        let s = self.env.find(n);
        if s == 0 {
            self.fail(ErrorKind::UnknownConst, at);
        }
        s
    }

    /// The byte size of a `Nat` value for the size guard (`lean_nat_size_in_bytes`): 8 bytes for each 64-bit limb.
    pub(crate) fn nat_size(v: &Nat) -> u64 {
        let n = v.limb_count() as u64;
        if n == 0 { 8 } else { n * 8 }
    }

    /// Records a fault if the size is above the bound (`check_nat_size`). It gives true if the size is in the bound.
    pub(crate) fn check_nat_size(&mut self, bytes: u64, at: ExprId) -> bool {
        if bytes > NAT_MAX_BYTES {
            self.fail(ErrorKind::NatTooLarge, at);
            return false;
        }
        true
    }

    // Inference.

    /// `ensure_sort_core`.
    pub(crate) fn ensure_sort_core(&mut self, e: ExprId, s: ExprId) -> ExprId {
        if self.bad() || self.is_sort(e) {
            return e;
        }
        let new_e = self.whnf(e);
        if self.bad() || self.is_sort(new_e) {
            new_e
        } else {
            self.fail(ErrorKind::TypeExpected, s)
        }
    }

    /// `ensure_pi_core`.
    pub(crate) fn ensure_pi_core(&mut self, e: ExprId, s: ExprId) -> ExprId {
        if self.bad() || self.is_pi(e) {
            return e;
        }
        let new_e = self.whnf(e);
        if self.bad() || self.is_pi(new_e) {
            new_e
        } else {
            self.fail(ErrorKind::FunctionExpected, s)
        }
    }

    /// `check_level`.
    pub(crate) fn check_level(&mut self, l: LevelId, at: ExprId) {
        if self.check_lparams && level::undef_param(&self.st, l, &self.lparams) != 0 {
            self.fail(ErrorKind::UndefLevelParam, at);
        }
    }

    /// `infer_fvar`.
    fn infer_fvar(&mut self, e: ExprId, lvl: u32, ty: ExprId) -> ExprId {
        if (lvl as usize) < self.lctx_ty.len() {
            ty
        } else {
            self.fail(ErrorKind::UnknownFVar, e)
        }
    }

    /// `infer_constant`.
    fn infer_constant(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        let (n, list) = match self.st.node(e) {
            Expr::Const(n, list) => (n, list),
            _ => return self.fail(ErrorKind::BadConst, e),
        };
        let slot = self.get_const(n, e);
        if slot == 0 {
            return self.dummy;
        }
        let ls = self.st.level_list_vec(list);
        let c = self.env.at(slot);
        if c.lparams.len() != ls.len() {
            return self.fail(ErrorKind::LevelCount, e);
        }
        if !infer_only {
            let c = self.env.at(slot);
            if c.is_unsafe() && self.safety != Safety::Unsafe {
                return self.fail(ErrorKind::UnsafeUse, e);
            }
            if c.is_partial_defn() && self.safety == Safety::Safe {
                return self.fail(ErrorKind::PartialUse, e);
            }
            let mut i = 0;
            while i < ls.len() {
                self.check_level(ls[i], e);
                i += 1;
            }
            if self.bad() {
                return self.dummy;
            }
        }
        self.instantiate_type_lparams(slot, &ls)
    }

    /// `infer_lambda`.
    fn infer_lambda(&mut self, e0: ExprId, infer_only: bool) -> ExprId {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Lam(b) => {
                    let d = self.instantiate_rev(b.dom, &fvars);
                    if !infer_only {
                        let t = self.infer_type_core(d, infer_only);
                        self.ensure_sort_core(t, d);
                    }
                    let fv = self.mk_local(b.name, b.info, d, None);
                    fvars.push(fv);
                    e = b.body;
                }
                _ => walking = false,
            }
        }
        if self.bad() {
            return self.dummy;
        }
        let body = self.instantiate_rev(e, &fvars);
        let r = self.infer_type_core(body, infer_only);
        if self.bad() {
            return self.dummy;
        }
        let r = expr::cheap_beta_reduce(&mut self.st, r);
        self.mk_binding(&fvars, r, false, false)
    }

    /// `infer_pi`.
    fn infer_pi(&mut self, e0: ExprId, infer_only: bool) -> ExprId {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut us: Vec<LevelId> = Vec::new();
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Pi(b) => {
                    let d = self.instantiate_rev(b.dom, &fvars);
                    let t = self.infer_type_core(d, infer_only);
                    let t1 = self.ensure_sort_core(t, d);
                    let u = self.sort_level(t1);
                    us.push(u);
                    let fv = self.mk_local(b.name, b.info, d, None);
                    fvars.push(fv);
                    e = b.body;
                }
                _ => walking = false,
            }
        }
        if self.bad() {
            return self.dummy;
        }
        let body = self.instantiate_rev(e, &fvars);
        let t = self.infer_type_core(body, infer_only);
        let s = self.ensure_sort_core(t, body);
        if self.bad() {
            return self.dummy;
        }
        let mut r = self.sort_level(s);
        let mut i = us.len();
        while i > 0 {
            i -= 1;
            r = level::mk_imax(&mut self.st, us[i], r);
        }
        self.st.mk_sort(r)
    }

    /// True if `e` is `eagerReduce _ _` (`is_eager_reduce`).
    fn is_eager_reduce(&self, e: ExprId) -> bool {
        let f = expr::app_fn(&self.st, e);
        self.pin_on(pin::PIN_EAGER)
            && self.is_constant_named(f, self.b.eager_reduce)
            && expr::app_num_args(&self.st, e) == 2
    }

    /// `infer_app`.
    fn infer_app(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        if !infer_only {
            let (f, a) = match self.st.node(e) {
                Expr::App(f, a) => (f, a),
                _ => return self.fail(ErrorKind::BadConst, e),
            };
            let ft0 = self.infer_type_core(f, infer_only);
            let f_type = self.ensure_pi_core(ft0, e);
            let a_type = self.infer_type_core(a, infer_only);
            if self.bad() {
                return self.dummy;
            }
            let (d_type, body) = self.binding(f_type);
            let saved = self.eager;
            if self.is_eager_reduce(a) {
                self.eager = true;
            }
            let ok = self.is_def_eq(a_type, d_type);
            self.eager = saved;
            if self.bad() {
                return self.dummy;
            }
            if !ok {
                return self.fail(ErrorKind::AppTypeMismatch, e);
            }
            self.instantiate1(body, a)
        } else {
            self.infer_app_only(e)
        }
    }

    /// The infer-only branch of `infer_app`. It instantiates the arguments in chunks.
    fn infer_app_only(&mut self, e: ExprId) -> ExprId {
        let mut args: Vec<ExprId> = Vec::new();
        let f = expr::app_args(&self.st, e, &mut args);
        let mut f_type = self.infer_type_core(f, true);
        let mut j = 0;
        let nargs = args.len();
        let mut i = 0;
        while i < nargs && !self.bad() {
            let (t, k) = self.app_only_step(e, f_type, &args, j, i);
            f_type = t;
            j = k;
            i += 1;
        }
        if self.bad() {
            return self.dummy;
        }
        self.instantiate_rev(f_type, &args[j..nargs])
    }

    /// One step of `infer_app_only`. It gives the new function type and the new start of the chunk.
    fn app_only_step(
        &mut self,
        e: ExprId,
        f_type: ExprId,
        args: &[ExprId],
        j: usize,
        i: usize,
    ) -> (ExprId, usize) {
        match self.st.node(f_type) {
            Expr::Pi(b) => (b.body, j),
            _ => {
                let t = self.instantiate_rev(f_type, &args[j..i]);
                let t = self.ensure_pi_core(t, e);
                let (_, body) = self.binding(t);
                (body, i)
            }
        }
    }

    /// `infer_let`.
    fn infer_let(&mut self, e0: ExprId, infer_only: bool) -> ExprId {
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Let(l) => {
                    let ty = self.instantiate_rev(l.ty, &fvars);
                    let val = self.instantiate_rev(l.value, &fvars);
                    if !infer_only {
                        let t = self.infer_type_core(ty, infer_only);
                        self.ensure_sort_core(t, ty);
                        let vt = self.infer_type_core(val, infer_only);
                        if !self.bad() && !self.is_def_eq(vt, ty) && !self.bad() {
                            self.fail(ErrorKind::DefTypeMismatch, e);
                        }
                    }
                    let fv = self.mk_local(l.name, BinderInfo::Default, ty, Some(val));
                    fvars.push(fv);
                    e = l.body;
                }
                _ => walking = false,
            }
        }
        if self.bad() {
            return self.dummy;
        }
        let body = self.instantiate_rev(e, &fvars);
        let r = self.infer_type_core(body, infer_only);
        if self.bad() {
            return self.dummy;
        }
        let r = expr::cheap_beta_reduce(&mut self.st, r);
        self.mk_binding(&fvars, r, false, true)
    }

    /// The data of the inductive type of a slot that `infer_proj` needs: the number of parameters, the number of indices, the number of constructors and the first constructor.
    pub(crate) fn induct_shape(&self, slot: u32) -> Option<(u32, u32, usize, NameId)> {
        let anon = self.st.anon();
        match &self.env.at(slot).kind {
            ConstKind::Induct(i) => Some(induct_data(i, anon)),
            _ => None,
        }
    }

    /// `infer_proj`.
    fn infer_proj(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        let (sname, idx, c) = match self.st.node(e) {
            Expr::Proj(p) => (p.struct_name, p.index, p.expr),
            _ => return self.fail(ErrorKind::BadConst, e),
        };
        let t0 = self.infer_type_core(c, infer_only);
        let ty = self.whnf(t0);
        if self.bad() {
            return self.dummy;
        }
        let mut args: Vec<ExprId> = Vec::new();
        let i_fn = expr::app_args(&self.st, ty, &mut args);
        let (i_name, i_levels) = match self.st.node(i_fn) {
            Expr::Const(n, ls) => (n, ls),
            _ => return self.fail(ErrorKind::InvalidProj, e),
        };
        if i_name != sname {
            return self.fail(ErrorKind::InvalidProj, e);
        }
        let i_slot = self.get_const(i_name, e);
        if i_slot == 0 {
            return self.dummy;
        }
        let (nparams, nindices, nctors, ctor) = match self.induct_shape(i_slot) {
            Some(x) => x,
            None => return self.fail(ErrorKind::InvalidProj, e),
        };
        if nctors != 1 || args.len() != (nparams + nindices) as usize {
            return self.fail(ErrorKind::InvalidProj, e);
        }
        let c_slot = self.get_const(ctor, e);
        if c_slot == 0 {
            return self.dummy;
        }
        let ls = self.st.level_list_vec(i_levels);
        let mut r = self.instantiate_type_lparams(c_slot, &ls);
        let mut i = 0;
        while i < nparams as usize && !self.bad() {
            r = self.whnf(r);
            match self.st.node(r) {
                Expr::Pi(b) => r = self.instantiate1(b.body, args[i]),
                _ => {
                    self.fail(ErrorKind::InvalidProj, e);
                }
            }
            i += 1;
        }
        if self.bad() {
            return self.dummy;
        }
        let is_prop_type = self.is_prop(ty);
        self.infer_proj_fields(e, i_name, idx, c, r, is_prop_type)
    }

    /// The field loop of `infer_proj`.
    fn infer_proj_fields(
        &mut self,
        e: ExprId,
        i_name: NameId,
        idx: u32,
        c: ExprId,
        r0: ExprId,
        is_prop_type: bool,
    ) -> ExprId {
        let mut r = r0;
        let mut i = 0;
        while i < idx && !self.bad() {
            r = self.whnf(r);
            match self.st.node(r) {
                Expr::Pi(b) => {
                    if expr::has_loose_bvars(&self.st, b.body) {
                        if is_prop_type && !self.is_prop(b.dom) && !self.bad() {
                            self.fail(ErrorKind::InvalidProj, e);
                        }
                        let p = self.st.mk_proj(i_name, i, c);
                        r = self.instantiate1(b.body, p);
                    } else {
                        r = b.body;
                    }
                }
                _ => {
                    self.fail(ErrorKind::InvalidProj, e);
                }
            }
            i += 1;
        }
        if self.bad() {
            return self.dummy;
        }
        r = self.whnf(r);
        let d = match self.st.node(r) {
            Expr::Pi(b) => b.dom,
            _ => return self.fail(ErrorKind::InvalidProj, e),
        };
        if is_prop_type && !self.is_prop(d) && !self.bad() {
            return self.fail(ErrorKind::InvalidProj, e);
        }
        d
    }

    /// `infer_lit`.
    fn infer_lit(&mut self, e: ExprId, l: Literal) -> ExprId {
        match l {
            Literal::Nat(n) => {
                let bytes = Checker::nat_size(self.st.nat(n));
                self.check_nat_size(bytes, e);
                self.b.e_nat
            }
            Literal::Str(_) => self.b.e_string,
        }
    }

    /// `infer_type_core`. The result is cached with the mode.
    pub(crate) fn infer_type_core(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        if self.bad() {
            return self.dummy;
        }
        if expr::has_loose_bvars(&self.st, e) {
            return self.fail(ErrorKind::LooseBVar, e);
        }
        if !self.enter(e) {
            return self.dummy;
        }
        let mode = infer_only as u32;
        let r = match self.c_infer.get(e.0, raw(mode)) {
            Some(r) => ExprId(r),
            None => {
                // Only infer-only results go into the session: a check-mode result also depends on the level parameters and the safety of the declaration.
                let key = infer_only && self.sess_key(e);
                let hit = if key {
                    self.sess_get(S_INFER, e.0, 0)
                } else {
                    None
                };
                match hit {
                    Some(r) => {
                        self.c_infer.put(e.0, raw(mode), r);
                        ExprId(r)
                    }
                    None => {
                        let r = self.infer_type_node(e, infer_only);
                        if !self.bad() {
                            self.c_infer.put(e.0, raw(mode), r.0);
                            if key {
                                self.sess.note(S_INFER, e.0, 0, r.0);
                            }
                        }
                        r
                    }
                }
            }
        };
        self.leave();
        r
    }

    fn infer_type_node(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        match self.st.node(e) {
            Expr::Lit(l) => self.infer_lit(e, l),
            Expr::Proj(_) => self.infer_proj(e, infer_only),
            Expr::FVar(lvl, ty) => self.infer_fvar(e, lvl, ty),
            Expr::BVar(_) => self.fail(ErrorKind::LooseBVar, e),
            Expr::Sort(l) => {
                if !infer_only {
                    self.check_level(l, e);
                }
                let s = self.st.level_succ(l);
                self.st.mk_sort(s)
            }
            Expr::Const(_, _) => self.infer_constant(e, infer_only),
            Expr::Lam(_) => self.infer_lambda(e, infer_only),
            Expr::Pi(_) => self.infer_pi(e, infer_only),
            Expr::App(_, _) => self.infer_app(e, infer_only),
            Expr::Let(_) => self.infer_let(e, infer_only),
        }
    }

    /// `infer_type`: inference without checks.
    pub fn infer(&mut self, e: ExprId) -> ExprId {
        self.infer_type_core(e, true)
    }

    /// `check`: inference with all checks, with the level parameters of the declaration.
    pub fn check(&mut self, e: ExprId) -> ExprId {
        let saved = self.check_lparams;
        self.check_lparams = true;
        let r = self.infer_type_core(e, false);
        self.check_lparams = saved;
        r
    }

    /// `check_ignore_undefined_universes`.
    pub fn check_ignore_undefined_universes(&mut self, e: ExprId) -> ExprId {
        let saved = self.check_lparams;
        self.check_lparams = false;
        let r = self.infer_type_core(e, false);
        self.check_lparams = saved;
        r
    }

    /// `ensure_sort`.
    pub fn ensure_sort(&mut self, e: ExprId, s: ExprId) -> ExprId {
        self.ensure_sort_core(e, s)
    }

    /// `ensure_pi`.
    pub fn ensure_pi(&mut self, e: ExprId, s: ExprId) -> ExprId {
        self.ensure_pi_core(e, s)
    }

    /// `is_prop`: the type of `e` is a sort whose level normalizes to zero.
    pub fn is_prop(&mut self, e: ExprId) -> bool {
        let t = self.infer(e);
        let s = self.ensure_sort(t, e);
        if self.bad() {
            return false;
        }
        let l = self.sort_level(s);
        level::normalizes_to_zero(&self.st, l)
    }
}

/// The number of parameters, the number of indices, the number of constructors and the first constructor of an inductive type. If there is no constructor, the first constructor is `anon`.
fn induct_data(i: &crate::env::InductInfo, anon: NameId) -> (u32, u32, usize, NameId) {
    let n = i.ctors.len();
    let mut first = anon;
    if n > 0 {
        first = i.ctors[0];
    }
    (i.nparams, i.nindices, n, first)
}
