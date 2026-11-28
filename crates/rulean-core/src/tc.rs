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
use rulean_store::ids::{low, raw};
use rulean_store::{
    BinderInfo, Expr, ExprId, LevelId, LevelListId, Literal, NameId, Raw, Store, Tier,
};

use crate::conv::{Engine, FStats};
use crate::env::{ConstKind, Env};
use crate::expr::{self, Scratch};
use crate::finfer::FInfer;
use crate::level::{self, LevelCache};
use crate::memo::{Intern, Lossy, Memo};
use crate::pin;
use crate::profile::{Flags, Profile};
use crate::session::{S_CHECK, S_INFER, Session};
use crate::trace::Trace;
use crate::value::{Arena, ValueId};

/// The default upper bound in bytes of a `Nat` literal (`LEAN_NAT_MAX_SIZE_DEFAULT`). This is semantics and not a resource limit (spec 05.11). The in-process kernel can set another bound in `Checker::nat_max` (spec 09.6).
pub const NAT_MAX_BYTES: u64 = 128 * 1024 * 1024;

/// The default bound of the call depth: 4 times 16 times the default `maxRecDepth` of 512 (spec 05.5 and 05.11).
pub const MAX_DEPTH: u32 = 4 * 16 * 512;

/// The C++ kernel stops at a depth of `maxRecDepth` times this factor (`g_kernel_rec_depth_factor`), because the kernel recurses deeper than the elaborator for the same term.
pub const REC_DEPTH_FACTOR: u64 = 16;

/// The number of calls of `enter` between two memory checks. A check adds about 30 sizes, so the cost is small.
const MEMORY_TICKS: u32 = 4096;

/// The largest number of vectors in `vpool` and in `lpool`. It is more than the depth of the nested calls that hold a vector on Init (spec perf/04.3 A9).
const POOL_MAX: usize = 64;

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
    /// A lookup of the check found no constant for a name that the mirror of `rulean-ffi` does not know (spec 09.6.3). The mirror converts the constant if the Lean environment has it, and checks the declaration again, so this is never a verdict.
    Missed,
    /// The value arena of engine F is full (spec 04.5). This is a resource failure and not a verdict.
    ArenaFull,
    /// The checker uses more memory than `--max-memory` allows (spec 12.3). This is a resource failure and not a verdict.
    MemoryLimit,
    /// The heartbeats of the declaration are above `max_heartbeat` (`deterministicTimeout`, spec 09.6.4). This is a resource failure and not a verdict.
    Heartbeat,
    /// Engine F cannot follow a rule of the profile on this query, so engine R must decide it. Engine F removes this fault, so it is never a verdict.
    FDefer,
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
    /// Two types of the error, as the C++ kernel gives them in its exception. For `AppTypeMismatch`, they are the type of the function and the type of the argument. For `DefTypeMismatch`, they are the type of the value and the expected type. The expected type of a declaration is not kept, because the declaration has it. For `BadCtor`, `ty1` is the return type of the constructor if the return type is not valid, and the dummy term if the name of the constructor is a duplicate. For the other kinds, they are the dummy term.
    pub ty1: ExprId,
    pub ty2: ExprId,
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
    /// `HAdd.hAdd`, `Add.add` and `OfNat.ofNat`, the heads that the offset view of engine F unfolds (row O11 of spec 05.7.3). They are not pinned, because the view only unfolds them, and an unfolding is a delta step of the official rules.
    pub hadd_hadd: NameId,
    pub add_add: NameId,
    pub of_nat_of_nat: NameId,
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
    /// The names of the constants of `nat_ops`, in the same order.
    pub nat_op_names: Vec<NameId>,
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

fn nat_op(st: &mut Store, out: &mut Vec<ExprId>, names: &mut Vec<NameId>, op: &[u8]) {
    let n = name2(st, b"Nat", op);
    let c = const0(st, n);
    out.push(c);
    names.push(n);
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
        let hadd_hadd = name2(st, b"HAdd", b"hAdd");
        let add_add = name2(st, b"Add", b"add");
        let of_nat_of_nat = name2(st, b"OfNat", b"ofNat");
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
        let mut nat_op_names = Vec::with_capacity(14);
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"add");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"sub");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"mul");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"pow");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"gcd");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"mod");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"div");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"beq");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"ble");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"land");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"lor");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"xor");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"shiftLeft");
        nat_op(st, &mut nat_ops, &mut nat_op_names, b"shiftRight");
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
            hadd_hadd,
            add_add,
            of_nat_of_nat,
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
            nat_op_names,
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
    /// A stack of the arguments of spines (spec perf/04.3 A9). A function that reads the arguments of a spine pushes them here and removes them before it returns, so the functions that it calls can push more arguments above them. This replaces a new `Vec` for each spine.
    pub(crate) vstk: Vec<ValueId>,
    /// A stack of the arguments of applications in `whnf_core` of engine R, used in the same way as `vstk` (spec perf/04.3 A9).
    pub(crate) estk: Vec<ExprId>,
    /// Vectors of terms that keep their capacity. A function takes one with `take_vec` and gives it back with `give_vec`, so a hot path makes no allocation, also when it recurses (spec perf/04.3 A9).
    pub(crate) vpool: Vec<Vec<ExprId>>,
    /// Vectors of levels, used in the same way as `vpool`.
    pub(crate) lpool: Vec<Vec<LevelId>>,
    /// The map of the copies of `promote` in the session. A commit takes it, clears it and gives it back, so it keeps its capacity (spec perf/11.21).
    pub(crate) pmap: Option<Memo>,
    /// The stack of `promote`, used in the same way as `pmap`.
    pub(crate) pstack: Vec<(ExprId, bool)>,
    /// The contexts and caches of engine F inference. They are cleared together with the arena.
    pub(crate) fi: FInfer,
    /// The number of binders that `quote` of engine F has opened. Their free variables are not in the local context.
    pub(crate) f_under: u32,
    /// The read-backs of one top-level `quote`, at key (value, `base` and `k`). It is cleared at the start of each top-level `quote`, because a release of the arena between two calls can give an old value id to a new value.
    pub(crate) c_quote: Lossy,
    /// The number of `quote` calls that are open.
    pub(crate) q_depth: u32,
    /// The engine of the definitional equality queries (`--engine`).
    pub engine: Engine,
    /// `--confirm all`: engine R confirms each "equal" answer of engine F.
    pub confirm_all: bool,
    /// The counts of engine F since the checker was made.
    pub f_stats: FStats,
    /// The rules that the current engine F query used, as the bits `F_DELTA` and `F_TYPED`.
    pub(crate) f_bits: u32,
    /// True if engine F declined a check of the current declaration because engine R is the better engine for its term (`term_large`). Then the queries of the declaration use engine R only.
    pub(crate) f_declined: bool,
    /// True while a delta step of the conversion of engine F evaluates an unfolding. Then `eval` reduces the structure of a projection without delta, as `whnf_core` with cheap projections in the official kernel. `force` sets it to false for its own steps.
    pub(crate) cheap_proj: bool,
    /// The number of open definitional equality queries. Engine F answers only a query that is not inside another query.
    pub(crate) eq_depth: u32,
    /// `rulean explain`: write the rules that the checker applies into `trace`.
    pub trace_on: bool,
    /// The rule trace, when `trace_on` is true.
    pub trace: Trace,
    /// Count the unfolds of the kernel diagnostics into `diag` (spec 09.6.4).
    pub diag_on: bool,
    /// The kernel diagnostics, when `diag_on` is true: each unfolded constant and its number of unfolds, in the order of the first unfold. The C++ kernel records an unfold when it unfolds a definition or a theorem (`unfold_definition_core`), and when a recursor or a quotient constant steps (`whnf_core`). The checker counts at the same steps. Use `clear_diag` to start again.
    pub diag: Vec<(NameId, u64)>,
    /// The index in `diag` of each constant, plus 1, at key (name, 0).
    pub(crate) diag_at: Memo,
    /// The level parameters of the declaration (`m_lparams`). They are checked only if `check_lparams` is true.
    pub(crate) lparams: Vec<NameId>,
    pub(crate) check_lparams: bool,
    /// The second key of a check-mode `infer` entry of the session: 1 plus the level list of the level parameters of the declaration (spec perf/11.15).
    pub(crate) lp_key: Raw,
    /// True if a local of the declaration has a value. Then the session takes no key with free variables (spec perf/11.16).
    pub(crate) lctx_let: bool,
    /// The last pair that `quick_is_def_eq` found alpha-equal or in a success cache. `is_def_eq` does not put this pair in the caches (spec perf/11.18).
    pub(crate) known_pair: (ExprId, ExprId),
    /// The safety of the declaration (`m_definition_safety`).
    pub(crate) safety: Safety,
    // The local context, indexed by the level of the free variable.
    pub(crate) lctx_name: Vec<NameId>,
    pub(crate) lctx_info: Vec<BinderInfo>,
    pub(crate) lctx_ty: Vec<ExprId>,
    /// The free variable term of each level, `mk_fvar(level, lctx_ty[level])`. The read-back of a free variable uses it, so it does not intern the term again.
    pub(crate) lctx_fv: Vec<ExprId>,
    pub(crate) lctx_val: Vec<Option<ExprId>>,
    /// The levels of the free variables in scope, in the order of `mk_local`. The C++ kernel removes the local declarations of a binder when `infer_lambda`, `infer_pi`, `infer_let` and `is_def_eq_binding` return (`flet<local_ctx>`). The checker keeps all the free variables, because the caches can refer to them, but it removes their levels from this list. After a fault, the list does not change, so it has the scope of the fault.
    pub(crate) scope: Vec<u32>,
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
    /// Engine F: the result of `force` of a value at key (value, 0), of `force_core` at key (value, 1), and of `proj_unfold` at key (value, 2). The bits of `f_bits` that these steps set are in the high bits of the same entry. It is cleared together with the arena.
    pub(crate) c_force: Memo,
    /// Engine F: the hash-consed nodes of the value keys (spec 04.12). A node (a, b) has the key at its entry. It is cleared together with the arena, and a release of a region does not change it, because a key does not contain a value handle.
    pub(crate) k_nodes: Intern,
    /// Engine F: the unfolding of a glued value at key (value key, 0), with the bits of `f_bits` that its evaluation set in the high bits of the entry (spec 04.12). It holds value handles, so it is truncated together with `c_force`.
    pub(crate) c_unfold_key: Memo,
    /// Engine F: `const_never_proof` of a constant at key (constant, 0), and `const_never_proof_at` with the levels `us` at key (constant, `us` + 1). The value is 1 for true and 2 for false.
    pub(crate) c_never_proof: Memo,
    /// `instantiate_lparams` of a term of a constant at key (term, levels), where the parameters are the level parameters of the constant (spec 04.8). The iota rule of a recursor and the type of a constant get the same levels many times in one declaration. The table `c_lps_owner` has the slot of the constant at key (term, 0), and a term that two constants share does not use the cache for the second one, because the parameters of the two constants can be different.
    pub(crate) c_lps: Memo,
    /// The slot of the constant of each term in `c_lps`.
    pub(crate) c_lps_owner: Memo,
    /// The keys of `c_infer`, `c_whnf_core` and `c_whnf`. The C++ kernel keys these caches with `is_equal`, so terms that are equal up to binder names and binder info share one entry. Key (term, 0) is the first equal term that the checker saw (`canon`). Key (hash, 2) is the last term of the chain of terms with this hash, and key (term, 1) is the next term of the chain.
    pub(crate) c_canon: Memo,
    /// The closed terms on which engine G bailed in this declaration.
    pub(crate) c_ground_fail: Memo,
    /// The pairs of closed terms of `ground_cmp` in this declaration: 1 if they are not equal, 2 if there is no result.
    pub(crate) c_ground_cmp: Memo,
    /// Above zero while engine R works on a query in which `ground_cmp` compared data and found no difference. The sub-queries of such a query are parts of the same data, so `ground_cmp` does not run on them, and the time stays linear in the size of the data.
    pub(crate) gcmp_block: u32,
    /// The state of engine G (spec perf/10).
    pub(crate) gm: crate::ground::Ground,
    /// The session: judgments on frozen closed terms that stay across declarations (spec 08.4).
    pub sess: Session,
    /// `m_eager_reduce`.
    pub(crate) eager: bool,
    pub(crate) depth: u32,
    pub max_depth: u32,
    /// The upper bound in bytes of a `Nat` literal (`g_nat_max_size`). The default is `NAT_MAX_BYTES`. Only the in-process kernel changes it, to the value of `LEAN_NAT_MAX_SIZE` (spec 09.6).
    pub nat_max: u64,
    // The memory budget in bytes (`--max-memory`). `usize::MAX` is no budget.
    pub(crate) max_memory: usize,
    // The calls of `enter`. Each `MEMORY_TICKS` calls, `enter` compares the memory with the budget.
    pub(crate) ticks: u32,
    /// The calls of `enter` since the checker was made. This is the work count of the report (spec 08.7.4). It does not depend on the machine, so a gate can compare it with a fixed baseline.
    pub steps: u64,
    /// The heartbeat limit of a declaration (spec 09.6.4). 0 is no limit, and this is the default.
    pub max_heartbeat: u64,
    /// The heartbeats since the start of the declaration. The C++ kernel counts one heartbeat for each call of `infer_type_core`, `whnf_core` and `is_def_eq_core` (`check_system`), and the checker counts one at the same functions.
    pub(crate) heartbeats: u64,
    /// The `maxRecDepth` of a declaration (spec 09.6.4). The C++ kernel stops with `deepRecursion` if the depth of `infer_type_core`, `whnf_core` and `is_def_eq_core` is above `REC_DEPTH_FACTOR` times this value. 0 is no limit, and this is the default.
    pub max_rec_depth: u64,
    /// The depth of `infer_type_core`, `whnf_core` and `is_def_eq_core` (`scope_rec_depth` of the C++ kernel). `depth` also counts the other recursive functions of the checker.
    pub(crate) rec_depth: u64,
    /// The memory of the other checkers of the run in bytes, as the driver last saw it. With `--threads`, the checkers share one budget, and the driver sets this value before each job. The core has no shared state, so the driver keeps the total.
    pub mem_others: usize,
    /// The memory of this checker that the driver last added to the total of the run.
    pub mem_published: usize,
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
    /// The input is a `Declaration` of the Lean API, as in the in-process mode (spec 09.6), and not a stream of constants. An inductive declaration then gives only the types and the constructors, so `add_inductive` does not compare the block with an export. A quotient declaration gives no constants, so `add_quot` adds the four reference constants once and does nothing after that, as `environment::add_quot` does.
    pub kernel_api: bool,
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
            vstk: Vec::new(),
            estk: Vec::new(),
            vpool: Vec::new(),
            lpool: Vec::new(),
            pmap: None,
            pstack: Vec::new(),
            fi: FInfer::new(),
            f_under: 0,
            c_quote: Lossy::new(),
            q_depth: 0,
            engine: Engine::R,
            confirm_all: false,
            f_stats: FStats::default(),
            f_bits: 0,
            f_declined: false,
            cheap_proj: false,
            eq_depth: 0,
            trace_on: false,
            trace: Trace::new(),
            diag_on: false,
            diag: Vec::new(),
            diag_at: Memo::new(),
            lparams: Vec::new(),
            check_lparams: false,
            lp_key: 0,
            lctx_let: false,
            known_pair: (ExprId(0), ExprId(0)),
            safety: Safety::Safe,
            lctx_name: Vec::new(),
            lctx_info: Vec::new(),
            lctx_ty: Vec::new(),
            lctx_fv: Vec::new(),
            lctx_val: Vec::new(),
            scope: Vec::new(),
            c_infer: Memo::new(),
            c_canon: Memo::new(),
            c_ground_fail: Memo::new(),
            c_ground_cmp: Memo::new(),
            gcmp_block: 0,
            gm: crate::ground::Ground::default(),
            c_whnf_core: Memo::new(),
            c_whnf: Memo::new(),
            c_unfold: Memo::new(),
            c_success: Memo::new(),
            c_failure: Memo::new(),
            c_conv_failure: Memo::new(),
            c_conv_success: Memo::new(),
            c_force: Memo::new(),
            k_nodes: Intern::new(),
            c_unfold_key: Memo::new(),
            c_never_proof: Memo::new(),
            c_lps: Memo::new(),
            c_lps_owner: Memo::new(),
            sess: Session::default(),
            eager: false,
            depth: 0,
            max_depth: MAX_DEPTH,
            nat_max: NAT_MAX_BYTES,
            max_memory: usize::MAX,
            ticks: 0,
            steps: 0,
            max_heartbeat: 0,
            heartbeats: 0,
            max_rec_depth: 0,
            rec_depth: 0,
            mem_others: 0,
            mem_published: 0,
            fault: None,
            pin_off: 0,
            pin_done: 0,
            pin_mismatch: Vec::new(),
            trust_primitives: false,
            flags: Profile::V4_35.flags(),
            kernel_api: false,
            dummy,
        }
    }

    /// Starts a declaration: clears the caches, the local context and the fault, and sets the level parameters and the safety (`type_checker(env, lctx, safety)`).
    pub fn begin(&mut self, lparams: Vec<NameId>, safety: Safety) {
        let mut ls = Vec::with_capacity(lparams.len());
        let mut i = 0;
        while i < lparams.len() {
            ls.push(self.st.level_param(lparams[i]));
            i += 1;
        }
        self.lp_key = raw(self.st.level_list(&ls).0) + 1;
        self.lparams = lparams;
        self.check_lparams = true;
        self.safety = safety;
        self.lctx_name.truncate(0);
        self.lctx_info.truncate(0);
        self.lctx_ty.truncate(0);
        self.lctx_fv.truncate(0);
        self.lctx_val.truncate(0);
        self.lctx_let = false;
        self.scope.truncate(0);
        self.clear_caches();
        self.va.reset();
        self.k_nodes.clear();
        self.fi.reset();
        self.f_under = 0;
        self.f_bits = 0;
        self.f_declined = false;
        self.eq_depth = 0;
        self.eager = false;
        self.depth = 0;
        self.gcmp_block = 0;
        self.rec_depth = 0;
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
        self.c_unfold_key.clear();
        self.c_never_proof.clear();
        self.c_lps.clear();
        self.c_lps_owner.clear();
        self.c_canon.clear();
        self.c_ground_fail.clear();
        self.c_ground_cmp.clear();
        self.gm.clear();
    }

    /// Removes the counts of the kernel diagnostics.
    pub fn clear_diag(&mut self) {
        self.diag.clear();
        self.diag_at.clear();
    }

    /// The number of unfolds of the constant `n` in the kernel diagnostics.
    pub fn diag_count(&self, n: NameId) -> u64 {
        match self.diag_at.get(raw(n.0), 0) {
            Some(i) => self.diag[low(i) as usize - 1].1,
            None => 0,
        }
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
        let d = self.dummy;
        self.fail_with(kind, at, d, d)
    }

    /// Records the fault `kind` at `at` with the two types of the error (`Fault::ty1` and `Fault::ty2`), if there is no fault yet. It gives the dummy term.
    pub(crate) fn fail_with(
        &mut self,
        kind: ErrorKind,
        at: ExprId,
        ty1: ExprId,
        ty2: ExprId,
    ) -> ExprId {
        if self.fault.is_none() {
            self.fault = Some(Fault { kind, at, ty1, ty2 });
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
        self.steps += 1;
        if self.max_memory != usize::MAX {
            self.ticks = self.ticks.wrapping_add(1);
            if (self.ticks.is_multiple_of(MEMORY_TICKS) || self.st.is_full()) && self.over_memory()
            {
                self.fail(ErrorKind::MemoryLimit, at);
                return false;
            }
        }
        self.depth += 1;
        true
    }

    /// Sets the memory budget in bytes (`--max-memory`, spec 12.3). The store gets the same budget, so it stops to grow at the budget. `usize::MAX` is no budget, and this is the default.
    pub fn set_max_memory(&mut self, bytes: usize) {
        self.max_memory = bytes;
        self.st.set_max_bytes(bytes);
    }

    /// The memory budget in bytes. `usize::MAX` is no budget.
    pub fn max_memory(&self) -> usize {
        self.max_memory
    }

    /// The number of bytes that the store, the environment, the local context, the caches, the value arena and the session use, without the allocator overhead. This is the measure of `--max-memory`.
    pub fn memory(&self) -> usize {
        let lctx = self.lctx_name.capacity() * core::mem::size_of::<NameId>()
            + self.lctx_info.capacity() * core::mem::size_of::<BinderInfo>()
            + self.lctx_ty.capacity() * core::mem::size_of::<ExprId>()
            + self.lctx_fv.capacity() * core::mem::size_of::<ExprId>()
            + self.lctx_val.capacity() * core::mem::size_of::<Option<ExprId>>();
        let memos = self.c_infer.bytes()
            + self.c_whnf_core.bytes()
            + self.c_whnf.bytes()
            + self.c_unfold.bytes()
            + self.c_success.bytes()
            + self.c_failure.bytes()
            + self.c_conv_failure.bytes()
            + self.c_conv_success.bytes()
            + self.c_force.bytes()
            + self.c_never_proof.bytes()
            + self.c_lps.bytes()
            + self.c_lps_owner.bytes()
            + self.c_canon.bytes()
            + self.c_ground_fail.bytes()
            + self.c_ground_cmp.bytes()
            + self.gm.bytes();
        self.st.memory().total()
            + self.env.bytes()
            + lctx
            + memos
            + self.va.bytes()
            + self.sess.bytes()
            + self.lparams.capacity() * core::mem::size_of::<NameId>()
    }

    /// True if the checker has a budget and the store is full, or the memory of this checker and of the other checkers (`mem_others`) is above the budget.
    pub fn over_memory(&self) -> bool {
        self.max_memory != usize::MAX
            && (self.st.is_full()
                || self.memory().saturating_add(self.mem_others) > self.max_memory)
    }

    /// `enter`, then one level of `scope_rec_depth` and one heartbeat (`check_system` of the C++ kernel). It gives false and records a fault if the depth is above the limit of `max_rec_depth`, or if the heartbeats are above `max_heartbeat`. The caller calls `leave_beat` at the end.
    pub(crate) fn enter_beat(&mut self, at: ExprId) -> bool {
        if !self.enter(at) {
            return false;
        }
        if self.max_rec_depth != 0
            && self.rec_depth >= self.max_rec_depth.saturating_mul(REC_DEPTH_FACTOR)
        {
            self.leave();
            self.fail(ErrorKind::DeepRecursion, at);
            return false;
        }
        self.rec_depth += 1;
        self.heartbeats = self.heartbeats.saturating_add(1);
        if self.max_heartbeat != 0 && self.heartbeats > self.max_heartbeat {
            self.leave_beat();
            self.fail(ErrorKind::Heartbeat, at);
            return false;
        }
        if self.env.missed() {
            self.leave_beat();
            self.fail(ErrorKind::Missed, at);
            return false;
        }
        true
    }

    /// The end of a call level of `enter_beat`.
    pub(crate) fn leave_beat(&mut self) {
        self.rec_depth = self.rec_depth.saturating_sub(1);
        self.leave();
    }

    /// The heartbeats since the start of the declaration, or since `reset_heartbeats`.
    pub fn heartbeats(&self) -> u64 {
        self.heartbeats
    }

    /// Sets the heartbeats to 0. `add_decl` does this at the start of each declaration.
    pub fn reset_heartbeats(&mut self) {
        self.heartbeats = 0;
    }

    pub(crate) fn leave(&mut self) {
        if self.depth > 0 {
            self.depth -= 1;
        }
    }

    // The local context.

    /// Adds a local declaration and returns its free variable (`mk_local_decl`). The free variable has the level of the declaration in the local context, so the declaration `i` after `begin` has the level `i`.
    pub fn mk_local(
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
        if val.is_some() {
            self.lctx_let = true;
        }
        self.lctx_val.push(val);
        if !self.bad() {
            self.scope.push(lvl);
        }
        let fv = self.st.mk_fvar(lvl, ty);
        self.lctx_fv.push(fv);
        fv
    }

    /// The length of the scope list. Give it to `leave_scope` when the binders of the caller go out of scope.
    pub(crate) fn enter_scope(&self) -> usize {
        self.scope.len()
    }

    /// Removes the free variables after `mark` from the scope list, if there is no fault.
    pub(crate) fn leave_scope(&mut self, mark: usize) {
        if !self.bad() {
            self.scope.truncate(mark);
        }
    }

    /// The levels of the free variables in scope. After a fault, these are the free variables in scope at the fault, as in the local context of a C++ kernel exception.
    pub fn scope(&self) -> &[u32] {
        &self.scope
    }

    /// The dummy term. A fault has it for a term that it does not keep.
    pub fn dummy(&self) -> ExprId {
        self.dummy
    }

    /// The number of free variables of the local context. The context keeps its free variables until the next declaration or term call.
    pub fn local_count(&self) -> usize {
        self.lctx_ty.len()
    }

    /// The free variable of the level `i`: its user name, its binder info, its type and its value. `i` is less than `local_count`.
    pub fn local(&self, i: usize) -> (NameId, BinderInfo, ExprId, Option<ExprId>) {
        (
            self.lctx_name[i],
            self.lctx_info[i],
            self.lctx_ty[i],
            self.lctx_val[i],
        )
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

    /// The cache key of a term: the first term that the checker saw that is equal to it up to binder names and binder info (`expr_map` with `is_equal`).
    pub(crate) fn canon(&mut self, e: ExprId) -> ExprId {
        // A term without a binder is its own key (spec perf/11.17).
        if !expr::has_binder(&self.st, e) {
            return e;
        }
        if let Some(c) = self.c_canon.get(e.0, 0) {
            return ExprId(c);
        }
        let h = raw(self.st.hash(e));
        let head = self.c_canon.get(h, 2);
        let mut at = head;
        let mut found = e;
        while let Some(c) = at {
            if expr::expr_equal(&self.st, &mut self.x, ExprId(c), e) {
                found = ExprId(c);
                at = None;
            } else {
                at = self.c_canon.get(c, 1);
            }
        }
        if found == e {
            if let Some(c) = head {
                self.c_canon.put(e.0, 1, c);
            }
            self.c_canon.put(h, 2, e.0);
        }
        self.c_canon.put(e.0, 0, found.0);
        found
    }

    /// The alpha-equality of the official kernel (`operator==` on `expr`).
    pub(crate) fn eq(&mut self, a: ExprId, b: ExprId) -> bool {
        expr::expr_equal(&self.st, &mut self.x, a, b)
    }

    pub(crate) fn instantiate1(&mut self, e: ExprId, v: ExprId) -> ExprId {
        expr::instantiate1(&mut self.st, &mut self.x, e, v)
    }

    /// An empty vector of terms from `vpool`, or a new vector if the pool is empty.
    pub(crate) fn take_vec(&mut self) -> Vec<ExprId> {
        self.vpool.pop().unwrap_or_default()
    }

    /// Gives a vector of terms back to `vpool`. The pool keeps at most `POOL_MAX` vectors.
    pub(crate) fn give_vec(&mut self, mut v: Vec<ExprId>) {
        v.truncate(0);
        if self.vpool.len() < POOL_MAX {
            self.vpool.push(v);
        }
    }

    /// The items of the level list `l` in a vector from `lpool`. The caller gives the vector back with `give_levels`.
    pub(crate) fn take_levels(&mut self, l: LevelListId) -> Vec<LevelId> {
        let mut v = self.lpool.pop().unwrap_or_default();
        self.st.level_list_into(l, &mut v);
        v
    }

    /// Gives a vector of levels back to `lpool`.
    pub(crate) fn give_levels(&mut self, mut v: Vec<LevelId>) {
        v.truncate(0);
        if self.lpool.len() < POOL_MAX {
            self.lpool.push(v);
        }
    }

    pub(crate) fn instantiate_rev(&mut self, e: ExprId, subst: &[ExprId]) -> ExprId {
        expr::instantiate_rev(&mut self.st, &mut self.x, e, subst)
    }

    /// The type of the constant of the slot with the levels for its parameters (`instantiate_type_lparams`).
    pub(crate) fn instantiate_type_lparams(&mut self, slot: u32, ls: &[LevelId]) -> ExprId {
        let c = self.env.at(slot);
        let ty = c.ty;
        expr::instantiate_lparams(&mut self.st, &mut self.x, ty, &c.lparams, ls)
    }

    /// `instantiate_lparams` of the term `e` of the constant of the slot with the levels `us`, through the cache `c_lps`. The caller makes sure that `us` has one level for each level parameter of the constant.
    pub(crate) fn inst_lps_cached(&mut self, slot: u32, e: ExprId, us: LevelListId) -> ExprId {
        let own = self.c_lps_owner.get(e.0, 0);
        let mine = match own {
            Some(o) => o == raw(slot),
            None => {
                self.c_lps_owner.put(e.0, 0, raw(slot));
                true
            }
        };
        if mine {
            if let Some(r) = self.c_lps.get(e.0, raw(us.0)) {
                return ExprId(r);
            }
        }
        let ls = self.take_levels(us);
        let c = self.env.at(slot);
        let r = expr::instantiate_lparams(&mut self.st, &mut self.x, e, &c.lparams, &ls);
        self.give_levels(ls);
        if mine {
            self.c_lps.put(e.0, raw(us.0), r.0);
        }
        r
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
        if bytes > self.nat_max {
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
    pub(crate) fn infer_constant(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        let (n, list) = match self.st.node(e) {
            Expr::Const(n, list) => (n, list),
            _ => return self.fail(ErrorKind::BadConst, e),
        };
        let slot = self.get_const(n, e);
        if slot == 0 {
            return self.dummy;
        }
        // The count of the levels is read in place, so the inference of a constant makes no allocation (spec perf/04.3 A9).
        let nls = self.st.level_list_items(list).len();
        let c = self.env.at(slot);
        if c.lparams.len() != nls {
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
            while i < nls {
                let l = self.st.level_list_items(list)[i];
                self.check_level(l, e);
                i += 1;
            }
            if self.bad() {
                return self.dummy;
            }
        }
        let ty = self.env.at(slot).ty;
        self.inst_lps_cached(slot, ty, list)
    }

    /// `infer_lambda`.
    fn infer_lambda(&mut self, e0: ExprId, infer_only: bool) -> ExprId {
        let mark = self.enter_scope();
        let mut fvars = self.take_vec();
        let mut doms = self.take_vec();
        let r = self.infer_lambda_in(e0, infer_only, &mut fvars, &mut doms);
        self.give_vec(fvars);
        self.give_vec(doms);
        self.leave_scope(mark);
        r
    }

    /// The body of `infer_lambda`. The free variables that it makes stay in scope. `doms` gets the domain of each binder as it is in `e0`.
    fn infer_lambda_in(
        &mut self,
        e0: ExprId,
        infer_only: bool,
        fvars: &mut Vec<ExprId>,
        doms: &mut Vec<ExprId>,
    ) -> ExprId {
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Lam(b) => {
                    let d = self.instantiate_rev(b.dom, fvars);
                    if !infer_only {
                        let t = self.infer_type_core(d, infer_only);
                        self.ensure_sort_core(t, d);
                    }
                    let fv = self.mk_local(b.name, b.info, d, None);
                    fvars.push(fv);
                    doms.push(b.dom);
                    e = b.body;
                }
                _ => walking = false,
            }
        }
        if self.bad() {
            return self.dummy;
        }
        let body = self.instantiate_rev(e, fvars);
        let r = self.infer_type_core(body, infer_only);
        if self.bad() {
            return self.dummy;
        }
        let r = expr::cheap_beta_reduce(&mut self.st, r);
        self.mk_pi_doms(fvars, doms, r)
    }

    /// `mk_binding(fvars, r)` for a pi type, where `doms[i]` is the type of `fvars[i]` with `fvars[..i]` abstracted. `e0` of `infer_lambda` has no loose bound variable, so its domain at the depth `i` is this term, and the abstraction of the types of the free variables is not necessary (spec perf/12.8).
    fn mk_pi_doms(&mut self, fvars: &[ExprId], doms: &[ExprId], b: ExprId) -> ExprId {
        let mut r = expr::abstract_fvars(&mut self.st, &mut self.x, b, fvars);
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            let lvl = match self.st.node(fvars[i]) {
                Expr::FVar(l, _) => l as usize,
                _ => 0,
            };
            r = self
                .st
                .mk_pi(self.lctx_name[lvl], self.lctx_info[lvl], doms[i], r);
        }
        r
    }

    /// `infer_pi`.
    fn infer_pi(&mut self, e0: ExprId, infer_only: bool) -> ExprId {
        let mark = self.enter_scope();
        let mut fvars = self.take_vec();
        let mut us = self.take_levels(self.st.level_list_empty());
        let r = self.infer_pi_in(e0, infer_only, &mut fvars, &mut us);
        self.give_vec(fvars);
        self.give_levels(us);
        self.leave_scope(mark);
        r
    }

    /// The body of `infer_pi`. The free variables that it makes stay in scope.
    fn infer_pi_in(
        &mut self,
        e0: ExprId,
        infer_only: bool,
        fvars: &mut Vec<ExprId>,
        us: &mut Vec<LevelId>,
    ) -> ExprId {
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Pi(b) => {
                    let d = self.instantiate_rev(b.dom, fvars);
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
        let body = self.instantiate_rev(e, fvars);
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
    pub(crate) fn is_eager_reduce(&self, e: ExprId) -> bool {
        let f = expr::app_fn(&self.st, e);
        self.pin_on(pin::PIN_EAGER)
            && self.is_constant_named(f, self.b.eager_reduce)
            && expr::app_num_args(&self.st, e) == 2
    }

    /// `infer_app`.
    fn infer_app(&mut self, e: ExprId, infer_only: bool) -> ExprId {
        if infer_only {
            self.infer_app_only(e)
        } else {
            self.infer_app_check(e)
        }
    }

    /// The check branch of `infer_app`. It does the checks of the C++ kernel for each argument in the same order, but it infers the type of the head one time and does not infer the type of each partial application. The pi type of the head is instantiated in chunks, as in `infer_app_only`, and the domain of each binder is instantiated with the arguments before it. Thus the body of the pi type is not instantiated again for each argument.
    fn infer_app_check(&mut self, e: ExprId) -> ExprId {
        let mut nodes = self.take_vec();
        let mut f = e;
        let mut walking = true;
        while walking {
            match self.st.node(f) {
                Expr::App(g, _) => {
                    nodes.push(f);
                    f = g;
                }
                _ => walking = false,
            }
        }
        let mut args = self.take_vec();
        let f = expr::app_args(&self.st, e, &mut args);
        let mut f_type = self.infer_type_core(f, false);
        let n = args.len();
        let mut j = 0;
        let mut i = 0;
        while i < n && !self.bad() {
            let (t, k) = self.app_check_step(nodes[n - 1 - i], f_type, &args, j, i);
            f_type = t;
            j = k;
            i += 1;
        }
        let r = if self.bad() {
            self.dummy
        } else {
            self.instantiate_rev(f_type, &args[j..n])
        };
        self.give_vec(nodes);
        self.give_vec(args);
        r
    }

    /// One step of `infer_app_check` for the argument `i`, at the application node `e`. `f_type` is a pi type or a term whose loose bound variables are the arguments `j..i`. It gives the body of the pi type and the new start of the chunk.
    fn app_check_step(
        &mut self,
        e: ExprId,
        f_type: ExprId,
        args: &[ExprId],
        j: usize,
        i: usize,
    ) -> (ExprId, usize) {
        let (pi, j) = if self.is_pi(f_type) {
            (f_type, j)
        } else {
            let t = self.instantiate_rev(f_type, &args[j..i]);
            (self.ensure_pi_core(t, e), i)
        };
        let a = args[i];
        let a_type = self.infer_type_core(a, false);
        if self.bad() {
            return (self.dummy, j);
        }
        let (dom, body) = self.binding(pi);
        let d_type = self.instantiate_rev(dom, &args[j..i]);
        let saved = self.eager;
        if self.is_eager_reduce(a) {
            self.eager = true;
        }
        let ok = self.is_def_eq(a_type, d_type);
        self.eager = saved;
        if self.bad() {
            return (self.dummy, j);
        }
        if !ok {
            let ft = self.instantiate_rev(pi, &args[j..i]);
            self.fail_with(ErrorKind::AppTypeMismatch, e, ft, a_type);
        }
        (body, j)
    }

    /// The infer-only branch of `infer_app`. It instantiates the arguments in chunks.
    fn infer_app_only(&mut self, e: ExprId) -> ExprId {
        let mut args = self.take_vec();
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
        let r = if self.bad() {
            self.dummy
        } else {
            self.instantiate_rev(f_type, &args[j..nargs])
        };
        self.give_vec(args);
        r
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
        let mark = self.enter_scope();
        let mut fvars = self.take_vec();
        let r = self.infer_let_in(e0, infer_only, &mut fvars);
        self.give_vec(fvars);
        self.leave_scope(mark);
        r
    }

    /// The body of `infer_let`. The free variables that it makes stay in scope.
    fn infer_let_in(&mut self, e0: ExprId, infer_only: bool, fvars: &mut Vec<ExprId>) -> ExprId {
        let mut e = e0;
        let mut walking = true;
        while walking && !self.bad() {
            match self.st.node(e) {
                Expr::Let(l) => {
                    let ty = self.instantiate_rev(l.ty, fvars);
                    let val = self.instantiate_rev(l.value, fvars);
                    if !infer_only {
                        let t = self.infer_type_core(ty, infer_only);
                        self.ensure_sort_core(t, ty);
                        let vt = self.infer_type_core(val, infer_only);
                        if !self.bad() && !self.is_def_eq(vt, ty) && !self.bad() {
                            self.fail_with(ErrorKind::DefTypeMismatch, e, vt, ty);
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
        let body = self.instantiate_rev(e, fvars);
        let r = self.infer_type_core(body, infer_only);
        if self.bad() {
            return self.dummy;
        }
        let r = expr::cheap_beta_reduce(&mut self.st, r);
        self.mk_binding(fvars, r, false, true)
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
        let i_fn = expr::app_fn(&self.st, ty);
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
        if nctors != 1 || expr::app_num_args(&self.st, ty) != (nparams + nindices) as usize {
            return self.fail(ErrorKind::InvalidProj, e);
        }
        let c_slot = self.get_const(ctor, e);
        if c_slot == 0 {
            return self.dummy;
        }
        // The levels and the arguments go in vectors from the pools, so the check makes no new vector (spec perf/04.3 A9).
        let ls = self.take_levels(i_levels);
        let mut r = self.instantiate_type_lparams(c_slot, &ls);
        self.give_levels(ls);
        let mut args = self.take_vec();
        expr::app_args(&self.st, ty, &mut args);
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
        self.give_vec(args);
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
    pub(crate) fn infer_lit(&mut self, e: ExprId, l: Literal) -> ExprId {
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
        if !self.enter_beat(e) {
            return self.dummy;
        }
        let mode = infer_only as u32;
        let k = self.canon(e);
        let r = match self.c_infer.get(k.0, raw(mode)) {
            Some(r) => ExprId(r),
            None => {
                // A check-mode result also depends on the level parameters and the safety of the declaration. So it goes into the session only for a term with no level parameter in a safe declaration, and a safe declaration can use fewer constants than the other kinds.
                let tag = if infer_only { S_INFER } else { S_CHECK };
                let kb = if infer_only {
                    0
                } else if self.st.flags(e).has(rulean_store::Flags::HAS_LEVEL_PARAM) {
                    self.lp_key
                } else {
                    0
                };
                let key = self.sess_key_local(e)
                    && (infer_only
                        || (self.safety == Safety::Safe && (kb == 0 || self.check_lparams)));
                let hit = if key && e.tier() == Tier::Frozen {
                    self.sess_get(tag, e.0, kb)
                } else {
                    None
                };
                match hit {
                    Some(r) => {
                        self.c_infer.put(k.0, raw(mode), r);
                        ExprId(r)
                    }
                    None => {
                        let r = self.infer_type_node(e, infer_only);
                        if !self.bad() {
                            self.c_infer.put(k.0, raw(mode), r.0);
                            if key {
                                self.sess.note(tag, e.0, kb, r.0);
                            }
                        }
                        r
                    }
                }
            }
        };
        self.leave_beat();
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

    /// `is_prop`: the type of `e` is a sort whose level normalizes to zero. As in the C++ kernel, the term of `typeExpected` is the type of `e`, not `e`.
    pub fn is_prop(&mut self, e: ExprId) -> bool {
        let t = self.infer(e);
        let s = self.ensure_sort(t, t);
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
