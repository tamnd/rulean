//! Engine G: a call-by-need machine for closed terms (spec perf/10).
//!
//! Engine G evaluates a closed term to a `Bool` or a `Nat` value. It is a Krivine machine with update frames: an argument is a thunk, the first read of a thunk evaluates it, and the value replaces the thunk. The machine has an explicit stack of arguments and an explicit stack of frames, so it does not recurse.
//!
//! The machine reads the terms of the store directly. It does not substitute, so it makes no new terms. A definition unfolds to its value without the substitution of its level parameters, because a closed computation that gives a `Bool` or a `Nat` value does not depend on the levels: no rule of reduction reads a level.
//!
//! Each step of the machine is a step of the official kernel: beta, zeta, delta, iota, projection, the quotient rules and the `Nat` extension. The machine stops with no result ("bail") when the next step needs more than the term: a K-like recursor, a major premise that can be a proof when `no_whnf_prop_major` is on, a string literal, an axiom or an opaque constant, a free variable, a `Nat` result above the size bound, or a budget. Then engine R does the work as before. A result is a constructor or a literal, and two different ones are not definitionally equal, so a result answers the query.

use alloc::vec::Vec;
use rulean_nat::Nat;
use rulean_store::ids::{Tier, low, raw};
use rulean_store::{Expr, ExprId, Literal, NameId, NatId, Raw};

use crate::env::ConstKind;
use crate::expr;
use crate::memo::Memo;
use crate::nbe::{SmallOut, small_op};
use crate::tc::{Checker, NAT_POW, NAT_SHL};
use crate::value::{EnvId, Head, SMALL_NAT_LIMIT, Value, ValueId, small_get};
use crate::whnf::find_rule;

/// The empty environment.
const NIL: u32 = u32::MAX;
/// No term.
const NIL_E: ExprId = ExprId(Raw::MAX);
/// The nodes that `g_inline` reads at most for one definition, and the depth of the wrappers that it opens in one place.
const G_INL_FUEL: u32 = 512;
const G_INL_DEPTH: u32 = 4;

/// The largest number of cells, environment nodes and fields of one run.
pub const G_MAX_CELLS: usize = 1 << 25;

/// The largest number of steps of one run. A run that does not stop, as the unfold of `f := f`, stops at this bound.
pub const G_MAX_STEPS: u64 = 1 << 32;

/// The first size at which the collector runs. After a collection, the next one is at two times the live size, and at least at this size.
const G_GC_FIRST: usize = 1 << 21;

/// The largest number of words of the big numbers before a collection.
const G_GC_WORDS: usize = 1 << 24;

/// The operation index of `Nat.succ` in a frame. The binary operations use the indices of `nat_ops`.
const OP_SUCC: u32 = 100;

/// The largest number of pairs of values that one `ground_cmp` query compares.
const G_CMP_PAIRS: u32 = 1 << 22;

/// A value of engine G, in weak head normal form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GVal {
    /// A `Nat` value below `SMALL_NAT_LIMIT`.
    Small(u64),
    /// A `Nat` value of at least `SMALL_NAT_LIMIT`: the index in `nats`.
    Big(u32),
    /// A constructor application: the constructor, the index of the first field in `fields`, and the number of fields. The parameters are not kept.
    Ctor(NameId, u32, u32),
    /// A lambda: the lambda term and the environment.
    Clo(ExprId, u32),
    /// A constant with too few arguments for its rule: the constant term, the index of the first argument in `fields`, and the number of arguments.
    Pap(ExprId, u32, u32),
    /// A type: a sort, a pi type or an inductive type. No rule reads it.
    Type,
}

/// A cell of the heap.
#[derive(Clone, Copy, Debug)]
enum Slot {
    /// A term and its environment, not evaluated yet.
    Thunk(ExprId, u32),
    /// A thunk that is under evaluation, with its term and environment. A read of it is a loop, and the run bails. A bail puts the thunk back.
    Busy(ExprId, u32),
    Val(GVal),
}

/// A node of an environment: the cell of de Bruijn index 0 and the rest.
#[derive(Clone, Copy, Debug)]
struct GEnv {
    cell: u32,
    parent: u32,
}

/// What to do with the next value.
#[derive(Clone, Copy, Debug)]
enum Frame {
    /// Write the value into the cell.
    Update(u32),
    /// The value is the major premise of the recursor of the slot.
    Rec(u32),
    /// The value is the structure of the projection.
    Proj(NameId, u32),
    /// The value is the first argument of the `Nat` operation. The cell is the second argument.
    Nat1(u32, u32),
    /// The value is the second argument of the `Nat` operation. The value of the frame is the first argument.
    Nat2(u32, GVal),
    /// The value is the `Quot.mk` argument of `Quot.lift` or `Quot.ind`, at this position.
    Quot(u32),
}

/// A frame and the height of the argument stack when the frame was pushed. The arguments above the height belong to the evaluation of the frame.
#[derive(Clone, Copy, Debug)]
struct FrameAt {
    f: Frame,
    base: u32,
}

/// The next step of the machine.
#[derive(Clone, Copy, Debug)]
enum Ctl {
    Eval(ExprId, u32),
    Force(u32),
    Ret(GVal),
    Done(GVal),
    Bail,
}

/// A constant, resolved for `g_const`.
#[derive(Clone, Copy, Debug)]
enum CKind {
    Succ,
    Zero,
    /// A binary `Nat` operation, with its index in `nat_ops`.
    NatOp(u32),
    /// A definition or a theorem: the slot and the value.
    Defn(u32, ExprId),
    Type,
    /// A constructor: the name, the parameters and the fields.
    Ctor(NameId, u32, u32),
    /// A recursor that engine G can reduce: the slot and the index of the major premise.
    Rec(u32, u32),
    Quot(NameId),
    Bail,
}

/// An entry of the constant cache. `kind` is good while `epoch` is the epoch of the declaration, and `cell` is good while `hgen` is the generation of the heap.
#[derive(Clone, Copy, Debug)]
struct CEntry {
    key: ExprId,
    epoch: u32,
    hgen: u32,
    kind: CKind,
    cell: u32,
}

/// An argument of an application record: a variable (its index and its term), an open term, or a closed term.
#[derive(Clone, Copy, Debug)]
enum GArg {
    Var(u32, ExprId),
    Open(ExprId),
    Closed(ExprId),
}

/// An entry of the cache of application records: the term, the generation of `codes`, the head, and the arguments `start .. start + n` of `codes`, the last argument first.
#[derive(Clone, Copy, Debug)]
struct ARec {
    key: ExprId,
    cgen: u32,
    head: ExprId,
    start: u32,
    n: u32,
}

/// The number of argument entries in `codes` at which the records start again.
const G_MAX_CODES: usize = 1 << 20;

/// The number of entries of the direct-mapped caches.
const CACHE_BITS: u32 = 12;

fn cache_index(e: ExprId) -> usize {
    (u64::from(low(e.0)).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - CACHE_BITS)) as usize
}

/// The state of engine G. The arrays are empty between two runs.
#[derive(Debug, Default)]
pub struct Ground {
    cells: Vec<Slot>,
    envs: Vec<GEnv>,
    fields: Vec<u32>,
    nats: Vec<Nat>,
    args: Vec<u32>,
    frames: Vec<FrameAt>,
    tmp: Vec<u32>,
    /// The pairs of cells that `ground_cmp` must still compare. They are roots of the collector.
    roots: Vec<u32>,
    /// Key (slot, 0) is the cell of the value of the definition of the slot, and key (term, 1) is the cell of a closed argument. The heap stays from one run to the next in a declaration, so a definition is computed one time (a constant applicative form).
    caf: Memo,
    /// The keys and the cells of `caf`, for the collector.
    caf_keys: Vec<(Raw, Raw, u32)>,
    /// The collector runs when `size` is above this.
    gc_at: usize,
    /// The words of the big numbers in `nats`, and the number of words at which the collector runs.
    nat_words: usize,
    words_at: usize,
    /// The collections.
    pub gcs: u64,
    /// A direct-mapped cache of the constants, in front of the environment and `caf`.
    ccache: Vec<CEntry>,
    /// A direct-mapped cache of the cells of the closed arguments, in front of `caf`: the term, the generation and the cell.
    acache: Vec<(ExprId, u32, u32)>,
    /// The application records (spec perf/10, G5): the kinds of the arguments of each application, found one time. `ccells` keeps the cell of each closed argument and the generation of the heap of the cell.
    apcache: Vec<ARec>,
    codes: Vec<GArg>,
    ccells: Vec<(u32, u32)>,
    /// The generation of `codes`. A clear of `codes` starts a new one.
    cgen: u32,
    /// The epoch of the declaration, and the generation of the heap. A clear starts a new epoch and a new generation, and a collection starts a new generation.
    epoch: u32,
    hgen: u32,
    /// The runs, and the runs that gave a result.
    pub runs: u64,
    pub hits: u64,
    /// For each slot, a value that `g_inline` does not change. A clear keeps it, because a wrong entry only stops an inline step.
    plain: Vec<ExprId>,
    /// For each slot, a frozen value and its frozen result after the inline pass. A clear keeps it.
    inl_val: Vec<(ExprId, ExprId)>,
    /// True while the inline pass makes frozen terms. Then it uses only the frozen values of the wrappers.
    inl_frozen: bool,
}

/// The number of value nodes that `value_term` reads at most.
const VT_FUEL: u32 = 64;

impl Checker {
    /// A closed term with the value `v`. The value must be a suspended closed argument, a `Nat` literal, or a constant or a folded definition applied to such values. The function reads at most `VT_FUEL` nodes, so it is cheap. Engine F uses it to give a closed query to engine G.
    fn value_term(&mut self, v: ValueId, fuel: &mut u32) -> Option<ExprId> {
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        match self.va.get(v) {
            Value::Susp(env, e, slot) => {
                if env == EnvId::NIL {
                    Some(e)
                } else {
                    match self.va.slot_get(slot) {
                        Some(w) => self.value_term(w, fuel),
                        None => None,
                    }
                }
            }
            Value::Small(lo, hi) => Some(self.mk_nat(Nat::from_u64(small_get(lo, hi)))),
            Value::Lit(Literal::Nat(n)) => Some(self.st.mk_nat_lit(n)),
            Value::Glued(c, us, sp, _) | Value::Neu(Head::Const(c, us), sp) => {
                // The arguments go on the stack `vstk`, so the walk makes no vector (spec perf/04.3 A9).
                let base = self.vstk.len();
                let n = self.va.spine_push_args(sp, &mut self.vstk);
                let mut t = self.st.mk_const(c, us);
                let mut i = 0;
                let mut ok = true;
                while ok && i < n {
                    let v = self.vstk[base + i];
                    match self.value_term(v, fuel) {
                        Some(a) => t = self.st.mk_app(t, a),
                        None => ok = false,
                    }
                    i += 1;
                }
                self.vstk.truncate(base);
                if ok { Some(t) } else { None }
            }
            _ => None,
        }
    }

    /// True if the value `v` is `Bool.true`, `Bool.false`, `Nat.zero` or a `Nat` literal. The function does not evaluate `v`.
    fn value_scalar(&self, v: ValueId) -> bool {
        match self.va.get(v) {
            Value::Small(..) | Value::Lit(Literal::Nat(_)) => true,
            Value::Neu(Head::Const(c, _), sp) => {
                self.va.spine_len(sp) == 0
                    && (c == self.b.bool_true || c == self.b.bool_false || c == self.b.nat_zero)
            }
            _ => false,
        }
    }

    /// `a =?= b` with engine G, when one value is a scalar and `value_term` gives a closed term for the other value. Without this step, engine F evaluates the closed term with its own `Nat` operations, fills its arena, and engine R then does the same work again with engine G.
    pub(crate) fn conv_ground(&mut self, a: ValueId, b: ValueId) -> Option<bool> {
        if !(self.value_scalar(a) || self.value_scalar(b)) {
            return None;
        }
        let mut fuel = VT_FUEL;
        let t = match self.value_term(a, &mut fuel) {
            Some(t) => t,
            None => return None,
        };
        let s = match self.value_term(b, &mut fuel) {
            Some(s) => s,
            None => return None,
        };
        self.ground_defeq(t, s)
    }
}

impl Ground {
    /// The number of bytes of the arrays.
    pub fn bytes(&self) -> usize {
        self.cells.capacity() * core::mem::size_of::<Slot>()
            + self.envs.capacity() * core::mem::size_of::<GEnv>()
            + (self.fields.capacity()
                + self.args.capacity()
                + self.tmp.capacity()
                + self.roots.capacity())
                * 4
            + self.frames.capacity() * core::mem::size_of::<FrameAt>()
            + self.nats.capacity() * core::mem::size_of::<Nat>()
            + self.caf.bytes()
            + self.plain.capacity() * core::mem::size_of::<ExprId>()
            + self.inl_val.capacity() * 2 * core::mem::size_of::<ExprId>()
            + self.ccache.capacity() * core::mem::size_of::<CEntry>()
            + self.acache.capacity() * 12
            + self.apcache.capacity() * core::mem::size_of::<ARec>()
            + self.codes.capacity() * core::mem::size_of::<GArg>()
            + self.ccells.capacity() * 8
    }

    /// Makes the caches, the first time.
    fn caches(&mut self) {
        if self.ccache.len() == 0 {
            let n = 1usize << CACHE_BITS;
            let mut i = 0;
            while i < n {
                self.ccache.push(CEntry {
                    key: ExprId(0),
                    epoch: u32::MAX,
                    hgen: u32::MAX,
                    kind: CKind::Bail,
                    cell: 0,
                });
                self.acache.push((ExprId(0), u32::MAX, 0));
                self.apcache.push(ARec {
                    key: ExprId(0),
                    cgen: u32::MAX,
                    head: ExprId(0),
                    start: 0,
                    n: 0,
                });
                i += 1;
            }
        }
    }

    /// Empties the arrays. A large array is given back to the allocator.
    pub(crate) fn clear(&mut self) {
        self.epoch = self.epoch.wrapping_add(1) & 0x7fff_ffff;
        self.hgen = self.hgen.wrapping_add(1) & 0x7fff_ffff;
        self.caf.clear();
        // A small array keeps its memory, so the next run of the machine does no `malloc` for it (spec perf/04.3 A9).
        if self.caf_keys.capacity() > (1 << 16)
            || self.codes.capacity() > (1 << 16)
            || self.ccells.capacity() > (1 << 16)
        {
            self.caf_keys = Vec::new();
            self.codes = Vec::new();
            self.ccells = Vec::new();
        } else {
            self.caf_keys.truncate(0);
            self.codes.truncate(0);
            self.ccells.truncate(0);
        }
        self.cgen = self.cgen.wrapping_add(1) & 0x7fff_ffff;
        self.gc_at = G_GC_FIRST;
        self.nat_words = 0;
        self.words_at = G_GC_WORDS;
        if self.cells.capacity() > (1 << 20) || self.fields.capacity() > (1 << 20) {
            self.cells = Vec::new();
            self.envs = Vec::new();
            self.fields = Vec::new();
            self.args = Vec::new();
            self.frames = Vec::new();
        } else {
            self.cells.truncate(0);
            self.envs.truncate(0);
            self.fields.truncate(0);
            self.args.truncate(0);
            self.frames.truncate(0);
        }
        if self.nats.capacity() > (1 << 16) {
            self.nats = Vec::new();
        } else {
            self.nats.truncate(0);
        }
        self.tmp.truncate(0);
        self.roots.truncate(0);
    }

    fn size(&self) -> usize {
        self.cells.len() + self.envs.len() + self.fields.len() + self.args.len() + self.frames.len()
    }

    fn cell(&mut self, c: Slot) -> u32 {
        let i = self.cells.len() as u32;
        self.cells.push(c);
        i
    }

    fn env_push(&mut self, env: u32, cell: u32) -> u32 {
        let i = self.envs.len() as u32;
        self.envs.push(GEnv { cell, parent: env });
        i
    }

    fn env_get(&self, env: u32, idx: u32) -> Option<u32> {
        let mut e = env;
        let mut k = idx;
        while k > 0 && e != NIL {
            e = self.envs[e as usize].parent;
            k -= 1;
        }
        if e == NIL {
            None
        } else {
            Some(self.envs[e as usize].cell)
        }
    }

    fn base(&self) -> u32 {
        match self.frames.last() {
            Some(f) => f.base,
            None => 0,
        }
    }

    fn frame(&mut self, f: Frame) {
        let base = self.args.len() as u32;
        self.frames.push(FrameAt { f, base });
    }

    /// The number of arguments above the base of the top frame.
    fn avail(&self) -> u32 {
        self.args.len() as u32 - self.base()
    }

    /// The argument at depth `i` from the top of the stack.
    fn arg_at(&self, i: u32) -> u32 {
        self.args[self.args.len() - 1 - i as usize]
    }

    fn pop_arg(&mut self) -> u32 {
        self.args.pop().unwrap_or_default()
    }

    /// Moves `n` arguments from the stack into `fields`, the first argument first. It gives the index of the first one.
    fn pop_fields(&mut self, n: u32) -> u32 {
        let start = self.fields.len() as u32;
        let mut i = 0;
        while i < n {
            let a = self.pop_arg();
            self.fields.push(a);
            i += 1;
        }
        start
    }

    /// Removes `n` arguments from the stack.
    fn drop_args(&mut self, n: u32) {
        let len = self.args.len() - n as usize;
        self.args.truncate(len);
    }

    /// Pushes the fields `start .. start + n` on the stack, so that the first one is at the top.
    fn push_fields(&mut self, start: u32, n: u32) {
        let mut i = n;
        while i > 0 {
            i -= 1;
            let a = self.fields[(start + i) as usize];
            self.args.push(a);
        }
    }

    /// The `Nat` value of `x`.
    fn nat_val(&mut self, x: Nat) -> GVal {
        match x.to_u64() {
            Some(v) if v < SMALL_NAT_LIMIT => GVal::Small(v),
            _ => {
                let i = self.nats.len() as u32;
                self.nat_words += x.limb_count();
                self.nats.push(x);
                GVal::Big(i)
            }
        }
    }
}

impl Checker {
    /// True if engine G may run on `e`: the term is closed and compound, and no mode needs the steps of engine R (the rule trace, the kernel diagnostics, the heartbeat and depth limits, and pinning).
    fn ground_ok(&self, e: ExprId) -> bool {
        let compound = matches!(
            self.st.node(e),
            Expr::App(..) | Expr::Const(..) | Expr::Proj(_) | Expr::Let(_)
        );
        compound
            && !self.trace_on
            && !self.diag_on
            && self.max_heartbeat == 0
            && self.max_rec_depth == 0
            && self.pin_off == 0
            && !expr::has_fvar(&self.st, e)
            && !expr::has_loose_bvars(&self.st, e)
    }

    /// Engine G on `e`: the value of `e` as a term, if it is `Bool.true`, `Bool.false` or a `Nat` literal. `None` if the run bails or gives another value.
    pub(crate) fn ground_scalar(&mut self, e: ExprId) -> Option<ExprId> {
        if !self.ground_ok(e) {
            return None;
        }
        // Key (e, 0) is a bail, and key (e, 1) is the result.
        if self.c_ground_fail.get(e.0, 0).is_some() {
            return None;
        }
        if let Some(w) = self.c_ground_fail.get(e.0, 1) {
            return Some(ExprId(w));
        }
        self.gm.runs += 1;
        self.gm.caches();
        let v = self.ground_run(e);
        let r = match v {
            Some(GVal::Small(x)) => Some(self.mk_nat(Nat::from_u64(x))),
            Some(GVal::Big(i)) => {
                let x = self.gm.nats[i as usize].clone();
                Some(self.mk_nat(x))
            }
            Some(GVal::Ctor(c, _, 0)) if c == self.b.bool_true => Some(self.b.e_bool_true),
            Some(GVal::Ctor(c, _, 0)) if c == self.b.bool_false => Some(self.b.e_bool_false),
            _ => None,
        };
        // A run that bails leaves cells under evaluation. Each one is in an update frame, and it becomes a thunk again, so the other values stay for the next run. A run above the budget empties the heap.
        if v.is_none() {
            if self.gm.size() > G_MAX_CELLS {
                self.gm.clear();
            } else {
                self.gm.unwind();
            }
        }
        self.gm.args.truncate(0);
        self.gm.frames.truncate(0);
        match r {
            Some(w) => {
                self.gm.hits += 1;
                self.c_ground_fail.put(e.0, 1, w.0);
            }
            None => self.c_ground_fail.put(e.0, 0, 1),
        }
        r
    }

    /// True if `e` is `Bool.true`, `Bool.false`, `Nat.zero` or a `Nat` literal.
    fn is_scalar(&self, e: ExprId) -> bool {
        e == self.b.e_bool_true
            || e == self.b.e_bool_false
            || e == self.b.e_nat_zero
            || matches!(self.st.node(e), Expr::Lit(Literal::Nat(_)))
    }

    /// The number of a `Nat.zero` or a `Nat` literal.
    fn scalar_nat(&self, e: ExprId) -> Option<Nat> {
        if e == self.b.e_nat_zero {
            return Some(Nat::zero());
        }
        match self.st.node(e) {
            Expr::Lit(Literal::Nat(n)) => Some(self.st.nat(n).clone()),
            _ => None,
        }
    }

    /// True if the scalar `w` of engine G is the scalar `x`.
    fn scalar_eq(&self, w: ExprId, x: ExprId) -> bool {
        if w == x {
            return true;
        }
        match (self.scalar_nat(w), self.scalar_nat(x)) {
            (Some(a), Some(b)) => a.beq(&b),
            _ => false,
        }
    }

    /// `t =?= s` with engine G, when one side is a scalar and the other side is a closed term (as `eval_closed_scalar` of rpylean). Two different scalars are different constructors or different literals, so they are not definitionally equal. `None` if engine G gives no value.
    pub(crate) fn ground_defeq(&mut self, t: ExprId, s: ExprId) -> Option<bool> {
        if self.is_scalar(s) {
            if let Some(w) = self.ground_scalar(t) {
                return Some(self.scalar_eq(w, s));
            }
        } else if self.is_scalar(t)
            && let Some(w) = self.ground_scalar(s)
        {
            return Some(self.scalar_eq(w, t));
        }
        None
    }

    /// True if engine G shows that the closed terms `t` and `s` are not definitionally equal (spec perf/10). The step computes the weak head normal form of the two terms, and then the normal forms of the pairs of fields, the first field first, as far as the comparison needs them. Two different `Nat` values are not equal. Two constructor applications of an inductive type that is never a proposition are not equal if the constructors are different, and they are not equal if a pair of their fields is not equal. A pair of other values (a lambda, a type, or a value that can be a proof) does not give a result, and the step goes to the next pair. The step never gives "equal", so a false result only tells engine R to continue. The rivals compute closed data in the same way: rpylean has a closed evaluator, and nano-lean compares values that it computed one time.
    ///
    /// The result is 1 if the terms are not equal, 4 if the step compared data and found no difference, and 0 for the other cases.
    pub(crate) fn ground_cmp(&mut self, t: ExprId, s: ExprId) -> u32 {
        if t == s || self.gcmp_block > 0 || !self.ground_ok(t) || !self.ground_ok(s) {
            return 0;
        }
        if let Some(x) = self.c_ground_cmp.get(t.0, s.0) {
            return low(x);
        }
        self.gm.runs += 1;
        self.gm.caches();
        let a = self.g_arg(t, NIL);
        let b = self.g_arg(s, NIL);
        self.gm.roots.push(a);
        self.gm.roots.push(b);
        let mut ticks: u64 = 0;
        let mut pairs: u32 = 0;
        // 0: continue, 1: not equal, 2: no result, 3: all pairs read.
        let mut state: u32 = 0;
        let mut data = false;
        let mut bailed = false;
        while state == 0 {
            let n = self.gm.roots.len();
            if n < 2 {
                state = 3;
            } else if pairs >= G_CMP_PAIRS {
                state = 2;
            } else if self.gm.roots[n - 2] == self.gm.roots[n - 1] {
                // One cell is one term, so the pair is equal and the step does not compute it.
                self.gm.roots.truncate(n - 2);
            } else {
                pairs += 1;
                let x = self.gm.roots[n - 2];
                let ok = self.ground_loop(Ctl::Force(x), &mut ticks).is_some();
                let y = self.gm.roots[n - 1];
                let ok = ok && self.ground_loop(Ctl::Force(y), &mut ticks).is_some();
                if ok {
                    // The collector can move the cells, so the step reads them after the two loops.
                    let x = self.gm.cells[self.gm.roots[n - 2] as usize];
                    let y = self.gm.cells[self.gm.roots[n - 1] as usize];
                    self.gm.roots.truncate(n - 2);
                    state = match (x, y) {
                        (Slot::Val(v), Slot::Val(w)) => self.g_cmp_vals(v, w),
                        _ => 2,
                    };
                    data = data || !self.gm.roots.is_empty();
                } else {
                    bailed = true;
                    state = 2;
                }
            }
        }
        if bailed {
            if self.gm.size() > G_MAX_CELLS {
                self.gm.clear();
            } else {
                self.gm.unwind();
            }
        }
        self.gm.args.truncate(0);
        self.gm.frames.truncate(0);
        self.gm.roots.truncate(0);
        let r = if state == 1 {
            self.gm.hits += 1;
            1
        } else if state == 3 && data {
            4
        } else {
            0
        };
        self.c_ground_cmp.put(t.0, s.0, raw(r));
        r
    }

    /// One pair of values of `ground_cmp`: 1 if they are not equal, and 0 if the step continues. A pair of constructor applications with the same constructor puts the pairs of fields on `roots`, the last field first, so that the first field is the next pair.
    fn g_cmp_vals(&mut self, v: GVal, w: GVal) -> u32 {
        match (v, w) {
            (GVal::Small(x), GVal::Small(y)) => u32::from(x != y),
            (GVal::Big(i), GVal::Big(j)) => {
                u32::from(!self.gm.nats[i as usize].beq(&self.gm.nats[j as usize]))
            }
            (GVal::Small(_), GVal::Big(_)) | (GVal::Big(_), GVal::Small(_)) => 1,
            (GVal::Ctor(c, fs, nf), GVal::Ctor(d, gs, mf)) => {
                if !self.const_never_proof(c) || !self.const_never_proof(d) {
                    0
                } else if c != d {
                    1
                } else {
                    let mut i = nf.min(mf);
                    while i > 0 {
                        i -= 1;
                        let p = self.gm.fields[(fs + i) as usize];
                        let q = self.gm.fields[(gs + i) as usize];
                        self.gm.roots.push(p);
                        self.gm.roots.push(q);
                    }
                    0
                }
            }
            _ => 0,
        }
    }

    /// The loop of the machine on the term `e`.
    fn ground_run(&mut self, e: ExprId) -> Option<GVal> {
        let mut ticks: u64 = 0;
        self.ground_loop(Ctl::Eval(e, NIL), &mut ticks)
    }

    /// The loop of the machine from the control `c0`. `ticks` counts the steps of all the loops of one query, so that the budget and the collector see all of them.
    fn ground_loop(&mut self, c0: Ctl, ticks: &mut u64) -> Option<GVal> {
        let mut c = c0;
        let mut out = None;
        let mut go = true;
        let mut tk = *ticks;
        while go {
            c = match c {
                Ctl::Eval(t, env) => self.g_eval(t, env),
                Ctl::Force(s) => self.g_force(s),
                Ctl::Ret(v) => self.g_ret(v),
                Ctl::Done(v) => {
                    out = Some(v);
                    go = false;
                    Ctl::Bail
                }
                Ctl::Bail => {
                    go = false;
                    Ctl::Bail
                }
            };
            tk += 1;
            if tk.is_multiple_of(4096) {
                if self.gm.size() > self.gm.gc_at.max(G_GC_FIRST)
                    || self.gm.nat_words > self.gm.words_at.max(G_GC_WORDS)
                {
                    c = self.gm.gc(c);
                }
                if tk > G_MAX_STEPS || self.ground_over() {
                    c = Ctl::Bail;
                }
            }
        }
        *ticks = tk;
        out
    }

    /// True if the run is above its budget, or above the memory budget of the checker.
    fn ground_over(&self) -> bool {
        self.gm.size() > G_MAX_CELLS
            || (self.max_memory != usize::MAX
                && self
                    .memory()
                    .saturating_add(self.mem_others)
                    .saturating_add(self.gm.bytes())
                    > self.max_memory)
    }

    /// The cell of an argument: the cell of a variable, or a thunk. A closed argument has one thunk in the declaration, keyed by the term, so all uses of a closed term share one value. The types, the instances and the literals are closed terms in most cases.
    fn g_arg(&mut self, a: ExprId, env: u32) -> u32 {
        if let Expr::BVar(i) = self.st.node(a)
            && let Some(c) = self.gm.env_get(env, i)
        {
            return c;
        }
        if expr::has_loose_bvars(&self.st, a) {
            return self.gm.cell(Slot::Thunk(a, env));
        }
        let i = cache_index(a);
        let (k, g, c) = self.gm.acache[i];
        if k == a && g == self.gm.hgen {
            return c;
        }
        let c = match self.gm.caf.get(a.0, 1) {
            Some(c) => low(c),
            None => {
                let c = self.gm.cell(Slot::Thunk(a, NIL));
                self.gm.caf_put(a.0, 1, c);
                c
            }
        };
        self.gm.acache[i] = (a, self.gm.hgen, c);
        c
    }

    fn g_eval(&mut self, t: ExprId, env: u32) -> Ctl {
        match self.st.node(t) {
            Expr::BVar(i) => self.g_var(env, i),
            Expr::App(..) => self.g_app(t, env),
            Expr::Lam(b) => {
                if self.gm.avail() > 0 {
                    self.g_beta(b.body, env)
                } else {
                    Ctl::Ret(GVal::Clo(t, env))
                }
            }
            Expr::Let(l) => {
                let a = self.g_arg(l.value, env);
                let env2 = self.gm.env_push(env, a);
                Ctl::Eval(l.body, env2)
            }
            Expr::Lit(Literal::Nat(n)) => Ctl::Ret(self.g_lit(n)),
            Expr::Lit(Literal::Str(_)) => Ctl::Bail,
            Expr::Proj(p) => {
                self.gm.frame(Frame::Proj(p.struct_name, p.index));
                Ctl::Eval(p.expr, env)
            }
            Expr::Sort(_) | Expr::Pi(_) => Ctl::Ret(GVal::Type),
            Expr::FVar(..) => Ctl::Bail,
            Expr::Const(..) => self.g_const(t),
        }
    }

    /// The variable `i` of the environment. A cell with a value gives the value in the same step.
    fn g_var(&mut self, env: u32, i: u32) -> Ctl {
        match self.gm.env_get(env, i) {
            Some(c) => self.g_force(c),
            None => Ctl::Bail,
        }
    }

    /// The body of a lambda, with the top argument for its variable. The lambdas of the body take the next arguments in the same step, while there are arguments above the base.
    fn g_beta(&mut self, body: ExprId, env: u32) -> Ctl {
        let a = self.gm.pop_arg();
        let mut e = self.gm.env_push(env, a);
        let mut t = body;
        let mut go = true;
        while go {
            go = false;
            if self.gm.avail() > 0
                && let Expr::Lam(b) = self.st.node(t)
            {
                let a2 = self.gm.pop_arg();
                e = self.gm.env_push(e, a2);
                t = b.body;
                go = true;
            }
        }
        Ctl::Eval(t, e)
    }

    /// The record of the application `t`, from the cache or new: the head, and the start and the number of its arguments in `codes`.
    fn app_rec(&mut self, t: ExprId) -> (ExprId, u32, u32) {
        let i = cache_index(t);
        let r = self.gm.apcache[i];
        if r.key == t && r.cgen == self.gm.cgen {
            return (r.head, r.start, r.n);
        }
        if self.gm.codes.len() > G_MAX_CODES {
            self.gm.codes.truncate(0);
            self.gm.ccells.truncate(0);
            self.gm.cgen = self.gm.cgen.wrapping_add(1);
        }
        let start = self.gm.codes.len() as u32;
        let mut f = t;
        let mut go = true;
        while go {
            match self.st.node(f) {
                Expr::App(g, a) => {
                    let k = match self.st.node(a) {
                        Expr::BVar(j) => GArg::Var(j, a),
                        _ => {
                            if expr::has_loose_bvars(&self.st, a) {
                                GArg::Open(a)
                            } else {
                                GArg::Closed(a)
                            }
                        }
                    };
                    self.gm.codes.push(k);
                    self.gm.ccells.push((u32::MAX, 0));
                    f = g;
                }
                _ => go = false,
            }
        }
        let n = self.gm.codes.len() as u32 - start;
        self.gm.apcache[i] = ARec {
            key: t,
            cgen: self.gm.cgen,
            head: f,
            start,
            n,
        };
        (f, start, n)
    }

    /// An application: the arguments go on the stack, the last one first, and the head is next. The kinds of the arguments come from the record of the application. A head that is a constant or a variable is done in the same step.
    fn g_app(&mut self, t: ExprId, env: u32) -> Ctl {
        let (f, start, n) = self.app_rec(t);
        let mut j = start;
        let end = start + n;
        while j < end {
            let c = match self.gm.codes[j as usize] {
                GArg::Var(i, a) => match self.gm.env_get(env, i) {
                    Some(c) => c,
                    None => self.gm.cell(Slot::Thunk(a, env)),
                },
                GArg::Open(a) => self.gm.cell(Slot::Thunk(a, env)),
                GArg::Closed(a) => {
                    let (g, c) = self.gm.ccells[j as usize];
                    if g == self.gm.hgen {
                        c
                    } else {
                        let c2 = self.g_arg(a, env);
                        self.gm.ccells[j as usize] = (self.gm.hgen, c2);
                        c2
                    }
                }
            };
            self.gm.args.push(c);
            j += 1;
        }
        match self.st.node(f) {
            Expr::Const(..) => self.g_const(f),
            Expr::BVar(i) => self.g_var(env, i),
            _ => Ctl::Eval(f, env),
        }
    }

    fn g_lit(&mut self, n: NatId) -> GVal {
        let x = self.st.nat(n).clone();
        self.gm.nat_val(x)
    }

    fn g_force(&mut self, c: u32) -> Ctl {
        match self.gm.cells[c as usize] {
            Slot::Val(v) => self.g_ret(v),
            Slot::Busy(..) => Ctl::Bail,
            Slot::Thunk(t, env) => {
                self.gm.cells[c as usize] = Slot::Busy(t, env);
                self.gm.frame(Frame::Update(c));
                Ctl::Eval(t, env)
            }
        }
    }

    fn g_ret(&mut self, v: GVal) -> Ctl {
        if self.gm.avail() > 0 {
            return self.g_apply(v);
        }
        match self.gm.frames.pop() {
            None => Ctl::Done(v),
            Some(fa) => match fa.f {
                Frame::Update(c) => {
                    self.gm.cells[c as usize] = Slot::Val(v);
                    Ctl::Ret(v)
                }
                Frame::Rec(slot) => self.g_iota(slot, v),
                Frame::Proj(sn, i) => self.g_proj(sn, i, v),
                Frame::Nat1(op, b) => {
                    if op == OP_SUCC {
                        self.g_nat_out(op, v, v)
                    } else {
                        self.gm.frame(Frame::Nat2(op, v));
                        Ctl::Force(b)
                    }
                }
                Frame::Nat2(op, x) => self.g_nat_out(op, x, v),
                Frame::Quot(pos) => self.g_quot(pos, v),
            },
        }
    }

    /// A value applied to the arguments on the stack.
    fn g_apply(&mut self, v: GVal) -> Ctl {
        match v {
            GVal::Clo(lam, env) => match self.st.node(lam) {
                Expr::Lam(b) => self.g_beta(b.body, env),
                _ => Ctl::Bail,
            },
            GVal::Pap(c, start, n) => {
                self.gm.push_fields(start, n);
                self.g_const(c)
            }
            _ => Ctl::Bail,
        }
    }

    /// A partial application of the constant `t` to all the arguments above the base.
    fn g_pap(&mut self, t: ExprId) -> Ctl {
        let n = self.gm.avail();
        let start = self.gm.pop_fields(n);
        Ctl::Ret(GVal::Pap(t, start, n))
    }

    /// What `g_const` does with the constant `t`, from the environment.
    fn g_resolve(&mut self, t: ExprId) -> CKind {
        let (n, ls) = match self.st.node(t) {
            Expr::Const(n, ls) => (n, ls),
            _ => return CKind::Bail,
        };
        if n == self.b.nat_succ {
            return CKind::Succ;
        }
        if n == self.b.nat_zero {
            return CKind::Zero;
        }
        let op = self.nat_op_name_index(n);
        if op < self.b.nat_op_names.len() {
            return CKind::NatOp(op as u32);
        }
        let s = self.env.find(n);
        if s == 0 {
            return CKind::Bail;
        }
        let nls = self.st.level_list_items(ls).len();
        let c = self.env.at(s);
        let lps_ok = nls == c.lparams.len();
        match &c.kind {
            ConstKind::Defn { value, .. } | ConstKind::Thm { value } if lps_ok => {
                CKind::Defn(s, *value)
            }
            ConstKind::Induct(_) => CKind::Type,
            ConstKind::Ctor(ci) => CKind::Ctor(n, ci.nparams, ci.nfields),
            ConstKind::Rec(_) if lps_ok => self.g_resolve_rec(s),
            ConstKind::Quot { .. } => CKind::Quot(n),
            _ => CKind::Bail,
        }
    }

    /// A recursor that engine G can reduce: not K-like, and with a major premise that is not a proof when `no_whnf_prop_major` is on.
    fn g_resolve_rec(&mut self, s: u32) -> CKind {
        let r = match self.rec_shape(s) {
            Some(r) => r,
            None => return CKind::Bail,
        };
        if r.k || (self.flags.no_whnf_prop_major && !self.major_not_prop(s, r.major_idx)) {
            return CKind::Bail;
        }
        CKind::Rec(s, r.major_idx)
    }

    /// The cell of the value of the definition of the slot.
    fn g_caf(&mut self, s: u32, value: ExprId) -> u32 {
        match self.gm.caf.get(raw(s), 0) {
            Some(c) => low(c),
            None => {
                // Only a function goes through the inline pass. For a value that is not a lambda, the pass costs more than it gives.
                let v = if matches!(self.st.node(value), Expr::Lam(_)) {
                    self.g_inline_value(s, value)
                } else {
                    value
                };
                let c = self.gm.cell(Slot::Thunk(v, NIL));
                self.gm.caf_put(raw(s), 0, c);
                c
            }
        }
    }

    /// The value of the slot `s` after the inline pass. A frozen value gives a frozen result, which stays for the next declarations.
    fn g_inline_value(&mut self, s: u32, value: ExprId) -> ExprId {
        let k = s as usize;
        if k < self.gm.plain.len() && self.gm.plain[k] == value {
            return value;
        }
        let frozen = value.tier() == Tier::Frozen;
        if frozen && k < self.gm.inl_val.len() && self.gm.inl_val[k].0 == value {
            return self.gm.inl_val[k].1;
        }
        let saved = self.st.uses_scratch();
        if frozen {
            self.st.set_scratch(false);
        }
        self.gm.inl_frozen = frozen;
        let mut fuel = G_INL_FUEL;
        let v = self.g_inline(value, G_INL_DEPTH, &mut fuel);
        if frozen {
            self.st.set_scratch(saved);
        }
        if v == value {
            while self.gm.plain.len() <= k {
                self.gm.plain.push(NIL_E);
            }
            self.gm.plain[k] = value;
        } else if frozen {
            while self.gm.inl_val.len() <= k {
                self.gm.inl_val.push((NIL_E, NIL_E));
            }
            self.gm.inl_val[k] = (value, v);
        }
        v
    }

    /// The term `e` with each application of a wrapper replaced by the body of the wrapper (spec perf/10, G5b). A wrapper is a definition whose body after its lambdas is an application of a constant, for example a matcher or `casesOn`. Engine G does not read the levels and the types, so the result has the same value as `e`. An argument that is not a variable, a constant, a literal or a lambda goes in only for a parameter that the body uses at most one time and not under a lambda, so no work is done two times.
    fn g_inline(&mut self, e: ExprId, depth: u32, fuel: &mut u32) -> ExprId {
        if *fuel == 0 {
            return e;
        }
        *fuel -= 1;
        match self.st.node(e) {
            Expr::Lam(b) => {
                let body = self.g_inline(b.body, depth, fuel);
                if body == b.body {
                    e
                } else {
                    self.st.mk_lam(b.name, b.info, b.dom, body)
                }
            }
            Expr::App(_, _) => self.g_inline_app(e, depth, fuel),
            _ => e,
        }
    }

    fn g_inline_app(&mut self, e: ExprId, depth: u32, fuel: &mut u32) -> ExprId {
        let mut args = self.take_vec();
        let h = expr::app_args(&self.st, e, &mut args);
        let mut changed = false;
        let mut i = 0;
        while i < args.len() {
            let a = self.g_inline(args[i], depth, fuel);
            if a != args[i] {
                changed = true;
                args[i] = a;
            }
            i += 1;
        }
        let w = if depth > 0 {
            self.g_wrapper(h, &args)
        } else {
            NIL_E
        };
        let r = if w != NIL_E {
            NIL_E
        } else if changed {
            self.st.mk_apps(h, &args)
        } else {
            e
        };
        self.give_vec(args);
        if w != NIL_E {
            self.g_inline(w, depth - 1, fuel)
        } else {
            r
        }
    }

    /// The body of the wrapper `h` applied to `args`, or `NIL_E` if `h` is not a wrapper or an argument cannot go in.
    fn g_wrapper(&mut self, h: ExprId, args: &[ExprId]) -> ExprId {
        if !matches!(self.st.node(h), Expr::Const(_, _)) {
            return NIL_E;
        }
        let (s, value) = match self.g_kind(h) {
            CKind::Defn(s, v) => (s, v),
            _ => return NIL_E,
        };
        if !matches!(self.env.at(s).kind, ConstKind::Defn { .. })
            || (self.gm.inl_frozen && value.tier() != Tier::Frozen)
        {
            return NIL_E;
        }
        let mut k = 0;
        let mut b = value;
        let mut walking = true;
        while walking {
            match self.st.node(b) {
                Expr::Lam(x) => {
                    b = x.body;
                    k += 1;
                }
                _ => walking = false,
            }
        }
        if k == 0 || k > args.len() {
            return NIL_E;
        }
        let f = expr::app_fn(&self.st, b);
        if !matches!(self.st.node(f), Expr::Const(_, _)) || f == h {
            return NIL_E;
        }
        let mut ok = true;
        let mut j = 0;
        while ok && j < k {
            let simple = matches!(
                self.st.node(args[j]),
                Expr::BVar(_)
                    | Expr::Const(_, _)
                    | Expr::Lit(_)
                    | Expr::Sort(_)
                    | Expr::Lam(_)
                    | Expr::Pi(_)
            );
            if !simple {
                let mut f2 = G_INL_FUEL;
                ok = self.g_occ(b, (k - 1 - j) as u32, false, &mut f2) <= 1;
            }
            j += 1;
        }
        if !ok {
            return NIL_E;
        }
        let mut rev: Vec<ExprId> = Vec::with_capacity(args.len());
        let mut i = args.len();
        while i > 0 {
            i -= 1;
            rev.push(args[i]);
        }
        expr::apply_beta(&mut self.st, &mut self.x, value, &rev)
    }

    /// The uses of the bound variable `i` in `e` that engine G can compute, with a use under a lambda counted as 2. The result is at most 2, and 2 when the fuel ends.
    fn g_occ(&self, e: ExprId, i: u32, under: bool, fuel: &mut u32) -> u32 {
        if expr::no_loose_from(&self.st, e, i as u64) {
            return 0;
        }
        if *fuel == 0 {
            return 2;
        }
        *fuel -= 1;
        let n = match self.st.node(e) {
            Expr::BVar(j) if j == i => {
                if under {
                    2
                } else {
                    1
                }
            }
            Expr::App(f, a) => self.g_occ(f, i, under, fuel) + self.g_occ(a, i, under, fuel),
            Expr::Lam(b) => self.g_occ(b.body, i + 1, true, fuel),
            Expr::Let(l) => {
                self.g_occ(l.value, i, under, fuel) + self.g_occ(l.body, i + 1, true, fuel)
            }
            Expr::Proj(p) => self.g_occ(p.expr, i, under, fuel),
            Expr::BVar(_) | Expr::Pi(_) => 0,
            _ => 2,
        };
        if n > 2 { 2 } else { n }
    }

    /// What `g_const` does with the constant `t`, from the cache of the constants.
    fn g_kind(&mut self, t: ExprId) -> CKind {
        let i = cache_index(t);
        let ent = self.gm.ccache[i];
        if ent.key == t && ent.epoch == self.gm.epoch {
            ent.kind
        } else {
            let k = self.g_resolve(t);
            self.gm.ccache[i] = CEntry {
                key: t,
                epoch: self.gm.epoch,
                hgen: u32::MAX,
                kind: k,
                cell: 0,
            };
            k
        }
    }

    /// A constant applied to the arguments above the base.
    fn g_const(&mut self, t: ExprId) -> Ctl {
        let i = cache_index(t);
        let kind = self.g_kind(t);
        let avail = self.gm.avail();
        match kind {
            CKind::Succ => {
                if avail == 0 {
                    return self.g_pap(t);
                }
                let a = self.gm.pop_arg();
                self.gm.frame(Frame::Nat1(OP_SUCC, a));
                Ctl::Force(a)
            }
            CKind::Zero => Ctl::Ret(GVal::Small(0)),
            CKind::NatOp(op) => {
                if avail < 2 {
                    return self.g_pap(t);
                }
                let a = self.gm.pop_arg();
                let b = self.gm.pop_arg();
                self.gm.frame(Frame::Nat1(op, b));
                Ctl::Force(a)
            }
            CKind::Defn(s, value) => {
                let e2 = self.gm.ccache[i];
                if e2.key == t && e2.hgen == self.gm.hgen {
                    return self.g_force(e2.cell);
                }
                let c = self.g_caf(s, value);
                // The inline pass of `g_caf` can use the same entry for another constant, so all of the entry is written again.
                self.gm.ccache[i] = CEntry {
                    key: t,
                    epoch: self.gm.epoch,
                    hgen: self.gm.hgen,
                    kind,
                    cell: c,
                };
                self.g_force(c)
            }
            CKind::Type => Ctl::Ret(GVal::Type),
            CKind::Ctor(n, np, nf) => self.g_ctor(t, n, np, nf),
            CKind::Rec(s, major_idx) => {
                if avail <= major_idx {
                    return self.g_pap(t);
                }
                let m = self.gm.arg_at(major_idx);
                self.gm.frame(Frame::Rec(s));
                Ctl::Force(m)
            }
            CKind::Quot(n) => self.g_quot_const(t, n),
            CKind::Bail => Ctl::Bail,
        }
    }

    fn g_ctor(&mut self, t: ExprId, n: NameId, np: u32, nf: u32) -> Ctl {
        if self.gm.avail() < np + nf {
            return self.g_pap(t);
        }
        self.gm.drop_top(np);
        let start = self.gm.pop_fields(nf);
        Ctl::Ret(GVal::Ctor(n, start, nf))
    }

    /// The rule of the recursor of the slot for the major premise `v`. The arguments of the recursor are on the stack.
    fn g_iota(&mut self, slot: u32, v: GVal) -> Ctl {
        let (ctor, start, nf) = match v {
            GVal::Small(0) => (self.b.nat_zero, 0, 0),
            GVal::Small(x) => {
                let c = self.gm.cell(Slot::Val(GVal::Small(x - 1)));
                let start = self.gm.fields.len() as u32;
                self.gm.fields.push(c);
                (self.b.nat_succ, start, 1)
            }
            GVal::Big(i) => {
                let one = Nat::from_u64(1);
                let p = self.gm.nats[i as usize].sub(&one);
                let pv = self.gm.nat_val(p);
                let c = self.gm.cell(Slot::Val(pv));
                let start = self.gm.fields.len() as u32;
                self.gm.fields.push(c);
                (self.b.nat_succ, start, 1)
            }
            GVal::Ctor(c, start, nf) => (c, start, nf),
            _ => return Ctl::Bail,
        };
        let r = match self.rec_shape(slot) {
            Some(r) => r,
            None => return Ctl::Bail,
        };
        let rule = match &self.env.at(slot).kind {
            ConstKind::Rec(info) => find_rule(&info.rules, ctor),
            _ => None,
        };
        let rule = match rule {
            Some(x) if x.nfields <= nf => x,
            _ => return Ctl::Bail,
        };
        // The stack has, from the top: the parameters, the motives and the minor premises (`nprefix`), the indices, the major premise, and the other arguments.
        let np = r.nprefix;
        self.gm.tmp.truncate(0);
        let mut i = 0;
        while i < np {
            let a = self.gm.pop_arg();
            self.gm.tmp.push(a);
            i += 1;
        }
        self.gm.drop_top(r.major_idx - np + 1);
        let first = start + nf - rule.nfields;
        self.gm.push_fields(first, rule.nfields);
        let mut j = np;
        while j > 0 {
            j -= 1;
            let a = self.gm.tmp[j as usize];
            self.gm.args.push(a);
        }
        Ctl::Eval(rule.rhs, NIL)
    }

    fn g_proj(&mut self, sn: NameId, idx: u32, v: GVal) -> Ctl {
        let (c, start, nf) = match v {
            GVal::Ctor(c, start, nf) => (c, start, nf),
            _ => return Ctl::Bail,
        };
        match self.ctor_shape(c) {
            Some((induct, _, _)) if induct == sn && idx < nf => {
                let f = self.gm.fields[(start + idx) as usize];
                Ctl::Force(f)
            }
            _ => Ctl::Bail,
        }
    }

    /// `Quot.mk` is a constructor with one field. `Quot.lift` and `Quot.ind` force the `Quot.mk` argument.
    fn g_quot_const(&mut self, t: ExprId, n: NameId) -> Ctl {
        if !self.env.quot_initialized() {
            return Ctl::Bail;
        }
        let pos = if n == self.b.quot_mk {
            return self.g_ctor(t, n, 2, 1);
        } else if n == self.b.quot_lift {
            5
        } else if n == self.b.quot_ind {
            4
        } else {
            return Ctl::Ret(GVal::Type);
        };
        if self.gm.avail() <= pos {
            return self.g_pap(t);
        }
        let m = self.gm.arg_at(pos);
        self.gm.frame(Frame::Quot(pos));
        Ctl::Force(m)
    }

    /// `Quot.lift f h (Quot.mk r a)` is `f a`, and `Quot.ind h (Quot.mk r a)` is `h a`. The function is the argument at position 3.
    fn g_quot(&mut self, pos: u32, v: GVal) -> Ctl {
        let a = match v {
            GVal::Ctor(c, start, 1) if c == self.b.quot_mk => self.gm.fields[start as usize],
            _ => return Ctl::Bail,
        };
        let f = self.gm.arg_at(3);
        self.gm.drop_top(pos + 1);
        self.gm.args.push(a);
        Ctl::Force(f)
    }

    /// The result of the `Nat` operation `op` on the values `x` and `y`. `Nat.succ` reads only `x`. A size above the bound or a count that is too large bails, so that engine R gives the same fault as before.
    fn g_nat_out(&mut self, op: u32, x: GVal, y: GVal) -> Ctl {
        if let (GVal::Small(a), GVal::Small(b)) = (x, y)
            && self.nat_max >= 8
        {
            let fast = if op == OP_SUCC {
                Some(SmallOut::Num(a + 1))
            } else {
                small_op(op as usize, a, b)
            };
            match fast {
                Some(SmallOut::Num(r)) => return Ctl::Ret(self.gm.nat_val(Nat::from_u64(r))),
                Some(SmallOut::Bool(t)) => return Ctl::Ret(self.g_bool(t)),
                None => {}
            }
        }
        // The operands are read in place. A copy of a large number costs a memory copy and a free for each operation (spec perf/10.9).
        let sa;
        let sb;
        let a: &Nat = match x {
            GVal::Small(v) => {
                sa = Nat::from_u64(v);
                &sa
            }
            GVal::Big(i) => &self.gm.nats[i as usize],
            _ => return Ctl::Bail,
        };
        let b: &Nat = match y {
            GVal::Small(v) => {
                sb = Nat::from_u64(v);
                &sb
            }
            GVal::Big(i) => &self.gm.nats[i as usize],
            _ => return Ctl::Bail,
        };
        let out = if op == OP_SUCC {
            sized(a.succ(), self.nat_max)
        } else {
            nat_big(op as usize, a, b, self.nat_max)
        };
        match out {
            BigOut::Num(r) => Ctl::Ret(self.gm.nat_val(r)),
            BigOut::Bool(t) => Ctl::Ret(self.g_bool(t)),
            BigOut::Bail => Ctl::Bail,
        }
    }

    fn g_bool(&self, t: bool) -> GVal {
        let c = if t {
            self.b.bool_true
        } else {
            self.b.bool_false
        };
        GVal::Ctor(c, 0, 0)
    }
}

/// The result of `nat_big`.
enum BigOut {
    Num(Nat),
    Bool(bool),
    Bail,
}

/// `r`, or a bail if its size is above `nat_max`.
fn sized(r: Nat, nat_max: u64) -> BigOut {
    if Checker::nat_size(&r) > nat_max {
        BigOut::Bail
    } else {
        BigOut::Num(r)
    }
}

/// The binary operation of `nat_bin` on two numbers, with a bail in place of each fault.
fn nat_big(op: usize, a: &Nat, b: &Nat, nat_max: u64) -> BigOut {
    if op == NAT_POW || op == NAT_SHL {
        let k = match b.to_u64() {
            Some(k) if k <= u32::MAX as u64 => k,
            _ => return BigOut::Bail,
        };
        if op == NAT_POW {
            let one = Nat::from_u64(1);
            if a.compare(&one) == core::cmp::Ordering::Greater
                && k != 0
                && Checker::nat_size(a) > nat_max / k
            {
                return BigOut::Bail;
            }
            return BigOut::Num(a.pow(k));
        }
        if a.is_zero() {
            return BigOut::Num(Nat::from_u64(0));
        }
        if Checker::nat_size(a) + k / 8 + 1 > nat_max {
            return BigOut::Bail;
        }
        return BigOut::Num(a.shift_left(k));
    }
    match op {
        crate::tc::NAT_ADD => sized(a.add(b), nat_max),
        crate::tc::NAT_SUB => sized(a.sub(b), nat_max),
        crate::tc::NAT_MUL => sized(a.mul(b), nat_max),
        crate::tc::NAT_GCD => BigOut::Num(a.gcd(b)),
        crate::tc::NAT_MOD => BigOut::Num(a.rem(b)),
        crate::tc::NAT_DIV => BigOut::Num(a.div(b)),
        crate::tc::NAT_BEQ => BigOut::Bool(a.beq(b)),
        crate::tc::NAT_BLE => BigOut::Bool(a.ble(b)),
        crate::tc::NAT_LAND => BigOut::Num(a.land(b)),
        crate::tc::NAT_LOR => BigOut::Num(a.lor(b)),
        crate::tc::NAT_XOR => BigOut::Num(a.xor(b)),
        crate::tc::NAT_SHR => BigOut::Num(a.shift_right_nat(b)),
        _ => BigOut::Bail,
    }
}

impl Ground {
    fn caf_put(&mut self, a: Raw, b: Raw, c: u32) {
        self.caf.put(a, b, raw(c));
        self.caf_keys.push((a, b, c));
    }

    /// A copying collection: the cells, the environments, the fields and the numbers that the roots reach go to new arrays, and the rest goes. The roots are the control, the argument stack, the frames and the cells of `caf`. It gives the control with the new indices.
    fn gc(&mut self, c: Ctl) -> Ctl {
        self.gcs += 1;
        let mut g = Gc {
            cfwd: alloc::vec![NIL; self.cells.len()],
            efwd: alloc::vec![NIL; self.envs.len()],
            ffwd: alloc::vec![NIL; self.fields.len()],
            nfwd: alloc::vec![NIL; self.nats.len()],
            cells: Vec::with_capacity(self.cells.len() + 16),
            envs: Vec::with_capacity(self.envs.len() + 16),
            fields: Vec::with_capacity(self.fields.len() + 16),
            nats: Vec::new(),
            words: 0,
        };
        let c2 = match c {
            Ctl::Eval(t, env) => Ctl::Eval(t, g.env(self, env)),
            Ctl::Force(x) => Ctl::Force(g.cell(self, x)),
            Ctl::Ret(v) => Ctl::Ret(g.val(self, v)),
            Ctl::Done(v) => Ctl::Done(g.val(self, v)),
            Ctl::Bail => Ctl::Bail,
        };
        let mut i = 0;
        while i < self.args.len() {
            self.args[i] = g.cell(self, self.args[i]);
            i += 1;
        }
        i = 0;
        while i < self.tmp.len() {
            self.tmp[i] = g.cell(self, self.tmp[i]);
            i += 1;
        }
        i = 0;
        while i < self.roots.len() {
            self.roots[i] = g.cell(self, self.roots[i]);
            i += 1;
        }
        i = 0;
        while i < self.frames.len() {
            let f = match self.frames[i].f {
                Frame::Update(x) => Frame::Update(g.cell(self, x)),
                Frame::Nat1(op, x) => Frame::Nat1(op, g.cell(self, x)),
                Frame::Nat2(op, v) => Frame::Nat2(op, g.val(self, v)),
                other => other,
            };
            self.frames[i].f = f;
            i += 1;
        }
        i = 0;
        while i < self.caf_keys.len() {
            let (a, b, x) = self.caf_keys[i];
            self.caf_keys[i] = (a, b, g.cell(self, x));
            i += 1;
        }
        g.scan(self);
        self.cells = g.cells;
        self.envs = g.envs;
        self.fields = g.fields;
        self.nats = g.nats;
        self.nat_words = g.words;
        self.caf.clear();
        i = 0;
        while i < self.caf_keys.len() {
            let (a, b, x) = self.caf_keys[i];
            self.caf.put(a, b, raw(x));
            i += 1;
        }
        self.hgen = self.hgen.wrapping_add(1) & 0x7fff_ffff;
        let live = self.size();
        self.gc_at = live * 2;
        self.words_at = self.nat_words * 2;
        c2
    }

    /// Puts back the thunk of each cell under evaluation, after a bail.
    fn unwind(&mut self) {
        let mut i = self.frames.len();
        while i > 0 {
            i -= 1;
            if let Frame::Update(c) = self.frames[i].f
                && let Slot::Busy(t, env) = self.cells[c as usize]
            {
                self.cells[c as usize] = Slot::Thunk(t, env);
            }
        }
    }

    /// Removes `n` arguments from the top of the stack.
    fn drop_top(&mut self, n: u32) {
        self.drop_args(n);
    }
}

/// The state of one collection: the forward index of each old cell, environment, field range and number (`NIL` if not copied yet), and the new arrays.
struct Gc {
    cfwd: Vec<u32>,
    efwd: Vec<u32>,
    ffwd: Vec<u32>,
    nfwd: Vec<u32>,
    cells: Vec<Slot>,
    envs: Vec<GEnv>,
    fields: Vec<u32>,
    nats: Vec<Nat>,
    words: usize,
}

impl Gc {
    /// The new index of an old cell. The copy has old indices until `scan` reads it.
    fn cell(&mut self, old: &Ground, c: u32) -> u32 {
        let f = self.cfwd[c as usize];
        if f != NIL {
            return f;
        }
        let n = self.cells.len() as u32;
        self.cells.push(old.cells[c as usize]);
        self.cfwd[c as usize] = n;
        n
    }

    fn env(&mut self, old: &Ground, e: u32) -> u32 {
        if e == NIL {
            return NIL;
        }
        let f = self.efwd[e as usize];
        if f != NIL {
            return f;
        }
        let n = self.envs.len() as u32;
        self.envs.push(old.envs[e as usize]);
        self.efwd[e as usize] = n;
        n
    }

    /// The new start of the field range at `start` with `k` fields. A range has one start, so the forward index of the start is the forward index of the range.
    fn range(&mut self, old: &Ground, start: u32, k: u32) -> u32 {
        if k == 0 {
            return 0;
        }
        let f = self.ffwd[start as usize];
        if f != NIL {
            return f;
        }
        let n = self.fields.len() as u32;
        let mut i = 0;
        while i < k {
            self.fields.push(old.fields[(start + i) as usize]);
            i += 1;
        }
        self.ffwd[start as usize] = n;
        n
    }

    fn val(&mut self, old: &Ground, v: GVal) -> GVal {
        match v {
            GVal::Big(i) => {
                let f = self.nfwd[i as usize];
                if f != NIL {
                    return GVal::Big(f);
                }
                let n = self.nats.len() as u32;
                let x = old.nats[i as usize].clone();
                self.words += x.limb_count();
                self.nats.push(x);
                self.nfwd[i as usize] = n;
                GVal::Big(n)
            }
            GVal::Ctor(c, start, k) => GVal::Ctor(c, self.range(old, start, k), k),
            GVal::Pap(c, start, k) => GVal::Pap(c, self.range(old, start, k), k),
            GVal::Clo(l, env) => GVal::Clo(l, self.env(old, env)),
            other => other,
        }
    }

    /// Reads the new cells, environments and fields in order, and moves their old indices to new indices. A step can copy more, so the loop runs until all three arrays are read.
    fn scan(&mut self, old: &Ground) {
        let mut ci = 0;
        let mut ei = 0;
        let mut fi = 0;
        while ci < self.cells.len() || ei < self.envs.len() || fi < self.fields.len() {
            while ci < self.cells.len() {
                let x = match self.cells[ci] {
                    Slot::Thunk(t, env) => Slot::Thunk(t, self.env(old, env)),
                    Slot::Busy(t, env) => Slot::Busy(t, self.env(old, env)),
                    Slot::Val(v) => Slot::Val(self.val(old, v)),
                };
                self.cells[ci] = x;
                ci += 1;
            }
            while ei < self.envs.len() {
                let x = self.envs[ei];
                let cell = self.cell(old, x.cell);
                let parent = self.env(old, x.parent);
                self.envs[ei] = GEnv { cell, parent };
                ei += 1;
            }
            while fi < self.fields.len() {
                let x = self.fields[fi];
                self.fields[fi] = self.cell(old, x);
                fi += 1;
            }
        }
    }
}
