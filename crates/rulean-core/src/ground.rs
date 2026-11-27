//! Engine G: a call-by-need machine for closed terms (spec perf/10).
//!
//! Engine G evaluates a closed term to a `Bool` or a `Nat` value. It is a Krivine machine with update frames: an argument is a thunk, the first read of a thunk evaluates it, and the value replaces the thunk. The machine has an explicit stack of arguments and an explicit stack of frames, so it does not recurse.
//!
//! The machine reads the terms of the store directly. It does not substitute, so it makes no new terms. A definition unfolds to its value without the substitution of its level parameters, because a closed computation that gives a `Bool` or a `Nat` value does not depend on the levels: no rule of reduction reads a level.
//!
//! Each step of the machine is a step of the official kernel: beta, zeta, delta, iota, projection, the quotient rules and the `Nat` extension. The machine stops with no result ("bail") when the next step needs more than the term: a K-like recursor, a major premise that can be a proof when `no_whnf_prop_major` is on, a string literal, an axiom or an opaque constant, a free variable, a `Nat` result above the size bound, or a budget. Then engine R does the work as before. A result is a constructor or a literal, and two different ones are not definitionally equal, so a result answers the query.

use alloc::vec::Vec;
use rulean_nat::Nat;
use rulean_store::ids::{low, raw};
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
    /// The epoch of the declaration, and the generation of the heap. A clear starts a new epoch and a new generation, and a collection starts a new generation.
    epoch: u32,
    hgen: u32,
    /// The runs, and the runs that gave a result.
    pub runs: u64,
    pub hits: u64,
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
                let mut args = Vec::new();
                let n = self.va.spine_push_args(sp, &mut args);
                let mut t = self.st.mk_const(c, us);
                let mut i = 0;
                let mut ok = true;
                while ok && i < n {
                    match self.value_term(args[i], fuel) {
                        Some(a) => t = self.st.mk_app(t, a),
                        None => ok = false,
                    }
                    i += 1;
                }
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
            + (self.fields.capacity() + self.args.capacity() + self.tmp.capacity()) * 4
            + self.frames.capacity() * core::mem::size_of::<FrameAt>()
            + self.nats.capacity() * core::mem::size_of::<Nat>()
            + self.caf.bytes()
            + self.ccache.capacity() * core::mem::size_of::<CEntry>()
            + self.acache.capacity() * 12
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
                i += 1;
            }
        }
    }

    /// Empties the arrays. A large array is given back to the allocator.
    pub(crate) fn clear(&mut self) {
        self.epoch = self.epoch.wrapping_add(1) & 0x7fff_ffff;
        self.hgen = self.hgen.wrapping_add(1) & 0x7fff_ffff;
        self.caf.clear();
        self.caf_keys = Vec::new();
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
        self.nats = Vec::new();
        self.tmp.truncate(0);
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

    /// The number of a `Nat` value.
    fn nat_of(&self, v: GVal) -> Option<Nat> {
        match v {
            GVal::Small(x) => Some(Nat::from_u64(x)),
            GVal::Big(i) => Some(self.nats[i as usize].clone()),
            _ => None,
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

    /// The loop of the machine.
    fn ground_run(&mut self, e: ExprId) -> Option<GVal> {
        let mut c = Ctl::Eval(e, NIL);
        let mut out = None;
        let mut go = true;
        let mut ticks: u64 = 0;
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
            ticks += 1;
            if ticks.is_multiple_of(4096) {
                if self.gm.size() > self.gm.gc_at.max(G_GC_FIRST)
                    || self.gm.nat_words > self.gm.words_at.max(G_GC_WORDS)
                {
                    c = self.gm.gc(c);
                }
                if ticks > G_MAX_STEPS || self.ground_over() {
                    c = Ctl::Bail;
                }
            }
        }
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
            Expr::BVar(i) => match self.gm.env_get(env, i) {
                Some(c) => Ctl::Force(c),
                None => Ctl::Bail,
            },
            Expr::App(..) => self.g_app(t, env),
            Expr::Lam(b) => {
                if self.gm.avail() > 0 {
                    let a = self.gm.pop_arg();
                    let env2 = self.gm.env_push(env, a);
                    Ctl::Eval(b.body, env2)
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

    /// An application: the arguments go on the stack, the last one first, and the head is next.
    fn g_app(&mut self, t: ExprId, env: u32) -> Ctl {
        let mut f = t;
        let mut go = true;
        while go {
            match self.st.node(f) {
                Expr::App(g, a) => {
                    let c = self.g_arg(a, env);
                    self.gm.args.push(c);
                    f = g;
                }
                _ => go = false,
            }
        }
        Ctl::Eval(f, env)
    }

    fn g_lit(&mut self, n: NatId) -> GVal {
        let x = self.st.nat(n).clone();
        self.gm.nat_val(x)
    }

    fn g_force(&mut self, c: u32) -> Ctl {
        match self.gm.cells[c as usize] {
            Slot::Val(v) => Ctl::Ret(v),
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
                Expr::Lam(b) => {
                    let a = self.gm.pop_arg();
                    let env2 = self.gm.env_push(env, a);
                    Ctl::Eval(b.body, env2)
                }
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
                let c = self.gm.cell(Slot::Thunk(value, NIL));
                self.gm.caf_put(raw(s), 0, c);
                c
            }
        }
    }

    /// A constant applied to the arguments above the base.
    fn g_const(&mut self, t: ExprId) -> Ctl {
        let i = cache_index(t);
        let ent = self.gm.ccache[i];
        let kind = if ent.key == t && ent.epoch == self.gm.epoch {
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
        };
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
                    return Ctl::Force(e2.cell);
                }
                let c = self.g_caf(s, value);
                self.gm.ccache[i].hgen = self.gm.hgen;
                self.gm.ccache[i].cell = c;
                Ctl::Force(c)
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
        let (a, b) = match (self.gm.nat_of(x), self.gm.nat_of(y)) {
            (Some(a), Some(b)) => (a, b),
            _ => return Ctl::Bail,
        };
        if op == OP_SUCC {
            let r = a.succ();
            return self.g_sized(r);
        }
        self.g_nat_big(op as usize, &a, &b)
    }

    fn g_bool(&self, t: bool) -> GVal {
        let c = if t {
            self.b.bool_true
        } else {
            self.b.bool_false
        };
        GVal::Ctor(c, 0, 0)
    }

    fn g_sized(&mut self, r: Nat) -> Ctl {
        if Checker::nat_size(&r) > self.nat_max {
            return Ctl::Bail;
        }
        Ctl::Ret(self.gm.nat_val(r))
    }

    /// The binary operation of `nat_bin` on two numbers, with a bail in place of each fault.
    fn g_nat_big(&mut self, op: usize, a: &Nat, b: &Nat) -> Ctl {
        if op == NAT_POW || op == NAT_SHL {
            let k = match b.to_u64() {
                Some(k) if k <= u32::MAX as u64 => k,
                _ => return Ctl::Bail,
            };
            if op == NAT_POW {
                let one = Nat::from_u64(1);
                if a.compare(&one) == core::cmp::Ordering::Greater
                    && k != 0
                    && Checker::nat_size(a) > self.nat_max / k
                {
                    return Ctl::Bail;
                }
                return Ctl::Ret(self.gm.nat_val(a.pow(k)));
            }
            if a.is_zero() {
                return Ctl::Ret(GVal::Small(0));
            }
            if Checker::nat_size(a) + k / 8 + 1 > self.nat_max {
                return Ctl::Bail;
            }
            return Ctl::Ret(self.gm.nat_val(a.shift_left(k)));
        }
        match op {
            crate::tc::NAT_ADD => self.g_sized(a.add(b)),
            crate::tc::NAT_SUB => self.g_sized(a.sub(b)),
            crate::tc::NAT_MUL => self.g_sized(a.mul(b)),
            crate::tc::NAT_GCD => Ctl::Ret(self.gm.nat_val(a.gcd(b))),
            crate::tc::NAT_MOD => Ctl::Ret(self.gm.nat_val(a.rem(b))),
            crate::tc::NAT_DIV => Ctl::Ret(self.gm.nat_val(a.div(b))),
            crate::tc::NAT_BEQ => Ctl::Ret(self.g_bool(a.beq(b))),
            crate::tc::NAT_BLE => Ctl::Ret(self.g_bool(a.ble(b))),
            crate::tc::NAT_LAND => Ctl::Ret(self.gm.nat_val(a.land(b))),
            crate::tc::NAT_LOR => Ctl::Ret(self.gm.nat_val(a.lor(b))),
            crate::tc::NAT_XOR => Ctl::Ret(self.gm.nat_val(a.xor(b))),
            crate::tc::NAT_SHR => Ctl::Ret(self.gm.nat_val(a.shift_right_nat(b))),
            _ => Ctl::Bail,
        }
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
            cells: Vec::with_capacity(self.cells.len() / 2 + 16),
            envs: Vec::with_capacity(self.envs.len() / 2 + 16),
            fields: Vec::with_capacity(self.fields.len() / 2 + 16),
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
