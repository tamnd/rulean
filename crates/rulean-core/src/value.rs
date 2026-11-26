//! The value arena of engine F (spec 04.5 and 05.4.1).
//!
//! A worker keeps one arena. Values, environments, spines and unfolding slots are in typed arrays, and each handle is a `u32` index into one array. A closure is the pair of an environment and a stored term, so the arena has no Rust closures (spec 10.6).
//!
//! An environment is a persistent list: each node has one value and the handle of its parent. A spine is a persistent list in the other order: each node has the last argument, the handle of the spine before it and the length. So `push` on an environment and on a spine makes one node and copies nothing, and two values can share a prefix.
//!
//! The arena is cleared at the end of each declaration. `reset` sets the length of each array to zero, so no value crosses a declaration (spec 04.5).

use alloc::vec::Vec;
use rulean_store::{BinderInfo, ExprId, LevelId, LevelListId, Literal, NameId};

/// A handle to a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueId(pub u32);

/// A handle to an environment. `EnvId::NIL` is the empty environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EnvId(pub u32);

/// A handle to a spine. `SpineId::NIL` is the empty spine.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpineId(pub u32);

/// A handle to an unfolding slot of a glued value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SlotId(pub u32);

impl EnvId {
    /// The empty environment.
    pub const NIL: EnvId = EnvId(u32::MAX);
}

impl SpineId {
    /// The empty spine.
    pub const NIL: SpineId = SpineId(u32::MAX);
}

/// The largest number of nodes in one array of the arena, 2^18. At this limit the arena is full. Engine F then stops with a fault, the fault is removed, and engine R decides the query and each later query of the declaration (spec 05.1). With nodes of 8 to 24 bytes, the four arrays use at most about 25 MiB, well inside the per-worker scratch of spec 04.9.
///
/// The limit is a budget for engine F on one declaration. When engine F fills the arena, the work that it did is lost, and engine R does the query again. A larger limit lets engine F waste more work on a declaration that it cannot finish. On the 42 Arena perf tests, the total count of instructions was 1537 G with 2^22, 1348 G with 2^20 and 1326 G with 2^18. The test `grind-ring-5` went from 121 G to 28 G, and `gf3-matrix-product` went from 49 G with 2^20 to 68 G with 2^18. A reset of the arena at each query was worse: `grind-ring-5` took 698 G with 2^22.
pub const MAX_NODES: u32 = 1 << 18;

/// The number of values that the regions of one declaration can remove (spec perf/04.3 A4), 2^13. After that, the arena fills as without regions, and engine R checks the declaration.
///
/// The budget is also a limit for engine F on a declaration that it cannot finish. On Init, each check that engine F did not finish with a budget of 2^18 stopped with a full arena after the regions removed all of the budget. Engine F used 3.6 s on these 168 checks before the stop, and engine R then used 3.0 s on them. On Init (one thread, `--engine F`), the run used 264.9 G instructions with 2^18, 257.4 G with 2^17, 251.1 G with 2^15, 249.5 G with 2^13 and 249.1 G with 2^10, and a budget of 2^22 used 303.2 G. With 2^13, engine F gives 281 checks to engine R in place of 168. The 42 Arena perf tests used 525.0 G with 2^18 and 526.2 G with 2^13, and no test changed by more than the noise.
pub const FREE_BUDGET: usize = 1 << 13;

/// The bound of the inline `Nat` numbers of `Value::Small`: 2^63. The sum of two inline numbers fits in a `u64`.
pub const SMALL_NAT_LIMIT: u64 = 1 << 63;

/// The `Value::Small` of `x`, which must be below `SMALL_NAT_LIMIT`.
pub fn small(x: u64) -> Value {
    Value::Small(x as u32, (x >> 32) as u32)
}

/// The number of a `Value::Small`.
pub fn small_get(lo: u32, hi: u32) -> u64 {
    (lo as u64) | ((hi as u64) << 32)
}

/// A closure: the body of a binder and the environment of its free de Bruijn indices.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Closure {
    pub env: EnvId,
    pub body: ExprId,
}

/// The head of a neutral value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Head {
    /// A free variable: its de Bruijn level and its type.
    FVar(u32, ValueId),
    /// A constant that does not unfold: an axiom, an opaque constant, an inductive type, a constructor, a quotient constant or a stuck recursor.
    Const(NameId, LevelListId),
    /// A stuck projection: the structure name, the field index and the value of the structure.
    Proj(NameId, u32, ValueId),
}

/// A value (spec 05.4.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    Sort(LevelId),
    /// A literal. A `Nat` literal of this form is at least `SMALL_NAT_LIMIT`, because a smaller one is a `Value::Small`.
    Lit(Literal),
    /// A `Nat` literal below `SMALL_NAT_LIMIT` as an inline number: the low and the high 32 bits (spec perf/04.8). The `Nat` extension computes on two such numbers with machine arithmetic, and the store does not keep the result.
    Small(u32, u32),
    /// A lambda: the binder name and information, the domain and the body. The name is used only by read-back.
    Lam(NameId, BinderInfo, ValueId, Closure),
    /// A pi type: the binder name and information, the domain and the body.
    Pi(NameId, BinderInfo, ValueId, Closure),
    /// A neutral value: a head and its arguments.
    Neu(Head, SpineId),
    /// A definition applied to its arguments, in folded form, with a slot for its unfolding.
    Glued(NameId, LevelListId, SpineId, SlotId),
    /// An argument that is not evaluated yet: the environment, the term and a slot for its value (spec perf/04.3 A5). The first read evaluates the term and puts the value in the slot, so the term is evaluated at most once. A value of this form is never in weak head normal form: each read of the form of a value goes through `Checker::vget`, which evaluates it first.
    Susp(EnvId, ExprId, SlotId),
    /// The type of a lambda that engine F inference made, before its read-back (spec perf/04.5): the binder name and information, the local `x` of the lambda as a neutral value `FVar(l, d)`, the type of the body as a value under `x`, and a slot for the pi value with a closure. `conv` compares it with a pi type under `x` and makes no new local and no read-back. Each other read goes through `Checker::vget`, which reads the body type back once, as before this form, and keeps the pi value in the slot. So a value of this form is never in weak head normal form either.
    PiOpen(NameId, BinderInfo, ValueId, ValueId, SlotId),
}

#[derive(Clone, Copy, Debug)]
struct EnvNode {
    value: ValueId,
    parent: EnvId,
    len: u32,
    /// The value key of the environment (spec 04.12), or 0 if it is not computed.
    key: u32,
}

#[derive(Clone, Copy, Debug)]
struct SpineNode {
    arg: ValueId,
    parent: SpineId,
    len: u32,
    /// The value key of the spine (spec 04.12), or 0 if it is not computed.
    key: u32,
}

/// The number of nodes in each array of the arena.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    pub values: usize,
    pub envs: usize,
    pub spines: usize,
    pub slots: usize,
}

/// The value arena of one worker.
#[derive(Clone, Debug, Default)]
pub struct Arena {
    values: Vec<Value>,
    /// The value key of each value (spec 04.12), or 0 if it is not computed.
    vkeys: Vec<u32>,
    envs: Vec<EnvNode>,
    spines: Vec<SpineNode>,
    slots: Vec<Option<ValueId>>,
    /// The bits of `f_bits` that the evaluation of a suspended argument set, one entry for each slot. A read of a filled slot sets them again.
    sbits: Vec<u8>,
    full: bool,
    /// True between `mark` and `release` or `unmark`.
    marked: bool,
    /// The number of slots at the mark. A slot below this number that gets a value is put in `log`.
    floor: usize,
    /// The slots older than the mark that got a value after the mark (spec perf/04.3 A4).
    log: Vec<u32>,
    /// The number of values that `release` removed since the last `reset`.
    freed: usize,
}

impl Arena {
    /// An empty arena.
    pub fn new() -> Arena {
        Arena {
            values: Vec::new(),
            vkeys: Vec::new(),
            envs: Vec::new(),
            spines: Vec::new(),
            slots: Vec::new(),
            sbits: Vec::new(),
            full: false,
            marked: false,
            floor: 0,
            log: Vec::new(),
            freed: 0,
        }
    }

    /// True when an array of the arena reached `MAX_NODES`. After that, each new node is the last node of its array, so the caller must stop.
    pub fn full(&self) -> bool {
        self.full
    }

    /// The number of bytes of the arrays, without the allocator overhead.
    pub fn bytes(&self) -> usize {
        self.values.capacity() * core::mem::size_of::<Value>()
            + self.envs.capacity() * core::mem::size_of::<EnvNode>()
            + self.spines.capacity() * core::mem::size_of::<SpineNode>()
            + self.slots.capacity() * core::mem::size_of::<Option<ValueId>>()
            + self.sbits.capacity()
    }

    /// The number of nodes in each array.
    pub fn counts(&self) -> Counts {
        Counts {
            values: self.values.len(),
            envs: self.envs.len(),
            spines: self.spines.len(),
            slots: self.slots.len(),
        }
    }

    /// Removes all nodes. The arrays keep their capacity for the next declaration.
    pub fn reset(&mut self) {
        self.values.truncate(0);
        self.vkeys.truncate(0);
        self.envs.truncate(0);
        self.spines.truncate(0);
        self.slots.truncate(0);
        self.sbits.truncate(0);
        self.full = false;
        self.marked = false;
        self.log.truncate(0);
        self.freed = 0;
    }

    /// Starts a region and gives its mark, or `None` if a region is open already. The nodes made after the mark can be removed with `release` (spec perf/04.3 A4).
    pub fn mark(&mut self) -> Option<Counts> {
        if self.marked || self.full {
            return None;
        }
        self.marked = true;
        self.floor = self.slots.len();
        self.log.truncate(0);
        Some(self.counts())
    }

    /// True if an array of the arena has more than half of `MAX_NODES` nodes. Then a region is released, and else it is kept for its caches.
    pub fn crowded(&self) -> bool {
        let half = (MAX_NODES / 2) as usize;
        if self.freed >= FREE_BUDGET {
            return false;
        }
        self.values.len() > half
            || self.envs.len() > half
            || self.spines.len() > half
            || self.slots.len() > half
    }

    /// Closes the region and keeps its nodes.
    pub fn unmark(&mut self) {
        self.marked = false;
        self.log.truncate(0);
    }

    /// Closes the region and removes the nodes made after the mark `m`. The caller must hold no handle to these nodes. An older slot that got a value of the region becomes empty again, because a slot is a cache of an evaluation. An older slot that got an older value keeps it.
    pub fn release(&mut self, m: Counts) {
        let n = self.log.len();
        let mut i = 0;
        while i < n {
            let s = self.log[i] as usize;
            if let Some(v) = self.slots[s] {
                if v.0 as usize >= m.values {
                    self.slots[s] = None;
                    self.sbits[s] = 0;
                }
            }
            i += 1;
        }
        self.freed += self.values.len() - m.values;
        self.values.truncate(m.values);
        self.vkeys.truncate(m.values);
        self.envs.truncate(m.envs);
        self.spines.truncate(m.spines);
        self.slots.truncate(m.slots);
        self.sbits.truncate(m.slots);
        self.full = false;
        self.unmark();
    }

    /// The index of the next node of an array of length `len`. At the limit it marks the arena full.
    fn next_index(&mut self, len: usize) -> u32 {
        if len >= MAX_NODES as usize {
            self.full = true;
        }
        len as u32
    }

    // Values.

    /// Adds a value.
    pub fn alloc(&mut self, v: Value) -> ValueId {
        if self.full {
            return ValueId(0);
        }
        let i = self.next_index(self.values.len());
        if self.full {
            return ValueId(0);
        }
        self.values.push(v);
        self.vkeys.push(0);
        ValueId(i)
    }

    /// The value key of a value (spec 04.12), or 0 if it is not computed.
    pub fn vkey(&self, v: ValueId) -> u32 {
        self.vkeys[v.0 as usize]
    }

    /// Keeps the value key of a value.
    pub fn set_vkey(&mut self, v: ValueId, k: u32) {
        self.vkeys[v.0 as usize] = k;
    }

    /// The value key of an environment node, or 0 if it is not computed.
    pub fn env_key(&self, e: EnvId) -> u32 {
        self.envs[e.0 as usize].key
    }

    /// Keeps the value key of an environment node.
    pub fn set_env_key(&mut self, e: EnvId, k: u32) {
        self.envs[e.0 as usize].key = k;
    }

    /// The value key of a spine node, or 0 if it is not computed.
    pub fn spine_key(&self, s: SpineId) -> u32 {
        self.spines[s.0 as usize].key
    }

    /// Keeps the value key of a spine node.
    pub fn set_spine_key(&mut self, s: SpineId, k: u32) {
        self.spines[s.0 as usize].key = k;
    }

    /// The value of a handle. The handle must come from this arena after the last `reset`.
    pub fn get(&self, id: ValueId) -> Value {
        self.values[id.0 as usize]
    }

    // Environments.

    /// The environment `env` with `v` added as de Bruijn index 0.
    pub fn env_push(&mut self, env: EnvId, v: ValueId) -> EnvId {
        if self.full {
            return EnvId::NIL;
        }
        let i = self.next_index(self.envs.len());
        if self.full {
            return EnvId::NIL;
        }
        let len = self.env_len(env) + 1;
        self.envs.push(EnvNode {
            value: v,
            parent: env,
            len,
            key: 0,
        });
        EnvId(i)
    }

    /// The number of values in an environment.
    pub fn env_len(&self, env: EnvId) -> u32 {
        if env == EnvId::NIL {
            0
        } else {
            self.envs[env.0 as usize].len
        }
    }

    /// The value of de Bruijn index `idx` in `env`, or `None` if `idx` is not bound in `env`.
    pub fn env_get(&self, env: EnvId, idx: u32) -> Option<ValueId> {
        if idx >= self.env_len(env) {
            return None;
        }
        let mut e = env;
        let mut k = idx;
        while k > 0 {
            e = self.envs[e.0 as usize].parent;
            k -= 1;
        }
        Some(self.envs[e.0 as usize].value)
    }

    /// The value and the parent of an environment node that is not `EnvId::NIL`.
    pub fn env_node(&self, env: EnvId) -> (ValueId, EnvId) {
        let n = self.envs[env.0 as usize];
        (n.value, n.parent)
    }

    // Spines.

    /// The last argument and the parent of a spine node that is not `SpineId::NIL`.
    pub fn spine_node(&self, sp: SpineId) -> (ValueId, SpineId) {
        let n = self.spines[sp.0 as usize];
        (n.arg, n.parent)
    }

    /// The spine `sp` with `arg` added as the last argument.
    pub fn spine_push(&mut self, sp: SpineId, arg: ValueId) -> SpineId {
        if self.full {
            return SpineId::NIL;
        }
        let i = self.next_index(self.spines.len());
        if self.full {
            return SpineId::NIL;
        }
        let len = self.spine_len(sp) + 1;
        self.spines.push(SpineNode {
            arg,
            parent: sp,
            len,
            key: 0,
        });
        SpineId(i)
    }

    /// The number of arguments of a spine.
    pub fn spine_len(&self, sp: SpineId) -> u32 {
        if sp == SpineId::NIL {
            0
        } else {
            self.spines[sp.0 as usize].len
        }
    }

    /// Argument `i` of a spine, where 0 is the first argument, or `None` if the spine is shorter.
    pub fn spine_arg(&self, sp: SpineId, i: u32) -> Option<ValueId> {
        let len = self.spine_len(sp);
        if i >= len {
            return None;
        }
        let mut s = sp;
        let mut k = len - 1 - i;
        while k > 0 {
            s = self.spines[s.0 as usize].parent;
            k -= 1;
        }
        Some(self.spines[s.0 as usize].arg)
    }

    /// Pushes the arguments of a spine on the stack `out`, first argument first, and gives the number of arguments. The stack keeps its capacity, so this makes no allocation when the stack has room (spec perf/04.3 A9).
    pub fn spine_push_args(&self, sp: SpineId, out: &mut Vec<ValueId>) -> usize {
        let len = self.spine_len(sp) as usize;
        let base = out.len();
        let mut i = 0;
        while i < len {
            out.push(ValueId(0));
            i += 1;
        }
        let mut s = sp;
        let mut k = len;
        while k > 0 {
            let n = self.spines[s.0 as usize];
            out[base + k - 1] = n.arg;
            s = n.parent;
            k -= 1;
        }
        len
    }

    // Unfolding slots.

    /// A new empty slot.
    pub fn slot_new(&mut self) -> SlotId {
        if self.full {
            return SlotId(0);
        }
        let i = self.next_index(self.slots.len());
        if self.full {
            return SlotId(0);
        }
        self.slots.push(None);
        self.sbits.push(0);
        SlotId(i)
    }

    /// The bits that `slot_set_bits` put on a slot, or 0.
    pub fn slot_bits(&self, s: SlotId) -> u32 {
        u32::from(self.sbits[s.0 as usize])
    }

    /// Puts the bits `b` on a slot. Only the low 8 bits are kept, and the flags of `f_bits` use fewer.
    pub fn slot_set_bits(&mut self, s: SlotId, b: u32) {
        self.sbits[s.0 as usize] = (b & 0xff) as u8;
    }

    /// The unfolding in a slot, if it was computed.
    pub fn slot_get(&self, s: SlotId) -> Option<ValueId> {
        self.slots[s.0 as usize]
    }

    /// Fills an empty slot and gives true. A slot is filled once (call by need), so on a filled slot it changes nothing and gives false.
    pub fn slot_set(&mut self, s: SlotId, v: ValueId) -> bool {
        let i = s.0 as usize;
        match self.slots[i] {
            Some(_) => false,
            None => {
                self.slots[i] = Some(v);
                if self.marked && i < self.floor {
                    self.log.push(i as u32);
                }
                true
            }
        }
    }

    // Values made from other values.

    /// A neutral value with no arguments.
    pub fn neutral(&mut self, h: Head) -> ValueId {
        self.alloc(Value::Neu(h, SpineId::NIL))
    }

    /// A suspended argument: the term `e` in the environment `env`, with an empty slot.
    pub fn susp(&mut self, env: EnvId, e: ExprId) -> ValueId {
        let s = self.slot_new();
        self.alloc(Value::Susp(env, e, s))
    }

    /// The type of a lambda with the local `x` and the body type `bt`, with an empty slot (see `Value::PiOpen`).
    pub fn pi_open(&mut self, name: NameId, info: BinderInfo, x: ValueId, bt: ValueId) -> ValueId {
        let s = self.slot_new();
        self.alloc(Value::PiOpen(name, info, x, bt, s))
    }

    /// A glued value with no arguments and an empty slot.
    pub fn glued(&mut self, c: NameId, us: LevelListId) -> ValueId {
        let s = self.slot_new();
        self.alloc(Value::Glued(c, us, SpineId::NIL, s))
    }

    /// `v` applied to `arg`, when `v` is neutral or glued. The spine of `v` is shared, not copied. A glued result gets a new empty slot, because its unfolding is not the unfolding of `v`. For other values it gives `None`: the caller does a beta step or reports a type error.
    pub fn apply_stuck(&mut self, v: ValueId, arg: ValueId) -> Option<ValueId> {
        match self.get(v) {
            Value::Neu(h, sp) => {
                let sp2 = self.spine_push(sp, arg);
                Some(self.alloc(Value::Neu(h, sp2)))
            }
            Value::Glued(c, us, sp, _) => {
                let sp2 = self.spine_push(sp, arg);
                let s = self.slot_new();
                Some(self.alloc(Value::Glued(c, us, sp2, s)))
            }
            _ => None,
        }
    }
}
