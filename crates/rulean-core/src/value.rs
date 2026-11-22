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
    Lit(Literal),
    /// A lambda: the binder name and information, the domain and the body. The name is used only by read-back.
    Lam(NameId, BinderInfo, ValueId, Closure),
    /// A pi type: the binder name and information, the domain and the body.
    Pi(NameId, BinderInfo, ValueId, Closure),
    /// A neutral value: a head and its arguments.
    Neu(Head, SpineId),
    /// A definition applied to its arguments, in folded form, with a slot for its unfolding.
    Glued(NameId, LevelListId, SpineId, SlotId),
}

#[derive(Clone, Copy, Debug)]
struct EnvNode {
    value: ValueId,
    parent: EnvId,
    len: u32,
}

#[derive(Clone, Copy, Debug)]
struct SpineNode {
    arg: ValueId,
    parent: SpineId,
    len: u32,
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
    envs: Vec<EnvNode>,
    spines: Vec<SpineNode>,
    slots: Vec<Option<ValueId>>,
    full: bool,
}

impl Arena {
    /// An empty arena.
    pub fn new() -> Arena {
        Arena {
            values: Vec::new(),
            envs: Vec::new(),
            spines: Vec::new(),
            slots: Vec::new(),
            full: false,
        }
    }

    /// True when an array of the arena reached `MAX_NODES`. After that, each new node is the last node of its array, so the caller must stop.
    pub fn full(&self) -> bool {
        self.full
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
        self.envs.truncate(0);
        self.spines.truncate(0);
        self.slots.truncate(0);
        self.full = false;
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
        ValueId(i)
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

    // Spines.

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

    /// The arguments of a spine, first argument first.
    pub fn spine_args(&self, sp: SpineId) -> Vec<ValueId> {
        let len = self.spine_len(sp) as usize;
        let mut out: Vec<ValueId> = Vec::with_capacity(len);
        let mut i = 0;
        while i < len {
            out.push(ValueId(0));
            i += 1;
        }
        let mut s = sp;
        let mut k = len;
        while k > 0 {
            let n = self.spines[s.0 as usize];
            out[k - 1] = n.arg;
            s = n.parent;
            k -= 1;
        }
        out
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
        SlotId(i)
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
                true
            }
        }
    }

    // Values made from other values.

    /// A neutral value with no arguments.
    pub fn neutral(&mut self, h: Head) -> ValueId {
        self.alloc(Value::Neu(h, SpineId::NIL))
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
