//! Primitive pinning (spec 05.8, deviation D1).
//!
//! The official kernel finds the `Nat` and `String` extensions by name only. rulean compares each target declaration of the export with a reference declaration of the profile. The comparison uses a SHA-256 digest of the declaration. The digest ignores binder names and binder info, and it does not look into the constants that the declaration refers to. If the digest is not the reference digest, the extension of the target is off, and the constant unfolds like any other definition.
//!
//! The digest of a node is the SHA-256 of a tag byte and the fields of the node. A field is the 32-byte digest of a child, a `u64` in little-endian order, or a byte string with its length as a `u64` before it. `scripts/pin-digests.py` computes the same digests from an export.

use alloc::vec::Vec;
use rulean_format::Safety;
use rulean_store::{Expr, ExprId, Level, LevelId, LevelListId, Literal, Name, NameId, Store};

use crate::env::ConstKind;
use crate::memo::Memo;
use crate::sha256::sha256;
use crate::tc::{Checker, dotted_name};

/// The bit of the `Nat` group: the literal to constructor conversion, the offset rule and all `Nat` operations. Bits 0 to 13 are the binary operations, in the order of the `nat_ops` table.
pub const PIN_NAT: u32 = 1 << 14;
/// The bit of the `String` group: the string literal to constructor conversion.
pub const PIN_STRING: u32 = 1 << 15;
/// The bit of the `eagerReduce` hint.
pub const PIN_EAGER: u32 = 1 << 16;

/// The number of pinned declarations.
pub const TARGET_COUNT: usize = 21;

/// The handles of the target names, in the order of `TARGET_REF`. A name is a list of parts, separated by a dot. The names are literals in the calls and not a global array, because Aeneas does not translate a global array of byte strings.
pub(crate) fn target_names(st: &mut Store) -> Vec<NameId> {
    let mut v = Vec::with_capacity(TARGET_COUNT);
    let n = dotted_name(st, b"Nat");
    v.push(n);
    let n = dotted_name(st, b"Nat.add");
    v.push(n);
    let n = dotted_name(st, b"Nat.sub");
    v.push(n);
    let n = dotted_name(st, b"Nat.mul");
    v.push(n);
    let n = dotted_name(st, b"Nat.pow");
    v.push(n);
    let n = dotted_name(st, b"Nat.gcd");
    v.push(n);
    let n = dotted_name(st, b"Nat.mod");
    v.push(n);
    let n = dotted_name(st, b"Nat.div");
    v.push(n);
    let n = dotted_name(st, b"Nat.beq");
    v.push(n);
    let n = dotted_name(st, b"Nat.ble");
    v.push(n);
    let n = dotted_name(st, b"Nat.land");
    v.push(n);
    let n = dotted_name(st, b"Nat.lor");
    v.push(n);
    let n = dotted_name(st, b"Nat.xor");
    v.push(n);
    let n = dotted_name(st, b"Nat.shiftLeft");
    v.push(n);
    let n = dotted_name(st, b"Nat.shiftRight");
    v.push(n);
    let n = dotted_name(st, b"String");
    v.push(n);
    let n = dotted_name(st, b"String.ofList");
    v.push(n);
    let n = dotted_name(st, b"Char");
    v.push(n);
    let n = dotted_name(st, b"Char.ofNat");
    v.push(n);
    let n = dotted_name(st, b"List");
    v.push(n);
    let n = dotted_name(st, b"eagerReduce");
    v.push(n);
    v
}

/// The reference digests of the `v4.35` profile, from the exports of the Lean v4.36.0 prelude. `scripts/pin-digests.py` gives these values.
pub const TARGET_REF: [[u8; 32]; TARGET_COUNT] = include!("pin_ref_v4_35.in");

/// The extension bit that a mismatch of target `i` turns off.
pub fn target_bit(i: usize) -> u32 {
    if i == 0 {
        PIN_NAT
    } else if i <= 14 {
        1 << (i - 1)
    } else if i <= 19 {
        PIN_STRING
    } else {
        PIN_EAGER
    }
}

const K_NAME: u32 = 1;
const K_LEVEL: u32 = 2;
const K_EXPR: u32 = 3;

/// The digest depth bound. A deeper term is a mismatch.
const MAX_DEPTH: u32 = 10_000;

/// The digest state: the digests computed so far, keyed by the handle and the kind of the handle.
#[derive(Debug)]
pub struct Digest {
    memo: Memo,
    out: Vec<[u8; 32]>,
    depth: u32,
    /// True if a term was deeper than `MAX_DEPTH`.
    pub deep: bool,
}

impl Default for Digest {
    fn default() -> Digest {
        Digest::new()
    }
}

fn push_bytes(m: &mut Vec<u8>, b: &[u8]) {
    let mut i = 0;
    while i < b.len() {
        m.push(b[i]);
        i += 1;
    }
}

fn push_u64(m: &mut Vec<u8>, v: u64) {
    let mut k = 0;
    while k < 8 {
        m.push(((v >> (8 * k)) & 0xff) as u8);
        k += 1;
    }
}

fn push_str(m: &mut Vec<u8>, b: &[u8]) {
    push_u64(m, b.len() as u64);
    push_bytes(m, b);
}

impl Digest {
    /// An empty state.
    pub fn new() -> Digest {
        Digest {
            memo: Memo::new(),
            out: Vec::new(),
            depth: 0,
            deep: false,
        }
    }

    fn remember(&mut self, id: u32, kind: u32, h: [u8; 32]) -> [u8; 32] {
        let i = self.out.len() as u32;
        self.out.push(h);
        self.memo.put(id, kind, i);
        h
    }

    /// The digest of a name.
    pub fn name(&mut self, st: &Store, n: NameId) -> [u8; 32] {
        if let Some(i) = self.memo.get(n.0, K_NAME) {
            return self.out[i as usize];
        }
        let mut m: Vec<u8> = Vec::new();
        match st.name(n) {
            Name::Anon => m.push(0x01),
            Name::Str(pre, s) => {
                m.push(0x02);
                let p = self.name(st, pre);
                push_bytes(&mut m, &p);
                push_str(&mut m, st.str_bytes(s));
            }
            Name::Num(pre, k) => {
                m.push(0x03);
                let p = self.name(st, pre);
                push_bytes(&mut m, &p);
                push_u64(&mut m, k);
            }
        }
        let h = sha256(&m);
        self.remember(n.0, K_NAME, h)
    }

    /// The digest of a level.
    pub fn level(&mut self, st: &Store, l: LevelId) -> [u8; 32] {
        if let Some(i) = self.memo.get(l.0, K_LEVEL) {
            return self.out[i as usize];
        }
        let mut m: Vec<u8> = Vec::new();
        match st.level(l) {
            Level::Zero => m.push(0x08),
            Level::Succ(a) => {
                m.push(0x09);
                let x = self.level(st, a);
                push_bytes(&mut m, &x);
            }
            Level::Max(a, b) => {
                m.push(0x0a);
                let x = self.level(st, a);
                push_bytes(&mut m, &x);
                let y = self.level(st, b);
                push_bytes(&mut m, &y);
            }
            Level::IMax(a, b) => {
                m.push(0x0b);
                let x = self.level(st, a);
                push_bytes(&mut m, &x);
                let y = self.level(st, b);
                push_bytes(&mut m, &y);
            }
            Level::Param(n) => {
                m.push(0x0c);
                let x = self.name(st, n);
                push_bytes(&mut m, &x);
            }
        }
        let h = sha256(&m);
        self.remember(l.0, K_LEVEL, h)
    }

    fn levels(&mut self, st: &Store, m: &mut Vec<u8>, ls: LevelListId) {
        let items = st.level_list_vec(ls);
        push_u64(m, items.len() as u64);
        let mut i = 0;
        while i < items.len() {
            let x = self.level(st, items[i]);
            push_bytes(m, &x);
            i += 1;
        }
    }

    fn child(&mut self, st: &Store, m: &mut Vec<u8>, e: ExprId) {
        let x = self.expr(st, e);
        push_bytes(m, &x);
    }

    /// The digest of an expression. A free variable has no digest of its own, because a declaration has none.
    pub fn expr(&mut self, st: &Store, e: ExprId) -> [u8; 32] {
        if let Some(i) = self.memo.get(e.0, K_EXPR) {
            return self.out[i as usize];
        }
        if self.depth >= MAX_DEPTH {
            self.deep = true;
            return [0u8; 32];
        }
        self.depth += 1;
        let mut m: Vec<u8> = Vec::new();
        match st.node(e) {
            Expr::BVar(i) => {
                m.push(0x10);
                push_u64(&mut m, i as u64);
            }
            Expr::Sort(l) => {
                m.push(0x11);
                let x = self.level(st, l);
                push_bytes(&mut m, &x);
            }
            Expr::Const(n, ls) => {
                m.push(0x12);
                let x = self.name(st, n);
                push_bytes(&mut m, &x);
                self.levels(st, &mut m, ls);
            }
            Expr::App(f, a) => {
                m.push(0x13);
                self.child(st, &mut m, f);
                self.child(st, &mut m, a);
            }
            Expr::Lam(b) => {
                m.push(0x14);
                self.child(st, &mut m, b.dom);
                self.child(st, &mut m, b.body);
            }
            Expr::Pi(b) => {
                m.push(0x15);
                self.child(st, &mut m, b.dom);
                self.child(st, &mut m, b.body);
            }
            Expr::Let(x) => {
                m.push(0x16);
                self.child(st, &mut m, x.ty);
                self.child(st, &mut m, x.value);
                self.child(st, &mut m, x.body);
            }
            Expr::Lit(Literal::Nat(n)) => {
                m.push(0x17);
                let v = st.nat(n);
                let mut b: Vec<u8> = Vec::new();
                let mut i = 0;
                while i < v.limb_count() {
                    push_u64(&mut b, v.limb(i));
                    i += 1;
                }
                while b.len() > 0 && b[b.len() - 1] == 0 {
                    b.pop();
                }
                push_str(&mut m, &b);
            }
            Expr::Lit(Literal::Str(s)) => {
                m.push(0x18);
                push_str(&mut m, st.str_bytes(s));
            }
            Expr::Proj(p) => {
                m.push(0x19);
                let x = self.name(st, p.struct_name);
                push_bytes(&mut m, &x);
                push_u64(&mut m, p.index as u64);
                self.child(st, &mut m, p.expr);
            }
            Expr::FVar(..) => {
                m.push(0x1f);
            }
        }
        self.depth -= 1;
        let h = sha256(&m);
        self.remember(e.0, K_EXPR, h)
    }

    fn lparams(&mut self, st: &Store, m: &mut Vec<u8>, ls: &[NameId]) {
        push_u64(m, ls.len() as u64);
        let mut i = 0;
        while i < ls.len() {
            let x = self.name(st, ls[i]);
            push_bytes(m, &x);
            i += 1;
        }
    }
}

impl Checker {
    /// The digest of the constant at slot `s` of the environment, or `None` if the constant cannot be a pinned primitive: an unsafe or partial constant, or a constant that is not a definition or an inductive type.
    fn pin_digest(&self, d: &mut Digest, s: u32) -> Option<[u8; 32]> {
        let c = self.env.at(s);
        if c.safety != Safety::Safe {
            return None;
        }
        let mut m: Vec<u8> = Vec::new();
        match &c.kind {
            ConstKind::Defn { value, .. } => {
                m.push(0x20);
                d.lparams(&self.st, &mut m, &c.lparams);
                let t = d.expr(&self.st, c.ty);
                push_bytes(&mut m, &t);
                let v = d.expr(&self.st, *value);
                push_bytes(&mut m, &v);
            }
            ConstKind::Induct(info) => {
                m.push(0x21);
                d.lparams(&self.st, &mut m, &c.lparams);
                let t = d.expr(&self.st, c.ty);
                push_bytes(&mut m, &t);
                push_u64(&mut m, info.nparams as u64);
                push_u64(&mut m, info.nindices as u64);
                push_u64(&mut m, info.ctors.len() as u64);
                let mut i = 0;
                while i < info.ctors.len() {
                    let cn = d.name(&self.st, info.ctors[i]);
                    push_bytes(&mut m, &cn);
                    let ct = self.env.at(self.env.find(info.ctors[i])).ty;
                    let x = d.expr(&self.st, ct);
                    push_bytes(&mut m, &x);
                    i += 1;
                }
            }
            _ => return None,
        }
        if d.deep {
            return None;
        }
        Some(sha256(&m))
    }

    /// Compares each target that the environment has now, and that is not compared yet, with its reference. A mismatch turns the extension of the target off (deviation D1). With `trust_primitives` the extensions stay on, as in the official kernel.
    pub fn check_pins(&mut self) {
        let mut i = 0;
        while i < TARGET_COUNT {
            let n = self.b.pin_names[i];
            if self.pin_done & (1 << i) == 0 && self.env.contains(n) {
                self.pin_done |= 1 << i;
                let mut d = Digest::new();
                let ok = match self.pin_digest(&mut d, self.env.find(n)) {
                    Some(h) => h == TARGET_REF[i],
                    None => false,
                };
                if !ok {
                    self.pin_mismatch.push(n);
                    if !self.trust_primitives {
                        self.pin_off |= target_bit(i);
                    }
                }
            }
            i += 1;
        }
    }

    /// True if the extension with bit `bit` is on.
    pub(crate) fn pin_on(&self, bit: u32) -> bool {
        self.pin_off & bit == 0
    }
}
