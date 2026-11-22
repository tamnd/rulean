//! The decoder of the rulean binary format, `.rlb` (spec 07.2).
//!
//! The format is a cache of an NDJSON export, not a new source of truth. The decoder reads the tables in one forward pass. Each index must refer to an item that the decoder already read, and each section must have the CRC-32C of its directory entry. The decoder makes every node again with the constructors of the store, so the store computes all hashes and flags. It never reads them from the file.
//!
//! `rulean-pack` writes the format. The constants of this module give the layout to both sides.

use alloc::vec::Vec;
use rulean_nat::Nat;
use rulean_store::{BinderInfo, ExprId, LevelId, LevelListId, NameId, NatId, Store, StrId};

use crate::crc::crc32c;
use crate::decl::{
    Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Opaque, Quot, QuotKind, Rec, RecRule,
    Safety, Thm,
};
use crate::error::{Error, ErrorKind};
use crate::json::utf8_valid;
use crate::ndjson::{MAX_NAT_BITS, MAX_TABLE_INDEX};

/// The first 8 bytes of a `.rlb` file.
pub const MAGIC: [u8; 8] = *b"RULEANB\0";
/// The format version that this decoder reads.
pub const VERSION: u32 = 1;
/// The size of the header, in bytes.
pub const HEADER_BYTES: usize = 128;
/// The size of one entry of the section directory, in bytes.
pub const DIR_BYTES: usize = 32;
/// The size of the Lean version field of the header.
pub const LEAN_VERSION_BYTES: usize = 32;
/// The size of the Lean githash field of the header.
pub const GITHASH_BYTES: usize = 40;

/// Section kinds.
pub const SEC_STRINGS: u32 = 1;
pub const SEC_NAMES: u32 = 2;
pub const SEC_LEVELS: u32 = 3;
pub const SEC_EXPRS: u32 = 4;
pub const SEC_NATS: u32 = 5;
pub const SEC_DECLS: u32 = 6;
pub const SEC_DEPS: u32 = 7;

/// The size of a record of the NAMES section: tag u8, three zero bytes, prefix u32, payload u64.
pub const NAME_BYTES: usize = 16;
/// The size of a record of the LEVELS section: tag u8, three zero bytes, two operands u32.
pub const LEVEL_BYTES: usize = 12;

/// Tags of the NAMES section.
pub const N_STR: u8 = 1;
pub const N_NUM: u8 = 2;

/// Tags of the LEVELS section.
pub const L_SUCC: u8 = 1;
pub const L_MAX: u8 = 2;
pub const L_IMAX: u8 = 3;
pub const L_PARAM: u8 = 4;

/// Tags of the EXPRS section. The tag is the low byte of the first word of a record. For a binder, the next byte is the binder information.
pub const E_BVAR: u32 = 0;
pub const E_SORT: u32 = 1;
pub const E_CONST: u32 = 2;
pub const E_APP: u32 = 3;
pub const E_LAM: u32 = 4;
pub const E_PI: u32 = 5;
pub const E_LET: u32 = 6;
pub const E_NAT: u32 = 7;
pub const E_STR: u32 = 8;
pub const E_PROJ: u32 = 9;

/// Tags of the DECLS section.
pub const D_AXIOM: u32 = 1;
pub const D_DEFN: u32 = 2;
pub const D_THM: u32 = 3;
pub const D_OPAQUE: u32 = 4;
pub const D_QUOT: u32 = 5;
pub const D_INDUCT: u32 = 6;

/// The required sections, in the order of decoding. A table refers only to tables before it in this list.
pub const ORDER: [u32; 6] = [
    SEC_STRINGS,
    SEC_NAMES,
    SEC_LEVELS,
    SEC_NATS,
    SEC_EXPRS,
    SEC_DECLS,
];

/// The fields of the header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub version: u32,
    pub flags: u32,
    /// The Lean version of the source export, without the zero padding.
    pub lean_version: Vec<u8>,
    /// The Lean githash of the source export, without the zero padding.
    pub githash: Vec<u8>,
    pub profile: u32,
    pub sections: u32,
    /// The SHA-256 digest of the source export.
    pub source_sha256: [u8; 32],
}

/// One entry of the section directory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Section {
    pub kind: u32,
    pub offset: u64,
    pub length: u64,
    pub count: u64,
    pub crc: u32,
}

/// A decoded file: the header and the declarations in file order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binary {
    pub header: Header,
    pub decls: Vec<Decl>,
}

/// True if `b` starts with the magic of the binary format.
pub fn is_binary(b: &[u8]) -> bool {
    let mut ok = b.len() >= MAGIC.len();
    let mut i = 0;
    while ok && i < MAGIC.len() {
        ok = b[i] == MAGIC[i];
        i += 1;
    }
    ok
}

fn u32_at(b: &[u8], p: usize) -> u32 {
    u32::from_le_bytes([b[p], b[p + 1], b[p + 2], b[p + 3]])
}

fn u64_at(b: &[u8], p: usize) -> u64 {
    u64::from_le_bytes([
        b[p],
        b[p + 1],
        b[p + 2],
        b[p + 3],
        b[p + 4],
        b[p + 5],
        b[p + 6],
        b[p + 7],
    ])
}

fn fail<T>(kind: ErrorKind) -> Result<T, Error> {
    Err(Error { line: 0, kind })
}

/// The text of a zero-padded field: the bytes before the first zero byte. The second result is false if a byte after the first zero byte is not zero, or if the text is not valid UTF-8.
fn padded(b: &[u8], start: usize, len: usize) -> (Vec<u8>, bool) {
    let mut out = Vec::with_capacity(len);
    let mut ended = false;
    let mut ok = true;
    let mut i = start;
    while i < start + len {
        if b[i] == 0 {
            ended = true;
        } else if ended {
            ok = false;
        } else {
            out.push(b[i]);
        }
        i += 1;
    }
    ok = ok && utf8_valid(&out);
    (out, ok)
}

/// Reads and checks the header.
pub fn header(b: &[u8]) -> Result<Header, Error> {
    if !is_binary(b) {
        return fail(ErrorKind::BadBinary);
    }
    if b.len() < HEADER_BYTES {
        return fail(ErrorKind::BadBinary);
    }
    let version = u32_at(b, 8);
    let flags = u32_at(b, 12);
    let profile = u32_at(b, 88);
    if version != VERSION || flags != 0 || profile != 0 {
        return fail(ErrorKind::UnknownVersion);
    }
    let (lean_version, ok1) = padded(b, 16, LEAN_VERSION_BYTES);
    let (githash, ok2) = padded(b, 16 + LEAN_VERSION_BYTES, GITHASH_BYTES);
    if !ok1 || !ok2 {
        return fail(ErrorKind::BadBinary);
    }
    let mut source_sha256 = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        source_sha256[i] = b[96 + i];
        i += 1;
    }
    Ok(Header {
        version,
        flags,
        lean_version,
        githash,
        profile,
        sections: u32_at(b, 92),
        source_sha256,
    })
}

/// Reads and checks the section directory. Each section must be in the file, start at an 8-byte boundary and have its checksum. Each required kind must be there one time. A DEPS section is allowed. It is a hint, and this decoder does not read it.
pub fn sections(b: &[u8], h: &Header) -> Result<Vec<Section>, Error> {
    let n = h.sections as usize;
    if n > 16 || b.len() < HEADER_BYTES + n * DIR_BYTES {
        return fail(ErrorKind::BadBinary);
    }
    let mut out = Vec::with_capacity(n);
    let mut seen: [u32; 8] = [0; 8];
    let mut bad = false;
    let mut sum = false;
    let mut i = 0;
    while i < n && !bad && !sum {
        let p = HEADER_BYTES + i * DIR_BYTES;
        let s = Section {
            kind: u32_at(b, p),
            offset: u64_at(b, p + 4),
            length: u64_at(b, p + 12),
            count: u64_at(b, p + 20),
            crc: u32_at(b, p + 28),
        };
        let len = b.len() as u64;
        bad = s.kind == 0
            || s.kind > SEC_DEPS
            || !s.offset.is_multiple_of(8)
            || s.offset < (HEADER_BYTES + n * DIR_BYTES) as u64
            || s.offset > len
            || s.length > len - s.offset;
        if !bad {
            seen[s.kind as usize] += 1;
            bad = seen[s.kind as usize] > 1;
        }
        if !bad {
            sum = crc32c(b, s.offset as usize, (s.offset + s.length) as usize) != s.crc;
        }
        out.push(s);
        i += 1;
    }
    let mut k = 0;
    while k < ORDER.len() && !bad {
        bad = seen[ORDER[k] as usize] != 1;
        k += 1;
    }
    if sum {
        fail(ErrorKind::BadChecksum)
    } else if bad {
        fail(ErrorKind::BadBinary)
    } else {
        Ok(out)
    }
}

/// The entry of kind `kind`. `sections` has checked that it is there.
fn find(secs: &[Section], kind: u32) -> Section {
    let mut i = 0;
    let mut at = 0;
    while i < secs.len() {
        if secs[i].kind == kind {
            at = i;
        }
        i += 1;
    }
    secs[at]
}

/// The state of a decode: the cursor in the current section and the map from file indices to store handles for each table.
struct Decoder {
    pos: usize,
    end: usize,
    fault: Option<ErrorKind>,
    strs: Vec<StrId>,
    names: Vec<NameId>,
    levels: Vec<LevelId>,
    nats: Vec<NatId>,
    exprs: Vec<ExprId>,
    lv: Vec<LevelId>,
}

impl Decoder {
    fn ok(&self) -> bool {
        match self.fault {
            None => true,
            Some(_) => false,
        }
    }

    fn fail(&mut self, kind: ErrorKind) {
        if self.ok() {
            self.fault = Some(kind);
        }
    }

    /// Starts section `s`. The second argument is the smallest size of one item, so that a wrong count cannot make a large allocation.
    fn start(&mut self, s: Section, min_item: u64) -> usize {
        self.pos = s.offset as usize;
        self.end = (s.offset + s.length) as usize;
        if s.count > MAX_TABLE_INDEX {
            self.fail(ErrorKind::IndexLimit);
            0
        } else if s.count * min_item > s.length {
            self.fail(ErrorKind::BadBinary);
            0
        } else {
            s.count as usize
        }
    }

    /// Ends a section. All of its bytes must be read.
    fn finish(&mut self) {
        if self.ok() && self.pos != self.end {
            self.fail(ErrorKind::BadBinary);
        }
    }

    fn byte(&mut self, b: &[u8]) -> u8 {
        if self.pos < self.end {
            self.pos += 1;
            b[self.pos - 1]
        } else {
            self.fail(ErrorKind::BadBinary);
            0
        }
    }

    fn word(&mut self, b: &[u8]) -> u32 {
        if self.pos + 4 <= self.end {
            self.pos += 4;
            u32_at(b, self.pos - 4)
        } else {
            self.fail(ErrorKind::BadBinary);
            0
        }
    }

    fn long(&mut self, b: &[u8]) -> u64 {
        if self.pos + 8 <= self.end {
            self.pos += 8;
            u64_at(b, self.pos - 8)
        } else {
            self.fail(ErrorKind::BadBinary);
            0
        }
    }

    /// Reads a field that must be zero.
    fn zero_bytes(&mut self, b: &[u8], n: usize) {
        let mut i = 0;
        while i < n {
            if self.byte(b) != 0 {
                self.fail(ErrorKind::BadBinary);
            }
            i += 1;
        }
    }

    fn str_ref(&mut self, i: u64) -> StrId {
        if i < self.strs.len() as u64 {
            self.strs[i as usize]
        } else {
            self.fail(ErrorKind::UndefinedIndex);
            StrId(0)
        }
    }

    fn name(&mut self, b: &[u8]) -> NameId {
        let i = self.word(b) as usize;
        if i < self.names.len() {
            self.names[i]
        } else {
            self.fail(ErrorKind::UndefinedIndex);
            NameId(0)
        }
    }

    fn level(&mut self, b: &[u8]) -> LevelId {
        let i = self.word(b) as usize;
        if i < self.levels.len() {
            self.levels[i]
        } else {
            self.fail(ErrorKind::UndefinedIndex);
            LevelId(0)
        }
    }

    fn expr(&mut self, b: &[u8]) -> ExprId {
        let i = self.word(b) as usize;
        if i < self.exprs.len() {
            self.exprs[i]
        } else {
            self.fail(ErrorKind::UndefinedIndex);
            ExprId(0)
        }
    }

    /// A count of items of at least `size` bytes each that follow in the section.
    fn count(&mut self, b: &[u8], size: usize) -> usize {
        let n = self.word(b) as usize;
        if self.ok() && n > (self.end - self.pos) / size {
            self.fail(ErrorKind::BadBinary);
            0
        } else {
            n
        }
    }

    fn strings(&mut self, store: &mut Store, b: &[u8], s: Section) {
        let n = self.start(s, 4);
        let mut data = self.pos + 4 * n;
        let mut i = 0;
        while i < n && self.ok() {
            let len = self.word(b) as usize;
            if len > self.end - data {
                self.fail(ErrorKind::BadBinary);
            } else if !utf8_valid(&b[data..data + len]) {
                self.fail(ErrorKind::BadUtf8);
            } else {
                let id = store.intern_str(&b[data..data + len]);
                self.strs.push(id);
                data += len;
            }
            i += 1;
        }
        if self.ok() {
            self.pos = data;
        }
        self.finish();
    }

    fn name_table(&mut self, store: &mut Store, b: &[u8], s: Section) {
        let n = self.start(s, NAME_BYTES as u64);
        self.names = Vec::with_capacity(n + 1);
        self.names.push(store.anon());
        let mut i = 0;
        while i < n && self.ok() {
            let tag = self.byte(b);
            self.zero_bytes(b, 3);
            let pre = self.name(b);
            let payload = self.long(b);
            let mut id = NameId(0);
            if tag == N_STR {
                let sid = self.str_ref(payload);
                if self.ok() {
                    id = store.name_str(pre, sid);
                }
            } else if tag == N_NUM {
                if self.ok() {
                    id = store.name_num(pre, payload);
                }
            } else {
                self.fail(ErrorKind::BadEnumValue);
            }
            self.names.push(id);
            i += 1;
        }
        self.finish();
    }

    fn level_table(&mut self, store: &mut Store, b: &[u8], s: Section) {
        let n = self.start(s, LEVEL_BYTES as u64);
        self.levels = Vec::with_capacity(n + 1);
        self.levels.push(store.level_zero());
        let mut i = 0;
        while i < n && self.ok() {
            let tag = self.byte(b);
            self.zero_bytes(b, 3);
            let mut id = LevelId(0);
            match tag {
                L_SUCC => {
                    let a = self.level(b);
                    if self.word(b) != 0 {
                        self.fail(ErrorKind::BadBinary);
                    }
                    if self.ok() {
                        id = store.level_succ(a);
                    }
                }
                L_MAX | L_IMAX => {
                    let x = self.level(b);
                    let y = self.level(b);
                    if self.ok() {
                        id = if tag == L_MAX {
                            store.level_max(x, y)
                        } else {
                            store.level_imax(x, y)
                        };
                    }
                }
                L_PARAM => {
                    let p = self.name(b);
                    if self.word(b) != 0 {
                        self.fail(ErrorKind::BadBinary);
                    }
                    if self.ok() {
                        id = store.level_param(p);
                    }
                }
                _ => self.fail(ErrorKind::BadEnumValue),
            }
            self.levels.push(id);
            i += 1;
        }
        self.finish();
    }

    fn nat_table(&mut self, store: &mut Store, b: &[u8], s: Section) {
        let n = self.start(s, 8);
        self.nats = Vec::with_capacity(n);
        let mut i = 0;
        while i < n && self.ok() {
            let k = self.word(b) as usize;
            if self.word(b) != 0 {
                self.fail(ErrorKind::BadBinary);
            }
            if self.ok() && k > (self.end - self.pos) / 8 {
                self.fail(ErrorKind::BadBinary);
            }
            if self.ok() && k as u64 > MAX_NAT_BITS / 64 {
                self.fail(ErrorKind::NatTooLarge);
            }
            let mut limbs = Vec::with_capacity(k);
            let mut j = 0;
            while j < k && self.ok() {
                let x = self.long(b);
                limbs.push(x);
                j += 1;
            }
            // The top limb must not be zero, so that each number has one form.
            if self.ok() && k > 0 && limbs[k - 1] == 0 {
                self.fail(ErrorKind::BadNatLiteral);
            }
            if self.ok() {
                let v = Nat::from_limbs(limbs);
                if v.bits() > MAX_NAT_BITS {
                    self.fail(ErrorKind::NatTooLarge);
                }
                let id = store.intern_nat(v);
                self.nats.push(id);
            }
            i += 1;
        }
        self.finish();
    }

    fn level_list(&mut self, store: &mut Store, b: &[u8]) -> LevelListId {
        let k = self.count(b, 4);
        self.lv.truncate(0);
        let mut j = 0;
        while j < k && self.ok() {
            let l = self.level(b);
            self.lv.push(l);
            j += 1;
        }
        if self.ok() {
            store.level_list(&self.lv)
        } else {
            LevelListId(0)
        }
    }

    fn binder_info(&mut self, x: u32) -> BinderInfo {
        match x {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                BinderInfo::Default
            }
        }
    }

    fn expr_table(&mut self, store: &mut Store, b: &[u8], s: Section) {
        let n = self.start(s, 8);
        self.exprs = Vec::with_capacity(n);
        let mut i = 0;
        while i < n && self.ok() {
            let id = self.expr_node(store, b);
            if self.ok() && store.is_full() {
                self.fail(ErrorKind::StoreFull);
            }
            self.exprs.push(id);
            i += 1;
        }
        self.finish();
    }

    fn expr_node(&mut self, store: &mut Store, b: &[u8]) -> ExprId {
        let w = self.word(b);
        let tag = w & 0xff;
        let extra = w >> 8;
        if tag != E_LAM && tag != E_PI && extra != 0 {
            self.fail(ErrorKind::BadBinary);
        }
        let mut id = ExprId(0);
        match tag {
            E_BVAR => {
                let i = self.word(b);
                if self.ok() {
                    id = store.mk_bvar(i);
                }
            }
            E_SORT => {
                let l = self.level(b);
                if self.ok() {
                    id = store.mk_sort(l);
                }
            }
            E_CONST => {
                let c = self.name(b);
                let ls = self.level_list(store, b);
                if self.ok() {
                    id = store.mk_const(c, ls);
                }
            }
            E_APP => {
                let f = self.expr(b);
                let a = self.expr(b);
                if self.ok() {
                    id = store.mk_app(f, a);
                }
            }
            E_LAM | E_PI => {
                let info = self.binder_info(extra);
                let x = self.name(b);
                let dom = self.expr(b);
                let body = self.expr(b);
                if self.ok() {
                    id = if tag == E_LAM {
                        store.mk_lam(x, info, dom, body)
                    } else {
                        store.mk_pi(x, info, dom, body)
                    };
                }
            }
            E_LET => {
                let x = self.name(b);
                let ty = self.expr(b);
                let v = self.expr(b);
                let body = self.expr(b);
                if self.ok() {
                    id = store.mk_let(x, ty, v, body);
                }
            }
            E_NAT => {
                let k = self.word(b) as usize;
                if k < self.nats.len() {
                    id = store.mk_nat_lit(self.nats[k]);
                } else {
                    self.fail(ErrorKind::UndefinedIndex);
                }
            }
            E_STR => {
                let k = self.word(b) as u64;
                let sid = self.str_ref(k);
                if self.ok() {
                    id = store.mk_str_lit(sid);
                }
            }
            E_PROJ => {
                let x = self.name(b);
                let i = self.word(b);
                let e = self.expr(b);
                if self.ok() {
                    id = store.mk_proj(x, i, e);
                }
            }
            _ => self.fail(ErrorKind::BadEnumValue),
        }
        id
    }

    fn names_list(&mut self, b: &[u8]) -> Vec<NameId> {
        let k = self.count(b, 4);
        let mut out = Vec::with_capacity(k);
        let mut j = 0;
        while j < k && self.ok() {
            let x = self.name(b);
            out.push(x);
            j += 1;
        }
        out
    }

    fn number(&mut self, b: &[u8]) -> u32 {
        self.word(b)
    }

    fn boolean(&mut self, b: &[u8]) -> bool {
        match self.word(b) {
            0 => false,
            1 => true,
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                false
            }
        }
    }

    /// A safety field. NDJSON gives `partial` only for definitions, so the other kinds accept 0 (safe) and 1 (unsafe) only.
    fn safety(&mut self, b: &[u8], partial: bool) -> Safety {
        let x = self.word(b);
        match x {
            0 => Safety::Safe,
            1 => Safety::Unsafe,
            2 => {
                if !partial {
                    self.fail(ErrorKind::BadEnumValue);
                }
                Safety::Partial
            }
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                Safety::Safe
            }
        }
    }

    fn hints(&mut self, b: &[u8]) -> Hints {
        match self.word(b) {
            0 => Hints::Opaque,
            1 => Hints::Abbrev,
            2 => Hints::Regular(self.word(b)),
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                Hints::Opaque
            }
        }
    }

    fn quot_kind(&mut self, b: &[u8]) -> QuotKind {
        match self.word(b) {
            0 => QuotKind::Type,
            1 => QuotKind::Ctor,
            2 => QuotKind::Lift,
            3 => QuotKind::Ind,
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                QuotKind::Type
            }
        }
    }

    fn decl_table(&mut self, b: &[u8], s: Section) -> Vec<Decl> {
        let n = self.start(s, 4);
        let mut out = Vec::with_capacity(n);
        let mut i = 0;
        while i < n && self.ok() {
            let d = self.decl(b);
            if self.ok() {
                out.push(d);
            }
            i += 1;
        }
        self.finish();
        out
    }

    fn decl(&mut self, b: &[u8]) -> Decl {
        let tag = self.word(b);
        match tag {
            D_AXIOM => Decl::Axiom(Axiom {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                safety: self.safety(b, false),
            }),
            D_DEFN => Decl::Defn(Defn {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                value: self.expr(b),
                hints: self.hints(b),
                safety: self.safety(b, true),
                all: self.names_list(b),
            }),
            D_THM => Decl::Thm(Thm {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                value: self.expr(b),
                all: self.names_list(b),
            }),
            D_OPAQUE => Decl::Opaque(Opaque {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                value: self.expr(b),
                safety: self.safety(b, false),
                all: self.names_list(b),
            }),
            D_QUOT => Decl::Quot(Quot {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                kind: self.quot_kind(b),
            }),
            D_INDUCT => Decl::Induct(self.inductive(b)),
            _ => {
                self.fail(ErrorKind::BadEnumValue);
                Decl::Quot(Quot {
                    name: NameId(0),
                    lparams: Vec::new(),
                    ty: ExprId(0),
                    kind: QuotKind::Type,
                })
            }
        }
    }

    fn inductive(&mut self, b: &[u8]) -> Induct {
        let nt = self.count(b, 4);
        let nc = self.count(b, 4);
        let nr = self.count(b, 4);
        let mut d = Induct {
            types: Vec::with_capacity(nt),
            ctors: Vec::with_capacity(nc),
            recs: Vec::with_capacity(nr),
        };
        let mut i = 0;
        while i < nt && self.ok() {
            let t = InductType {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                num_params: self.number(b),
                num_indices: self.number(b),
                all: self.names_list(b),
                ctors: self.names_list(b),
                num_nested: self.number(b),
                is_rec: self.boolean(b),
                is_reflexive: self.boolean(b),
                safety: self.safety(b, false),
            };
            d.types.push(t);
            i += 1;
        }
        i = 0;
        while i < nc && self.ok() {
            let c = Ctor {
                name: self.name(b),
                lparams: self.names_list(b),
                ty: self.expr(b),
                induct: self.name(b),
                cidx: self.number(b),
                num_params: self.number(b),
                num_fields: self.number(b),
                safety: self.safety(b, false),
            };
            d.ctors.push(c);
            i += 1;
        }
        i = 0;
        while i < nr && self.ok() {
            let r = self.recursor(b);
            d.recs.push(r);
            i += 1;
        }
        d
    }

    fn recursor(&mut self, b: &[u8]) -> Rec {
        let name = self.name(b);
        let lparams = self.names_list(b);
        let ty = self.expr(b);
        let all = self.names_list(b);
        let num_params = self.number(b);
        let num_indices = self.number(b);
        let num_motives = self.number(b);
        let num_minors = self.number(b);
        let k = self.boolean(b);
        let nrules = self.count(b, 12);
        let mut rules = Vec::with_capacity(nrules);
        let mut j = 0;
        while j < nrules && self.ok() {
            let x = RecRule {
                ctor: self.name(b),
                nfields: self.number(b),
                rhs: self.expr(b),
            };
            rules.push(x);
            j += 1;
        }
        Rec {
            name,
            lparams,
            ty,
            all,
            num_params,
            num_indices,
            num_motives,
            num_minors,
            k,
            rules,
            safety: self.safety(b, false),
        }
    }
}

/// Decodes a whole `.rlb` file into `store`. The result is the header and the declarations in file order, or the first error. The `line` of an error is 0.
pub fn decode(store: &mut Store, b: &[u8]) -> Result<Binary, Error> {
    match header(b) {
        Ok(h) => match sections(b, &h) {
            Ok(secs) => tables(store, b, h, &secs),
            Err(e) => Err(e),
        },
        Err(e) => Err(e),
    }
}

/// Decodes the tables of a file whose header and directory are checked.
fn tables(store: &mut Store, b: &[u8], h: Header, secs: &[Section]) -> Result<Binary, Error> {
    let mut d = Decoder {
        pos: 0,
        end: 0,
        fault: None,
        strs: Vec::new(),
        names: Vec::new(),
        levels: Vec::new(),
        nats: Vec::new(),
        exprs: Vec::new(),
        lv: Vec::new(),
    };
    d.strings(store, b, find(secs, SEC_STRINGS));
    if d.ok() {
        d.name_table(store, b, find(secs, SEC_NAMES));
    }
    if d.ok() {
        d.level_table(store, b, find(secs, SEC_LEVELS));
    }
    if d.ok() {
        d.nat_table(store, b, find(secs, SEC_NATS));
    }
    if d.ok() {
        d.expr_table(store, b, find(secs, SEC_EXPRS));
    }
    let decls = if d.ok() {
        d.decl_table(b, find(secs, SEC_DECLS))
    } else {
        Vec::new()
    };
    if d.ok() && store.is_full() {
        d.fail(ErrorKind::StoreFull);
    }
    match d.fault {
        Some(kind) => Err(Error { line: 0, kind }),
        None => Ok(Binary { header: h, decls }),
    }
}
