//! The lean4export NDJSON 3.x parser (spec 07.1).
//!
//! The parser reads one line at a time. A name, level or expression record goes into the store, and the parser keeps the handle in the table of its index. A declaration record becomes a `Decl`. The parser builds no tree of the input.

use alloc::vec::Vec;
use rulean_nat::Nat;
use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, ExprId, LevelId, LevelListId, NameId, Raw, Store};

use crate::decl::{
    Axiom, Ctor, Decl, Defn, Hints, Induct, InductType, Opaque, Quot, QuotKind, Rec, RecRule,
    Safety, Thm,
};
use crate::error::{Error, ErrorKind};
use crate::json::{MISSING, NONE, Obj, Range, Scanner, at, skip_ws, utf8_valid};
use crate::keys;

/// The newest minor version of format 3 that the parser knows.
pub const KNOWN_MINOR: u64 = 1;

/// The largest index that the parser tables accept. A larger index is a decline (spec 07.1.2 permits gaps, so the table size follows the index, not the line count).
pub const MAX_TABLE_INDEX: u64 = 1 << 28;

/// The largest number of decimal digits of a `natVal`. A value below 2^(2^30), which is 128 MiB, has at most this many digits (spec 05.8).
pub const MAX_NAT_DIGITS: usize = 323_228_497;

/// The largest number of bits of a `natVal`: 128 MiB.
pub const MAX_NAT_BITS: u64 = 1 << 30;

/// The value of an undefined slot of an index table.
const UNDEF: Raw = Raw::MAX;

/// A table from the indices of one record kind to store handles.
#[derive(Debug)]
struct Index {
    slots: Vec<Raw>,
}

impl Index {
    fn new() -> Index {
        Index { slots: Vec::new() }
    }

    fn get(&self, k: u64) -> Raw {
        if k < self.slots.len() as u64 {
            self.slots[k as usize]
        } else {
            UNDEF
        }
    }
}

/// The state of the parser between lines.
#[derive(Debug)]
pub struct Parser {
    scan: Scanner,
    names: Index,
    levels: Index,
    exprs: Index,
    line: u64,
    /// The `lean.version` string of the meta line, or empty if the meta line has none.
    lean_version: Vec<u8>,
    /// The `format.version` string of the meta line.
    format_version: Vec<u8>,
}

impl Default for Parser {
    fn default() -> Parser {
        Parser::new()
    }
}

/// The record kinds of a line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Record {
    Meta,
    Name,
    Level,
    Expr,
    Decl,
}

impl Parser {
    /// A new parser. Name index 0 is the anonymous name and level index 0 is zero.
    pub fn new() -> Parser {
        let mut p = Parser {
            scan: Scanner::new(),
            names: Index::new(),
            levels: Index::new(),
            exprs: Index::new(),
            line: 0,
            lean_version: Vec::new(),
            format_version: Vec::new(),
        };
        p.names.slots.push(0);
        p.levels.slots.push(0);
        p
    }

    /// The `lean.version` string of the meta line (spec 05.2), or an empty string if the meta line has none.
    pub fn lean_version(&self) -> &[u8] {
        &self.lean_version
    }

    /// The number of lines that the parser has read.
    pub fn lines(&self) -> u64 {
        self.line
    }

    /// Reads one line, without its newline. The result is the declaration of the line, if the line is a declaration record.
    pub fn line(&mut self, store: &mut Store, b: &[u8]) -> Result<Option<Decl>, Error> {
        self.line += 1;
        self.scan.fault = None;
        let d = self.record(store, b);
        if store.is_full() {
            self.scan.fail(ErrorKind::StoreFull);
        }
        match self.scan.fault {
            Some(kind) => Err(Error {
                line: self.line,
                kind,
            }),
            None => Ok(d),
        }
    }

    fn ok(&self) -> bool {
        self.scan.ok()
    }

    fn fail(&mut self, kind: ErrorKind) {
        self.scan.fail(kind);
    }

    fn record(&mut self, store: &mut Store, b: &[u8]) -> Option<Decl> {
        if b.len() == 0 {
            self.fail(ErrorKind::EmptyLine);
            return None;
        }
        if !utf8_valid(b) {
            self.fail(ErrorKind::BadUtf8);
            return None;
        }
        let (o, end) = self.scan.object(b, 0);
        if self.ok() && skip_ws(b, end) != b.len() {
            self.fail(ErrorKind::BadJson);
        }
        let kind = self.kind_of(&o);
        if !self.ok() {
            return None;
        }
        if self.line == 1 && kind != Record::Meta {
            self.fail(ErrorKind::NoMeta);
        }
        if self.line != 1 && kind == Record::Meta {
            self.fail(ErrorKind::LateMeta);
        }
        match kind {
            Record::Meta => {
                self.meta(b, &o);
                None
            }
            Record::Name => {
                self.name_record(store, b, &o);
                None
            }
            Record::Level => {
                self.level_record(store, b, &o);
                None
            }
            Record::Expr => {
                self.expr_record(store, b, &o);
                None
            }
            Record::Decl => self.decl_record(b, &o),
        }
    }

    /// The record kind of a line, from its keys.
    fn kind_of(&mut self, o: &Obj) -> Record {
        let decls = count(
            o,
            &[
                keys::AXIOM,
                keys::DEF,
                keys::OPAQUE,
                keys::THM,
                keys::QUOT,
                keys::INDUCTIVE,
            ],
        );
        let tags = count(o, &[keys::META, keys::IN, keys::IL, keys::IE]);
        if tags + decls != 1 {
            self.fail(ErrorKind::UnknownRecord);
        }
        if has(o, keys::META) {
            Record::Meta
        } else if has(o, keys::IN) {
            Record::Name
        } else if has(o, keys::IL) {
            Record::Level
        } else if has(o, keys::IE) {
            Record::Expr
        } else {
            Record::Decl
        }
    }

    // Values.

    fn val(&mut self, o: &Obj, k: usize) -> Range {
        let r = o.vals[k];
        if r.start == NONE {
            self.fail(ErrorKind::MissingKey);
        }
        r
    }

    fn uint(&mut self, b: &[u8], o: &Obj, k: usize) -> u64 {
        let r = self.val(o, k);
        self.scan.uint(b, r)
    }

    fn uint32(&mut self, b: &[u8], o: &Obj, k: usize) -> u32 {
        let r = self.val(o, k);
        self.scan.uint32(b, r)
    }

    fn boolean(&mut self, b: &[u8], o: &Obj, k: usize) -> bool {
        let r = self.val(o, k);
        if self.ok() {
            self.scan.boolean(b, r)
        } else {
            false
        }
    }

    /// Decodes the string of key `k` into `self.scan.buf`.
    fn string(&mut self, b: &[u8], o: &Obj, k: usize) {
        let r = self.val(o, k);
        self.scan.string(b, r);
    }

    fn object(&mut self, b: &[u8], o: &Obj, k: usize) -> Obj {
        let r = self.val(o, k);
        self.object_at(b, r)
    }

    fn object_at(&mut self, b: &[u8], r: Range) -> Obj {
        if self.ok() {
            let (inner, _) = self.scan.object(b, r.start);
            inner
        } else {
            empty_obj()
        }
    }

    fn array(&mut self, b: &[u8], o: &Obj, k: usize) -> Vec<Range> {
        let r = self.val(o, k);
        self.scan.array(b, r)
    }

    fn safety_of_unsafe(&mut self, b: &[u8], o: &Obj) -> Safety {
        if self.boolean(b, o, keys::IS_UNSAFE) {
            Safety::Unsafe
        } else {
            Safety::Safe
        }
    }

    // References to earlier records.

    fn name_ref(&mut self, k: u64) -> NameId {
        let v = self.names.get(k);
        if v == UNDEF {
            self.fail(ErrorKind::UndefinedIndex);
            NameId(0)
        } else {
            NameId(low(v))
        }
    }

    fn level_ref(&mut self, k: u64) -> LevelId {
        let v = self.levels.get(k);
        if v == UNDEF {
            self.fail(ErrorKind::UndefinedIndex);
            LevelId(0)
        } else {
            LevelId(low(v))
        }
    }

    fn expr_ref(&mut self, k: u64) -> ExprId {
        let v = self.exprs.get(k);
        if v == UNDEF {
            self.fail(ErrorKind::UndefinedIndex);
            ExprId(0)
        } else {
            ExprId(v)
        }
    }

    fn name_at(&mut self, b: &[u8], o: &Obj, k: usize) -> NameId {
        let v = self.uint(b, o, k);
        if self.ok() {
            self.name_ref(v)
        } else {
            NameId(0)
        }
    }

    fn level_at(&mut self, b: &[u8], o: &Obj, k: usize) -> LevelId {
        let v = self.uint(b, o, k);
        if self.ok() {
            self.level_ref(v)
        } else {
            LevelId(0)
        }
    }

    fn expr_at(&mut self, b: &[u8], o: &Obj, k: usize) -> ExprId {
        let v = self.uint(b, o, k);
        if self.ok() {
            self.expr_ref(v)
        } else {
            ExprId(0)
        }
    }

    /// The array of name indices of key `k`.
    fn names_at(&mut self, b: &[u8], o: &Obj, k: usize) -> Vec<NameId> {
        let items = self.array(b, o, k);
        let mut out = Vec::with_capacity(items.len());
        let mut i = 0;
        while i < items.len() && self.ok() {
            let v = self.scan.uint(b, items[i]);
            let n = self.name_ref(v);
            out.push(n);
            i += 1;
        }
        out
    }

    /// Defines index `k` of a table. Index 0 of the name and level tables is defined from the start.
    fn define(&mut self, which: Record, k: u64, v: Raw) {
        if k > MAX_TABLE_INDEX {
            self.fail(ErrorKind::IndexLimit);
        }
        if self.ok() {
            let t = match which {
                Record::Name => &mut self.names,
                Record::Level => &mut self.levels,
                _ => &mut self.exprs,
            };
            while (t.slots.len() as u64) <= k {
                t.slots.push(UNDEF);
            }
            if t.slots[k as usize] != UNDEF {
                self.scan.fail(ErrorKind::DuplicateIndex);
            } else {
                t.slots[k as usize] = v;
            }
        }
    }

    // Records.

    fn meta(&mut self, b: &[u8], o: &Obj) {
        let m = self.object(b, o, keys::META);
        let f = self.object(b, &m, keys::FORMAT);
        self.string(b, &f, keys::VERSION);
        if self.ok() {
            self.format_version = self.scan.buf.clone();
            let (major, minor, good) = version(&self.scan.buf);
            if !good || major != 3 || minor > KNOWN_MINOR {
                self.fail(ErrorKind::UnknownVersion);
            }
        }
        if self.ok() && has(&m, keys::LEAN) {
            let l = self.object(b, &m, keys::LEAN);
            if self.ok() && has(&l, keys::VERSION) {
                self.string(b, &l, keys::VERSION);
                self.lean_version = self.scan.buf.clone();
            }
        }
    }

    fn name_record(&mut self, store: &mut Store, b: &[u8], o: &Obj) {
        let k = self.uint(b, o, keys::IN);
        if count(o, &[keys::STR, keys::NUM]) != 1 {
            self.fail(ErrorKind::UnknownRecord);
        }
        let mut id = NameId(0);
        if has(o, keys::STR) {
            let s = self.object(b, o, keys::STR);
            let pre = self.name_at(b, &s, keys::PRE);
            self.string(b, &s, keys::STR);
            if self.ok() {
                id = store.name_str_bytes(pre, &self.scan.buf);
            }
        } else {
            let s = self.object(b, o, keys::NUM);
            let pre = self.name_at(b, &s, keys::PRE);
            let i = self.uint(b, &s, keys::I);
            if self.ok() {
                id = store.name_num(pre, i);
            }
        }
        self.define(Record::Name, k, raw(id.0));
    }

    fn level_record(&mut self, store: &mut Store, b: &[u8], o: &Obj) {
        let k = self.uint(b, o, keys::IL);
        if count(o, &[keys::SUCC, keys::MAX, keys::IMAX, keys::PARAM]) != 1 {
            self.fail(ErrorKind::UnknownRecord);
        }
        let mut id = LevelId(0);
        if has(o, keys::SUCC) {
            let l = self.level_at(b, o, keys::SUCC);
            if self.ok() {
                id = store.level_succ(l);
            }
        } else if has(o, keys::PARAM) {
            let n = self.name_at(b, o, keys::PARAM);
            if self.ok() {
                id = store.level_param(n);
            }
        } else {
            let is_max = has(o, keys::MAX);
            let items = self.array(b, o, if is_max { keys::MAX } else { keys::IMAX });
            if self.ok() && items.len() != 2 {
                self.fail(ErrorKind::WrongType);
            }
            if self.ok() {
                let x = self.scan.uint(b, items[0]);
                let y = self.scan.uint(b, items[1]);
                let lx = self.level_ref(x);
                let ly = self.level_ref(y);
                if self.ok() {
                    id = if is_max {
                        store.level_max(lx, ly)
                    } else {
                        store.level_imax(lx, ly)
                    };
                }
            }
        }
        self.define(Record::Level, k, raw(id.0));
    }

    fn expr_record(&mut self, store: &mut Store, b: &[u8], o: &Obj) {
        let k = self.uint(b, o, keys::IE);
        let kinds = [
            keys::BVAR,
            keys::SORT,
            keys::CONST,
            keys::APP,
            keys::LAM,
            keys::FORALL_E,
            keys::LET_E,
            keys::PROJ,
            keys::NAT_VAL,
            keys::STR_VAL,
            keys::MDATA,
        ];
        if count(o, &kinds) != 1 {
            self.fail(ErrorKind::UnknownRecord);
        }
        let mut which = keys::COUNT;
        let mut i = 0;
        while i < kinds.len() {
            if has(o, kinds[i]) {
                which = kinds[i];
            }
            i += 1;
        }
        let id = if self.ok() {
            self.expr_node(store, b, o, which)
        } else {
            ExprId(0)
        };
        self.define(Record::Expr, k, id.0);
    }

    /// Makes the node of an expression record. `which` is the key of the node kind.
    fn expr_node(&mut self, store: &mut Store, b: &[u8], o: &Obj, which: usize) -> ExprId {
        let mut id = ExprId(0);
        match which {
            keys::BVAR => {
                let i = self.uint32(b, o, keys::BVAR);
                if self.ok() {
                    id = store.mk_bvar(i);
                }
            }
            keys::SORT => {
                let l = self.level_at(b, o, keys::SORT);
                if self.ok() {
                    id = store.mk_sort(l);
                }
            }
            keys::CONST => {
                let c = self.object(b, o, keys::CONST);
                let n = self.name_at(b, &c, keys::NAME);
                let ls = self.level_list(store, b, &c, keys::US);
                if self.ok() {
                    id = store.mk_const(n, ls);
                }
            }
            keys::APP => {
                let a = self.object(b, o, keys::APP);
                let f = self.expr_at(b, &a, keys::FN);
                let x = self.expr_at(b, &a, keys::ARG);
                if self.ok() {
                    id = store.mk_app(f, x);
                }
            }
            keys::LAM | keys::FORALL_E => {
                let a = self.object(b, o, which);
                let n = self.name_at(b, &a, keys::NAME);
                let dom = self.expr_at(b, &a, keys::TYPE);
                let body = self.expr_at(b, &a, keys::BODY);
                self.string(b, &a, keys::BINDER_INFO);
                let info = self.binder_info();
                if self.ok() {
                    id = if which == keys::LAM {
                        store.mk_lam(n, info, dom, body)
                    } else {
                        store.mk_pi(n, info, dom, body)
                    };
                }
            }
            keys::LET_E => {
                let a = self.object(b, o, keys::LET_E);
                let n = self.name_at(b, &a, keys::NAME);
                let ty = self.expr_at(b, &a, keys::TYPE);
                let v = self.expr_at(b, &a, keys::VALUE);
                let body = self.expr_at(b, &a, keys::BODY);
                // `nondep` has no effect on checking (spec 07.1.2), but it must be a boolean.
                self.boolean(b, &a, keys::NONDEP);
                if self.ok() {
                    id = store.mk_let(n, ty, v, body);
                }
            }
            keys::PROJ => {
                let a = self.object(b, o, keys::PROJ);
                let n = self.name_at(b, &a, keys::TYPE_NAME);
                let i = self.uint32(b, &a, keys::IDX);
                let e = self.expr_at(b, &a, keys::STRUCT);
                if self.ok() {
                    id = store.mk_proj(n, i, e);
                }
            }
            keys::NAT_VAL => {
                self.string(b, o, keys::NAT_VAL);
                let n = self.nat_literal();
                if self.ok() {
                    let nid = store.intern_nat(n);
                    id = store.mk_nat_lit(nid);
                }
            }
            keys::STR_VAL => {
                self.string(b, o, keys::STR_VAL);
                if self.ok() {
                    let s = store.intern_str(&self.scan.buf);
                    id = store.mk_str_lit(s);
                }
            }
            _ => {
                // `mdata`: the index names the inner expression. The data is checked as JSON only.
                let a = self.object(b, o, keys::MDATA);
                self.val(&a, keys::DATA);
                id = self.expr_at(b, &a, keys::EXPR);
            }
        }
        id
    }

    /// The binder information in `self.scan.buf`.
    fn binder_info(&mut self) -> BinderInfo {
        let s = &self.scan;
        if s.buf_is(b"default") {
            BinderInfo::Default
        } else if s.buf_is(b"implicit") {
            BinderInfo::Implicit
        } else if s.buf_is(b"instImplicit") {
            BinderInfo::InstImplicit
        } else if s.buf_is(b"strictImplicit") {
            BinderInfo::StrictImplicit
        } else {
            self.scan.fail(ErrorKind::BadEnumValue);
            BinderInfo::Default
        }
    }

    /// The natural number in `self.scan.buf`.
    fn nat_literal(&mut self) -> Nat {
        let s = &self.scan.buf;
        let mut good = s.len() > 0 && !(s.len() > 1 && s[0] == b'0');
        let mut i = 0;
        while good && i < s.len() {
            good = s[i] >= b'0' && s[i] <= b'9';
            i += 1;
        }
        if !self.ok() {
            Nat::zero()
        } else if !good {
            self.fail(ErrorKind::BadNatLiteral);
            Nat::zero()
        } else if s.len() > MAX_NAT_DIGITS {
            self.fail(ErrorKind::NatTooLarge);
            Nat::zero()
        } else {
            match Nat::from_decimal(s) {
                Some(n) => {
                    if n.bits() > MAX_NAT_BITS {
                        self.fail(ErrorKind::NatTooLarge);
                    }
                    n
                }
                None => {
                    self.fail(ErrorKind::BadNatLiteral);
                    Nat::zero()
                }
            }
        }
    }

    /// The level list of key `k`.
    fn level_list(&mut self, store: &mut Store, b: &[u8], o: &Obj, k: usize) -> LevelListId {
        let items = self.array(b, o, k);
        let mut ls = Vec::with_capacity(items.len());
        let mut i = 0;
        while i < items.len() && self.ok() {
            let v = self.scan.uint(b, items[i]);
            let l = self.level_ref(v);
            ls.push(l);
            i += 1;
        }
        if self.ok() {
            store.level_list(&ls)
        } else {
            LevelListId(0)
        }
    }

    fn decl_record(&mut self, b: &[u8], o: &Obj) -> Option<Decl> {
        let d = if has(o, keys::AXIOM) {
            let a = self.object(b, o, keys::AXIOM);
            Decl::Axiom(Axiom {
                name: self.name_at(b, &a, keys::NAME),
                lparams: self.names_at(b, &a, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &a, keys::TYPE),
                safety: self.safety_of_unsafe(b, &a),
            })
        } else if has(o, keys::DEF) {
            let a = self.object(b, o, keys::DEF);
            Decl::Defn(Defn {
                name: self.name_at(b, &a, keys::NAME),
                lparams: self.names_at(b, &a, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &a, keys::TYPE),
                value: self.expr_at(b, &a, keys::VALUE),
                hints: self.hints(b, &a),
                safety: self.safety(b, &a),
                all: self.names_at(b, &a, keys::ALL),
            })
        } else if has(o, keys::THM) {
            let a = self.object(b, o, keys::THM);
            Decl::Thm(Thm {
                name: self.name_at(b, &a, keys::NAME),
                lparams: self.names_at(b, &a, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &a, keys::TYPE),
                value: self.expr_at(b, &a, keys::VALUE),
                all: self.names_at(b, &a, keys::ALL),
            })
        } else {
            self.decl_rest(b, o)
        };
        if self.ok() { Some(d) } else { None }
    }

    fn decl_rest(&mut self, b: &[u8], o: &Obj) -> Decl {
        if has(o, keys::OPAQUE) {
            let a = self.object(b, o, keys::OPAQUE);
            Decl::Opaque(Opaque {
                name: self.name_at(b, &a, keys::NAME),
                lparams: self.names_at(b, &a, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &a, keys::TYPE),
                value: self.expr_at(b, &a, keys::VALUE),
                safety: self.safety_of_unsafe(b, &a),
                all: self.names_at(b, &a, keys::ALL),
            })
        } else if has(o, keys::QUOT) {
            let a = self.object(b, o, keys::QUOT);
            Decl::Quot(Quot {
                name: self.name_at(b, &a, keys::NAME),
                lparams: self.names_at(b, &a, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &a, keys::TYPE),
                kind: self.quot_kind(b, &a),
            })
        } else {
            let a = self.object(b, o, keys::INDUCTIVE);
            Decl::Induct(self.inductive(b, &a))
        }
    }

    fn safety(&mut self, b: &[u8], o: &Obj) -> Safety {
        self.string(b, o, keys::SAFETY);
        let s = &self.scan;
        if s.buf_is(b"safe") {
            Safety::Safe
        } else if s.buf_is(b"unsafe") {
            Safety::Unsafe
        } else if s.buf_is(b"partial") {
            Safety::Partial
        } else {
            self.fail(ErrorKind::BadEnumValue);
            Safety::Safe
        }
    }

    fn hints(&mut self, b: &[u8], o: &Obj) -> Hints {
        let r = self.val(o, keys::HINTS);
        if !self.ok() {
            Hints::Opaque
        } else if at(b, r.start) == b'{' {
            let h = self.object_at(b, r);
            Hints::Regular(self.uint32(b, &h, keys::REGULAR))
        } else {
            self.scan.string(b, r);
            let s = &self.scan;
            if s.buf_is(b"opaque") {
                Hints::Opaque
            } else if s.buf_is(b"abbrev") {
                Hints::Abbrev
            } else {
                self.fail(ErrorKind::BadEnumValue);
                Hints::Opaque
            }
        }
    }

    fn quot_kind(&mut self, b: &[u8], o: &Obj) -> QuotKind {
        self.string(b, o, keys::KIND);
        let s = &self.scan;
        if s.buf_is(b"type") {
            QuotKind::Type
        } else if s.buf_is(b"ctor") {
            QuotKind::Ctor
        } else if s.buf_is(b"lift") {
            QuotKind::Lift
        } else if s.buf_is(b"ind") {
            QuotKind::Ind
        } else {
            self.fail(ErrorKind::BadEnumValue);
            QuotKind::Type
        }
    }

    fn inductive(&mut self, b: &[u8], o: &Obj) -> Induct {
        let types = self.array(b, o, keys::TYPES);
        let ctors = self.array(b, o, keys::CTORS);
        let recs = self.array(b, o, keys::RECS);
        let mut d = Induct {
            types: Vec::with_capacity(types.len()),
            ctors: Vec::with_capacity(ctors.len()),
            recs: Vec::with_capacity(recs.len()),
        };
        let mut i = 0;
        while i < types.len() && self.ok() {
            let t = self.object_at(b, types[i]);
            d.types.push(InductType {
                name: self.name_at(b, &t, keys::NAME),
                lparams: self.names_at(b, &t, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &t, keys::TYPE),
                num_params: self.uint32(b, &t, keys::NUM_PARAMS),
                num_indices: self.uint32(b, &t, keys::NUM_INDICES),
                all: self.names_at(b, &t, keys::ALL),
                ctors: self.names_at(b, &t, keys::CTORS),
                num_nested: self.uint32(b, &t, keys::NUM_NESTED),
                is_rec: self.boolean(b, &t, keys::IS_REC),
                is_reflexive: self.boolean(b, &t, keys::IS_REFLEXIVE),
                safety: self.safety_of_unsafe(b, &t),
            });
            i += 1;
        }
        i = 0;
        while i < ctors.len() && self.ok() {
            let c = self.object_at(b, ctors[i]);
            d.ctors.push(Ctor {
                name: self.name_at(b, &c, keys::NAME),
                lparams: self.names_at(b, &c, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &c, keys::TYPE),
                induct: self.name_at(b, &c, keys::INDUCT),
                cidx: self.uint32(b, &c, keys::CIDX),
                num_params: self.uint32(b, &c, keys::NUM_PARAMS),
                num_fields: self.uint32(b, &c, keys::NUM_FIELDS),
                safety: self.safety_of_unsafe(b, &c),
            });
            i += 1;
        }
        i = 0;
        while i < recs.len() && self.ok() {
            let r = self.object_at(b, recs[i]);
            let rule_items = self.array(b, &r, keys::RULES);
            let mut rules = Vec::with_capacity(rule_items.len());
            let mut j = 0;
            while j < rule_items.len() && self.ok() {
                let x = self.object_at(b, rule_items[j]);
                rules.push(RecRule {
                    ctor: self.name_at(b, &x, keys::CTOR),
                    nfields: self.uint32(b, &x, keys::NFIELDS),
                    rhs: self.expr_at(b, &x, keys::RHS),
                });
                j += 1;
            }
            d.recs.push(Rec {
                name: self.name_at(b, &r, keys::NAME),
                lparams: self.names_at(b, &r, keys::LEVEL_PARAMS),
                ty: self.expr_at(b, &r, keys::TYPE),
                all: self.names_at(b, &r, keys::ALL),
                num_params: self.uint32(b, &r, keys::NUM_PARAMS),
                num_indices: self.uint32(b, &r, keys::NUM_INDICES),
                num_motives: self.uint32(b, &r, keys::NUM_MOTIVES),
                num_minors: self.uint32(b, &r, keys::NUM_MINORS),
                k: self.boolean(b, &r, keys::K),
                rules,
                safety: self.safety_of_unsafe(b, &r),
            });
            i += 1;
        }
        d
    }
}

fn has(o: &Obj, k: usize) -> bool {
    o.vals[k].start != NONE
}

fn count(o: &Obj, ks: &[usize]) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < ks.len() {
        if has(o, ks[i]) {
            n += 1;
        }
        i += 1;
    }
    n
}

fn empty_obj() -> Obj {
    let mut vals = Vec::with_capacity(keys::COUNT);
    let mut i = 0;
    while i < keys::COUNT {
        vals.push(MISSING);
        i += 1;
    }
    Obj { vals }
}

/// The major and minor numbers of a version string `major.minor.patch`. The third result is false if the string has another form.
fn version(s: &[u8]) -> (u64, u64, bool) {
    let mut parts: [u64; 3] = [0, 0, 0];
    let mut digits: [usize; 3] = [0, 0, 0];
    let mut p = 0;
    let mut good = true;
    let mut i = 0;
    while good && i < s.len() {
        let c = s[i];
        if c == b'.' {
            p += 1;
            good = p < 3;
        } else if c >= b'0' && c <= b'9' && digits[p] < 9 {
            parts[p] = parts[p] * 10 + (c - b'0') as u64;
            digits[p] += 1;
        } else {
            good = false;
        }
        i += 1;
    }
    good = good && p == 2 && digits[0] > 0 && digits[1] > 0 && digits[2] > 0;
    (parts[0], parts[1], good)
}

/// A parsed export: the declarations in input order and the facts of the meta line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Export {
    pub decls: Vec<Decl>,
    /// The `lean.version` string of the meta line, or empty.
    pub lean_version: Vec<u8>,
    /// The `format.version` string of the meta line.
    pub format_version: Vec<u8>,
}

/// Parses a whole NDJSON export into `store`. The result is the declarations in input order, or the first error.
pub fn parse(store: &mut Store, input: &[u8]) -> Result<Vec<Decl>, Error> {
    match parse_export(store, input) {
        Ok(x) => Ok(x.decls),
        Err(e) => Err(e),
    }
}

/// Parses a whole NDJSON export into `store`, as `parse` does, and also gives the facts of the meta line.
pub fn parse_export(store: &mut Store, input: &[u8]) -> Result<Export, Error> {
    let mut s = Stream::new();
    let mut tail = false;
    let mut start = 0;
    while s.ok() && start < input.len() {
        let mut j = start;
        while j < input.len() && input[j] != b'\n' {
            j += 1;
        }
        if j == input.len() {
            tail = true;
        } else {
            s.line(store, &input[start..j]);
        }
        start = j + 1;
    }
    s.end(tail)
}

/// An export parse that takes the input one line at a time. The caller does not need to keep the whole input in memory. `parse_export` uses this type, so the two give the same result.
#[derive(Debug)]
pub struct Stream {
    p: Parser,
    decls: Vec<Decl>,
    failed: bool,
    err: Error,
}

impl Default for Stream {
    fn default() -> Stream {
        Stream::new()
    }
}

impl Stream {
    /// A parse with no input.
    pub fn new() -> Stream {
        Stream {
            p: Parser::new(),
            decls: Vec::new(),
            failed: false,
            err: Error {
                line: 0,
                kind: ErrorKind::EmptyLine,
            },
        }
    }

    /// False after the first error. The parse ignores the lines after an error.
    pub fn ok(&self) -> bool {
        !self.failed
    }

    /// Reads one line, without its newline.
    pub fn line(&mut self, store: &mut Store, b: &[u8]) {
        if !self.failed {
            match self.p.line(store, b) {
                Ok(Some(d)) => self.decls.push(d),
                Ok(None) => {}
                Err(e) => {
                    self.failed = true;
                    self.err = e;
                }
            }
        }
    }

    /// Ends the parse. `tail` is true if the input has bytes after its last newline, which is a truncated line.
    pub fn end(self, tail: bool) -> Result<Export, Error> {
        let mut failed = self.failed;
        let mut err = self.err;
        if !failed && tail {
            failed = true;
            err = Error {
                line: self.p.lines() + 1,
                kind: ErrorKind::TruncatedLine,
            };
        }
        if !failed && self.p.lines() == 0 {
            failed = true;
            err = Error {
                line: 1,
                kind: ErrorKind::NoMeta,
            };
        }
        if failed {
            Err(err)
        } else {
            Ok(Export {
                decls: self.decls,
                lean_version: self.p.lean_version,
                format_version: self.p.format_version,
            })
        }
    }
}
