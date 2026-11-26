//! The template fast path of the NDJSON parser (spec perf/05.3).
//!
//! lean4export writes each name, level and expression record in one fixed form: the keys are in alphabetical order, with no spaces. The fast path compares a line with these forms byte by byte, and reads the numbers and the strings between the fixed texts. It changes nothing until the full line matches and each index of the line is defined. Then it makes the same store calls as the general parser, in the same order. If a byte does not match, or an index is not defined, or the index table must grow, the fast path gives the line back, and the general parser reads it from the start. So the fast path accepts only lines that the general parser accepts, and it gives the same result on them.

use rulean_nat::Nat;
use rulean_store::ids::{low, raw};
use rulean_store::{BinderInfo, ExprId, LevelId, NameId, Store};

use super::{MAX_NAT_BITS, MAX_NAT_DIGITS, MAX_TABLE_INDEX, Parser, Record, UNDEF};
use crate::json::{bytes_eq, utf8_valid};

/// The largest number of digits of a number on the fast path. Each number with 19 digits fits in a `u64`.
const MAX_DIGITS: usize = 19;

/// The word with the byte 1 in each of its 8 bytes.
const ONES: u64 = 0x0101_0101_0101_0101;

/// The 8 bytes of `b` at `i` as one little-endian word. The caller makes sure that `i + 8 <= b.len()`.
#[inline]
fn word(b: &[u8], i: usize) -> u64 {
    let s = &b[i..i + 8];
    (s[0] as u64)
        | (s[1] as u64) << 8
        | (s[2] as u64) << 16
        | (s[3] as u64) << 24
        | (s[4] as u64) << 32
        | (s[5] as u64) << 40
        | (s[6] as u64) << 48
        | (s[7] as u64) << 56
}

/// A position in one line. `ok` is false after the first byte that does not match a form.
struct Cur {
    i: usize,
    ok: bool,
}

impl Cur {
    fn new(i: usize) -> Cur {
        Cur { i, ok: true }
    }

    /// Reads the fixed text `lit`.
    #[inline]
    fn lit(&mut self, b: &[u8], lit: &[u8]) {
        if self.ok {
            let i = self.i;
            let n = lit.len();
            let mut eq = i <= b.len() && n <= b.len() - i;
            let mut j = 0;
            // The text is a constant at each call, so after inlining the words of `lit` are constants too, and a long text is one compare for each 8 bytes.
            while eq && j + 8 <= n {
                eq = word(b, i + j) == word(lit, j);
                j += 8;
            }
            while eq && j < n {
                eq = b[i + j] == lit[j];
                j += 1;
            }
            if eq {
                self.i = i + n;
            } else {
                self.ok = false;
            }
        }
    }

    /// Reads a number with 1 to 19 ASCII digits and no leading zero. A number with at most 7 digits and 8 bytes of the line from its start goes to `num_word`. Another number goes to the loop of `num_bytes`.
    #[inline]
    fn num(&mut self, b: &[u8]) -> u64 {
        let mut v: u64 = 0;
        if self.ok {
            let start = self.i;
            if b.len() - start >= 8 {
                let w = word(b, start);
                // A byte of `odd` is 0 if the byte of `w` is an ASCII digit: its high half is 3 and its low half is at most 9. The sums stay in their bytes, so a byte does not change the next byte.
                let odd = ((w & (0xF0 * ONES)) ^ (0x30 * ONES))
                    | (((w & (0x0F * ONES)) + 0x06 * ONES) & (0x10 * ONES));
                // The high bit of a byte of `stops` is 1 if the byte of `w` is not a digit.
                let stops = (odd | ((odd & (0x7F * ONES)) + 0x7F * ONES)) & (0x80 * ONES);
                if stops != 0 {
                    v = self.num_word(b, start, w, stops);
                } else {
                    v = self.num_bytes(b);
                }
            } else {
                v = self.num_bytes(b);
            }
        }
        v
    }

    /// Reads a number of at most 7 digits from the word `w` of the line at `start`. The high bit of a byte of `stops` is 1 if the byte of `w` is not a digit, and `stops` is not 0. The digits are combined two, four and then eight at a time, and each product stays below 2^64, so no step has an overflow.
    fn num_word(&mut self, b: &[u8], start: usize, w: u64, stops: u64) -> u64 {
        // The lowest high bit of `stops` is bit 8 * n + 7, where n is the count of the digits. `!stops + 1` has no overflow, because `stops` is not 0.
        let low = (stops & (!stops + 1)) >> 7;
        let n4 = (low >= 1 << 32) as u32;
        let t4 = low >> (32 * n4);
        let n2 = (t4 >= 1 << 16) as u32;
        let t2 = t4 >> (16 * n2);
        let n1 = (t2 >= 1 << 8) as u32;
        let n = (4 * n4 + 2 * n2 + n1) as usize;
        let mut v: u64 = 0;
        if n == 0 || (n > 1 && b[start] == b'0') {
            self.ok = false;
        } else {
            // The digits go to the high bytes, with the first digit in byte 8 - n and the last digit in byte 7. The bytes after the number go out of the word.
            let d = (w & (0x0F * ONES)) << (8 * (8 - n));
            let d2 = (d * 10 + (d >> 8)) & 0x00FF_00FF_00FF_00FF;
            let d4 = (d2 * 100 + (d2 >> 16)) & 0x0000_FFFF_0000_FFFF;
            v = (d4 * 10000 + (d4 >> 32)) & 0xFFFF_FFFF;
            self.i = start + n;
        }
        v
    }

    /// Reads a number with 1 to 19 ASCII digits and no leading zero, one byte at a time. The loop reads a slice of at most 19 bytes with a local index, so the index needs no bounds check, and `10 * v` is two shifts and one add.
    fn num_bytes(&mut self, b: &[u8]) -> u64 {
        let mut v: u64 = 0;
        let start = self.i;
        let end = if b.len() - start > MAX_DIGITS {
            start + MAX_DIGITS
        } else {
            b.len()
        };
        let s = &b[start..end];
        let mut j = 0;
        while j < s.len() && is_digit(s[j]) {
            v = (v << 3) + (v << 1) + (s[j] - b'0') as u64;
            j += 1;
        }
        let i = start + j;
        self.i = i;
        let more = i < b.len() && is_digit(b[i]);
        if j == 0 || (j > 1 && s[0] == b'0') || more {
            self.ok = false;
        }
        v
    }

    /// Reads the text of a string after its opening quote, and the closing quote. The result is the start and the end of the text. The text has no escape and no control byte, and it is valid UTF-8.
    fn text(&mut self, b: &[u8]) -> (usize, usize) {
        let start = self.i;
        if self.ok {
            while self.i < b.len() && b[self.i] != b'"' && b[self.i] != b'\\' && b[self.i] >= 0x20 {
                self.i += 1;
            }
            if self.i < b.len() && b[self.i] == b'"' && utf8_valid(&b[start..self.i]) {
                self.i += 1;
            } else {
                self.ok = false;
            }
        }
        (start, if self.ok { self.i - 1 } else { start })
    }

    /// Reads `false` or `true`.
    fn boolean(&mut self, b: &[u8]) {
        if self.ok {
            if bytes_eq(b, self.i, self.i + 5, b"false") {
                self.i += 5;
            } else if bytes_eq(b, self.i, self.i + 4, b"true") {
                self.i += 4;
            } else {
                self.ok = false;
            }
        }
    }

    /// Reads a binder information string, with its closing quote.
    fn binder_info(&mut self, b: &[u8]) -> BinderInfo {
        let mut info = BinderInfo::Default;
        if self.ok {
            let c = if self.i + 1 < b.len() {
                b[self.i + 1]
            } else {
                0
            };
            let (lit, v): (&[u8], BinderInfo) = match c {
                b'e' => (b"default\"", BinderInfo::Default),
                b'm' => (b"implicit\"", BinderInfo::Implicit),
                b'n' => (b"instImplicit\"", BinderInfo::InstImplicit),
                _ => (b"strictImplicit\"", BinderInfo::StrictImplicit),
            };
            self.lit(b, lit);
            info = v;
        }
        info
    }

    /// True if the form matched and the line ends here.
    fn end(&self, b: &[u8]) -> bool {
        self.ok && self.i == b.len()
    }
}

fn is_digit(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

impl Parser {
    /// Reads line `b` on the fast path. The result is true if the fast path read the line. If the result is false, the parser and the store did not change.
    pub(super) fn fast_line(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let c2 = if b.len() > 4 { b[2] } else { 0 };
        let c3 = if b.len() > 4 { b[3] } else { 0 };
        let done = match c2 {
            b'a' => self.fast_app(store, b),
            b'i' => match c3 {
                b'e' => self.fast_ie(store, b),
                b'n' => self.fast_name(store, b),
                _ => self.fast_level(store, b),
            },
            b'f' => self.fast_forall(store, b),
            b'c' => self.fast_const(store, b),
            b'b' => self.fast_bvar(store, b),
            _ => false,
        };
        if done {
            self.fast_lines += 1;
        }
        done
    }

    // Lookups that change nothing. An undefined index makes the form fail.

    fn fast_name_ref(&self, c: &mut Cur, k: u64) -> NameId {
        let v = self.names.get(k);
        if v == UNDEF {
            c.ok = false;
            NameId(0)
        } else {
            NameId(low(v))
        }
    }

    fn fast_level_ref(&self, c: &mut Cur, k: u64) -> LevelId {
        let v = self.levels.get(k);
        if v == UNDEF {
            c.ok = false;
            LevelId(0)
        } else {
            LevelId(low(v))
        }
    }

    fn fast_expr_ref(&self, c: &mut Cur, k: u64) -> ExprId {
        let v = self.exprs.get(k);
        if v == UNDEF {
            c.ok = false;
            ExprId(0)
        } else {
            ExprId(v)
        }
    }

    /// True if `define` can set index `k` of `which` with no error and with no growth of the table.
    fn fast_free(&self, which: Record, k: u64) -> bool {
        let t = match which {
            Record::Name => &self.names,
            Record::Level => &self.levels,
            _ => &self.exprs,
        };
        let len = t.slots.len() as u64;
        // The ids of an export go up by one from line to line (spec perf/05.4), so the first test is the usual case.
        if k == len {
            k <= MAX_TABLE_INDEX && len < t.slots.capacity() as u64
        } else {
            k < len && k <= MAX_TABLE_INDEX && t.slots[k as usize] == UNDEF
        }
    }

    /// Sets index `k` of `which`. The caller checked `fast_free` first.
    fn fast_set(&mut self, which: Record, k: u64, v: rulean_store::Raw) {
        let t = match which {
            Record::Name => &mut self.names,
            Record::Level => &mut self.levels,
            _ => &mut self.exprs,
        };
        if k == t.slots.len() as u64 {
            t.slots.push(v);
        } else {
            t.slots[k as usize] = v;
        }
    }

    // Expressions.

    /// `{"app":{"arg":X,"fn":F},"ie":K}`
    fn fast_app(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"app\":{\"arg\":");
        let x = c.num(b);
        c.lit(b, b",\"fn\":");
        let f = c.num(b);
        c.lit(b, b"},\"ie\":");
        let k = c.num(b);
        c.lit(b, b"}");
        let fx = self.fast_expr_ref(&mut c, f);
        let xx = self.fast_expr_ref(&mut c, x);
        let go = c.end(b) && self.fast_free(Record::Expr, k);
        if go {
            let id = store.mk_app(fx, xx);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// The fields of a binder: `{"binderInfo":"I","body":B,"name":N,"type":T}`. The result is the binder information, the name, the type and the body.
    fn fast_binder(&self, c: &mut Cur, b: &[u8]) -> (BinderInfo, NameId, ExprId, ExprId) {
        c.lit(b, b"{\"binderInfo\":\"");
        let info = c.binder_info(b);
        c.lit(b, b",\"body\":");
        let body = c.num(b);
        c.lit(b, b",\"name\":");
        let n = c.num(b);
        c.lit(b, b",\"type\":");
        let ty = c.num(b);
        c.lit(b, b"}");
        let nn = self.fast_name_ref(c, n);
        let tt = self.fast_expr_ref(c, ty);
        let bb = self.fast_expr_ref(c, body);
        (info, nn, tt, bb)
    }

    /// `{"forallE":{...},"ie":K}`
    fn fast_forall(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"forallE\":");
        let (info, n, ty, body) = self.fast_binder(&mut c, b);
        c.lit(b, b",\"ie\":");
        let k = c.num(b);
        c.lit(b, b"}");
        let go = c.end(b) && self.fast_free(Record::Expr, k);
        if go {
            let id = store.mk_pi(n, info, ty, body);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `{"const":{"name":N,"us":[L,...]},"ie":K}`
    fn fast_const(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"const\":{\"name\":");
        let n = c.num(b);
        c.lit(b, b",\"us\":[");
        self.us.truncate(0);
        if c.ok && c.i < b.len() && b[c.i] != b']' {
            self.fast_levels(&mut c, b);
        }
        c.lit(b, b"]},\"ie\":");
        let k = c.num(b);
        c.lit(b, b"}");
        let nn = self.fast_name_ref(&mut c, n);
        let go = c.end(b) && self.fast_free(Record::Expr, k);
        if go {
            let ls = store.level_list(&self.us);
            let id = store.mk_const(nn, ls);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// Reads the level indices `L,L,...` of a list into `self.us`.
    fn fast_levels(&mut self, c: &mut Cur, b: &[u8]) {
        let mut more = true;
        while more && c.ok {
            let v = c.num(b);
            let l = self.fast_level_ref(c, v);
            self.us.push(l);
            more = c.i < b.len() && b[c.i] == b',';
            if more {
                c.i += 1;
            }
        }
    }

    /// `{"bvar":I,"ie":K}`
    fn fast_bvar(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"bvar\":");
        let i = c.num(b);
        c.lit(b, b",\"ie\":");
        let k = c.num(b);
        c.lit(b, b"}");
        let go = c.end(b) && i <= u32::MAX as u64 && self.fast_free(Record::Expr, k);
        if go {
            let id = store.mk_bvar(i as u32);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// The forms that start with `{"ie":K,"`: `lam`, `letE`, `proj`, `sort`, `natVal` and `strVal`.
    fn fast_ie(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"ie\":");
        let k = c.num(b);
        c.lit(b, b",\"");
        let go = c.ok && c.i + 1 < b.len() && self.fast_free(Record::Expr, k);
        if go {
            match b[c.i] {
                b'l' => {
                    if b[c.i + 1] == b'a' {
                        self.fast_lam(store, b, c, k)
                    } else {
                        self.fast_let(store, b, c, k)
                    }
                }
                b'p' => self.fast_proj(store, b, c, k),
                b's' => {
                    if b[c.i + 1] == b'o' {
                        self.fast_sort(store, b, c, k)
                    } else {
                        self.fast_str_val(store, b, c, k)
                    }
                }
                b'n' => self.fast_nat_val(store, b, c, k),
                _ => false,
            }
        } else {
            false
        }
    }

    /// `lam":{...}}`
    fn fast_lam(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"lam\":");
        let (info, n, ty, body) = self.fast_binder(&mut c, b);
        c.lit(b, b"}");
        let go = c.end(b);
        if go {
            let id = store.mk_lam(n, info, ty, body);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `letE":{"body":B,"name":N,"nondep":D,"type":T,"value":V}}`
    fn fast_let(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"letE\":{\"body\":");
        let body = c.num(b);
        c.lit(b, b",\"name\":");
        let n = c.num(b);
        c.lit(b, b",\"nondep\":");
        c.boolean(b);
        c.lit(b, b",\"type\":");
        let ty = c.num(b);
        c.lit(b, b",\"value\":");
        let v = c.num(b);
        c.lit(b, b"}}");
        let nn = self.fast_name_ref(&mut c, n);
        let tt = self.fast_expr_ref(&mut c, ty);
        let vv = self.fast_expr_ref(&mut c, v);
        let bb = self.fast_expr_ref(&mut c, body);
        let go = c.end(b);
        if go {
            let id = store.mk_let(nn, tt, vv, bb);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `proj":{"idx":I,"struct":E,"typeName":N}}`
    fn fast_proj(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"proj\":{\"idx\":");
        let i = c.num(b);
        c.lit(b, b",\"struct\":");
        let e = c.num(b);
        c.lit(b, b",\"typeName\":");
        let n = c.num(b);
        c.lit(b, b"}}");
        let nn = self.fast_name_ref(&mut c, n);
        let ee = self.fast_expr_ref(&mut c, e);
        let go = c.end(b) && i <= u32::MAX as u64;
        if go {
            let id = store.mk_proj(nn, i as u32, ee);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `sort":L}`
    fn fast_sort(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"sort\":");
        let l = c.num(b);
        c.lit(b, b"}");
        let ll = self.fast_level_ref(&mut c, l);
        let go = c.end(b);
        if go {
            let id = store.mk_sort(ll);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `strVal":"S"}`
    fn fast_str_val(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"strVal\":\"");
        let (s, e) = c.text(b);
        c.lit(b, b"}");
        let go = c.end(b);
        if go {
            let t = store.intern_str(&b[s..e]);
            let id = store.mk_str_lit(t);
            self.fast_set(Record::Expr, k, id.0);
        }
        go
    }

    /// `natVal":"D"}`. The digits follow the rules of `nat_literal`.
    fn fast_nat_val(&mut self, store: &mut Store, b: &[u8], mut c: Cur, k: u64) -> bool {
        c.lit(b, b"natVal\":\"");
        let (s, e) = c.text(b);
        c.lit(b, b"}");
        let mut good = c.end(b) && e > s && !(e - s > 1 && b[s] == b'0') && e - s <= MAX_NAT_DIGITS;
        let mut i = s;
        while good && i < e {
            good = is_digit(b[i]);
            i += 1;
        }
        let mut n = Nat::zero();
        if good {
            match Nat::from_decimal(&b[s..e]) {
                Some(v) => {
                    good = v.bits() <= MAX_NAT_BITS;
                    n = v;
                }
                None => good = false,
            }
        }
        if good {
            let nid = store.intern_nat(n);
            let id = store.mk_nat_lit(nid);
            self.fast_set(Record::Expr, k, id.0);
        }
        good
    }

    // Names and levels.

    /// `{"in":K,"str":{"pre":P,"str":"S"}}` and `{"in":K,"num":{"i":I,"pre":P}}`
    fn fast_name(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"in\":");
        let k = c.num(b);
        c.lit(b, b",\"");
        let is_str = c.ok && c.i < b.len() && b[c.i] == b's';
        let mut id = NameId(0);
        if is_str {
            c.lit(b, b"str\":{\"pre\":");
            let p = c.num(b);
            c.lit(b, b",\"str\":\"");
            let (s, e) = c.text(b);
            c.lit(b, b"}}");
            let pre = self.fast_name_ref(&mut c, p);
            if c.end(b) && self.fast_free(Record::Name, k) {
                id = store.name_str_bytes(pre, &b[s..e]);
            } else {
                c.ok = false;
            }
        } else {
            c.lit(b, b"num\":{\"i\":");
            let i = c.num(b);
            c.lit(b, b",\"pre\":");
            let p = c.num(b);
            c.lit(b, b"}}");
            let pre = self.fast_name_ref(&mut c, p);
            if c.end(b) && self.fast_free(Record::Name, k) {
                id = store.name_num(pre, i);
            } else {
                c.ok = false;
            }
        }
        if c.ok {
            self.fast_set(Record::Name, k, raw(id.0));
        }
        c.ok
    }

    /// `{"il":K,"succ":L}`, `{"il":K,"max":[L,L]}`, `{"il":K,"imax":[L,L]}` and `{"il":K,"param":N}`
    fn fast_level(&mut self, store: &mut Store, b: &[u8]) -> bool {
        let mut c = Cur::new(0);
        c.lit(b, b"{\"il\":");
        let k = c.num(b);
        c.lit(b, b",\"");
        let tag = if c.ok && c.i < b.len() { b[c.i] } else { 0 };
        let go = c.ok && self.fast_free(Record::Level, k);
        let mut id = LevelId(0);
        let mut done = false;
        if go {
            match tag {
                b's' => {
                    c.lit(b, b"succ\":");
                    let v = c.num(b);
                    c.lit(b, b"}");
                    let l = self.fast_level_ref(&mut c, v);
                    if c.end(b) {
                        id = store.level_succ(l);
                        done = true;
                    }
                }
                b'p' => {
                    c.lit(b, b"param\":");
                    let v = c.num(b);
                    c.lit(b, b"}");
                    let n = self.fast_name_ref(&mut c, v);
                    if c.end(b) {
                        id = store.level_param(n);
                        done = true;
                    }
                }
                b'm' | b'i' => {
                    let is_max = tag == b'm';
                    let lit: &[u8] = if is_max { b"max\":[" } else { b"imax\":[" };
                    c.lit(b, lit);
                    let x = c.num(b);
                    c.lit(b, b",");
                    let y = c.num(b);
                    c.lit(b, b"]}");
                    let lx = self.fast_level_ref(&mut c, x);
                    let ly = self.fast_level_ref(&mut c, y);
                    if c.end(b) {
                        id = if is_max {
                            store.level_max(lx, ly)
                        } else {
                            store.level_imax(lx, ly)
                        };
                        done = true;
                    }
                }
                _ => {}
            }
        }
        if done {
            self.fast_set(Record::Level, k, raw(id.0));
        }
        done
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::vec;
    use alloc::vec::Vec;

    /// Reads one number from `line` at 0 with `num` and with `num_bytes`, and gives the value, the end and the state of each.
    fn both(line: &[u8]) -> ((u64, usize, bool), (u64, usize, bool)) {
        let mut a = Cur::new(0);
        let va = a.num(line);
        let mut b = Cur::new(0);
        let vb = b.num_bytes(line);
        ((va, a.i, a.ok), (vb, b.i, b.ok))
    }

    #[test]
    fn the_word_read_and_the_byte_read_agree() {
        let mut cases: Vec<Vec<u8>> = Vec::new();
        let mut n: u64 = 0;
        while n < 200_000 {
            cases.push(format!("{n},\"fn\":1}}").into_bytes());
            cases.push(format!("{n}}}").into_bytes());
            n += 1;
        }
        let mut p: u64 = 1;
        while p < 10_000_000_000_000_000_000 {
            cases.push(format!("{}x{{}}}}", p - 1).into_bytes());
            cases.push(format!("{p}/abcdefgh").into_bytes());
            p *= 10;
        }
        // Leading zeros, no digit, and each byte after a digit.
        let mut c: u16 = 0;
        while c < 256 {
            cases.push(vec![
                b'0', c as u8, b'1', b'2', b'3', b'4', b'5', b'6', b'7',
            ]);
            cases.push(vec![
                b'4', b'2', c as u8, b'1', b'1', b'1', b'1', b'1', b'1',
            ]);
            cases.push(vec![
                c as u8, b'1', b'1', b'1', b'1', b'1', b'1', b'1', b'1',
            ]);
            c += 1;
        }
        cases.push(b"12345678901234567890,".to_vec());
        cases.push(b"1234567,".to_vec());
        cases.push(b"12345678,".to_vec());
        let mut k = 0;
        while k < cases.len() {
            let (a, b) = both(&cases[k]);
            assert_eq!(a.2, b.2, "state of {:?}", cases[k]);
            if a.2 {
                assert_eq!(a, b, "value of {:?}", cases[k]);
            }
            k += 1;
        }
    }
}
