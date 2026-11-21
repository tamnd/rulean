//! The JSON layer of the NDJSON scanner (spec 07.1.3).
//!
//! This is not a general JSON library. It reads one line into a table of its keys, and it reads the values that the format uses: unsigned integers, booleans, strings, arrays and objects. It checks that every other value is well-formed JSON and then skips it.
//!
//! The functions do not return early on an error. The first error goes into `Scanner::fault`, and the later steps of the line run on dummy values. The caller checks `Scanner::ok` before it writes anything into the store. Every byte access checks its bounds, so a bad input never makes a panic.

use alloc::vec::Vec;

use crate::error::ErrorKind;
use crate::keys;

/// The value of `Range::start` for a missing value.
pub const NONE: usize = usize::MAX;

/// The bytes `start..end` of a line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub start: usize,
    pub end: usize,
}

/// The range of a key that the object does not have.
pub const MISSING: Range = Range {
    start: NONE,
    end: NONE,
};

/// One key and its value in an object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Field {
    /// The bytes of the key, without the quotes.
    key: Range,
    /// True if the key has an escape.
    escaped: bool,
    value: Range,
}

/// The known keys of one object. `vals[k]` is the value of the key with code `k` (see `keys`), or `MISSING`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Obj {
    pub vals: Vec<Range>,
}

/// The state of the scanner: the first error and the scratch buffers.
#[derive(Debug, Default)]
pub struct Scanner {
    pub fault: Option<ErrorKind>,
    /// The decoded bytes of the last string.
    pub buf: Vec<u8>,
    /// The decoded bytes of the last key.
    kbuf: Vec<u8>,
    /// A second key buffer for the duplicate check.
    kbuf2: Vec<u8>,
    /// The open arrays and objects of `skip_value`.
    stack: Vec<u8>,
}

/// The byte at `i`, or 0 after the end.
pub fn at(b: &[u8], i: usize) -> u8 {
    if i < b.len() { b[i] } else { 0 }
}

fn is_digit(c: u8) -> bool {
    c >= b'0' && c <= b'9'
}

/// The first byte at or after `i` that is not JSON white space.
pub fn skip_ws(b: &[u8], start: usize) -> usize {
    let mut i = start;
    while i < b.len() && (b[i] == b' ' || b[i] == b'\t' || b[i] == b'\r' || b[i] == b'\n') {
        i += 1;
    }
    i
}

/// True if `b[i]` exists and is in `lo..=hi`.
fn byte_in(b: &[u8], i: usize, lo: u8, hi: u8) -> bool {
    i < b.len() && b[i] >= lo && b[i] <= hi
}

/// True if `b` is valid UTF-8: no overlong forms, no surrogates and no value above U+10FFFF.
pub fn utf8_valid(b: &[u8]) -> bool {
    let mut ok = true;
    let mut i = 0;
    while ok && i < b.len() {
        let c = b[i];
        match c {
            0x00..=0x7f => i += 1,
            0xc2..=0xdf => {
                ok = byte_in(b, i + 1, 0x80, 0xbf);
                i += 2;
            }
            0xe0..=0xef => {
                let lo = if c == 0xe0 { 0xa0 } else { 0x80 };
                let hi = if c == 0xed { 0x9f } else { 0xbf };
                ok = byte_in(b, i + 1, lo, hi) && byte_in(b, i + 2, 0x80, 0xbf);
                i += 3;
            }
            0xf0..=0xf4 => {
                let lo = if c == 0xf0 { 0x90 } else { 0x80 };
                let hi = if c == 0xf4 { 0x8f } else { 0xbf };
                ok = byte_in(b, i + 1, lo, hi)
                    && byte_in(b, i + 2, 0x80, 0xbf)
                    && byte_in(b, i + 3, 0x80, 0xbf);
                i += 4;
            }
            _ => ok = false,
        }
    }
    ok
}

/// The value of one hex digit, or 16 if `c` is not a hex digit.
fn hex(c: u8) -> u32 {
    match c {
        b'0'..=b'9' => (c - b'0') as u32,
        b'a'..=b'f' => (c - b'a') as u32 + 10,
        b'A'..=b'F' => (c - b'A') as u32 + 10,
        _ => 16,
    }
}

/// The value of the four hex digits at `i`, or `u32::MAX` if they are not four hex digits.
fn hex4(b: &[u8], i: usize) -> u32 {
    let mut v: u32 = 0;
    let mut ok = true;
    let mut j = 0;
    while ok && j < 4 {
        let d = hex(at(b, i + j));
        if d == 16 {
            ok = false;
        } else {
            v = v * 16 + d;
        }
        j += 1;
    }
    if ok { v } else { u32::MAX }
}

/// Writes the code point `cp` as UTF-8. The caller makes sure that `cp` is a Unicode scalar value.
fn push_utf8(out: &mut Vec<u8>, cp: u32) {
    if cp < 0x80 {
        out.push(cp as u8);
    } else if cp < 0x800 {
        out.push((0xc0 | (cp >> 6)) as u8);
        out.push((0x80 | (cp & 0x3f)) as u8);
    } else if cp < 0x1_0000 {
        out.push((0xe0 | (cp >> 12)) as u8);
        out.push((0x80 | ((cp >> 6) & 0x3f)) as u8);
        out.push((0x80 | (cp & 0x3f)) as u8);
    } else {
        out.push((0xf0 | (cp >> 18)) as u8);
        out.push((0x80 | ((cp >> 12) & 0x3f)) as u8);
        out.push((0x80 | ((cp >> 6) & 0x3f)) as u8);
        out.push((0x80 | (cp & 0x3f)) as u8);
    }
}

/// True if `b[start..end]` is the bytes of `lit`.
pub fn bytes_eq(b: &[u8], start: usize, end: usize, lit: &[u8]) -> bool {
    let mut eq = end >= start && end - start == lit.len() && end <= b.len();
    let mut i = 0;
    while eq && i < lit.len() {
        eq = b[start + i] == lit[i];
        i += 1;
    }
    eq
}

/// Decodes the string between the quotes `start..end` into `out`, and checks the surrogate pairs of the `\u` escapes. The result is the first error, if there is one.
fn decode(b: &[u8], start: usize, end: usize, out: &mut Vec<u8>) -> Option<ErrorKind> {
    let mut fault = None;
    out.clear();
    let mut i = start;
    while i < end && i < b.len() && matches!(fault, None) {
        let c = b[i];
        if c != b'\\' {
            out.push(c);
            i += 1;
        } else {
            let e = at(b, i + 1);
            match e {
                b'b' => out.push(0x08),
                b'f' => out.push(0x0c),
                b'n' => out.push(b'\n'),
                b'r' => out.push(b'\r'),
                b't' => out.push(b'\t'),
                b'u' => {}
                _ => out.push(e),
            }
            if e != b'u' {
                i += 2;
            } else {
                let cp = hex4(b, i + 2);
                i += 6;
                let lo = if at(b, i) == b'\\' && at(b, i + 1) == b'u' {
                    hex4(b, i + 2)
                } else {
                    u32::MAX
                };
                match cp {
                    0xd800..=0xdbff => {
                        if lo >= 0xdc00 && lo <= 0xdfff {
                            push_utf8(out, 0x1_0000 + ((cp - 0xd800) << 10) + (lo - 0xdc00));
                            i += 6;
                        } else {
                            fault = Some(ErrorKind::LoneSurrogate);
                        }
                    }
                    0xdc00..=0xdfff => fault = Some(ErrorKind::LoneSurrogate),
                    0x1_0000..=u32::MAX => fault = Some(ErrorKind::BadJson),
                    _ => push_utf8(out, cp),
                }
            }
        }
    }
    fault
}

impl Scanner {
    /// A new scanner with no error.
    pub fn new() -> Scanner {
        Scanner {
            fault: None,
            buf: Vec::new(),
            kbuf: Vec::new(),
            kbuf2: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// True if there is no error.
    pub fn ok(&self) -> bool {
        matches!(self.fault, None)
    }

    /// Records an error. Only the first error of a line is kept.
    pub fn fail(&mut self, kind: ErrorKind) {
        if self.ok() {
            self.fault = Some(kind);
        }
    }

    /// Skips the string that starts with the quote at `start`. The result is the position after the closing quote. The escapes are checked here, and the surrogate pairs are checked when the string is decoded.
    fn skip_string(&mut self, b: &[u8], start: usize) -> usize {
        let mut i = start + 1;
        let mut open = true;
        while open && self.ok() {
            let c = at(b, i);
            if i >= b.len() || c < 0x20 {
                self.fail(ErrorKind::BadJson);
            } else if c == b'"' {
                open = false;
                i += 1;
            } else if c == b'\\' {
                match at(b, i + 1) {
                    b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => i += 2,
                    b'u' => {
                        if hex4(b, i + 2) == u32::MAX {
                            self.fail(ErrorKind::BadJson);
                        }
                        i += 6;
                    }
                    _ => self.fail(ErrorKind::BadJson),
                }
            } else {
                i += 1;
            }
        }
        i
    }

    /// Skips the number at `start`, with the full JSON grammar.
    fn skip_number(&mut self, b: &[u8], start: usize) -> usize {
        let mut i = start;
        if at(b, i) == b'-' {
            i += 1;
        }
        if at(b, i) == b'0' {
            i += 1;
        } else if is_digit(at(b, i)) {
            while is_digit(at(b, i)) {
                i += 1;
            }
        } else {
            self.fail(ErrorKind::BadJson);
        }
        if at(b, i) == b'.' {
            i += 1;
            if !is_digit(at(b, i)) {
                self.fail(ErrorKind::BadJson);
            }
            while is_digit(at(b, i)) {
                i += 1;
            }
        }
        if at(b, i) == b'e' || at(b, i) == b'E' {
            i += 1;
            if at(b, i) == b'+' || at(b, i) == b'-' {
                i += 1;
            }
            if !is_digit(at(b, i)) {
                self.fail(ErrorKind::BadJson);
            }
            while is_digit(at(b, i)) {
                i += 1;
            }
        }
        i
    }

    /// Skips the literal `lit` at `start`.
    fn skip_literal(&mut self, b: &[u8], start: usize, lit: &[u8]) -> usize {
        if !bytes_eq(b, start, start + lit.len(), lit) {
            self.fail(ErrorKind::BadJson);
        }
        start + lit.len()
    }

    /// Skips a key and its colon. The key starts at `start`. The result is the position after the colon.
    fn skip_key(&mut self, b: &[u8], start: usize) -> usize {
        let mut i = start;
        if at(b, i) != b'"' {
            self.fail(ErrorKind::BadJson);
        } else {
            i = skip_ws(b, self.skip_string(b, i));
            if at(b, i) != b':' {
                self.fail(ErrorKind::BadJson);
            }
            i += 1;
        }
        i
    }

    /// Skips one JSON value that starts at `start`, and checks that it is well-formed. The result is the position after the value. The nesting is kept on a stack, so a deep value uses no call stack.
    ///
    /// The loop body is in two functions, `skip_open` and `skip_close`. Each step gives the new position and the new value of `want_value`. This keeps the loop state small for Aeneas.
    pub fn skip_value(&mut self, b: &[u8], start: usize) -> usize {
        self.stack.clear();
        let mut i = start;
        let mut want_value = true;
        let mut done = false;
        while !done && self.ok() {
            if !want_value && self.stack.len() == 0 {
                done = true;
            } else if want_value {
                let (j, w) = self.skip_open(b, i);
                i = j;
                want_value = w;
            } else {
                let (j, w) = self.skip_close(b, i);
                i = j;
                want_value = w;
            }
        }
        i
    }

    /// One step of `skip_value` where a value must come next. It skips a scalar value, or it opens an array or an object.
    fn skip_open(&mut self, b: &[u8], start: usize) -> (usize, bool) {
        let mut i = skip_ws(b, start);
        let mut want_value = false;
        match at(b, i) {
            b'{' => {
                i = skip_ws(b, i + 1);
                if at(b, i) == b'}' {
                    i += 1;
                } else {
                    self.stack.push(b'{');
                    i = self.skip_key(b, i);
                    want_value = true;
                }
            }
            b'[' => {
                i = skip_ws(b, i + 1);
                if at(b, i) == b']' {
                    i += 1;
                } else {
                    self.stack.push(b'[');
                    want_value = true;
                }
            }
            b'"' => i = self.skip_string(b, i),
            b'-' | b'0'..=b'9' => i = self.skip_number(b, i),
            b't' => i = self.skip_literal(b, i, b"true"),
            b'f' => i = self.skip_literal(b, i, b"false"),
            b'n' => i = self.skip_literal(b, i, b"null"),
            _ => self.fail(ErrorKind::BadJson),
        }
        (i, want_value)
    }

    /// One step of `skip_value` after a value inside an array or an object. It reads a comma or the closing bracket.
    fn skip_close(&mut self, b: &[u8], start: usize) -> (usize, bool) {
        let mut i = skip_ws(b, start);
        let mut want_value = false;
        let top = self.stack[self.stack.len() - 1];
        let c = at(b, i);
        if c == b',' {
            i = skip_ws(b, i + 1);
            if top == b'{' {
                i = self.skip_key(b, i);
            }
            want_value = true;
        } else if (c == b'}' && top == b'{') || (c == b']' && top == b'[') {
            self.stack.pop();
            i += 1;
        } else {
            self.fail(ErrorKind::BadJson);
        }
        (i, want_value)
    }

    /// Decodes the string between the quotes `start..end` into `self.buf` (`to_key` false) or `self.kbuf` (`to_key` true).
    fn decode_into(&mut self, b: &[u8], start: usize, end: usize, to_key: bool) {
        let fault = if to_key {
            decode(b, start, end, &mut self.kbuf)
        } else {
            decode(b, start, end, &mut self.buf)
        };
        if let Some(k) = fault {
            self.fail(k);
        }
    }

    /// True if the keys of two fields are the same after decoding.
    fn same_key(&mut self, b: &[u8], x: Field, y: Field) -> bool {
        if !x.escaped && !y.escaped {
            let mut eq = x.key.end - x.key.start == y.key.end - y.key.start;
            let mut i = 0;
            while eq && x.key.start + i < x.key.end {
                eq = b[x.key.start + i] == b[y.key.start + i];
                i += 1;
            }
            eq
        } else {
            self.decode_into(b, x.key.start, x.key.end, true);
            let fault = decode(b, y.key.start, y.key.end, &mut self.kbuf2);
            if let Some(k) = fault {
                self.fail(k);
            }
            let mut eq = self.kbuf.len() == self.kbuf2.len();
            let mut i = 0;
            while eq && i < self.kbuf.len() {
                eq = self.kbuf[i] == self.kbuf2[i];
                i += 1;
            }
            eq
        }
    }

    /// Reads the object that starts at `start` into a key table. The second result is the position after the object. Two equal keys are an error. A key that the format does not use is checked and skipped.
    pub fn object(&mut self, b: &[u8], start: usize) -> (Obj, usize) {
        let mut vals = Vec::with_capacity(keys::COUNT);
        let mut n = 0;
        while n < keys::COUNT {
            vals.push(MISSING);
            n += 1;
        }
        let mut fields: Vec<Field> = Vec::new();
        let mut i = skip_ws(b, start);
        if at(b, i) != b'{' {
            self.fail(ErrorKind::WrongType);
        } else {
            i = skip_ws(b, i + 1);
            let mut more = at(b, i) != b'}';
            if !more {
                i += 1;
            }
            while more && self.ok() {
                i = skip_ws(b, i);
                if at(b, i) != b'"' {
                    self.fail(ErrorKind::BadJson);
                } else {
                    let ks = i + 1;
                    let ke = self.skip_string(b, i);
                    let mut escaped = false;
                    let mut j = ks;
                    while self.ok() && j + 1 < ke {
                        escaped = escaped || b[j] == b'\\';
                        j += 1;
                    }
                    i = skip_ws(b, ke);
                    if at(b, i) != b':' {
                        self.fail(ErrorKind::BadJson);
                    }
                    let vs = skip_ws(b, i + 1);
                    i = self.skip_value(b, vs);
                    if self.ok() {
                        fields.push(Field {
                            key: Range {
                                start: ks,
                                end: ke - 1,
                            },
                            escaped,
                            value: Range { start: vs, end: i },
                        });
                    }
                    i = skip_ws(b, i);
                    if at(b, i) == b',' {
                        i += 1;
                    } else if at(b, i) == b'}' {
                        i += 1;
                        more = false;
                    } else {
                        self.fail(ErrorKind::BadJson);
                    }
                }
            }
        }
        // The duplicate check and the key table.
        let mut x = 0;
        while x < fields.len() && self.ok() {
            let mut y = x + 1;
            while y < fields.len() {
                if self.same_key(b, fields[x], fields[y]) {
                    self.fail(ErrorKind::DuplicateKey);
                }
                y += 1;
            }
            let f = fields[x];
            let code = if f.escaped {
                self.decode_into(b, f.key.start, f.key.end, true);
                keys::code(&self.kbuf)
            } else {
                keys::code(&b[f.key.start..f.key.end])
            };
            if code < keys::COUNT {
                vals[code] = f.value;
            }
            x += 1;
        }
        (Obj { vals }, i)
    }

    /// The items of the array at `r`.
    pub fn array(&mut self, b: &[u8], r: Range) -> Vec<Range> {
        let mut items = Vec::new();
        let mut i = r.start;
        if !self.ok() {
            // Nothing to read.
        } else if at(b, i) != b'[' {
            self.fail(ErrorKind::WrongType);
        } else {
            i = skip_ws(b, i + 1);
            let mut more = at(b, i) != b']';
            while more && self.ok() {
                let vs = skip_ws(b, i);
                i = self.skip_value(b, vs);
                items.push(Range { start: vs, end: i });
                i = skip_ws(b, i);
                if at(b, i) == b',' {
                    i += 1;
                } else if at(b, i) == b']' {
                    more = false;
                } else {
                    self.fail(ErrorKind::BadJson);
                }
            }
        }
        items
    }

    /// The unsigned integer at `r`. A sign, a fraction or an exponent is `BadInteger`. A value above 2^64 - 1 is `IntegerOverflow`.
    pub fn uint(&mut self, b: &[u8], r: Range) -> u64 {
        let mut v: u64 = 0;
        if !self.ok() {
            // Nothing to read.
        } else if !(is_digit(at(b, r.start)) || at(b, r.start) == b'-') {
            self.fail(ErrorKind::WrongType);
        } else {
            let mut i = r.start;
            while i < r.end && self.ok() {
                let c = b[i];
                if !is_digit(c) {
                    self.fail(ErrorKind::BadInteger);
                } else {
                    let d = (c - b'0') as u64;
                    if v > 1_844_674_407_370_955_161 || (v == 1_844_674_407_370_955_161 && d > 5) {
                        self.fail(ErrorKind::IntegerOverflow);
                    } else {
                        v = v * 10 + d;
                    }
                }
                i += 1;
            }
        }
        v
    }

    /// The integer at `r`, which must be at most 2^32 - 1.
    pub fn uint32(&mut self, b: &[u8], r: Range) -> u32 {
        let v = self.uint(b, r);
        if v > u32::MAX as u64 {
            self.fail(ErrorKind::IntegerOverflow);
            0
        } else {
            v as u32
        }
    }

    /// The boolean at `r`.
    pub fn boolean(&mut self, b: &[u8], r: Range) -> bool {
        if bytes_eq(b, r.start, r.end, b"true") {
            true
        } else {
            if !bytes_eq(b, r.start, r.end, b"false") {
                self.fail(ErrorKind::WrongType);
            }
            false
        }
    }

    /// Decodes the string at `r` into `self.buf`.
    pub fn string(&mut self, b: &[u8], r: Range) {
        self.buf.clear();
        if !self.ok() {
            // Nothing to read.
        } else if at(b, r.start) != b'"' || r.end < r.start + 2 {
            self.fail(ErrorKind::WrongType);
        } else {
            self.decode_into(b, r.start + 1, r.end - 1, false);
        }
    }

    /// True if `self.buf` is the bytes of `lit`.
    pub fn buf_is(&self, lit: &[u8]) -> bool {
        bytes_eq(&self.buf, 0, self.buf.len(), lit)
    }
}
