//! Operations on limb vectors.
//!
//! A limb vector is a little-endian list of `u64` digits in base 2^64. The functions accept vectors with leading zero limbs and with no limbs (the value 0). The results can have leading zero limbs. `Nat::from_limbs` removes them.
//!
//! The code stays in the Aeneas subset of spec 10.6: `while` loops with an index, no iterators, no closures and only the modelled `Vec` methods.

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

/// The number of limbs below which multiplication uses the schoolbook method (spec 04.6).
pub const KARATSUBA_MIN: usize = 48;

/// The number of limbs without the leading zero limbs.
pub fn used_len(a: &[u64]) -> usize {
    let mut n = a.len();
    while n > 0 && a[n - 1] == 0 {
        n -= 1;
    }
    n
}

/// A vector of `n` zero limbs.
pub fn zeros(n: usize) -> Vec<u64> {
    vec![0; n]
}

/// A copy of the limbs `lo..hi` of `a`. A limb at or above `a.len()` is zero.
pub fn part(a: &[u64], lo: usize, hi: usize) -> Vec<u64> {
    let mut v = zeros(hi.saturating_sub(lo));
    let end = if hi < a.len() { hi } else { a.len() };
    if lo < end {
        let src = &a[lo..end];
        let dst = &mut v[..end - lo];
        let mut i = 0;
        while i < src.len() {
            dst[i] = src[i];
            i += 1;
        }
    }
    v
}

/// The limb `i` of `a`, or zero if `i` is at or above the length.
pub fn get(a: &[u64], i: usize) -> u64 {
    if i < a.len() { a[i] } else { 0 }
}

/// Compares two values.
pub fn cmp(a: &[u64], b: &[u64]) -> Ordering {
    let na = used_len(a);
    let nb = used_len(b);
    if na != nb {
        if na < nb {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    } else {
        let mut result = Ordering::Equal;
        let mut i = na;
        while i > 0 && result == Ordering::Equal {
            i -= 1;
            if a[i] < b[i] {
                result = Ordering::Less;
            } else if a[i] > b[i] {
                result = Ordering::Greater;
            }
        }
        result
    }
}

/// `a + b`.
pub fn add(a: &[u64], b: &[u64]) -> Vec<u64> {
    // `long` is the longer operand. The first loop runs on the limbs of both operands and has no test of the length, and the second loop runs on the other limbs of `long`.
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let n = long.len();
    let m = short.len();
    let mut r = zeros(n + 1);
    let mut carry: u64 = 0;
    let (x, y, out) = (&long[..m], &short[..m], &mut r[..m]);
    let mut i = 0;
    while i < m {
        let s = x[i] as u128 + y[i] as u128 + carry as u128;
        out[i] = s as u64;
        carry = (s >> 64) as u64;
        i += 1;
    }
    let (x, out) = (&long[m..n], &mut r[m..n]);
    let mut j = 0;
    while j < x.len() && carry != 0 {
        let s = x[j] as u128 + carry as u128;
        out[j] = s as u64;
        carry = (s >> 64) as u64;
        j += 1;
    }
    while j < x.len() {
        out[j] = x[j];
        j += 1;
    }
    if carry != 0 {
        r[n] = carry;
    } else {
        r.truncate(n);
    }
    r
}

/// `a - b`. The caller makes sure that `a >= b`.
pub fn sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    let n = a.len();
    let m = if b.len() < n { b.len() } else { n };
    let mut r = Vec::with_capacity(n);
    let mut borrow: u128 = 0;
    let mut i = 0;
    while i < m {
        // The sum is at least 2^64 - (2^64 - 1) - 1 = 0, so it does not go below zero.
        let d = (1u128 << 64) + a[i] as u128 - b[i] as u128 - borrow;
        r.push(d as u64);
        borrow = 1 - (d >> 64);
        i += 1;
    }
    // The limbs of `b` from `m` are zero, because `a >= b`.
    while i < n {
        let d = (1u128 << 64) + a[i] as u128 - borrow;
        r.push(d as u64);
        borrow = 1 - (d >> 64);
        i += 1;
    }
    r
}

/// Adds `b` into `acc` at limb `offset`. The caller makes sure that the sum fits in `acc`. The leading zero limbs of `b` are not read, so `b` can be longer than the free part of `acc`.
fn add_into(acc: &mut [u64], b: &[u64], offset: usize) {
    let nb = used_len(b);
    let mut carry: u128 = 0;
    let (x, y) = (&mut acc[offset..offset + nb], &b[..nb]);
    let mut i = 0;
    while i < nb {
        let s = x[i] as u128 + y[i] as u128 + carry;
        x[i] = s as u64;
        carry = s >> 64;
        i += 1;
    }
    let mut k = offset + nb;
    while carry != 0 {
        let s = acc[k] as u128 + carry;
        acc[k] = s as u64;
        carry = s >> 64;
        k += 1;
    }
}

/// Subtracts `b` from `acc` at limb `offset`. The caller makes sure that the result is not negative.
fn sub_into(acc: &mut [u64], b: &[u64], offset: usize) {
    let nb = used_len(b);
    let mut borrow: u128 = 0;
    let (x, y) = (&mut acc[offset..offset + nb], &b[..nb]);
    let mut i = 0;
    while i < nb {
        let d = (1u128 << 64) + x[i] as u128 - y[i] as u128 - borrow;
        x[i] = d as u64;
        borrow = 1 - (d >> 64);
        i += 1;
    }
    let mut k = offset + nb;
    while borrow != 0 {
        let d = (1u128 << 64) + acc[k] as u128 - borrow;
        acc[k] = d as u64;
        borrow = 1 - (d >> 64);
        k += 1;
    }
}

/// `a * b` with the schoolbook method.
pub fn mul_school(a: &[u64], b: &[u64]) -> Vec<u64> {
    // The outer loop runs on the shorter operand, so the inner loop is long and its cost for each limb is low.
    let (long, short) = if used_len(a) >= used_len(b) {
        (a, b)
    } else {
        (b, a)
    };
    let nl = used_len(long);
    let ns = used_len(short);
    let mut r = zeros(nl + ns);
    school_rows(&mut r, &long[..nl], &short[..ns]);
    r
}

/// Writes `long * short` into `r`, which has at least `long.len() + short.len()` limbs and is zero.
fn school_rows(r: &mut [u64], long: &[u64], short: &[u64]) {
    let nl = long.len();
    let ns = short.len();
    // Two rows go in one pass on the long operand, so each limb of the result is read and written half as often. The carries are single limbs: `t` and `u` are at most (2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1.
    let mut i = 0;
    while i + 3 < ns {
        let x0 = short[i] as u128;
        let x1 = short[i + 1] as u128;
        let x2 = short[i + 2] as u128;
        let x3 = short[i + 3] as u128;
        let row = &mut r[i..i + nl + 4];
        let (mut c0, mut c1, mut c2, mut c3): (u64, u64, u64, u64) = (0, 0, 0, 0);
        let (mut p1, mut p2, mut p3): (u64, u64, u64) = (0, 0, 0);
        let mut j = 0;
        while j < nl {
            let l = long[j];
            let t = row[j] as u128 + x0 * l as u128 + c0 as u128;
            let u = (t as u64) as u128 + x1 * p1 as u128 + c1 as u128;
            let v = (u as u64) as u128 + x2 * p2 as u128 + c2 as u128;
            let w = (v as u64) as u128 + x3 * p3 as u128 + c3 as u128;
            row[j] = w as u64;
            c0 = (t >> 64) as u64;
            c1 = (u >> 64) as u64;
            c2 = (v >> 64) as u64;
            c3 = (w >> 64) as u64;
            p3 = p2;
            p2 = p1;
            p1 = l;
            j += 1;
        }
        // Three more columns empty the pipeline: in column nl + k, the rows below k have no more input.
        let u = c0 as u128 + x1 * p1 as u128 + c1 as u128;
        let v = (u as u64) as u128 + x2 * p2 as u128 + c2 as u128;
        let w = (v as u64) as u128 + x3 * p3 as u128 + c3 as u128;
        row[nl] = w as u64;
        let (c1, c2, c3) = ((u >> 64) as u64, (v >> 64) as u64, (w >> 64) as u64);
        let v = c1 as u128 + x2 * p1 as u128 + c2 as u128;
        let w = (v as u64) as u128 + x3 * p2 as u128 + c3 as u128;
        row[nl + 1] = w as u64;
        let (c2, c3) = ((v >> 64) as u64, (w >> 64) as u64);
        let w = c2 as u128 + x3 * p1 as u128 + c3 as u128;
        row[nl + 2] = w as u64;
        row[nl + 3] = (w >> 64) as u64;
        i += 4;
    }
    while i + 1 < ns {
        let x0 = short[i] as u128;
        let x1 = short[i + 1] as u128;
        let row = &mut r[i..i + nl + 2];
        let mut c0: u64 = 0;
        let mut c1: u64 = 0;
        let mut prev: u64 = 0;
        let mut j = 0;
        while j < nl {
            let l = long[j];
            let t = row[j] as u128 + x0 * l as u128 + c0 as u128;
            let u = (t as u64) as u128 + x1 * prev as u128 + c1 as u128;
            row[j] = u as u64;
            c0 = (t >> 64) as u64;
            c1 = (u >> 64) as u64;
            prev = l;
            j += 1;
        }
        let u = c0 as u128 + x1 * prev as u128 + c1 as u128;
        row[nl] = u as u64;
        row[nl + 1] = (u >> 64) as u64;
        i += 2;
    }
    if i < ns {
        let x = short[i] as u128;
        let row = &mut r[i..i + nl + 1];
        let mut c: u64 = 0;
        let mut j = 0;
        while j < nl {
            let t = row[j] as u128 + x * long[j] as u128 + c as u128;
            row[j] = t as u64;
            c = (t >> 64) as u64;
            j += 1;
        }
        row[nl] = c;
    }
}

/// `a * b`. The method is Karatsuba when both operands have at least `KARATSUBA_MIN` limbs, and schoolbook otherwise.
pub fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    let na = used_len(a);
    let nb = used_len(b);
    if na < KARATSUBA_MIN || nb < KARATSUBA_MIN {
        mul_school(a, b)
    } else if na == nb {
        let mut r = zeros(2 * na);
        karatsuba(&mut r, &a[..na], &b[..nb]);
        r
    } else {
        mul_parts(&a[..na], &b[..nb])
    }
}

/// `a * b` for operands of different lengths. The longer operand is cut into parts with the length of the shorter operand, and each part is multiplied by the shorter operand.
fn mul_parts(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let nl = long.len();
    let ns = short.len();
    let mut r = zeros(nl + ns);
    let mut off = 0;
    while off < nl {
        let end = if off + ns < nl { off + ns } else { nl };
        let p = mul(&long[off..end], short);
        add_into(&mut r, &p, off);
        off = end;
    }
    r
}

/// `r = a * b` with the schoolbook method. The operands have the same length, and `r` has two times this length.
fn school_into(r: &mut [u64], a: &[u64], b: &[u64]) {
    let mut k = 0;
    while k < r.len() {
        r[k] = 0;
        k += 1;
    }
    school_rows(r, a, b);
}

/// `out = |x - y|`. The length of `out` is the length of `x`, and `y` is not longer than `x`. The result is true if `x >= y`.
fn abs_diff(out: &mut [u64], x: &[u64], y: &[u64]) -> bool {
    let ge = cmp(x, y) != Ordering::Less;
    let (big, small) = if ge { (x, y) } else { (y, x) };
    let mut borrow: u128 = 0;
    let mut i = 0;
    while i < out.len() {
        let d = (1u128 << 64) + get(big, i) as u128 - get(small, i) as u128 - borrow;
        out[i] = d as u64;
        borrow = 1 - (d >> 64);
        i += 1;
    }
    ge
}

/// Karatsuba multiplication into `r`: with `a = a1 * B^lo + a0` and `b = b1 * B^lo + b0`, the product is `z2 * B^2lo + z1 * B^lo + z0`, where `z1 = z0 + z2 - (a1 - a0)(b1 - b0)`. The operands have the same length `n`, and `r` has the length `2n`. `z0` and `z2` go directly into `r`, so a step makes only four small arrays. The form with a difference keeps the operands of the middle product at `n - lo` limbs.
fn karatsuba(r: &mut [u64], a: &[u64], b: &[u64]) {
    let n = a.len();
    if n < KARATSUBA_MIN {
        school_into(r, a, b);
    } else {
        let lo = n / 2;
        let hi = n - lo;
        karatsuba(&mut r[..2 * lo], &a[..lo], &b[..lo]);
        karatsuba(&mut r[2 * lo..], &a[lo..], &b[lo..]);
        let mut da = zeros(hi);
        let mut db = zeros(hi);
        let sa = abs_diff(&mut da, &a[lo..], &a[..lo]);
        let sb = abs_diff(&mut db, &b[lo..], &b[..lo]);
        let mut m = zeros(2 * hi);
        karatsuba(&mut m, &da, &db);
        let mut w = zeros(2 * hi + 1);
        add_into(&mut w, &r[..2 * lo], 0);
        add_into(&mut w, &r[2 * lo..], 0);
        if sa == sb {
            sub_into(&mut w, &m, 0);
        } else {
            add_into(&mut w, &m, 0);
        }
        add_into(r, &w, lo);
    }
}

/// The number of leading zero bits of a limb.
pub fn leading_zeros(x: u64) -> u32 {
    let mut n = 0;
    let mut y = x;
    if y == 0 {
        64
    } else {
        while y & (1u64 << 63) == 0 {
            y <<= 1;
            n += 1;
        }
        n
    }
}

/// `a * 2^s` for a shift `s` below 64. The result has one more limb than `a`.
fn shl_small(a: &[u64], s: u32) -> Vec<u64> {
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry: u64 = 0;
    let mut i = 0;
    while i < a.len() {
        if s == 0 {
            r.push(a[i]);
        } else {
            r.push((a[i] << s) | carry);
            carry = a[i] >> (64 - s);
        }
        i += 1;
    }
    r.push(carry);
    r
}

/// The value of the limbs `0..n` of `a`, divided by `2^s` for a shift `s` below 64.
fn shr_small(a: &[u64], n: usize, s: u32) -> Vec<u64> {
    let mut r = zeros(n);
    if n > 0 {
        let (x, out) = (&a[..n], &mut r[..n]);
        if s == 0 {
            let mut i = 0;
            while i < n {
                out[i] = x[i];
                i += 1;
            }
        } else {
            let mut i = 0;
            while i + 1 < n {
                out[i] = (x[i] >> s) | (x[i + 1] << (64 - s));
                i += 1;
            }
            out[n - 1] = x[n - 1] >> s;
        }
    }
    r
}

/// Division by one limb `d`, which is not zero. The result is the quotient and the remainder.
pub fn divmod_limb(a: &[u64], d: u64) -> (Vec<u64>, u64) {
    let n = used_len(a);
    let mut q = zeros(n);
    let mut rem: u128 = 0;
    let dd = d as u128;
    let mut i = n;
    while i > 0 {
        i -= 1;
        let cur = (rem << 64) | a[i] as u128;
        q[i] = (cur / dd) as u64;
        rem = cur % dd;
    }
    (q, rem as u64)
}

/// Division with the remainder, algorithm D of Knuth (TAOCP 4.3.1). The divisor `b` has at least one limb that is not zero.
pub fn divmod(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let n = used_len(b);
    let na = used_len(a);
    if na < n {
        (Vec::new(), part(a, 0, na))
    } else if n == 1 {
        let (q, r) = divmod_limb(a, b[0]);
        let mut rv = Vec::with_capacity(1);
        rv.push(r);
        (q, rv)
    } else {
        knuth_d(a, b, na, n)
    }
}

/// The main loop of algorithm D, for a divisor of at least two limbs.
fn knuth_d(a: &[u64], b: &[u64], na: usize, n: usize) -> (Vec<u64>, Vec<u64>) {
    let base: u128 = 1u128 << 64;
    let s = leading_zeros(b[n - 1]);
    let v = shl_small(&part(b, 0, n), s);
    // `u` has na + 1 limbs. The top limb takes the bits that the shift moves out.
    let mut u = shl_small(&part(a, 0, na), s);
    let m = na - n;
    let mut q = zeros(m + 1);
    let vtop = v[n - 1] as u128;
    let vnext = v[n - 2] as u128;
    let mut k = m + 1;
    while k > 0 {
        k -= 1;
        let j = k;
        let num = ((u[j + n] as u128) << 64) | u[j + n - 1] as u128;
        let mut qhat = num / vtop;
        let mut rhat = num % vtop;
        while rhat < base && (qhat >= base || qhat * vnext > ((rhat << 64) | u[j + n - 2] as u128))
        {
            qhat -= 1;
            rhat += vtop;
        }
        // Multiply and subtract: u[j..=j+n] -= qhat * v.
        let mut borrow: u128 = 0;
        let mut carry: u128 = 0;
        let mut i = 0;
        while i <= n {
            let vi = if i < n { v[i] as u128 } else { 0 };
            let p = qhat * vi + carry;
            carry = p >> 64;
            let d = base + u[j + i] as u128 - (p & 0xffff_ffff_ffff_ffff) - borrow;
            u[j + i] = d as u64;
            borrow = 1 - (d >> 64);
            i += 1;
        }
        if borrow != 0 {
            // The estimate was one too large. Add v back.
            qhat -= 1;
            let mut c: u128 = 0;
            let mut i2 = 0;
            while i2 < n {
                let t = u[j + i2] as u128 + v[i2] as u128 + c;
                u[j + i2] = t as u64;
                c = t >> 64;
                i2 += 1;
            }
            u[j + n] = (u[j + n] as u128 + c) as u64;
        }
        q[j] = qhat as u64;
    }
    let r = shr_small(&u, n, s);
    (q, r)
}

/// `a & b`.
pub fn and(a: &[u64], b: &[u64]) -> Vec<u64> {
    let n = if a.len() < b.len() { a.len() } else { b.len() };
    let (x, y) = (&a[..n], &b[..n]);
    // The high limbs of the result are often zero, so the length is found first.
    let mut top = n;
    while top > 0 && x[top - 1] & y[top - 1] == 0 {
        top -= 1;
    }
    let mut r = zeros(top);
    let (x, y, out) = (&x[..top], &y[..top], &mut r[..top]);
    let mut i = 0;
    while i < top {
        out[i] = x[i] & y[i];
        i += 1;
    }
    r
}

/// `a | b`.
pub fn or(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let n = long.len();
    let m = short.len();
    let mut r = zeros(n);
    let (x, y, out) = (&long[..m], &short[..m], &mut r[..m]);
    let mut i = 0;
    while i < m {
        out[i] = x[i] | y[i];
        i += 1;
    }
    let (x, out) = (&long[m..n], &mut r[m..n]);
    let mut j = 0;
    while j < x.len() {
        out[j] = x[j];
        j += 1;
    }
    r
}

/// `a ^ b`.
pub fn xor(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let n = long.len();
    let m = short.len();
    let mut r = zeros(n);
    let (x, y, out) = (&long[..m], &short[..m], &mut r[..m]);
    let mut i = 0;
    while i < m {
        out[i] = x[i] ^ y[i];
        i += 1;
    }
    let (x, out) = (&long[m..n], &mut r[m..n]);
    let mut j = 0;
    while j < x.len() {
        out[j] = x[j];
        j += 1;
    }
    r
}

/// `a * 2^s`.
pub fn shl(a: &[u64], s: u64) -> Vec<u64> {
    let limbs = (s / 64) as usize;
    let bits = (s % 64) as u32;
    let n = used_len(a);
    let x = &a[..n];
    let mut r = zeros(limbs + n + 1);
    let out = &mut r[limbs..limbs + n + 1];
    if bits == 0 {
        let mut i = 0;
        while i < n {
            out[i] = x[i];
            i += 1;
        }
    } else if n > 0 {
        out[0] = x[0] << bits;
        let (lo, hi) = (&x[..n - 1], &x[1..n]);
        let o = &mut out[1..n];
        let mut i = 0;
        while i < o.len() {
            o[i] = (hi[i] << bits) | (lo[i] >> (64 - bits));
            i += 1;
        }
        out[n] = x[n - 1] >> (64 - bits);
    }
    r
}

/// `a / 2^s`, rounded down. The result is built in one pass, without a copy of the input.
pub fn shr(a: &[u64], s: u64) -> Vec<u64> {
    let n = used_len(a) as u64;
    let limbs = s / 64;
    if limbs >= n {
        Vec::new()
    } else {
        let x = &a[limbs as usize..n as usize];
        let m = x.len();
        let b = (s % 64) as u32;
        let mut r = zeros(m);
        let out = &mut r[..m];
        if b == 0 {
            let mut i = 0;
            while i < m {
                out[i] = x[i];
                i += 1;
            }
        } else {
            let (lo, hi) = (&x[..m - 1], &x[1..m]);
            let o = &mut out[..m - 1];
            let mut i = 0;
            while i < o.len() {
                o[i] = (lo[i] >> b) | (hi[i] << (64 - b));
                i += 1;
            }
            out[m - 1] = x[m - 1] >> b;
        }
        r
    }
}

/// The number of bits of the value: 0 for 0, else `floor(log2 a) + 1`.
pub fn bits(a: &[u64]) -> u64 {
    let n = used_len(a);
    if n == 0 {
        0
    } else {
        (n as u64) * 64 - leading_zeros(a[n - 1]) as u64
    }
}

/// Bit `i` of the value.
pub fn bit(a: &[u64], i: u64) -> bool {
    let limb = i / 64;
    if limb >= a.len() as u64 {
        false
    } else {
        (a[limb as usize] >> (i % 64)) & 1 == 1
    }
}
