//! The natural number type of the kernel. A small value is a `u64`, a large value is a list of limbs. See spec section 04.6.
//!
//! This crate is part of the verified core. It uses only `core` and `alloc` (spec 03.3).
//!
//! The operations follow the meaning of Lean's `Nat`: subtraction stops at zero, and division or remainder by zero give `0` and the dividend. The size guards of spec 05.8 are the job of the caller. For example, the caller refuses `pow` and `shift_left` when the result is too large, before it calls them.

#![no_std]
#![forbid(unsafe_code)]
// The `vec!` macro is outside the modelled `Vec` functions of spec 10.6, so the code uses `with_capacity` and `push`.
#![allow(clippy::vec_init_then_push)]

extern crate alloc;

pub mod limbs;

use alloc::vec::Vec;
use core::cmp::Ordering;

/// A natural number of any size.
///
/// The form is canonical: a value below 2^64 is always `Small`, and the limbs of a `Large` value have no leading zero limb. So two equal numbers have the same form, and the derived equality is the equality of numbers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Nat {
    /// A value below 2^64.
    Small(u64),
    /// A value of at least 2^64, as little-endian limbs in base 2^64. There are at least two limbs and the last limb is not zero.
    Large(Vec<u64>),
}

/// The binary operations that have a path for large values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
}

/// 10^19, the largest power of ten in a `u64`.
const TEN19: u64 = 10_000_000_000_000_000_000;

impl Nat {
    /// The number 0.
    pub fn zero() -> Nat {
        Nat::Small(0)
    }

    /// The number `x`.
    pub fn from_u64(x: u64) -> Nat {
        Nat::Small(x)
    }

    /// The number with the little-endian limbs `v`. The limbs can have leading zero limbs.
    pub fn from_limbs(v: Vec<u64>) -> Nat {
        let n = limbs::used_len(&v);
        if n == 0 {
            Nat::Small(0)
        } else if n == 1 {
            Nat::Small(v[0])
        } else {
            let mut v = v;
            v.truncate(n);
            Nat::Large(v)
        }
    }

    /// The value as a `u64`, if it is below 2^64.
    pub fn to_u64(&self) -> Option<u64> {
        match self {
            Nat::Small(x) => Some(*x),
            Nat::Large(_) => None,
        }
    }

    /// True if the value is 0.
    pub fn is_zero(&self) -> bool {
        matches!(self, Nat::Small(0))
    }

    /// The number of limbs: 0 for the value 0, 1 for other small values.
    pub fn limb_count(&self) -> usize {
        match self {
            Nat::Small(0) => 0,
            Nat::Small(_) => 1,
            Nat::Large(v) => v.len(),
        }
    }

    /// The limb `i`, or 0 if `i` is at or above `limb_count`.
    pub fn limb(&self, i: usize) -> u64 {
        match self {
            Nat::Small(x) => {
                if i == 0 {
                    *x
                } else {
                    0
                }
            }
            Nat::Large(v) => limbs::get(v, i),
        }
    }

    /// The number of bits: 0 for 0, else `log2 n + 1`.
    pub fn bits(&self) -> u64 {
        match self {
            Nat::Small(x) => 64 - limbs::leading_zeros(*x) as u64,
            Nat::Large(v) => limbs::bits(v),
        }
    }

    /// `Nat.log2`: the floor of the binary logarithm, and 0 for 0.
    pub fn log2(&self) -> u64 {
        let b = self.bits();
        if b == 0 { 0 } else { b - 1 }
    }

    /// Bit `i` of the value.
    pub fn bit(&self, i: u64) -> bool {
        match self {
            Nat::Small(x) => i < 64 && (*x >> i) & 1 == 1,
            Nat::Large(v) => limbs::bit(v, i),
        }
    }

    /// Compares two numbers.
    pub fn compare(&self, other: &Nat) -> Ordering {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => {
                if x < y {
                    Ordering::Less
                } else if x > y {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }
            (Nat::Small(_), Nat::Large(_)) => Ordering::Less,
            (Nat::Large(_), Nat::Small(_)) => Ordering::Greater,
            (Nat::Large(a), Nat::Large(b)) => limbs::cmp(a, b),
        }
    }

    /// `Nat.beq`.
    pub fn beq(&self, other: &Nat) -> bool {
        self == other
    }

    /// `Nat.ble`.
    pub fn ble(&self, other: &Nat) -> bool {
        self.compare(other) != Ordering::Greater
    }

    /// `Nat.succ`.
    pub fn succ(&self) -> Nat {
        self.add(&Nat::Small(1))
    }

    /// `Nat.add`.
    pub fn add(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => from_u128(*x as u128 + *y as u128),
            _ => large(Op::Add, self, other),
        }
    }

    /// `Nat.sub`: the difference, or 0 if `other` is larger.
    pub fn sub(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => {
                if x >= y {
                    Nat::Small(x - y)
                } else {
                    Nat::Small(0)
                }
            }
            _ => {
                if self.compare(other) == Ordering::Greater {
                    large(Op::Sub, self, other)
                } else {
                    Nat::Small(0)
                }
            }
        }
    }

    /// `Nat.mul`.
    pub fn mul(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => from_u128(*x as u128 * *y as u128),
            _ => {
                if self.is_zero() || other.is_zero() {
                    Nat::Small(0)
                } else {
                    large(Op::Mul, self, other)
                }
            }
        }
    }

    /// `Nat.div`: the quotient rounded down, and 0 if `other` is 0.
    pub fn div(&self, other: &Nat) -> Nat {
        match (self, other) {
            (_, Nat::Small(0)) => Nat::Small(0),
            (Nat::Small(x), Nat::Small(y)) => Nat::Small(x / y),
            (Nat::Small(_), Nat::Large(_)) => Nat::Small(0),
            _ => large(Op::Div, self, other),
        }
    }

    /// `Nat.mod`: the remainder, and `self` if `other` is 0.
    pub fn rem(&self, other: &Nat) -> Nat {
        match (self, other) {
            (_, Nat::Small(0)) => self.clone(),
            (Nat::Small(x), Nat::Small(y)) => Nat::Small(x % y),
            (Nat::Small(x), Nat::Large(_)) => Nat::Small(*x),
            _ => large(Op::Mod, self, other),
        }
    }

    /// The quotient and the remainder, with the meaning of `div` and `rem`.
    pub fn div_rem(&self, other: &Nat) -> (Nat, Nat) {
        (self.div(other), self.rem(other))
    }

    /// `Nat.gcd`, with `gcd 0 n = n`.
    pub fn gcd(&self, other: &Nat) -> Nat {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            if let (Nat::Small(x), Nat::Small(y)) = (&a, &b) {
                a = Nat::Small(gcd_u64(*x, *y));
                b = Nat::Small(0);
            } else {
                let r = a.rem(&b);
                a = b;
                b = r;
            }
        }
        a
    }

    /// `Nat.land`.
    pub fn land(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => Nat::Small(x & y),
            (Nat::Small(x), Nat::Large(v)) => Nat::Small(x & v[0]),
            (Nat::Large(v), Nat::Small(y)) => Nat::Small(v[0] & y),
            _ => large(Op::And, self, other),
        }
    }

    /// `Nat.lor`.
    pub fn lor(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => Nat::Small(x | y),
            _ => large(Op::Or, self, other),
        }
    }

    /// `Nat.xor`.
    pub fn xor(&self, other: &Nat) -> Nat {
        match (self, other) {
            (Nat::Small(x), Nat::Small(y)) => Nat::Small(x ^ y),
            _ => large(Op::Xor, self, other),
        }
    }

    /// `Nat.shiftLeft`: `self * 2^s`. The caller checks the size of the result first (spec 05.8).
    pub fn shift_left(&self, s: u64) -> Nat {
        match self {
            Nat::Small(0) => Nat::Small(0),
            Nat::Small(x) => {
                if s < 64 && (s == 0 || *x >> (64 - s) == 0) {
                    Nat::Small(*x << s)
                } else {
                    let mut one = Vec::with_capacity(1);
                    one.push(*x);
                    Nat::from_limbs(limbs::shl(&one, s))
                }
            }
            Nat::Large(v) => Nat::from_limbs(limbs::shl(v, s)),
        }
    }

    /// `Nat.shiftRight`: `self / 2^s`, rounded down.
    pub fn shift_right(&self, s: u64) -> Nat {
        match self {
            Nat::Small(x) => {
                if s >= 64 {
                    Nat::Small(0)
                } else {
                    Nat::Small(*x >> s)
                }
            }
            Nat::Large(v) => Nat::from_limbs(limbs::shr(v, s)),
        }
    }

    /// `Nat.shiftRight` with a shift of any size. A shift of 2^64 or more gives 0.
    pub fn shift_right_nat(&self, s: &Nat) -> Nat {
        match s {
            Nat::Small(k) => self.shift_right(*k),
            Nat::Large(_) => Nat::Small(0),
        }
    }

    /// `Nat.pow`: `self ^ e`, with `0 ^ 0 = 1`. The caller checks the size of the result first (spec 05.8).
    pub fn pow(&self, e: u64) -> Nat {
        let mut result = Nat::Small(1);
        let mut base = self.clone();
        let mut k = e;
        while k > 0 {
            if k & 1 == 1 {
                result = result.mul(&base);
            }
            k >>= 1;
            if k > 0 {
                base = base.mul(&base);
            }
        }
        result
    }

    /// The number of a decimal string. The string has one or more ASCII digits and nothing else. Leading zeros are allowed here. The format rules of spec 07.1.2 are the job of the parser.
    pub fn from_decimal(digits: &[u8]) -> Option<Nat> {
        let n = digits.len();
        let mut ok = n > 0;
        let mut i = 0;
        while ok && i < n {
            ok = digits[i] >= b'0' && digits[i] <= b'9';
            i += 1;
        }
        if ok { Some(from_digits(digits)) } else { None }
    }

    /// The decimal string of the number, with no leading zero.
    pub fn to_decimal(&self) -> Vec<u8> {
        match self {
            Nat::Small(x) => u64_digits(*x, false),
            Nat::Large(v) => large_digits(v),
        }
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Nat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Nat {
    fn cmp(&self, other: &Nat) -> Ordering {
        self.compare(other)
    }
}

/// The number for a `u128` value.
fn from_u128(x: u128) -> Nat {
    if x >> 64 == 0 {
        Nat::Small(x as u64)
    } else {
        let mut v = Vec::with_capacity(2);
        v.push(x as u64);
        v.push((x >> 64) as u64);
        Nat::Large(v)
    }
}

fn gcd_u64(x: u64, y: u64) -> u64 {
    let mut a = x;
    let mut b = y;
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

/// The path for large values. At least one operand is `Large`, or the operation has no small path.
fn large(op: Op, a: &Nat, b: &Nat) -> Nat {
    match (a, b) {
        (Nat::Small(x), Nat::Small(y)) => {
            let mut xa = Vec::with_capacity(1);
            xa.push(*x);
            let mut yb = Vec::with_capacity(1);
            yb.push(*y);
            on_limbs(op, &xa, &yb)
        }
        (Nat::Small(x), Nat::Large(v)) => {
            let mut xa = Vec::with_capacity(1);
            xa.push(*x);
            on_limbs(op, &xa, v)
        }
        (Nat::Large(u), Nat::Small(y)) => {
            let mut yb = Vec::with_capacity(1);
            yb.push(*y);
            on_limbs(op, u, &yb)
        }
        (Nat::Large(u), Nat::Large(v)) => on_limbs(op, u, v),
    }
}

/// One operation on limb vectors. The callers have handled division by zero and subtraction below zero.
fn on_limbs(op: Op, a: &[u64], b: &[u64]) -> Nat {
    match op {
        Op::Add => Nat::from_limbs(limbs::add(a, b)),
        Op::Sub => Nat::from_limbs(limbs::sub(a, b)),
        Op::Mul => Nat::from_limbs(limbs::mul(a, b)),
        Op::Div => {
            let (q, _) = limbs::divmod(a, b);
            Nat::from_limbs(q)
        }
        Op::Mod => {
            let (_, r) = limbs::divmod(a, b);
            Nat::from_limbs(r)
        }
        Op::And => Nat::from_limbs(limbs::and(a, b)),
        Op::Or => Nat::from_limbs(limbs::or(a, b)),
        Op::Xor => Nat::from_limbs(limbs::xor(a, b)),
    }
}

/// The value of a string of ASCII digits, which the caller has checked.
fn from_digits(digits: &[u8]) -> Nat {
    let n = digits.len();
    // The first chunk has n mod 19 digits, the other chunks have 19 digits.
    let first = n % 19;
    let mut acc: Vec<u64> = Vec::with_capacity(n / 19 + 1);
    let mut i = 0;
    let mut chunk_end = if first == 0 { 19 } else { first };
    while i < n {
        let mut chunk: u64 = 0;
        let mut scale: u64 = 1;
        while i < chunk_end {
            chunk = chunk * 10 + (digits[i] - b'0') as u64;
            scale *= 10;
            i += 1;
        }
        mul_add_limb(&mut acc, scale, chunk);
        chunk_end += 19;
    }
    Nat::from_limbs(acc)
}

/// `acc = acc * m + a`, in place.
fn mul_add_limb(acc: &mut Vec<u64>, m: u64, a: u64) {
    let mut carry = a as u128;
    let mut i = 0;
    while i < acc.len() {
        let t = acc[i] as u128 * m as u128 + carry;
        acc[i] = t as u64;
        carry = t >> 64;
        i += 1;
    }
    if carry != 0 {
        acc.push(carry as u64);
    }
}

/// The decimal digits of `x`. With `pad`, the result has exactly 19 digits, with leading zeros.
fn u64_digits(x: u64, pad: bool) -> Vec<u8> {
    let mut rev: Vec<u8> = Vec::with_capacity(20);
    let mut y = x;
    let mut more = true;
    while more {
        rev.push(b'0' + (y % 10) as u8);
        y /= 10;
        more = y != 0 || (pad && rev.len() < 19);
    }
    let mut out = Vec::with_capacity(rev.len());
    let mut i = rev.len();
    while i > 0 {
        i -= 1;
        out.push(rev[i]);
    }
    out
}

/// The decimal digits of a large value: repeated division by 10^19.
fn large_digits(v: &[u64]) -> Vec<u8> {
    let mut chunks: Vec<u64> = Vec::with_capacity(v.len() * 2);
    let mut cur = limbs::part(v, 0, v.len());
    while limbs::used_len(&cur) > 0 {
        let (q, r) = limbs::divmod_limb(&cur, TEN19);
        chunks.push(r);
        cur = q;
    }
    let mut out: Vec<u8> = Vec::with_capacity(chunks.len() * 19);
    let mut i = chunks.len();
    while i > 0 {
        i -= 1;
        let d = u64_digits(chunks[i], i + 1 != chunks.len());
        let mut j = 0;
        while j < d.len() {
            out.push(d[j]);
            j += 1;
        }
    }
    out
}
