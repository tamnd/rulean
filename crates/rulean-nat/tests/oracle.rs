//! Differential tests against `num-bigint`, the test oracle of spec 04.6.

use num_bigint::BigUint;
use rulean_nat::Nat;

/// A small deterministic generator (xorshift64*), so that each run tests the same numbers.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    /// A number with up to `max_limbs` limbs. Some limbs are 0 or all ones, to test the carries.
    fn nat(&mut self, max_limbs: u64) -> Vec<u64> {
        let n = self.next() % (max_limbs + 1);
        (0..n)
            .map(|_| match self.next() % 5 {
                0 => 0,
                1 => u64::MAX,
                _ => self.next(),
            })
            .collect()
    }
}

fn big(v: &[u64]) -> BigUint {
    BigUint::from_slice(
        &v.iter()
            .flat_map(|x| [*x as u32, (*x >> 32) as u32])
            .collect::<Vec<u32>>(),
    )
}

fn to_big(n: &Nat) -> BigUint {
    match n {
        Nat::Small(x) => BigUint::from(*x),
        Nat::Large(v) => big(v),
    }
}

fn canonical(n: &Nat) -> bool {
    match n {
        Nat::Small(_) => true,
        Nat::Large(v) => v.len() >= 2 && v[v.len() - 1] != 0,
    }
}

fn check(what: &str, got: Nat, want: BigUint) {
    assert!(canonical(&got), "{what}: not canonical: {got:?}");
    assert_eq!(to_big(&got), want, "{what}");
}

fn pairs(seed: u64, count: usize, max_limbs: u64) -> Vec<(Vec<u64>, Vec<u64>)> {
    let mut rng = Rng(seed);
    (0..count)
        .map(|_| (rng.nat(max_limbs), rng.nat(max_limbs)))
        .collect()
}

#[test]
fn arithmetic_agrees_with_num_bigint() {
    for (a, b) in pairs(1, 3000, 6) {
        let (x, y) = (Nat::from_limbs(a.clone()), Nat::from_limbs(b.clone()));
        let (bx, by) = (big(&a), big(&b));
        check("add", x.add(&y), &bx + &by);
        let diff = if bx >= by { &bx - &by } else { BigUint::ZERO };
        check("sub", x.sub(&y), diff);
        check("mul", x.mul(&y), &bx * &by);
        if by == BigUint::ZERO {
            check("div by 0", x.div(&y), BigUint::ZERO);
            check("mod by 0", x.rem(&y), bx.clone());
        } else {
            check("div", x.div(&y), &bx / &by);
            check("mod", x.rem(&y), &bx % &by);
        }
        check("gcd", x.gcd(&y), num_integer_gcd(&bx, &by));
        check("land", x.land(&y), &bx & &by);
        check("lor", x.lor(&y), &bx | &by);
        check("xor", x.xor(&y), &bx ^ &by);
        assert_eq!(x.compare(&y), bx.cmp(&by));
        assert_eq!(x.beq(&y), bx == by);
        assert_eq!(x.ble(&y), bx <= by);
    }
}

/// The divisor has a top limb that makes the quotient estimate of algorithm D too large, which tests the add-back step.
#[test]
fn division_with_the_add_back_step() {
    let mut rng = Rng(7);
    for _ in 0..2000 {
        let n = 2 + (rng.next() % 4) as usize;
        let mut b: Vec<u64> = (0..n).map(|_| rng.next()).collect();
        b[n - 1] = 1u64 << 63 | (rng.next() & 0xff);
        let mut a: Vec<u64> = (0..n + 2).map(|_| rng.next()).collect();
        a[n + 1] = b[n - 1] - 1;
        a[n] = u64::MAX;
        let (x, y) = (Nat::from_limbs(a.clone()), Nat::from_limbs(b.clone()));
        check("div", x.div(&y), big(&a) / big(&b));
        check("mod", x.rem(&y), big(&a) % big(&b));
    }
}

#[test]
fn karatsuba_agrees_with_num_bigint() {
    let mut rng = Rng(3);
    for (na, nb) in [
        (32, 32),
        (33, 40),
        (64, 64),
        (100, 37),
        (32, 500),
        (257, 129),
    ] {
        let a: Vec<u64> = (0..na).map(|_| rng.next()).collect();
        let b: Vec<u64> = (0..nb).map(|_| rng.next()).collect();
        check(
            "karatsuba",
            Nat::from_limbs(a.clone()).mul(&Nat::from_limbs(b.clone())),
            big(&a) * big(&b),
        );
        let ones = vec![u64::MAX; na];
        check(
            "karatsuba ones",
            Nat::from_limbs(ones.clone()).mul(&Nat::from_limbs(ones.clone())),
            big(&ones) * big(&ones),
        );
    }
}

#[test]
fn large_division_agrees_with_num_bigint() {
    let mut rng = Rng(11);
    for _ in 0..200 {
        let a = rng.nat(80);
        let b = rng.nat(40);
        if big(&b) == BigUint::ZERO {
            continue;
        }
        let (x, y) = (Nat::from_limbs(a.clone()), Nat::from_limbs(b.clone()));
        check("div", x.div(&y), big(&a) / big(&b));
        check("mod", x.rem(&y), big(&a) % big(&b));
    }
}

#[test]
fn shifts_bits_and_pow() {
    let mut rng = Rng(5);
    for _ in 0..1000 {
        let a = rng.nat(4);
        let s = rng.next() % 300;
        let x = Nat::from_limbs(a.clone());
        let bx = big(&a);
        check("shl", x.shift_left(s), &bx << s);
        check("shr", x.shift_right(s), &bx >> s);
        assert_eq!(x.bits(), bx.bits());
        assert_eq!(x.log2(), bx.bits().saturating_sub(1));
        assert_eq!(x.bit(s), bx.bit(s));
        let e = rng.next() % 40;
        check("pow", x.pow(e), bx.pow(e as u32));
    }
    check("0^0", Nat::zero().pow(0), BigUint::from(1u8));
    check(
        "shr by 2^64",
        Nat::from_u64(5).shift_right_nat(&Nat::from_limbs(vec![0, 1])),
        BigUint::ZERO,
    );
}

#[test]
fn decimal_round_trip() {
    let mut rng = Rng(9);
    for _ in 0..1000 {
        let a = rng.nat(8);
        let x = Nat::from_limbs(a.clone());
        let text = big(&a).to_str_radix(10);
        assert_eq!(String::from_utf8(x.to_decimal()).expect("utf8"), text);
        assert_eq!(Nat::from_decimal(text.as_bytes()), Some(x));
    }
    for (s, want) in [
        ("0", Some(0u64)),
        ("007", Some(7)),
        ("18446744073709551615", Some(u64::MAX)),
    ] {
        assert_eq!(Nat::from_decimal(s.as_bytes()), want.map(Nat::from_u64));
    }
    assert_eq!(
        Nat::from_decimal(b"18446744073709551616"),
        Some(Nat::from_limbs(vec![0, 1]))
    );
    for bad in ["", "-1", "1e3", " 1", "1.0", "x"] {
        assert_eq!(Nat::from_decimal(bad.as_bytes()), None, "{bad:?}");
    }
    assert_eq!(
        Nat::from_u64(10_000_000_000_000_000_000).to_decimal(),
        b"10000000000000000000"
    );
}

#[test]
fn canonical_form() {
    assert_eq!(Nat::from_limbs(vec![]), Nat::Small(0));
    assert_eq!(Nat::from_limbs(vec![5, 0, 0]), Nat::Small(5));
    assert_eq!(Nat::from_limbs(vec![0, 1, 0]), Nat::Large(vec![0, 1]));
    let two64 = Nat::from_limbs(vec![0, 1]);
    check(
        "2^64 - 1",
        two64.sub(&Nat::from_u64(1)),
        BigUint::from(u64::MAX),
    );
    check("succ max", Nat::from_u64(u64::MAX).succ(), big(&[0, 1]));
    assert_eq!(two64.limb_count(), 2);
    assert_eq!(Nat::zero().limb_count(), 0);
    assert_eq!(two64.to_u64(), None);
}

fn num_integer_gcd(a: &BigUint, b: &BigUint) -> BigUint {
    let (mut x, mut y) = (a.clone(), b.clone());
    while y != BigUint::ZERO {
        let r = &x % &y;
        x = y;
        y = r;
    }
    x
}
