//! Tests of the caches of `memo`.

use rulean_core::memo::Lossy;
use rulean_store::Raw;

#[test]
fn a_lossy_cache_gives_the_value_of_a_pair_it_keeps() {
    let mut c = Lossy::new();
    assert_eq!(c.get(1, 2), None);
    c.put(1, 2, 7);
    assert_eq!(c.get(1, 2), Some(7));
    assert!(c.contains(1, 2));
    // The key has an order, so the pair (2, 1) is a different key.
    assert_eq!(c.get(2, 1), None);
}

#[test]
fn a_lossy_cache_is_empty_after_the_clear() {
    let mut c = Lossy::new();
    c.put(3, 0, 9);
    c.clear();
    assert_eq!(c.get(3, 0), None);
    c.put(3, 0, 10);
    assert_eq!(c.get(3, 0), Some(10));
}

#[test]
fn a_lossy_cache_never_gives_a_wrong_value() {
    // More pairs than slots, so some pairs replace others. A pair that the cache keeps has its own value.
    let mut c = Lossy::new();
    let n: Raw = 1 << 15;
    for i in 0..n {
        c.put(i, i + 1, i * 3);
    }
    let mut kept = 0;
    for i in 0..n {
        if let Some(v) = c.get(i, i + 1) {
            assert_eq!(v, i * 3);
            kept += 1;
        }
    }
    assert!(kept > 0);
    assert!(kept < n);
}
