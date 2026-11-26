//! Tests of the caches of `memo`.

use rulean_core::memo::{Lossy, Memo};
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

#[test]
fn a_memo_truncate_removes_the_new_entries_and_keeps_the_old_entries() {
    let mut m = Memo::new();
    m.put(1, 0, 10);
    m.put(2, 0, 20);
    let n = m.len();
    m.put(3, 0, 30);
    m.put(4, 0, 40);
    m.truncate(n);
    assert_eq!(m.get(1, 0), Some(10));
    assert_eq!(m.get(2, 0), Some(20));
    assert_eq!(m.get(3, 0), None);
    assert_eq!(m.get(4, 0), None);
    // A new entry takes the index of a removed entry. The table keeps the slot of the removed key, but a lookup compares the full key.
    m.put(5, 0, 50);
    assert_eq!(m.get(5, 0), Some(50));
    assert_eq!(m.get(3, 0), None);
    m.put(3, 0, 31);
    assert_eq!(m.get(3, 0), Some(31));
    assert_eq!(m.get(5, 0), Some(50));
    assert_eq!(m.len(), 4);
}
