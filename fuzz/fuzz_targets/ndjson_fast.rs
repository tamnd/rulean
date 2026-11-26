//! The template fast path of the NDJSON parser (spec perf/05.3). The parse with the fast path and the parse without it must give the same result and the same store on each input.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut a = rulean_store::Store::new();
    let mut b = rulean_store::Store::new();
    let ra = rulean_format::parse_export_with(&mut a, data, true);
    let rb = rulean_format::parse_export_with(&mut b, data, false);
    assert_eq!(ra, rb);
    assert_eq!(a.memory(), b.memory());
    assert_eq!(a.interns(), b.interns());
});
