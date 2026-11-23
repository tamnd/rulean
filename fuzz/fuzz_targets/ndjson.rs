//! The NDJSON parser (spec 07.1). Each input must give an export or an error, and never a panic.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut st = rulean_store::Store::new();
    let _ = rulean_format::parse_export(&mut st, data);
});
