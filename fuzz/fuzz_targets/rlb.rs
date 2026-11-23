//! The `.rlb` decoder (spec 07.2). Each input must give an export or an error, and never a panic.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut st = rulean_store::Store::new();
    let _ = rulean_format::rlb::decode(&mut st, data);
});
