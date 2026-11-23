//! The `.olean` reader on the parts of one module (spec 07.3.5). The input layout is in `src/lib.rs`. Each input must give a module or an error, and never a panic.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let parts = rulean_fuzz::split(data);
    let mut st = rulean_store::Store::new();
    let _ = rulean_olean::decode_parts(&mut st, parts);
});
