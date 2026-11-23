//! The fuzz finds of spec 11.5.1. Each file in `tests/fuzz` is an input that made a reader panic, hang or allocate too much. Each one must now give an error.

use std::path::Path;

use rulean_store::Store;

#[test]
fn each_fuzz_find_gives_an_error() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fuzz");
    let mut n = 0;
    for e in std::fs::read_dir(&dir).expect("tests/fuzz") {
        let p = e.expect("entry").path();
        let b = std::fs::read(&p).expect("read");
        let mut st = Store::new();
        let r = match p.extension().and_then(|x| x.to_str()) {
            Some("rlb") => rulean_format::rlb::decode(&mut st, &b).map(|_| ()),
            _ => rulean_format::parse_export(&mut st, &b).map(|_| ()),
        };
        assert!(r.is_err(), "{}", p.display());
        n += 1;
    }
    assert!(n > 0);
}
