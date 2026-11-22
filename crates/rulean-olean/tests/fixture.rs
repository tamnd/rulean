//! Tests on the real files of `Init.Control.Do` of Lean v4.36.0 (see `tests/fixtures/v4.36.0/README.md`).
//!
//! The reader treats each byte as hostile input (spec 07.3). So a damaged file must give an error or a result, and never a panic, a hang or a large allocation.

use std::path::{Path, PathBuf};

use rulean_olean::{FaultKind, read_module};
use rulean_store::Store;

const MODULE: &str = "Init.Control.Do";
const PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/v4.36.0")
}

fn originals() -> Vec<Vec<u8>> {
    PARTS
        .iter()
        .map(|x| {
            std::fs::read(fixtures().join("Init/Control/Do").with_extension(x)).expect("fixture")
        })
        .collect()
}

/// A directory in the temporary directory with a name for this test only.
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("rulean-olean-{}-{name}", std::process::id()));
    std::fs::create_dir_all(d.join("Init/Control")).expect("scratch directory");
    d
}

/// Writes the parts into `dir` and decodes the module. `None` leaves a part out.
fn decode(dir: &Path, parts: &[Option<&[u8]>]) -> Result<usize, FaultKind> {
    for (x, b) in PARTS.iter().zip(parts) {
        let p = dir.join("Init/Control/Do").with_extension(x);
        match b {
            Some(b) => std::fs::write(&p, b).expect("write"),
            None => {
                let _ = std::fs::remove_file(&p);
            }
        }
    }
    let mut st = Store::new();
    read_module(&mut st, &[dir.to_path_buf()], MODULE)
        .map(|m| m.decls.len())
        .map_err(|e| e.kind)
}

/// A small generator of random numbers (xorshift64), so that each run damages the same bytes.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn the_fixture_decodes() {
    let mut st = Store::new();
    let m = read_module(&mut st, &[fixtures()], MODULE).expect("the fixture decodes");
    assert!(
        m.imports.iter().any(|x| x == "Init.Control.Except"),
        "{:?}",
        m.imports
    );
    assert!(!m.decls.is_empty());
    let names: Vec<Vec<u8>> = m.decls.iter().map(|d| st.name_text(d.name())).collect();
    assert!(
        names.iter().any(|n| n == b"EarlyReturnT.return"),
        "EarlyReturnT.return is missing"
    );
}

#[test]
fn a_missing_private_part_is_reported() {
    let o = originals();
    let d = scratch("private");
    let got = decode(&d, &[Some(&o[0]), Some(&o[1]), None]);
    assert_eq!(got, Err(FaultKind::Missing));
    std::fs::remove_dir_all(d).expect("remove");
}

#[test]
fn a_cut_file_is_an_error() {
    let o = originals();
    let d = scratch("cut");
    for p in 0..3 {
        let mut n = 0;
        while n < o[p].len() {
            let mut parts: Vec<Option<&[u8]>> = o.iter().map(|b| Some(&b[..])).collect();
            parts[p] = Some(&o[p][..n]);
            assert!(decode(&d, &parts).is_err(), "part {p} cut at {n}");
            n += 1 + n / 16;
        }
    }
    std::fs::remove_dir_all(d).expect("remove");
}

#[test]
fn damaged_bytes_never_panic() {
    let o = originals();
    let d = scratch("damage");
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut errors = 0;
    let rounds = 1500;
    for i in 0..rounds {
        let p = i % 3;
        let mut b = o[p].clone();
        // Change one to four bytes. Half of the changes write a small number, because a small number is more likely to be a valid tag, size or pointer.
        let k = 1 + (rng.next() % 4) as usize;
        for _ in 0..k {
            let at = (rng.next() as usize) % b.len();
            let r = rng.next();
            b[at] = if r & 1 == 0 {
                (r >> 8) as u8
            } else {
                ((r >> 8) % 8) as u8
            };
        }
        let mut parts: Vec<Option<&[u8]>> = o.iter().map(|x| Some(&x[..])).collect();
        parts[p] = Some(&b);
        if decode(&d, &parts).is_err() {
            errors += 1;
        }
    }
    // Most changes hit a header, a pointer or a tag, so most of them must give an error.
    assert!(
        errors > rounds / 4,
        "only {errors} of {rounds} damaged files give an error"
    );
    std::fs::remove_dir_all(d).expect("remove");
}
