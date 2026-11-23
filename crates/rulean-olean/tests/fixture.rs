//! Tests on the real files of `Init.Control.Do` of Lean v4.36.0 (olean format version 2) and v4.37.0-rc1 (version 4). See the README of each directory in `tests/fixtures`.
//!
//! The reader treats each byte as hostile input (spec 07.3). So a damaged file must give an error or a result, and never a panic, a hang or a large allocation.

use std::path::{Path, PathBuf};

use rulean_olean::{FaultKind, decode_parts, read_module};
use rulean_store::Store;

const MODULE: &str = "Init.Control.Do";
const PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

/// The Lean releases of the fixtures.
const RELEASES: [&str; 2] = ["v4.36.0", "v4.37.0-rc1"];

fn fixtures(release: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(release)
}

fn originals(release: &str) -> Vec<Vec<u8>> {
    PARTS
        .iter()
        .map(|x| {
            std::fs::read(fixtures(release).join("Init/Control/Do").with_extension(x))
                .expect("fixture")
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
    for r in RELEASES {
        let mut st = Store::new();
        let m = read_module(&mut st, &[fixtures(r)], MODULE).expect("the fixture decodes");
        assert!(
            m.imports.iter().any(|x| x == "Init.Control.Except"),
            "{r}: {:?}",
            m.imports
        );
        assert!(!m.decls.is_empty());
        let names: Vec<Vec<u8>> = m.decls.iter().map(|d| st.name_text(d.name())).collect();
        assert!(
            names.iter().any(|n| n == b"EarlyReturnT.return"),
            "{r}: EarlyReturnT.return is missing"
        );
    }
}

#[test]
fn bytes_in_memory_decode_as_the_files() {
    for r in RELEASES {
        let mut st = Store::new();
        let files = read_module(&mut st, &[fixtures(r)], MODULE).expect("the fixture decodes");
        let mut st2 = Store::new();
        let o = originals(r);
        let mem = decode_parts(
            &mut st2,
            [Some(o[0].clone()), Some(o[1].clone()), Some(o[2].clone())],
        )
        .expect("the bytes decode");
        assert_eq!(mem.imports, files.imports, "{r}");
        let names = |st: &Store, ds: &[rulean_format::Decl]| -> Vec<Vec<u8>> {
            ds.iter().map(|d| st.name_text(d.name())).collect()
        };
        assert_eq!(names(&st2, &mem.decls), names(&st, &files.decls), "{r}");
        let e = decode_parts(
            &mut Store::new(),
            [Some(o[0].clone()), Some(o[1].clone()), None],
        )
        .expect_err("no private part");
        assert_eq!(e.kind, FaultKind::Missing, "{r}");
        assert_eq!(
            e.file.as_deref(),
            Some(Path::new("mem.olean.private")),
            "{r}"
        );
    }
}

#[test]
fn a_missing_private_part_is_reported() {
    for r in RELEASES {
        let o = originals(r);
        let d = scratch(&format!("private-{r}"));
        let got = decode(&d, &[Some(&o[0]), Some(&o[1]), None]);
        assert_eq!(got, Err(FaultKind::Missing), "{r}");
        std::fs::remove_dir_all(d).expect("remove");
    }
}

#[test]
fn a_cut_file_is_an_error() {
    for r in RELEASES {
        let o = originals(r);
        let d = scratch(&format!("cut-{r}"));
        for p in 0..3 {
            let mut n = 0;
            while n < o[p].len() {
                let mut parts: Vec<Option<&[u8]>> = o.iter().map(|b| Some(&b[..])).collect();
                parts[p] = Some(&o[p][..n]);
                assert!(decode(&d, &parts).is_err(), "{r}: part {p} cut at {n}");
                n += 1 + n / 16;
            }
        }
        std::fs::remove_dir_all(d).expect("remove");
    }
}

#[test]
fn damaged_bytes_never_panic() {
    for r in RELEASES {
        let o = originals(r);
        let d = scratch(&format!("damage-{r}"));
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
            "{r}: only {errors} of {rounds} damaged files give an error"
        );
        std::fs::remove_dir_all(d).expect("remove");
    }
}

/// The word at `off` of `b`.
fn word(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(b[off..off + 8].try_into().expect("8 bytes"))
}

/// The part and the offset that the pointer `ptr` points to. The base address of a part is at offset 80 of its header.
fn locate(o: &[Vec<u8>], ptr: u64) -> (usize, usize) {
    for (i, b) in o.iter().enumerate() {
        let base = word(b, 80);
        if ptr >= base && ptr - base < b.len() as u64 {
            return (i, (ptr - base) as usize);
        }
    }
    panic!("the pointer {ptr:#x} is outside the parts");
}

/// The field `k` of the object at `(part, off)`.
fn field(o: &[Vec<u8>], at: (usize, usize), k: usize) -> u64 {
    word(&o[at.0], at.1 + 8 + 8 * k)
}

/// The position of field `k` of the module data of the private part of the version 4 fixture. The root pointer of a version 4 file is at offset 96.
fn module_data_field(o: &[Vec<u8>], k: usize) -> (usize, usize) {
    let md = locate(o, word(&o[2], 96));
    (md.0, md.1 + 8 + 8 * k)
}

#[test]
fn a_version_4_module_without_a_constant_trie_is_malformed() {
    let mut o = originals("v4.37.0-rc1");
    let (p, off) = module_data_field(&o, 5);
    // The boxed scalar 0 is `none`.
    o[p][off..off + 8].copy_from_slice(&1u64.to_le_bytes());
    let d = scratch("no-trie");
    let parts: Vec<Option<&[u8]>> = o.iter().map(|x| Some(&x[..])).collect();
    assert_eq!(decode(&d, &parts), Err(FaultKind::Malformed));
    std::fs::remove_dir_all(d).expect("remove");
}

#[test]
fn a_wrong_cached_hash_in_the_constant_trie_is_malformed() {
    let mut o = originals("v4.37.0-rc1");
    let (p, off) = module_data_field(&o, 5);
    let some = locate(&o, word(&o[p], off));
    let root = locate(&o, field(&o, some, 0));
    // The root is an `inner` node: the key and the children.
    let kids = locate(&o, field(&o, root, 1));
    let first = locate(&o, word(&o[kids.0], kids.1 + 24));
    let key = locate(&o, field(&o, first, 0));
    // A name object has two object fields and then the cached hash.
    let h = key.1 + 24;
    o[key.0][h] ^= 1;
    let d = scratch("hash");
    let parts: Vec<Option<&[u8]>> = o.iter().map(|x| Some(&x[..])).collect();
    assert_eq!(decode(&d, &parts), Err(FaultKind::Malformed));
    std::fs::remove_dir_all(d).expect("remove");
}

#[test]
fn a_module_above_the_budget_is_store_full() {
    // The reader checks the parts and the tables of the decoder before it allocates the tables (spec 05.11.1).
    for r in RELEASES {
        let mut st = Store::new();
        st.set_max_bytes(st.memory().total() + 1024);
        let e = read_module(&mut st, &[fixtures(r)], MODULE).expect_err("over the budget");
        assert_eq!(e.kind, FaultKind::StoreFull, "{r}");
        let mut st = Store::new();
        st.set_max_bytes(st.memory().total() + (256 << 20));
        assert!(read_module(&mut st, &[fixtures(r)], MODULE).is_ok(), "{r}");
    }
}
