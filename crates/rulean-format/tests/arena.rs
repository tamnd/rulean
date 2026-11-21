//! Every Arena test must parse. The bad tests are bad for the type checker, not for the parser.
//!
//! The test reads the directory in `RULEAN_ARENA`, or `_tmp/arena/tests` in the repository. If neither exists, the test prints a note and passes. CI fetches the Arena first (see `scripts/arena-fetch.sh`).

use std::path::{Path, PathBuf};

fn arena_dir() -> Option<PathBuf> {
    let dir = match std::env::var_os("RULEAN_ARENA") {
        Some(d) => PathBuf::from(d),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("../../_tmp/arena/tests"),
    };
    if dir.is_dir() { Some(dir) } else { None }
}

fn files(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read the directory")
        .map(|e| e.expect("a directory entry").path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            files(&p, out);
        } else if p.extension().is_some_and(|x| x == "ndjson") {
            out.push(p);
        }
    }
}

#[test]
fn every_arena_test_parses() {
    let Some(dir) = arena_dir() else {
        eprintln!("note: no Arena directory, so the test does nothing");
        return;
    };
    let mut paths = Vec::new();
    files(&dir, &mut paths);
    assert!(!paths.is_empty(), "no .ndjson files in {}", dir.display());
    let mut failures = Vec::new();
    let mut decls = 0;
    for p in &paths {
        let input = std::fs::read(p).expect("read the test");
        let mut store = rulean_store::Store::new();
        match rulean_format::parse(&mut store, &input) {
            Ok(d) => decls += d.len(),
            Err(e) => failures.push(format!(
                "{}: line {}: {}",
                p.display(),
                e.line,
                e.kind.text()
            )),
        }
    }
    eprintln!("{} files, {} declarations", paths.len(), decls);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
