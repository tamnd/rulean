//! Runs the checker on the Arena tests in `_tmp/arena/tests`. If the Arena is not there, the tests do nothing.
//!
//! A test in `good` must be accepted in full. A test in `bad` must have a rejected declaration. The checker can decline a test with `Unsupported`, and the test then counts as declined, not as wrong. A declined test must not have a rejection before the declined declaration.

use rulean_core::tc::{Checker, ErrorKind};
use rulean_store::Store;
use std::path::{Path, PathBuf};

const ACCEPT: u8 = 0;
const REJECT: u8 = 1;
const DECLINE: u8 = 2;

struct Run {
    verdict: u8,
    text: String,
}

fn root() -> PathBuf {
    PathBuf::from(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../_tmp/arena/tests"
    ))
}

fn check_file(path: &Path) -> Run {
    let input = std::fs::read(path).expect("the test file reads");
    let mut st = Store::new();
    let decls = match rulean_format::parse(&mut st, &input) {
        Ok(d) => d,
        Err(e) => {
            return Run {
                verdict: REJECT,
                text: format!("parse error {:?}", e),
            };
        }
    };
    let mut c = Checker::new(st);
    for d in &decls {
        if let Some(f) = c.add_decl(d) {
            let n = String::from_utf8_lossy(&c.st.name_text(d.name())).into_owned();
            let verdict = if f.kind == ErrorKind::Unsupported {
                DECLINE
            } else {
                REJECT
            };
            return Run {
                verdict,
                text: format!("{:?} at {}", f.kind, n),
            };
        }
    }
    Run {
        verdict: ACCEPT,
        text: String::new(),
    }
}

/// Runs `check_file` in a thread with a large stack, because the checker recurses on the depth of the terms.
fn check_big_stack(path: &Path) -> Run {
    let p = path.to_path_buf();
    let h = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || check_file(&p))
        .expect("the thread starts");
    h.join().expect("the checker does not panic")
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).expect("the directory reads") {
        let p = e.expect("the entry reads").path();
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().is_some_and(|x| x == "ndjson") {
            out.push(p);
        }
    }
}

/// The Init prelude has many inductives. All declarations before the first nested inductive must be accepted.
#[test]
fn init_prelude() {
    let path = root().join("good/init-prelude.ndjson");
    if !path.exists() {
        return;
    }
    let r = check_big_stack(&path);
    assert!(r.verdict != REJECT, "the prelude is rejected: {}", r.text);
}

/// All Arena tests. This test is slow, so it runs only with `--ignored`.
#[test]
#[ignore]
fn arena_all() {
    let dir = root();
    if !dir.exists() {
        return;
    }
    let mut files = Vec::new();
    walk(&dir, &mut files);
    files.sort();
    let mut wrong: Vec<String> = Vec::new();
    let mut declined = 0;
    for f in &files {
        let good = f
            .strip_prefix(&dir)
            .expect("the path is in the root")
            .starts_with("good");
        let t0 = std::time::Instant::now();
        let r = check_big_stack(f);
        let ms = t0.elapsed().as_millis();
        let name = f
            .strip_prefix(&dir)
            .expect("the path is in the root")
            .display()
            .to_string();
        let tag = if r.verdict == DECLINE {
            declined += 1;
            "decline"
        } else if (r.verdict == ACCEPT) == good {
            "ok"
        } else {
            wrong.push(name.clone());
            "WRONG"
        };
        println!("{tag}\t{ms}ms\t{name}\t{}", r.text);
    }
    println!(
        "{} tests, {} wrong, {declined} declined",
        files.len(),
        wrong.len()
    );
    assert!(wrong.is_empty(), "wrong verdicts: {:?}", wrong);
}
