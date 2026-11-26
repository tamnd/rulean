//! The template fast path of the parser (spec perf/05.3) gives the same result as the general parser on each input.
//!
//! Each case parses one input two times, with the fast path and without it, into two new stores. The two results must be equal: the same declarations or the same error, and the same store. The test reads the Arena tests too, from `RULEAN_ARENA` or `_tmp/arena/tests`, if the directory exists.

use std::path::{Path, PathBuf};

use rulean_format::parse_export_with;
use rulean_store::Store;

const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.36.0"}}}"#;

/// The records of a small export. Each line has the form of lean4export. The fast path reads each line except the meta line and the declarations.
const BASE: &[&str] = &[
    r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
    r#"{"in":2,"num":{"i":3,"pre":1}}"#,
    r#"{"in":3,"str":{"pre":1,"str":"größe α"}}"#,
    r#"{"il":1,"param":1}"#,
    r#"{"il":2,"succ":1}"#,
    r#"{"il":3,"max":[1,2]}"#,
    r#"{"il":4,"imax":[2,3]}"#,
    r#"{"ie":0,"sort":0}"#,
    r#"{"ie":1,"sort":4}"#,
    r#"{"bvar":0,"ie":2}"#,
    r#"{"const":{"name":1,"us":[]},"ie":3}"#,
    r#"{"const":{"name":2,"us":[1,3]},"ie":4}"#,
    r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
    r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
    r#"{"ie":7,"lam":{"binderInfo":"implicit","body":2,"name":1,"type":0}}"#,
    r#"{"forallE":{"binderInfo":"instImplicit","body":0,"name":3,"type":0},"ie":8}"#,
    r#"{"forallE":{"binderInfo":"strictImplicit","body":0,"name":3,"type":0},"ie":9}"#,
    r#"{"ie":10,"letE":{"body":2,"name":1,"nondep":false,"type":0,"value":3}}"#,
    r#"{"ie":11,"letE":{"body":2,"name":1,"nondep":true,"type":0,"value":3}}"#,
    r#"{"ie":12,"proj":{"idx":0,"struct":5,"typeName":1}}"#,
    r#"{"ie":13,"natVal":"0"}"#,
    r#"{"ie":14,"natVal":"123456789012345678901234567890"}"#,
    r#"{"ie":15,"strVal":"hello, world"}"#,
    r#"{"ie":16,"strVal":""}"#,
    r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#,
];

/// Parses `input` with and without the fast path, checks that the results are equal, and gives the number of lines that the fast path read.
fn same(input: &[u8]) -> u64 {
    let mut a = Store::new();
    let mut b = Store::new();
    let ra = parse_export_with(&mut a, input, true);
    let rb = parse_export_with(&mut b, input, false);
    let text = String::from_utf8_lossy(input);
    assert_eq!(ra, rb, "input:\n{text}");
    assert_eq!(a.memory(), b.memory(), "input:\n{text}");
    assert_eq!(a.interns(), b.interns(), "input:\n{text}");
    let mut s = rulean_format::Stream::new();
    let mut st = Store::new();
    let mut start = 0;
    while s.ok() && start < input.len() {
        let mut j = start;
        while j < input.len() && input[j] != b'\n' {
            j += 1;
        }
        if j < input.len() {
            s.line(&mut st, &input[start..j]);
        }
        start = j + 1;
    }
    s.fast_lines()
}

fn export(lines: &[&str]) -> String {
    let mut out = String::from(META);
    out.push('\n');
    for l in lines {
        out.push_str(l);
        out.push('\n');
    }
    out
}

#[test]
fn the_fast_path_reads_the_lean4export_forms() {
    let n = same(export(BASE).as_bytes());
    // Each line except the meta line, the declaration and the lines that grow an index table. The general parser reads these, because it checks the memory budget after the store call (spec perf/05.4). In this export, the three tables grow at most 9 times in total.
    assert!(n + 9 >= BASE.len() as u64 - 1, "{n} lines on the fast path");
}

/// Changes of one line of `BASE`. Each change must give the same result on the two paths. Most of them go to the general parser, and some of them are errors.
const CHANGES: &[(&str, &str)] = &[
    // Spaces and order.
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2, "fn":3},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":5} "#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"fn":3,"arg":2},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"ie":5,"app":{"arg":2,"fn":3}}"#,
    ),
    // Numbers.
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":02,"fn":3},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":-2,"fn":3},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2.0,"fn":3},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":18446744073709551616}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":9999999999999999999}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":268435457}"#,
    ),
    (r#"{"bvar":0,"ie":2}"#, r#"{"bvar":4294967296,"ie":2}"#),
    (r#"{"bvar":0,"ie":2}"#, r#"{"bvar":4294967295,"ie":2}"#),
    (
        r#"{"ie":12,"proj":{"idx":0,"struct":5,"typeName":1}}"#,
        r#"{"ie":12,"proj":{"idx":4294967296,"struct":5,"typeName":1}}"#,
    ),
    // Indices.
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":99},"ie":5}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":4}"#,
    ),
    (
        r#"{"app":{"arg":2,"fn":3},"ie":5}"#,
        r#"{"app":{"arg":2,"fn":3},"ie":5000}"#,
    ),
    (
        r#"{"in":2,"num":{"i":3,"pre":1}}"#,
        r#"{"in":1,"num":{"i":3,"pre":1}}"#,
    ),
    (
        r#"{"in":2,"num":{"i":3,"pre":1}}"#,
        r#"{"in":2,"num":{"i":3,"pre":7}}"#,
    ),
    (r#"{"il":3,"max":[1,2]}"#, r#"{"il":3,"max":[1,9]}"#),
    (r#"{"il":3,"max":[1,2]}"#, r#"{"il":2,"max":[1,2]}"#),
    (r#"{"ie":1,"sort":4}"#, r#"{"ie":1,"sort":40}"#),
    (
        r#"{"const":{"name":2,"us":[1,3]},"ie":4}"#,
        r#"{"const":{"name":2,"us":[1,30]},"ie":4}"#,
    ),
    (r#"{"il":1,"param":1}"#, r#"{"il":1,"param":10}"#),
    // Lists.
    (r#"{"il":3,"max":[1,2]}"#, r#"{"il":3,"max":[1,2,1]}"#),
    (r#"{"il":3,"max":[1,2]}"#, r#"{"il":3,"max":[1]}"#),
    (
        r#"{"const":{"name":2,"us":[1,3]},"ie":4}"#,
        r#"{"const":{"name":2,"us":[1,]},"ie":4}"#,
    ),
    (
        r#"{"const":{"name":2,"us":[1,3]},"ie":4}"#,
        r#"{"const":{"name":2,"us":[,1]},"ie":4}"#,
    ),
    (
        r#"{"const":{"name":2,"us":[1,3]},"ie":4}"#,
        r#"{"const":{"name":2,"us":[1 ,3]},"ie":4}"#,
    ),
    // Strings.
    (
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        r#"{"in":1,"str":{"pre":0,"str":"N\"at"}}"#,
    ),
    (
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"N\tat\"}}",
    ),
    (
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        r#"{"in":1,"str":{"pre":0,"str":"Nat}}"#,
    ),
    (
        r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
        r#"{"in":1,"str":{"pre":0,"str":3}}"#,
    ),
    (
        r#"{"ie":15,"strVal":"hello, world"}"#,
        r#"{"ie":15,"strVal":"a\\b"}"#,
    ),
    (
        r#"{"ie":15,"strVal":"hello, world"}"#,
        r#"{"ie":15,"strVal":"😀"}"#,
    ),
    (
        r#"{"ie":15,"strVal":"hello, world"}"#,
        r#"{"ie":15,"strVal":"\ud83d"}"#,
    ),
    // Literals.
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":"00"}"#),
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":"01"}"#),
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":""}"#),
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":"1a"}"#),
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":-1}"#),
    (r#"{"ie":13,"natVal":"0"}"#, r#"{"ie":13,"natVal":0}"#),
    // Enums and booleans.
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"Default","body":2,"name":1,"type":0}}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"defaults","body":2,"name":1,"type":0}}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"","body":2,"name":1,"type":0}}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"strict","body":2,"name":1,"type":0}}"#,
    ),
    (
        r#"{"ie":10,"letE":{"body":2,"name":1,"nondep":false,"type":0,"value":3}}"#,
        r#"{"ie":10,"letE":{"body":2,"name":1,"nondep":"false","type":0,"value":3}}"#,
    ),
    (
        r#"{"ie":10,"letE":{"body":2,"name":1,"nondep":false,"type":0,"value":3}}"#,
        r#"{"ie":10,"letE":{"body":2,"name":1,"nondep":fals,"type":0,"value":3}}"#,
    ),
    // Keys.
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0,"x":1}}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lamb":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}"#,
    ),
    (
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}"#,
        r#"{"ie":6,"lam":{"binderInfo":"default","body":2,"name":1,"type":0}}}"#,
    ),
    (
        r#"{"ie":12,"proj":{"idx":0,"struct":5,"typeName":1}}"#,
        r#"{"ie":12,"mdata":{"data":{},"expr":5}}"#,
    ),
    (r#"{"ie":0,"sort":0}"#, r#"{"ie":0,"sort":0,"ie":0}"#),
    (r#"{"ie":0,"sort":0}"#, r#"{"ie":0}"#),
    (r#"{"ie":0,"sort":0}"#, r#"{"i"#),
    (r#"{"ie":0,"sort":0}"#, r#"{"#),
    (r#"{"ie":0,"sort":0}"#, ""),
];

#[test]
fn each_change_gives_the_same_result() {
    for (from, to) in CHANGES {
        let lines: Vec<&str> = BASE
            .iter()
            .map(|l| if l == from { *to } else { *l })
            .collect();
        assert!(lines.contains(to), "{from} is not in BASE");
        same(export(&lines).as_bytes());
    }
}

#[test]
fn a_record_on_line_one_is_not_a_meta_line() {
    let input = "{\"ie\":0,\"sort\":0}\n";
    assert_eq!(same(input.as_bytes()), 0);
}

/// Each byte of the base export, changed to a few other bytes. A small linear congruential generator picks the bytes, so the test is the same on each run.
#[test]
fn byte_changes_give_the_same_result() {
    let base = export(BASE).into_bytes();
    let picks = [b'0', b'9', b'"', b',', b'}', b']', b' ', b'\\', b'a', 0xff];
    let mut seed: u32 = 1;
    for i in META.len() + 1..base.len() {
        seed = seed.wrapping_mul(1_103_515_245).wrapping_add(12345);
        let c = picks[(seed >> 16) as usize % picks.len()];
        if base[i] != c {
            let mut v = base.clone();
            v[i] = c;
            same(&v);
        }
    }
}

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

/// The Arena tests up to 64 MiB. A larger test takes too long in a debug build.
#[test]
fn each_arena_test_gives_the_same_result() {
    let Some(dir) = arena_dir() else {
        eprintln!("note: no Arena directory, so the test does nothing");
        return;
    };
    let mut paths = Vec::new();
    files(&dir, &mut paths);
    let (mut n, mut lines) = (0, 0);
    for p in &paths {
        if std::fs::metadata(p).expect("stat").len() <= 64 << 20 {
            let input = std::fs::read(p).expect("read the test");
            lines += same(&input);
            n += 1;
        }
    }
    eprintln!("{n} files, {lines} lines on the fast path");
}
