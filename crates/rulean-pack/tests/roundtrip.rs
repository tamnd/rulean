//! Tests of the binary format: an encode, a decode and a second encode give the same bytes, and the decoder rejects a damaged file.
//!
//! The round trip runs on the Arena tests in `RULEAN_ARENA`, or in `_tmp/arena/tests` in the repository. If neither exists, that test prints a note and passes. The other tests use small exports in this file.

use std::path::{Path, PathBuf};

use rulean_format::ErrorKind;
use rulean_format::crc::crc32c;
use rulean_format::rlb::{self, DIR_BYTES, HEADER_BYTES};
use rulean_pack::{Source, encode};
use rulean_store::Store;

/// An export with a definition, a theorem, an inductive type, literals, a projection and a `let`.
const EXPORT: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.36.0"}}}
{"in":1,"str":{"pre":0,"str":"T"}}
{"in":2,"str":{"pre":1,"str":"mk"}}
{"in":3,"str":{"pre":1,"str":"rec"}}
{"in":4,"num":{"pre":1,"i":7}}
{"in":5,"str":{"pre":0,"str":"u"}}
{"in":6,"str":{"pre":0,"str":"x"}}
{"in":7,"str":{"pre":0,"str":"motive"}}
{"in":8,"str":{"pre":0,"str":"d"}}
{"il":1,"succ":0}
{"il":2,"param":5}
{"il":3,"max":[1,2]}
{"il":4,"imax":[2,1]}
{"ie":0,"sort":1}
{"ie":1,"const":{"name":1,"us":[]}}
{"ie":2,"const":{"name":2,"us":[]}}
{"ie":3,"sort":2}
{"ie":4,"bvar":0}
{"ie":5,"app":{"fn":4,"arg":2}}
{"ie":6,"forallE":{"name":7,"type":1,"body":3,"binderInfo":"implicit"}}
{"ie":7,"forallE":{"name":6,"type":1,"body":5,"binderInfo":"default"}}
{"ie":8,"forallE":{"name":7,"type":6,"body":3,"binderInfo":"instImplicit"}}
{"ie":9,"natVal":"340282366920938463463374607431768211457"}
{"ie":10,"strVal":"héllo"}
{"ie":11,"lam":{"name":6,"type":1,"body":4,"binderInfo":"strictImplicit"}}
{"ie":12,"letE":{"name":6,"type":1,"value":2,"body":4,"nondep":false}}
{"ie":13,"proj":{"typeName":1,"idx":0,"struct":2}}
{"ie":14,"mdata":{"expr":11,"data":{}}}
{"ie":15,"forallE":{"name":6,"type":1,"body":1,"binderInfo":"default"}}
{"ie":16,"const":{"name":5,"us":[3,4]}}
{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[2],"numNested":0,"isRec":false,"isReflexive":false,"isUnsafe":false}],"ctors":[{"name":2,"levelParams":[],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false}],"recs":[{"name":3,"levelParams":[5],"type":7,"all":[1],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":1,"k":true,"rules":[{"ctor":2,"nfields":0,"rhs":11}],"isUnsafe":false}]}}
{"def":{"name":4,"levelParams":[5],"type":15,"value":14,"hints":{"regular":3},"safety":"partial","all":[4]}}
{"thm":{"name":8,"levelParams":[],"type":1,"value":12,"all":[8]}}
{"opaque":{"name":6,"levelParams":[],"type":1,"value":13,"isUnsafe":true,"all":[6]}}
{"axiom":{"name":7,"levelParams":[],"type":0,"isUnsafe":false}}
"#;

fn source(lean: &[u8]) -> Source {
    Source {
        lean_version: lean.to_vec(),
        githash: b"0".to_vec(),
        sha256: [7; 32],
    }
}

/// Parses an NDJSON export and encodes it.
fn pack(input: &[u8]) -> Vec<u8> {
    let mut st = Store::new();
    let x = rulean_format::parse_export(&mut st, input).expect("a valid export");
    encode(&st, &x.decls, &source(&x.lean_version))
        .expect("the encoder takes the export")
        .0
}

/// Decodes `b` into a new store and encodes the result again.
fn repack(b: &[u8]) -> Vec<u8> {
    let mut st = Store::new();
    let x = rlb::decode(&mut st, b).expect("the decoder takes the file");
    let src = Source {
        lean_version: x.header.lean_version.clone(),
        githash: x.header.githash.clone(),
        sha256: x.header.source_sha256,
    };
    encode(&st, &x.decls, &src)
        .expect("the encoder takes the decode")
        .0
}

fn decode_err(b: &[u8]) -> ErrorKind {
    let mut st = Store::new();
    match rlb::decode(&mut st, b) {
        Ok(_) => panic!("the decoder takes a damaged file"),
        Err(e) => e.kind,
    }
}

/// The directory entry `i`: offset, length and the position of its checksum.
fn entry(b: &[u8], i: usize) -> (usize, usize, usize) {
    let p = HEADER_BYTES + i * DIR_BYTES;
    let off = u64::from_le_bytes(b[p + 4..p + 12].try_into().expect("4 or 8 bytes")) as usize;
    let len = u64::from_le_bytes(b[p + 12..p + 20].try_into().expect("4 or 8 bytes")) as usize;
    (off, len, p + 28)
}

/// Writes the checksums again after a change, so that the test reaches the check after the checksum.
fn fix_sums(b: &mut [u8]) {
    let n = u32::from_le_bytes(b[92..96].try_into().expect("4 or 8 bytes")) as usize;
    for i in 0..n {
        let (off, len, at) = entry(b, i);
        let c = crc32c(b, off, off + len);
        b[at..at + 4].copy_from_slice(&c.to_le_bytes());
    }
}

#[test]
fn round_trip_keeps_every_field() {
    let a = pack(EXPORT.as_bytes());
    assert_eq!(a.len() % 8, 0);
    assert_eq!(repack(&a), a);
    let mut st = Store::new();
    let x = rlb::decode(&mut st, &a).expect("decode");
    let mut st2 = Store::new();
    let y = rulean_format::parse_export(&mut st2, EXPORT.as_bytes()).expect("parse");
    assert_eq!(x.decls.len(), y.decls.len());
    assert_eq!(x.header.lean_version, b"4.36.0");
    assert_eq!(x.header.githash, b"0");
    assert_eq!(x.header.source_sha256, [7; 32]);
    // Names, levels and strings go in store order, so their handles are the same.
    for (d, e) in x.decls.iter().zip(&y.decls) {
        assert_eq!(st.name_text(d.name()), st2.name_text(e.name()));
    }
    assert_eq!(st.name_count(), st2.name_count());
    assert_eq!(st.level_count(), st2.level_count());
    assert_eq!(st.str_count(), st2.str_count());
    assert_eq!(st.nat_count(), st2.nat_count());
}

#[test]
fn damage_is_found() {
    let a = pack(EXPORT.as_bytes());
    // A changed byte in a section.
    let (off, _, _) = entry(&a, 4);
    let mut b = a.clone();
    b[off + 5] ^= 1;
    assert_eq!(decode_err(&b), ErrorKind::BadChecksum);
    // A cut file.
    assert_eq!(decode_err(&a[..a.len() - 8]), ErrorKind::BadBinary);
    assert_eq!(decode_err(&a[..100]), ErrorKind::BadBinary);
    // A wrong magic.
    let mut b = a.clone();
    b[0] = b'X';
    assert_eq!(decode_err(&b), ErrorKind::BadBinary);
    // Another version, a flag or a profile id is a decline.
    for at in [8, 12, 88] {
        let mut b = a.clone();
        b[at] = 9;
        assert_eq!(decode_err(&b), ErrorKind::UnknownVersion, "byte {at}");
    }
    // A missing section.
    let mut b = a.clone();
    b[HEADER_BYTES] = 7;
    assert_eq!(decode_err(&b), ErrorKind::BadBinary);
    // A section that starts out of the 8-byte grid.
    let mut b = a.clone();
    b[HEADER_BYTES + 4] += 1;
    assert_eq!(decode_err(&b), ErrorKind::BadBinary);
}

#[test]
fn a_forward_reference_is_an_undefined_index() {
    // The first app node of EXPRS refers to itself. Its operands are the second and third words of the record.
    let a = pack(EXPORT.as_bytes());
    let (off, len, _) = entry(&a, 4);
    let mut b = a.clone();
    let mut p = off;
    let mut found = false;
    let mut index = 0u32;
    while p < off + len {
        let tag = u32::from_le_bytes(b[p..p + 4].try_into().expect("4 or 8 bytes"));
        let words = match tag & 0xff {
            rlb::E_CONST => {
                3 + u32::from_le_bytes(b[p + 8..p + 12].try_into().expect("4 or 8 bytes")) as usize
            }
            rlb::E_APP => 3,
            rlb::E_LAM | rlb::E_PI => 4,
            rlb::E_LET => 5,
            rlb::E_PROJ => 4,
            _ => 2,
        };
        if tag == rlb::E_APP {
            b[p + 4..p + 8].copy_from_slice(&index.to_le_bytes());
            found = true;
            break;
        }
        p += 4 * words;
        index += 1;
    }
    assert!(found);
    fix_sums(&mut b);
    assert_eq!(decode_err(&b), ErrorKind::UndefinedIndex);
}

#[test]
fn a_bad_tag_or_a_nonzero_pad_is_found() {
    let a = pack(EXPORT.as_bytes());
    // NAMES: a tag of 3.
    let (off, _, _) = entry(&a, 1);
    let mut b = a.clone();
    b[off] = 3;
    fix_sums(&mut b);
    assert_eq!(decode_err(&b), ErrorKind::BadEnumValue);
    // NAMES: a byte of the pad.
    let mut b = a.clone();
    b[off + 1] = 1;
    fix_sums(&mut b);
    assert_eq!(decode_err(&b), ErrorKind::BadBinary);
    // STRINGS: a byte that is not UTF-8.
    let (off, _, _) = entry(&a, 0);
    let n = u32::from_le_bytes(
        a[HEADER_BYTES + 20..HEADER_BYTES + 24]
            .try_into()
            .expect("4 or 8 bytes"),
    ) as usize;
    let mut b = a.clone();
    b[off + 4 * n] = 0xff;
    fix_sums(&mut b);
    assert_eq!(decode_err(&b), ErrorKind::BadUtf8);
}

#[test]
fn a_large_count_does_not_allocate() {
    let a = pack(EXPORT.as_bytes());
    let mut b = a.clone();
    let p = HEADER_BYTES + 4 * DIR_BYTES + 20;
    b[p..p + 8].copy_from_slice(&(1u64 << 27).to_le_bytes());
    assert_eq!(decode_err(&b), ErrorKind::BadBinary);
    b[p..p + 8].copy_from_slice(&(1u64 << 40).to_le_bytes());
    assert_eq!(decode_err(&b), ErrorKind::IndexLimit);
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

#[test]
fn every_arena_test_round_trips() {
    let Some(dir) = arena_dir() else {
        eprintln!("note: no Arena directory, so the test does nothing");
        return;
    };
    let mut paths = Vec::new();
    files(&dir, &mut paths);
    assert!(!paths.is_empty(), "no .ndjson files in {}", dir.display());
    let mut ndjson = 0;
    let mut binary = 0;
    for p in &paths {
        let input = std::fs::read(p).expect("read the test");
        let a = pack(&input);
        assert_eq!(repack(&a), a, "{}", p.display());
        ndjson += input.len();
        binary += a.len();
    }
    eprintln!(
        "{} files, {ndjson} bytes of NDJSON, {binary} bytes of binary",
        paths.len()
    );
}
