//! The input rules of spec 07.1.2, one test for each rule.

use rulean_format::{Decl, ErrorKind, parse};
use rulean_store::{Expr, Literal, Store};

const META: &str = r#"{"meta":{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"","version":""}}}"#;

/// Joins the lines with a newline after each one, after the meta line.
fn doc(lines: &[&str]) -> Vec<u8> {
    let mut s = String::from(META);
    s.push('\n');
    for l in lines {
        s.push_str(l);
        s.push('\n');
    }
    s.into_bytes()
}

fn run(input: &[u8]) -> (Store, Result<Vec<Decl>, rulean_format::Error>) {
    let mut store = Store::new();
    let r = parse(&mut store, input);
    (store, r)
}

fn error_of(input: &[u8]) -> (u64, ErrorKind) {
    let (_, r) = run(input);
    let e = r.expect_err("the input must fail");
    (e.line, e.kind)
}

const AXIOM: &str = r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#;
const NAME: &str = r#"{"in":1,"str":{"pre":0,"str":"a"}}"#;
const SORT: &str = r#"{"ie":0,"sort":0}"#;

#[test]
fn a_small_export_parses() {
    let (store, r) = run(&doc(&[NAME, SORT, AXIOM]));
    let d = r.expect("valid");
    assert_eq!(d.len(), 1);
    assert_eq!(store.name_text(d[0].name()), b"a");
}

#[test]
fn line_rules() {
    assert_eq!(error_of(b""), (1, ErrorKind::NoMeta));
    assert_eq!(error_of(&doc(&[""])), (2, ErrorKind::EmptyLine));
    let mut t = doc(&[NAME]);
    t.extend_from_slice(SORT.as_bytes());
    assert_eq!(error_of(&t), (3, ErrorKind::TruncatedLine));
    assert_eq!(error_of(&doc(&[META])), (2, ErrorKind::LateMeta));
    assert_eq!(
        error_of(format!("{NAME}\n").as_bytes()),
        (1, ErrorKind::NoMeta)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"sort":0} x"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"foo":1}"#])),
        (2, ErrorKind::UnknownRecord)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"sort":0,"bvar":0}"#])),
        (2, ErrorKind::UnknownRecord)
    );
    assert_eq!(error_of(&doc(&["[1]"])), (2, ErrorKind::WrongType));
    // White space between the tokens is valid JSON.
    let (_, r) = run(&doc(&[" { \"ie\" : 0 , \"sort\" : 0 } \r"]));
    r.expect("white space");
}

#[test]
fn version_rules() {
    let v = |s: &str| format!("{{\"meta\":{{\"format\":{{\"version\":\"{s}\"}}}}}}\n").into_bytes();
    run(&v("3.0.0")).1.expect("3.0.0");
    run(&v("3.1.7")).1.expect("3.1.7");
    for bad in ["4.0.0", "2.1.0", "3.2.0", "3.1", "x", "3.1.0-rc"] {
        let (line, kind) = error_of(&v(bad));
        assert_eq!((line, kind), (1, ErrorKind::UnknownVersion), "{bad}");
        assert!(kind.is_decline());
    }
}

#[test]
fn index_rules() {
    // Gaps and any order are valid (Arena sparse-name-index and level-index-out-of-order).
    let (_, r) = run(&doc(&[
        r#"{"in":7,"str":{"pre":0,"str":"a"}}"#,
        r#"{"il":5,"succ":0}"#,
        r#"{"il":2,"succ":5}"#,
        r#"{"ie":9,"sort":2}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":7,"type":9}}"#,
    ]));
    r.expect("gaps");
    // A use before the definition.
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"sort":1}"#])),
        (2, ErrorKind::UndefinedIndex)
    );
    assert_eq!(
        error_of(&doc(&[SORT, r#"{"ie":1,"app":{"fn":0,"arg":2}}"#])),
        (3, ErrorKind::UndefinedIndex)
    );
    assert_eq!(
        error_of(&doc(&[SORT, AXIOM])),
        (3, ErrorKind::UndefinedIndex)
    );
    // Two definitions of one index. Index 0 of names and levels is implicit.
    assert_eq!(
        error_of(&doc(&[NAME, NAME])),
        (3, ErrorKind::DuplicateIndex)
    );
    assert_eq!(
        error_of(&doc(&[SORT, SORT])),
        (3, ErrorKind::DuplicateIndex)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"in":0,"str":{"pre":0,"str":"a"}}"#])),
        (2, ErrorKind::DuplicateIndex)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"il":0,"succ":0}"#])),
        (2, ErrorKind::DuplicateIndex)
    );
    // An index above the table limit is a decline.
    let (_, kind) = error_of(&doc(&[r#"{"ie":4294967296,"sort":0}"#]));
    assert_eq!(kind, ErrorKind::IndexLimit);
    assert!(kind.is_decline());
}

#[test]
fn json_rules() {
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"ie":1,"sort":0}"#])),
        (2, ErrorKind::DuplicateKey)
    );
    // An escaped key is the same key.
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"\u0069e":1,"sort":0}"#])),
        (2, ErrorKind::DuplicateKey)
    );
    run(&doc(&[r#"{"\u0069e":0,"s\u006frt":0}"#]))
        .1
        .expect("escaped key");
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0.0,"sort":0}"#])),
        (2, ErrorKind::BadInteger)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":1e2,"sort":0}"#])),
        (2, ErrorKind::BadInteger)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":-1,"sort":0}"#])),
        (2, ErrorKind::BadInteger)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":01,"sort":0}"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":"0","sort":0}"#])),
        (2, ErrorKind::WrongType)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":18446744073709551616,"sort":0}"#])),
        (2, ErrorKind::IntegerOverflow)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"bvar":4294967296}"#])),
        (2, ErrorKind::IntegerOverflow)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"sort":0"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"sort":0,}"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0 "sort":0}"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[SORT, r#"{"ie":1,"app":{"fn":0}}"#])),
        (3, ErrorKind::MissingKey)
    );
    assert_eq!(
        error_of(&doc(&["{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\tb\"}}"])),
        (2, ErrorKind::BadJson)
    );
    // The largest u64 is valid where a u64 is expected.
    run(&doc(&[
        r#"{"in":1,"num":{"pre":0,"i":18446744073709551615}}"#,
    ]))
    .1
    .expect("u64 max");
}

#[test]
fn string_rules() {
    let (store, r) = run(&doc(&[r#"{"ie":0,"strVal":"é😀\n\"\\\/"}"#]));
    r.expect("escapes");
    assert!(has_str(&store, "é😀\n\"\\/".as_bytes()));
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\ud83d"}"#])),
        (2, ErrorKind::LoneSurrogate)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\ud83dx"}"#])),
        (2, ErrorKind::LoneSurrogate)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\ude00"}"#])),
        (2, ErrorKind::LoneSurrogate)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\ud83dA"}"#])),
        (2, ErrorKind::LoneSurrogate)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\x"}"#])),
        (2, ErrorKind::BadJson)
    );
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"strVal":"\u12"}"#])),
        (2, ErrorKind::BadJson)
    );
    let mut bad = doc(&[]);
    bad.extend_from_slice(b"{\"ie\":0,\"strVal\":\"\xc3\x28\"}\n");
    assert_eq!(error_of(&bad), (2, ErrorKind::BadUtf8));
    let mut sur = doc(&[]);
    sur.extend_from_slice(b"{\"ie\":0,\"strVal\":\"\xed\xa0\x80\"}\n");
    assert_eq!(error_of(&sur), (2, ErrorKind::BadUtf8));
}

/// True if the store has the string `b`.
fn has_str(store: &Store, b: &[u8]) -> bool {
    (0..store.str_count()).any(|i| store.str_bytes(rulean_store::StrId(i as u32)) == b)
}

#[test]
fn nat_rules() {
    let big = "1".repeat(100);
    let line = format!(r#"{{"ie":0,"natVal":"{big}"}}"#);
    let (store, r) = run(&doc(&[r#"{"ie":1,"natVal":"0"}"#, &line]));
    r.expect("nat literals");
    let mut found = false;
    for i in 0..store.expr_count(rulean_store::Kind::Lit) {
        let e = rulean_store::ExprId::new(
            rulean_store::Tier::Frozen,
            rulean_store::Kind::Lit,
            i as u32,
        );
        if let Expr::Lit(Literal::Nat(n)) = store.node(e) {
            found |= store.nat(n).to_decimal() == big.as_bytes();
        }
    }
    assert!(found);
    for bad in ["", "01", "00", "1a", "-1", " 1"] {
        let line = format!(r#"{{"ie":0,"natVal":"{bad}"}}"#);
        assert_eq!(
            error_of(&doc(&[&line])),
            (2, ErrorKind::BadNatLiteral),
            "{bad:?}"
        );
    }
    assert_eq!(
        error_of(&doc(&[r#"{"ie":0,"natVal":5}"#])),
        (2, ErrorKind::WrongType)
    );
}

#[test]
fn mdata_is_stripped() {
    let (store, r) = run(&doc(&[
        NAME,
        SORT,
        r#"{"ie":1,"mdata":{"expr":0,"data":{"k":[1,{"x":null}],"b":true}}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":1}}"#,
    ]));
    let d = r.expect("mdata");
    let Decl::Axiom(a) = &d[0] else {
        panic!("an axiom")
    };
    assert_eq!(store.node(a.ty), Expr::Sort(store.level_zero()));
    // The data must be well-formed JSON.
    assert_eq!(
        error_of(&doc(&[
            SORT,
            r#"{"ie":1,"mdata":{"expr":0,"data":{"k":}}}"#
        ])),
        (3, ErrorKind::BadJson)
    );
    // A deep value uses no call stack.
    let deep = format!(
        r#"{{"ie":1,"mdata":{{"expr":0,"data":{}{}}}}}"#,
        "[".repeat(200_000),
        "]".repeat(200_000)
    );
    run(&doc(&[SORT, &deep])).1.expect("deep data");
}

#[test]
fn enum_values() {
    let lam = |bi: &str| {
        format!(r#"{{"ie":1,"lam":{{"binderInfo":"{bi}","body":0,"name":0,"type":0}}}}"#)
    };
    for bi in ["default", "implicit", "strictImplicit", "instImplicit"] {
        run(&doc(&[SORT, &lam(bi)])).1.expect(bi);
    }
    assert_eq!(
        error_of(&doc(&[SORT, &lam("auto")])),
        (3, ErrorKind::BadEnumValue)
    );
    let def = |safety: &str, hints: &str| {
        format!(
            r#"{{"def":{{"all":[1],"hints":{hints},"levelParams":[],"name":1,"safety":"{safety}","type":0,"value":0}}}}"#
        )
    };
    run(&doc(&[NAME, SORT, &def("partial", r#"{"regular":3}"#)]))
        .1
        .expect("regular");
    run(&doc(&[NAME, SORT, &def("unsafe", r#""abbrev""#)]))
        .1
        .expect("abbrev");
    assert_eq!(
        error_of(&doc(&[NAME, SORT, &def("total", r#""opaque""#)])),
        (4, ErrorKind::BadEnumValue)
    );
    assert_eq!(
        error_of(&doc(&[NAME, SORT, &def("safe", r#""never""#)])),
        (4, ErrorKind::BadEnumValue)
    );
    let quot =
        |k: &str| format!(r#"{{"quot":{{"kind":"{k}","levelParams":[],"name":1,"type":0}}}}"#);
    run(&doc(&[NAME, SORT, &quot("lift")])).1.expect("lift");
    assert_eq!(
        error_of(&doc(&[NAME, SORT, &quot("mk")])),
        (4, ErrorKind::BadEnumValue)
    );
}

#[test]
fn changed_bytes_never_panic() {
    let base = doc(&[
        NAME,
        r#"{"in":2,"num":{"pre":1,"i":3}}"#,
        r#"{"il":1,"param":1}"#,
        r#"{"il":2,"max":[0,1]}"#,
        r#"{"il":3,"imax":[1,2]}"#,
        SORT,
        r#"{"ie":1,"const":{"name":1,"us":[1,2]}}"#,
        r#"{"ie":2,"app":{"fn":1,"arg":0}}"#,
        r#"{"ie":3,"forallE":{"binderInfo":"default","body":0,"name":1,"type":0}}"#,
        r#"{"ie":4,"letE":{"body":0,"name":1,"nondep":false,"type":0,"value":0}}"#,
        r#"{"ie":5,"proj":{"idx":0,"struct":2,"typeName":1}}"#,
        r#"{"ie":6,"natVal":"123456789012345678901234567890"}"#,
        r#"{"ie":7,"strVal":"é😀"}"#,
        r#"{"ie":8,"bvar":0}"#,
        r#"{"thm":{"all":[1],"levelParams":[1],"name":2,"type":0,"value":8}}"#,
        r#"{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":0}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[],"name":1,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":0,"rules":[{"ctor":2,"nfields":0,"rhs":0}],"type":0}],"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}"#,
    ]);
    let (_, r) = run(&base);
    assert_eq!(r.expect("the base input is valid").len(), 2);
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let alphabet = b"{}[]\":,\\u0123456789abcdefe.-+ \nxtrn\xff\xc3\xed";
    for _ in 0..20_000 {
        let mut t = base.clone();
        let edits = 1 + next() % 3;
        for _ in 0..edits {
            let pos = (next() % t.len() as u64) as usize;
            match next() % 3 {
                0 => t[pos] = alphabet[(next() % alphabet.len() as u64) as usize],
                1 => {
                    t.remove(pos);
                }
                _ => t.insert(pos, alphabet[(next() % alphabet.len() as u64) as usize]),
            }
        }
        let _ = run(&t);
    }
}
