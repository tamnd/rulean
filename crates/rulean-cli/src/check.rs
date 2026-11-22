//! The `check` command (spec 09.2).
//!
//! The command reads an export, selects the semantics profile and checks each declaration with engine R. It stops at the first declaration that is not accepted. The exit code follows spec 09.3, and `--report` writes the JSON report of spec 09.4.

use std::collections::BTreeSet;
use std::io::{BufRead, BufReader};
use std::time::Instant;

use rulean_core::axioms::Axioms;
use rulean_core::conv::Engine;
use rulean_core::env::ConstKind;
use rulean_core::profile::{self, Profile};
use rulean_core::sha256::Hasher;
use rulean_core::tc::{Checker, ErrorKind as CheckError};
use rulean_format::{ErrorKind, Stream};
use rulean_store::Store;

use crate::exit::Code;
use crate::report::{self, Report};

/// The stack size of the checker thread. Engine R recurses on the depth of the terms, so the default stack of 2 MiB is too small for real exports.
pub(crate) const STACK_BYTES: usize = 1 << 30;

/// The options of `check`.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Options {
    pub input: Option<String>,
    pub parse_only: bool,
    pub profile: Option<String>,
    pub report: Option<String>,
    pub json: bool,
    pub trust_primitives: bool,
    /// `--engine R` gives true: engine R only. The default is engine R in this version (see `run`).
    pub engine_r: bool,
    /// `--engine` was given.
    pub engine_set: bool,
    /// `--confirm all`.
    pub confirm_all: bool,
    /// `--session off`: clear all caches at each declaration, as the official kernel does.
    pub no_session: bool,
    /// The axioms that a theorem can use, from `--axioms`. None is `any`: each axiom is allowed.
    pub axioms: Option<Vec<String>>,
}

/// The axioms of `--axioms std` (spec 09.2).
pub const STD_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// The list of `--axioms`: `any`, `none`, or names and `std` with a comma between them.
fn axiom_list(v: &str) -> Result<Option<Vec<String>>, String> {
    if v == "any" {
        return Ok(None);
    }
    let mut out = Vec::new();
    if v == "none" {
        return Ok(Some(out));
    }
    for part in v.split(',') {
        let part = part.trim();
        if part.is_empty() {
            return Err(format!("an empty name in `--axioms {v}`"));
        } else if part == "std" {
            out.extend(STD_AXIOMS.iter().map(|a| (*a).to_owned()));
        } else {
            out.push(part.to_owned());
        }
    }
    Ok(Some(out))
}

/// The value of an option that takes one, from `--name=value` or from the next argument.
fn value(name: &str, a: &str, rest: &mut std::slice::Iter<'_, String>) -> Result<String, String> {
    if let Some(v) = a.strip_prefix(name).and_then(|s| s.strip_prefix('=')) {
        return Ok(v.to_owned());
    }
    match rest.next() {
        Some(v) => Ok(v.clone()),
        None => Err(format!("`{name}` needs a value")),
    }
}

fn is_option(a: &str, name: &str) -> bool {
    a == name || a.starts_with(&format!("{name}="))
}

/// Reads the options. The result is an error text for a usage error.
pub fn options(args: &[String]) -> Result<Options, String> {
    let mut o = Options::default();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let a = a.as_str();
        if a == "--parse-only" {
            o.parse_only = true;
        } else if a == "--trust-primitives-by-name" {
            o.trust_primitives = true;
        } else if is_option(a, "--engine") {
            match value("--engine", a, &mut it)?.as_str() {
                "F" => o.engine_r = false,
                "R" => o.engine_r = true,
                v => return Err(format!("unknown engine `{v}`")),
            }
            o.engine_set = true;
        } else if is_option(a, "--confirm") {
            match value("--confirm", a, &mut it)?.as_str() {
                "default" => o.confirm_all = false,
                "all" => o.confirm_all = true,
                v => return Err(format!("unknown confirm set `{v}`")),
            }
        } else if is_option(a, "--session") {
            match value("--session", a, &mut it)?.as_str() {
                "on" => o.no_session = false,
                "off" => o.no_session = true,
                v => return Err(format!("unknown session mode `{v}`")),
            }
        } else if is_option(a, "--axioms") {
            o.axioms = axiom_list(&value("--axioms", a, &mut it)?)?;
        } else if is_option(a, "--profile") {
            o.profile = Some(value("--profile", a, &mut it)?);
        } else if is_option(a, "--report") {
            o.report = Some(value("--report", a, &mut it)?);
        } else if is_option(a, "--format") {
            match value("--format", a, &mut it)?.as_str() {
                "text" => o.json = false,
                "json" => o.json = true,
                v => return Err(format!("unknown format `{v}`")),
            }
        } else if a.starts_with("--") {
            return Err(format!("unknown option `{a}`"));
        } else if o.input.is_some() {
            return Err(format!("a second input `{a}`"));
        } else {
            o.input = Some(a.to_owned());
        }
    }
    if o.input.is_none() {
        return Err("no input".to_owned());
    }
    Ok(o)
}

/// Runs `check` with the arguments after the command name.
pub fn run(args: &[String]) -> Code {
    let o = match options(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("rulean check: {e}");
            return Code::Usage;
        }
    };
    if o.parse_only {
        let path = o.input.clone().unwrap_or_default();
        return match open_input(&path) {
            Ok(r) => parse_only(&path, r),
            Err(e) => {
                eprintln!("rulean: cannot read {path}: {e}");
                Code::Input
            }
        };
    }
    let r = match check_options(o) {
        Ok(r) => r,
        Err(code) => return code,
    };
    finish(&r)
}

/// Checks the input of the options on the checker thread. An error gives the exit code, after a message on standard error.
pub fn check_options(o: Options) -> Result<Run, Code> {
    let path = o.input.clone().unwrap_or_default();
    let reader = match open_input(&path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("rulean: cannot read {path}: {e}");
            return Err(Code::Input);
        }
    };
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || check_reader(&o, reader));
    match h {
        Ok(h) => match h.join() {
            Ok(Ok(r)) => Ok(r),
            Ok(Err(e)) => {
                eprintln!("rulean: cannot read {path}: {e}");
                Err(Code::Input)
            }
            Err(_) => {
                eprintln!("rulean: internal error: the checker thread stopped");
                Err(Code::Resource)
            }
        },
        Err(e) => {
            eprintln!("rulean: cannot start the checker thread: {e}");
            Err(Code::Resource)
        }
    }
}

/// Prints the result, writes the report and gives the exit code.
fn finish(r: &Run) -> Code {
    let rep = &r.report;
    if let Some(file) = &r.report_file
        && let Err(e) = std::fs::write(file, report::json(rep))
    {
        eprintln!("rulean: cannot write the report {file}: {e}");
        return Code::Usage;
    }
    if r.json {
        println!("{}", report::json(rep));
    } else {
        println!("{}", report::text(rep));
    }
    rep.code
}

/// The result of a check.
pub struct Run {
    pub report: Report,
    pub report_file: Option<String>,
    pub json: bool,
}

/// Checks an export that `input` gives. The parse reads one line at a time, so the input is not in memory as a whole. This runs on the checker thread.
pub fn check_reader<R: BufRead>(o: &Options, input: R) -> std::io::Result<Run> {
    let start = Instant::now();
    let mut store = Store::new();
    let (parsed, digest) = read_export(&mut store, input)?;
    let mut rep = Report {
        input_path: o.input.clone().unwrap_or_default(),
        sha256: hex(&digest),
        ..Report::default()
    };
    let export = match parsed {
        Ok(x) => x,
        Err(e) => {
            rep.code = code_of(e.kind);
            rep.error = Some(format!("line {}: {}", e.line, e.kind.text()));
            return Ok(done(o, rep, start));
        }
    };
    rep.lean_version = String::from_utf8_lossy(&export.lean_version).into_owned();
    rep.format_version = String::from_utf8_lossy(&export.format_version).into_owned();
    let prof = match select_profile(o, &export.lean_version) {
        Ok(p) => p,
        Err(e) => {
            rep.code = Code::Decline;
            rep.error = Some(e);
            return Ok(done(o, rep, start));
        }
    };
    rep.profile = Some(prof.id());
    rep.declarations = export.decls.len();
    let mut c = Checker::new(store);
    c.flags = prof.flags();
    c.trust_primitives = o.trust_primitives;
    c.engine = engine_of(o);
    c.confirm_all = o.confirm_all;
    c.sess.on = !o.no_session;
    rep.engine = c.engine;
    rep.confirm_all = o.confirm_all;
    let mut seen = 0;
    let mut ax = Axioms::new();
    let mut used: BTreeSet<String> = BTreeSet::new();
    let mut outside: Option<String> = None;
    for d in &export.decls {
        if let Some(f) = c.add_decl(d) {
            let n = name_text(&c, d.name());
            rep.code = code_of_check(f.kind);
            if rep.code == Code::Reject {
                rep.rejected = 1;
            }
            rep.error = Some(format!("{n}: {:?}", f.kind));
            rep.failed_decl = Some(n);
            break;
        }
        rep.accepted += 1;
        ax.update(&c.st, &c.env);
        while seen < c.env.len() {
            seen += 1;
            let ci = c.env.at(seen as u32);
            if ci.is_unsafe() || ci.is_partial_defn() {
                rep.quarantine.push(name_text(&c, ci.name));
            }
            if matches!(ci.kind, ConstKind::Thm { .. }) {
                for a in ax.of_slot(seen as u32) {
                    let t = name_text(&c, *a);
                    if outside.is_none()
                        && let Some(allowed) = &o.axioms
                        && !allowed.contains(&t)
                    {
                        outside = Some(format!(
                            "{}: the theorem uses the axiom {t}, which is not in --axioms",
                            name_text(&c, ci.name)
                        ));
                    }
                    used.insert(t);
                }
            }
        }
    }
    rep.axioms_used = used.into_iter().collect();
    if rep.code == Code::Accept
        && let Some(e) = outside
    {
        rep.code = Code::AxiomPolicy;
        rep.error = Some(e);
    }
    rep.f_stats = c.f_stats;
    rep.session = !o.no_session;
    rep.s_stats = c.sess.stats;
    rep.s_entries = c.sess.len();
    for n in &c.pin_mismatch {
        rep.pin_mismatch.push(name_text(&c, *n));
    }
    if !rep.pin_mismatch.is_empty() && !o.trust_primitives {
        rep.deviations.push("D1");
    }
    Ok(done(o, rep, start))
}

fn done(o: &Options, mut rep: Report, start: Instant) -> Run {
    rep.wall_ms = start.elapsed().as_millis();
    Run {
        report: rep,
        report_file: o.report.clone(),
        json: o.json,
    }
}

/// The engine of the run. Engine R is the default in this version, because engine F is new and the Arena runs with `--confirm all` must first show no difference (spec 05.1). Spec 09.2 makes engine F the default later.
pub(crate) fn engine_of(o: &Options) -> Engine {
    if o.engine_set && !o.engine_r {
        Engine::F
    } else {
        Engine::R
    }
}

/// The profile from `--profile`, or from the Lean version of the export (spec 05.2).
pub(crate) fn select_profile(o: &Options, lean_version: &[u8]) -> Result<Profile, String> {
    if let Some(id) = &o.profile {
        return profile::of_id(id.as_bytes()).ok_or_else(|| format!("unknown profile `{id}`"));
    }
    if lean_version.is_empty() {
        return Err(
            "unsupported-version: the export does not give the Lean version. Use --profile."
                .to_owned(),
        );
    }
    profile::of_lean_version(lean_version).ok_or_else(|| {
        format!(
            "unsupported-version: no profile for Lean {}. Use --profile.",
            String::from_utf8_lossy(lean_version)
        )
    })
}

pub(crate) fn name_text(c: &Checker, n: rulean_store::NameId) -> String {
    String::from_utf8_lossy(&c.st.name_text(n)).into_owned()
}

fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(2 * b.len());
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// `--parse-only`: parses the export and reports the counts.
fn parse_only<R: BufRead>(path: &str, input: R) -> Code {
    let start = Instant::now();
    let mut store = Store::new();
    let parsed = match read_export(&mut store, input) {
        Ok((p, _)) => p,
        Err(e) => {
            eprintln!("rulean: cannot read {path}: {e}");
            return Code::Input;
        }
    };
    match parsed {
        Ok(x) => {
            let ms = start.elapsed().as_millis();
            let mem = store.memory();
            println!(
                "parsed {path}: {} declarations, {} expression nodes, {} names, {} levels, {} bytes of store, {ms} ms",
                x.decls.len(),
                store.expr_total(),
                store.name_count(),
                store.level_count(),
                mem.total()
            );
            Code::Accept
        }
        Err(e) => {
            eprintln!("rulean: {path}: line {}: {}", e.line, e.kind.text());
            code_of(e.kind)
        }
    }
}

/// The exit code of a parse error (spec 09.3).
pub fn code_of(kind: ErrorKind) -> Code {
    match kind {
        ErrorKind::StoreFull => Code::Resource,
        k if k.is_decline() => Code::Decline,
        _ => Code::Input,
    }
}

/// The exit code of a checker error (spec 09.3). A depth bound and a full value arena are resource failures, and a declaration kind that rulean does not check is a decline. Every other error is a reject.
pub fn code_of_check(kind: CheckError) -> Code {
    match kind {
        CheckError::DeepRecursion => Code::Resource,
        CheckError::ArenaFull => Code::Resource,
        CheckError::Unsupported => Code::Decline,
        _ => Code::Reject,
    }
}

/// The size of the read buffer.
const READ_BYTES: usize = 1 << 20;

/// Opens the input file, or standard input for `-`.
pub(crate) fn open_input(path: &str) -> std::io::Result<Box<dyn BufRead + Send>> {
    if path == "-" {
        Ok(Box::new(BufReader::with_capacity(
            READ_BYTES,
            std::io::stdin(),
        )))
    } else {
        let f = std::fs::File::open(path)?;
        Ok(Box::new(BufReader::with_capacity(READ_BYTES, f)))
    }
}

/// Parses the export that `input` gives, one line at a time, and computes the SHA-256 digest of all of the input. After a parse error, the function reads the rest of the input for the digest only.
pub(crate) fn read_export<R: BufRead>(
    store: &mut Store,
    mut input: R,
) -> std::io::Result<(
    Result<rulean_format::Export, rulean_format::Error>,
    [u8; 32],
)> {
    let mut s = Stream::new();
    let mut hasher = Hasher::new();
    let mut tail = false;
    let mut line = Vec::new();
    loop {
        line.clear();
        let n = input.read_until(b'\n', &mut line)?;
        if n == 0 {
            break;
        }
        hasher.update(&line);
        if line.last() == Some(&b'\n') {
            s.line(store, &line[..line.len() - 1]);
        } else {
            tail = true;
        }
    }
    Ok((s.end(tail), hasher.finish()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn option_rules() {
        let o = options(&strs(&["x.ndjson", "--parse-only"])).expect("valid");
        assert_eq!(o.input.as_deref(), Some("x.ndjson"));
        assert!(o.parse_only);
        assert!(options(&strs(&[])).is_err());
        assert!(options(&strs(&["a", "b"])).is_err());
        assert!(options(&strs(&["a", "--fast"])).is_err());
    }

    #[test]
    fn options_with_values() {
        let o = options(&strs(&[
            "--profile",
            "v4.35",
            "--report=r.json",
            "--format",
            "json",
            "x",
        ]))
        .expect("valid");
        assert_eq!(o.profile.as_deref(), Some("v4.35"));
        assert_eq!(o.report.as_deref(), Some("r.json"));
        assert!(o.json);
        assert!(options(&strs(&["x", "--profile"])).is_err());
        assert!(options(&strs(&["x", "--format=xml"])).is_err());
        let o = options(&strs(&["x", "--trust-primitives-by-name"])).expect("valid");
        assert!(o.trust_primitives);
        let o = options(&strs(&["x", "--engine", "F", "--confirm=all"])).expect("valid");
        assert_eq!(engine_of(&o), Engine::F);
        assert!(o.confirm_all);
        let o = options(&strs(&["x", "--engine=R"])).expect("valid");
        assert_eq!(engine_of(&o), Engine::R);
        let o = options(&strs(&["x"])).expect("valid");
        assert_eq!(engine_of(&o), Engine::R);
        assert!(options(&strs(&["x", "--engine", "G"])).is_err());
        assert!(options(&strs(&["x", "--confirm", "some"])).is_err());
        assert!(
            options(&strs(&["x", "--session=off"]))
                .expect("valid")
                .no_session
        );
        assert!(
            !options(&strs(&["x", "--session", "on"]))
                .expect("valid")
                .no_session
        );
        assert!(options(&strs(&["x", "--session", "maybe"])).is_err());
        assert_eq!(options(&strs(&["x"])).expect("valid").axioms, None);
        let o = options(&strs(&["x", "--axioms", "any"])).expect("valid");
        assert_eq!(o.axioms, None);
        let o = options(&strs(&["x", "--axioms=none"])).expect("valid");
        assert_eq!(o.axioms, Some(Vec::new()));
        let o = options(&strs(&["-", "--axioms", "std,A.b"])).expect("valid");
        let want = ["propext", "Quot.sound", "Classical.choice", "A.b"];
        assert_eq!(
            o.axioms,
            Some(want.iter().map(|a| (*a).to_owned()).collect())
        );
        assert!(options(&strs(&["x", "--axioms", "std,"])).is_err());
    }

    #[test]
    fn error_codes() {
        assert_eq!(code_of(ErrorKind::BadJson), Code::Input);
        assert_eq!(code_of(ErrorKind::UndefinedIndex), Code::Input);
        assert_eq!(code_of(ErrorKind::UnknownVersion), Code::Decline);
        assert_eq!(code_of(ErrorKind::IndexLimit), Code::Decline);
        assert_eq!(code_of(ErrorKind::StoreFull), Code::Resource);
        assert_eq!(code_of_check(CheckError::AppTypeMismatch), Code::Reject);
        assert_eq!(code_of_check(CheckError::DeepRecursion), Code::Resource);
        assert_eq!(code_of_check(CheckError::ArenaFull), Code::Resource);
        assert_eq!(code_of_check(CheckError::Unsupported), Code::Decline);
    }

    const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.36.0"}}}"#;

    fn run_on(text: &str, o: &Options) -> Report {
        check_reader(o, text.as_bytes())
            .expect("no read error")
            .report
    }

    #[test]
    fn empty_export_is_accepted() {
        let r = run_on(&format!("{META}\n"), &Options::default());
        assert_eq!(r.code, Code::Accept);
        assert_eq!(r.profile, Some("v4.35"));
        assert_eq!(r.lean_version, "4.36.0");
    }

    #[test]
    fn unknown_lean_version_declines() {
        let text = format!("{}\n", META.replace("4.36.0", "4.20.0"));
        let r = run_on(&text, &Options::default());
        assert_eq!(r.code, Code::Decline);
        let o = Options {
            profile: Some("v4.35".to_owned()),
            ..Options::default()
        };
        assert_eq!(run_on(&text, &o).code, Code::Accept);
        let o = Options {
            profile: Some("v9".to_owned()),
            ..Options::default()
        };
        assert_eq!(run_on(&text, &o).code, Code::Decline);
    }

    #[test]
    fn axiom_is_accepted_and_bad_axiom_is_rejected() {
        // `axiom A : Prop`, and then the axiom `B` with a loose bound variable as its type.
        let good = format!(
            "{META}\n{}\n{}\n{}\n",
            r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#
        );
        let r = run_on(&good, &Options::default());
        assert_eq!(r.code, Code::Accept, "{:?}", r.error);
        assert_eq!(r.accepted, 1);
        let bad = format!(
            "{good}{}\n{}\n{}\n",
            r#"{"in":2,"str":{"pre":0,"str":"B"}}"#,
            r#"{"bvar":0,"ie":1}"#,
            r#"{"axiom":{"name":2,"levelParams":[],"type":1,"isUnsafe":false}}"#
        );
        let r = run_on(&bad, &Options::default());
        assert_eq!(r.code, Code::Reject);
        assert_eq!(r.failed_decl.as_deref(), Some("B"));
    }

    #[test]
    fn unsafe_axiom_is_in_quarantine() {
        let text = format!(
            "{META}\n{}\n{}\n{}\n",
            r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":true}}"#
        );
        let r = run_on(&text, &Options::default());
        assert_eq!(r.code, Code::Accept, "{:?}", r.error);
        assert_eq!(r.quarantine, vec!["A".to_owned()]);
    }

    /// `axiom A : Prop`, `axiom h : A` and `theorem t : A := h`.
    fn theorem_with_axiom() -> String {
        format!(
            "{META}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
            r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
            r#"{"in":2,"str":{"pre":0,"str":"h"}}"#,
            r#"{"in":3,"str":{"pre":0,"str":"t"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
            r#"{"ie":2,"const":{"name":2,"us":[]}}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{"axiom":{"name":2,"levelParams":[],"type":1,"isUnsafe":false}}"#,
            r#"{"thm":{"all":[3],"levelParams":[],"name":3,"type":1,"value":2}}"#
        )
    }

    #[test]
    fn axiom_policy() {
        let text = theorem_with_axiom();
        let r = run_on(&text, &Options::default());
        assert_eq!(r.code, Code::Accept, "{:?}", r.error);
        assert_eq!(r.axioms_used, vec!["A".to_owned(), "h".to_owned()]);
        let o = Options {
            axioms: Some(vec!["A".to_owned(), "h".to_owned()]),
            ..Options::default()
        };
        assert_eq!(run_on(&text, &o).code, Code::Accept);
        let o = Options {
            axioms: Some(vec!["A".to_owned()]),
            ..Options::default()
        };
        let r = run_on(&text, &o);
        assert_eq!(r.code, Code::AxiomPolicy);
        assert_eq!(r.accepted, 3);
        assert!(
            r.error.as_deref().is_some_and(|e| e.starts_with("t: ")),
            "{:?}",
            r.error
        );
        assert!(report::json(&r).contains(r#""axioms_used": ["A", "h"]"#));
    }

    #[test]
    fn malformed_export_is_an_input_error() {
        let r = run_on(&format!("{META}\n{{\n"), &Options::default());
        assert_eq!(r.code, Code::Input);
    }
}
