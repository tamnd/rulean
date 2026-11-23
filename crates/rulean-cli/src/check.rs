//! The `check` command (spec 09.2).
//!
//! The command reads an export, selects the semantics profile and checks each declaration with engine R. It stops at the first declaration that is not accepted. The exit code follows spec 09.3, and `--report` writes the JSON report of spec 09.4.

use std::collections::BTreeSet;
use std::io::BufRead;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use rulean_core::axioms::Axioms;
use rulean_core::conv::Engine;
use rulean_core::env::ConstKind;
use rulean_core::profile::{self, Profile};
use rulean_core::sched;
use rulean_core::tc::{Checker, ErrorKind as CheckError};
use rulean_format::{Decl, ErrorKind, Stream, rlb};
use rulean_io::sha::Sha256;
use rulean_store::Store;

use crate::exit::Code;
use crate::limits::{self, Limited};
use crate::report::{self, Report, SLOWEST};

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
    /// `--threads N`: the number of workers of the check stage (spec 08.3). 0 and 1 give the sequential check.
    pub threads: usize,
    /// `rulean olean`: the directories of `--path`, in order.
    pub paths: Vec<String>,
    /// `rulean olean`: the modules to check.
    pub modules: Vec<String>,
    /// `--max-memory`: the memory budget in bytes. None is the default of spec 05.11, and `limits::NO_LIMIT` is no budget.
    pub max_memory: Option<usize>,
    /// `--timeout`: the limit of the wall time. None is no limit.
    pub timeout: Option<Duration>,
}

impl Options {
    /// The memory budget of the run in bytes: the value of `--max-memory`, or else 0.8 times the physical memory.
    pub fn memory_budget(&self) -> usize {
        self.max_memory.unwrap_or_else(limits::default_max_memory)
    }
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

/// Reads the options of `check`. The result is an error text for a usage error.
pub fn options(args: &[String]) -> Result<Options, String> {
    parse(args, false)
}

/// Reads the options of `check`, or of `olean` if `olean` is true. The `olean` command also takes `--path DIR`, and each argument that is not an option is a module.
pub fn parse(args: &[String], olean: bool) -> Result<Options, String> {
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
        } else if is_option(a, "--threads") {
            let v = value("--threads", a, &mut it)?;
            o.threads = match v.parse::<usize>() {
                Ok(n) if (1..=1024).contains(&n) => n,
                _ => {
                    return Err(format!(
                        "`--threads` needs a number from 1 to 1024, not `{v}`"
                    ));
                }
            };
        } else if is_option(a, "--max-memory") {
            o.max_memory = Some(limits::parse_size(&value("--max-memory", a, &mut it)?)?);
        } else if is_option(a, "--timeout") {
            o.timeout = Some(limits::parse_duration(&value("--timeout", a, &mut it)?)?);
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
        } else if olean && is_option(a, "--path") {
            o.paths.push(value("--path", a, &mut it)?);
        } else if a.starts_with("--") {
            return Err(format!("unknown option `{a}`"));
        } else if olean {
            o.modules.push(a.to_owned());
        } else if o.input.is_some() {
            return Err(format!("a second input `{a}`"));
        } else {
            o.input = Some(a.to_owned());
        }
    }
    if olean && o.modules.is_empty() {
        return Err("no module".to_owned());
    }
    if !olean && o.input.is_none() {
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
            Ok(i) => parse_only(&path, i.reader),
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
    let input = match open_input(&path) {
        Ok(i) => i,
        Err(e) => {
            eprintln!("rulean: cannot read {path}: {e}");
            return Err(Code::Input);
        }
    };
    let source = input.source;
    let reader = input.reader;
    let timeout = o.timeout;
    let report_file = o.report.clone();
    let json = o.json;
    let start = Instant::now();
    match limits::run_limited(timeout, move || check_reader(&o, reader)) {
        Limited::Done(Ok(mut r)) => {
            confirm_input(&source, &mut r.report);
            Ok(r)
        }
        Limited::Done(Err(e)) => {
            eprintln!("rulean: cannot read {path}: {e}");
            Err(Code::Input)
        }
        Limited::Timeout => {
            let t = timeout.unwrap_or_default();
            eprintln!("rulean: {}", limits::timeout_text(t));
            // The report needs the SHA-256 of the input. Only a file can be read again for it, so a run on standard input gives no report.
            let digest = match &source {
                rulean_io::Source::File(f) => {
                    std::fs::File::open(f).and_then(rulean_io::digest).ok()
                }
                _ => None,
            };
            match digest {
                Some(d) => Ok(timeout_run(path, hex(&d), t, start, report_file, json)),
                None => Err(Code::Resource),
            }
        }
        Limited::Stopped => {
            eprintln!("rulean: internal error: the checker thread stopped");
            Err(Code::Resource)
        }
        Limited::NoThread(e) => {
            eprintln!("rulean: cannot start the checker thread: {e}");
            Err(Code::Resource)
        }
    }
}

/// The result of a run that `--timeout` stopped: no verdict, with the resource code.
pub(crate) fn timeout_run(
    path: String,
    sha256: String,
    t: Duration,
    start: Instant,
    report_file: Option<String>,
    json: bool,
) -> Run {
    let report = Report {
        input_path: path,
        sha256,
        code: Code::Resource,
        error: Some(limits::timeout_text(t)),
        wall_ms: start.elapsed().as_millis(),
        ..Report::default()
    };
    Run {
        report,
        report_file,
        json,
    }
}

/// Prints the result, writes the report and gives the exit code.
pub(crate) fn finish(r: &Run) -> Code {
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
    store.set_max_bytes(o.memory_budget());
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
            rep.error = Some(error_text(&e));
            if e.kind == ErrorKind::StoreFull && store.max_bytes() != limits::NO_LIMIT {
                rep.error = Some(memory_text(store.max_bytes()));
            }
            return Ok(done(o, rep, start));
        }
    };
    Ok(check_export(o, store, export, rep, start))
}

/// Checks the declarations of a decoded export. `rep` has the input path and the digest. This runs on the checker thread.
pub(crate) fn check_export(
    o: &Options,
    store: Store,
    export: rulean_format::Export,
    mut rep: Report,
    start: Instant,
) -> Run {
    rep.lean_version = String::from_utf8_lossy(&export.lean_version).into_owned();
    rep.format_version = String::from_utf8_lossy(&export.format_version).into_owned();
    let prof = match select_profile(o, &export.lean_version) {
        Ok(p) => p,
        Err(e) => {
            rep.code = Code::Decline;
            rep.error = Some(e);
            return done(o, rep, start);
        }
    };
    rep.profile = Some(prof.id());
    rep.declarations = export.decls.len();
    let mut c = Checker::new(store);
    c.set_max_memory(o.memory_budget());
    // The declarations of the export stay in memory during the check, so they count in the budget (spec 05.11.1).
    c.mem_others = export.decls.capacity() * core::mem::size_of::<Decl>();
    c.flags = prof.flags();
    c.trust_primitives = o.trust_primitives;
    c.engine = engine_of(o);
    c.confirm_all = o.confirm_all;
    c.sess.on = !o.no_session;
    rep.engine = c.engine;
    rep.confirm_all = o.confirm_all;
    if o.threads > 1 {
        check_parallel(o, &mut c, &export.decls, &mut rep);
    } else {
        check_sequential(o, &mut c, &export.decls, &mut rep);
    }
    rep.session = !o.no_session;
    for n in &c.pin_mismatch {
        rep.pin_mismatch.push(name_text(&c, *n));
    }
    if !rep.pin_mismatch.is_empty() && !o.trust_primitives {
        rep.deviations.push("D1");
    }
    done(o, rep, start)
}

/// Checks the declarations one after the other, and stops at the first declaration that is not accepted.
fn check_sequential(o: &Options, c: &mut Checker, ds: &[Decl], rep: &mut Report) {
    let mut t = Tally::new();
    let mut times: Vec<(u64, usize)> = Vec::new();
    for (i, d) in ds.iter().enumerate() {
        // The memory check between declarations. Inside a declaration, the checker makes the same check at intervals.
        if c.over_memory() {
            rep.code = Code::Resource;
            rep.error = Some(memory_text(c.max_memory()));
            break;
        }
        let t0 = Instant::now();
        let fault = c.add_decl(d);
        keep_slowest(&mut times, (micros(t0), i));
        if let Some(f) = fault {
            let n = name_text(c, d.name());
            rep.code = code_of_check(f.kind);
            if rep.code == Code::Reject {
                rep.rejected = 1;
            }
            rep.error = Some(format!("{n}: {:?}", f.kind));
            rep.failed_decl = Some(n);
            break;
        }
        rep.accepted += 1;
        t.step(o, c, rep);
    }
    t.finish(rep);
    for (us, i) in times {
        rep.slowest.push((name_text(c, ds[i].name()), us));
    }
    rep.f_stats = c.f_stats;
    rep.steps = c.steps;
    rep.interns = c.st.interns();
    rep.s_stats = c.sess.stats;
    rep.s_entries = c.sess.len();
    if c.st.is_full() {
        store_full(c, rep);
    }
}

/// The time since `t0` in microseconds.
fn micros(t0: Instant) -> u64 {
    u64::try_from(t0.elapsed().as_micros()).unwrap_or(u64::MAX)
}

/// Puts `x` into `times`, which holds the `SLOWEST` largest times, the largest first.
fn keep_slowest(times: &mut Vec<(u64, usize)>, x: (u64, usize)) {
    if times.len() == SLOWEST && times.last().is_some_and(|l| l.0 >= x.0) {
        return;
    }
    let at = times.partition_point(|y| y.0 >= x.0);
    times.insert(at, x);
    times.truncate(SLOWEST);
}

/// The quarantine and the axioms of the accepted declarations. `step` reads the constants that the last accepted declaration added.
struct Tally {
    seen: usize,
    ax: Axioms,
    used: BTreeSet<String>,
    outside: Option<String>,
}

impl Tally {
    fn new() -> Tally {
        Tally {
            seen: 0,
            ax: Axioms::new(),
            used: BTreeSet::new(),
            outside: None,
        }
    }

    /// Reads the constants after the last call, up to the length of the environment.
    fn step(&mut self, o: &Options, c: &Checker, rep: &mut Report) {
        self.ax.update(&c.st, &c.env);
        while self.seen < c.env.len() {
            self.seen += 1;
            let ci = c.env.at(self.seen as u32);
            if ci.is_unsafe() || ci.is_partial_defn() {
                rep.quarantine.push(name_text(c, ci.name));
            }
            if matches!(ci.kind, ConstKind::Thm { .. }) {
                for a in self.ax.of_slot(self.seen as u32) {
                    let t = name_text(c, *a);
                    if self.outside.is_none()
                        && let Some(allowed) = &o.axioms
                        && !allowed.contains(&t)
                    {
                        self.outside = Some(format!(
                            "{}: the theorem uses the axiom {t}, which is not in --axioms",
                            name_text(c, ci.name)
                        ));
                    }
                    self.used.insert(t);
                }
            }
        }
    }

    /// Puts the axioms into the report. If all declarations are accepted and a theorem uses an axiom outside `--axioms`, the verdict is `axiom-policy`.
    fn finish(self, rep: &mut Report) {
        rep.axioms_used = self.used.into_iter().collect();
        if rep.code == Code::Accept
            && let Some(e) = self.outside
        {
            rep.code = Code::AxiomPolicy;
            rep.error = Some(e);
        }
    }
}

/// Checks the declarations with the two-stage scheduler of spec 08.3 on `o.threads` workers. The result is the same as the result of `check_sequential`, except for the counts of the caches.
fn check_parallel(o: &Options, c: &mut Checker, ds: &[Decl], rep: &mut Report) {
    let plan = c.plan(ds);
    let order = rulean_pool::largest_first(&plan.costs);
    let main: &Checker = c;
    // The main checker and the workers share one budget. Each worker has a copy of the store, so the copies count too. The core has no shared state, so the total is here: before and after each job, a worker adds the change of its memory to the total and reads the memory of the others.
    let total = AtomicUsize::new(main.memory() + main.mem_others);
    let publish = |w: &mut Checker| {
        let m = w.memory();
        total.fetch_add(m, Ordering::Relaxed);
        let now = total.fetch_sub(w.mem_published, Ordering::Relaxed) - w.mem_published;
        w.mem_published = m;
        w.mem_others = now.saturating_sub(m);
    };
    let results = rulean_pool::run_all(
        o.threads,
        STACK_BYTES,
        &order,
        || Checker::worker(main.st.clone(), main.env.clone(), main),
        |w: &mut Checker, k| {
            publish(w);
            let r = w.run_job(&plan, ds, k);
            publish(w);
            r
        },
    );
    let out = sched::merge(&plan, &results, ds.len() as u32);
    rep.accepted = out.accepted as usize;
    if let Some((i, f)) = out.failed {
        let n = name_text(c, ds[i as usize].name());
        rep.code = code_of_check(f.kind);
        if rep.code == Code::Reject {
            rep.rejected = 1;
        }
        rep.error = Some(format!("{n}: {:?}", f.kind));
        rep.failed_decl = Some(n);
    }
    // The constants of the accepted declarations, in the order of the add stage. The cut gives `Tally` the environment after each declaration, as in a sequential run.
    let mut t = Tally::new();
    for &end in plan.ends.iter().take(out.accepted as usize) {
        c.env.set_cut(end);
        t.step(o, c, rep);
    }
    c.env.set_cut(u32::MAX);
    t.finish(rep);
    rep.f_stats = out.f_stats;
    rep.steps = c.steps + out.steps;
    rep.interns = c.st.interns() + out.interns;
    rep.s_stats = out.s_stats;
    rep.s_entries = out.s_entries as usize;
    if out.full || c.st.is_full() {
        store_full(c, rep);
    }
}

/// The result of a run where an array of the store was full. Then some handles are wrong, so the run stops with a resource error (see the crate `rulean-store`). With a memory budget, the cause can also be the budget.
fn store_full(c: &Checker, rep: &mut Report) {
    rep.code = Code::Resource;
    rep.error = Some(match c.max_memory() {
        limits::NO_LIMIT => "the store is full".to_owned(),
        b => format!("the store is full or {}", memory_text(b)),
    });
}

/// The text of a run that is above the memory budget.
pub(crate) fn memory_text(budget: usize) -> String {
    format!("the memory is above the limit of `--max-memory` ({budget} bytes)")
}

pub(crate) fn done(o: &Options, mut rep: Report, start: Instant) -> Run {
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

pub(crate) fn hex(b: &[u8]) -> String {
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
            eprintln!("rulean: {path}: {}", error_text(&e));
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
        CheckError::MemoryLimit => Code::Resource,
        CheckError::Unsupported => Code::Decline,
        _ => Code::Reject,
    }
}

/// The format version that `read_export` gives for a binary input.
pub(crate) const BINARY_FORMAT: &str = "rlb-1";

/// The text of a parse error. The line of an error in a binary input is 0.
pub(crate) fn error_text(e: &rulean_format::Error) -> String {
    if e.line == 0 {
        format!("binary input: {}", e.kind.text())
    } else {
        format!("line {}: {}", e.line, e.kind.text())
    }
}

/// Opens the input read-only through `rulean-io` (contract K2, spec 10.7), or standard input for `-`.
pub(crate) fn open_input(path: &str) -> std::io::Result<rulean_io::Input> {
    rulean_io::open(path)
}

/// Reads the input file again after the run (contract K2). If the file changed, the report gets the input error and the verdict is not given. An input that cannot be read again does not change the report.
pub(crate) fn confirm_input(source: &rulean_io::Source, rep: &mut Report) {
    let mut start = [0u8; 32];
    if !unhex(&rep.sha256, &mut start) {
        return;
    }
    match rulean_io::confirm(source, &start) {
        Ok(rulean_io::Confirm::Same | rulean_io::Confirm::NotAFile) => {}
        Ok(rulean_io::Confirm::Changed(end)) => {
            rep.code = Code::Input;
            rep.error = Some(format!(
                "the input changed during the run, the SHA-256 at the end is {}",
                hex(&end)
            ));
        }
        Err(e) => {
            rep.code = Code::Input;
            rep.error = Some(format!("cannot read the input again after the run: {e}"));
        }
    }
}

/// Reads 64 hex digits into `out`. The result is false for a text that is not 64 hex digits.
fn unhex(s: &str, out: &mut [u8; 32]) -> bool {
    let b = s.as_bytes();
    if b.len() != 64 {
        return false;
    }
    for (i, o) in out.iter_mut().enumerate() {
        match (digit(b[2 * i]), digit(b[2 * i + 1])) {
            (Some(x), Some(y)) => *o = (x << 4) | y,
            _ => return false,
        }
    }
    true
}

fn digit(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    }
}

/// Parses the export that `input` gives, one line at a time, and computes the SHA-256 digest of all of the input. After a parse error, the function reads the rest of the input for the digest only.
///
/// An input that starts with the magic of the binary format (spec 07.2) is read as a whole and decoded. Then the format version of the result is `rlb-1`, and the line of an error is 0.
pub(crate) fn read_export<R: BufRead>(
    store: &mut Store,
    mut input: R,
) -> std::io::Result<(
    Result<rulean_format::Export, rulean_format::Error>,
    [u8; 32],
)> {
    let mut hasher = Sha256::new();
    if rlb::is_binary(input.fill_buf()?) {
        let mut b = Vec::new();
        let parsed = match next_chunk(&mut input, &mut hasher, &mut b, store, 0, false)? {
            Chunk::Over => Err(rulean_format::Error {
                line: 0,
                kind: ErrorKind::StoreFull,
            }),
            _ => rlb::decode(store, &b).map(|x| rulean_format::Export {
                decls: x.decls,
                lean_version: x.header.lean_version,
                format_version: BINARY_FORMAT.as_bytes().to_vec(),
            }),
        };
        return Ok((parsed, hasher.finish()));
    }
    let mut s = Stream::new();
    let mut tail = false;
    let mut line = Vec::new();
    loop {
        line.clear();
        match next_chunk(&mut input, &mut hasher, &mut line, store, s.bytes(), true)? {
            Chunk::End => break,
            Chunk::Line => s.line(store, &line[..line.len() - 1]),
            Chunk::Tail => tail = true,
            Chunk::Over => s.full(),
        }
    }
    Ok((s.end(tail), hasher.finish()))
}

/// The result of `next_chunk`.
enum Chunk {
    /// The input has no more bytes.
    End,
    /// The buffer has a line and its newline.
    Line,
    /// The buffer has the last bytes of the input, with no newline.
    Tail,
    /// The buffer must grow above the memory budget of the store. The function read the rest of the line or of the input into the digest only, and the buffer is empty.
    Over,
}

/// Reads the next line of `input` into `buf`, or all of the input if `lines` is false. All of the bytes go into `hasher`. Before the buffer grows, the function checks that the buffer and `base` more bytes fit in the memory budget of `store` (spec 05.11.1).
fn next_chunk<R: BufRead>(
    input: &mut R,
    hasher: &mut Sha256,
    buf: &mut Vec<u8>,
    store: &Store,
    base: usize,
    lines: bool,
) -> std::io::Result<Chunk> {
    let mut read = 0;
    let mut over = false;
    loop {
        let avail = input.fill_buf()?;
        if avail.is_empty() {
            return Ok(if over {
                Chunk::Over
            } else if read == 0 {
                Chunk::End
            } else {
                Chunk::Tail
            });
        }
        let nl = if lines {
            avail.iter().position(|&c| c == b'\n')
        } else {
            None
        };
        let take = nl.map_or(avail.len(), |k| k + 1);
        hasher.update(&avail[..take]);
        if !over {
            let need = buf.len() + take;
            if need > buf.capacity() && store.over_budget(base + need.max(buf.capacity() * 2)) {
                over = true;
                *buf = Vec::new();
            } else {
                buf.extend_from_slice(&avail[..take]);
            }
        }
        read += take;
        input.consume(take);
        if nl.is_some() {
            return Ok(if over { Chunk::Over } else { Chunk::Line });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Reads `input` with a store budget of `extra` bytes above the empty store.
    fn read_in_budget(
        input: &[u8],
        extra: usize,
    ) -> (
        Result<rulean_format::Export, rulean_format::Error>,
        [u8; 32],
    ) {
        let mut store = Store::new();
        store.set_max_bytes(store.memory().total() + extra);
        read_export(&mut store, input).expect("read")
    }

    #[test]
    fn a_long_line_is_in_the_budget() {
        let meta = r#"{"meta":{"exporter":{"name":"t","version":"0"},"format":{"version":"3.1.0"},"lean":{"githash":"","version":""}}}"#;
        let mut input = format!("{meta}\n").into_bytes();
        input.extend(std::iter::repeat_n(b' ', 4 << 20));
        input.extend_from_slice(b"{}\nmore\n");
        let (parsed, digest) = read_in_budget(&input, 1 << 20);
        let e = parsed.expect_err("over the budget");
        assert_eq!((e.line, e.kind), (2, ErrorKind::StoreFull));
        // The digest is of all of the input.
        let mut h = Sha256::new();
        h.update(&input);
        assert_eq!(digest, h.finish());
    }

    #[test]
    fn a_binary_input_is_in_the_budget() {
        let mut input = rlb::MAGIC.to_vec();
        input.extend(std::iter::repeat_n(0u8, 4 << 20));
        assert!(rlb::is_binary(&input), "the magic of the test");
        let (parsed, _) = read_in_budget(&input, 1 << 20);
        assert_eq!(
            parsed.expect_err("over the budget").kind,
            ErrorKind::StoreFull
        );
    }

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
        assert_eq!(options(&strs(&["x"])).expect("valid").threads, 0);
        assert_eq!(
            options(&strs(&["x", "--threads", "8"]))
                .expect("valid")
                .threads,
            8
        );
        assert_eq!(
            options(&strs(&["x", "--threads=1024"]))
                .expect("valid")
                .threads,
            1024
        );
        assert!(options(&strs(&["x", "--threads", "0"])).is_err());
        assert!(options(&strs(&["x", "--threads", "1025"])).is_err());
        assert!(options(&strs(&["x", "--threads", "many"])).is_err());
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
        assert_eq!(code_of_check(CheckError::MemoryLimit), Code::Resource);
        let o = options(&strs(&["x", "--max-memory", "8G", "--timeout=90s"])).expect("valid");
        assert_eq!(o.max_memory, Some(8 << 30));
        assert_eq!(o.memory_budget(), 8 << 30);
        assert_eq!(o.timeout, Some(Duration::from_secs(90)));
        let o = options(&strs(&["x", "--max-memory=none"])).expect("valid");
        assert_eq!(o.memory_budget(), limits::NO_LIMIT);
        let o = options(&strs(&["x"])).expect("valid");
        assert_eq!((o.max_memory, o.timeout), (None, None));
        assert!(options(&strs(&["x", "--max-memory", "0"])).is_err());
        assert!(options(&strs(&["x", "--max-memory"])).is_err());
        assert!(options(&strs(&["x", "--timeout", "0"])).is_err());
        assert!(options(&strs(&["x", "--timeout", "soon"])).is_err());
        assert_eq!(code_of_check(CheckError::Unsupported), Code::Decline);
    }

    const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0","version":"4.36.0"}}}"#;

    fn run_on(text: &str, o: &Options) -> Report {
        check_reader(o, text.as_bytes())
            .expect("no read error")
            .report
    }

    #[test]
    fn memory_limit_gives_a_resource_failure() {
        // `axiom A : Prop`.
        let text = format!(
            "{META}\n{}\n{}\n{}\n",
            r#"{"in":1,"str":{"pre":0,"str":"A"}}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#
        );
        let o = Options {
            max_memory: Some(1024),
            ..Options::default()
        };
        let r = run_on(&text, &o);
        assert_eq!(r.code, Code::Resource);
        assert_eq!(r.accepted, 0);
        assert!(r.error.unwrap_or_default().contains("--max-memory"));
        let o = Options {
            max_memory: Some(64 << 20),
            ..Options::default()
        };
        assert_eq!(run_on(&text, &o).code, Code::Accept);
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
        // The scheduler gives the same results. The type of `B` is checked in the check stage.
        let four = Options {
            threads: 4,
            ..Options::default()
        };
        let r = run_on(&good, &four);
        assert_eq!(r.code, Code::Accept, "{:?}", r.error);
        assert_eq!(r.accepted, 1);
        let r = run_on(&bad, &four);
        assert_eq!(r.code, Code::Reject);
        assert_eq!(r.accepted, 1);
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

    #[test]
    fn keep_slowest_keeps_the_largest_times_in_order() {
        let mut v = Vec::new();
        for (k, us) in [5u64, 1, 9, 7, 3, 9, 2, 8, 6, 4, 10, 0].iter().enumerate() {
            keep_slowest(&mut v, (*us, k));
        }
        let us: Vec<u64> = v.iter().map(|x| x.0).collect();
        assert_eq!(us, vec![10, 9, 9, 8, 7, 6, 5, 4, 3, 2]);
        // For equal times, the declaration that came first stays first.
        assert_eq!(v[1].1, 2);
        assert_eq!(v[2].1, 5);
    }

    #[test]
    fn hex_digits_are_read_back() {
        let d: [u8; 32] = core::array::from_fn(|i| (i * 37) as u8);
        let mut out = [0u8; 32];
        assert!(unhex(&hex(&d), &mut out));
        assert_eq!(out, d);
        assert!(!unhex("ab", &mut out));
        assert!(!unhex(&"g".repeat(64), &mut out));
    }

    /// Writes `first`, gives the report of a run on it, and then writes `then` to the same file.
    fn changed_report(name: &str, first: &[u8], then: &[u8]) -> (rulean_io::Source, Report) {
        let p = std::env::temp_dir().join(format!("rulean-cli-{}-{name}", std::process::id()));
        std::fs::write(&p, first).expect("write");
        let i = open_input(p.to_str().expect("utf-8")).expect("open");
        let d = rulean_io::digest(i.reader).expect("digest");
        std::fs::write(&p, then).expect("write");
        let rep = Report {
            sha256: hex(&d),
            ..Report::default()
        };
        (i.source, rep)
    }

    #[test]
    fn a_changed_input_is_an_input_error() {
        let (src, mut rep) = changed_report("changed", b"abc\n", b"abd\n");
        confirm_input(&src, &mut rep);
        assert_eq!(rep.code, Code::Input);
        assert!(rep.error.as_deref().unwrap_or("").contains("changed"));
        if let rulean_io::Source::File(p) = src {
            std::fs::remove_file(p).expect("remove");
        }
    }

    #[test]
    fn an_unchanged_input_keeps_the_verdict() {
        let (src, mut rep) = changed_report("same", b"abc\n", b"abc\n");
        rep.code = Code::Reject;
        confirm_input(&src, &mut rep);
        assert_eq!(rep.code, Code::Reject);
        assert_eq!(rep.error, None);
        if let rulean_io::Source::File(p) = src {
            std::fs::remove_file(p).expect("remove");
        }
    }
}
