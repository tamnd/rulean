//! The `rulean-bench` command line. See spec section 08.7 and `crates/rulean-bench/README.md`.

use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rulean_bench::compare;
use rulean_bench::gate;
use rulean_bench::measure::{self, Counter, Limits};
use rulean_bench::record::{self, RunInfo};
use rulean_bench::suite;
use rulean_bench::work;

const USAGE: &str = "\
usage: rulean-bench <command> [options]

commands:
  run [options] <TESTS>... -- <COMMAND>...
      Run COMMAND on each .ndjson file under TESTS. In COMMAND, {} is the
      path of the export. The variable IN also holds it, as in the Arena.
      --checker NAME      the checker name in the results (default: the program name)
      --counter KIND      auto, perf, cachegrind, rusage or none (default: auto)
      --timeout SECONDS   stop a test after this time
      --cachegrind-max SECONDS
                          with the cachegrind counter, count only the tests
                          whose first run took at most this time
      --filter TEXT       run only the tests whose name contains TEXT
      --out FILE          write the results to FILE (default: standard output)

  compare [options] <BASE> <NEW>
      Compare the instruction counts of two result files. A result file can
      be a file of `run`, the results.json of the Arena, or a directory of
      Arena result files.
      --base-checker NAME  use only the results of NAME in BASE
      --new-checker NAME   use only the results of NAME in NEW
      --tolerance PERCENT  fail if a test differs by more than PERCENT

  gate [options] <RUN>
      Check limits on each result of a run file of `run`.
      --filter TEXT          check only the tests whose name contains TEXT
      --correct              each test must give the expected verdict
      --max-virtual-seconds S
                             at most S virtual seconds (S times 6.0 G
                             instructions) on each test; a test without a
                             count fails
      --max-rss-mib N        at most N MiB of peak memory on each test
      --max-wall SECONDS     at most this wall time on each test

  work [options] <BASELINE> <NAME>=<REPORT>...
      Compare the work count (`summary.steps` plus `summary.interns`) of
      each JSON report of `rulean check` with the entry NAME of the
      baseline file. Use a sequential check, because its count is the same
      on each machine.
      --tolerance PERCENT  fail if a count differs by more than PERCENT in
                           either direction (default: 1)
      --write              write the counts into BASELINE and do not compare

  help
      print this text

exit codes: 0 done, 1 the comparison failed, 64 usage error, 74 input or output error";

const USAGE_ERROR: u8 = 64;
const IO_ERROR: u8 = 74;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = match args.first().map(String::as_str) {
        Some("run") => run(&args[1..]),
        Some("compare") => compare_cmd(&args[1..]),
        Some("gate") => gate_cmd(&args[1..]),
        Some("work") => work_cmd(&args[1..]),
        Some("help" | "-h" | "--help") => {
            println!("{USAGE}");
            Ok(0)
        }
        Some(other) => Err(Failure::Usage(format!("unknown command `{other}`"))),
        None => Err(Failure::Usage("no command".into())),
    };
    match code {
        Ok(code) => ExitCode::from(code),
        Err(Failure::Usage(message)) => {
            eprintln!("rulean-bench: {message}\n\n{USAGE}");
            ExitCode::from(USAGE_ERROR)
        }
        Err(Failure::Io(error)) => {
            eprintln!("rulean-bench: {error}");
            ExitCode::from(IO_ERROR)
        }
    }
}

#[derive(Debug)]
enum Failure {
    Usage(String),
    Io(std::io::Error),
}

impl From<std::io::Error> for Failure {
    fn from(error: std::io::Error) -> Self {
        Failure::Io(error)
    }
}

/// The options of `run`.
#[derive(Debug)]
struct RunArgs {
    checker: Option<String>,
    counter: Option<Counter>,
    timeout: Option<Duration>,
    cachegrind_max: Option<Duration>,
    filter: Option<String>,
    out: Option<PathBuf>,
    tests: Vec<PathBuf>,
    command: Vec<String>,
}

fn parse_run(args: &[String]) -> Result<RunArgs, Failure> {
    let split = args
        .iter()
        .position(|a| a == "--")
        .ok_or_else(|| Failure::Usage("`run` needs `--` before the command".into()))?;
    let (opts, command) = (&args[..split], &args[split + 1..]);
    let mut parsed = RunArgs {
        checker: None,
        counter: None,
        timeout: None,
        cachegrind_max: None,
        filter: None,
        out: None,
        tests: Vec::new(),
        command: command.to_vec(),
    };
    let mut it = opts.iter();
    while let Some(arg) = it.next() {
        let mut value = || {
            it.next()
                .cloned()
                .ok_or_else(|| Failure::Usage(format!("`{arg}` needs a value")))
        };
        match arg.as_str() {
            "--checker" => parsed.checker = Some(value()?),
            "--counter" => {
                let text = value()?;
                parsed.counter = Some(
                    Counter::parse(&text)
                        .ok_or_else(|| Failure::Usage(format!("unknown counter `{text}`")))?,
                );
            }
            "--timeout" => parsed.timeout = Some(seconds(arg, &value()?)?),
            "--cachegrind-max" => parsed.cachegrind_max = Some(seconds(arg, &value()?)?),
            "--filter" => parsed.filter = Some(value()?),
            "--out" => parsed.out = Some(PathBuf::from(value()?)),
            flag if flag.starts_with("--") => {
                return Err(Failure::Usage(format!("unknown option `{flag}`")));
            }
            path => parsed.tests.push(PathBuf::from(path)),
        }
    }
    if parsed.tests.is_empty() {
        return Err(Failure::Usage("`run` needs at least one test path".into()));
    }
    if parsed.command.is_empty() {
        return Err(Failure::Usage("`run` needs a command after `--`".into()));
    }
    Ok(parsed)
}

fn seconds(option: &str, text: &str) -> Result<Duration, Failure> {
    text.parse()
        .ok()
        .filter(|s: &f64| s.is_finite() && *s > 0.0)
        .map(Duration::from_secs_f64)
        .ok_or_else(|| Failure::Usage(format!("bad value `{text}` for `{option}`")))
}

fn run(args: &[String]) -> Result<u8, Failure> {
    let args = parse_run(args)?;
    let counter = args.counter.unwrap_or_else(Counter::detect);
    let mut tests = suite::discover(&args.tests)?;
    if let Some(filter) = &args.filter {
        tests.retain(|t| t.name.contains(filter.as_str()));
    }
    let checker = args
        .checker
        .clone()
        .unwrap_or_else(|| program_name(&args.command[0]));
    let limits = Limits {
        timeout: args.timeout,
        output_cap: 16 * 1024,
        cachegrind_max: args.cachegrind_max,
    };
    let started = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    eprintln!(
        "rulean-bench: {} tests, checker {checker}, counter {}",
        tests.len(),
        counter.as_str()
    );

    let mut results = Vec::with_capacity(tests.len());
    let mut tally = Tally::default();
    for (i, test) in tests.iter().enumerate() {
        let path = test.path.to_string_lossy();
        let argv: Vec<String> = args
            .command
            .iter()
            .map(|a| a.replace("{}", &path))
            .collect();
        let sample = measure::measure(&argv, &test.path, counter, &limits)?;
        let result = record::result(&checker, test, counter, &sample);
        let correctness = result["correctness"].as_str().unwrap_or("error").to_owned();
        tally.add(&correctness, &sample);
        eprintln!(
            "[{}/{}] {}  {}  {}  {}  {:.3} s  {}",
            i + 1,
            tests.len(),
            test.name,
            result["status"].as_str().unwrap_or(""),
            correctness,
            count(sample.instructions.unwrap_or(0)),
            sample.wall_time,
            mebibytes(sample.max_rss)
        );
        results.push(result);
    }
    eprintln!("{}", tally.line());

    let info = RunInfo {
        checker: &checker,
        command: &args.command,
        counter,
        started,
    };
    let text = serde_json::to_string_pretty(&record::run_file(&info, results))
        .map_err(std::io::Error::other)?
        + "\n";
    match &args.out {
        Some(path) => std::fs::write(path, text)?,
        None => std::io::stdout().lock().write_all(text.as_bytes())?,
    }
    Ok(0)
}

fn program_name(program: &str) -> String {
    std::path::Path::new(program)
        .file_stem()
        .map_or_else(|| program.to_owned(), |s| s.to_string_lossy().into_owned())
}

#[derive(Debug, Default)]
struct Tally {
    correct: usize,
    incorrect: usize,
    declined: usize,
    error: usize,
    unknown: usize,
    instructions: u64,
    wall_time: f64,
}

impl Tally {
    fn add(&mut self, correctness: &str, sample: &measure::Sample) {
        match correctness {
            "correct" => self.correct += 1,
            "incorrect" => self.incorrect += 1,
            "declined" => self.declined += 1,
            "unknown" => self.unknown += 1,
            _ => self.error += 1,
        }
        self.instructions = self
            .instructions
            .saturating_add(sample.instructions.unwrap_or(0));
        self.wall_time += sample.wall_time;
    }

    fn line(&self) -> String {
        format!(
            "rulean-bench: {} correct, {} incorrect, {} declined, {} error, {} unknown; {} instructions, {:.3} s wall",
            self.correct,
            self.incorrect,
            self.declined,
            self.error,
            self.unknown,
            count(self.instructions),
            self.wall_time
        )
    }
}

fn compare_cmd(args: &[String]) -> Result<u8, Failure> {
    let mut base_checker = None;
    let mut new_checker = None;
    let mut tolerance: Option<f64> = None;
    let mut paths = Vec::new();
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || {
            it.next()
                .cloned()
                .ok_or_else(|| Failure::Usage(format!("`{arg}` needs a value")))
        };
        match arg.as_str() {
            "--base-checker" => base_checker = Some(value()?),
            "--new-checker" => new_checker = Some(value()?),
            "--tolerance" => {
                let text = value()?;
                tolerance = Some(
                    text.parse()
                        .ok()
                        .filter(|t: &f64| t.is_finite() && *t >= 0.0)
                        .ok_or_else(|| Failure::Usage(format!("bad tolerance `{text}`")))?,
                );
            }
            flag if flag.starts_with("--") => {
                return Err(Failure::Usage(format!("unknown option `{flag}`")));
            }
            path => paths.push(PathBuf::from(path)),
        }
    }
    let [base, new] = &paths[..] else {
        return Err(Failure::Usage("`compare` needs two result files".into()));
    };
    let base = compare::load(base, base_checker.as_deref())?;
    let new = compare::load(new, new_checker.as_deref())?;
    let report = compare::compare(&base, &new);
    print_report(&report);
    let mut failed = report.rows.iter().any(|r| r.status_differs);
    if let Some(tolerance) = tolerance {
        failed |= report.max_deviation() > tolerance;
    }
    Ok(u8::from(failed))
}

fn parse_gate(args: &[String]) -> Result<(gate::Limits, PathBuf), Failure> {
    let mut limits = gate::Limits::default();
    let mut paths = Vec::new();
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        let mut value = || {
            it.next()
                .cloned()
                .ok_or_else(|| Failure::Usage(format!("`{arg}` needs a value")))
        };
        match arg.as_str() {
            "--filter" => limits.filter = Some(value()?),
            "--correct" => limits.correct = true,
            "--max-virtual-seconds" => {
                let s = seconds(arg, &value()?)?.as_secs_f64();
                #[allow(
                    clippy::cast_possible_truncation,
                    clippy::cast_sign_loss,
                    clippy::cast_precision_loss,
                    reason = "the value is positive and far below 2^64"
                )]
                let n = (s * gate::VIRTUAL_SECOND as f64) as u64;
                limits.max_instructions = Some(n);
            }
            "--max-rss-mib" => {
                let text = value()?;
                let n: u64 = text
                    .parse()
                    .map_err(|_| Failure::Usage(format!("bad value `{text}` for `{arg}`")))?;
                limits.max_rss = Some(n.saturating_mul(1024 * 1024));
            }
            "--max-wall" => limits.max_wall = Some(seconds(arg, &value()?)?.as_secs_f64()),
            flag if flag.starts_with("--") => {
                return Err(Failure::Usage(format!("unknown option `{flag}`")));
            }
            path => paths.push(PathBuf::from(path)),
        }
    }
    let [path] = &paths[..] else {
        return Err(Failure::Usage("`gate` needs one run file".into()));
    };
    Ok((limits, path.clone()))
}

fn gate_cmd(args: &[String]) -> Result<u8, Failure> {
    let (limits, path) = parse_gate(args)?;
    let text = std::fs::read_to_string(&path)?;
    let value: serde_json::Value = serde_json::from_str(&text).map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("{}: {e}", path.display()),
        )
    })?;
    let records = value["results"].as_array().cloned().unwrap_or_default();
    let outcome = gate::check(&records, &limits);
    for f in &outcome.failures {
        println!("{f}");
    }
    println!(
        "gate: {} tests checked, {} failures",
        outcome.checked,
        outcome.failures.len()
    );
    Ok(u8::from(!outcome.passed()))
}

/// The options of `work`.
#[derive(Debug, PartialEq)]
struct WorkArgs {
    tolerance: f64,
    write: bool,
    baseline: PathBuf,
    reports: Vec<(String, PathBuf)>,
}

fn parse_work(args: &[String]) -> Result<WorkArgs, Failure> {
    let mut tolerance = 1.0;
    let mut write = false;
    let mut rest = Vec::new();
    let mut it = args.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--tolerance" => {
                let text = it
                    .next()
                    .ok_or_else(|| Failure::Usage("`--tolerance` needs a value".into()))?;
                tolerance = text
                    .parse()
                    .ok()
                    .filter(|t: &f64| t.is_finite() && *t >= 0.0)
                    .ok_or_else(|| {
                        Failure::Usage(format!("bad value `{text}` for `--tolerance`"))
                    })?;
            }
            "--write" => write = true,
            flag if flag.starts_with("--") => {
                return Err(Failure::Usage(format!("unknown option `{flag}`")));
            }
            other => rest.push(other.to_owned()),
        }
    }
    let mut rest = rest.into_iter();
    let baseline = rest
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| Failure::Usage("`work` needs a baseline file".into()))?;
    let mut reports = Vec::new();
    for r in rest {
        let (name, path) = r
            .split_once('=')
            .filter(|(n, p)| !n.is_empty() && !p.is_empty())
            .ok_or_else(|| Failure::Usage(format!("`{r}` is not NAME=REPORT")))?;
        reports.push((name.to_owned(), PathBuf::from(path)));
    }
    if reports.is_empty() {
        return Err(Failure::Usage(
            "`work` needs at least one NAME=REPORT".into(),
        ));
    }
    Ok(WorkArgs {
        tolerance,
        write,
        baseline,
        reports,
    })
}

fn read_json(path: &std::path::Path) -> Result<serde_json::Value, Failure> {
    let text = std::fs::read_to_string(path)?;
    serde_json::from_str(&text).map_err(|e| {
        Failure::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!("{}: {e}", path.display()),
        ))
    })
}

fn work_cmd(args: &[String]) -> Result<u8, Failure> {
    let args = parse_work(args)?;
    let mut baseline = if args.write && !args.baseline.exists() {
        serde_json::Value::Null
    } else {
        read_json(&args.baseline)?
    };
    let mut failed = 0;
    for (name, path) in &args.reports {
        let new = match work::from_report(&read_json(path)?) {
            Ok(c) => c,
            Err(e) => {
                println!("{name}: {}: {e}", path.display());
                failed += 1;
                continue;
            }
        };
        if args.write {
            work::set_baseline(&mut baseline, name, &new);
            println!(
                "{name}: wrote a work count of {}, Lean {}",
                new.work, new.lean_version
            );
            continue;
        }
        let base = work::from_baseline(&baseline, name);
        let verdict = work::compare(base.as_ref(), &new, args.tolerance);
        let base_work = base.as_ref().map_or(0, |b| b.work);
        let line = match verdict {
            work::Verdict::Pass(c) => {
                format!("work {base_work} to {} ({c:+.3}%), pass", new.work)
            }
            work::Verdict::More(c) => format!(
                "work {base_work} to {} ({c:+.3}%), more work than the tolerance of {}%",
                new.work, args.tolerance
            ),
            work::Verdict::Less(c) => format!(
                "work {base_work} to {} ({c:+.3}%), less work than the tolerance of {}%, so update the baseline with --write",
                new.work, args.tolerance
            ),
            work::Verdict::Version => format!(
                "the report is for Lean {} and the baseline is for Lean {}, so update the baseline with --write",
                new.lean_version,
                base.as_ref().map_or("", |b| b.lean_version.as_str())
            ),
            work::Verdict::Missing => format!(
                "a work count of {}, Lean {}, but the baseline has no entry, so add it with --write",
                new.work, new.lean_version
            ),
        };
        println!("{name}: {line}");
        if !verdict.passed() {
            failed += 1;
        }
    }
    if args.write {
        let mut text = serde_json::to_string_pretty(&baseline)
            .map_err(|e| Failure::Io(std::io::Error::new(std::io::ErrorKind::InvalidData, e)))?;
        text.push('\n');
        std::fs::write(&args.baseline, text)?;
    }
    println!("work: {} exports, {failed} failures", args.reports.len());
    Ok(u8::from(failed > 0))
}

fn print_report(report: &compare::Report) {
    println!("{:<50} {:>14} {:>14} {:>8}", "test", "base", "new", "ratio");
    for row in &report.rows {
        let mark = if row.status_differs {
            "  status differs"
        } else {
            ""
        };
        println!(
            "{:<50} {:>14} {:>14} {:>8.4}{mark}",
            row.test, row.base, row.new, row.ratio
        );
    }
    println!(
        "{:<50} {:>14} {:>14} {:>8.4}",
        "total",
        report.base_total,
        report.new_total,
        report.total_ratio()
    );
    println!(
        "{} tests compared, {} skipped, largest deviation {:.2}%",
        report.rows.len(),
        report.skipped.len(),
        report.max_deviation()
    );
}

/// An instruction count with the unit of spec 00.3 (G or T).
fn count(n: u64) -> String {
    const G: f64 = 1e9;
    #[allow(clippy::cast_precision_loss)]
    let n = n as f64;
    if n >= 1000.0 * G {
        format!("{:.3} T", n / (1000.0 * G))
    } else {
        format!("{:.3} G", n / G)
    }
}

fn mebibytes(bytes: u64) -> String {
    format!("{} MiB", bytes / (1024 * 1024))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(args: &[&str]) -> Vec<String> {
        args.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn work_reads_its_options() {
        let a = parse_work(&strs(&[
            "b.json",
            "Init=i.json",
            "--tolerance",
            "0.5",
            "Std=s.json",
        ]))
        .expect("valid");
        assert_eq!(
            a,
            WorkArgs {
                tolerance: 0.5,
                write: false,
                baseline: PathBuf::from("b.json"),
                reports: vec![
                    ("Init".to_owned(), PathBuf::from("i.json")),
                    ("Std".to_owned(), PathBuf::from("s.json")),
                ],
            }
        );
        assert!(
            parse_work(&strs(&["b.json", "--write", "Init=i.json"]))
                .expect("valid")
                .write
        );
        assert!(parse_work(&strs(&["b.json"])).is_err());
        assert!(parse_work(&strs(&["b.json", "i.json"])).is_err());
        assert!(parse_work(&strs(&["b.json", "=i.json"])).is_err());
        assert!(parse_work(&strs(&["b.json", "Init=i.json", "--tolerance", "-1"])).is_err());
        assert!(parse_work(&strs(&["b.json", "Init=i.json", "--other"])).is_err());
    }

    #[test]
    fn run_splits_the_options_from_the_command() {
        let args = parse_run(&strs(&[
            "--counter",
            "none",
            "--timeout",
            "1.5",
            "--cachegrind-max",
            "2",
            "tests",
            "--",
            "leanchecker",
            "--from-export",
            "{}",
        ]))
        .expect("parse");
        assert_eq!(args.counter, Some(Counter::None));
        assert_eq!(args.timeout, Some(Duration::from_millis(1500)));
        assert_eq!(args.cachegrind_max, Some(Duration::from_secs(2)));
        assert_eq!(args.tests, [PathBuf::from("tests")]);
        assert_eq!(args.command, ["leanchecker", "--from-export", "{}"]);
    }

    #[test]
    fn run_rejects_bad_arguments() {
        assert!(parse_run(&strs(&["tests", "leanchecker"])).is_err());
        assert!(parse_run(&strs(&["--", "leanchecker"])).is_err());
        assert!(parse_run(&strs(&["tests", "--"])).is_err());
        assert!(parse_run(&strs(&["--timeout", "-1", "tests", "--", "x"])).is_err());
        assert!(parse_run(&strs(&["--counter", "cycles", "tests", "--", "x"])).is_err());
    }

    #[test]
    fn gate_options() {
        let (l, p) = parse_gate(&strs(&[
            "--filter",
            "perf/",
            "--correct",
            "--max-virtual-seconds",
            "1",
            "--max-rss-mib",
            "4096",
            "run.json",
        ]))
        .expect("parse");
        assert_eq!(p, PathBuf::from("run.json"));
        assert_eq!(l.filter.as_deref(), Some("perf/"));
        assert!(l.correct);
        assert_eq!(l.max_instructions, Some(6_000_000_000));
        assert_eq!(l.max_rss, Some(4 << 30));
        assert!(parse_gate(&strs(&["a.json", "b.json"])).is_err());
        assert!(parse_gate(&strs(&["--max-rss-mib", "x", "a.json"])).is_err());
    }

    #[test]
    fn counts_use_the_units_of_the_spec() {
        assert_eq!(count(192_639_950), "0.193 G");
        assert_eq!(count(12_100_000_000_000), "12.100 T");
        assert_eq!(program_name("/usr/bin/leanchecker"), "leanchecker");
    }
}
