//! The `rulean-bench` command line. See spec section 08.7 and `crates/rulean-bench/README.md`.

use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rulean_bench::compare;
use rulean_bench::measure::{self, Counter, Limits};
use rulean_bench::record::{self, RunInfo};
use rulean_bench::suite;

const USAGE: &str = "\
usage: rulean-bench <command> [options]

commands:
  run [options] <TESTS>... -- <COMMAND>...
      Run COMMAND on each .ndjson file under TESTS. In COMMAND, {} is the
      path of the export. The variable IN also holds it, as in the Arena.
      --checker NAME      the checker name in the results (default: the program name)
      --counter KIND      auto, perf, cachegrind, rusage or none (default: auto)
      --timeout SECONDS   stop a test after this time
      --filter TEXT       run only the tests whose name contains TEXT
      --out FILE          write the results to FILE (default: standard output)

  compare [options] <BASE> <NEW>
      Compare the instruction counts of two result files. A result file can
      be a file of `run`, the results.json of the Arena, or a directory of
      Arena result files.
      --base-checker NAME  use only the results of NAME in BASE
      --new-checker NAME   use only the results of NAME in NEW
      --tolerance PERCENT  fail if a test differs by more than PERCENT

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
            "--timeout" => {
                let text = value()?;
                let seconds: f64 = text
                    .parse()
                    .ok()
                    .filter(|s: &f64| s.is_finite() && *s > 0.0)
                    .ok_or_else(|| Failure::Usage(format!("bad timeout `{text}`")))?;
                parsed.timeout = Some(Duration::from_secs_f64(seconds));
            }
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
    fn run_splits_the_options_from_the_command() {
        let args = parse_run(&strs(&[
            "--counter",
            "none",
            "--timeout",
            "1.5",
            "tests",
            "--",
            "leanchecker",
            "--from-export",
            "{}",
        ]))
        .expect("parse");
        assert_eq!(args.counter, Some(Counter::None));
        assert_eq!(args.timeout, Some(Duration::from_millis(1500)));
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
    fn counts_use_the_units_of_the_spec() {
        assert_eq!(count(192_639_950), "0.193 G");
        assert_eq!(count(12_100_000_000_000), "12.100 T");
        assert_eq!(program_name("/usr/bin/leanchecker"), "leanchecker");
    }
}
