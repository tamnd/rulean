//! The results of a run, in the format of the Arena.
//!
//! Each result has the fields of a result file of the Lean Kernel Arena (`checker`, `test`, `status`, `correctness`, `exit_code`, `wall_time`, `cpu_time`, `max_rss`, `instructions`, `stdout`, `stderr`). So `compare` can read the results of rulean-bench and the results of the Arena in the same way. Two fields are new: `counter` names the instruction counter, and `expected` gives the outcome of the test.

use serde_json::{Value, json};

use crate::measure::{Counter, Sample};
use crate::suite::{Outcome, Test};

/// The Arena status of a run: the verdict that the exit code gives.
pub fn status(sample: &Sample) -> &'static str {
    if sample.timed_out {
        return "timeout";
    }
    match sample.exit_code {
        0 => "accepted",
        1 => "rejected",
        2 => "declined",
        _ => "error",
    }
}

/// The Arena correctness of a run: does the verdict match the outcome of the test?
pub fn correctness(outcome: Outcome, status: &str) -> &'static str {
    match (status, outcome) {
        ("declined", _) => "declined",
        ("error" | "timeout", _) => "error",
        (_, Outcome::Unknown) => "unknown",
        ("accepted", Outcome::Accept) | ("rejected", Outcome::Reject) => "correct",
        _ => "incorrect",
    }
}

/// The result of one test, as a JSON object.
pub fn result(checker: &str, test: &Test, counter: Counter, sample: &Sample) -> Value {
    let status = status(sample);
    json!({
        "checker": checker,
        "test": test.name,
        "expected": test.outcome.as_str(),
        "status": status,
        "correctness": correctness(test.outcome, status),
        "exit_code": sample.exit_code,
        "wall_time": sample.wall_time,
        "cpu_time": sample.cpu_time,
        "max_rss": sample.max_rss,
        "instructions": sample.instructions.unwrap_or(0),
        "counter": if sample.instructions.is_some() { counter.as_str() } else { "none" },
        "stdout": sample.stdout,
        "stderr": sample.stderr,
    })
}

/// The facts of a run, written before the results.
#[derive(Debug, Clone)]
pub struct RunInfo<'a> {
    /// The name of the checker.
    pub checker: &'a str,
    /// The command, with `{}` in the place of the input path.
    pub command: &'a [String],
    /// The instruction counter.
    pub counter: Counter,
    /// The time of the start of the run, in seconds since the Unix epoch.
    pub started: u64,
}

/// The file of a run: the facts of the run and one result for each test.
pub fn run_file(info: &RunInfo<'_>, results: Vec<Value>) -> Value {
    json!({
        "format": "rulean-bench/1",
        "checker": info.checker,
        "command": info.command,
        "counter": info.counter.as_str(),
        "started": info.started,
        "host": { "os": std::env::consts::OS, "arch": std::env::consts::ARCH },
        "bench_version": env!("CARGO_PKG_VERSION"),
        "results": results,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(exit_code: i32, timed_out: bool) -> Sample {
        Sample {
            exit_code,
            timed_out,
            ..Sample::default()
        }
    }

    #[test]
    fn the_exit_code_gives_the_status() {
        assert_eq!(status(&sample(0, false)), "accepted");
        assert_eq!(status(&sample(1, false)), "rejected");
        assert_eq!(status(&sample(2, false)), "declined");
        assert_eq!(status(&sample(139, false)), "error");
        assert_eq!(status(&sample(137, true)), "timeout");
    }

    #[test]
    fn the_outcome_gives_the_correctness() {
        assert_eq!(correctness(Outcome::Accept, "accepted"), "correct");
        assert_eq!(correctness(Outcome::Reject, "rejected"), "correct");
        assert_eq!(correctness(Outcome::Reject, "accepted"), "incorrect");
        assert_eq!(correctness(Outcome::Accept, "rejected"), "incorrect");
        assert_eq!(correctness(Outcome::Accept, "declined"), "declined");
        assert_eq!(correctness(Outcome::Reject, "timeout"), "error");
        assert_eq!(correctness(Outcome::Unknown, "accepted"), "unknown");
    }

    #[test]
    fn a_result_without_a_count_names_no_counter() {
        let test = Test {
            name: "t".into(),
            path: "t.ndjson".into(),
            outcome: Outcome::Accept,
        };
        let value = result("official", &test, Counter::Perf, &sample(0, false));
        assert_eq!(value["counter"], "none");
        assert_eq!(value["instructions"], 0);
        assert_eq!(value["correctness"], "correct");
    }
}
