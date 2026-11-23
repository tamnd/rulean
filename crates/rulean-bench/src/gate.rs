//! The gates of a run (spec 08.7.2).
//!
//! A gate reads a run file of `run` and checks limits on each result. The nightly bench uses it for the verdicts, for P1.d (no `perf/` test above 1 virtual second) and for the peak memory of P1.f.

use serde_json::Value;

/// The instructions of one virtual second: 6.0 G (spec 08.7.1).
pub const VIRTUAL_SECOND: u64 = 6_000_000_000;

/// The limits of a gate. A limit that is `None` is not checked.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Limits {
    /// Check only the tests whose name contains this text.
    pub filter: Option<String>,
    /// Each test must have the correctness `correct`.
    pub correct: bool,
    /// The largest instruction count of one test. A test without a count fails this limit.
    pub max_instructions: Option<u64>,
    /// The largest peak memory of one test, in bytes.
    pub max_rss: Option<u64>,
    /// The largest wall time of one test, in seconds.
    pub max_wall: Option<f64>,
}

/// The result of a gate.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Outcome {
    /// The number of tests that the gate checked.
    pub checked: usize,
    /// One line for each failed limit.
    pub failures: Vec<String>,
}

impl Outcome {
    /// True if no limit failed and the gate checked at least one test.
    pub fn passed(&self) -> bool {
        self.failures.is_empty() && self.checked > 0
    }
}

/// Checks `limits` on each result of `records`.
pub fn check(records: &[Value], limits: &Limits) -> Outcome {
    let mut out = Outcome::default();
    for r in records {
        let test = r["test"].as_str().unwrap_or("?");
        if limits.filter.as_deref().is_some_and(|f| !test.contains(f)) {
            continue;
        }
        out.checked += 1;
        if limits.correct {
            let c = r["correctness"].as_str().unwrap_or("error");
            if c != "correct" {
                out.failures.push(format!(
                    "{test}: the result is {c}, with status {}",
                    r["status"].as_str().unwrap_or("?")
                ));
            }
        }
        if let Some(max) = limits.max_instructions {
            let n = r["instructions"].as_u64().unwrap_or(0);
            if n == 0 {
                out.failures
                    .push(format!("{test}: the run has no instruction count"));
            } else if n > max {
                out.failures
                    .push(format!("{test}: {n} instructions, the limit is {max}"));
            }
        }
        if let Some(max) = limits.max_rss {
            let n = r["max_rss"].as_u64().unwrap_or(0);
            if n > max {
                out.failures
                    .push(format!("{test}: peak memory {n} bytes, the limit is {max}"));
            }
        }
        if let Some(max) = limits.max_wall {
            let t = r["wall_time"].as_f64().unwrap_or(f64::INFINITY);
            if t > max {
                out.failures
                    .push(format!("{test}: wall time {t:.3} s, the limit is {max} s"));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn rec(test: &str, correctness: &str, instructions: u64, rss: u64, wall: f64) -> Value {
        json!({
            "test": test,
            "status": "accepted",
            "correctness": correctness,
            "instructions": instructions,
            "max_rss": rss,
            "wall_time": wall,
        })
    }

    #[test]
    fn a_run_within_the_limits_passes() {
        let rs = [
            rec("perf/a", "correct", 5_000_000_000, 100, 1.0),
            rec("tutorial/b", "correct", 9_000_000_000, 100, 1.0),
        ];
        let l = Limits {
            filter: Some("perf/".into()),
            correct: true,
            max_instructions: Some(VIRTUAL_SECOND),
            ..Limits::default()
        };
        let o = check(&rs, &l);
        assert_eq!(o.checked, 1);
        assert!(o.passed(), "{:?}", o.failures);
    }

    #[test]
    fn each_limit_can_fail() {
        let rs = [
            rec("perf/a", "incorrect", 7_000_000_000, 5000, 9.0),
            rec("perf/b", "correct", 0, 1, 0.5),
        ];
        let l = Limits {
            filter: None,
            correct: true,
            max_instructions: Some(VIRTUAL_SECOND),
            max_rss: Some(4096),
            max_wall: Some(2.0),
        };
        let o = check(&rs, &l);
        assert_eq!(o.checked, 2);
        assert_eq!(o.failures.len(), 5, "{:?}", o.failures);
        assert!(o.failures[4].contains("no instruction count"));
    }

    #[test]
    fn a_gate_that_checks_no_test_fails() {
        let rs = [rec("tutorial/b", "correct", 1, 1, 0.1)];
        let l = Limits {
            filter: Some("perf/".into()),
            ..Limits::default()
        };
        assert!(!check(&rs, &l).passed());
    }
}
