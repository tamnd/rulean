//! The work gate of the quick suite (spec 08.7.4).
//!
//! The gate compares the work count of the JSON reports of `rulean check` with a baseline file. A sequential check gives the same count on each machine, so the baseline is a file in the repository and the gate has no noise.
//!
//! The work count is `summary.steps` plus `summary.interns` of the report: the calls of `enter` of the type checker and the calls of `intern_expr` of the store. The first count follows the reductions and the inference, and the second count follows the substitution and the parse.
//!
//! The baseline file is a JSON object. Each key is the name of an export, for example `Init`. Each value has the Lean version of the export and the work count:
//!
//! ```json
//! { "Init": { "lean_version": "4.36.0", "work": 123456789 } }
//! ```

use serde_json::{Map, Value, json};

/// The work count of one export in the baseline or in a report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Count {
    /// The Lean version of the export.
    pub lean_version: String,
    /// The work count.
    pub work: u64,
}

/// Reads the work count and the verdict of a JSON report of `rulean check`. It gives an error text if the report has no count or the verdict is not `accept`.
pub fn from_report(report: &Value) -> Result<Count, String> {
    let verdict = report["verdict"].as_str().unwrap_or("none");
    if verdict != "accept" {
        return Err(format!("the verdict is `{verdict}`, not `accept`"));
    }
    let steps = report["summary"]["steps"]
        .as_u64()
        .ok_or("the report has no `summary.steps`")?;
    let interns = report["summary"]["interns"]
        .as_u64()
        .ok_or("the report has no `summary.interns`")?;
    let lean_version = report["input"]["lean_version"]
        .as_str()
        .unwrap_or("")
        .to_owned();
    Ok(Count {
        lean_version,
        work: steps.saturating_add(interns),
    })
}

/// Reads the entry `name` of a baseline file. It gives `None` if there is no entry or the entry is not valid.
pub fn from_baseline(baseline: &Value, name: &str) -> Option<Count> {
    let e = &baseline[name];
    Some(Count {
        lean_version: e["lean_version"].as_str()?.to_owned(),
        work: e["work"].as_u64()?,
    })
}

/// Puts the count of `name` into a baseline file. Other entries stay.
pub fn set_baseline(baseline: &mut Value, name: &str, count: &Count) {
    if !baseline.is_object() {
        *baseline = Value::Object(Map::new());
    }
    baseline[name] = json!({ "lean_version": count.lean_version, "work": count.work });
}

/// The result of the comparison of one export.
#[derive(Debug, Clone, PartialEq)]
pub enum Verdict {
    /// The count is within the tolerance. The value is the change in percent.
    Pass(f64),
    /// The count is above the baseline by more than the tolerance. The value is the change in percent.
    More(f64),
    /// The count is below the baseline by more than the tolerance. The value is the change in percent. The baseline must go down, or a later regression of the same size does not fail the gate.
    Less(f64),
    /// The Lean version of the report is not the Lean version of the baseline.
    Version,
    /// The baseline has no entry for the export.
    Missing,
}

impl Verdict {
    /// True if the gate passes.
    pub fn passed(&self) -> bool {
        matches!(self, Verdict::Pass(_))
    }
}

/// Compares a count with the baseline. `tolerance` is in percent.
pub fn compare(base: Option<&Count>, new: &Count, tolerance: f64) -> Verdict {
    let Some(base) = base else {
        return Verdict::Missing;
    };
    if base.lean_version != new.lean_version {
        return Verdict::Version;
    }
    let change = change(base.work, new.work);
    if change > tolerance {
        Verdict::More(change)
    } else if change < -tolerance {
        Verdict::Less(change)
    } else {
        Verdict::Pass(change)
    }
}

/// The change from `base` to `new` in percent. A base of 0 gives 0 for a new count of 0, and 100 for a larger new count.
#[allow(clippy::cast_precision_loss)]
pub fn change(base: u64, new: u64) -> f64 {
    if base == 0 {
        return if new == 0 { 0.0 } else { 100.0 };
    }
    (new as f64 - base as f64) * 100.0 / base as f64
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count(v: &str, work: u64) -> Count {
        Count {
            lean_version: v.to_owned(),
            work,
        }
    }

    #[test]
    fn a_report_gives_its_count() {
        let r = json!({ "verdict": "accept", "input": { "lean_version": "4.36.0" }, "summary": { "steps": 42, "interns": 8 } });
        assert_eq!(from_report(&r), Ok(count("4.36.0", 50)));
    }

    #[test]
    fn a_report_without_accept_or_count_fails() {
        let r = json!({ "verdict": "reject", "summary": { "steps": 42 } });
        assert!(from_report(&r).expect_err("a failure").contains("reject"));
        let r = json!({ "verdict": "accept", "summary": {} });
        assert!(
            from_report(&r)
                .expect_err("a failure")
                .contains("summary.steps")
        );
        let r = json!({ "verdict": "accept", "summary": { "steps": 1 } });
        assert!(
            from_report(&r)
                .expect_err("a failure")
                .contains("summary.interns")
        );
    }

    #[test]
    fn the_baseline_keeps_other_entries() {
        let mut b = json!({ "Std": { "lean_version": "4.36.0", "work": 7 } });
        set_baseline(&mut b, "Init", &count("4.36.0", 5));
        assert_eq!(from_baseline(&b, "Init"), Some(count("4.36.0", 5)));
        assert_eq!(from_baseline(&b, "Std"), Some(count("4.36.0", 7)));
        assert_eq!(from_baseline(&b, "Mathlib"), None);
        let mut empty = Value::Null;
        set_baseline(&mut empty, "Init", &count("4.36.0", 5));
        assert_eq!(from_baseline(&empty, "Init"), Some(count("4.36.0", 5)));
    }

    #[test]
    fn the_tolerance_applies_in_both_directions() {
        let base = count("4.36.0", 1000);
        assert_eq!(
            compare(Some(&base), &count("4.36.0", 1010), 1.0),
            Verdict::Pass(1.0)
        );
        assert_eq!(
            compare(Some(&base), &count("4.36.0", 1011), 1.0),
            Verdict::More(1.1)
        );
        assert_eq!(
            compare(Some(&base), &count("4.36.0", 989), 1.0),
            Verdict::Less(-1.1)
        );
        assert!(compare(Some(&base), &count("4.36.0", 990), 1.0).passed());
    }

    #[test]
    fn a_new_version_or_export_fails() {
        let base = count("4.36.0", 1000);
        assert_eq!(
            compare(Some(&base), &count("4.37.0", 1000), 1.0),
            Verdict::Version
        );
        assert_eq!(compare(None, &count("4.36.0", 1000), 1.0), Verdict::Missing);
    }

    #[test]
    fn a_zero_base_is_safe() {
        assert!((change(0, 0)).abs() < f64::EPSILON);
        assert!((change(0, 5) - 100.0).abs() < f64::EPSILON);
    }
}
