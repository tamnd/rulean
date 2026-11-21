//! Compare the instruction counts of two runs.
//!
//! A side of the comparison can be a run file of rulean-bench, the `results.json` file of the Arena, or a directory of Arena result files. The M0 exit criterion of spec 14 uses this: the counts of the official kernel on our machine must be within 2% of the counts of the Arena.

use std::collections::BTreeMap;
use std::io;
use std::path::Path;

use serde_json::Value;

/// The count and the status of one test on one side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The instruction count. 0 means that the run gave no count.
    pub instructions: u64,
    /// The Arena status, for example `accepted`.
    pub status: String,
}

/// The results of one side, by test name.
pub type Side = BTreeMap<String, Entry>;

/// Read the results of one side. If `checker` is given, keep only the results of that checker. A file with the results of more than one checker needs it.
pub fn load(path: &Path, checker: Option<&str>) -> io::Result<Side> {
    let mut records = Vec::new();
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            let file = entry?.path();
            if file.extension().is_some_and(|e| e == "json") {
                collect(read_json(&file)?, &mut records);
            }
        }
    } else {
        collect(read_json(path)?, &mut records);
    }
    side(&records, checker).map_err(|e| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{}: {e}", path.display()),
        )
    })
}

fn read_json(path: &Path) -> io::Result<Value> {
    let text = std::fs::read_to_string(path)?;
    serde_json::from_str(&text).map_err(|e| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{}: {e}", path.display()),
        )
    })
}

fn collect(value: Value, records: &mut Vec<Value>) {
    match value {
        Value::Array(items) => records.extend(items),
        Value::Object(mut map) => match map.remove("results") {
            Some(Value::Array(items)) => records.extend(items),
            _ => records.push(Value::Object(map)),
        },
        _ => {}
    }
}

fn side(records: &[Value], checker: Option<&str>) -> Result<Side, String> {
    let mut checkers: Vec<&str> = records
        .iter()
        .filter_map(|r| r["checker"].as_str())
        .collect();
    checkers.sort_unstable();
    checkers.dedup();
    if checker.is_none() && checkers.len() > 1 {
        return Err(format!(
            "the results have {} checkers, so name one with --base-checker or --new-checker",
            checkers.len()
        ));
    }
    let mut out = Side::new();
    for record in records {
        if checker.is_some_and(|c| record["checker"].as_str() != Some(c)) {
            continue;
        }
        let Some(test) = record["test"].as_str() else {
            continue;
        };
        let entry = Entry {
            instructions: record["instructions"].as_u64().unwrap_or(0),
            status: record["status"].as_str().unwrap_or("error").to_owned(),
        };
        out.insert(test.to_owned(), entry);
    }
    if out.is_empty() {
        return Err("no results for the checker".to_owned());
    }
    Ok(out)
}

/// One row of the comparison.
#[derive(Debug, Clone, PartialEq)]
pub struct Row {
    /// The test name.
    pub test: String,
    /// The count of the base side.
    pub base: u64,
    /// The count of the new side.
    pub new: u64,
    /// The new count divided by the base count.
    pub ratio: f64,
    /// The two sides give a different status.
    pub status_differs: bool,
}

/// The comparison of two sides.
#[derive(Debug, Clone, PartialEq)]
pub struct Report {
    /// One row for each test that has a count on both sides.
    pub rows: Vec<Row>,
    /// The tests that are on one side only, or that have no count on one side.
    pub skipped: Vec<String>,
    /// The sum of the counts of the base side, over the rows.
    pub base_total: u64,
    /// The sum of the counts of the new side, over the rows.
    pub new_total: u64,
}

impl Report {
    /// The largest deviation of a row from a ratio of 1, in percent.
    pub fn max_deviation(&self) -> f64 {
        self.rows
            .iter()
            .map(|r| (r.ratio - 1.0).abs() * 100.0)
            .fold(0.0, f64::max)
    }

    /// The new total divided by the base total.
    pub fn total_ratio(&self) -> f64 {
        ratio(self.new_total, self.base_total)
    }
}

fn ratio(new: u64, base: u64) -> f64 {
    if base == 0 {
        return f64::NAN;
    }
    // The counts are below 2^53 on each corpus of spec 08.7.2, so the conversion is exact.
    new as f64 / base as f64
}

/// Compare two sides, test by test.
pub fn compare(base: &Side, new: &Side) -> Report {
    let mut report = Report {
        rows: Vec::new(),
        skipped: Vec::new(),
        base_total: 0,
        new_total: 0,
    };
    for (test, b) in base {
        match new.get(test) {
            Some(n) if b.instructions > 0 && n.instructions > 0 => {
                report.base_total += b.instructions;
                report.new_total += n.instructions;
                report.rows.push(Row {
                    test: test.clone(),
                    base: b.instructions,
                    new: n.instructions,
                    ratio: ratio(n.instructions, b.instructions),
                    status_differs: b.status != n.status,
                });
            }
            _ => report.skipped.push(test.clone()),
        }
    }
    report
        .skipped
        .extend(new.keys().filter(|t| !base.contains_key(*t)).cloned());
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn entry(instructions: u64, status: &str) -> Entry {
        Entry {
            instructions,
            status: status.into(),
        }
    }

    #[test]
    fn arena_results_need_a_checker_name() {
        let records = [
            json!({"checker": "official", "test": "a", "instructions": 100, "status": "accepted"}),
            json!({"checker": "nanoda", "test": "a", "instructions": 10, "status": "accepted"}),
        ];
        assert!(side(&records, None).is_err());
        let official = side(&records, Some("official")).expect("official");
        assert_eq!(official["a"], entry(100, "accepted"));
    }

    #[test]
    fn a_run_file_and_an_arena_file_read_the_same() {
        let mut records = Vec::new();
        collect(
            json!({"format": "rulean-bench/1", "results": [{"checker": "c", "test": "t", "instructions": 5, "status": "rejected"}]}),
            &mut records,
        );
        collect(
            json!({"meta": {}, "results": [{"checker": "c", "test": "u", "instructions": 6, "status": "accepted"}]}),
            &mut records,
        );
        let side = side(&records, None).expect("side");
        assert_eq!(side.len(), 2);
    }

    #[test]
    fn the_report_gives_the_ratios_and_the_skipped_tests() {
        let base: Side = [
            ("a".into(), entry(100, "accepted")),
            ("b".into(), entry(200, "rejected")),
            ("c".into(), entry(0, "error")),
        ]
        .into();
        let new: Side = [
            ("a".into(), entry(101, "accepted")),
            ("b".into(), entry(196, "accepted")),
            ("c".into(), entry(7, "accepted")),
            ("d".into(), entry(1, "accepted")),
        ]
        .into();
        let report = compare(&base, &new);
        assert_eq!(report.rows.len(), 2);
        assert_eq!(report.skipped, ["c", "d"]);
        assert!(!report.rows[0].status_differs);
        assert!(report.rows[1].status_differs);
        assert!((report.max_deviation() - 2.0).abs() < 1e-9);
        assert!((report.total_ratio() - 297.0 / 300.0).abs() < 1e-12);
    }
}
