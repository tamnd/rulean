//! Find the tests of a run.
//!
//! A test is one `.ndjson` export. The layout is the layout of the Arena test tarball: `good/NAME.ndjson` must be accepted and `bad/NAME.ndjson` must be rejected. The name of a test is its path under `good/` or `bad/`, without the extension, with `/` between the parts. This is the test name of the Arena.

use std::ffi::OsStr;
use std::io;
use std::path::{Component, Path, PathBuf};

/// The verdict that a test expects.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The test is in a `good` directory. The checker must accept it.
    Accept,
    /// The test is in a `bad` directory. The checker must reject it.
    Reject,
    /// The layout does not give the verdict.
    Unknown,
}

impl Outcome {
    /// The name of the outcome in the Arena results.
    pub fn as_str(self) -> &'static str {
        match self {
            Outcome::Accept => "accept",
            Outcome::Reject => "reject",
            Outcome::Unknown => "unknown",
        }
    }

    fn from_dir(name: &OsStr) -> Option<Outcome> {
        match name.to_str() {
            Some("good") => Some(Outcome::Accept),
            Some("bad") => Some(Outcome::Reject),
            _ => None,
        }
    }
}

/// One test: an export file and the verdict that it expects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Test {
    /// The Arena name of the test, for example `tutorial/011_nonTypeAxiom`.
    pub name: String,
    /// The path of the export file.
    pub path: PathBuf,
    /// The verdict that the test expects.
    pub outcome: Outcome,
}

/// Find the tests under each root. A root can be a file or a directory. The result is sorted by name, so that a run does not depend on the order of the file system.
pub fn discover(roots: &[PathBuf]) -> io::Result<Vec<Test>> {
    let mut tests = Vec::new();
    for root in roots {
        if root.is_file() {
            tests.push(single(root));
        } else {
            walk(root, &mut tests)?;
        }
    }
    tests.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(tests)
}

fn single(path: &Path) -> Test {
    let outcome = path
        .parent()
        .and_then(Path::file_name)
        .and_then(Outcome::from_dir)
        .unwrap_or(Outcome::Unknown);
    let name = path
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();
    Test {
        name,
        path: path.to_path_buf(),
        outcome,
    }
}

fn walk(root: &Path, tests: &mut Vec<Test>) -> io::Result<()> {
    let root_outcome = root.file_name().and_then(Outcome::from_dir);
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir)? {
            let path = entry?.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension() == Some(OsStr::new("ndjson")) {
                tests.push(named(root, root_outcome, path));
            }
        }
    }
    Ok(())
}

fn named(root: &Path, root_outcome: Option<Outcome>, path: PathBuf) -> Test {
    let rel = path.strip_prefix(root).unwrap_or(&path).with_extension("");
    let mut parts: Vec<String> = rel
        .components()
        .filter_map(|c| match c {
            Component::Normal(s) => Some(s.to_string_lossy().into_owned()),
            _ => None,
        })
        .collect();
    let mut outcome = root_outcome;
    if outcome.is_none() && parts.len() > 1 {
        outcome = Outcome::from_dir(OsStr::new(&parts[0]));
        if outcome.is_some() {
            parts.remove(0);
        }
    }
    Test {
        name: parts.join("/"),
        path,
        outcome: outcome.unwrap_or(Outcome::Unknown),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree() -> PathBuf {
        let dir = std::env::temp_dir().join(format!("rulean-bench-suite-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        for file in [
            "good/tutorial/001_a.ndjson",
            "good/init-prelude.ndjson",
            "bad/tutorial/002_b.ndjson",
            "bad/notes.txt",
            "other/x.ndjson",
        ] {
            let path = dir.join(file);
            std::fs::create_dir_all(path.parent().expect("parent")).expect("create dir");
            std::fs::write(&path, "").expect("write test");
        }
        dir
    }

    #[test]
    fn the_layout_gives_the_name_and_the_outcome() {
        let dir = tree();
        let tests = discover(std::slice::from_ref(&dir)).expect("discover");
        let found: Vec<(&str, Outcome)> =
            tests.iter().map(|t| (t.name.as_str(), t.outcome)).collect();
        assert_eq!(
            found,
            [
                ("init-prelude", Outcome::Accept),
                ("other/x", Outcome::Unknown),
                ("tutorial/001_a", Outcome::Accept),
                ("tutorial/002_b", Outcome::Reject),
            ]
        );
        let good = discover(&[dir.join("good")]).expect("discover good");
        assert!(good.iter().all(|t| t.outcome == Outcome::Accept));
        assert_eq!(good[1].name, "tutorial/001_a");
        let one = discover(&[dir.join("bad/tutorial/002_b.ndjson")]).expect("discover file");
        assert_eq!(one[0].name, "002_b");
        std::fs::remove_dir_all(&dir).expect("clean up");
    }
}
