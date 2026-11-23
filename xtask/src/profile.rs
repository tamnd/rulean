//! The build-profile check of contracts K5 and K6 of spec 10.7.
//!
//! K5 needs `overflow-checks = true`, so that each overflow is a panic and not a wrap. K6 needs `panic = "abort"` and the system allocator, so that a failed allocation stops the process and no partial state is observable. The check reads the `[profile.release]` and `[profile.dev]` tables of the workspace `Cargo.toml`. It also fails on a setting that turns a contract off in another profile or in `.cargo/config.toml`, and on a `#[global_allocator]` in `crates/`.

use std::fs;
use std::path::Path;

use crate::metadata;

/// The settings that each of the two profiles must have.
const REQUIRED: &[(&str, &str)] = &[("panic", "\"abort\""), ("overflow-checks", "true")];

/// The profiles that must have the settings. `test` and `bench` inherit from `dev` and `release`.
const PROFILES: &[&str] = &["release", "dev"];

/// Settings that turn a contract off in any profile.
const FORBIDDEN: &[(&str, &str)] = &[("panic", "\"unwind\""), ("overflow-checks", "false")];

/// Runs the check from the workspace root.
pub fn run() -> Result<(), Vec<String>> {
    let root = metadata::workspace_root()?;
    let mut problems = Vec::new();
    let manifest = read(&root.join("Cargo.toml"), &mut problems);
    for profile in PROFILES {
        let table = format!("profile.{profile}");
        for (key, value) in REQUIRED {
            if setting(&manifest, &table, key).as_deref() != Some(*value) {
                problems.push(format!("Cargo.toml: [{table}] must have {key} = {value} (contracts K5 and K6, spec 10.7)"));
            }
        }
    }
    let config = root.join(".cargo/config.toml");
    let config_text = if config.exists() {
        read(&config, &mut problems)
    } else {
        String::new()
    };
    for (name, text) in [
        ("Cargo.toml", &manifest),
        (".cargo/config.toml", &config_text),
    ] {
        for (table, key, value) in settings(text) {
            if FORBIDDEN.iter().any(|(k, v)| *k == key && *v == value) {
                problems.push(format!("{name}: [{table}] has {key} = {value}, which turns off contract K5 or K6 (spec 10.7)"));
            }
        }
    }
    allocators(&root, &mut problems);
    if problems.is_empty() {
        println!(
            "profile: the release and dev profiles have panic = \"abort\" and overflow-checks = true, and no crate sets a global allocator"
        );
        Ok(())
    } else {
        Err(problems)
    }
}

fn read(path: &Path, problems: &mut Vec<String>) -> String {
    match fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) => {
            problems.push(format!("{}: {e}", path.display()));
            String::new()
        }
    }
}

/// The value of `key` in the table `table`, with the spaces and the comment removed.
fn setting(text: &str, table: &str, key: &str) -> Option<String> {
    settings(text)
        .into_iter()
        .filter(|(t, k, _)| t == table && k == key)
        .map(|(_, _, v)| v)
        .next_back()
}

/// Each `key = value` line of a TOML file, with the name of its table. The check needs only the simple form that the manifest uses, so it does not parse the full TOML grammar.
fn settings(text: &str) -> Vec<(String, String, String)> {
    let mut table = String::new();
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            table = name.trim().to_string();
        } else if let Some((key, value)) = line.split_once('=') {
            out.push((
                table.clone(),
                key.trim().to_string(),
                value.trim().to_string(),
            ));
        }
    }
    out
}

/// Fails on each Rust file of the crates of rulean that sets a global allocator, because K6 assumes the system allocator.
fn allocators(root: &Path, problems: &mut Vec<String>) {
    let mut stack = vec![root.join("crates")];
    while let Some(path) = stack.pop() {
        let Ok(entries) = fs::read_dir(&path) else {
            continue;
        };
        for entry in entries.flatten() {
            let p = entry.path();
            if p.is_dir() {
                if p.file_name().is_some_and(|n| n != "target") {
                    stack.push(p);
                }
            } else if p.extension().is_some_and(|e| e == "rs")
                && fs::read_to_string(&p).is_ok_and(|t| t.contains("#[global_allocator]"))
            {
                problems.push(format!("{}: sets a global allocator, and contract K6 assumes the system allocator (spec 10.7)", p.display()));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_setting_is_read_from_its_table() {
        let text = "[profile.release]\npanic = \"abort\" # K6\noverflow-checks = true\n[profile.dev]\npanic = \"unwind\"\n";
        assert_eq!(
            setting(text, "profile.release", "panic").as_deref(),
            Some("\"abort\"")
        );
        assert_eq!(
            setting(text, "profile.dev", "panic").as_deref(),
            Some("\"unwind\"")
        );
        assert_eq!(setting(text, "profile.dev", "overflow-checks"), None);
    }
}
