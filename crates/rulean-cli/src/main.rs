//! The `rulean` command line.
//!
//! The commands and the exit codes follow section 09 of the specification. A command that is not written yet exits with code 2 (decline) and names the milestone that adds it, so that a caller never reads it as an accept.

use std::process::ExitCode;

mod check;
mod exit;
mod report;

use exit::Code;

const USAGE: &str = "\
usage: rulean <command> [options]

commands:
  check <INPUT>     check an export (.ndjson or \"-\" for standard input)
                    --profile <id>: the semantics profile, from the input by default
                    --report <file>: write the JSON report
                    --format text|json: the format of standard output
                    --trust-primitives-by-name: keep the extensions on a pin mismatch
                    --parse-only: parse the export and check nothing
  version           print the version and the build facts
  help              print this text

See docs/spec/09-integration.md for the full command line.";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    run(&args).into()
}

fn run(args: &[String]) -> Code {
    let Some(command) = args.first() else {
        eprintln!("{USAGE}");
        return Code::Usage;
    };
    match command.as_str() {
        "help" | "-h" | "--help" => {
            println!("{USAGE}");
            Code::Accept
        }
        "version" | "-V" | "--version" => {
            println!("{}", version_text());
            Code::Accept
        }
        "check" => check::run(&args[1..]),
        "olean" => not_written("olean", "M4"),
        "pack" => not_written("pack", "M4"),
        "diff" => not_written("diff", "M3"),
        "explain" => not_written("explain", "M3"),
        other => {
            eprintln!("rulean: unknown command `{other}`\n\n{USAGE}");
            Code::Usage
        }
    }
}

fn not_written(command: &str, milestone: &str) -> Code {
    eprintln!("rulean: the `{command}` command is not written yet. Milestone {milestone} adds it.");
    Code::Decline
}

fn version_text() -> String {
    let mut ids = Vec::new();
    for p in rulean_core::profile::PROFILES {
        ids.push(p.id());
    }
    format!(
        "rulean {}\nprofiles: {}\nbuild: unverified",
        env!("CARGO_PKG_VERSION"),
        ids.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_strs(args: &[&str]) -> Code {
        let owned: Vec<String> = args.iter().map(|s| (*s).to_owned()).collect();
        run(&owned)
    }

    #[test]
    fn no_arguments_is_a_usage_error() {
        assert_eq!(run_strs(&[]), Code::Usage);
    }

    #[test]
    fn unknown_command_is_a_usage_error() {
        assert_eq!(run_strs(&["frobnicate"]), Code::Usage);
    }

    #[test]
    fn help_and_version_succeed() {
        assert_eq!(run_strs(&["help"]), Code::Accept);
        assert_eq!(run_strs(&["version"]), Code::Accept);
    }

    #[test]
    fn commands_that_are_not_written_decline() {
        assert_eq!(run_strs(&["check"]), Code::Usage);
        assert_eq!(run_strs(&["check", "no-such-file.ndjson"]), Code::Input);
        for command in ["olean", "pack", "diff", "explain"] {
            assert_eq!(run_strs(&[command]), Code::Decline, "{command}");
        }
    }

    #[test]
    fn version_names_the_package_version() {
        let t = version_text();
        assert!(t.starts_with(&format!("rulean {}", env!("CARGO_PKG_VERSION"))));
        assert!(t.contains("profiles: v4.35"));
    }
}
