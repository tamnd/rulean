//! The `rulean` command line.
//!
//! The commands and the exit codes follow section 09 of the specification.

use std::process::ExitCode;

mod check;
mod diff;
mod exit;
mod explain;
mod limits;
mod olean;
mod pack;
mod report;

use exit::Code;

const USAGE: &str = "\
usage: rulean <command> [options]

commands:
  check <INPUT>     check an export (.ndjson, .rlb or \"-\" for standard input)
                    --profile <id>: the semantics profile, from the input by default
                    --report <file>: write the JSON report
                    --format text|json: the format of standard output
                    --trust-primitives-by-name: keep the extensions on a pin mismatch
                    --engine F|R: engine F first, or engine R only (R by default for now)
                    --confirm default|all: the queries where engine R confirms engine F
                    --parse-only: parse the export and check nothing
                    --max-memory <size>|none: the memory limit, for example 8G
                    (0.8 times the physical memory by default)
                    --timeout <time>: the wall time limit, for example 90s or 2h
  diff <INPUT> --against <CMD>
                    check an export with rulean and with the command CMD, and
                    compare the verdicts (exit 0 if they are the same, 1 if not)
  explain <INPUT> <DECL>
                    check an export up to the declaration DECL and print the
                    rules that the checker applies to DECL (takes --profile,
                    --engine and --confirm)
  olean <MODULE>... check modules and their imports from .olean files
                    --path <dir>: a directory of the search path, more than one
                    is allowed (LEAN_PATH by default); takes the options of check
  pack <INPUT> -o <OUT.rlb>
                    write the binary format of an NDJSON export, which
                    `check` reads with less parse work
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
        "olean" => olean::run(&args[1..]),
        "pack" => pack::run(&args[1..]),
        "diff" => diff::run(&args[1..]),
        "explain" => explain::run(&args[1..]),
        other => {
            eprintln!("rulean: unknown command `{other}`\n\n{USAGE}");
            Code::Usage
        }
    }
}

fn version_text() -> String {
    let mut ids = Vec::new();
    for p in rulean_core::profile::PROFILES {
        ids.push(p.id());
    }
    format!(
        "rulean {}\nprofiles: {}\nhandles: {}-bit\nsha256: {}\nbuild: unverified",
        env!("CARGO_PKG_VERSION"),
        ids.join(", "),
        rulean_store::Raw::BITS,
        if rulean_io::sha::Sha256::new().hardware() {
            "the SHA instructions of the CPU"
        } else {
            "portable"
        }
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
    fn commands_check_their_arguments() {
        assert_eq!(run_strs(&["check"]), Code::Usage);
        assert_eq!(run_strs(&["check", "no-such-file.ndjson"]), Code::Input);
        assert_eq!(run_strs(&["olean"]), Code::Usage);
        assert_eq!(
            run_strs(&["olean", "--path", "/no/such/rulean/dir", "No.Such.Module"]),
            Code::Input
        );
        assert_eq!(run_strs(&["pack"]), Code::Usage);
    }

    #[test]
    fn version_names_the_package_version() {
        let t = version_text();
        assert!(t.starts_with(&format!("rulean {}", env!("CARGO_PKG_VERSION"))));
        assert!(t.contains("profiles: v4.35"));
        assert!(t.contains(&format!("handles: {}-bit", rulean_store::Raw::BITS)));
    }
}
