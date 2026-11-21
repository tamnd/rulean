//! Repository checks for rulean. Run them with `cargo xtask <command>`.

use std::process::ExitCode;

mod deps;
mod metadata;
mod nonc;
mod subset;

const USAGE: &str = "\
usage: cargo xtask <command>

commands:
  deps      check the dependency rule of spec 03.3
  nonc      check the no-C policy of spec 13.3 (add --vendor to scan the vendored sources)
  subset    check that the core crates stay in the Aeneas subset of spec 10.6
  all       run every check, with --vendor";

/// Runs every check and joins the problems, so that one run shows all of them.
fn all() -> Result<(), Vec<String>> {
    let mut problems = Vec::new();
    for check in [deps::run as fn() -> Result<(), Vec<String>>, || {
        nonc::run(true)
    }] {
        if let Err(p) = check() {
            problems.extend(p);
        }
    }
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems)
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let vendor = args.iter().any(|a| a == "--vendor");
    let result = match args.first().map(String::as_str) {
        Some("deps") => deps::run(),
        Some("nonc") => nonc::run(vendor),
        Some("subset") => subset::run(),
        Some("all") => all(),
        Some("help" | "-h" | "--help") => {
            println!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(64);
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(problems) => {
            for problem in &problems {
                eprintln!("error: {problem}");
            }
            eprintln!("{} problem(s)", problems.len());
            ExitCode::FAILURE
        }
    }
}
