//! Repository checks for rulean. Run them with `cargo xtask <command>`.

use std::process::ExitCode;

mod deps;
mod metadata;

const USAGE: &str = "\
usage: cargo xtask <command>

commands:
  deps      check the dependency rule of spec 03.3
  all       run every check";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("deps") => deps::run(),
        Some("all") => deps::run(),
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
