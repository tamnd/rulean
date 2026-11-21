//! The `diff` command (spec 09.2 and 11.3).
//!
//! `rulean diff INPUT --against CMD` checks the export with rulean and runs the command CMD on the same export. Then it compares the two verdicts. The command reads the exit codes of CMD as the Arena does: 0 is accept, 1 is reject, and each other code is "no verdict".
//!
//! CMD is a shell command. The command gives the path of the export to CMD as the shell parameter `$1`. If CMD has the text `{}`, `{}` is replaced with `"$1"`. If not, `"$1"` is added at the end. So the path is never part of the shell text.
//!
//! This version compares the verdicts of the whole export. It does not yet bisect a rejected export to compare the verdict of each declaration (spec 11.3.1).

use std::process::Command;

use crate::check::{self, Options};
use crate::exit::Code;

/// The verdict of a checker on an export.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Accept,
    Reject,
    /// No verdict: a decline, a resource limit or an error of the checker.
    None,
}

impl Verdict {
    fn word(self) -> &'static str {
        match self {
            Verdict::Accept => "accept",
            Verdict::Reject => "reject",
            Verdict::None => "no verdict",
        }
    }
}

/// The verdict of an exit code of another checker, as the Arena reads it.
pub fn verdict_of_exit(code: Option<i32>) -> Verdict {
    match code {
        Some(0) => Verdict::Accept,
        Some(1) => Verdict::Reject,
        _ => Verdict::None,
    }
}

/// The verdict of a rulean exit code. An input error is a reject and the other codes are no verdict, as in `scripts/arena-run.sh`.
pub fn verdict_of_code(code: Code) -> Verdict {
    match code {
        Code::Accept => Verdict::Accept,
        Code::Reject | Code::Input | Code::AxiomPolicy => Verdict::Reject,
        _ => Verdict::None,
    }
}

/// The shell text that runs `cmd` on the path in `$1`.
pub fn shell_text(cmd: &str) -> String {
    if cmd.contains("{}") {
        cmd.replace("{}", "\"$1\"")
    } else {
        format!("{cmd} \"$1\"")
    }
}

/// Reads the options of `diff`: the input, `--against CMD`, and the options of `check`.
fn options(args: &[String]) -> Result<(Options, String), String> {
    let mut against = None;
    let mut rest = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--against" {
            match it.next() {
                Some(v) => against = Some(v.clone()),
                None => return Err("`--against` needs a value".to_owned()),
            }
        } else if let Some(v) = a.strip_prefix("--against=") {
            against = Some(v.to_owned());
        } else {
            rest.push(a.clone());
        }
    }
    let o = check::options(&rest)?;
    if o.parse_only || o.report.is_some() || o.json {
        return Err("`diff` takes only the check options of the checker".to_owned());
    }
    if o.input.as_deref() == Some("-") {
        return Err("`diff` reads the input two times, so the input must be a file".to_owned());
    }
    match against {
        Some(c) => Ok((o, c)),
        None => Err("no `--against` command".to_owned()),
    }
}

/// Runs `diff` with the arguments after the command name. The exit code is 0 if the verdicts are the same and 1 if they are different.
pub fn run(args: &[String]) -> Code {
    let (o, cmd) = match options(args) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("rulean diff: {e}");
            return Code::Usage;
        }
    };
    let path = o.input.clone().unwrap_or_default();
    let ours = match check::check_options(o) {
        Ok(r) => r.report,
        Err(code) => return code,
    };
    let status = Command::new("sh")
        .arg("-c")
        .arg(shell_text(&cmd))
        .arg("sh")
        .arg(&path)
        .status();
    let theirs = match status {
        Ok(s) => verdict_of_exit(s.code()),
        Err(e) => {
            eprintln!("rulean diff: cannot run the command: {e}");
            return Code::Usage;
        }
    };
    let mine = verdict_of_code(ours.code);
    let detail = match &ours.error {
        Some(e) => format!(" ({e})"),
        None => String::new(),
    };
    if mine == theirs {
        println!("same: {path}: {}{detail}", mine.word());
        Code::Accept
    } else {
        println!(
            "different: {path}: rulean {}{detail}, the other checker {}",
            mine.word(),
            theirs.word()
        );
        Code::Reject
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn exit_codes_are_read_as_the_arena_reads_them() {
        assert_eq!(verdict_of_exit(Some(0)), Verdict::Accept);
        assert_eq!(verdict_of_exit(Some(1)), Verdict::Reject);
        assert_eq!(verdict_of_exit(Some(2)), Verdict::None);
        assert_eq!(verdict_of_exit(None), Verdict::None);
        assert_eq!(verdict_of_code(Code::Input), Verdict::Reject);
        assert_eq!(verdict_of_code(Code::Resource), Verdict::None);
    }

    #[test]
    fn the_path_is_a_shell_parameter() {
        assert_eq!(
            shell_text("leanchecker --from-export"),
            "leanchecker --from-export \"$1\""
        );
        assert_eq!(shell_text("k {} --fast"), "k \"$1\" --fast");
    }

    #[test]
    fn options_need_a_command_and_a_file() {
        let (o, c) = options(&strs(&["x.ndjson", "--against", "true"])).expect("valid");
        assert_eq!(o.input.as_deref(), Some("x.ndjson"));
        assert_eq!(c, "true");
        let (o, _) = options(&strs(&["--against=k", "x", "--engine", "F"])).expect("valid");
        assert!(o.engine_set);
        assert!(options(&strs(&["x"])).is_err());
        assert!(options(&strs(&["-", "--against", "k"])).is_err());
        assert!(options(&strs(&["x", "--against", "k", "--parse-only"])).is_err());
    }
}
