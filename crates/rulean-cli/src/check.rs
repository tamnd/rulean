//! The `check` command (spec 09.2).
//!
//! Milestone M1 has only `--parse-only`. It reads the export into the term store and reports what it read, but it checks no declaration. Without `--parse-only`, the command declines until milestone M2.

use std::io::Read;
use std::time::Instant;

use rulean_format::ErrorKind;
use rulean_store::Store;

use crate::exit::Code;

/// The options of `check`.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Options {
    pub input: Option<String>,
    pub parse_only: bool,
}

/// Reads the options. The result is an error text for a usage error.
pub fn options(args: &[String]) -> Result<Options, String> {
    let mut o = Options::default();
    for a in args {
        match a.as_str() {
            "--parse-only" => o.parse_only = true,
            s if s.starts_with("--") => return Err(format!("unknown option `{s}`")),
            s => {
                if o.input.is_some() {
                    return Err(format!("a second input `{s}`"));
                }
                o.input = Some(s.to_owned());
            }
        }
    }
    if o.input.is_none() {
        return Err("no input".to_owned());
    }
    Ok(o)
}

/// Runs `check` with the arguments after the command name.
pub fn run(args: &[String]) -> Code {
    let o = match options(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("rulean check: {e}");
            return Code::Usage;
        }
    };
    if !o.parse_only {
        eprintln!(
            "rulean: the `check` command checks nothing yet. Milestone M2 adds the type checker. Use --parse-only to parse the input."
        );
        return Code::Decline;
    }
    let path = o.input.unwrap_or_default();
    let input = match read_input(&path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("rulean: cannot read {path}: {e}");
            return Code::Input;
        }
    };
    let start = Instant::now();
    let mut store = Store::new();
    match rulean_format::parse(&mut store, &input) {
        Ok(decls) => {
            let ms = start.elapsed().as_millis();
            let mem = store.memory();
            println!(
                "parsed {path}: {} declarations, {} expression nodes, {} names, {} levels, {} bytes of store, {ms} ms",
                decls.len(),
                store.expr_total(),
                store.name_count(),
                store.level_count(),
                mem.total()
            );
            Code::Accept
        }
        Err(e) => {
            eprintln!("rulean: {path}: line {}: {}", e.line, e.kind.text());
            code_of(e.kind)
        }
    }
}

/// The exit code of a parse error (spec 09.3).
pub fn code_of(kind: ErrorKind) -> Code {
    match kind {
        ErrorKind::StoreFull => Code::Resource,
        k if k.is_decline() => Code::Decline,
        _ => Code::Input,
    }
}

fn read_input(path: &str) -> std::io::Result<Vec<u8>> {
    if path == "-" {
        let mut b = Vec::new();
        std::io::stdin().lock().read_to_end(&mut b)?;
        Ok(b)
    } else {
        std::fs::read(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn option_rules() {
        let o = options(&strs(&["x.ndjson", "--parse-only"])).expect("valid");
        assert_eq!(o.input.as_deref(), Some("x.ndjson"));
        assert!(o.parse_only);
        assert!(options(&strs(&[])).is_err());
        assert!(options(&strs(&["a", "b"])).is_err());
        assert!(options(&strs(&["a", "--fast"])).is_err());
    }

    #[test]
    fn error_codes() {
        assert_eq!(code_of(ErrorKind::BadJson), Code::Input);
        assert_eq!(code_of(ErrorKind::UndefinedIndex), Code::Input);
        assert_eq!(code_of(ErrorKind::UnknownVersion), Code::Decline);
        assert_eq!(code_of(ErrorKind::IndexLimit), Code::Decline);
        assert_eq!(code_of(ErrorKind::StoreFull), Code::Resource);
    }
}
