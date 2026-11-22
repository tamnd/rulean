//! The `pack` command (spec 09.2): writes the binary format of spec 07.2 from an NDJSON export.
//!
//! The binary file is a cache. `rulean check` reads it and checks what it decodes, so a wrong file can cause a reject but not a wrong accept.

use std::time::Instant;

use rulean_format::rlb;
use rulean_pack::{Source, encode};
use rulean_store::Store;

use crate::check::{code_of, error_text, open_input, read_export};
use crate::exit::Code;

/// The options of `pack`.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Options {
    pub input: Option<String>,
    pub output: Option<String>,
}

/// Reads the options. The result is an error text for a usage error.
pub fn options(args: &[String]) -> Result<Options, String> {
    let mut o = Options::default();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let a = a.as_str();
        if a == "-o" || a == "--output" {
            match it.next() {
                Some(v) => o.output = Some(v.clone()),
                None => return Err(format!("`{a}` needs a value")),
            }
        } else if let Some(v) = a.strip_prefix("--output=") {
            o.output = Some(v.to_owned());
        } else if a.starts_with("--") {
            return Err(format!("unknown option `{a}`"));
        } else if o.input.is_some() {
            return Err(format!("a second input `{a}`"));
        } else {
            o.input = Some(a.to_owned());
        }
    }
    if o.input.is_none() {
        return Err("no input".to_owned());
    }
    if o.output.is_none() {
        return Err("no output, use -o <OUT.rlb>".to_owned());
    }
    Ok(o)
}

/// Runs `pack` with the arguments after the command name.
pub fn run(args: &[String]) -> Code {
    let o = match options(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("rulean pack: {e}");
            return Code::Usage;
        }
    };
    let input = o.input.unwrap_or_default();
    let output = o.output.unwrap_or_default();
    match pack(&input, &output) {
        Ok(text) => {
            println!("{text}");
            Code::Accept
        }
        Err((code, e)) => {
            eprintln!("rulean pack: {e}");
            code
        }
    }
}

/// Parses `input` and writes the binary file `output`. The result is a line with the counts, or the exit code and an error text.
pub fn pack(input: &str, output: &str) -> Result<String, (Code, String)> {
    let start = Instant::now();
    let opened =
        open_input(input).map_err(|e| (Code::Input, format!("cannot read {input}: {e}")))?;
    let mut reader = opened.reader;
    let head = std::io::BufRead::fill_buf(&mut reader)
        .map_err(|e| (Code::Input, format!("cannot read {input}: {e}")))?;
    if rlb::is_binary(head) {
        return Err((Code::Usage, format!("{input} is a binary file already")));
    }
    let mut store = Store::new();
    let (parsed, digest) = read_export(&mut store, reader)
        .map_err(|e| (Code::Input, format!("cannot read {input}: {e}")))?;
    let export = parsed.map_err(|e| (code_of(e.kind), format!("{input}: {}", error_text(&e))))?;
    let src = Source {
        lean_version: export.lean_version.clone(),
        githash: Vec::new(),
        sha256: digest,
    };
    let (bytes, n) = encode(&store, &export.decls, &src).map_err(|e| (Code::Input, e))?;
    // Contract K2 (spec 10.7): the digest in the header must be the digest of the file as it is now.
    match rulean_io::confirm(&opened.source, &digest) {
        Ok(rulean_io::Confirm::Same | rulean_io::Confirm::NotAFile) => {}
        Ok(rulean_io::Confirm::Changed(_)) => {
            return Err((Code::Input, format!("{input} changed during the run")));
        }
        Err(e) => {
            return Err((Code::Input, format!("cannot read {input} again: {e}")));
        }
    }
    std::fs::write(output, &bytes)
        .map_err(|e| (Code::Usage, format!("cannot write {output}: {e}")))?;
    Ok(format!(
        "packed {input} into {output}: {} declarations, {} expressions, {} names, {} levels, {} strings, {} numbers, {} bytes, {} ms",
        n.decls,
        n.exprs,
        n.names,
        n.levels,
        n.strings,
        n.nats,
        bytes.len(),
        start.elapsed().as_millis()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn option_rules() {
        let o = options(&strs(&["a.ndjson", "-o", "a.rlb"])).expect("valid");
        assert_eq!(o.input.as_deref(), Some("a.ndjson"));
        assert_eq!(o.output.as_deref(), Some("a.rlb"));
        let o = options(&strs(&["--output=b.rlb", "b.ndjson"])).expect("valid");
        assert_eq!(o.output.as_deref(), Some("b.rlb"));
        assert!(options(&strs(&["a.ndjson"])).is_err());
        assert!(options(&strs(&["-o", "a.rlb"])).is_err());
        assert!(options(&strs(&["a", "b", "-o", "c"])).is_err());
        assert!(options(&strs(&["a", "-o"])).is_err());
        assert!(options(&strs(&["a", "-o", "c", "--fast"])).is_err());
    }

    #[test]
    fn a_missing_input_is_an_input_error() {
        let r = pack("no-such-file.ndjson", "out.rlb");
        assert_eq!(r.map_err(|e| e.0), Err(Code::Input));
    }

    #[test]
    fn check_reads_what_pack_writes() {
        let dir = std::env::temp_dir().join(format!("rulean-pack-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let src = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/axiom.ndjson");
        let out = dir.join("axiom.rlb");
        let out = out.to_str().expect("utf-8 path");
        pack(src, out).expect("pack");
        let o = check::options(&strs(&[out])).expect("valid");
        let r = check::check_options(o).expect("run");
        assert_eq!(r.report.code, Code::Accept);
        assert_eq!(r.report.format_version, "rlb-1");
        assert!(report_has_rlb(&r));
        let again = dir.join("again.rlb");
        let again = again.to_str().expect("utf-8 path");
        let e = pack(out, again).map_err(|e| e.0);
        assert_eq!(e, Err(Code::Usage));
        std::fs::remove_dir_all(&dir).ok();
    }

    fn report_has_rlb(r: &check::Run) -> bool {
        crate::report::json(&r.report).contains("\"format\": \"rlb-1\"")
    }
}
