//! The `explain` command (spec 09.2).
//!
//! `rulean explain INPUT DECL` checks the export up to the declaration DECL, and it writes the rule trace of the check of DECL. Each line of the trace is one rule that the checker applied: delta, iota, the quotient rules, the `Nat` extension, the type-directed rules of definitional equality, and the answers of engine F. The indent of a line shows the depth of the checker. At the end, the command writes the number of events of each rule.
//!
//! The exit code is the exit code of the check of DECL. If a declaration before DECL is not accepted, or if the export does not have DECL, the command gives an error.

use std::io::BufRead;

use rulean_core::tc::Checker;
use rulean_core::trace::{RULES, Rule, Trace};
use rulean_store::Store;

use crate::check::{self, Options};
use crate::exit::Code;

/// The largest indent of a trace line.
const MAX_INDENT: u32 = 40;

/// Reads the options of `explain`: the input, the declaration, and `--profile`, `--engine` and `--confirm`.
fn options(args: &[String]) -> Result<(Options, String), String> {
    let mut pass = Vec::new();
    let mut pos = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let takes = a == "--profile" || a == "--engine" || a == "--confirm";
        if takes {
            pass.push(a.clone());
            match it.next() {
                Some(v) => pass.push(v.clone()),
                None => return Err(format!("`{a}` needs a value")),
            }
        } else if a.starts_with("--profile=")
            || a.starts_with("--engine=")
            || a.starts_with("--confirm=")
        {
            pass.push(a.clone());
        } else if a.starts_with("--") {
            return Err(format!("unknown option `{a}`"));
        } else {
            pos.push(a.clone());
        }
    }
    if pos.len() != 2 {
        return Err("`explain` needs an input and a declaration name".to_owned());
    }
    pass.push(pos[0].clone());
    let o = check::options(&pass)?;
    Ok((o, pos[1].clone()))
}

/// Runs `explain` with the arguments after the command name.
pub fn run(args: &[String]) -> Code {
    let (o, decl) = match options(args) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("rulean explain: {e}");
            return Code::Usage;
        }
    };
    let path = o.input.clone().unwrap_or_default();
    let reader = match check::open_input(&path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("rulean explain: cannot read {path}: {e}");
            return Code::Input;
        }
    };
    let h = std::thread::Builder::new()
        .stack_size(check::STACK_BYTES)
        .spawn(move || explain_reader(&o, &decl, reader));
    let r = match h {
        Ok(h) => match h.join() {
            Ok(r) => r,
            Err(_) => {
                eprintln!("rulean explain: internal error: the checker thread stopped");
                return Code::Resource;
            }
        },
        Err(e) => {
            eprintln!("rulean explain: cannot start the checker thread: {e}");
            return Code::Resource;
        }
    };
    match r {
        Ok((code, text)) => {
            print!("{text}");
            code
        }
        Err((code, e)) => {
            eprintln!("rulean explain: {e}");
            code
        }
    }
}

/// Checks the export up to `decl` and gives the exit code and the trace text of `decl`.
fn explain_reader<R: BufRead>(
    o: &Options,
    decl: &str,
    input: R,
) -> Result<(Code, String), (Code, String)> {
    let mut store = Store::new();
    let parsed = match check::read_export(&mut store, input) {
        Ok((p, _)) => p,
        Err(e) => return Err((Code::Input, format!("cannot read the input: {e}"))),
    };
    let export = match parsed {
        Ok(x) => x,
        Err(e) => {
            return Err((
                check::code_of(e.kind),
                format!("line {}: {}", e.line, e.kind.text()),
            ));
        }
    };
    let prof = match check::select_profile(o, &export.lean_version) {
        Ok(p) => p,
        Err(e) => return Err((Code::Decline, e)),
    };
    let mut c = Checker::new(store);
    c.flags = prof.flags();
    c.trust_primitives = o.trust_primitives;
    c.engine = check::engine_of(o);
    c.confirm_all = o.confirm_all;
    for d in &export.decls {
        let n = check::name_text(&c, d.name());
        let target = n == decl;
        c.trace_on = target;
        let f = c.add_decl(d);
        if target {
            let (code, kind) = match f {
                Some(f) => (check::code_of_check(f.kind), Some(f.kind)),
                None => (Code::Accept, None),
            };
            let head = match kind {
                Some(k) => format!("reject: {n}: {k:?}"),
                None => format!("accept: {n}"),
            };
            return Ok((code, trace_text(&c, &head)));
        }
        if let Some(f) = f {
            return Err((
                check::code_of_check(f.kind),
                format!(
                    "the declaration {n} comes before {decl} and is not accepted: {:?}",
                    f.kind
                ),
            ));
        }
    }
    Err((Code::Usage, format!("the export has no declaration {decl}")))
}

/// The text of the trace of `c`, after the line `head`.
fn trace_text(c: &Checker, head: &str) -> String {
    let t: &Trace = &c.trace;
    let mut s = String::new();
    s.push_str(head);
    s.push('\n');
    let anon = c.st.anon();
    let mut total: u64 = 0;
    for n in &t.counts {
        total += n;
    }
    for e in &t.events {
        let indent = e.depth.min(MAX_INDENT);
        let mut i = 0;
        while i < indent {
            s.push_str("  ");
            i += 1;
        }
        s.push_str(e.rule.word());
        if e.name != anon {
            s.push(' ');
            s.push_str(&check::name_text(c, e.name));
        }
        s.push('\n');
    }
    if total > t.events.len() as u64 {
        s.push_str(&format!(
            "the trace has {total} events, and this text shows the first {}\n",
            t.events.len()
        ));
    }
    s.push_str("counts:\n");
    let mut i = 0;
    while i < RULES && i < t.counts.len() {
        let n = t.counts[i];
        if n > 0 {
            s.push_str(&format!("  {} {n}\n", Rule::of_index(i).word()));
        }
        i += 1;
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn options_need_an_input_and_a_declaration() {
        let (o, d) = options(&strs(&["x.ndjson", "Nat.add", "--profile", "v4.35"])).expect("valid");
        assert_eq!(o.input.as_deref(), Some("x.ndjson"));
        assert_eq!(o.profile.as_deref(), Some("v4.35"));
        assert_eq!(d, "Nat.add");
        let (o, _) = options(&strs(&["x", "d", "--engine=F", "--confirm", "all"])).expect("valid");
        assert!(o.engine_set && !o.engine_r && o.confirm_all);
        assert!(options(&strs(&["x"])).is_err());
        assert!(options(&strs(&["x", "d", "e"])).is_err());
        assert!(options(&strs(&["x", "d", "--report", "r.json"])).is_err());
        assert!(options(&strs(&["x", "d", "--profile"])).is_err());
    }
}
