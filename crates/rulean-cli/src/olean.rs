//! The `olean` command (spec 09.2): checks modules from `.olean` files (spec 07.3).
//!
//! The command loads the modules and their import closure with `rulean-olean`, and then checks the declarations as `check` does. It takes the options of `check`, and `--path DIR` for each directory of the search path. Without `--path`, the search path comes from `LEAN_PATH`, so `lake env rulean olean MODULE` uses the search path of the project.

use std::path::PathBuf;
use std::time::Instant;

use rulean_olean::FaultKind;
use rulean_store::Store;

use crate::check::{self, Options, Run, STACK_BYTES};
use crate::exit::Code;
use crate::report::Report;

/// Runs `olean` with the arguments after the command name.
pub fn run(args: &[String]) -> Code {
    let o = match check::parse(args, true) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("rulean olean: {e}");
            return Code::Usage;
        }
    };
    let search = search_path(&o, std::env::var("LEAN_PATH").ok().as_deref());
    if search.is_empty() {
        eprintln!("rulean olean: no search path. Give `--path DIR`, or set LEAN_PATH.");
        return Code::Usage;
    }
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || check_modules(&o, &search));
    match h {
        Ok(h) => match h.join() {
            Ok(Ok(r)) => check::finish(&r),
            Ok(Err(code)) => code,
            Err(_) => {
                eprintln!("rulean: internal error: the checker thread stopped");
                Code::Resource
            }
        },
        Err(e) => {
            eprintln!("rulean: cannot start the checker thread: {e}");
            Code::Resource
        }
    }
}

/// The directories of `--path`, or else the directories of `lean_path` (the value of `LEAN_PATH`, with `:` between the directories). An empty directory name is skipped.
fn search_path(o: &Options, lean_path: Option<&str>) -> Vec<PathBuf> {
    let dirs: Vec<&str> = if o.paths.is_empty() {
        lean_path
            .map(|p| p.split(':').collect())
            .unwrap_or_default()
    } else {
        o.paths.iter().map(String::as_str).collect()
    };
    dirs.into_iter()
        .filter(|d| !d.is_empty())
        .map(PathBuf::from)
        .collect()
}

/// The exit code of a loader error (spec 09.3). A file that is not on the search path or that cannot be read is an input error, as for `check`.
fn code_of(kind: FaultKind) -> Code {
    match kind {
        FaultKind::Decline => Code::Decline,
        FaultKind::StoreFull => Code::Resource,
        FaultKind::Malformed | FaultKind::Missing | FaultKind::Io => Code::Input,
    }
}

/// Loads and checks the modules. This runs on the checker thread. With `--parse-only`, it only loads the modules, prints the result and gives the exit code as the error.
fn check_modules(o: &Options, search: &[PathBuf]) -> Result<Run, Code> {
    let start = Instant::now();
    let mut store = Store::new();
    let mut rep = Report {
        input_path: o.modules.join(" "),
        format_version: "olean".to_owned(),
        ..Report::default()
    };
    let l = match rulean_olean::load(&mut store, &o.modules, search) {
        Ok(l) => l,
        Err(e) => {
            if o.parse_only {
                eprintln!("rulean: {e}");
                return Err(code_of(e.kind));
            }
            rep.code = code_of(e.kind);
            rep.error = Some(e.to_string());
            return Ok(check::done(o, rep, start));
        }
    };
    if o.parse_only {
        println!(
            "loaded {}: {} declarations, {} modules, {} files, {} objects, {} expression nodes, {} ms",
            rep.input_path,
            l.decls.len(),
            l.modules.len(),
            l.files.len(),
            l.objects,
            store.expr_total(),
            start.elapsed().as_millis()
        );
        return Err(Code::Accept);
    }
    rep.sha256 = check::hex(&l.sha256);
    let export = rulean_format::Export {
        decls: l.decls,
        lean_version: l.lean_version,
        format_version: format!("olean-{}", l.version).into_bytes(),
    };
    let mut r = check::check_export(o, store, export, rep, start);
    confirm(&l.files, &l.sha256, &mut r.report);
    Ok(r)
}

/// Reads the files again after the run (contract K2, spec 10.7). If a file changed, the report gets the input error and the verdict is not given.
fn confirm(files: &[PathBuf], start: &[u8; 32], rep: &mut Report) {
    match rulean_olean::digest(files) {
        Ok(end) if &end == start => {}
        Ok(end) => {
            rep.code = Code::Input;
            rep.error = Some(format!(
                "the input changed during the run, the SHA-256 at the end is {}",
                check::hex(&end)
            ));
        }
        Err(e) => {
            rep.code = Code::Input;
            rep.error = Some(format!("cannot read the input again after the run: {e}"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strs(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn olean_options() {
        let o = check::parse(
            &strs(&["--path", "a", "--path=b", "M.N", "P", "--threads", "2"]),
            true,
        )
        .expect("valid");
        assert_eq!(o.paths, strs(&["a", "b"]));
        assert_eq!(o.modules, strs(&["M.N", "P"]));
        assert_eq!(o.threads, 2);
        assert!(check::parse(&strs(&["--path", "a"]), true).is_err());
        assert!(check::parse(&strs(&["--path"]), true).is_err());
        // `check` does not take `--path`.
        assert!(check::parse(&strs(&["--path", "a", "x.ndjson"]), false).is_err());
    }

    #[test]
    fn the_search_path_comes_from_lean_path_without_path_options() {
        let o = check::parse(&strs(&["M"]), true).expect("valid");
        assert_eq!(
            search_path(&o, Some("/a::/b")),
            vec![PathBuf::from("/a"), PathBuf::from("/b")]
        );
        assert!(search_path(&o, None).is_empty());
        let o = check::parse(&strs(&["--path", "/c", "M"]), true).expect("valid");
        assert_eq!(search_path(&o, Some("/a")), vec![PathBuf::from("/c")]);
    }

    #[test]
    fn loader_errors_have_exit_codes() {
        assert_eq!(code_of(FaultKind::Decline), Code::Decline);
        assert_eq!(code_of(FaultKind::StoreFull), Code::Resource);
        assert_eq!(code_of(FaultKind::Malformed), Code::Input);
        assert_eq!(code_of(FaultKind::Missing), Code::Input);
    }
}
