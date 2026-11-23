//! Loads modules from `.olean` files and checks them with engine R. Usage: `olean_check DIR MODULE...`.

use rulean_core::profile;
use rulean_core::tc::Checker;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: olean_check DIR MODULE...");
        std::process::exit(64);
    }
    let search = vec![std::path::PathBuf::from(&args[0])];
    let mut st = rulean_store::Store::new();
    let t = std::time::Instant::now();
    let l = match rulean_olean::load(&mut st, &args[1..], &search) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error ({:?}): {e}", e.kind);
            std::process::exit(1);
        }
    };
    let load = t.elapsed();
    let prof = profile::of_lean_version(&l.lean_version).expect("a profile for the Lean version");
    let mut c = Checker::new(st);
    c.flags = prof.flags();
    let mut ok = 0;
    for d in &l.decls {
        if let Some(f) = c.add_decl(d) {
            println!(
                "{}: {:?} after {ok} declarations",
                String::from_utf8_lossy(&c.st.name_text(d.name())),
                f.kind
            );
            std::process::exit(1);
        }
        ok += 1;
    }
    println!(
        "accept: {ok} declarations, load {load:?}, total {:?}",
        t.elapsed()
    );
}
