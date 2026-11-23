//! Loads modules from `.olean` files and prints a summary. Usage: `olean_load DIR MODULE...`.

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: olean_load DIR MODULE...");
        std::process::exit(64);
    }
    let search = vec![std::path::PathBuf::from(&args[0])];
    let mut st = rulean_store::Store::new();
    let t = std::time::Instant::now();
    match rulean_olean::load(&mut st, &args[1..], &search) {
        Ok(l) => {
            let seen: std::collections::BTreeSet<_> = l.decls.iter().map(|d| d.name()).collect();
            println!("{} distinct names", seen.len());
            println!(
                "{} declarations, {} modules, {} files, {} objects, Lean {}, {:?}",
                l.decls.len(),
                l.modules.len(),
                l.files.len(),
                l.objects,
                String::from_utf8_lossy(&l.lean_version),
                t.elapsed()
            );
        }
        Err(e) => {
            eprintln!("error ({:?}): {e}", e.kind);
            std::process::exit(1);
        }
    }
}
