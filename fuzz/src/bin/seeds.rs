//! Writes the seed inputs of the `olean` target: the parts of `Init.Control.Do` of each fixture release of `rulean-olean`, in the layout of `src/lib.rs`.
//!
//! Usage: `cargo run --bin seeds -- DIR`. The files go to `DIR`.

use std::path::{Path, PathBuf};

fn main() {
    let Some(out) = std::env::args().nth(1).map(PathBuf::from) else {
        eprintln!("usage: seeds DIR");
        std::process::exit(64);
    };
    std::fs::create_dir_all(&out).expect("cannot make the output directory");
    let fixtures =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../crates/rulean-olean/tests/fixtures");
    let mut n = 0;
    for release in ["v4.36.0", "v4.37.0-rc1"] {
        let base = fixtures.join(release).join("Init/Control/Do");
        let parts = ["olean", "olean.server", "olean.private"]
            .map(|x| std::fs::read(base.with_extension(x)).ok());
        // The full module, and the public part alone.
        let public = [parts[0].clone(), None, None];
        for (name, p) in [("full", &parts), ("public", &public)] {
            std::fs::write(out.join(format!("{release}-{name}")), rulean_fuzz::join(p))
                .expect("cannot write a seed");
            n += 1;
        }
    }
    println!("seeds: {n} files in {}", out.display());
}
