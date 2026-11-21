//! The "no C/C++" policy of spec section 13.3.2.
//!
//! The check has three parts:
//!
//! 1. The resolved dependency graph has no crate that builds C or links a native library: no banned name and no `links` key.
//! 2. The rulean tree has no C, C++ or assembly source and no prebuilt native code.
//! 3. The vendored source of every dependency has none of these files either. `cargo vendor` writes the sources to a temporary directory.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::metadata;

/// Crates that build C, run a C build tool or link a C library. `deny.toml` bans the same list.
pub const BANNED: &[&str] = &[
    "cc",
    "cmake",
    "bindgen",
    "pkg-config",
    "vcpkg",
    "mimalloc",
    "libmimalloc-sys",
    "tikv-jemallocator",
    "tikv-jemalloc-sys",
    "jemallocator",
    "snmalloc-rs",
    "snmalloc-sys",
    "rpmalloc",
    "rpmalloc-sys",
    "rug",
    "gmp-mpfr-sys",
    "zstd-sys",
    "libz-sys",
    "openssl-sys",
    "ring",
];

/// Source files of C, C++, Objective-C and assembly.
const SOURCE_EXTENSIONS: &[&str] = &[
    "c", "cc", "cpp", "cxx", "c++", "h", "hh", "hpp", "hxx", "h++", "m", "mm", "s", "asm",
];

/// Prebuilt native code.
const PREBUILT_EXTENSIONS: &[&str] = &["o", "obj", "a", "lib", "so", "dylib", "dll"];

/// Directories of the rulean tree that the scan skips: build output, caches and version control.
const SKIP_DIRS: &[&str] = &["target", ".git", ".lake", "_tmp", "dist", "node_modules"];

pub fn run(vendor: bool) -> Result<(), Vec<String>> {
    let mut problems = Vec::new();
    let packages = metadata::resolved_packages()?;
    problems.extend(check_graph(&packages));
    let root = metadata::workspace_root()?;
    problems.extend(
        scan(&root, true)
            .into_iter()
            .map(|p| format!("rulean tree: {p}")),
    );
    if vendor {
        problems.extend(scan_vendored(&root)?);
    }
    if problems.is_empty() {
        let scope = if vendor {
            "the graph, the tree and the vendored sources"
        } else {
            "the graph and the tree"
        };
        println!("nonc: {} packages, no C or C++ in {scope}", packages.len());
        Ok(())
    } else {
        Err(problems)
    }
}

/// Checks the resolved graph for banned crates and for crates with a `links` key.
pub fn check_graph(packages: &[metadata::Package]) -> Vec<String> {
    let mut problems = Vec::new();
    for p in packages {
        if BANNED.contains(&p.name.as_str()) {
            problems.push(format!(
                "{} {}: banned crate (spec 13.3.1)",
                p.name, p.version
            ));
        }
        if let Some(links) = &p.links {
            problems.push(format!(
                "{} {}: links the native library `{links}` (spec 13.3.1)",
                p.name, p.version
            ));
        }
    }
    problems
}

/// Returns one line for each C, C++, assembly or prebuilt file under `root`.
pub fn scan(root: &Path, skip_build_dirs: bool) -> Vec<String> {
    let mut problems = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            problems.push(format!("cannot read {}", dir.display()));
            continue;
        };
        let mut entries: Vec<_> = entries.filter_map(Result::ok).collect();
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            let Ok(kind) = entry.file_type() else {
                continue;
            };
            if kind.is_dir() {
                let name = entry.file_name();
                if skip_build_dirs && SKIP_DIRS.iter().any(|s| name == *s) {
                    continue;
                }
                stack.push(path);
            } else if let Some(what) = classify(&path) {
                let shown = path.strip_prefix(root).unwrap_or(&path);
                problems.push(format!("{}: {what}", shown.display()));
            }
        }
    }
    problems
}

/// Says why a file breaks the policy, or `None` if it does not.
pub fn classify(path: &Path) -> Option<&'static str> {
    let ext = path.extension()?.to_str()?;
    // `.S` and `.s` are both assembly. The other extensions compare in lower case.
    let lower = ext.to_ascii_lowercase();
    if SOURCE_EXTENSIONS.contains(&lower.as_str()) {
        Some("C, C++ or assembly source")
    } else if PREBUILT_EXTENSIONS.contains(&lower.as_str()) {
        Some("prebuilt native code")
    } else {
        None
    }
}

fn scan_vendored(root: &Path) -> Result<Vec<String>, Vec<String>> {
    let dir = vendor_dir();
    let _ = std::fs::remove_dir_all(&dir);
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
    let output = Command::new(cargo)
        .current_dir(root)
        .args(["vendor", "--locked", "--versioned-dirs", "--quiet"])
        .arg(&dir)
        .output()
        .map_err(|e| vec![format!("cannot run cargo vendor: {e}")])?;
    if !output.status.success() {
        return Err(vec![format!(
            "cargo vendor failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )]);
    }
    let problems = if dir.exists() {
        scan(&dir, false)
            .into_iter()
            .map(|p| format!("vendored: {p}"))
            .collect()
    } else {
        Vec::new()
    };
    let _ = std::fs::remove_dir_all(&dir);
    Ok(problems)
}

fn vendor_dir() -> PathBuf {
    std::env::temp_dir().join(format!("rulean-vendor-{}", std::process::id()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metadata::Package;

    fn package(name: &str, links: Option<&str>) -> Package {
        Package {
            name: name.to_owned(),
            version: "1.0.0".to_owned(),
            links: links.map(str::to_owned),
        }
    }

    #[test]
    fn source_files_are_found() {
        for name in [
            "a.c", "b.cpp", "c.h", "d.S", "e.s", "f.asm", "g.HPP", "h.mm",
        ] {
            assert_eq!(
                classify(Path::new(name)),
                Some("C, C++ or assembly source"),
                "{name}"
            );
        }
    }

    #[test]
    fn prebuilt_files_are_found() {
        for name in ["a.o", "b.a", "c.lib", "d.so", "e.dylib", "f.dll", "g.obj"] {
            assert_eq!(
                classify(Path::new(name)),
                Some("prebuilt native code"),
                "{name}"
            );
        }
    }

    #[test]
    fn rust_and_text_files_pass() {
        for name in [
            "a.rs",
            "Cargo.toml",
            "README.md",
            "c",
            "x.lean",
            "y.json",
            "z.cs",
        ] {
            assert_eq!(classify(Path::new(name)), None, "{name}");
        }
    }

    #[test]
    fn banned_crates_and_links_are_problems() {
        let packages = [
            package("serde", None),
            package("cc", None),
            package("foo-sys", Some("foo")),
        ];
        let problems = check_graph(&packages);
        assert_eq!(problems.len(), 2);
        assert!(problems[0].starts_with("cc "));
        assert!(problems[1].contains("`foo`"));
    }

    #[test]
    fn the_ban_list_agrees_with_deny_toml() {
        let deny = include_str!("../../deny.toml");
        for name in BANNED {
            assert!(
                deny.contains(&format!("crate = \"{name}\"")),
                "{name} is not in deny.toml"
            );
        }
        let in_deny = deny.matches("{ crate = ").count();
        assert_eq!(
            in_deny,
            BANNED.len(),
            "deny.toml and BANNED have different lengths"
        );
    }

    #[test]
    fn scan_finds_a_planted_file_and_skips_target() {
        let dir = std::env::temp_dir().join(format!("rulean-scan-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).expect("create src");
        std::fs::create_dir_all(dir.join("target")).expect("create target");
        std::fs::write(dir.join("src/lib.rs"), "").expect("write lib.rs");
        std::fs::write(dir.join("src/shim.c"), "").expect("write shim.c");
        std::fs::write(dir.join("target/out.o"), "").expect("write out.o");
        let problems = scan(&dir, true);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].contains("shim.c"));
    }
}
