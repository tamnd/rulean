//! The dependency rule of spec section 03.3.
//!
//! 1. Each crate names its layer in `[package.metadata.rulean]`.
//! 2. A core crate has normal and build dependencies only on other core crates.
//! 3. A core crate starts with `#![no_std]`, so that it uses only `core` and `alloc`.
//!
//! Dev dependencies of a core crate are allowed, because they do not go into the checker.

use std::collections::BTreeMap;

use crate::metadata::{self, Layer, Member};

pub fn run() -> Result<(), Vec<String>> {
    let members = metadata::members()?;
    let problems = check(&members, |path| std::fs::read_to_string(path).ok());
    if problems.is_empty() {
        println!("deps: {} crates follow the dependency rule", members.len());
        Ok(())
    } else {
        Err(problems)
    }
}

/// Returns one line for each break of the rule. `read` gives the text of a source file.
pub fn check(members: &[Member], read: impl Fn(&std::path::Path) -> Option<String>) -> Vec<String> {
    let layers: BTreeMap<&str, Option<Layer>> =
        members.iter().map(|m| (m.name.as_str(), m.layer)).collect();
    let mut problems = Vec::new();
    for m in members {
        match (&m.layer, &m.layer_text) {
            (Some(_), _) => {}
            (None, None) => problems.push(format!(
                "{}: no layer in [package.metadata.rulean] of {}",
                m.name,
                m.manifest.display()
            )),
            (None, Some(text)) => problems.push(format!("{}: unknown layer `{text}`", m.name)),
        }
        if m.layer != Some(Layer::Core) {
            continue;
        }
        for d in &m.deps {
            if d.kind.as_deref() == Some("dev") {
                continue;
            }
            match layers.get(d.name.as_str()) {
                Some(Some(Layer::Core)) => {}
                _ => problems.push(format!(
                    "{}: a core crate depends on `{}`, which is not a core crate",
                    m.name, d.name
                )),
            }
        }
        match m.lib_root.as_deref().and_then(&read) {
            Some(text) if declares_no_std(&text) => {}
            Some(_) => problems.push(format!("{}: a core crate must declare #![no_std]", m.name)),
            None => problems.push(format!("{}: cannot read the library root", m.name)),
        }
    }
    problems
}

fn declares_no_std(text: &str) -> bool {
    text.lines().any(|line| line.trim() == "#![no_std]")
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;
    use crate::metadata::Dep;

    fn member(name: &str, layer: Option<Layer>, deps: &[(&str, Option<&str>)]) -> Member {
        Member {
            name: name.to_owned(),
            layer,
            layer_text: layer.map(|_| "set".to_owned()),
            manifest: PathBuf::from(format!("{name}/Cargo.toml")),
            lib_root: Some(PathBuf::from(format!("{name}/src/lib.rs"))),
            deps: deps
                .iter()
                .map(|(n, k)| Dep {
                    name: (*n).to_owned(),
                    kind: k.map(str::to_owned),
                })
                .collect(),
        }
    }

    fn no_std_everywhere(_: &std::path::Path) -> Option<String> {
        Some("//! doc\n\n#![no_std]\n".to_owned())
    }

    #[test]
    fn core_on_core_is_allowed() {
        let ms = [
            member("a", Some(Layer::Core), &[("b", None)]),
            member("b", Some(Layer::Core), &[]),
        ];
        assert!(check(&ms, no_std_everywhere).is_empty());
    }

    #[test]
    fn core_on_an_outside_crate_is_a_problem() {
        let ms = [member("a", Some(Layer::Core), &[("hashbrown", None)])];
        let problems = check(&ms, no_std_everywhere);
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("hashbrown"));
    }

    #[test]
    fn core_on_an_island_is_a_problem() {
        let ms = [
            member("a", Some(Layer::Core), &[("pool", Some("build"))]),
            member("pool", Some(Layer::Island), &[]),
        ];
        assert_eq!(check(&ms, no_std_everywhere).len(), 1);
    }

    #[test]
    fn dev_dependencies_of_core_are_allowed() {
        let ms = [member("a", Some(Layer::Core), &[("proptest", Some("dev"))])];
        assert!(check(&ms, no_std_everywhere).is_empty());
    }

    #[test]
    fn a_tool_can_depend_on_anything() {
        let ms = [member("t", Some(Layer::Tool), &[("serde_json", None)])];
        assert!(check(&ms, no_std_everywhere).is_empty());
    }

    #[test]
    fn a_missing_layer_is_a_problem() {
        let ms = [member("x", None, &[])];
        assert_eq!(check(&ms, no_std_everywhere).len(), 1);
    }

    #[test]
    fn core_without_no_std_is_a_problem() {
        let ms = [member("a", Some(Layer::Core), &[])];
        let problems = check(&ms, |_| Some("//! doc\n".to_owned()));
        assert_eq!(problems.len(), 1);
        assert!(problems[0].contains("no_std"));
    }
}
