//! The workspace facts that the checks need, read from `cargo metadata`.

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

/// The layer of a crate, as in spec section 03.2.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layer {
    /// The verified core. Only `core`, `alloc` and other core crates.
    Core,
    /// A small crate outside the Aeneas subset, with a contract.
    Island,
    /// Code outside the theorem that reads hostile input.
    Hardened,
    /// A tool that is not part of the checker.
    Tool,
}

impl Layer {
    fn parse(text: &str) -> Option<Layer> {
        match text {
            "core" => Some(Layer::Core),
            "island" => Some(Layer::Island),
            "hardened" => Some(Layer::Hardened),
            "tool" => Some(Layer::Tool),
            _ => None,
        }
    }
}

/// A dependency of a workspace crate.
#[derive(Debug)]
pub struct Dep {
    pub name: String,
    /// `None` for a normal dependency, `Some("dev")` or `Some("build")` for the others.
    pub kind: Option<String>,
}

/// A crate of the workspace.
#[derive(Debug)]
pub struct Member {
    pub name: String,
    pub layer: Option<Layer>,
    pub layer_text: Option<String>,
    pub manifest: PathBuf,
    pub lib_root: Option<PathBuf>,
    pub deps: Vec<Dep>,
}

/// A package of the resolved dependency graph, with the workspace members included.
#[derive(Debug)]
pub struct Package {
    pub name: String,
    pub version: String,
    /// The native library that the package links, from the `links` key of its manifest.
    pub links: Option<String>,
}

/// Reads the workspace members from `cargo metadata`.
pub fn members() -> Result<Vec<Member>, Vec<String>> {
    let json = cargo_metadata(&["--no-deps"])?;
    let packages = json["packages"].as_array().cloned().unwrap_or_default();
    Ok(packages.iter().map(member).collect())
}

/// Reads every package of the resolved graph, for all targets and all features.
pub fn resolved_packages() -> Result<Vec<Package>, Vec<String>> {
    let json = cargo_metadata(&["--all-features"])?;
    let packages = json["packages"].as_array().cloned().unwrap_or_default();
    Ok(packages
        .iter()
        .map(|p| Package {
            name: p["name"].as_str().unwrap_or_default().to_owned(),
            version: p["version"].as_str().unwrap_or_default().to_owned(),
            links: p["links"].as_str().map(str::to_owned),
        })
        .collect())
}

/// The root directory of the workspace.
pub fn workspace_root() -> Result<PathBuf, Vec<String>> {
    let json = cargo_metadata(&["--no-deps"])?;
    json["workspace_root"]
        .as_str()
        .map(PathBuf::from)
        .ok_or_else(|| vec!["cargo metadata gave no workspace_root".to_owned()])
}

fn cargo_metadata(extra: &[&str]) -> Result<Value, Vec<String>> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());
    let output = Command::new(cargo)
        .args(["metadata", "--format-version", "1", "--locked"])
        .args(extra)
        .output()
        .map_err(|e| vec![format!("cannot run cargo metadata: {e}")])?;
    if !output.status.success() {
        return Err(vec![format!(
            "cargo metadata failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )]);
    }
    serde_json::from_slice(&output.stdout)
        .map_err(|e| vec![format!("cargo metadata gave bad JSON: {e}")])
}

fn member(package: &Value) -> Member {
    let layer_text = package["metadata"]["rulean"]["layer"]
        .as_str()
        .map(str::to_owned);
    let lib_root = package["targets"].as_array().and_then(|targets| {
        targets
            .iter()
            .find(|t| {
                t["kind"]
                    .as_array()
                    .is_some_and(|k| k.iter().any(|k| k == "lib"))
            })
            .and_then(|t| t["src_path"].as_str())
            .map(PathBuf::from)
    });
    let deps = package["dependencies"]
        .as_array()
        .map(|deps| {
            deps.iter()
                .map(|d| Dep {
                    name: d["name"].as_str().unwrap_or_default().to_owned(),
                    kind: d["kind"].as_str().map(str::to_owned),
                })
                .collect()
        })
        .unwrap_or_default();
    Member {
        name: package["name"].as_str().unwrap_or_default().to_owned(),
        layer: layer_text.as_deref().and_then(Layer::parse),
        layer_text,
        manifest: PathBuf::from(package["manifest_path"].as_str().unwrap_or_default()),
        lib_root,
        deps,
    }
}
