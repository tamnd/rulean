# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning. Before 1.0, a minor version closes a milestone of `docs/spec/14-milestones.md` and a patch version is a step inside a milestone.

## [Unreleased]

### Fixed

- `cargo xtask all` runs the subset check too. Before this change, the `policy` CI job did not check the Aeneas subset.

## [0.0.2] - 2026-11-21

### Added

- `flake.nix` pins Aeneas, Charon and the Rust nightly of Charon with one Aeneas commit.
- `scripts/extract.sh` translates the four crates of the verified core to Lean with Charon and Aeneas, and the `extract` CI job runs it on each PR.
- The Lean proof package in `proof/`, with con-leche pinned by commit. The `proof` CI job builds it, checks it with the official kernel and audits its axioms.
- `scripts/proof-rules.sh` checks the source rules of spec 10.9 on the Lean files.
- A draft of `proof/RuleanProof/Statements.lean` with the theorems T1 to T6 of spec 10.1, stated over an interface of the objects that later milestones add.
- `scripts/leanchecker.sh` checks the proof package and all of its imports with the official kernel.
- `rulean-bench run` runs a checker on each test of a corpus and records the instructions, the wall time, the CPU time and the peak memory in the format of the Arena. It counts instructions with `perf`, valgrind cachegrind or the macOS `time -l`.
- `rulean-bench compare` compares the instruction counts of two runs, or of a run and the Arena `results.json`.

### Changed

- The `extract` CI job keeps the Nix store in the Actions cache, so it does not build the Aeneas tools again on each run.

## [0.0.1] - 2026-11-21

### Added

- The `rulean` command line with `help` and `version`. The other commands of the spec exit with code 2 and name the milestone that adds them.
- The exit codes of spec section 09.3.
- CI on Linux (x86-64 and ARM), macOS and Windows, CodeQL, OpenSSF Scorecard, zizmor and Dependabot.
- A release workflow that builds the binaries, writes SHA-256 checksums and signs build provenance attestations.
- The specification in `docs/spec/`.
- The crates of spec section 03.3 as empty libraries. The four crates of the verified core are `no_std`.
- `cargo xtask deps`, which checks the dependency rule of spec section 03.3, and the `policy` CI job that runs it.
- `cargo xtask nonc`, which checks the no-C policy of spec section 13.3: no banned crate and no `links` key in the dependency graph, and no C, C++, assembly or prebuilt native file in the tree or in the vendored source of any dependency.
- `deny.toml` and a `cargo-deny` CI job for advisories, licences, sources and banned crates.
- `cargo xtask subset` checks that the core crates stay in the Aeneas subset of spec 10.6. `cargo xtask all` runs it.
- The core crates declare `#![forbid(unsafe_code)]`.

[Unreleased]: https://github.com/tamnd/rulean/compare/v0.0.2...HEAD
[0.0.2]: https://github.com/tamnd/rulean/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/tamnd/rulean/releases/tag/v0.0.1
