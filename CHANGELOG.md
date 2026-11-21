# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning. Before 1.0, a minor version closes a milestone of `docs/spec/14-milestones.md` and a patch version is a step inside a milestone.

## [Unreleased]

### Added

- `rulean-nat` has the `Nat` type of spec 04.6 with the 15 kernel operations, `log2` and decimal conversion. Multiplication uses Karatsuba from 32 limbs, and division uses algorithm D of Knuth. The tests compare each operation with `num-bigint`.
- `rulean-store` has the term store of spec 04: `u32` handles with the kind in the handle, one node array for each kind, side records with the hash, the loose bound variable range and the flags, and hash-consing with an open-addressing table. It also interns strings, names, levels, level lists and natural number literals.
- `rulean-format` has the lean4export NDJSON 3.x parser of spec 07.1. It is a hand-written scanner that writes into the term store and returns the declaration stream of spec 04.7. It checks the input rules of 07.1.2: index tables with a defined bit, no duplicate keys or indices, strict integers, UTF-8 and surrogate pairs, `natVal` form and bound, and `mdata` stripping. All 225 Arena tests parse.
- `rulean-core` has the universe level functions of spec 05.6, as a transcription of `level.cpp` of the official kernel v4.35.0: `mk_max` and `mk_imax` with their simplifications, `normalize` with a cache for each level handle, `is_equivalent`, `is_geq`, `normalizes_to_zero`, `instantiate` and the name order of the kernel.
- `rulean-core` has the expression operations of engine R, as a transcription of `instantiate.cpp`, `abstract.cpp`, `expr.cpp` and `expr_eq_fn.cpp` of the official kernel v4.35.0: `instantiate`, `instantiate_rev`, `abstract_fvars`, `lift_loose_bvars`, `lower_loose_bvars`, `has_loose_bvar`, `instantiate_lparams`, the application spine functions, `head_beta`, `cheap_beta_reduce` and `expr_equal`. Each operation has a cache keyed by the node and the binder offset.
- `scripts/arena-fetch.sh` downloads the Arena tests and results and keeps only the tests whose export has the hash of the results.
- The `bench` workflow runs the official kernel of Lean v4.35.0 on the Arena tests each week and compares its instruction counts with the Arena numbers.
- `docs/bench/baseline.md` records the first baseline run. The verdicts match the Arena on all 225 tests. The cachegrind counts are not within 2% of the Arena counts, so the 2% limit applies only to `perf`.
- `rulean-core` has the environment and the type checker of engine R, as a transcription of `type_checker.cpp`, `inductive_reduce_rec` and `quot_reduce_rec` of the official kernel v4.35.0. The checker infers types in the infer-only mode and in the check mode, reduces terms to weak head normal form in the official order (beta, zeta, projections, recursors, quotients, the `Nat` extension and delta), and decides definitional equality with lazy delta reduction, eta, structure eta, proof irrelevance, unit-like types and the `Nat` and `String` literal extensions. An error is a sticky fault, and a depth bound stops deep recursion. The `Nat` operations check the size bound of 128 MiB.
- `rulean-core` has the declaration checks of spec 05.9 and 06.5, as a transcription of `environment.cpp` and `quot.cpp` of the official kernel v4.35.0: axioms, definitions, theorems, opaque constants, mutual blocks of unsafe or partial definitions and the quotient constants. An unsafe definition may refer to itself, and a safe declaration may not refer to an unsafe or partial constant. The first quotient declaration adds the four reference constants. Each exported quotient declaration must be equal to its reference constant. A rejected declaration does not change the environment.

### Changed

- The store hash of a `lam`, `pi` or `let` node does not mix the binder name or the binder info. This is the method of Lean. Alpha-equivalent terms now have equal hashes, so `expr_equal` can use the hash to reject unequal terms.

### Fixed

- The `extract` job failed on `rulean-nat`, because Aeneas binds its `Fuel` type to the Lean name `Nat`. The type now has the Lean name `BigNat` in the extracted code. The Rust name does not change.
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
