# Changelog

All changes that a user can see are in this file. The format follows Keep a Changelog, and the versions follow Semantic Versioning. Before 1.0, a minor version closes a milestone of `docs/spec/14-milestones.md` and a patch version is a step inside a milestone.

## [Unreleased]

### Added

- `rulean-io` is the island of contract K2 (spec 10.7). It opens the input read-only and reads it in blocks of 1 MiB. `rulean check`, `rulean pack` and `rulean explain` read the input through it. After the run, `rulean check` and `rulean pack` read the file again and compare the SHA-256 digests. If the file changed, `rulean check` gives exit code 4 and no verdict, and `rulean pack` writes no file. The second read costs 1.5 s and 29 G instructions on the 584 MB export of Std, about 7% of the check. Standard input and a pipe cannot be read again, so the check does not apply to them.
- `proof/RuleanProof/Contracts.lean` states contract K2 as `ReadsAs`. The field `K2` of `Interface` is still a free proposition.

## [0.0.4] - 2026-11-22

### Added

- `rulean check` checks an export with engine R. It reads the export, selects the semantics profile from the `lean.version` field of the meta line or from `--profile`, and checks the declarations in input order. It stops at the first declaration that is not accepted. The exit code follows spec 09.3: 0 for accept, 1 for reject, 2 for decline, 3 for a resource limit and 4 for a malformed input. An export from a Lean version with no profile declines with `unsupported-version`.
- `rulean check --report FILE` writes the JSON report of spec 09.4, and `--format json` writes the report to standard output. The report has the SHA-256 of the input, the profile, the verdict, the counts, the deviations, the quarantine array of spec 05.10 and the pin mismatch array. The schema is in `docs/report.schema.json`.
- `rulean check --trust-primitives-by-name` keeps the literal extensions on when a pin digest is not equal to its reference.
- `rulean-core` has the semantics profiles of spec 05.2. This version has only the `v4.35` profile, for Lean v4.35.0, v4.36.0 and the v4.36.x releases. `rulean version` lists the profiles.
- `rulean-format` has `parse_export`, which gives the declarations and the `lean.version` and `format.version` fields of the meta line.
- `scripts/arena-run.sh` is the entry of rulean in the Lean Kernel Arena. It runs `rulean check --profile v4.35` and maps the exit codes of spec 09.3 to the three Arena codes. `docs/arena/rulean.yaml` is the draft of the Arena entry.
- `scripts/arena-check.sh` runs the Arena entry on every Arena test and compares each verdict with the expected verdict. `docs/arena/either-v4.35.tsv` pins the verdict of each "either" test for the `v4.35` profile to the verdict of the official kernel v4.35.0. The `arena` CI job runs the script. All 225 tests of the Arena tarball give the expected verdict.
- `scripts/arena-build.py` builds the exports of the Arena tests that are not in the Arena tarball, with lake and the `leanexport` binary of the Lean toolchain. It keeps only the exports with the hash of the results. The new `arena either` CI job builds the 30 "either" tests with the Lean v4.36.0 release and checks the verdicts. `scripts/arena-check.sh` reads the `either/` directory and does not run the 2 tests on which the official kernel timed out. The other 28 tests give the pinned verdict.
- `rulean-format` has `Stream`, a parse that takes the export one line at a time. `parse_export` uses it.
- `rulean-core` has `sha256::Hasher`, a SHA-256 digest that takes its input in parts.
- `rulean-core` has the value arena of engine F (spec 04.5), in the module `value`. It holds values, closures, environments, spines and unfolding slots in typed arrays with `u32` handles. Environments and spines are persistent lists, so a push copies nothing. `reset` clears the arena at the end of a declaration. Engine F does not use it yet.
- `rulean-core` has `eval`, `apply`, `force` and `quote` of engine F (spec 05.4.2 and 05.4.3), in the module `nbe`. `eval` does beta and zeta and makes a glued value for each definition. `force` gives the weak head normal form of a value: the `Nat` extension, delta, iota, the quotient rules and the projections. It unfolds a glued value once and keeps the result in its slot. K-like reduction and structure eta read the major premise back and use engine R. `quote` reads a glued value back in folded form. The checker does not use engine F yet.
- The checker error `ArenaFull` is a resource failure, with exit code 3.
- `rulean-core` has definitional equality of engine F on values (spec 05.4.4), in the module `conv`. It uses the quick checks, beta, delta, iota, the `Nat` extension, proof irrelevance, lazy delta on folded definitions, the same head with equal arguments and function eta. It keeps the pairs of values that are not equal for the current query, and does not compare them again. Proof irrelevance does not read a value back if the head of the value shows that the value is not a proof. Engine F answers a query first. An "equal" answer is final, except in the confirm set of spec 05.1, where engine R confirms it. A "not equal" answer, or a fault of engine F, makes engine R decide the query.
- The value arena of engine F has a limit of 2^22 nodes in each array, about 0.2 GiB (spec 04.9). At the limit, engine R decides each query of the rest of the declaration. On the Arena test `ite-taken-branch-bad`, engine F took more than 90 s and 3.2 GB before this limit, and now it takes the same time as engine R.
- `rulean check --engine F|R` selects the engine, and `--confirm default|all` selects the queries where engine R confirms engine F. In this version the default is `--engine R`, because engine F is new. The JSON report has the new `engine` object with the counts of engine F.
- `scripts/arena-confirm.sh` runs engine F with `--confirm all` on each Arena test and fails if engine R does not confirm an equality of engine F. The `arena` and `arena either` CI jobs run it.
- `rulean diff INPUT --against CMD` checks an export with rulean and with another checker, and compares the two verdicts (spec 11.3). It reads the exit codes of the other checker as the Arena does. It exits with 0 if the verdicts are the same and with 1 if they are different. It takes the check options, such as `--engine`. It does not yet compare the verdict of each declaration.
- `rulean explain INPUT DECL` checks an export up to the declaration DECL and prints the rule trace of DECL (spec 09.2). Each line is one rule that the checker applied: delta, iota, the quotient rules, the `Nat` extension, proof irrelevance, function eta, structure eta, the unit-like rule, the string literal rule, and the answers of engine F. The indent shows the depth of the checker, and the last lines give the count of each rule. The trace keeps at most 100000 events. It takes `--profile`, `--engine` and `--confirm`.
- The proof package has the reordering lemmas O1 to O5 of spec 05.7.3, in `Twin/Order.lean` and `Twin/Zeta.lean`. A twin of the conversion loop has the quick check, the head reduction without delta, lazy delta with heights, a cache of equal pairs and the congruence of applications. The main theorem, `convF_conv`, says that each answer of the order of engine F is also an answer of the official order with some fuel. `convF_agrees` says that if both orders give an answer, the answers are equal. `zeta_lazy` says that a lazy `let` gives the value of the official substitution for a closed value. The twin terms have no binders and no types, and the link to the Aeneas model of engine F is not done yet.
- `rulean check --axioms LIST` gives the axioms that a theorem can use (spec 09.2). LIST is `any`, `none`, or names and `std` with a comma between them, and `std` means `propext`, `Quot.sound` and `Classical.choice`. The default is `any`. If every declaration is accepted but a theorem uses an axiom outside the list, the verdict is `axiom-policy` with exit code 5. `rulean check --format text --axioms std` is the command for an external kernel of `lake comparator`, and lake adds the path of the export at the end (spec 09.5).
- `tests/lake` is a small Lean project, and `scripts/lake-comparator.sh` runs `lake comparator` on it with rulean as an external kernel. The script also requires exit code 5 from `--axioms std` on a theorem that uses `sorry`. The new `lake comparator` CI job runs the script with the `bwrap` sandbox of lake and the Lean v4.36.0 release.
- `rulean-core` has the module `axioms`. It computes the axioms of each constant as `#print axioms` does: an axiom gives itself, a definition or a theorem gives the axioms of the constants in its type and its value, and an inductive type also gives the axioms of its constructors. The members of an inductive group share their axioms. The JSON report has the new field `summary.axioms_used`, with the axioms that the accepted theorems use.
- The checker keeps a session: the results of `infer` in infer-only mode, `whnf_core`, `whnf`, the definitional equality successes and the unfoldings of constants with level arguments, on frozen terms without free variables, stay from one declaration to the next (spec 08.4). The entries of a declaration go into the session only if the declaration is accepted. A result in the scratch tier is first copied into the frozen tier, with at most 10% of the scratch nodes of the declaration. Each entry has the length of the environment as its stamp. The session has at most 128 MiB, with a CLOCK policy in buckets of 4 entries. The session is not used with `rulean explain` and with `--confirm all`. `rulean check --session off` turns it off. The JSON report has the new `session` object with its counts. On the Init export of the Arena (58547 declarations), engine R used 306.5 G instructions and now uses 266.3 G, and the parse is 72.5 G of this. On the std export, engine R used 494.0 G and now uses 437.1 G, and the peak memory went from 971 MB to 1108 MB.
- `rulean pack INPUT -o OUT.rlb` writes the binary format of spec 07.2 from an NDJSON export, and `rulean check` reads a `.rlb` file. It finds the format from the first 8 bytes of the input. The decoder is in `rulean-format`, in the module `rlb`. It reads the tables in one forward pass, checks each index, each pad and the CRC-32C of each section, and makes each node again with the constructors of the store. The encoder is in `rulean-pack`. The JSON report gives the format `rlb-1` for a binary input. On Init, the file has 85 MB and the NDJSON export has 348 MB, and the parse takes 9.8 G instructions and not 72.6 G. On Std, the file has 140 MB and not 584 MB, and the parse takes 17.0 G and not 121.3 G. A full check of Std from the `.rlb` file takes 334 G instructions and 49 s, and from the NDJSON export it takes 439 G instructions and 67 s. The decode takes about 115 instructions for each byte, so the target of 3 instructions for each byte in spec 07.2.3 is not met.

### Changed

- Engine F does not run on a query whose success is already in the success cache of the declaration or in the session. On the Init export, engine F with `--session off` used 1026.1 G instructions and now uses 977.6 G. With the session, it uses 950.6 G. Engine R is still much faster on this export, at 266.3 G, so engine R stays the default.
- Proof irrelevance in engine F does not read back a value whose head is a local of a type that is not a proposition, for example `f : α → α` with `α : Type`. On the Arena test `church-numerals`, engine F used 251.09 G instructions and now uses 0.05 G.
- Engine F keeps the result of the `Nat` extension in the unfolding slot of the glued value, so the next `force` of the value does not compute it again. On the Arena test `gf3-matrix-product`, engine F used 148.94 G instructions and now uses 109.55 G.
- Engine F keeps the pairs of values that it found equal for the current query, and does not compare them again (row O2 of spec 05.7.3). On the Arena test `repeated-subproblem`, engine F used 3.71 G instructions and now uses 0.02 G.
- Engine F keeps the result of `force` of a glued value or of a neutral application of a constant for the current declaration. A recursor application has no unfolding slot, so before this change each `force` of the same value did the iota steps again. On the Arena test `gf3-matrix-product`, engine F used 109.55 G instructions and now uses 67.57 G.
- The value arena of engine F has a limit of 2^18 nodes in each array, about 25 MiB. Before this change the limit was 2^22. When engine F fills the arena, engine R does the work again, so a smaller limit wastes less work. On the 42 Arena perf tests, engine F used 1537 G instructions in total and now uses 1326 G. Engine R alone uses 1142 G. On `grind-ring-5`, engine F used 121.19 G and now uses 27.89 G. 21 tests still use more than 6 G. Engine R alone uses more than 6 G on 19 of them and does not finish in 60 s on 1 of them (`magma-list-pair-n21`).
- `scripts/arena-build.py` builds the Arena tests with a `url` field, such as Mathlib. It fetches the pinned commit of the repository, runs the `pre-build` commands with bash, and exports the module with the `leanexport` binary of the toolchain of the repository. It reads the test files with PyYAML if it is installed. With `--check RULEAN`, it sends each export to `rulean check -` through a pipe and does not write the export to the disk. The con-leche test is accepted in this mode.
- Engine R checks axioms, definitions, theorems and opaque constants in the scratch tier of spec 04.8. The terms that the checker makes for one declaration go into a separate node array, and the checker clears that array after the declaration. Inductive and quotient declarations use the frozen tier. On the full Init prelude, the check now takes 54 s and 964 MB, and before this change it took 93 s and 3.45 GB. On Std, it now takes 60 s and 1.6 GB, and before this change it took 192 s and 4.55 GB.
- `rulean check` reads the export one line at a time, and computes the SHA-256 digest of the input at the same time. The input is not in memory as a whole, so the peak memory of a check is less by the size of the export. A check of standard input with `-` works the same way.
- `rulean check` without `--parse-only` checks the export with engine R. Before this change, it declined.
- The `arena parse` CI job is now the `arena` job. It also checks the verdicts of the Arena tests.

## [0.0.3] - 2026-11-22

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
- `rulean check --parse-only` parses an export into the term store and prints the counts, the store memory and the time. Without `--parse-only`, `check` still declines until M2. A parse reject exits with code 4, and a decline exits with code 2.
- `scripts/arena-parse.sh` runs `rulean check --parse-only` on every Arena test, and the new `arena parse` CI job runs it on the downloaded Arena.
- `rulean-core` has the inductive checks of spec 06.2, as a transcription of `add_inductive` in `inductive.cpp` of the official kernel v4.35.0: the type and constructor checks, the uniform parameter occurrences, strict positivity, the universe bound of the fields, the elimination level, the K flag and the recursor rules. The checker makes the recursors and compares the types, constructors and recursors of the export with its own declarations.
- `rulean-core` has the nested inductive types of spec 06.3, as a transcription of `elim_nested_inductive_fn` and `restore_nested` in `inductive.cpp` of the official kernel v4.35.0. The checker replaces each nested occurrence with an auxiliary type, checks the larger mutual block, and then restores the nested occurrences in the types, constructors and recursors. The export must have the auxiliary recursors with the names `I.rec_1`, `I.rec_2` and so on. All 225 Arena tests give the expected verdict, and the full Init prelude is accepted.
- `rulean-core` has the primitive pinning of spec 05.8. When the export declares a `Nat` operation, `Nat`, `String`, `String.ofList`, `Char`, `Char.ofNat`, `List` or `eagerReduce`, the checker compares the SHA-256 digest of the declaration with the digest of the reference declaration of the `v4.35` profile. If the digests are not equal, the extension of that name is off, and the constant unfolds like any other definition. This is deviation D1. `Checker::trust_primitives` keeps the extensions on, as the official kernel does. The `Checker::pin_mismatch` list gives the names that are not equal to their reference.
- `scripts/pin-digests.py` computes the reference digests from lean4export files. The `arena parse` CI job checks that the digests in `pin_ref_v4_35.in` are the digests of the Lean v4.36.0 exports of the Arena, and that engine R accepts the full Init prelude with no pin mismatch.
- `docs/deviations.json` is the deviation register of spec 05.12.

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

[Unreleased]: https://github.com/tamnd/rulean/compare/v0.0.4...HEAD
[0.0.4]: https://github.com/tamnd/rulean/compare/v0.0.3...v0.0.4
[0.0.3]: https://github.com/tamnd/rulean/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/tamnd/rulean/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/tamnd/rulean/releases/tag/v0.0.1
