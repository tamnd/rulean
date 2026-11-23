# Soundness

This file tells what the proofs of rulean say, what you must trust, and which soundness bugs were found. The full text is in spec 10 (`docs/spec/10-formal-verification.md`). If this file and the spec do not agree, the spec is correct, and this file has a bug.

A soundness bug is a run that accepts an input that has a declaration that is not correct in Lean's logic. A run that rejects a correct input is a completeness bug, and a different verdict from the official kernel is a parity bug. Spec 05.12 and `DEVIATIONS.md` list the known differences from the official kernel.

## The theorems

The statements are in one file, `proof/RuleanProof/Statements.lean`, so that a person can read all of them in one place.

| ID | Name | What it says | Needed for 1.0 |
|---|---|---|---|
| T1 | model existence | If rulean accepts a byte stream, then the stream parses to a list of declarations, and the environment of these declarations has a model in set theory with ω inaccessible cardinals. | yes |
| T2 | no proof of `False` | If rulean accepts a stream, then no constant of the safe tier is a proof of `False` that uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. | yes |
| T3 | quarantine | No constant of the safe tier uses a constant of the quarantine tier, directly or through other constants. | yes |
| T4 | report fidelity | For each accepted theorem, the list of axioms in the report is the set of axioms that the theorem uses. | yes |
| T5 | parallel determinism | The verdict and the report do not change with the thread count or the schedule of the threads. | yes |
| T6 | relative completeness | If lean4lean accepts each declaration within some fuel, and the run stays within the resource limits for that fuel, then rulean accepts the input. | no |

The theorems do not say these things:

- They do not say that rulean stops. A run that does not stop does not accept. The CLI has a limit on the wall time.
- They do not say that rulean accepts each input that the official kernel accepts. That is the parity promise P2, and tests check it (spec 11).
- They do not cover the `.olean` reader. The `.olean` format has no specification. The theorems are about the declarations that come out of the reader, and a comparison with the export path checks the reader (spec 07.3.6).
- They do not cover in-process mode, where the input comes from Lean objects in memory and not from a byte stream.

## Status

rulean is not at 1.0. The theorems T1 to T6 are not proved yet. This table gives the state of each part.

| Part | State |
|---|---|
| statements of T1 to T6 | drafts. Each theorem is a `Prop` over the structure `Interface`, which collects the objects that do not exist yet: the Aeneas model of `check_stream` and the specification of the input format. |
| set-theoretic model | `RuleanProof.Basic` links to `ConLeche.IsModel` of con-leche at a pinned commit. |
| reordering lemmas of engine F | O1 to O7 of spec 05.7.3 are proved on a twin with no binders and no types (`RuleanProof.Twin.Order` and `RuleanProof.Twin.Zeta`). Theorem R1 must still connect this twin to the Aeneas model of engine F. |
| contracts K1 to K6 | stated in `proof/RuleanProof/Contracts.lean`, each with one theorem. K1 and K2 are on the models of the two islands in `Statements.lean`. |
| Aeneas extraction | the CI job `extract` translates the core crates to Lean. The proofs about the extracted code are not written yet. |

The CI job `proof` builds the package, checks it with the official kernel, and fails on a declaration under `RuleanProof` that uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`. `scripts/proof-rules.sh` fails on `sorry`, `admit`, a new `axiom`, `native_decide`, `bv_decide` and `implemented_by`.

## What you must trust

The proofs make each part below a trusted part. If a part is wrong, the theorems do not apply to rulean.

| Part | Why you must trust it | What reduces the risk | State of the mitigation |
|---|---|---|---|
| the set theory of con-leche (`ConLeche.SetTheory`, ZF⁻ with ω universes) | A proof that a theory is consistent needs a stronger theory (Gödel's second theorem). | It is the standard assumption, the same as the ω inaccessible cardinals of Carneiro. Other people reviewed it. | in place |
| the statements in `Statements.lean` and the specification of the input format | A wrong statement proves the wrong thing. | They are in one file. Two people review them before each release. The statement is compared with `main_json_model` of con-leche. | The statements are drafts. No review and no comparison is done yet. |
| the Lean kernel that checks the proofs | It checks each proof in `proof/`. | rulean, nanoda and con-leche also check the export of `RuleanProof`. | The CI job `proof` checks the proofs with the official kernel. The CI job `proof-kernels` exports `RuleanProof` and its imports with lean4export, and checks the export with rulean, nanoda and con-leche (`scripts/proof-kernels.sh`). |
| Charon and Aeneas (Rust to LLBC to Lean) | No proof shows that the translation is correct. | The versions are pinned. The tools have their own papers (ICFP 2022, ICFP 2024). A test runs the extracted Lean model against the Rust binary on the Init corpus. | The versions are pinned in `flake.nix`. The test of the extracted model is planned. |
| the Aeneas models of `Vec`, integer operations and slices | People wrote these models by hand. | The core uses few of them (spec 10.6). Each model has a test that runs the model and the real function on random inputs. | `cargo xtask subset` keeps the core in the subset. The tests of the models are planned. |
| the contracts K1 to K6 | The islands are outside Aeneas. | See the next section. | See the next section. |
| rustc, LLVM, the Rust standard library, the system allocator and the operating system | No verified compiler exists for real Rust. | The toolchain is pinned, and `panic = "abort"` is set. Users can check an input with a second kernel that has none of these parts. | The toolchain and the profile are in place. `--paranoid` with a second kernel is planned. |
| the `.olean` reader | The format has no specification. | It is not in T1. The CI compares it with the export path, and the reader treats each input as hostile (spec 12). | The CI job `olean-xval` and the weekly corpus run compare the reader with the export path. The fuzz targets run each week. |

## The island contracts

An island is a part of rulean that Aeneas cannot translate. Each island has a contract in Lean, and something outside Lean discharges it.

| ID | Island | Contract | How it is discharged |
|---|---|---|---|
| K1 | `rulean-pool`, the thread pool | The array of results has the result of job `i` at position `i`, the same as the sequential twin. | A Verus proof of the pool (`proof/verus/pool.rs`) and a test of each claim order of at most 3 workers on at most 5 jobs. |
| K2 | `rulean-io`, the file read | The bytes that the core gets are the content of the file when it was opened. | Review. The report gives the SHA-256 digest of the bytes, and rulean reads the file again after the run and gives no verdict if the digest changed. |
| K3 | the store of the main checker during the parallel stage | A worker does not change the store that it reads. | The Rust type system and the subset lint: each worker gets the store through a shared reference, and the core crates have no type with interior mutability. |
| K4 | `rulean-simd`, the SIMD line scanner | The SIMD scanner gives the same result as the scanner of the core. | rulean has no SIMD scanner now, so the contract holds. |
| K5 | overflow | Each overflow is a panic and not a wrap. | `overflow-checks = true`. `cargo xtask profile` checks it in CI. |
| K6 | allocation failure | An allocation succeeds or the process stops, so no partial result is visible. | `panic = "abort"` and the system allocator. `cargo xtask profile` checks both in CI. |

## Known soundness bugs

No soundness bug is known in a release of rulean.

| Date | Versions | Bug | Fix | Postmortem |
|---|---|---|---|---|

Each soundness bug gets a CVE request, a regression test, a postmortem in the repository and a row in this table. To report a soundness bug, read `SECURITY.md`.
