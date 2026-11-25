# 11. Conformance and testing

Promise P2 (verdict parity) is not a theorem (02.2). This document specifies the evidence for it: the corpus, the differential tests, fuzzing, mutation testing and adversarial testing. The same tests also give evidence for the parts of rulean that are outside theorem T1: the `.olean` reader, the in-process mode and the islands.

## 11.1 Test classes

| Class | Question | Oracle |
|---|---|---|
| conformance | does rulean give the official verdict? | the official kernel of the profile |
| cross-kernel | does rulean agree with other checkers? | nanoda, con-leche, con-ron, nano-lean, lean4lean |
| regression | does a bug that was fixed stay fixed? | the recorded verdict |
| adversarial | can a hostile input make rulean accept a false statement, crash, or hang? | soundness: no accepted proof of `False` under standard axioms |
| engine | do engines F and R agree on every query? | engine R |
| unit and property | do the store, the bignum, levels and the parser behave as specified? | the Lean twin, compiled; reference libraries |
| performance | 08.7 | budgets |

## 11.2 The conformance corpus

The corpus is the working meaning of "every Lean program" (02.2). It grows and never shrinks. Each entry has an export for each supported profile.

| Entry | Size | Source | Run |
|---|---|---|---|
| Lean core: Init, Std, Lean, Lake | Init 332 MB, Std 557 MB exports | Lean release | every pull request (Init, Std); nightly (all) |
| Batteries | | leanprover-community | nightly |
| Mathlib | 5.9 GB export, 112.1 M lines | Arena, Lean 4.36.0 | weekly (`corpus`) |
| CSLib | 2.3 GB export, 44.1 M lines | Arena, Lean 4.36.0 | weekly (`corpus`) |
| Cedar | 863 MB export, 15.9 M lines, uses `native_decide` | Arena, Lean 4.36.0 | weekly (`corpus`) |
| Navier-Stokes (OpenAI) | 1.5 GB export | Arena, Lean 4.34.0-rc2, which is out of scope (02.5) | none |
| con-leche's own export | 669 MB | Arena | nightly |
| FLT (Imperial, human-led) | | GitHub | weekly |
| FLT (Anthropic) | 37.8 GB export, 1,052,234 declarations | GitHub, `anthropics/fermats-last-theorem` at 6e837e75, Lean v4.33.1, which is out of scope (02.5, Q7 of 15.4) | weekly, on a large self-hosted machine (08.7.2) |
| RH project | about 17.5 M lines, about 1.06 M declarations | public archive, Lean v4.33.1, which is out of scope (02.5, Q7 of 15.4) | weekly, on a large self-hosted machine (08.7.2) |
| Arena tests | 265 tests: 145 accept, 90 reject, 30 either | Arena repo | every pull request |
| Lean test suite | `tests/lean/run`, `tests/lean` with kernel tests | lean4 repo | nightly |
| 2026 regression tests | the tests of each soundness PR (A§2.2, 06.8) | lean4 repo at v4.36.0 | every pull request |
| unsafe corpus | the above with `--export-unsafe` | own exports | weekly |
| rulean regressions and fuzz finds | grows | `tests/` | every pull request |

**Pass rule.** For each entry and each profile, the verdict of every declaration equals the verdict of the official kernel of that profile, except for rows of the deviation register (05.12). A release needs a 100% pass on every entry.

**Corpus run.** The weekly workflow `corpus` has one job for each of Mathlib, CSLib and Cedar. Each job makes the export again from the project at the commit of the Arena test, because the exports are too large for a cache entry. It runs `scripts/corpus.sh`, which has six steps: fetch, export, check, official, olean and compare. The step official runs the official kernel on the export for the full suite of 08.7.2. The step fetch does the pre-build step of the Arena test and then `lake build` of the module, as the Arena does. For Mathlib, the oleans come from `lake exe cache get`. For CSLib, the oleans of Mathlib come from the cache and the job builds the oleans of CSLib. For Cedar, the job builds all the oleans. It compares the SHA-256 digest of the new export with the digest of the Arena export, and it records a difference but does not fail. The job records the time and the peak memory of each step. A GitHub-hosted runner has 16 GB of memory, and each worker has its own copy of the store, so the default is one thread. On the Init export of v4.36.0 (348 MB), `rulean check` has a peak memory of 485 MB with one thread and 1.97 GB with four threads. A manual run can select one test with the input `test`, and with the input `steps` set to `olean` it does not run the steps check and official, so a test of the `.olean` reader takes less time.

## 11.3 Differential testing

### 11.3.1 Against the official kernel

- `rulean diff` runs the official `leanchecker --from-export` and rulean on the same export, and compares verdicts **per declaration**. The official checker stops at the first error, so for rejected inputs the tool bisects: it removes the failing declaration and its dependents and runs again.
- For the in-process mode, a dual-kernel Lean build calls both kernels on each `addDecl` and on each term function, and fails on any difference (09.6.5). `scripts/lean-build.sh --dual` makes this build. The static library of `rulean-ffi` then has the feature `dual`. Each exported symbol calls the C++ function with the suffix `_cpp` and then the rulean function, with new references to the same objects. `Kernel::compare_add` and `Kernel::compare_term` compare the two results. The verdicts must be the same, two exceptions must have the same constructor, and the two results of `isDefEq` must be the same. For an accepted inductive block, the types, the constructors and the recursors must be the same constants in the two environments. The terms of `whnf` and `check` are not compared, because the results of rulean have no `mdata`. `deterministicTimeout` and `interrupted` of the C++ kernel agree with each result of rulean, because rulean counts fewer heartbeats (D2) and reads the cancel token at other times. `interrupted` of rulean agrees with each result of the C++ kernel. If the results differ, the process writes the difference to the standard error and stops. Otherwise the result is the result of rulean. rulean finds the `_cpp` functions with `dlsym` when the program runs, so a test binary with the feature `dual` links without them.

### 11.3.2 Against other checkers

- The nightly run also checks the corpus with nanoda, con-leche, con-ron and nano-lean. A difference where rulean disagrees with the official kernel is a rulean bug. A difference where rulean agrees with the official kernel and another checker disagrees is reported to that checker's authors.
- This is how the 2026 bug hunt found bugs: one checker accepted and another rejected (A§2.2).

### 11.3.3 Arena corner cases

- The 30 "either" tests have no fixed answer in the Arena. rulean pins the answer per profile to the official verdict (05.2). For v4.35.0 and the nightly of 2026-11-14, the official verdicts differ on 8 of these tests (A§1.15). So the expected verdict file is per profile.
- Two corner cases time out on v4.35.0 at 60 s (eta-struct-major-and-no-whnf and eta-struct-major-no-whnf, A§1.15). For those, the expected outcome is "resource" for the official kernel. rulean's verdict is recorded as deviation D2 if it accepts. The official kernel of v4.37.0-rc1 accepts both tests, so they are pinned for the `v4.37` profile.
- For `v4.37`, the expected verdicts are the verdicts of `leanchecker --from-export` of v4.37.0-rc1 on the exports that Lean v4.36.0 makes (`docs/arena/either-v4.37.tsv`). The CI job `arena-either` runs that leanchecker on each run, so a wrong pin fails the job. The nightly of 2026-11-14 accepts the four `eta-unit-like-*` tests because of lean4#15372, which was reverted before v4.37.0-rc1, so v4.37 rejects them.

### 11.3.4 Engines F and R

- `--confirm=all` runs engine R on every query that engine F answers (05.1). The nightly run uses it on Init, Std and Mathlib.
- Any query where F says "equal" and R says "not equal" is a release blocker until it is understood. It is either a missing row in the confirm set, or a bug in R's transcription.

## 11.4 Unit and property tests

| Area | Method |
|---|---|
| store | property tests: interning is idempotent; equal handles mean equal structure; epoch clearing removes all scratch entries |
| bignum | differential tests against `num-bigint` and `malachite` for each of the 15 operations, on random sizes from 0 to 2^20 bits, plus edge cases (0, 2^64 − 1, 2^64, powers of two) |
| levels | the official `normalize`, `is_equivalent` and `is_geq` are compared with engine R's copy and with a brute-force evaluator over small level assignments |
| parser | round trip NDJSON → store → NDJSON; every Arena export parses; malformed-line corpus |
| extracted model | the Lean model that Aeneas produces is compiled and run against the Rust binary on Init (10.8, Charon/Aeneas row) |
| failure caches | engine R with and without the failure cache must give the same verdicts on the corpus (10.4.3) |

## 11.5 Fuzzing and mutation

### 11.5.1 Fuzzing

- **Byte fuzzing** with `cargo fuzz` (libFuzzer is C++, so it is used only in the test toolchain, never in the shipped build; `cargo-afl` or a pure-Rust fuzzer is an option). Targets: the NDJSON scanner, the `.rlb` decoder, the `.olean` reader. Goal: no panic, no hang beyond the limits, and no memory above the limits.
- **Grammar fuzzing.** A generator produces syntactically valid exports with random terms. Goal: no difference with the official kernel.
- **Type-directed fuzzing.** A generator produces well-typed declarations from small signatures, using a Lean elaborator to fill gaps. Then small edits are applied. Goal: no difference with the official kernel.

Fuzz runs take 100 CPU-hours each week. Every find becomes a regression test.

State of the fuzzing:

- Byte fuzzing has three targets in `fuzz/`: `olean`, `ndjson` and `rlb`. The workflow `fuzz` runs each target for 60 s on a pull request that changes the readers. Each week, it runs 2 shards of each target, and each shard runs 4 hours with 4 workers (libFuzzer `-fork=4`). This is 96 CPU-hours each week. The corpus of each shard is in the Actions cache, so each week starts from the corpus of the week before. The first weekly run with this budget is not done yet.
- The first local run of 10 minutes for each target found one fault in the `.rlb` decoder: after an error, the count of a list was not checked, and the decoder asked for about 6 GB. The fix makes a count after an error zero. The find is a regression test in `crates/rulean-format/tests/fuzz/`.
- A second local run of 10 minutes for each target, after the fix, found nothing. It ran 1.2 M inputs on `olean`, 3.2 M on `ndjson` and 21.6 M on `rlb`.
- Grammar fuzzing and type-directed fuzzing are not started.

### 11.5.2 Mutation testing

- **Input mutation.** For each check in 05.9 and 06.2, a mutator breaks that one property in a valid declaration of the corpus (a wrong universe, a non-positive occurrence, a wrong projection index, a wrong recursor rule, a duplicate level parameter, and so on). rulean must reject every mutant that the official kernel rejects.
- **Code mutation.** `cargo mutants` runs on the core each week. A surviving mutant in engine F or R or in the inductive checks needs a new test.

## 11.6 Adversarial testing

The 2026 incidents show that models find kernel bugs (A§2). rulean uses the same method against itself.

- **AI red team.** Before each release, agents get the rulean source and the task "make rulean accept a proof of `False` with only standard axioms, or make it disagree with the official kernel". They have a fixed compute budget per release. Every finding gets a public advisory if it affects a release.
- **Known exploit shapes.** The test suite includes the 2026 exploit shapes: phantom parameters in nested inductives (#14576), `imax` propositions (#14613), `_nested` names (#14616), cache order dependence (#14806), stuck sorts (#14807), big numerals (#14849), hash collisions that defeat caches (#14576 PoC), and refcount overflow shapes. The last one cannot happen in rulean (no reference counts), but the large test shape stays in the suite.
- **Bounty.** From release 1.0, a public bounty for an accepted proof of `False` under standard axioms. The bounty size is decided before 1.0 (15.4).
- **Deviation tests.** Each row of the deviation register (05.12) has at least one test in `tests/deviations/`.

## 11.7 Release gate

A release needs all of these:

1. 100% pass on the conformance corpus for every supported profile (11.2).
2. No open F/R disagreement (11.3.4).
3. No open fuzz find.
4. The proof builds with no `sorry` and with exactly the standard axioms (10.9).
5. The release proof export is accepted by rulean, con-leche and nanoda (10.9).
6. The P1 targets hold on the nightly bench of the release commit (08.7).
7. The Arena submission of the release commit has no incorrect result.
