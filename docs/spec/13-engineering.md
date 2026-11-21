# 13. Engineering

This document specifies the repository, the build, the "no C/C++" policy, CI, code style, review rules, documentation and licence.

## 13.1 Repository

The repository is `tamnd/rulean`.

```
rulean/
  Cargo.toml                 workspace
  rust-toolchain.toml        the pinned nightly that Charon needs (10.10)
  toolchains.toml            Rust, Charon, Aeneas and Lean versions, pinned together
  flake.nix, flake.lock      reproducible build and CI environment
  deny.toml                  dependency policy (13.3)
  crates/
    rulean-store/  rulean-nat/  rulean-format/  rulean-core/       verified core (03.3)
    rulean-pool/   rulean-io/   rulean-simd/                        islands
    rulean-olean/  rulean-cli/  rulean-ffi/                         hardened
    rulean-pack/   rulean-bench/  rulean-diff/                      tools
  proof/
    lakefile.lean  lean-toolchain
    RuleanProof/
      Statements.lean  Contracts.lean                               protected (10.9)
      Spec/  SpecExt/                                               protected
      Twin/                                                         the Lean twin
      Extracted/                                                    Aeneas output, generated, committed
      Refine/                                                       R1 and R2 proofs
      Lockstep/                                                     the lockstep tactic and lemmas
    vendor/                                                         pinned con-leche, if forked (10.2.3)
  tests/
    arena/  corpus/  regressions/  deviations/  fuzz/  mutants/
  docs/
    spec/                      a copy of this specification, kept current
    report.schema.json
  SECURITY.md  SOUNDNESS.md  CONTRIBUTING.md  LICENSE-APACHE  LICENSE-MIT
```

## 13.2 Languages and versions

| Part | Language | Version policy |
|---|---|---|
| rulean code | Rust, edition 2024 | the nightly pinned for Charon; the code also builds on stable Rust when the `aeneas` feature is off, and the release is built with the pinned nightly so that the verified code and the shipped code are the same |
| proofs | Lean 4 | one pinned release, bumped on a monthly cadence (10.10) |
| scripts | Rust (`xtask`) or POSIX shell | no Python in the build; Python is allowed in analysis scripts under `tools/` |

## 13.3 Build and the "no C/C++" policy

### 13.3.1 The rule

The requirement is "a Lean kernel rewrite in Rust (so no C/C++)". Its checkable form is (D§10, D§12.4):

1. **No C, C++ or assembly source** in the rulean tree, and none compiled by the build script of any dependency.
2. **Banned build dependencies:** `cc`, `cmake`, `bindgen`, `pkg-config`, `autotools`-based `-sys` crates. Banned crates include `mimalloc` / `libmimalloc-sys`, `tikv-jemallocator`, `snmalloc-rs`, `rpmalloc`, `rug` / `gmp-mpfr-sys`, and `blake3` without the `pure` feature.
3. **Allowed:** the platform system library through Rust `std` and the `libc` crate (glibc or musl on Linux, libSystem on macOS, the UCRT on Windows); the compiler-rt intrinsics shipped inside Rust's `std`. There is no portable way to avoid them: macOS has no stable system call interface (D§10). They are listed as "platform" in the trusted base (10.8).
4. **The C ABI is not C.** `rulean-ffi` exports `extern "C"` functions for Lean. That is Rust code with a calling convention.

### 13.3.2 Enforcement

- `cargo deny check` with a ban list for the crates above.
- `cargo tree -e build` in CI. The job fails if any crate in the build graph depends on `cc`, `cmake`, `bindgen` or `pkg-config`.
- A scan of the vendored source of every dependency (`cargo vendor`) for `*.c`, `*.cc`, `*.cpp`, `*.h`, `*.hpp`, `*.S`, `*.s`, `*.asm`. Any hit fails the job.
- The release build uses `-Z build-std` with `compiler-builtins` in its pure-Rust mode where the target supports it, so that no compiler-rt C intrinsics are linked (D§10). Where a target does not support it, the release notes say so.
- An optional Linux build links no libc at all (`rustix` with the `linux_raw` backend). It is a test target, not a promise (D§10).

### 13.3.3 Build profile

```toml
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
panic = "abort"
overflow-checks = true
debug = "line-tables-only"
```

- PGO uses the Init and Std exports as training input. PGO does not change semantics, so the verified build is still the measured build (02.2).
- `target-cpu` is the baseline of the platform (x86-64-v2, Apple M1) in release binaries. A `native` build is allowed for benchmarks only if the Arena build uses it too.

### 13.3.4 Allowed dependencies

| Crate | Where | Reason |
|---|---|---|
| none | verified core | 03.3 dependency rule |
| `memmap2` | `rulean-io` | read-only mapping |
| `zstd` (pure-Rust decoder, `ruzstd`) | `rulean-io` | compressed exports; the C `zstd` crate is banned |
| `sha2` | `rulean-cli` | report hash; pure Rust |
| `serde`, `serde_json` | `rulean-cli` | report writing only, not input |
| `clap` | `rulean-cli` | options |
| `proptest`, `num-bigint`, `malachite` | tests only | property tests and oracles; malachite is LGPL and never in a shipped binary |
| `kani-verifier`, `verus` | proof jobs | island proofs |

Any new dependency needs a maintainer review with the questions in `deny.toml`: does it compile C, is the licence compatible, is it maintained, does it have `unsafe`?

## 13.4 Continuous integration

| Job | Trigger | Time budget | Content |
|---|---|---|---|
| lint | every push | 5 min | `rustfmt`, `clippy -D warnings`, the Aeneas subset lint (10.6), no-C checks (13.3.2) |
| unit | every push | 10 min | unit and property tests (11.4) |
| extract | every push | 10 min | Charon and Aeneas on the verified crates; the `Extracted/` directory must equal the committed one |
| proof-incr | every pull request | 30 min | build the changed proof modules and their dependents |
| arena | every pull request | 15 min | the Arena test suite and the 2026 regression tests |
| bench-quick | every pull request | 15 min | 08.7.2 quick suite and its gates |
| proof-full | nightly, release branches | 60 min on 32 cores | the full proof; `#print axioms` on T1 to T5 equals the standard axioms (10.9) |
| corpus | nightly | 3 h | conformance corpus (11.2), cross-kernel runs, `--confirm=all` |
| scale | weekly | 12 h | FLT (Anthropic), RH, unsafe corpus, fuzzing, mutation tests |

The Aeneas subset lint is a `rustc` lint plugin or a `syn`-based checker. It rejects the patterns of 10.6 in the verified crates before Charon runs, so that authors get a clear message instead of an extraction failure.

## 13.5 Review rules

- Every pull request needs one maintainer approval. Pull requests that touch protected proof files (10.9), `deny.toml`, the build profile, `rulean-pool`, `rulean-io` or `rulean-ffi` need two.
- An AI agent can write code and proofs, open pull requests and review. An agent's approval does not count toward the approval rule.
- Every agent-made pull request states the model, the task class and the human responsible (10.9).
- Commits on `main` are signed.

## 13.6 Code style

- Names follow the official kernel where the concept is the same (`whnf_core`, `is_def_eq_core`, `infer_proj`), so that engine R can be compared with the C++ code line by line.
- Every function in engine R starts with a comment that names the C++ file, the line range and the lean4 commit it ports.
- Every function in the verified core has a doc comment with its twin function name.
- No macros in the verified core, except `derive` for simple traits that Aeneas supports.
- Error messages follow the official kernel text where one exists.

## 13.7 Documentation

| Document | Content |
|---|---|
| `docs/spec/` | this specification, updated with every design change; a pull request that changes behaviour updates the spec in the same pull request |
| `README.md` | what rulean is, how to install and run it, the current Arena numbers with their date |
| `SOUNDNESS.md` | the theorem statements in plain language, the trusted base table (10.8), and the history of soundness bugs |
| `DEVIATIONS.md` | the deviation register (05.12) |
| `CHANGELOG.md` | per release; every profile change and every deviation change is listed |

Documentation follows the same writing rules as this specification (00.4).

## 13.8 Licence

- rulean is dual-licensed Apache-2.0 and MIT, as most of the Rust ecosystem is.
- The proof reuses con-leche and may adapt con-ron's `lockstep` tactic. Before any code or proof is copied, the licences of con-leche and con-ron are checked and recorded in `proof/vendor/NOTICE` (15.4, open question Q1).
- Lean's own code is Apache-2.0. Engine R is a port of the C++ kernel, so it carries the Apache-2.0 notice of the Lean project in its file headers.
