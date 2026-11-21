# B. Lean kernels and kernel performance (research pass, 2026-11-21)

Scope: background for **rulean**, a pure-Rust Lean 4 kernel. The goals are 10x faster than the official C++ kernel, accepting exactly what it accepts on all Lean code, and being formally verified.

Tags:
- **[P]** a primary source I read: repo file, results.json, author blog, issue or paper.
- **[S]** secondary only: a summary, a search snippet, or a claim I did not cross-check.
- **[U]** unverified or contested.

Snapshots used:
- Live arena: `results.json` at lean-kernel-arena rev 2d6b1ff6, run on 2026-11-21 01:41 UTC on a GitHub Actions x86 runner. https://github.com/leanprover/lean-kernel-arena/commit/2d6b1ff6 [P]
- Round 2026-09 snapshot: Zenodo 10.5281/zenodo.22944094, results.json at rev 5d7ca987, published 2026-09-24. https://zenodo.org/records/22944094 [P]
- Shallow clones were read only and never built or run: nanoda, lean4lean, con-leche, con-ron, con-agua, ind-models, nano-lean, gruszka, sokonanoda and 15 other arena kernels (for line counts).

Arena metric. The arena's "virtual time" is instructions ÷ 6.0 Ginstr/s, which is CPU work rather than wall time. https://arena.lean-lang.org/ [P]

For the same run, wall time on the runner is usually larger for single-threaded checkers and smaller for multi-threaded ones. I quote instructions (T = 10^12) as the main metric because it is the most reproducible.

---

## 1. The Lean Kernel Arena

### 1.1 Size of the arena over time

| Snapshot | Checkers | Tests | Mathlib export | Source |
|---|---|---|---|---|
| 2026-03-16 ("Who watches the provers") | 7 kernels | 133 benchmarks | n/a | https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/ [P] |
| Round 2026-09 (rev 5d7ca987) | 26 | 219 | 5.2 GB, 100.0M lines, Lean 4.29.1, lean4export 3.1.0 | Zenodo 22944094 results.json [P] |
| Live 2026-11-21 (rev 2d6b1ff6) | 37 | 265: 145 accept, 90 reject, 30 "either" | 5.9 GB, 112.1M lines, Lean 4.36.0, lean4export 3.1.0 | arena results.json [P] |
| Hales on Tao's blog, 2026-10-09 | "About 25 kernels for Lean have been written" | | | https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/ [P] |

Notes on the table:
- The live tarball of tests has 135 good and 90 bad tests [P].
- The Mathlib export grew about 12% in bytes in two months (5.2 GB to 5.9 GB).
- The **30 "either" tests** are cases where both accepting and rejecting count as correct. Even the arena's reference semantics does not define the "exact" accept set for every input. That matters for rulean's "accept exactly what official accepts" requirement [P].

### 1.2 Mathlib ranking, live run 2026-11-21

Columns:
- **Instr**: total instructions over all threads.
- **V**: virtual minutes.
- **x off**: official v4.35.0 instructions ÷ this checker's.
- **Bad tests**: the result on the 90 must-reject tests.

| Checker | Language | Author / provenance | Instr | V (min) | Wall, CPU | RSS | Threads | x off | Mathlib | Bad tests |
|---|---|---|---|---|---|---|---|---|---|---|
| nano-lean v0.4.2 | Rust | sdiehl | 0.40T | 1.1 | 50 s, 167 s | 5.0 GiB | 4 | 30.6 | accepted | 90/90 |
| gruszka | Rust | jasisz, AI-written | 0.51T | 1.4 | 32 s, 110 s | 2.4 GiB | 4 | 23.6 | accepted | 90/90 |
| sokonanoda | Rust | intgrah (Jeremy Chen) | 0.53T | 1.5 | 54 s | 5.0 GiB | 4 | 22.9 | accepted | 90/90 |
| mathgraph | Rust | metalogiclabs | 0.91T | 2.5 | 179 s | 6.2 GiB | ? | 13.3 | accepted | **8 wrong accepts** |
| pestka | Aver→Rust | jasisz | 1.70T | 4.7 | 148 s | 3.4 GiB | ? | 7.1 | accepted | 90/90 |
| kefir | Rust | dmitrykorolev | 2.58T | 7.2 | 430 s | 2.5 GiB | 1 | 4.7 | accepted | 90/90 |
| palladium | Rust | Claude for yoonwoojeong | 2.83T | 7.9 | 162 s | 3.9 GiB | 4 | 4.3 | accepted | ok |
| nanoclo | Rust | sgraf812 | 3.01T | 8.4 | 256 s | 7.4 GiB | ? | 4.0 | accepted | **2 wrong accepts** |
| **con-ron** (verified) | Rust | Claude under Breitner | 3.47T | 9.65 | 178 s, 551 s | 4.4 GiB | 4 | 3.5 | accepted | 87 + 3 declined |
| kefir-wasm | Rust→wasm | dmitrykorolev | 3.50T | 9.7 | | | | 3.5 | | |
| con-agua (verified) | x86-64 asm | leanprover, Claude | 3.93T | 10.9 | 167 s | 11.6 GiB | 4 | 3.1 | accepted | 87 + 3 declined |
| nanobruijn | Rust | nomeata | 4.71T | 13.1 | 405 s | 6.8 GiB | ? | 2.6 | accepted | 90/90 |
| nanoda | Rust | ammkrn (Chris Bailey) | 5.77T | 16.0 | 442 s, 1475 s | 6.0 GiB | 4 | 2.1 | accepted | 90/90; eta-struct-major tests time out |
| **con-leche** (verified) | Lean | Claude under Breitner | 6.13T | 17.0 | 206 s, 801 s | 4.8 GiB | 4 | 2.0 | accepted | 87 + 3 declined |
| pestka-wasm | Aver→wasm | jasisz | 7.05T | 19.6 | | | | 1.7 | | |
| tenet-jvm | Java | keithadler + Claude | 9.43T | 26.2 | | | | 1.3 | accepted | 90/90 |
| official-nightly 2026-11-14 | C++ | leanprover | 9.82T | 27.3 | 2575 s | 9.9 GiB | 1 | 1.23 | accepted | 90/90 |
| eink0rn | Haskell | Timeroot | 10.61T | 29.5 | 362 s | 13.5 GiB | 8 | 1.14 | accepted | 90/90 |
| **official v4.35.0** | C++ | leanprover | 12.10T | 33.6 | 2696 s | 9.9 GiB | 1 | 1.0 | accepted | 90/90 |
| ind-models | Lean, on the official kernel | nomeata + Claude/Codex | 12.94T | 35.9 | 1586 s | | | 0.94 | accepted | 90/90 |
| tenet | C# | keithadler + Claude | 16.99T | 47.2 | | | | 0.71 | accepted | 90/90 |
| tenet-hs | Haskell | keithadler + Claude | 19.27T | 53.5 | | | | 0.63 | accepted | 90/90 |

Mathlib runs that ended in error or rejection (instructions measured up to that point):

| Checker | Instr | Result |
|---|---|---|
| metalean-slow | 1.42T | declined |
| lean4lean | 1.93T | rejected: `unknown constant 'instDecidableEqBool'`. lean4lean is pinned to v4.33.0-rc2 and tested against a 4.36 export. |
| canonical-min | 2.09T | incorrect |
| nanoclo-fortran | 3.86T | error |
| metalean-fast | 4.49T | rejected |
| kiota | 6.16T | error |
| ocaml4lean | 13.31T | error |

Not run on Mathlib or declined:
- lazylean (C++): timeout at 3600 s.
- logos-kernel (Rust; Brahmastra-Labs/logicaffeine): recursion depth limit.
- Toy or novelty entries: lean4cobol (COBOL, kim-em), rpylean (RPython, Julian), evmlean (Solidity), mini (Lean, nomeata), overfull (TeX, kim-em), vow-lean-kernel.

Source for all of the above: arena results.json [P].

Where a cell above says "ok" or "?", I did not tabulate it individually.

Wrong accepts (all [P]):
- mathgraph accepts 8 must-reject tests: closure-level-subst, nested-name-capture, nested-rec-rule-nfields, pi-closure-context, rec-rule-proof-irrel, rec-rule-proof-irrel-nested, unit-rec-rule, inductive-undeclared-universe.
- nanoclo accepts rec-rule-proof-irrel and rec-rule-proof-irrel-nested.

### 1.3 Round 2026-09 (Zenodo) Mathlib ranking, for trend

Mathlib export here is 5.2 GB, Lean 4.29.1. Results are only comparable within a round. Source: Zenodo results.json [P].

| Checker | Instr | V (min) | Wall | RSS | Result |
|---|---|---|---|---|---|
| mathgraph | 0.71T | 2.0 | 112 s | 5.6 GiB | accepted |
| sokonanoda | 0.75T | 2.1 | 55 s | 5.9 GiB | accepted |
| **parse-only** (official v4.34.0 `--parse-only`) | **1.66T** | 4.6 | 139 s | 7.6 GiB | accepted |
| nanoclo | 3.06T | 8.5 | 198 s | 5.8 GiB | accepted |
| con-ron | 3.52T | 9.8 | 281 s | 6.6 GiB | accepted |
| lazylean | 5.53T | 15.4 | 324 s | 5.6 GiB | accepted |
| still-nanoda (cache-study fork) | 5.59T | 15.5 | 224 s | 5.2 GiB | accepted |
| nanoda | 6.46T | 18.0 | 456 s | 7.4 GiB | accepted |
| nanobruijn | 7.54T | 21.0 | 590 s | 6.1 GiB | accepted |
| con-leche | 8.04T | 22.3 | 461 s | 8.0 GiB | accepted |
| eink0rn | 9.73T | 27.0 | 327 s | 12.0 GiB | accepted |
| ind-models | 11.39T | 31.6 | 1526 s | 8.0 GiB | accepted |
| official | 11.83T | 32.9 | 3302 s | 7.6 GiB | accepted |
| **lean4lean** | **14.35T** | **39.9** | 3368 s | **9.3 GiB** | accepted |
| official-v4.28.0 | 14.92T | 41.4 | 3112 s | 9.4 GiB | accepted |
| tenet | 16.53T | 45.9 | 485 s | 12.8 GiB | accepted |
| nanoclo-fortran | 18.16T | 50.4 | 2567 s | 13.5 GiB | accepted |

Trends:
- **The official kernel is a moving target** [P]. Successive official checkers fell from 14.92T (v4.28.0) to 11.83T (Round 2026-09 "official", about v4.33/4.34), and then to 9.82T (nightly 2026-11-14). That is a 34% cut in a few months, and it came from kernel work that includes Adjedj's renovation meta-issue lean4#14977 (opened 2026-08-31). https://github.com/leanprover/lean4/issues/14977
- In that round, **parsing NDJSON cost the official kernel 1.66T, about 14% of its total**. That agrees with con-leche PERF.md: about 306 instr/byte, or 18.1% of the official Mathlib run and 24.3% of Init [P].
- nano-lean's whole run, parsing included, is 0.40T on a 5.9 GB file, about 68 instr/byte [P, derived].

### 1.4 Other large tests (live run, virtual time)

Source: arena results.json [P].

| Test | Official v4.35.0 | Fastest |
|---|---|---|
| init | 66.9 s | 4.1 s |
| std | 111 s | 6.7 s |
| cedar | 147 s | 10.5 s (nano-lean) |
| con-leche (export of con-leche itself) | 216 s | 10.3 s |
| cslib (2.3 GB) | 566 s | 23.6 s |
| navier-stokes-euler (1.5 GB) | 672 s | 17.2 s |

con-leche, con-ron and con-agua decline Cedar because it relies on the `native_decide` axiom (`Lean.ofReduceBool`) [P].

### 1.5 The arena's `perf/` tests where the official kernel is slow

Values are virtual seconds. Source: arena results.json [P].

| Test | Official | nano-lean | con-ron | Comment |
|---|---|---|---|---|
| magma-list-deep-n36 | 35.3 | 0.42 | 21.9 | deep defeq over nested structures |
| ite-taken-branch | 19.45 | 0.04 | 11.59 | lazy-delta unfolds the wrong side |
| short-circuit-and | 17.6 | 0.04 | n/a | |
| unfold-before-literal | 14.5 | n/a | n/a | |
| loop-unfolded-once-bad | 14.24 | 0.04 | n/a | gruszka shows its own pathology here: 23.4 s |
| proj-applied-struct | 13.96 | ~0 | 10.33 | |

Reading:
- These are **algorithmic gaps of 100-1000x**, not constant-factor gaps.
- con-ron keeps the official kernel's lazy-delta strategy, so it inherits most of the official slowness on these tests (about 0.6-0.75x of official).
- NbE kernels avoid it.

---

## 2. nanoda (ammkrn/nanoda_lib)

### 2.1 Repository facts [P]

Repository: https://github.com/ammkrn/nanoda_lib

| Field | Value |
|---|---|
| Created | 2020-02-11 |
| Head | 0da9f98, 2026-11-07 |
| Version | v0.4.32 |
| Licence | Apache-2.0 |
| Stars | 243 |
| Author | Chris Bailey (ammkrn) |
| Dependencies | indexmap 2.13, rustc-hash 1.1 (FxHash), num-bigint 0.5.1, num-integer, num-traits, serde_json |
| Release profile | `lto`, `overflow-checks = true` |

**Line counts**: 10,258 `.rs` lines in total, of which 1,504 are tests and 1,181 are printers.

| File | Lines | File | Lines |
|---|---|---|---|
| inductive.rs | 1825 | env.rs | 328 |
| tc.rs | 1400 | quot.rs | 316 |
| parser.rs | 1083 | level.rs | 304 |
| util.rs | 1036 | debug_printer.rs | 228 |
| pretty_printer.rs | 953 | union_find.rs | 130 |
| expr.rs | 926 | name.rs | 91 |
| tests/natlit.rs | 916 | main.rs | 72 |
| tests/level.rs 213, tests/util.rs 160, tests/expr.rs 115 | | unique_hasher.rs 41, lib.rs 21 | |

The core checker (inductive, tc, expr, env, quot, level, util, name, union_find) is about 6.4k lines. So the blog phrase "under 5,000 lines of checking logic" depends on what is counted [U].

### 2.2 Architecture [P]

All of the following is from the repo source.

- **Terms.**
  - `enum Expr<'a>`. Every node stores a precomputed `hash: u64`, `num_loose_bvars: u16` and `has_fvars`.
  - Variables are de Bruijn indices: `Var{dbj_idx:u16}`.
  - `Local` carries its binder type and an `FVarId::{DbjLevel(u16) | Unique(u32)}`. This is **locally nameless, with free variables named by de Bruijn level**.
- **Handles.** `Ptr<A>{raw:u32}`. Bit 31 is the DAG marker (persistent `ExportFile` vs temporary `TcCtx`), and the remaining 31 bits are an index.
  - Everything is **hash-consed** into `UniqueIndexSet`s inside a `LeanDag`, which holds names, levels, exprs, uparams, strings and bignums.
  - Pointer equality therefore equals structural equality within a tier.
- **Caches.**
  - `ExprCache` holds inst, subst, dsubst, abstr and abstr_levels caches.
  - `TcCache` holds infer (check and no-check variants), whnf, whnf_no_unfolding, eq_cache (a union-find), congr_fail, defeq_fail and strong_cache.
  - **All of them are cleared per declaration.**
- **Parallelism.**
  - `std::thread::scope` workers take declarations by bumping an `AtomicUsize` index into the declarations `IndexMap`.
  - Environment visibility is enforced by a `cutoff` index.
  - The default stack is 32 MB; the arena raises it to 256 MiB.
  - In the arena run (4 threads), CPU÷wall = 1475÷442 = 3.3x.
- **Extensions.** `nat_extension` and `string_extension` (GMP-like literal fast paths) are off by default and on in the arena.
- **Serial memory.** con-ron's overview reports that serial nanoda on Mathlib was aborted at a 27 GiB memory cap, and that nanoda's Init run took 225.76G instructions [P, con-ron OVERVIEW]. https://github.com/leanprover/con-ron

### 2.3 nanoda bugs

| Date | Bug | Source |
|---|---|---|
| 2026-03 | Claude Opus 4.6 found **2 nanoda bugs** (and 7 Rocq kernel bugs). The blog gives **no technical detail** of the two nanoda bugs. | https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/ [P]; bug detail [U] |
| 2026-07/08 | The #14576 Collatz exploit was also accepted by a **week-old nanoda**, through a **separate bug: projection type name not verified**, reported by Jeremy Chen. Hales calls it "a somewhat out-of-date Nanoda kernel". | https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/ [P]; Tao/Hales post [P] |
| 2026-08 | During the bug hunt, nanoda accepted #14807/#14843; lean4lean was unaffected by these. | https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/ [P] |
| 2026-08 | #14607–#14616, found with Selsam/OpenAI, were caught by nanoda (nanoda rejected them). | 14576 postmortem [P] |

---

## 3. lean4lean (digama0/lean4lean)

Repository facts [P], https://github.com/digama0/lean4lean:
- Head 67f63b0 (2026-10-10), toolchain v4.33.0-rc2, 279 stars.
- Lines by directory: Verify 23,745; Theory 6,911; Experimental 13,309; Inductive 885.
- Recent commits:
  - 2026-08-14: substDF. Same day, a new file, `Theory/LevelSat.lean`, proves **level equivalence is coNP-hard** by reduction from SAT.
  - 2026-08-28: three-part "primitives" proofs.
  - 2026-08-26: `recDepth` raised to 50000.
  - 2026-10-10: primitive types compared up to `mdata`.

The paper is "Lean4Lean: Verifying a Typechecker for Lean, in Lean", by M. Carneiro. https://arxiv.org/abs/2403.14064 [P]
- Versions: v1 2024-03-21, v2 2024-12-03, v3 2025-09-14.
- The paper reports lean4lean is **20–50% slower than the C++ kernel** on Mathlib [P].
- The kernel itself is a port of the C++ kernel into Lean, compiled by the Lean compiler; it is not a new algorithm.

Arena performance:
- Round 2026-09: 14.35T instructions, 39.9 virtual minutes, 3368 s wall, 9.3 GiB. That is 1.21x the official kernel's instructions in that round, consistent with the paper [P].
- Live run: **fails on Mathlib** with `unknown constant 'instDecidableEqBool'`, a version-skew issue [P].

Verification status, from the repo [P]:
- `Verify/` proves the implementation refines the `Theory/` typing judgement, but it is **not complete**.
- Remaining `sorry`s include:
  - `inductDecl` in Verify/Environment;
  - projections (TrProj);
  - `tryEtaStructCore`, `isDefEqUnitLike` and WHNF parts;
  - `VEnv.addInduct` / `VInductDecl.WF`;
  - and, in the metatheory, Injectivity, ChurchRosser and UniqueTyping.
- The 2026-10-15 blog says lean4lean's verification is "expected within months" [P].

Bugs found (`bugs-found.md`) [P]:
- a `hasLooseBVars` issue (reported on Zulip);
- lean4#10475 and lean4#10511.

The postmortem says lean4lean was affected by #14576 [P].

lean4lean-model (https://github.com/digama0/lean4lean-model) [P]:
- Created 2026-08-02, pinned to Lean v4.32.2 plus Mathlib.
- Target: consistency of `Lean4Lean.Theory`, assuming ω inaccessibles.
- `Consistency.lean` is **still `sorry`ed, "pending the model construction"**.
- Separately, con-leche instantiates its set theory via `carneiro_implies_conleche` from this package (see §4.1).

---

## 4. con-leche, con-ron, con-agua, ind-models, Ix

### 4.1 con-leche, the verified kernel written in Lean [P]

Repository: https://github.com/leanprover/con-leche

| Field | Value |
|---|---|
| Created | 2026-08-19 |
| Head | 11d8ff13, 2026-11-21 |
| Stars | 165 |
| Toolchain | v4.36.0 |
| Authors | Claude (Fable and Opus) under Joachim Breitner (2026-10-15 blog) |
| Size | 1,423 `.lean` files, **364,744 lines** |
| Trusted C | `native/nat_hash.c` (55 lines) |
| Docs | OVERVIEW.md 2,322 lines; DESIGN.md 126,151 lines |

Lines by directory:

| Directory | Lines | Directory | Lines |
|---|---|---|---|
| Model | 121,060 | SetModel | 3,691 |
| Verify | 112,138 | SetTheory | 2,963 |
| Frontend | 19,128 | PinGen | 1,828 |
| Kernel | 15,412 | Rules | 1,609 |
| Semantics | 12,755 | Complete | 1,473 |
| Cached | 8,284 | Term | 403 |
| Driver | 6,772 | Modular | 382 |

So the executable kernel is about 15k lines and the proofs about 250k lines. The proof-to-code ratio is about 16:1 [P, derived].

**What is proven** [P]:
- `main_json_model`: if the driver accepts an NDJSON file, the resulting environment has `IsModel V model`. The corollary `main_no_False` says no declaration proves `False`.
- Also `model_exists` (pure), `main_modular_one` (modular checking) and `main_compare_json_model`.
- The set-theoretic background is ZF without infinity and without choice, plus an ω-chain of Tarski-style Grothendieck universes. It is instantiated from Carneiro's ω-inaccessibles assumption via `carneiro_implies_conleche`.
- IO is modelled through a `CheckerIO` class with a nondeterministic `ModelIO`.
- The result is partial correctness: it says nothing about termination or completeness.

**What is trusted** [P]:
- The Lean compiler, runtime and GMP used to run it.
- `nat_hash.c`.
- The `withPtrAddr` / RC-peeking primitives.
- The meaning of the export format and the driver's file IO.
- The consistency of the set theory, i.e. ω inaccessibles.

**Design, and where it departs from the official kernel** [P]:
- **Own term representation.** Locally nameless, with free variables carrying a de Bruijn level and a type (nanoda-inspired), plus hashes in `computed_field`s.
- **Nested inductives.** A uniform positivity-based treatment, with **no nested→mutual translation**.
- **Theorem bodies are opaque**, anticipating lean4#14896 (nomeata, "make theorems opaque to the kernel", open since 2026-08-23). An "And rescue", a K-like hack, handles a known case.
- **Nat.** Literals use Lean's `Nat` (GMP).
  - Structural operations are certified by checking their recurrences up to defeq.
  - div, mod, gcd and the bitwise operations rely on pinned toolchain definitions.
  - A pinned basis covers Eq, Nat, Empty, False, Quot and And.
- **Axioms.**
  - Only propext, Classical.choice and Quot.sound are allowed. `sorryAx` is tolerated only if it is unused.
  - `trustCompiler`, `reduceBool` and `reduceNat` are replaced.
  - **native_decide and bv_decide are declined, and so are unsafe and partial definitions.**
- Supported conversions: eta, struct-eta, unit-like types, proof irrelevance and K.
- **It accepts more than the official kernel**:
  - semantic level comparison;
  - proof-irrelevance fall-through;
  - large elimination for some single-constructor Prop-sort blocks;
  - the And rescue.
- **It rejects some things the released kernel accepts**: those whose checking reduces a proof, which becomes impossible once theorems are opaque.
- Front end: an `.olean` reader, modular checking, `--compare` and a `--schedule` scheduler.

**Arena result** [P]:
- 87 of 90 bad tests rejected, 3 declined.
- 6 good tests declined (non-standard axioms, unsafe/partial), plus Cedar (native_decide).

**Performance.** From PERF.md (commit a0f1865, 2026-10-13), on an AMD EPYC 9455 (96 cores) with Lean v4.33.0 exports. The Mathlib export is 6.07 GB, 107.8M lines, 691,203 records. https://github.com/leanprover/con-leche/blob/HEAD/PERF.md [P]

| Stream | Official | `--trusted` | `--verified` |
|---|---|---|---|
| Mathlib instructions | 10.26T | 6.40T (0.62x) | 7.05T (0.69x) |
| init-full instructions | 439.61G | 402.66G | 408.36G (0.93x) |
| Mathlib wall, 1 job | 28.9 min | 9.8 min | 10.7 min |
| Mathlib RSS | 11.44 GiB | 4.27 GiB | 4.27 GiB |
| Mathlib wall by jobs (verified) | n/a | n/a | 14.7 min at 1, 3.1 min at 4, **100 s at 8** |

More PERF.md figures [P]:
- At 8 jobs the phases are parse 5.4 s, install 5.3 s and check 88.5 s. The worker pool adds 3.5% instructions.
- The official kernel spends **11.89M instructions per declaration on Mathlib**, against 5.60M on Init.
- **Lean allocation and refcount symbols are 45–48% of con-leche's instructions**, with `lean_dec_ref_cold` alone at 16–20%. In the official init-full profile they are 25%.

### 4.2 con-ron, a Rust refinement of con-leche [P]

Repository: https://github.com/leanprover/con-ron

| Field | Value |
|---|---|
| Created | 2026-09-13 |
| Head | de06320, 2026-11-17, Joachim Breitner |
| Rust | **116,245 lines**: con-ron-core 110,163 (verified), driver 3,824, con-ron-dump 1,993 |
| Lean proofs | **388,606 lines** |
| Build | Nix flake pins Aeneas, Charon and a Rust nightly; `patches/aeneas.patch` is 595 lines |
| Profile | `overflow-checks = true`, fat LTO, `codegen-units = 1` (−11.6% instructions on Init) |
| Allocator | mimalloc by default; system malloc and jemalloc as options |

**Representation** [P]:
- A 32-bit handle: bit 31 is the tier (persistent vs scratch).
  - The wide form, used for applications, has a 30-bit index.
  - The narrow form has a 4-bit constructor tag and a 26-bit index.
- **One array per constructor.** An application node is two u32s, and applications are 85% of nodes.
- A derived column stores the hash, a loose-bvar bound, an fvar range and a has-level-param flag.
- Hash-consing tables use 8-byte slots. `HashMap2` is open-addressed with epoch stamps, so clearing it is O(1).
- The frozen persistent tier is shared read-only between workers.
- Caches are keyed by handle, and the per-declaration caches are flushed after each declaration.

**Proof chain** [P]:
- Theorem 1: a pure-Lean "twin" refines con-leche.
- Theorem 2: the Rust code, translated to Lean by **Aeneas/Charon**, refines the twin, using a custom `lockstep` tactic.
- The capstone `no_False_declaration` / `model_exists` gives partial correctness on propext, Classical.choice and Quot.sound only.

**Trusted base** [P]:
- Aeneas and Charon, i.e. the faithfulness of the Rust-to-LLBC-to-Lean translation, including the 595-line patch.
- rustc, std and the allocator.
- The `overflow-checks` flag, which the proof assumes panics on overflow.
- The unverified driver, `pool.rs::parallel_all`, and the file-snapshot assumption.
- Axiomatised "holes": `Arc` new/clone/deref/ptr_eq and `str::as_bytes`.
- Everything con-leche itself trusts, except the Lean runtime and GMP.

**Aeneas subset constraints** [P]: no closures, no `?`, no derive, no `std::collections`, no `unsafe`. All data structures, including hash maps, are hand-written and verified.

**Performance** (con-ron docs, 2026-10-05) [P]:

| | Init instr | Mathlib instr | Mathlib RSS |
|---|---|---|---|
| con-ron, 1 worker | 211.5G | 3,848G | 7.26 GB |
| con-leche, 1 worker | 488.94G | 8,853G | n/a |

- Init wall: 21.8 s at 1 worker, 5.4 s at 8.
- **Same algorithm, Rust representation: 2.3x fewer instructions than con-leche.**
- On Init, con-ron uses 93.7% of nanoda's instructions.
- Differential testing uses 602 streams.
- Live arena run: 3.47T, 178 s wall and 551 s CPU on 4 threads, 4.4 GiB RSS. That is 3.5x fewer instructions than v4.35.0, 2.8x fewer than the nightly, and **15x faster in wall time than the single-threaded official leanchecker**.

### 4.3 con-agua: verified x86-64 [P]

Repository: https://github.com/leanprover/con-agua (created 2026-10-25)

- Size: 1,086,328 Lean lines, 233,890 asm lines, 725 C lines.
- A verified compiler emits x86-64 asm, proved against the Kraken x86 semantics (sgraf812/kraken). A C harness of about 200 lines is trusted.
- Arena: 3.93T, 167 s, 11.6 GiB, 4 threads.
- This is the route that removes rustc, Aeneas and the Lean compiler from the trusted base, at about 1.13x con-ron's instructions.

### 4.4 ind-models (nomeata/lean-inductive-models) [P]

Repository: https://github.com/nomeata/lean-inductive-models

- Created 2026-08-11; 57,476 Lean lines.
- It is an NDJSON→NDJSON filter that performs **translation validation**.
  - Each supported inductive group is replaced by ordinary definitions: type formers, constructors, recursors and projections, built over a small hard-coded basis.
  - The *official* kernel then checks those definitions.
  - Computation rules are published as propositional equalities, not as definitional ones.
- In its own words: "This is translation validation, not a general soundness proof … and not yet a verified translation". The model constructions were "generated by Claude and Codex".
- Arena: 12.94T, 1586 s; all bad tests rejected.
- Relevance to rulean: a way to **remove inductive-type checking from the trusted core**. It is not a performance technique.

### 4.5 Ix (argumentcomputer/ix) [P]

Repository: https://github.com/argumentcomputer/ix (created 2025-01-31, 109 stars)

- Ix is a zk proof-carrying-code protocol for Lean 4 using the content-addressed `ixon` format.
- Its kernel, `IxC/Kernel`, is a **modified copy of con-leche's verified checker**.
  - The entry point is `Ix.Kernel.Admission.checkBytes`; BLAKE3 is used as the content hash.
  - Theorems: every accepted environment has a set-theoretic model and no proof of False.
  - A separate `Ix.Cert.CompileCorrect` relates the Lean→Ixon compiler to the checker.
- IxVM, which does zk reduction and type checking, is "not yet released" and outside both theorems.
- Source: https://github.com/argumentcomputer/ix/blob/HEAD/docs/kernel.md
- Ix is not an arena entry.

---

## 5. Other kernels, translators and relevant systems

Line counts are total source lines in a shallow clone, tests included [P, wc]. The other columns come from the GitHub API and the arena descriptions [P].

| System | Language | Lines | Created | Technique summary | Mathlib |
|---|---|---|---|---|---|
| nano-lean (sdiehl/nano-lean) | Rust | 30,090 | 2026-09-27 | NbE over the `unbound` crate, de Bruijn indices, bumpalo, hashbrown, mimalloc, num-bigint, PGO; its own `blean` binary format; `--cache` keyed by a dependency-closure hash. Nat primitives are trusted by name, like the official kernel. | 0.40T on the arena. README: 57.4 s at -j1 on an M5 (53.5 s kernel), 11.85 s at -j14 on an M4 Max (7.55 s kernel, 10.7 GB) [P] |
| gruszka (jasisz/gruszka) | Rust | 17,788 | 2026-11-16 | NbE with hash-consed values, environments and spines. Per-worker arenas, **sessions that keep caches across declarations** (milestone 10), regions for in-declaration reclamation, scratch arenas for definitions. Its own Susz binary format (`susz pack` takes 1.9 s). Big Nat via num-bigint. AI-written. | README, M2 Pro with PGO: 1 worker 44 s, 2.0 GB, 369G; 4 workers 13.6 s; 8 workers 8.4 s, 375G. FLT (1.71M declarations): 3 min 55 s, 6.6T, 11–12 GB [P] |
| sokonanoda (intgrah/sokonanoda) | Rust | 14,052 | 2026-05-22 | nanoda lineage, NbE inspired by smalltt | 0.53T |
| nanoclo (sgraf812/nanoclo) | Rust | 15,110 | 2026-08-10 | delayed substitutions (closures), skew-binary jump pointers | 3.01T, 2 wrong accepts |
| nanobruijn (nomeata/nanobruijn) | Rust | 15,589 | 2026-04-06 | pure de Bruijn indices, lazy shifting via pointer+offset, caching stratified by depth | 4.71T |
| palladium (yoonwoojeong/Palladium) | Rust | 11,744 | 2026-11-10 | binder names erased; typed canonical locals make caches context-free; re-derives recursors | 2.83T |
| kefir (dmitrykorolev/kefir) | Rust | 105,067 | 2026-10-23 | low memory; call-by-need evaluator with a substitution fallback; single-threaded | 2.58T on 1 thread, 2.5 GiB |
| mathgraph (metalogiclabs) | Rust | 13,680 | 2026-08-16 | | 0.91T but **8 wrong accepts** |
| kiota (sankalpsthakur/kiota) | Rust | 24,839 | | | error |
| pestka (jasisz/pestka) | Aver | 31,526 | 2026-10-20 | written in the Aver language, compiled to Rust | 1.70T |
| lazylean (corun1024/lazylean) | C++ | 7,182 | | Krivine machine in the style of Coq's cClosure; human + Claude | 5.53T (Round 09); timed out live |
| eink0rn (Timeroot/eink0rn) | Haskell | 11,175 | 2026-08-28 | clean-room; nested→mutual→single indexed family | 10.61T, 8 threads |
| tenet / tenet-hs / tenet-jvm (keithadler) | C#, Haskell, Java | 19,033 (C#) | 2026-09-08 | Claude-assisted; tenet-jvm did Mathlib in 824 s on a laptop (description) | 9.43–19.27T |
| ocaml4lean (yoonwoojeong) | OCaml 5 | 4,270 | | 4 domains, its own bignum | error |
| nyaya (kodyvajjha/nyaya) | OCaml | 6,023 | | | declines Mathlib (Round 09) |
| metalean (intgrah/metalean) | Lean | 61,923 | 2026-09-18 | verified; no nested inductives | declined / rejected |
| logos-kernel (Brahmastra-Labs/logicaffeine) | Rust | n/a | | hash-consed DAG, closures | recursion depth limit |
| still-nanoda (SchrodingerZhu) | Rust | n/a | | nanoda fork, cache study | 5.59T vs nanoda 6.46T (−13%), Round 09 |
| trepplein (gebner/trepplein) | Scala | 2,055 | 2017-03-06 | Lean 3 era checker; last push 2022 | not in arena |
| Lean4Less (Deducteam/Lean4Less) | Lean | 8,111 | 2025-01-12 | translation that eliminates definitional equalities (toward Dedukti) | not a kernel; not in arena |
| lean2dk (Deducteam/lean2dk) | Lean | n/a | 2023-04-18 | "WIP translation from Lean to Dedukti" | not in arena |
| franken_lean (Dicklesworthstone) | Rust | n/a | 2026-07-21 | claims a full Rust Lean 4 toolchain with a "≤12 KLOC dual-engine kernel" | not in arena; claims [U] |

Sources for the less obvious rows:
- nano-lean: https://github.com/sdiehl/nano-lean [P]
- gruszka: https://github.com/jasisz/gruszka/blob/HEAD/docs/architecture.md [P]
- Lean4Less: https://github.com/Deducteam/Lean4Less [P]
- franken_lean: https://github.com/Dicklesworthstone/franken_lean [S]

AI-written kernels: gruszka, palladium, tenet*, lazylean, ind-models and all the con-* kernels are explicitly AI-written or AI-assisted [P]. Whether nano-lean is AI-written is not stated in the files I read [U].

---

## 6. The 2026 soundness incidents: re-verified

| Date | Event | Source |
|---|---|---|
| 2026-03-16 | Blog post. Claude Opus 4.6 found 7 Rocq kernel bugs and 2 nanoda bugs, and no false proof in Lean's kernel. A 2022 Lean arithmetic bug was rejected by nanoda. At the time the arena had 7 kernels and 133 benchmarks. | https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/ [P] |
| 2026-07-25 | An AI-assisted, sorry-free "disproof" of Collatz was published. It exploited nested inductives with phantom parameters, reachable via metaprogramming (lean4#14576). Kiran Gopinathan later reduced it to a small proof of False. | 14576 postmortem [P] |
| about an hour after the report | Fix PR lean4#14577, with follow-up #14582; hardening in #14621, #14631 and #14632. | postmortem [P] |
| 2026-08-02 | oss-security advisory: affected are **"All Lean 4 versions up to and including v4.31.0"** and nightlies through 2026-07-27. Fixed in nightly-2026-07-29. No stable release had the fix yet, and no CVE was assigned. | https://www.openwall.com/lists/oss-security/2026/08/02/1 [P] |
| 2026-07-30 to 08-20 | Bug hunt: kernel bugs #14613, #14616, #14806 and #14807/#14843; refcount overflow #14838, fixed with Koka-style sticky counts; GMP fix #14833 (6.1.2→6.3.0 required in CI); numeral bound #14849. Plan for a verified bignum. | https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/ [P] |
| 2026-08-21 | v4.33.1 released with the fixes. | hunt postmortem [P] |
| 2026-10-09 | Hales's guest post: "About 25 kernels for Lean have been written"; "I know of no complete, public relative-consistency proof covering Lean abstract type theory"; con-leche's consistency proof "has been checked by more than a dozen other proof-checkers". | Tao blog [P] |
| 2026-10-14 | lean4#15686: kernel checking slows down quadratically for `Nat` literals that are multiples of 2^64 (the literal hash used only the low 64 bits). Closed. | https://github.com/leanprover/lean4/issues/15686 [P] |
| 2026-10-15 | Blog: Lean now ships with nanoda, lean4lean, con-leche and con-ron. `lake check --paranoid` also runs a hardened-allocator official variant. Scale quoted: FLT 13M LoC, Mathlib 2.5M, Tau Ceti 3M, Courtade–Kumar 50M. The FRO says binary export and incremental checking are needed. | https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/ [P] |
| 2026-11-08 | lean4#16343 (Kha, open): **check declarations in the kernel in parallel**. Example: Init.Data.BitVec.Lemmas went from 4.2 s to 2.6 s wall. Related: RFC lean4#15569 (2026-10-08), parallel theorem checking in `Environment.replay`, prototyped in comparator#99. | https://github.com/leanprover/lean4/pull/16343 [P]; https://github.com/leanprover/lean4/issues/15569 [P] |

Earlier parallelism work, Lean 4.17 (2025-03) [P]:
- #5145 split the kernel environment from the elaborator environment.
- #6368 made kernel checking run in parallel with elaboration.
- #6691 added the parallel environment API.
- 4.18 (#6770) parallelised codegen.
- Source: https://lean-lang.org/doc/reference/latest/releases/v4.17.0/

---

## 7. Corrections to the old notes (2148/01-research-2026.md §1.2)

| Old claim | Verdict | Correct statement and source |
|---|---|---|
| Arena has "127 good and 72 bad tests" | **Outdated** | Round 2026-09 had 219 tests and 26 checkers. Live: 265 tests (145 accept, 90 reject, 30 either), 37 checkers [P]. |
| Hales counts "about 25 independent kernels" | **Slightly wrong** | Hales: "About 25 kernels for Lean have been written". He does not say "independent", and many are nanoda descendants or AI siblings [P]. |
| Round 2026-09 snapshot at Zenodo 22944094 | **Correct** | Published 2026-09-24, editor Breitner, Apache-2.0 [P]. |
| nanoda: "under 5,000 lines of checking logic" | **Contested** | The repo has 10,258 `.rs` lines; the core checker is about 6.4k without tests and printers [P]. "Under 5,000" is only the blog's phrasing [U]. |
| nanoda: "~15.6 min and 6 GB on Mathlib" | **Unverifiable as stated** | Round 2026-09: 18.0 virtual min, 7.4 GiB. Live: 16.0 min, 6.0 GiB. Wall time is 442–456 s on 4 threads [P]. |
| lean4lean: "~38.8 min and 11.6 GB" | **Not found in either snapshot** | Round 2026-09: 39.9 virtual min, 9.3 GiB, 3368 s wall. Live: fails with a version-skew error. 11.6 GB matches con-agua's live RSS, so the old note may have mixed rows [U]. |
| lean4lean verification "expected within months" | **Correct as a quote** | 2026-10-15 blog [P]. Many key sorries remain, and lean4lean-model's consistency proof is still `sorry` [P]. |
| con-leche: Claude (Fable and Opus) under Breitner; ~100 s on 8 threads | **Correct** | PERF.md: 100 s at 8 jobs on a 96-core EPYC; 10.7 min at 1 job [P]. |
| con-ron is a Rust translation proved to refine con-leche via Aeneas | **Correct but incomplete** | It is Rust written to satisfy Aeneas. Aeneas, Charon, rustc, the `Arc` holes and the driver are trusted [P]. |
| ind-models "checks that inductive types have models" | **Imprecise** | It is unverified translation validation: it emits model definitions and the official kernel checks them [P]. |
| #14576: Collatz on 2026-07-25, phantom parameters, fix in about an hour | **Correct** | [P] |
| "All versions up to v4.31.0 affected" | **Correct** | It is in the openwall advisory, not the blog: "up to and including v4.31.0" [P]. |
| A week-old nanoda accepted the exploit via a separate bug | **Correct** | The bug was that the projection type name was not verified (Jeremy Chen) [P]. |
| Hunt bugs, refcount, GMP 6.1.2→6.3.0, v4.33.1 | **Correct** | [P] |
| March 2026: 7 Rocq and 2 nanoda bugs by Claude Opus 4.6 | **Correct; details missing** | There is no public description of the two nanoda bugs [U]. |
| De Moura: "AIs are really good at exploiting soundness bugs in the kernels" | **Unverified** | Not found in any of the three de Moura posts I fetched [U]. |
| Remaining assumption "runtime and GMP" | **Partly outdated for con-ron/con-agua** | con-ron does not use GMP or the Lean runtime. Its trusted base is Aeneas, rustc and its allocator. con-agua's is a C harness plus the x86 semantics [P]. |

---

## 8. Performance techniques: evidence

### 8.1 Term representation and sharing

| Technique | Evidence | Measured effect |
|---|---|---|
| **Hash-consing into a DAG with u32 handles** | nanoda (`Ptr{raw:u32}`, `UniqueIndexSet`); con-ron (per-constructor arrays, 2×u32 app nodes, 8-byte slots); gruszka (hash-consed values, environments and spines) [P] | con-ron vs con-leche: **2.3x fewer instructions with the same algorithm** (3.85T vs 8.85T on Mathlib) [P]. The difference is representation, no RC and no Lean runtime. |
| Persistent vs scratch tiers (bit 31) | nanoda, con-ron [P] | Lets the frozen tier be shared across threads without locks; scratch is freed per declaration. |
| Struct-of-arrays per constructor | con-ron [P] | Applications are 85% of nodes, so an 8-byte app node is the dominant memory factor. con-ron live RSS is 4.4 GiB vs official 9.9 GiB [P]. |
| Epoch-stamped open addressing (O(1) clear) | con-ron `HashMap2` [P] | Makes per-declaration cache flushes cheap. |
| Context-free caches via typed canonical locals | palladium [P] | Caches stay valid across binder contexts; 2.83T. |
| Locally nameless with fvars named by de Bruijn *level* (plus type) | nanoda, con-leche [P] | Levels are stable under going under binders, so cache keys stay valid. Free-variable creation needs no fresh-name counter, which helps determinism and parallelism. |
| Pure de Bruijn, lazy shift (pointer+offset) | nanobruijn [P] | 4.71T, so not a clear win over locally nameless with levels. |
| Delayed substitution / closures | nanoclo [P] | 3.01T; it had soundness slips (2 wrong accepts). |

### 8.2 Evaluation strategy

| Technique | Evidence | Effect |
|---|---|---|
| **NbE / glued closures (smalltt, elaboration-zoo)** | smalltt README: NatConv10M takes smalltt 0.712 s vs Lean 61.1 s vs Agda 19.7 s; stlcSmall1M elaboration 8.7 s vs Coq 149 s vs Lean 615 s. Lean wins TreeConvM23 (0.001 s) thanks to approximate conversion shortcuts. https://github.com/AndrasKovacs/smalltt [P]; https://github.com/AndrasKovacs/elaboration-zoo [S] | In Lean kernels, every one of the top three arena entries (nano-lean, gruszka, sokonanoda) uses NbE, at 0.40–0.53T vs 2.6–5.8T for substitution-based Rust kernels [P]. sokonanoda (NbE, nanoda lineage) is 10.9x fewer instructions than nanoda; that is a correlation and not a controlled ablation [U]. |
| Krivine machine / lazy cClosure (Rocq style) | lazylean [P]; Rocq `kernel/cClosure.ml` https://github.com/rocq-prover/rocq/blob/master/kernel/cClosure.ml [S] | lazylean 5.53T, about nanoda level. |
| Call-by-need plus substitution fallback | kefir [P] | 2.58T on a single thread, the lowest memory (2.5 GiB). |
| **Lazy delta with good heuristics** | arena `perf/` tests (§1.5) [P] | Official and con-ron take 10–35 s where NbE kernels take 0.04–0.4 s, a 100–1000x algorithmic gap on pathological unfolding. gruszka has its own pathology (23.4 s on loop-unfolded-once) [P]. |
| Defeq shortcuts: pointer-equality first, union-find eq cache, failure cache, congruence-before-unfold for same-head apps, Nat offset and literal folding only when needed | nanoda `TcCache` [P]; gruszka architecture.md "Checking" [P] | Not individually measured. still-nanoda (a cache study) is 13% fewer instructions than nanoda [P]. |
| Level defeq | lean4lean `Theory/LevelSat.lean`: level equivalence is **coNP-hard** [P] | Needs a normaliser with a fast path; con-leche uses semantic level comparison (§4.1). |

### 8.3 Caching across declarations

| Technique | Evidence | Effect |
|---|---|---|
| Per-declaration flush (official, nanoda, con-ron) | [P] | Simple and easy to verify, but recomputes the same unfoldings and inferences for each of about 700k declarations. |
| **Sessions: keep caches across declarations, invalidated by a monotone declaration stamp** | gruszka "Sessions" (milestone 10): kept facts cost +1.4%, a new session +3.5%; namespace grouping [P] | gruszka 0.51T. Ablation numbers are only in the design doc's simulations [P]. |
| Persistent result cache keyed by dependency-closure hash | nano-lean `--cache` [P] | Incremental re-checking. This is what the FRO says 13M–50M-line projects need (2026-10-15 blog) [P]. |

### 8.4 Parallelism

| System | Evidence | Speedup |
|---|---|---|
| con-leche worker pool | PERF.md: 14.7 min at 1 job, 3.1 min at 4, 100 s at 8; +3.5% instructions [P] | 8.8x wall at 8 jobs |
| gruszka | 44 s at 1 worker, 13.6 s at 4, 8.4 s at 8; instructions 369G→375G [P] | 5.2x at 8 |
| nanoda | CPU÷wall = 3.3x at 4 threads [P] | 3.3x at 4 |
| Kontroli (Rust Dedukti) | "reduces the checking time using eight threads by up to 6.6x"; kernel 663 lines vs Dedukti's 3,470; parallel *parsing* did not pay off because of channel overhead. https://arxiv.org/abs/2102.08766 (CPP 2022) [P via abstract, S for details] | 6.6x at 8 |
| Official Lean | Elaboration-parallel since 4.17–4.19. Kernel declaration-parallel checking only in PR #16343 (open, 2026-11-08); `leanchecker --from-export` is single-threaded today [P] | Nightly 2026-11-14 is still 2575 s wall on 1 thread [P] |

Granularity. Mathlib has about 691k–702k declarations (con-leche PERF.md; gruszka README) [P]. A slowest single declaration takes about 0.7–3.7 s:
- con-leche: QuadraticModuleCat.hom_hom_associator, 0.734 s;
- gruszka on FLT: WeierstrassCurve.ellipticNet_four, 3.7 s [P].

So Mathlib parallelises almost embarrassingly. The critical path is the dependency DAG depth, plus the few multi-second declarations.

### 8.5 Memory management, hashing, allocation

| Topic | Evidence | Note |
|---|---|---|
| Refcounting cost | Lean alloc/RC symbols are 45–48% of con-leche's instructions and 25% of the official init-full profile [P] | A Rust arena with u32 handles and no per-node RC removes this whole category. |
| RC soundness | refcount overflow #14838, fixed with Koka-style sticky counts [P] | Arenas avoid this bug class too. |
| Allocators | con-ron: mimalloc by default (jemalloc and system as options) [P]; nano-lean: mimalloc plus bumpalo [P] | No published ablation found [U]. |
| Hashers | nanoda: rustc-hash 1.1 (FxHash) [P]; nano-lean: hashbrown [P]; con-ron: its own verified open addressing [P] | Nodes carry a precomputed 64-bit hash, so per-lookup hashing cost is small. lean4#15686 shows that weak *literal* hashing can be quadratic [P]. |
| Instruction-level | con-ron fat LTO + codegen-units=1: −11.6% on Init [P]; nano-lean and gruszka use PGO and `target-cpu=native` [P] | |

### 8.6 Big integers

| Library | Licence | Speed evidence |
|---|---|---|
| GMP via `rug` | LGPL | Fastest at large sizes; FFI overhead at small sizes (DRMacIver bench: mul at size 10, rug 18 ns vs malachite 3 ns) https://github.com/DRMacIver/rust-bigint-benchmarks/blob/main/benchmark-report.md [S] |
| malachite | LGPL-3.0 | About GMP level at large sizes. tczajka bench: e to 10M digits 3.69 s vs num-bigint 482 s https://github.com/tczajka/bigint-benchmark-rs [S]; https://www.malachite.rs/performance/ [S] |
| num-bigint | MIT/Apache | Karatsuba/Toom-3 only; 100x+ slower at millions of digits [S]. Used by nanoda, nano-lean and gruszka [P]. |
| dashu / ibig | MIT/Apache | Between num-bigint and malachite (DRMacIver bench) [S] |

Relevance:
- Mathlib's Nat literals are overwhelmingly small. The big-literal cost shows up in the arena's literal tests, in `decide`-heavy AI-generated proofs, and in issues like #15686.
- A rulean kernel needs (a) an inline small-int fast path and (b) a verified, permissively licensed bignum. The FRO also plans a verified bignum (hunt postmortem) [P].
- GMP and malachite (LGPL) are bad fits for a "pure Rust, verified" goal.

### 8.7 Other systems for calibration

| System | Number | Source |
|---|---|---|
| Metamath Zero (mm0-c) | set.mm translation (>34k proofs) in **195 ± 5 ms** single-threaded on a 3.9 GHz i7; a binary `.mmb` format designed for checking. metamath.exe takes about 8 s and smm 0.7 s on the same corpus. | https://arxiv.org/abs/1910.10703 [P via abstract/thesis, S for details] |
| "Carnap Ten Years Later" (2026) | mm0-zig reimplements mm0-c and repeats the under-200 ms result | https://arxiv.org/abs/2607.07722 [S] |
| Kontroli | Sequential Kontroli is faster than Dedukti on all datasets (e.g. 62.1% of Dedukti's time on Zenon); 6.6x with 8 threads | https://arxiv.org/abs/2102.08766 [S] |
| smalltt | 10–100x over Lean 4 and Agda elaboration/conversion on synthetic stress tests | smalltt README [P] |
| Agda, Rocq kernel performance | No 2024–2026 primary numbers collected in this pass | [U] |

Lesson from MM0: a format designed for checking (binary, pre-indexed, no parsing ambiguity) plus a tiny checker gets about 1–2 orders of magnitude over text-based checkers. The arena evidence matches: official parsing is 14–18% of its run [P], and gruszka packs to Susz first (1.9 s on M2) [P].

---

## 9. Where the time goes in Mathlib, and why the official kernel is slow

Per-phase breakdown of the official kernel, from the measurements above:

| Phase | Share or cost | Source |
|---|---|---|
| NDJSON parsing (official) | 1.66T of 11.83T (14%) in Round 09; ~306 instr/byte; 18.1% of Mathlib, 24.3% of Init on v4.33 exports | Zenodo parse-only [P]; con-leche PERF.md [P] |
| Allocation and RC (official) | about 25% of the init-full profile | con-leche PERF.md [P] |
| Per declaration (official) | 11.89M instructions per declaration on Mathlib, vs 5.60M on Init | con-leche PERF.md [P] |
| Single thread | 2575–2696 s wall vs 27–34 virtual min; `leanchecker` uses 1 core | arena [P] |
| No cross-declaration caches | infer and whnf caches flushed per declaration | official C++ kernel [S]; nanoda/con-ron mirror it [P] |
| Heuristic pathologies | 14–35 s single tests (§1.5) | arena perf/ [P] |
| Version improvements | v4.28.0 14.92T → nightly 9.82T (−34%) | arena [P] |

For comparison, the fastest kernels:
- nano-lean: about 0.57M instructions per declaration including parsing (0.40T ÷ ~700k), 20x below the official kernel [P, derived].
- gruszka: about 0.53M instructions per declaration at 1 worker (369G ÷ 702k) [P, derived].

Hot spots:
- Distribution: a few declarations dominate tail latency (see §8.4).
- Kinds: deep algebraic hierarchies (category theory associators, Weierstrass curves) and big `decide`/Nat literal computations.
- This is consistent with the perf/ microtests: deep structure projections, `ite` branch selection, `&&` short-circuit and unfold-before-literal.

What I did not find: a published per-function profile of the official kernel on full Mathlib, i.e. how its time splits among whnf, defeq, infer and instantiate [U]. con-leche PERF.md has the symbol-level RC share, but not a semantic split.

---

## 10. Implications for a 10x Rust kernel

### 10.1 Define the target precisely

| Baseline | Mathlib instructions | 10x target | Already beaten by |
|---|---|---|---|
| official v4.35.0, live arena | 12.10T | **≤1.21T** | nano-lean 0.40, gruszka 0.51, sokonanoda 0.53, mathgraph 0.91 (unsound) |
| official nightly 2026-11-14 | 9.82T | **≤0.98T** | the same four |
| official wall time (1 thread, 2696 s) | n/a | ≤270 s | **already met by con-ron (178 s) and con-leche (206 s)** on 4 threads; not by nanoda (442 s) |

- **Wall-clock 10x is already reached by verified kernels**, purely from parallelism against today's single-threaded leanchecker [P].
- That margin will shrink once lean4#16343 or #15569 lands.
- The spec should therefore state the 10x target in **total instructions, or single-core time**. Measured that way, 10x requires about **2.9x (vs v4.35.0) to 3.5x (vs nightly) fewer instructions than con-ron**, the best verified kernel. It also requires 2.5–3x *more* instructions than the best unverified Rust kernels use.

### 10.2 Which techniques buy the most (ranked by measured or inferred effect)

1. **NbE / closure-based evaluation with good lazy-delta and defeq heuristics.** The largest single factor.
   - The top three kernels all use it. The gap between them and substitution-based Rust kernels with the same kind of representation is about 5–14x.
   - On pathological cases it is 100–1000x.
   - con-ron's algorithm, inherited from the official kernel, is its main bottleneck [P/U attribution].
2. **A compact, hash-consed DAG with u32 handles, arenas and no RC.** About 2.3x, measured directly: con-ron vs con-leche, same algorithm [P].
   - It also removes the 25–48% RC/alloc overhead [P].
   - Memory falls from about 10 GiB to 2.5–5 GiB [P].
3. **Fast input**: a binary format, or a SIMD/zero-copy NDJSON parser streamed into the hash-cons tables.
   - It removes most of the official kernel's 14–18% parse share [P].
   - The nano-lean pipeline as a whole costs about 68 instr/byte, against the official parser alone at about 300 instr/byte [P, derived].
4. **Cross-declaration caching (sessions)** with a monotone invalidation stamp, plus a persistent dependency-hash cache for incremental checks.
   - The gain is large but only measured inside gruszka's design doc [P].
   - It is required anyway for 10M–50M-line AI projects (FRO blog) [P].
5. **Declaration-level parallelism.** 3–9x wall at 4–8 threads for about +3.5% instructions [P].
   - Necessary for wall-clock goals; it does nothing for the instruction metric.
6. **Low-level tuning.** Fat LTO with codegen-units=1 gave −11.6% [P]; PGO and `target-cpu=native` are also used [P]; mimalloc; precomputed node hashes. Together about 1.1–1.3x [U].
7. **Bignum.** Negligible on Mathlib, but it decides worst-case behaviour on literal-heavy AI proofs.
   - Needed: an inline small-int path, a verified pure-Rust bignum, and a full-width literal hash (lean4#15686) [P].

### 10.3 Realistic headroom

Over the official kernel (instructions):
- **Unverified**: about 25–30x is demonstrated today (nano-lean 30.6x vs v4.35.0, 24.6x vs nightly) [P].
- **Verified**: about 3.5x is demonstrated (con-ron).
- A rulean that keeps con-ron's level of verification but adopts techniques 1, 3 and 4 could plausibly reach **0.6–1.2T**, i.e. **10–20x over v4.35.0 and 3–6x over con-ron**. This is an estimate [U].
- Reaching 0.4T verified (nano-lean parity) is plausible in principle, but nobody has shown it [U].

Over con-ron:
- The headroom is the 8.7x gap to nano-lean, mostly algorithmic (NbE, sessions, heuristics) and partly in parsing.
- The cost is proof effort. con-ron already has a 3.3:1 Lean-proof-to-Rust ratio (388k lines over 116k), and con-leche 16:1. NbE and cross-declaration caches have more complex invariants than per-declaration substitution [P sizes; U effort].
- The Aeneas subset forbids closures, `std::collections`, `?` and `unsafe` [P]. An NbE kernel would have to encode closures as defunctionalised arena records, which con-ron's style already resembles.

### 10.4 Risks to the "accept exactly what official accepts" requirement

All points below are [P].

- **Verified kernels do not accept the same set as official.** con-leche, con-ron and con-agua:
  - decline native_decide, bv_decide, unsafe/partial and non-standard axioms (6 good tests plus Cedar);
  - make theorem bodies opaque, so they reject some proofs that official accepts by reducing a proof;
  - and accept *more* in places (semantic level comparison, proof-irrelevance fall-through, some large elimination, the And rescue).
- The arena itself has **30 "either" tests** where the reference behaviour is unspecified.
- Official behaviour changes between versions, through the renovation #14977 and opaque theorems #14896.
- Defeq checking in Lean is heuristic and incomplete. Different evaluation strategies can differ on timeouts and deep recursion: nanoda times out on eta-struct-major tests, and logos-kernel hit a recursion limit. So an NbE kernel matches official "acceptance" only up to resource limits.
- Recommendation: specify acceptance as
  1. identical verdicts on every non-"either" arena test, all of Mathlib, Std/core, Cedar, CSLib and the AI-project corpus;
  2. an explicit, versioned list of deliberate deviations;
  3. a fallback mode (e.g. `--compat`) that defers to the official kernel's verdict on declines.

### 10.5 Architecture sketch implied by the evidence

- **Input**:
  - Stream NDJSON (lean4export 3.1.0) and a binary format (Susz, blean or a new one) straight into hash-cons tables.
  - Parse in parallel by record ranges, keeping Kontroli's warning about channel overhead in mind.
- **Store**:
  - A con-ron-style frozen persistent tier, struct-of-arrays per constructor, u32 handles with a tier bit.
  - Precomputed hash, loose-bvar bound and fvar range per node.
  - Epoch-cleared open-addressed tables.
- **Evaluation**:
  - NbE with defunctionalised closures stored in a per-worker arena.
  - Glued (unfolded and folded) values for lazy delta.
  - Free variables by de Bruijn level, with their types.
- **Caches**:
  - Per-worker session caches stamped by declaration index, plus an on-disk result cache keyed by dependency-closure hash.
- **Parallelism**:
  - Declaration DAG scheduling over workers that share the frozen tier.
  - Target ≥5x wall at 8 threads.
- **Verification route**:
  - A con-leche-style executable specification and model.
  - An Aeneas refinement of the Rust (con-ron route), or a verified compiler to asm (con-agua route, about 1.13x con-ron's instructions).
  - ind-models-style translation validation to shrink the inductive-types part of the trusted base.
  - Budget for a proof corpus 3–16x larger than the code.
