# 01. Research summary (as of 2026-11-21)

This document summarises the research that the specification depends on. The four full reports are in `research/`:

| Report | Scope | Lines |
|---|---|---|
| `research/A-lean-kernel.md` | the official kernel: source, exact semantics, versions, incidents, toolchain, Arena data, a semantics checklist | 792 |
| `research/B-kernels-and-performance.md` | the other Lean kernels, the Arena rankings, performance techniques and their evidence | 731 |
| `research/C-formal-verification.md` | metatheory, verified kernels in Lean and other systems, Rust verification tools, AI-assisted proof engineering | 624 |
| `research/D-runtime-formats-rust.md` | the Lean object model, `.olean`, lean4export, plugging into Lean, pure-Rust crates, the "no C" question | 682 |

Claims carry tags as in the reports. **[P]** means a primary source (code, issue, release note, author's post, raw data). **[S]** means a secondary source only. **[U]** means unverified or an inference. A reference such as `A§1.8` means report A, section 1.8.

## 01.1 Main findings

1. **10x fewer instructions than the official kernel is already done, without verification.** On Mathlib, nano-lean uses 30.6 times fewer instructions than official v4.35.0, gruszka 23.6, sokonanoda 22.9 [P] (A§5.2). All three use NbE.
2. **The best verified kernel is at 3.5x.** con-ron (Rust, refined through Aeneas to con-leche's model) uses 3.47 T against the official 12.10 T [P] (A§5.2). So rulean needs about 2.9 times fewer instructions than con-ron, with the same kind of proof (B§10.1).
3. **Wall time 10x is already met by verified kernels through threads.** con-ron takes 178 s on 4 threads, the official checker 2,696 s on 1 thread [P]. So P1 is stated in instructions (02.6).
4. **No verified kernel accepts every Lean program.** con-leche, con-ron and con-agua decline 9 definite Arena tests, Cedar (`native_decide`), unsafe and partial declarations, and make theorems opaque [P] (A§8, B§10.4). The official kernel still unfolds theorems [P by code reading] (A§1.3).
5. **The official kernel is a moving target.** Its semantics changed in v4.35.0, v4.37.0-rc1 and on master in the last two months [P] (A§1.15). Its instruction count fell 34% from v4.28.0 to the 2026-11-14 nightly [P] (B§9).
6. **Definitional equality in Lean is heuristic and not transitive** [P] (A§1.5, lean4#14806, lean4#12520). So "the same verdict as official" cannot be proved today. It is tested (02.2, P3 rules).
7. **A complete consistency proof exists for one production kernel.** con-leche proves that every environment it accepts has a model in ZF with an ω-chain of Grothendieck universes [P] (C§1.4). The declarative route (lean4lean) still has open `sorry`s [P] (C§1.2).

## 01.2 The official kernel

- `src/kernel` on master ab8894fb is 35 files and 8,049 lines. The largest files are `inductive.cpp` (1,415) and `type_checker.cpp` (1,303) [P] (A§1.1).
- It also trusts the Lean runtime: the object model and reference counts (`object.cpp` 3,120 lines, `lean.h` 3,901), bignums (`mpz.cpp` and GMP at least 6.3.0), hashing, sharing and compacted regions [P] (A§1.2).
- The definitional equality order, the reduction rules, the 15 Nat operations, the level algorithms and the inductive checks are listed in A§1.6 to A§1.12. The checklist in A§7 is the basis of 05 and 06.
- Since v4.35.0 (lean4#14953) the kernel never runs compiled code. `native_decide` makes an axiom `_native.….ax` [P] (A§1.7).
- The kernel matches the primitive Nat and String operations **by name** and does not check their definitions. `lake check` pins them for that reason [P] (A§1.7). rulean pins them inside the kernel (05.8).
- Releases: v4.36.0 is the latest stable (2026-11-16), v4.37.0-rc1 the latest release candidate (2026-11-18) [P] (A§3).
- Kernel renovation is planned in lean4#14977: complete level comparison, explicit inductive feature flags, and a new export format [P] (A§3).

## 01.3 Soundness incidents in 2026

| Event | Date | Facts | Source |
|---|---|---|---|
| Opus 4.6 audit | 2026-03 | 7 Rocq kernel bugs and 2 nanoda bugs; no false proof in Lean | [P] WW (A§2.4) |
| #14576, CVE-2026-72844 | 2026-07-28 | wrong-structure projections through phantom parameters in nested inductives gave an axiom-free proof of `False`; reachable only through raw `addDecl`; first fixed in v4.32.2; nanoda accepted it through a separate bug | [P] PM1 (A§2.1) |
| bug hunt | 2026-07-30 to 08-20 | #14613, #14616, #14806 (cache order dependence), #14807 and #14843 (stuck `is_prop`), #14582, #14808; runtime: refcount overflow #14838, GMP 6.3.0 #14833, numeral bound #14849; shipped in v4.33.1 | [P] PM2 (A§2.2) |
| runtime fixes | v4.35.0 | #15241 use-after-free, #15289 count wrap, #15288 cross-thread UB; "kernels that are not based on the Lean runtime were not affected" | [P] (A§2.3) |
| verified kernels ship | 2026-10-15 | nanoda, lean4lean, con-leche and con-ron bundled with `lake check --paranoid` | [P] VK (A§2.4) |
| Hales guest post | 2026-10-09 | "no complete, public relative-consistency proof covering Lean abstract type theory"; wants a clean-room kernel; warns about AI-planted bugs | [S] (A§2.4) |

Lessons for rulean: hostile input is real (12); caches must not depend on order (08.5); runtime bugs (reference counts, GMP) disappear with a handle store and an own bignum (04).

## 01.4 The Lean Kernel Arena

- Live run of 2026-11-21 (arena commit 2d6b1ff6): 37 checkers and 265 tests (145 accept, 90 reject, 30 either) [P] (A§5.1).
- The Zenodo round of 2026-09 (DOI 10.5281/zenodo.22944094) had 26 checkers and 219 tests [P].
- The metric is user-space instructions over all threads. Virtual time is instructions divided by 6.0 G per second [P].
- Mathlib export: 5.9 GiB, 112.1 M lines, Lean 4.36.0 [P].

Mathlib, live run [P] (A§5.2):

| Checker | Language | Instructions | Ratio to official v4.35.0 | Wall | Memory | Notes |
|---|---|---|---|---|---|---|
| nano-lean | Rust | 0.40 T | 30.6 | 50 s (4 threads) | 5.0 GiB | NbE |
| gruszka | Rust | 0.51 T | 23.6 | 32 s | 2.4 GiB | NbE, binary input |
| sokonanoda | Rust | 0.53 T | 22.9 | 54 s | 5.0 GiB | NbE |
| mathgraph | Rust | 0.91 T | 13.3 | 179 s | 6.2 GiB | 8 incorrect results |
| kefir | Rust | 2.58 T | 4.7 | 430 s (1 thread) | 2.5 GiB | |
| con-ron | Rust | 3.47 T | 3.5 | 178 s | 4.4 GiB | verified (Aeneas) |
| con-agua | x86-64 | 3.93 T | 3.1 | 167 s | 11.6 GiB | verified compiler |
| nanoda | Rust | 5.78 T | 2.1 | 442 s | 6.0 GiB | |
| con-leche | Lean | 6.14 T | 2.0 | 206 s | 4.8 GiB | verified |
| official nightly 2026-11-14 | C++ | 9.82 T | 1.23 | 2,575 s | 9.9 GiB | |
| official v4.35.0 | C++ | 12.10 T | 1.0 | 2,696 s | 9.9 GiB | |

lean4lean fails the live Mathlib test ("unknown constant instDecidableEqBool", from the new `Decidable` structure). In the 2026-09 round it took 39.9 virtual minutes and 9.3 GiB [P] (A§5.2, A§5.3).

The official parser alone costs 1.66 T on Mathlib, about 14% of the official run [P] (A§5.4).

## 01.5 Performance techniques

Ranked by evidence (B§10.2):

1. **NbE with glued values and good lazy delta.** The top three kernels use it. On the Arena `perf/` tests the official kernel takes 14 to 35 s where NbE kernels take 0.04 to 0.4 s [P] (B§1.5, B§8.2). smalltt shows the same gap outside Lean [P].
2. **A handle store with no reference counts.** con-ron against con-leche, same algorithm: 2.3 times fewer instructions [P]. Allocation and reference counting are 25% of the official profile and 45 to 48% of con-leche's [P] (B§8.5).
3. **Fast input.** Binary formats and small parsers. MM0 checks set.mm in 195 ms with a format designed for checking [P] (B§8.7).
4. **Sessions** (caches across declarations, with a monotone stamp). Measured only in gruszka's design doc [P] (B§8.3).
5. **Declaration-level parallelism.** 5 to 9 times wall time at 8 threads for about +3.5% instructions [P] (B§8.4). Official parallel kernel checking is still open (lean4#16343) [P].
6. **Build tuning.** Fat LTO and one codegen unit gave −11.6% for con-ron on Init [P].

The official kernel spends about 11.9 M instructions per Mathlib declaration, against about 0.5 M for the fastest kernels [P, derived] (B§9).

## 01.6 Metatheory and verified Lean kernels

- **Carneiro's thesis** (2019) gave the type theory of Lean and its soundness by a model in ZFC with inaccessibles. It also showed that algorithmic definitional equality is not transitive and that subject reduction fails. Its unique-typing argument has a known error: the stratification is not closed under substitution [P] (C§1.1).
- **lean4lean** (Carneiro, TYPES 2025, arXiv 2403.14064) ports the kernel to Lean and starts the metatheory. Key lemmas are still `sorry`: unique typing, Church–Rosser, `inductDecl`. `lean4lean-model` has `consistency` as `sorry`. Level equivalence is coNP-hard (`LevelSat`) [P] (C§1.2).
- **New papers.** "Definitional Inversion, Without Normalisation" (arXiv 2607.13662, 2026-07) and "Reflections on Trusting Lean" (arXiv 2610.30433, 2026-10), which shows that a second-order arithmetic formula is provable in ZFC with ω inaccessibles iff its Lean type is inhabited [P] (C§1.3).
- **con-leche** (leanprover/con-leche). A Lean kernel in Lean, written by Claude under Joachim Breitner. The kernel is about 15 k lines in a 365 k line repository. Its theorems `main_json_model`, `model_exists` and `main_no_False` show that every accepted environment has a model in `SetTheory V` (ZF⁻ with an ω-chain of Grothendieck universes). `carneiro_implies_conleche` builds `SetTheory V` from ω inaccessibles. Partial correctness only [P] (C§1.4).
  - It declines `native_decide`, `bv_decide`, unsafe, partial, and six good Arena tests (cedar, level-index-out-of-order, sparse-name-index, 034_letTypeDep, 035_letRed, 107_proofIrrelevanceUnderBinder).
  - It makes theorems opaque.
  - It accepts more than the official kernel in places: semantic level comparison, proof irrelevance fall-through, some large elimination, the `And` rescue [P] (B§10.4).
- **con-ron** (leanprover/con-ron). 116 k Rust lines (verified core 41.5 k) and 388 k Lean lines. A Lean twin refines con-leche (Theorem 1). The Aeneas translation of the Rust code refines the twin (Theorem 2, `lockstep` tactic). The capstone `model_exists` has a hypothesis `ParallelAll` as the contract of the thread pool. Representation: `u32` handles with a tier bit, per-constructor arrays, epoch-cleared `HashMap2`. About 3 proof lines per Rust line. It uses mimalloc, which is C [P] (B§4.2, C§1.4).
- **con-agua** (leanprover/con-agua). con-leche's algorithm in a first-order language, compiled to x86-64 by a verified compiler against the Kraken semantics. Termination is proved. Threads are not verified. A small C harness [P] (B§4.3).
- **ind-models** (nomeata/lean-inductive-models). Builds a model for each inductive declaration. It rejected the bad recursors of the bug hunt [P] (C§1.5).

## 01.7 Rust verification tools

| Tool | Fit for rulean | Source |
|---|---|---|
| **Aeneas + Charon** | the main tool: Rust to pure Lean, refinement proofs in Lean; used by con-ron and SymCrypt (16.7 k Rust lines, 237 k Lean lines, "a few dollars per line"); subset limits: no closures, no `?`, no `std::collections`, no `unsafe` | [P] C§3.1; con-ron `AENEAS_FINDINGS.md` |
| **Verus** | islands with concurrency and `unsafe` (the thread pool, K1); specifications are not in Lean | [P] C§3.3 |
| **Kani** | bounded checks of `unsafe` code and SIMD equivalence (K3, K4) | [P] C§3.6 |
| hax | Lean backend now goes through Aeneas | [P] C§3.2 |
| Creusot, RefinedRust, Gillian-Rust, Prusti | not Lean-based; not chosen | [P] C§3.4 to C§3.8 |
| RustCompCert | verified compiler for a Rust subset; not real Rust | [P] C§3.9 |

No verified compiler exists for the Rust that rulean is written in. rustc and LLVM stay in the trusted base. The mitigation is diversity with con-agua (10.8).

## 01.8 Verified kernels in other systems

| System | What is proved | Source |
|---|---|---|
| MetaRocq safe checker (JACM 2025) | sound and complete with respect to PCUIC typing; assumes strong normalization | [P] C§2 |
| McTT (ICFP 2025) | fully verified kernel for MLTT with NbE | [P] C§2 |
| Candle, CakeML checkers | HOL Light clone and proof checkers verified to machine code | [P] C§2 |
| Metamath Zero | small fast checker; 195 ms on set.mm | [P] B§8.7 |
| Isabelle metalogic checker | proof checker for Isabelle's logic, in the AFP | [P] C§2 |
| Agda Core | correct-by-construction checker for a core of Agda | [P] C§2 |
| Lean4Less and lean2dk | Lean to Lean⁻ and to Dedukti | [P] C§2 |

The lesson: a full verified kernel is possible, but every one of them either assumes normalization, covers a subset, or is slow. con-leche's model theorem avoids normalization because it proves only the accepting direction (10.2.1).

## 01.9 Runtime and "run every Lean program"

- A Lean program runs on the Lean runtime and the compiler, not on the kernel. Replacing those means the IR interpreter, the C backend, about 1,000 `@[extern]` primitives, the task and IO runtime, libuv, GMP and CaDiCaL [P] (D§8, D§12.1). That is a different project, much larger than a kernel.
- For a kernel, "every Lean program" means: every environment that a Lean program can produce is checked with the official verdict, and Lean can run with rulean as its kernel (02.2, P2).
- In-process integration needs the Lean object ABI in Rust: ownership rules, sticky reference counts, persistent objects in mapped regions [P] (D§4.2).

## 01.10 Formats and pure-Rust building blocks

- **`.olean`**: an 88-byte header and a compacted object graph with absolute pointers to `base_addr`. Version 2 and 3 in v4.36, version 4 in v4.37.0-rc1. Three parts with the module system (`.olean`, `.olean.server`, `.olean.private`); theorems are statements only in `.olean`. No structural validation in Lean (I#16542) [P] (D§5).
- **Cached data changes between versions.** v4.37.0-rc1 has a new 32-bit expression hash (PR#16107) and full-width literal hashes (PR#16146) [P] (D§3.4).
- **lean4export 3.1.0**: NDJSON with name, level and expression tables [P] (A§4.1, D§7).
- **Existing Rust readers**: leangz (version 4) and olean-export (version 2 only; 18 s for Mathlib against 1,526 s for lean4export) [P] (D§6).
- **Crates that compile C**: mimalloc, jemalloc, snmalloc, rpmalloc, rug and GMP, and blake3 without `pure`. Pure-Rust options: hashbrown, rustc-hash, foldhash, bumpalo, rayon, memmap2, num-bigint, dashu, malachite (LGPL), talc, rlsf [P] (D§9).
- **Rust `std` links the platform C library** and, in the shipped `std`, some compiler-rt C intrinsics. `panic = "abort"` removes the unwinder. `-Z build-std` can avoid the C intrinsics [P] (D§10).

## 01.11 Corpora and scale

| Corpus | Size | Source |
|---|---|---|
| Mathlib | 296,300 theorems and 142,131 definitions (mathlib.org); about 700 k kernel declarations; 5.9 GiB export | [P] A§6 |
| CSLib | 2.3 GB export | [P] D§11.2 |
| FLT (Anthropic) | about 13 M lines, 1,052,234 declarations, 37.8 GB export; nanoda took about 30 min on 16 threads and 40 GB | [S] B, C |
| RH project (Alpöge) | about 17.5 M lines, 175,187 modules, about 1.06 M declarations | [S] D§11.1 |

AI-made corpora are already 5 to 7 times the size of Mathlib in lines [U] (D§11.1). Throughput and memory per declaration decide the user experience at that scale.

## 01.12 Corrections to older notes

Report A§9 audits section 1.2 of `Spec/2148/01-research-2026.md` claim by claim. The main corrections:

- v4.36.0 is stable and v4.37.0-rc1 is out. v4.35.0 is not the latest.
- The Arena has 265 tests (145/90/30) and 37 checkers, not "127 good / 72 bad".
- The nanoda and lean4lean timings in the old notes match neither the round nor the live data.
- #14576 also affected v4.32.0 and v4.32.1. The first fixed release is v4.32.2.
- comparator#68 is fixed, comparator#85 was withdrawn as a false report, and RFC lean4#15800 was closed as not planned. The standalone comparator is deprecated in favour of `lake comparator`.
- The kernel still unfolds theorems, despite lean4#12973.

## 01.13 Bibliography

### Blog posts and announcements

- de Moura, "Who watches the provers", 2026-03-16. https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/
- de Moura, "Postmortem for kernel soundness bug #14576", 2026-08-01. https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/
- de Moura, "Postmortem for the kernel soundness bug hunt", 2026-08-24. https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/
- de Moura, "Lean now ships with verified kernels", 2026-10-15. https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/
- Hales, guest post on Tao's blog, 2026-10-09. https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/
- oss-security advisory for #14576, 2026-08-02. https://www.openwall.com/lists/oss-security/2026/08/02/1
- CVE-2026-72844 follow-up, 2026-10-26. https://www.openwall.com/lists/oss-security/2026/10/26/2
- Microsoft Research, SymCrypt in Rust with Aeneas. https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/
- Anthropic, formalizing Fermat's Last Theorem. https://www.anthropic.com/research/formalizing-fermats-last-theorem
- FRO roadmap Year 4 Part 1. https://lean-lang.org/fro/roadmap/y4-1/

### Papers

- Carneiro, *The Type Theory of Lean*, MSc thesis, CMU, 2019. https://github.com/digama0/lean-type-theory/releases
- Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean", TYPES 2025, LIPIcs 384. https://arxiv.org/abs/2403.14064
- Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich, "Definitional Inversion, Without Normalisation", 2026. https://arxiv.org/abs/2607.13662
- Bresolin, Mamino, "Reflections on Trusting Lean", 2026. https://arxiv.org/abs/2610.30433
- Ho, Protzenko, "Aeneas: Rust Verification by Functional Translation", ICFP 2022. https://arxiv.org/abs/2206.07185
- Ho, Protzenko et al., "Sound Borrow-Checking for Rust via Symbolic Semantics", ICFP 2024. https://arxiv.org/abs/2404.02680
- Ho et al., "Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean", 2026. https://arxiv.org/html/2609.15648v1
- Experience report on Rust to Lean with AI provers, 2026. https://arxiv.org/abs/2605.30106
- Lattuada et al., "Verus: A Practical Foundation for Systems Verification", SOSP 2024. https://dl.acm.org/doi/10.1145/3694715.3695952
- Gäher et al., "RefinedRust", PLDI 2024. https://dl.acm.org/doi/10.1145/3656422
- Ayoun et al., "A Hybrid Approach to Semi-automated Rust Verification" (Gillian-Rust), PLDI 2025. https://dl.acm.org/doi/10.1145/3729289
- "Verifying the Rust Standard Library", NFM 2026. https://arxiv.org/html/2606.17374v1
- RustCompCert, 2026. https://arxiv.org/abs/2602.07455
- MetaRocq safe checker, JACM 2025. https://dl.acm.org/doi/10.1145/3706056
- McTT, ICFP 2025. https://dl.acm.org/doi/10.1145/3747511
- Candle, ITP 2022. https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.3
- Carneiro, "Metamath Zero", 2019. https://arxiv.org/abs/1910.10703
- "Carnap Ten Years Later", 2026. https://arxiv.org/abs/2607.07722
- Färber, "Safe, Fast, Concurrent Proof Checking for the lambda-Pi Calculus Modulo Rewriting" (Kontroli), CPP 2022. https://arxiv.org/abs/2102.08766
- Agda Core, APLAS 2024. https://link.springer.com/chapter/10.1007/978-981-97-8943-6_4

### Systems and repositories

- Lean 4: https://github.com/leanprover/lean4 (master ab8894fb read on 2026-11-21)
- Lean Kernel Arena: https://arena.lean-lang.org/ and https://github.com/leanprover/lean-kernel-arena ; Round 2026-09: https://zenodo.org/records/22944094
- lean4export: https://github.com/leanprover/lean4export
- External kernels in the Lean reference: https://lean-lang.org/doc/reference/latest/External-Kernels/
- con-leche: https://github.com/leanprover/con-leche (proof idea: https://leanprover.github.io/con-leche/con-leche-proof-idea.html)
- con-ron: https://github.com/leanprover/con-ron (`OVERVIEW.md`, `AENEAS_FINDINGS.md`)
- con-agua: https://github.com/leanprover/con-agua ; Kraken: https://github.com/sgraf812/kraken
- ind-models: https://github.com/nomeata/lean-inductive-models
- lean4lean: https://github.com/digama0/lean4lean ; lean4lean-model: https://github.com/digama0/lean4lean-model
- nanoda: https://github.com/ammkrn/nanoda_lib
- nano-lean: https://github.com/sdiehl/nano-lean
- gruszka: https://github.com/jasisz/gruszka
- Ix: https://github.com/argumentcomputer/ix
- metalean: https://github.com/intgrah/metalean
- Lean4Less: https://github.com/Deducteam/Lean4Less
- smalltt: https://github.com/AndrasKovacs/smalltt
- Aeneas: https://github.com/AeneasVerif/aeneas ; Charon: https://github.com/AeneasVerif/charon
- Verus: https://github.com/verus-lang/verus ; Kani: https://github.com/model-checking/kani ; hax: https://github.com/cryspen/hax ; Creusot: https://github.com/creusot-rs/creusot
- leangz: https://github.com/digama0/leangz ; olean-export: https://github.com/sdiehl/olean-export
- lean-sys: https://crates.io/crates/lean-sys
- bigint benchmarks: https://github.com/tczajka/bigint-benchmark-rs
- Rust RFC 3873 (build-std context): https://rust-lang.github.io/rfcs/3873-build-std-context.html

Lean issue and pull request numbers in this specification refer to https://github.com/leanprover/lean4/issues/N.
