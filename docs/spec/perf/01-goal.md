# 01. Goal and targets

## 01.1 The goal

rulean must be at least 10 times faster than each popular Lean 4 kernel. The goal applies to two uses of rulean:

1. **External check.** rulean reads an export and checks it, as on the Lean Kernel Arena.
2. **In-process kernel.** rulean is the kernel of `lean`, for example during `lake build Mathlib` (spec 09.6).

## 01.2 Popular kernels

A kernel is **popular** if Lean users run it outside the Arena and it has documentation for users. Four kernels are popular in November 2026:

| Kernel | Language | Why it is popular | Source |
|---|---|---|---|
| official, the stable release (v4.35.0 on the Arena) | C++ | It is the kernel of `lean`. `leanchecker` and `lean4checker` use it. | https://github.com/leanprover/lean4 |
| official nightly (2026-11-14 on the Arena) | C++ | It is the newest official kernel. On Mathlib it uses 19% fewer instructions than the stable release. | https://arena.lean-lang.org/checker/official-nightly/ |
| lean4lean | Lean | It is the kernel of the Lean4Lean project and paper. | https://github.com/digama0/lean4lean, https://arxiv.org/abs/2403.14064 |
| nanoda | Rust | It is the oldest external checker. The book "Type checking in Lean 4" uses it. | https://github.com/ammkrn/nanoda_lib |

The kernels at the top of the Arena (nano-lean, gruszka, sokonanoda) are not popular by this rule. They are new in 2026 and have few users. They show what is possible, so this spec uses them as a reference (01.6).

## 01.3 The measure

**External check.** The measure is the measure of the Arena (spec 08.7.1): the instructions in user mode over all threads, from `perf stat -e instructions:u`, with the parse included. One virtual second is 6.0 G instructions. "10 times faster" means "at most one tenth of the instructions on the same export". The Arena publishes the counts of the popular kernels in `results.json`, so the targets below come from that file.

The source of the targets is the Arena `results.json` of 2026-11-25 21:04:48 UTC, revision 04c2e955 (https://github.com/leanprover/lean-kernel-arena/commit/04c2e955ce32a43e0f3e3c0a473c25215dd2afea).

**Local measure.** A Mac has no `perf`. On macOS, `/usr/bin/time -l` gives the instructions retired, with the system calls included. This count is not the Arena count. It is good for a ratio between two kernels on the same machine and the same export. `scripts/kbench.sh` (07) runs rulean and the popular kernels of the toolchain on one export and gives these ratios.

**In-process.** The measure is the time of the kernel inside `lean`, summed over all `lean` processes of the build. The dual-kernel build measures the two kernels on the same declarations in the same process (spec 09.6.3). For rulean the time is the conversion of the declarations, the mirror, the check and the conversion of the results. For C++ it is the time of the C++ kernel.

**Wall time.** Instructions do not show threads. A user waits for the wall time. So there is also a wall-time target, with the threads that the Arena gives to each kernel.

## 01.4 Targets

Each target is one tenth of the best popular kernel on that corpus. On each corpus the best popular kernel is nanoda, except for the `perf/` tests.

| ID | Corpus | Measure | Best popular | Target | Leaders (reference) |
|---|---|---|---|---|---|
| G1 | Mathlib (5.9 GB, v4.36.0) | instructions | nanoda 5773 G | at most 577 G | nano-lean 395 G, gruszka 461 G |
| G2.a | Init | instructions | nanoda 223.8 G | at most 22.4 G | nano-lean 24.3 G, gruszka 24.9 G |
| G2.b | Std | instructions | nanoda 345.6 G | at most 34.6 G | gruszka 40.1 G, nano-lean 40.3 G |
| G2.c | CSLib | instructions | nanoda 1547.8 G | at most 154.8 G | nano-lean 141.4 G, gruszka 164.3 G |
| G2.d | Cedar | instructions | nanoda 454.5 G | at most 45.4 G | gruszka 62.0 G, nano-lean 63.2 G |
| G3 | the 40 `perf/` tests that all four popular kernels pass | sum of instructions | official nightly 673.3 G | at most 67.3 G | nano-lean 58.4 G, gruszka 76.3 G |
| G4 | `lake build Mathlib`, in-process | kernel time | C++ kernel 3829 s (09.6.3) | at most 383 s | none |
| G5 | Mathlib, 4 threads | wall time on the Arena machine | nanoda 377 s | at most 37.7 s | gruszka 29 s, nano-lean 36 s |

Notes on the table:

- G2.a and G2.b are stricter than the leaders on Init and Std. So G2 asks for more than any kernel does today.
- In G3, the five `perf/` tests that a popular kernel fails or does not finish are not in the sum. They still have the rule P1.d: no `perf/` test above 1 virtual second.
- The `perf/` tests are summed, and not compared one by one. On a small test the start of the process takes most of the count. For example, `perf/repeated-subproblem` is 0.20 G on the official kernel and 0.01 G on nanoda, and the start of a process is about 0.01 G.
- G4 uses the C++ time of run 1 of the workflow `mathlib` (45616391280). This is the only popular kernel that runs in-process.
- G5 uses the wall time of the Arena run. The Arena gives 4 threads to nanoda, nano-lean and gruszka, and 1 thread to the official kernel.

## 01.5 What the goal does not mean

- **Not 10 times faster than the leaders.** One tenth of nano-lean on Mathlib is 39.5 G instructions, which is 6.7 instructions for each byte of the export. A parse of JSON uses about 1 to 3 instructions per byte at best (simdjson, [U] for the exact number on this input). The check of 700 k declarations would then have about 40 k instructions for each declaration. We do not know a way to do that, so it is not a target.
- **Not at the cost of verdicts.** A change that makes rulean faster and changes one verdict on the conformance corpus (spec 11) is not merged.
- **Not at the cost of the proofs.** The core stays in the Aeneas subset. The proof work (spec 10) may lag the code, but each new cache and each new rule has its lemma in the twin before the release (spec 08.8 rule 4).

## 01.6 Reference targets

These are not part of the goal. They show the position against the leaders.

| ID | Corpus | Target |
|---|---|---|
| S1 | Mathlib | at most 395 G, the count of nano-lean |
| S2 | Init and Std | at most 24.3 G and 40.1 G |

## 01.7 Starting point

On the Init export, rulean engine R uses 1.7 times fewer instructions than the official kernel, and about as many as nanoda (03.2). To reach G2.a, rulean must use 10.8 times fewer instructions: the check about 13 times fewer and the parse about 6 times fewer (04.10). To reach G4, the in-process kernel must use 18.2 times less time (03.6). These factors are larger than tuning can give. So the plan (07) changes the design of the check, the parse and the in-process kernel (04, 05, 06).
