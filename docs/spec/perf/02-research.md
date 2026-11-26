# 02. Research: fast kernels and their techniques

This section adds to research B (`docs/spec/research/B-kernels-and-performance.md`). It covers the kernels and the papers that B does not cover, and it gives the newer Arena numbers. Each fact has a source. [U] marks a fact that we did not check.

## 02.1 The Arena on 2026-11-25

Source: https://arena.lean-lang.org/results.json, revision 04c2e955. The Arena has 37 checkers and 45 `perf/` tests.

| Checker | Mathlib instructions | Wall | Threads | Kind |
|---|---|---|---|---|
| nano-lean v0.4.2 | 394.9 G | 36 s | 4 | NbE, Rust |
| gruszka 0.2.0 | 460.8 G | 29 s | 4 | NbE, Rust |
| sokonanoda | 527 G | 46 s | 4 | NbE, Rust |
| rpylean | 578 G | 130 s | ? | RPython |
| con-ron | 3473.9 G | 149 s | 4 | substitution, Rust, verified |
| nanoda | 5773.3 G | 377 s | 4 | substitution, Rust |
| official nightly 2026-11-14 | 9815.1 G | 1891 s | 1 | substitution, C++ |
| official v4.35.0 | 12095.3 G | 2234 s | 1 | substitution, C++ |
| lean4lean | 14543.2 G | 1937 s | 1 | substitution, Lean |

Changes since research B (2026-11-21):

- lean4lean now accepts Mathlib. In B it rejected Mathlib because of a version mismatch.
- rpylean is new. It is a kernel in RPython, and it uses 578 G instructions on Mathlib. So the language is not the main factor. The algorithm is the main factor.

## 02.2 How the Arena measures

Source: https://github.com/leanprover/lean-kernel-arena (`lka.py` and the workflows).

- The time column is virtual time: the instructions of `perf stat -e instructions` divided by 6.0 G per second.
- The runner is `nscloud-ubuntu-22.04-amd64-8x16` (8 vCPU, 16 GB). The runner has a virtual PMU, so `perf` can count instructions.
- The limit for each test is 3 times the wall time of the official kernel. On Mathlib the limit is 4120 s.
- The order of the ranking is: wrong accepts, then wrong rejects, then the time on Mathlib.

## 02.3 The official kernel outside the Arena

| Run | Time | Source |
|---|---|---|
| `lean4checker --fresh Mathlib`, October 2023 | 21 min 15 s wall, 1201 s user, 1 core | https://leanprover-community.github.io/archive/stream/113488-general/topic/Lean4Lean.3A.20Lean.204.20kernel.20in.20Lean.html |
| Mathlib, Batteries and Lean, Lean4Lean paper | 44.54 min, 1 thread, i7-1255U | https://arxiv.org/abs/2403.14064, figure 2 |
| RH proof export, 61.6 GB, 1.47 M declarations, `leanchecker` | 48 h 3 min, 82.6 GiB | https://math.mit.edu/~drew/grh/ |
| the same, with a tuned allocator | 9 h 8 min | the same page |
| the same, nanoda on 80 threads | 27 min 42 s | the same page |
| the same, con-leche on 64 threads | 3 min 15 s | the same page |

Two facts from this table are important for rulean:

1. The allocator alone made `leanchecker` 5 times faster on a large export. Allocation is a large cost in the official kernel. rulean has no allocation in the hot loop by rule (spec 08.8 rule 1), but engine F still calls `malloc` (03.3).
2. The kernels that scale to many threads finish the RH export in minutes. The official kernel uses one thread.

## 02.4 lean4lean

Source: https://arxiv.org/abs/2403.14064.

| Package | lean4checker | lean4lean | Ratio |
|---|---|---|---|
| Lean | 37.01 s | 44.61 s | 1.21 |
| Batteries | 32.49 s | 45.74 s | 1.40 |
| Mathlib | 44.54 min | 58.79 min | 1.32 |

lean4lean follows the official algorithm in Lean. It is about 30% slower than the official kernel. On the Arena it uses 1.20 times the instructions of the official stable kernel on Mathlib.

## 02.5 nanoda

Source: the code at commit 0da9f98, https://github.com/ammkrn/nanoda_lib.

- Terms are in a DAG of interned tables (`IndexSet`) for names, levels, expressions, strings and big numbers. A `Ptr` is a 32-bit index. Bit 31 selects the persistent DAG of the export or the temporary DAG of one checker.
- Bound variables are de Bruijn indices. Each expression caches its loose bound variables and a flag for free variables.
- The caches are: infer (checked and unchecked), whnf, whnf_core, a pair cache for equality, a failure cache for lazy delta, and caches for instantiate, abstract and substitution. The caches are cleared after each declaration.
- Nat literals use `num-bigint`.
- The threads take declarations from an atomic counter. Each declaration sees only the prefix of the environment before it.

nanoda has the same design as rulean engine R: substitution with hash-consed terms and caches per declaration. Its count is near the count of rulean (03.2). This agrees with the profile of rulean (03.3): the cost is in the design, not in small details.

## 02.6 The leaders

### 02.6.1 nano-lean

Source: https://github.com/sdiehl/nano-lean and the Arena page.

- de Bruijn indices and NbE. Each value keeps its normal form after the first computation.
- A cache for each declaration, keyed by a hash of its dependency closure. A second run checks only the declarations whose closure changed.
- The README gives Mathlib (718 k declarations) in 57.4 s with 1 thread on an Apple M5, and 16.7 s with 10 threads.
- mimalloc and bumpalo for memory.

### 02.6.2 gruszka

Source: https://github.com/jasisz/gruszka and the Arena file `checkers/gruszka.yaml`.

- NbE over arenas for each worker. Values, environments and spines are hash-consed. A value caches its weak head form and its type.
- An argument that the check does not read is not evaluated. `casesOn` reduces only the major premise.
- Sessions for each worker keep the work of earlier declarations.
- Its own binary input format, Susz, which it packs from NDJSON first.
- Values that a whnf call makes are freed inside the call. After 2^26 values, a call-by-need machine continues the work.
- Research B §8.4: 44 s with 1 worker, 13.6 s with 4, 8.4 s with 8.

### 02.6.3 sokonanoda

Source: https://github.com/intgrah/sokonanoda. It is NbE in the nanoda family. It uses 10.9 times fewer instructions than nanoda on Mathlib (527 G against 5773 G). The two kernels have a different algorithm, so this number is a correlation and not a test of one change [U].

## 02.7 Outside Lean

| System | Fact | Lesson | Source |
|---|---|---|---|
| smalltt | NatConv10M in 0.712 s, Agda 19.7 s, Lean 61.1 s | NbE with closures and glued values, with no substitution, is 27 to 86 times faster than Lean on conversion | https://github.com/AndrasKovacs/smalltt |
| smalltt | TreeConv23: Lean 0.001 s, smalltt 3.3 s | equality that uses sharing (pointer equality on hash-consed terms) is necessary; NbE alone is not sufficient | the same |
| normalization-bench | Nat 10M normalization in 227 ms with HOAS in GHC | the memory system (allocator and GC settings) decides much of the result | https://github.com/AndrasKovacs/normalization-bench |
| Coq `native_compute` | 2 to 5 times faster than the bytecode VM on most tests; the four colour proof 3 h 7 min against 34 min 47 s | compiled evaluation helps large computations, for example `decide` | https://inria.hal.science/hal-00650940 |
| Courant and Leroy, POPL 2026 | a lazy, concurrent convertibility checker | the source of some Arena `perf/` tests; it runs the two sides of a conversion at the same time | https://zenodo.org/records/17347533 |
| Metamath Zero | set.mm in 195 ms on one thread | a binary format that is made for the check, and a small checker, give one to two orders of magnitude | https://arxiv.org/abs/1910.10703 |
| metamath-knife | set.mm in 641 ms; metamath.exe 3.9 s | threads and a fast parse | https://github.com/metamath/set.mm/blob/develop/verifiers.md |
| Kontroli | 6.6 times faster with 8 threads; a parallel parse did not help, because of the cost of the channels | parallel check yes, parallel parse with channels no | https://arxiv.org/abs/2102.08766 |
| Lean 3, trepplein | 145490 declarations in 13 min on 1 thread, about 3 min on 16 threads; leanchecker about 50 min | an old external checker was already 4 times faster than the official one | https://leanprover-community.github.io/archive/stream/113488-general/topic/mathlib.20repo.20GitHub.20actions.20queue.html |

## 02.8 Definitional equality: what is known

- **Union-find is not sound for Lean.** Lean PR #14806 (August 2026) removed the union-find of `equiv_manager`. `is_def_eq` is not complete, so it is not transitive, and the union-find could make a proof of `False`. The PR uses caches of pairs for successes and failures. rulean has no union-find (spec 08.5). Source: https://github.com/leanprover/lean4/pull/14806.
- **The cost of that change.** The first bench in the PR thread gives +1.09% instructions on the Mathlib build. Some modules were much slower, for example +2499% on LocalCohomology. So the pair caches must be good. [U] for the numbers of the merged PR.
- **The current C++ kernel.** Caches: infer (two modes), whnf_core, whnf, unfold, and the two pair caches. Structural equality compares the hashes first and then uses a cache of pointer pairs. Lazy delta compares the heights of the definitions. If the two sides have the same head, it compares the arguments first. Nat literals have a limit of 128 MB (v4.34, #14849). Source: `src/kernel/type_checker.h` and `src/kernel/expr_eq_fn.cpp` of the master branch.
- **Repeated subproblems.** A pair cache changes `perf/repeated-subproblem` from exponential to linear time. Source: the Arena test description.
- **Memoization in the elaborator.** The "26 G instructions, -55%" change of v4.34 (#14520) is in `instantiateMVars` of the elaborator, not in the kernel. So it does not change the kernel numbers.

## 02.9 Lessons for rulean

1. The fast kernels do not make new terms during the check. They make values in an arena, and they free or reuse the arena. This is the largest single factor. The evidence is the Arena ranking (02.1), smalltt (02.7) and the profile of rulean (03.3).
2. Sharing is still necessary. A kernel that compares values without the pointer equality of hash-consed input terms is slow on deep shared terms (TreeConv).
3. The parse is a large part of the work. A design for the check, with a binary format or a parse at the speed of memory, gives a large factor (MM0, gruszka Susz).
4. Memory management is a large cost in the official kernel (the RH allocator result). An arena with mark and release has almost no cost.
5. Threads give 3 to 9 times on the wall time. They do not reduce the instructions. They need a shared store with no copy.
6. A kernel that only reorders the official algorithm stays near the official count. con-ron, nanoda and rulean engine R show this.
