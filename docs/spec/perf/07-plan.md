# 07. Plan

The plan has three milestones. Each milestone has one issue with a checklist. Each item is one or more PRs. Each PR that changes the speed gives the count before and after, with the command of 07.3.

## 07.1 Milestones

### M8. Perf: measure and input

Goal: a bench for the popular kernels in the repository, and a parse of NDJSON that meets its budget (05.2).

1. This spec, in `docs/spec/perf/`.
2. `scripts/kbench.sh`: runs rulean and the popular kernels of the toolchain on one export, and prints the instructions and the max RSS of each kernel (03.1).
3. `docs/bench/kernels.md`: the table of 03.2, made with `kbench.sh`.
4. The steps and the comparisons of each probe of the intern table, in the report of `rulean check --report` (05.5).
5. A fix of the probe, from the counts of item 4 (05.5). The counts show that the walks are short, so this item is closed with no change of the table.
6. The template fast path of the parse, with the test and the fuzz target that compare it with the general parser (05.3).
7. The fast path for the ids (05.4).

Exit: the parse and the intern of Init use at most 8 G instructions on the local measure (two times the budget of 05.2), and the verdicts of the corpus of spec 11 do not change.

### M9. Perf: engine F core

Goal: engine F with no new terms during a check (04), and engine F as the default engine.

1. A query that engine F cannot answer goes to engine R as one query, not as a whole declaration (04.3 A2, 04.7).
2. The confirm set: each rule pair has a reason, and the pairs with no reason are removed (04.3 A3).
3. finfer for projections, literals and free variables (04.5).
4. The type of a lambda as a pi value with a closure, with no read-back (04.5).
5. Marks in the arena, and release at the end of each query (04.3 A4).
6. Lazy arguments (04.3 A5, 04.4).
7. Sharing first in `conv` (04.3 A6).
8. Small Nat literals as inline numbers (04.8).
9. No `malloc` in the hot path of engine F, checked with a count of the allocations (04.3 A9).
10. Engine F is the default engine of `rulean check`. Section 11.9 gives the condition and the measures of a first try.

Exit: on the local measure, the check of Init with engine F uses at most 3 times fewer instructions than engine R does today (242.2 G, so at most 80 G for the whole run). The `perf/` gate of the nightly passes on at least 35 of the 45 tests. The verdicts of the corpus do not change.

### M10. Perf: in-process and threads

Goal: the in-process kernel uses engine F and has no checks again (06), and the threads share one store.

1. The source of constants in the core, and the lookup at first use in the FFI (06.2).
2. One pass in `add_decl`, with the limit of the call (06.2).
3. Engine F in-process, with calibration 2 of spec 09.6.4 done again (06.3).
4. The mirror converts a constant only at its first lookup (06.4).
5. The workers of the check stage share one frozen store, with no copy of the environment (spec 08.3).
6. The jobs of the check stage follow the dependency graph, so a long declaration does not wait at the end of a job list [U for the gain].

Exit: on the dual-kernel build of Mathlib, the rulean kernel time is at most the C++ kernel time (3829 s), and the checks again use 0 s. The Mathlib run of the Arena workflow gives a wall time of at most 2 times the wall time of nanoda (754 s).

## 07.2 The steps after M10

The exit criteria of M8, M9 and M10 are steps, not the targets of 01.4. After M10, a new issue sets the next step from the measurements. The targets G1 to G5 stay the goal. Each step is honest: if a measurement shows that a principle of 04 does not give its gain, the spec changes, and the change has the measurement.

The budget for Mathlib follows from Init: 81 instructions per byte today, 11.5 in the budget (05.2), so about 71 G for the parse of 5.9 GB and about 30 G for the intern. The check of about 700 k declarations has about 475 G, which is about 680 k instructions for each declaration. A declaration of Mathlib is larger than a declaration of Init, so this budget is not certain [U].

## 07.3 How to measure

- Locally: `scripts/kbench.sh EXPORT` (M8 item 2). It prints one line for each kernel: the name, the exit code, the instructions and the max RSS. Run it on Init and on the `perf/` tests. Give the machine and the load average in the PR.
- CI: the nightly workflow with cachegrind gives the `perf/` counts. The limit of cachegrind (5 s) gives no count for a long run (03.5). A test with no count fails the gate.
- Arena: the counts of the Arena are the final measure. A submission to the Arena is a step outside the repository, and it needs the approval of the owner.

## 07.4 Releases

- A patch release (v0.0.y) comes after a group of merged PRs, as today.
- When a milestone is done, the next minor release (v0.x.0) comes after it.
- The release notes give the count of Init and the `perf/` gate result of the release.

## 07.5 Risks

| Risk | Effect | Action |
|---|---|---|
| A smaller confirm set accepts a term that the official kernel rejects | wrong verdict | the twin lemma first, then the change (04.11); the corpus of spec 11 and the Arena tests in CI |
| Marks in the arena free a value that a cache keeps | wrong verdict or a crash | the lemma of 04.11; a debug mode that fills freed values with a bad pattern |
| Lazy arguments change the heartbeat count | in-process timeout where C++ does not time out | calibration 2 of 09.6.4 (06.3) |
| The fast parse accepts a line that the general parser rejects | wrong verdict | the parse gives each line that it does not fully match to the general parser; the fuzz target (05.3) |
| The source in the core is outside the Aeneas subset | no proof for the core | a generic parameter, or a callback through a table of functions in the FFI crate only (06.2) |
| The local measure is not the Arena measure | wrong target | ratios only, and a check against the Arena counts of nanoda and the official kernel (03.2) |
