# 03. rulean in November 2026

This section gives the measurements of rulean at commit bd14f4b (v0.0.19 and later). The numbers are the starting point for the targets of 01.4.

## 03.1 How we measured

- Machine: Apple Mac, 10 cores, 24 GB. Other jobs ran on the machine, with a load average of 35 to 87. So the wall times in this section are not good. The instruction counts are good, because the count does not change much with the load.
- Count: `/usr/bin/time -l`, the line "instructions retired". This count includes the system calls, and it is for the process that `time` starts. A kernel must run as that process. When a shell starts the kernel, the count is the count of the shell (about 30 M), and it is not valid.
- Export: `init.ndjson` of the Arena test `init` (348 MB, 6495296 lines, 58547 declarations).
- Toolchain: Lean v4.36.0, with `leanchecker` (the official kernel) and `nanoda_bin`.
- Script: `scripts/kbench.sh` (07.3). The date is 2026-11-25.

## 03.2 External check on Init

| Kernel | Threads | Instructions | Max RSS | Arena count (01.4) |
|---|---|---|---|---|
| rulean, engine R | 1 | 242.2 G | 462 MB | none |
| nanoda | 1 | 247.0 G | 548 MB | 223.8 G with 4 threads |
| official `leanchecker` | 1 | 410.9 G | 575 MB | 401.5 G (v4.35.0) |
| rulean, engine F | 1 | 437.0 G | 455 MB | none |
| con-ron | 1 | 566.0 G | 773 MB | 172 G with `--verified --jobs=4` |
| rulean, parse only | 1 | 28.1 G | | none |

The local counts of nanoda and the official kernel are within 10% of the Arena counts. So the local measure is good enough to compare kernels.

Results:

- rulean engine R uses 1.70 times fewer instructions than the official kernel, and about the same count as nanoda. The target G2.a (22.4 G) is 10.8 times fewer than engine R.
- Engine F uses 1.8 times the instructions of engine R. 03.4 gives the reason.
- The parse uses 28.1 G. This is 81 instructions for each byte, and about 4300 for each line. The check with engine R uses about 214 G, which is 3.7 M instructions for each declaration.

## 03.3 Profiles

The profiles come from `sample` on macOS, with the samples grouped by the function at the top of the stack. A sample is a point in time, so these shares are shares of the cycles and not of the instructions. A function that waits for memory, such as the probe of the intern table, has a larger share of the cycles than of the instructions (05.5). The instruction profiles come from the workflow `profile` with cachegrind.

**Engine F on Init** (23050 samples):

| Group | Share | Functions |
|---|---|---|
| intern | 26.7% | `probe`, `intern_expr`, `Table::put`, `mk_app` |
| evaluation | 19.7% | `nbe` |
| substitution | 17.2% | `inst_rec`, `lps_rec`, `Memo::find`, `Memo::put` |
| node reads | 12.4% | `Nodes::get` |
| `malloc` and `free` | 8.4% | |
| other | 6.4% | |
| whnf of engine R | 4.4% | |
| conversion | 2.3% | |
| finfer | 2.0% | |
| SHA-256 | 0.5% | |

**Engine R on Init.** The hot addresses are in the probe loop of the intern table (`rulean-store/src/expr.rs:295`, the comparison of a node with the node in the slot), in `Nodes::get` (`expr.rs:182`), in `Memo::find` (`rulean-core/src/memo.rs:62` to `67`) and in `table.rs:188`. So engine R also uses most of its time to make terms and to find them again.

**Parse on Init:**

| Group | Share | Functions |
|---|---|---|
| scan of JSON | 49.7% | `ndjson::Stream::line`, `Scanner::skip_string`, `skip_object`, `skip_value`, `keys::code` |
| intern | 30.5% | `probe` |
| read | 4.2% | |
| SHA-256 | 2.4% | `sha.rs`, which already uses the SHA instructions of the CPU |

**Lines of the Init export:**

| Kind | Lines | Bytes |
|---|---|---|
| `app` | 80.5% | 72.1% (48 bytes for each line) |
| `lam` | 8.2% | 13.1% |
| `forallE` | 4.7% | 7.8% |
| `str` | 2.7% | |
| `num` | 1.9% | |
| `const` | 0.9% | |

The keys of each object are in alphabetical order, and each kind has a fixed layout, for example `{"app":{"arg":1,"fn":7},"ie":8}`. The ids of each kind go up by one from line to line. 05 uses these facts.

## 03.4 Engine F counters on Init

From `rulean check --engine f --report` on Init:

| Counter | Value | Meaning |
|---|---|---|
| `f_queries` | 44159 | queries of the engine R paths that engine F tried first |
| `f_equal` | 42855 | queries where engine F said "equal" |
| `f_fallback` | 1270 | queries where engine F said "not equal" and engine R decided |
| `f_faults` | 34 | queries where engine F stopped, for example on a full arena |
| `r_confirmed` | 13205 | "equal" answers that engine R confirmed |
| `r_disagree` | 0 | answers where engine R did not agree |
| `f_infer` | 115872 | type checks and value checks of declarations that finfer tried |
| `f_infer_ok` | 114129 | type checks and value checks that finfer accepted |
| steps | 969540284 | calls of `enter`, with each step of `eval` |
| interns | 358402697 | calls of `intern_expr` |
| session hits | 881010 | |
| session entries | 71226 | |

In finfer, a "not equal" answer or a fault makes engine R check the whole declaration again (the header of `finfer.rs`). This happened for 1743 of the 115872 checks (1.5%). A confirmation runs engine R on one query, on the terms that engine F reads back, and engine F then continues. So the fallback to engine R is not the main cost of engine F.

The main cost is the work of engine F itself. With engine R, the same export has 56396829 steps and 200900317 interns. Engine F has 17 times the steps and 1.8 times the interns. A step of engine F is not the same unit as a step of engine R, because `eval` calls `enter` for each node that it evaluates [U for the ratio of the work]. But the count shows that engine F evaluates much more than engine R needs. Engine F evaluates each argument when it evaluates an application, and it reads values back into terms for the confirmations and for the types of lambdas. Principles A1, A5 and A7 of 04 are for this cost.

## 03.5 The Arena `perf/` tests

Source: the nightly run 45535065648 (2026-11-25), counter cachegrind, with a limit of 5 s for cachegrind. A run longer than that limit has no count.

- The gate for correct verdicts passes on all 230 tests.
- The gate for `perf/` (at most 1 virtual second, 6.0 G) fails on 20 of the 43 tests in the local corpus. 10 tests have a count above 6.0 G, and 10 tests have no count because they ran longer than the limit of cachegrind.
- On the 40 tests of G3, rulean has a count on 32 tests, with a sum of 207.3 G. Of the other 8 tests, 6 have no count and 2 are not in the local corpus. The target G3 is 67.3 G for all 40 tests.

The tests above 6.0 G are:

| Test | Instructions |
|---|---|
| `perf/ite-taken-branch-bad` | 41.7 G |
| `perf/proj-applied-struct-arg-bad` | 32.8 G |
| `perf/proj-applied-struct-bad` | 32.7 G |
| `perf/gf3-matrix-product` | 20.6 G |
| `perf/loop-unfolded-once-bad` | 18.3 G |
| `perf/magma-list-deep-n21` | 16.7 G |
| `perf/proj-app-lazy-delta` | 15.2 G |
| `perf/beta-ladder` | 11.4 G |
| `perf/magma-list-pair-n7` | 10.7 G |
| `perf/grind-ring-5` | 10.5 G |

The tests with no count are `app-lam`, `ite-taken-branch`, `magma-list-deep-n36`, `magma-list-pair-n21`, `proj-applied-struct`, `short-circuit-and`, `short-circuit-and-bad`, `unfold-before-literal`, `unfold-before-literal-bad` and `unfold-before-literal-fallback`. Their wall time is 5 to 35 s on the CI runner. The tests `magma-string-n4` and `magma-string-pair-n9` are not in the local corpus.

These runs use engine R. Most of the slow tests are tests of lazy evaluation (an argument that the check must not evaluate) or of projections of applied structures. Principles A5 and A7 of 04 are for these tests.

## 03.6 In-process

Source: run 1 of the workflow `mathlib` (45616391280), the dual-kernel build of Mathlib (spec 09.6.3). The times are summed over all `lean` processes.

| Part | Time |
|---|---|
| C++ kernel | 3829 s |
| rulean, check | 6295 s |
| of which: the checks again (`T_RECHECK`) | 3332 s |
| rulean, conversion of the declarations | 173.5 s |
| rulean, conversion of the results | 15.1 s |
| rulean, the mirror of the environment | 503.6 s |
| of which: conversion of the imported constants | 313.7 s |
| rulean, total | 6987.2 s |

The in-process kernel uses engine R. A check runs in passes (`add_decl` in `rulean-ffi/src/kernel.rs`). After a pass, the kernel compares each constant that the pass looked up with the Lean environment. The check runs again from the start in three cases: a lookup found no constant, a constant of the mirror is not the constant of the Lean environment, or the pass stopped at its heartbeat limit (1 M at first, then 10 times more for each pass) and the limit of the call is larger. These checks again use 53% of the check time. 06 removes them.

## 03.7 Summary

| Target | Today | Factor needed |
|---|---|---|
| G2.a, Init 22.4 G | 242.2 G (local, engine R) | 10.8 |
| G3, `perf/` 67.3 G | above 207.3 G (32 of 40 tests counted) | above 3.1, and much more on the 8 tests with no count |
| G4, in-process 383 s | 6987.2 s | 18.2 |

The causes are:

1. The check makes and interns new terms. More than half of the samples of engine F are intern, substitution, node reads and `malloc`.
2. Engine F evaluates much more than the check needs (17 times the steps of engine R), and it still makes terms (1.8 times the interns of engine R).
3. The parse reads each byte in a general JSON scanner, with about 4300 instructions for each line.
4. In-process, a lookup that misses or is stale, or a pass at its limit, causes a full check again.
