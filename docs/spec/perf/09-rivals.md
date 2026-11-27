# 09. What the fastest rivals do

This section compares engine F with the two fastest checkers on the perf tests of the Lean Kernel Arena, and it gives the changes to the architecture of engine F that follow. The facts come from a read of the source of each rival at the given revision. Nothing was built or run.

## 09.1 The measures

The table gives the sum of the instructions on the 44 perf tests of the Arena results. The count for rulean is the local measure of 07.3 on 42 of these tests, at v0.8.7.

| Checker | Revision | Perf tests | Instructions |
|---|---|---|---|
| nano-lean | 5cd4a25 | 44 | 90.6 G |
| gruszka | edd7d47 | 44 | 148.6 G |
| kefir | 095cff9 | 44 | 178.3 G |
| official-nightly | nightly | 44 | 959.2 G |
| rulean v0.8.7 | 7288838 | 42 | 449.2 G |

On some tests the gap is very large. The best rival is the checker with the smallest count and a correct verdict on the test:

| Test | rulean | Best rival |
|---|---|---|
| `magma-list-pair-n21` | 89.5 G | 6.7 G (rpylean) |
| `magma-list-deep-n36` | 153.1 G | 1.6 G (rpylean) |
| `gf3-matrix-product` | 40.7 G | 5.0 G (nano-lean) |
| `ite-taken-branch-bad` | 25.4 G | 1.6 G (nano-lean) |
| `grind-ring-5` | 6.4 G | 1.3 G (nano-lean) |

A first version of this table gave 0.5 G and 0.7 G for lean4lean. On these tests lean4lean rejects a good declaration, so its counts are not used.

## 09.2 Why engine F is slow on these tests

On each of these tests, engine F stops with `ArenaFull` on the main declaration, and engine R then checks the declaration. Thus the time is the time of engine R. A probe counted the values in the arena at the stop of `magma-list-pair-n7`:

| Kind | Count |
|---|---|
| `Lam` | 62,053 |
| `Glued` | 68,960 |
| `Susp` | 68,072 |
| `Neu` with a constant head | 51,360 |
| `Small` | 6,674 |
| `Sort` | 3,788 |
| others | 1,237 |

With an arena of 2^26 values, engine F finishes these tests, but it uses a large amount of memory. `magma-list-pair-n7` then uses 5.5 G instructions and 0.8 GB, and `gf3-matrix-product` uses 28.7 G and 3.6 GB. The bad tests use 40 to 64 G and up to 4.3 GB. Thus engine F makes too many values, and it frees none of them inside a declaration.

A cache of `eval` at the key (term, environment) did not change these tests. Two evaluations of the same term seldom have the same environment, because each closure keeps the full environment of its definition.

## 09.3 nano-lean

- It uses NbE with hash-consed values. Sorts, lambdas, constants, projections, neutral spines, literals and environments are interned, so the same computation gives the same pointer.
- It has a cache of `eval` at (term, universe substitution, environment). A closure keeps only the part of its environment that its body reads (`trim`, with a 32-bit mask of the loose bound variables of each term). Two closures that differ only in values that the body does not read are then the same value, and the cache finds them.
- Each value keeps its `whnf`, its `whnf_core`, its unfolding and its type. `whnf` writes the result on each state that it passed.
- It frees nothing inside a declaration. The budget is 4 GiB for each declaration.
- After 32 unfoldings of a definition, it evaluates the body on new locals and splits on the major premises of the recursors. The result is a case tree, and a later unfolding matches the arguments against the tree. This removes the layers of `brecOn`, `PProd` and matchers at each call.
- Lazy delta keeps the last 4 forms of each side, and it compares the arguments when one side gets to a head that the other side passed. Argument probes have a budget of steps.

## 09.4 gruszka

- It uses NbE with hash-consed values, environments and spines. Each value has its memos inline (whnf, `whnf_core`, type, unfolding).
- The arena holds up to 2^28 values. Regions start at 2^22 values, and a fallback machine starts at 2^26.
- A region is opened at the start of a `whnf` call. A write of a memo on a value that is older than the region goes into an undo log. At the end, if the region made many values and the result reaches few of them, the result is copied out, the region is removed, and the log is undone for dead values. The copy is interned again. This is sound because a value only points to older values, so the log has each pointer from an old value to a new value.
- The loop of `whnf` keeps only its current term. After 2^21 values, it closes the region with the current term as the result and opens it again. This frees memory inside a long loop, for example a `for` loop of `Array.set!`.
- An environment is a run of an array with a mask of the used variables. A value that the body does not read gets no thunk.
- A call-by-need machine with reference counts evaluates closed values that are compared with data. Each thunk is updated in place, and an environment is cut to the entries that the term reads.
- In lazy delta, the arguments of the same head are compared from the last to the first with a budget of 256 steps before the full comparison. One cheap difference then refutes the query.

## 09.5 What follows for engine F

The two rivals agree on three points that engine F does not have:

1. A value is shared. The same computation gives the same value, and a value keeps its results.
2. A closure keeps only the values that its body reads.
3. The memory budget is large: 4 GiB, or 2^28 values. Engine F has 2^18 values.

Engine F has point 1 only in part. Its value keys (04.12) share an unfolding, but not a value. It has no part of point 2. A larger arena alone is not a fix, because engine F then uses more instructions on the large declarations of Init (08.3).

The plan, in order:

| Step | Change | Expected effect |
|---|---|---|
| R1 | Closures keep only the used part of the environment. An environment of a closure is cut to the loose bound variables of its body. | Fewer live values, and equal closures for the same work |
| R2 | Hash-cons the values of engine F: neutral applications, glued values, closures and environments. Use the value key of 04.12 as the table key. | One value and one memo for each computation |
| R3 | A cache of `eval` at (term, cut environment). | No new values for a computation that was done |
| R4 | Regions at the boundary of `force`, with a copy of the result and the undo log, as in gruszka. | Memory that a long loop frees |
| R5 | A larger arena, with a budget of steps for each declaration in place of a budget of values. | Engine F finishes the evaluation tests |
| R6 | Arguments of the same head are compared from the last to the first with a budget, before the full comparison. | Cheap refutations on the bad tests |

Each step must keep the verdicts of 07.4 and the Arena tests. Each step is measured on Init and on the perf tests, and a step that does not help is not merged.
