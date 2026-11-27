# 11. The choice of the engine for each declaration

This section gives a new profile of Init after the engine G steps of section 10, and the rule that follows from it. All counts are from the local measure of 07.3 with one thread, on the machine of 03, on 2026-11-27. The command is `rulean check --threads 1 --engine F --report /dev/null init.ndjson`, and the count is the `instructions retired` line of `/usr/bin/time -l`. The perf total is the sum of the 42 perf tests of `scripts/perf` with engine F.

## 11.1 The start point

| Build | Init, engine F | Init, engine R | Perf total |
|---|---|---|---|
| main with #233 and #234 | 208.8 G | 138.6 G | 110.2 G |

Engine F uses 70 G more than engine R on Init. Section 08.2 found that engine F is only a little faster than engine R when it accepts a declaration, and that a stop of engine F loses its time.

## 11.2 Probes that did not help

Each probe is a change that we measured and did not keep.

| Probe | Init, engine F |
|---|---|
| No confirm by engine R (not sound, only a measure of the cost) | 198.6 G |
| `Intern::clear` makes `k_nodes` smaller after a small declaration | 216.8 G |
| No `c_unfold_key` | 229.8 G |
| The key of a closure and of a suspension uses only the used prefix of the environment | 210.3 G |
| `conv` compares the value keys first, and computes them if necessary | 218.2 G |
| `conv` compares the value keys first, only if both values have a key | 209.3 G |

The confirm set costs about 10 G. The value keys cost about 11% of the samples, but without them engine F does more work. The hash tables are not the problem: a walk of the store reads 1.15 slots on average.

## 11.3 The profile

A sample of engine F on Init gives these shares of the samples of `check_export`.

| Function | Share |
|---|---|
| `f_conv_top`, the check of each argument type and of the declared type | 59% |
| `unfold_glued`, of which `spine_key` is 42% | 24% |
| `check_value_r`, engine R after a stop of engine F | 15% |

On the slowest declaration, `Vector.extract_append._proof_1`, `explain` shows 54,815 delta steps with engine F and 45,012 with engine R. So engine F does only a little more search, but it takes about 3 times the time. The cost of each step of engine F is higher than the cost of each step of engine R on this kind of term.

## 11.4 The size of the value

A probe sent each value with more than N distinct nodes to engine R.

| N | Init, engine F | Notes |
|---|---|---|
| no limit | 208.8 G | |
| 4096 | 200.6 G | |
| 1024 | 172.6 G | |
| 256 | 162.1 G | `app-lam` goes from 0.17 G to 37.5 G and `let-ladder` from 0.07 G to 5.2 G |

So on Init, engine R is the better engine for most values, also for small ones. But on the perf tests, engine F is necessary for some values. `app-lam` has about 4,000 nested lambdas, and `let-ladder` has 2,000 nested `let` terms. Engine R copies the body of a binder when it goes under the binder, so its time grows with the depth times the size. Engine F does not copy the term.

## 11.5 The depth of the binders

A value with a chain of more than 64 nested binders stays with engine F. The walk goes first into the body of each binder, so it finds a deep chain early.

| N | Init, engine F | Perf total |
|---|---|---|
| 256 | 164.1 G | 108.7 G |
| 64 | 160.9 G | |
| 16 | 160.4 G | |

With the depth test, no perf test is slower. Below 64 nodes, the gain is small.

## 11.6 The queries of engine R

With N = 64, engine R checks most values of Init, but each top-level query of engine R still goes to engine F first (`is_def_eq_shared`). These queries used about half of the samples. A flag now stops this for the declaration.

| Rule for the flag | Init, engine F | Perf total | Slower perf tests |
|---|---|---|---|
| Set by the type check and the value check | 136.3 G | 174.6 G | `app-lam` 38.5 G, `ite-taken-branch` 19.6 G, `let-ladder` 5.2 G |
| Set by the value check, walk of 64 nodes | 137.8 G | 170.1 G | `app-lam` 39.0 G, `ite-taken-branch` 19.6 G |
| Value above 1024 nodes, walk of 1024 nodes | 145.0 G | 108.3 G | none |
| Value above 256 nodes | 139.7 G | 107.7 G | none |
| Value above 128 nodes | 139.4 G | 108.3 G | `discarded-argument` 0.02 G to 0.30 G |

The type check must not set the flag. In `app-lam` the type is large and not deep, but the value is deep. The walk must read more nodes than the depth limit, else it stops before it finds a deep chain. On a small value, the queries can need the rules of engine F, as in `ite-taken-branch`. So the limit of the flag is higher than the limit of the value check.

## 11.7 The rule

The value check of a definition, a theorem or an opaque constant uses this rule.

1. `term_walk` counts the distinct nodes of the value, up to 1025. It gives 0 if the value has a chain of more than 64 nested binders.
2. If the count is more than 64, engine R checks the value.
3. If the count is also more than 256, the queries of the declaration use engine R only.
4. Else engine F checks the value, as before.

The type check uses steps 1 and 2 of this rule (11.8).

Engine R is the reference engine, so the rule cannot change a verdict. It only changes the engine that does the work.

On main with #233, the rule takes Init with engine F from 208.9 G to 139.5 G, and the perf total from 110.6 G to 108.6 G. No perf test is slower by more than 0.15 G. `fueled-chain` goes from 0.82 G to 0.26 G and `grind-ring-5` from 6.40 G to 6.09 G.

## 11.8 The type check

After #235, the type check of a declaration with engine F used the same rule: a type with more than 64 distinct nodes and no chain of more than 64 nested binders goes to engine R. The type check does not set the flag of 11.6, because in `app-lam` the type is wide but the value is deep.

| Build | Init, engine F | Perf total |
|---|---|---|
| main with #235 | 139.5 G | 108.6 G |
| and the rule for the type check | 138.3 G | 108.5 G |

No perf test changes by more than 0.15 G. Engine F on Init now uses about as many instructions as engine R alone (138.6 G).

A value limit of 32 in place of 64 gave 139.6 G, so the limit stays at 64.

## 11.9 The default engine

PR #237 made engine F the default engine of `rulean check`, and this change was reverted. The work gate of CI showed 4.5% more work on Init and 17.0% more work on Std with engine F. A local measure of `std.ndjson` (101,146 declarations, Lean 4.36.0) gave these counts.

| Build | Std, engine F | Std, engine R | Init, engine F | Init, engine R | Perf total, engine F |
|---|---|---|---|---|---|
| main with #237 | 239.0 G | 225.3 G | 138.8 G | 138.6 G | 107.8 G |
| value limit 16 | 238.6 G | | 137.8 G | | |
| value limit 4 | 238.2 G | | 137.7 G | | |
| flag limit 64 | 231.7 G | | 138.5 G | | 126.0 G |

The value checks of engine F are not the cause of the difference on Std. With the flag limit of 64, the queries of engine F on Std go from 297,492 to 92,065, and Std uses 7.3 G less. But `ite-taken-branch` then goes from 1.04 G to 19.58 G. So engine R stays the default engine. Engine F becomes the default engine only when it uses at most as many instructions as engine R on Init and on Std, and when the perf gate passes.

## 11.10 Probes on engine R

A sample of engine R on Std gives these shares of the self time: `inst_rec` 15.7%, `mk_app` 13.4%, the probe of the hash-cons table 13.4%, `canon` 5.4% and `Memo::put` 4.2%. Each probe below is a change that we measured with `--engine R` and did not keep.

| Probe | Std | Init |
|---|---|---|
| main | 225.3 G | 138.6 G |
| No memo in `inst_rec` | 553.3 G | 178.9 G |
| Memo of `inst_rec` with 2^15 slots in place of 2^13 | 225.4 G | 137.3 G |
| Memo of `inst_rec` with 2^11 slots | 226.3 G | 137.4 G |
| A memo of `instantiate1` from one call to the next, cleared at each new generation of the store | 226.0 G | 137.2 G |

The memo of `inst_rec` is necessary, because the terms share many nodes. But its size is not the problem, and a cache of the results from one call to the next does not find enough repeated calls. So the cost of engine R is in the work of each substitution, and the next work must make fewer substitutions, not faster ones.

## 11.11 The confirm set after the rule

Item A3 of 04.3 asks for at most 1000 confirmations on Init, and it removes each pair of the confirm set that has no reason. A run of Init with engine F, on main with #241, gave 128,333 queries of engine F, 2,528 confirmations of engine R and 0 disagreements. Before the rule of 11.7, the count was 13,207 confirmations.

| Build | Init, engine F |
|---|---|
| main with #241 | 138.36 G |
| no confirmation (not sound, only a measure of the cost) | 137.32 G |

So the confirm set now costs 1.04 G, or 0.75% of the run. The 225 Arena tests give the expected verdict also with no confirmation. This is not a reason to remove a pair, because with the rule of 11.7 engine R checks most values, and engine F can miss the corner cases of spec 05.1 for this reason. The pairs of the confirm set are a type-directed rule and a delta step. These are the cases where the official order is not transitive (spec 05.1), so the hypothesis of the lemmas of rows O8 to O11, that the official order decides definitional equality, is false for them. So a lemma of this form cannot give a reason for a pair, and the confirm set does not change. A3 stays open. Its gain is at most 1.04 G on Init, so it is not on the path to the target of 80 G.

## 11.12 The profile of engine R

A sample of engine R on Init, on main with #241, gives these shares of the samples of the worker (10,548 samples, with each function counted only where it is at the top of the stack).

| Part | Share |
|---|---|
| The hash-cons walk: `mk_app`, `probe`, `intern_expr` and `push_node` | 28% |
| `inst_rec` | 16% |
| `canon` and `Memo::put` | 10% |
| `app_fn`, `whnf_core` and `app_rev_args` | 10% |

The callers of `inst_rec` are the beta step of `whnf_core_app` (about 60% of its samples), `infer_lambda` (18%), `infer_app` (13%) and `infer_pi` (4%). The beta step already instantiates all the arguments of a chain of lambdas in one call. So, as 11.10 found, the next work must make fewer substitutions and fewer new nodes, not faster ones.

## 11.13 What follows

Engine R on Init uses 137.4 G instructions. The exit of M9 needs at most 80 G, and nano-lean uses 24.3 G (01). The profile of 11.12 and the probes of 11.10 show that a faster substitution is not enough, because the cost is in the number of substitutions and new nodes. nano-lean and gruszka make no substitution: they evaluate with an environment, and they share each value and its results (09.3, 09.4). Engine F has the evaluation with an environment, but not the shared values. So with the rule of 11.7, engine R checks most values of Init.

So the path to the exit of M9 is the plan R1 to R6 of 09.5 for engine F, and not more work on engine R. When engine F uses fewer instructions than engine R on wide values, the limits of 11.7 go up, and engine F checks more of Init. The first step is R1, a closure that keeps only the used part of its environment, because R2 and R3 need equal closures for the same work. Each step is measured on Init with engine F and with the limits of 11.7 set very high, so that the measure shows engine F alone, and on the perf tests. Engine F stays the engine for deep terms and for the evaluation tests.
