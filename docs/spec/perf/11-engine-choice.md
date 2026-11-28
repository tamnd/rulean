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

## 11.14 The probes of R1 and R3

Each probe below is a change that we measured and did not keep. The column "engine F alone" is Init with engine F and with the limits of 11.7 set to 5000, as 11.13 gives. The column "rule" is Init with engine F and the limits of 11.7.

| Probe | Engine F alone | Rule | Perf total |
|---|---|---|---|
| main with #243 | 211.74 G | 138.36 G | 106.4 G |
| R1 and R3 | 213.99 G | 138.53 G | 105.9 G |
| R3 only | 210.87 G | | |

R1 cuts the environment of a closure and of a suspension to the part that the body uses. It copies at most 4 values, and else it keeps the full environment. R1 alone did not decrease the count. R3 is a lossy cache of the evaluation of a closed application, with 2^13 slots. It keeps a result only when the evaluation did not use a fallback. R1 and R3 together make engine F alone 1.1% slower. R3 alone makes it 0.4% faster, and this gain is too small for a new cache in the hot path.

The copy of R1 makes new environments, so two closures for the same work do not share an environment, and the value keys of the closures cost more. R3 finds few repeated closed applications, because the values of engine F are not shared. So R1 and R3 need R2 first. The next step is R2, the shared values of 09.5.

## 11.15 The probes of R2 and the session for check mode

R2 shares the values of engine F. Each new value gets its value key (04.12), and a lossy table with 2^13 slots gives the older value with the same key. A hit is used only if the older value is still in the arena and has the same key, so a region release cannot make a wrong hit. The column "engine F alone" has the meaning of 11.14.

| Probe | Engine F alone | Rule |
|---|---|---|
| main with #244 | 211.74 G | 138.36 G |
| R2: lambdas, pi types, constants and applications | 290.97 G | 143.53 G |
| R2: constants, and applications whose parts have a key | 252.64 G | 140.09 G |
| R2: constants only | 229.06 G | |

With constants only, engine F does the same 830 queries and the same 115,603 accepted inferences as main. So the shared values do not remove work on Init, and the cost is the key of each new value. R2 is not kept. The R3 probe of 11.14 also gave 30 disagreements that engine R found, so no verdict changed. A term with no loose bound variable can have free variables of the local context, and their values change with the context. So a cache of the evaluation of a closed term must also have the free variables in its key.

The session of 08.4 kept only infer-only results, because a check-mode result also depends on the level parameters and the safety of the declaration. PR #245 adds a check-mode entry. It is written and read only in a safe declaration, because a safe declaration can use fewer constants than the other kinds. For a term with a level parameter, the second key is the level list of the level parameters of the declaration.

| Build | Init, engine R | Std, engine R |
|---|---|---|
| main with #244 | 137.2 G | 226.0 G |
| terms with no level parameter | 129.2 G | 213.6 G |
| #245 | 126.4 G | 206.6 G |

This is the first change since 11.10 that makes engine R faster on Init. The work that it removes is the same work in two declarations, not a repeated step in one declaration. So the next work looks for other work that the declarations repeat.

## 11.16 Session keys with free variables

The session of 08.4 used a key only if the term had no free variable and was in the frozen tier. Most terms that the type check of a declaration infers are in the binders of the declaration, so they have free variables. A free variable is a hash-consed node `FVar(level, ty)`, and the local context of a declaration only grows. So two declarations that open the same binders in the same order make the same free variable nodes. A let binder is different, because the value of the free variable is not in the node. PR #247 permits a key with free variables if the declaration has no let binder until that point.

A key in the scratch tier is promoted to the frozen tier at the commit of the declaration. These promotions have a budget of 2% of the scratch size. A budget of 10% made the gf3 test slower and used much more memory. A lookup is done only with a frozen key, because a scratch key cannot be in the table before the commit.

PR #248 uses the same rule for the results of `whnf_core`, `whnf` and the successful definitional equalities. For a pair, both terms are promoted, and the order by hash does not change, because the hash is structural.

| Build | Init, engine R | Std, engine R |
|---|---|---|
| #245 | 126.4 G | 206.6 G |
| #247: inferences with free variables | 106.6 G | 180.1 G |
| #248: all tags but unfold | 103.9 G | 178.2 G |

The goal of M9 for Init is at most 80 G. The next work looks at the profile after #248.

## 11.17 Terms without a binder and the budget of local keys

The profile of Init after #248 gives `canon` 5.4% of the main thread. It finds the cache key of a term for each call of `whnf_core`, `whnf` and the type inference. PR #250 adds the store flag `HAS_BINDER`, which a `lam`, a `pi` or a `let` node sets. The store interns every node, and the alpha-equality compares each atom by its handle. So a term without a binder is alpha-equal only to itself. `canon` gives such a term back at once, and `expr_equal` stops when a term has no binder.

The same profile shows that the session drops 8.3 M pending entries and stores 0.77 M. Almost all drops come from the budget of the scratch keys of 11.16, and few come from a value. A probe of the budget gives these counts with engine R:

| Budget of scratch keys | Init | Std | Perf tests (engine F) | Peak memory, Init | Peak memory, Std |
|---|---|---|---|---|---|
| 2% (#250) | 101.7 G | 174.3 G | 106.5 G | 591 MB | 1020 MB |
| 4% | 95.0 G | 166.9 G | 105.7 G | 620 MB | 1136 MB |
| 6.25% | 93.0 G | 162.5 G | 104.7 G | 959 MB | 1136 MB |
| 8.3% | 91.4 G | 161.7 G | 105.9 G | 951 MB | 1171 MB |
| 10% | 91.4 G | 160.0 G | 105.6 G | 929 MB | 1186 MB |

The step of the memory of Init between 4% and 6.25% is one growth of the session table, and the table stays below its limit of 128 MiB. No perf test is slower with 10%, and gf3 goes from 16.4 G to 15.9 G. The slower gf3 of 11.16 was measured before #248 and #250. PR #251 sets the budget to 10%.

## 11.18 Pairs that the quick check finds known

`quick_is_def_eq` gives true at once for a pair that is alpha-equal or in a success cache. Before #254, `is_def_eq` then put the pair in the declaration cache and noted it in the session again. This work had no benefit, because the quick check finds the pair again with no work. PR #254 adds the field `known_pair`. The quick check sets it to the pair that it finds known, and `is_def_eq` clears it before each query. `is_def_eq` does not put the marked pair in the caches.

Three variants give these counts with engine R:

| Variant | Init | Std |
|---|---|---|
| #251, no mark | 90.8 G | 159.8 G |
| Mark only the cache hits | 91.1 G | 160.5 G |
| Mark only the alpha-equal pairs | 88.6 G | 156.2 G |
| Mark both (#254) | 87.8 G | 156.2 G |

Most of the gain comes from the alpha-equal pairs. A pair that is alpha-equal is no longer in the session cache, so the pre-check of engine F does not find it, and engine F gets the query. The confirm run gives 428 engine F queries instead of 360. All 413 equal results are confirmed by engine R, and the run has 0 differences.

The goal of M9 for Init is at most 80 G.

## 11.19 Types to engine R, and a walk of 256 nodes

The profile of Init after #254 shows that the type check with engine F uses 7.2 G and the type check with engine R uses 4.4 G. Engine F is the slower engine for most types. PR #256 makes two changes. First, engine F checks a type only if `term_walk` finds a chain of more than `F_DEEP` nested binders, and engine R checks the other types. Second, `term_walk` reads at most 256 nodes in place of 1024. The walk goes first into the body of each binder, so it finds a deep chain early. `F_WALK` is not less than `F_R_ONLY`, so the walk still counts a value with more than `F_R_ONLY` nodes.

| Corpus | Before (#255) | After (#256) |
|---|---|---|
| Init, engine F | 94.5 G | 92.0 G |
| Std, engine F | 177.7 G | 173.6 G |
| Init, engine R | 87.8 G | 87.6 G |
| Perf tests, engine F | 104.5 G | 103.7 G |

The walk limit alone gives -0.84 G on Init. When engine R checks all types, Init gives 91.5 G, but `beta-ladder` goes from 0.09 G to 5.88 G, because its type is deep. With the rule for deep types, `beta-ladder` stays at 0.09 G.

## 11.20 Pools of vectors

A count of the instructions in malloc and free shows that many hot paths make a new vector for each query and free it at the end. Examples are the arguments of an application in the type inference and in `is_def_eq_app`, the levels of a constant in `inst_lps_cached`, and the free variables of a binder. PR #257 adds two pools to the type checker, `vpool` for terms and `lpool` for levels. A hot path takes a vector from a pool and gives it back when it is done. A pool keeps at most 64 vectors. A function with many exits gets a wrapper that takes the vectors, calls the body with them and gives them back, so that the body can stop at any point.

All counts are from one batch on the same machine.

| Corpus | Before (#256) | Pools in the type inference | All hot paths (#257) |
|---|---|---|---|
| Init, engine R | 88.0 G | 83.7 G | 82.2 G |
| Std, engine R | 155.9 G | 148.7 G | 145.5 G |
| Init, engine F | 92.7 G | 88.0 G | 86.6 G |
| Std, engine F | 174.9 G | 167.1 G | 164.8 G |

The perf total with engine F goes from 103.7 G to 102.8 G. The confirm run gives 0 differences. Some vectors in the cold paths are still new for each call, and the arena of engine F has its own allocations, so item A9 of 04.3 stays open.

The goal of M9 for Init with engine F is at most 80 G. After #257, the gap is about 6.6 G.

## 11.21 The map of promote, and a cache of whole calls

The session promotes the terms of each declaration from the scratch store to the main store. Before #259, each commit made a new map and a new stack for this walk and freed them at the end. PR #259 keeps the map and the stack in the type checker and clears them for each commit. `Memo::clear` is O(1), because it uses an epoch.

| Corpus | Before (#258) | After (#259) |
|---|---|---|
| Init, engine R | 82.7 G | 80.4 G |
| Init, engine F | 86.8 G | 85.0 G |

The perf total went from 102.8 G to 104.6 G in one run. Repeated runs show that the change is noise in `gf3`, which gives 15.4 G and 15.9 G with the same binary.

We also tried two changes that did not help, and we did not merge them.

1. A cache of whole calls to `instantiate`. The key is the body and the list of arguments, and the value is the result. Engine R makes 10.5 M calls on Init, and about 2.9 M of them repeat a call before them. The cache gave less memory (963 MB to 628 MB), but more instructions: Init with engine R went from 80.7 G to 82.0 G, and Init with engine F went from 85.6 G to 87.1 G. The cost of the key and the log is more than the work that the cache saves, because the memo of `inst_rec` already finds most of the repeated nodes.
2. A cache of calls with one argument only. It was 0.8 G slower than no cache.

A larger budget for the scratch store of the session (one fifth in place of one tenth) gave less instructions on Init, but more memory, up to 1.6 GB on Std, and the runs were too noisy to show a real gain. We did not change the budget.

## 11.22 Values to engine R

After #268, a breakdown of the work of engine F on Init used the deterministic counts of the report, because the load on the machine made the instruction counts change by more than 10 G between two runs of the same binary. Engine R alone uses 37.3 M steps. Engine F uses 47.9 M steps. A test build in which engine F checks no small value uses 41.6 M steps, and a test build in which engine F takes no query of engine R uses 46.7 M steps. Thus the value checks of engine F cost about 5.9 M steps on Init, and the queries cost less than 1 M steps.

The value checks also do not help the perf tests. The large gains of engine F, as in `ite-taken-branch` and `short-circuit-and`, come from the queries of engine R, and these stay. PR #269 makes the cap a field of the type checker, `f_term_cap`, with the default 0. Engine F now checks a value only if `term_walk` finds a deep chain, as for a type (11.19). The tests of the inference of engine F set the cap to 64.

| Measure | Before (#268) | After (#269) |
|---|---|---|
| Init, engine F, steps | 47.92 M | 42.13 M |
| Init, engine F, minimum of two runs | 84.3 G | 83.6 G |
| Steps of all perf tests, engine F | 15.50 M | 13.60 M |
| `prop-struct-projections`, minimum of three runs | 0.413 G | 0.214 G |
| `gf3-matrix-product`, minimum of three runs | 17.83 G | 17.67 G |
| `grind-ring-5`, minimum of three runs | 5.44 G | 5.40 G |

No perf test uses more steps. On Init, engine F now takes 126,946 queries in place of 101,037, because engine R now checks the values and asks more queries. The verdicts do not change.

We also tried a change that did not help, and we did not merge it. `is_def_eq_shared` looked in the equality caches of engine R before engine F, and an "equal" answer of engine F went into the cache. This removed 36% of the queries of engine F on Init, but the instruction count did not change.

Engine R alone is still faster on Init, by about 4 G. The other cost of engine F on Init is the queries, the walk of `term_walk` and the deep types.

## 11.23 Engine R first, with a budget

Engine F is not faster on each query. On Init, most queries are small, and engine R answers them with its caches in fewer instructions than engine F needs to evaluate the two terms in the arena. Engine F is faster on the hard queries, where engine R unfolds again and again or copies large terms. So each query of engine R that goes to engine F now goes first to engine R with a small budget. If engine R decides the query in the budget, its answer is the answer. If engine R uses the budget, `r_first` removes the fault, the scope entries and the failures that the try put in the cache, and engine F takes the query as before. The caches of engine R put a result only when there is no fault, so a stopped try leaves no wrong result in them. Under `--confirm all`, there is no try, so that engine F still answers each query and engine R confirms it.

The budget has two limits, because one heartbeat does not have a fixed cost.

1. `R_BUDGET`, 1024 heartbeats.
2. `R_INTERNS`, 1024 interns in the store. One heartbeat of `beta-ladder` copies a large term, and with heartbeats only, the test went from 0.099 G to 2.926 G.

Two more rules apply in the try. Engine G does not run in the try, because one call of engine G can compute a large value with no heartbeat. With engine G in the try, `unfold-before-literal` went from 0.033 G to 5.09 G. A `Nat` operation that reads or makes a literal of more than 512 bytes also stops the try.

The search used the minimum instruction count of two runs on each of the 42 Arena perf tests.

| Interns | Perf total | `loop-unfolded-once` | `proj-lazy-struct` | `unfold-before-literal` | Init, two runs |
|---|---|---|---|---|---|
| no try (#269) | 106.20 G | 1.036 G | 0.118 G | 0.034 G | 83.1 G, 83.3 G |
| 512 | 106.24 G | 1.045 G | 0.029 G | 0.035 G | 83.1 G, 83.5 G |
| 1024 | 105.36 G | 0.859 G | 0.029 G | 0.037 G | 82.4 G, 82.8 G |
| 2048 | 105.81 G | 0.854 G | 0.029 G | 0.039 G | 82.1 G, 82.2 G |
| 4096 | 106.35 G | 0.855 G | 0.029 G | 0.043 G | 82.2 G, 82.3 G |

We use 1024, because no perf test is more than 10% slower with it. The steps of engine F on Init go from 42.13 M to 33.08 M. Engine F now takes few queries on Init, so the cost of engine F mode on Init is no longer in the queries.

We also tried two changes that did not help, and we did not merge them.

1. `term_walk` counted the nodes of the tree, not the distinct nodes, so that a value with a large tree went to engine R only. Init went from 42.13 M to 36.72 M steps, but `discarded-argument` went from 0.025 G to 0.254 G and `discarded-argument-match` from 0.027 G to 0.439 G. The value of these tests has 210 distinct nodes and 409 nodes in the tree. On Init, the values with at most 256 distinct nodes and more than 256 nodes in the tree have all ratios of tree to distinct nodes, so no bound on the ratio keeps the two tests and the gain.
2. A check of `has_binder` before the walk of a type. It gave the same steps and no change in instructions above the noise.

## 11.24 The cost of the walk

After #270, engine F mode on Init uses about 82.6 G instructions, and engine R mode uses about 79.6 G. To find the cost of each part of engine F mode, we made three probes. Each probe has the same decisions as main, or a known change of the decisions.

| Probe | What it does | Init, two runs |
|---|---|---|
| main (#270) | engine F mode | 82.6 G, 82.6 G |
| all declined | no walk, and each declaration uses engine R only | 80.4 G, 80.7 G |
| walk only | the walks of `term_walk` run, then each declaration uses engine R only | 82.2 G, 82.5 G |

So the walks of the values and the types use about 1.8 G on Init, and this is the largest cost of engine F mode. The walk reads at most 257 nodes of each value and of each type, so a node costs about 60 instructions. Most of these instructions are in the `Memo` that keeps the nodes that the walk saw: the hash of a pair, the order list for `truncate`, and the check for growth.

The walk now uses a `WalkSet`. It is an open table with 1024 slots, a key and an epoch in each slot, and Fibonacci hashing. The walk puts at most 257 nodes in the set, so the load stays below 1/2, and the table never grows. The table has 8 KiB, so it stays in the first level of the processor cache. The stack of the walk has the term and its binder depth in one item, so a step does one push and one pop in place of two.

The decisions do not change, so the steps on Init stay at 33.08 M. Engine F mode on Init goes from 82.7 G, 82.7 G to 81.6 G, 81.3 G.

We also tried two changes that did not help, and we did not merge them.

1. The store kept the tree size and the binder depth of each node in its side record, so that the test of a deep term was one read. The side record went from 8 to 12 bytes, and each new node read the side records of its fields. With the same decisions as the walk, Init went from 83.5 G to 86.2 G. With the tree size in place of the distinct nodes, Init used 84.3 G, as in 11.23.
2. Engine G before engine R in each query of engine F mode was off. Init did not change.

## 11.25 The same handle before the caches

With engine F, `is_def_eq` looks up a query in the success cache and in the session before the query goes to `is_def_eq_shared`. Engine F does not read these caches, so this first check finds a known success. Engine R does the same lookups in `quick_is_def_eq`, but only after the test for alpha equality.

On Init, 8.9 M queries come to this check, and 7.7 M of them have the same handle on the two sides. For each of these queries, the check did two lookups in large tables, and each lookup read memory that was not in the processor cache. The answer is always true, so the lookups did no useful work. A sample of the process shows the cost in `pair_seen`, `sess_seen` and `Session::find`, about 50 ns for each query.

The check now gives true for the same handle first, and it does the two lookups only for the other 1.2 M queries. A probe that does the lookups and ignores the result costs 3.7 G instructions more than a probe with no lookups, so most of this cost goes away.

| Build | Engine F on Init |
|---|---|
| main | 82.0 G, 82.5 G, 84.2 G |
| same handle first | 80.4 G, 80.9 G, 81.3 G |

The runs are interleaved, with a load average of about 24 on the machine, so the absolute numbers are high. In each pair the change saves 1.6 G to 2.9 G. The steps go down from 33.08 M to 32.02 M, and the verdicts do not change. Engine R does not use this check, so engine R does not change.

Two other probes did not help, and they are not merged. A probe that moved the check after `r_first` let more pairs go to `ground_defeq` first. A probe that marked a missed pair, so that `quick_is_def_eq` did not look it up again, saved about 0.3 G only. The cost was in the queries with the same handle, not in the second lookup.
