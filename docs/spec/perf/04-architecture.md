# 04. The check, from first principles

This section designs the check again. It starts from the cost of the work that a check must do, and not from the official algorithm. Spec 05 stays valid for the rules. This section changes how rulean applies them.

## 04.1 What a check must do

A check of a declaration has three kinds of work:

1. **Walk.** Infer the type of each node of the type and of the value. Each node of the input DAG is visited once for each context in which it occurs.
2. **Compute.** Reduce terms to weak head form and unfold definitions, when two types must be equal.
3. **Compare.** Decide if two types are equal. Most comparisons end at once, because the two sides are the same shared node.

Each other cost is overhead: making new terms, finding them in a hash table, substitution, allocation and copies. A fast kernel makes the overhead small against the three kinds of work.

## 04.2 Where rulean is today

The profiles of 03.3 give the shares on Init:

| Work | Engine F | Engine R |
|---|---|---|
| make and find terms (intern, probe, table) | 26.7% | the largest part (03.3) |
| substitution and its memo | 17.2% | a large part (03.3) |
| node reads | 12.4% | yes |
| `malloc` and `free` | 8.4% | small |
| evaluation (the useful work of NbE) | 19.7% | none |

So more than half of the time of engine F is overhead. Also, engine F evaluates much more than the check needs: it has 17 times the steps of engine R on Init (03.4), because it evaluates each argument of an application. This is why engine F uses more instructions than engine R on Init. The fallback to engine R for a whole declaration is rare (1.5% of the checks).

The fix is not a faster hash table. The fix is to not make the terms.

## 04.3 Principles

**A1. No new terms during a check.** The store holds the terms of the input, and they do not change during the check. The check makes values in the arena of the worker. It makes a term only in four cases: an error message, a term that the environment keeps (for example a recursor rule), a cache key that must be a term, and a query that goes to engine R.

**A2. A query that goes to engine R is one query.** When engine F cannot answer a query, engine R decides that query, and engine F continues with the answer. Engine R does not check the declaration again from the start. Engine R needs terms, so the query is read back into the scratch tier first. This is the only read-back on the normal path.

**A3. The confirm set is small and exact.** Engine R confirms an "equal" answer of engine F only when the rules of the query can give an answer that the official order does not give (spec 05.1). Each rule pair in the confirm set has a reason in the reordering table (spec 05.7.3) or an Arena test. A pair with no reason is removed. Today engine R confirms 13205 answers on Init, and each confirmation reads the two values back into terms (03.4). The target is at most 1000 confirmations on Init.

**A4. The arena has marks.** A query sets a mark in the arena at its start. At its end, the arena goes back to the mark, and only the values that a cache or the caller keeps stay. These values move down to the mark (promotion). So the arena of a declaration holds the live values and not all the values that the declaration made. This removes the limit `MAX_NODES` as a cause of a fallback (spec 08.7.3).

The first form of A4 has no promotion. Engine F sets the mark at the start of each top query of conversion (`f_conv_top`), because the result of such a query is a boolean and not a value. At the end of the query, the arena removes the nodes made after the mark. Three things can hold a handle to these nodes after the query, and the release clears them. An older slot that got a value of the region is put in a write log, and the release makes it empty again, because a slot is a cache of an evaluation. The entries of `c_force` that the query added are removed with `Memo::truncate`, which is O(1). The caches of conversion are cleared at the start of each top query, so they hold no handle. A query that fails, or that changes the value stack, keeps its nodes. A release also removes the cached work of the query, so the release occurs only when an array of the arena is more than half full, and the regions of one declaration can remove at most 2^18 values. After that, the arena fills as before, and engine R checks the declaration.

Result of the first form on Init: the declarations with a full arena went from 617 to 349, and engine F used 309.8 G instructions, against 308.3 G before. A larger budget removes more full arenas but costs more: 2^19 gave 318.5 G and 2^21 gave 337.1 G. On the perf tests the change is less than 2%. So a release does not make Init faster. It moves declarations from engine R to engine F, and on these declarations engine F costs about as much as engine R. The marks are a base for A5 and for later work that makes engine F cheaper on large declarations.

**A5. An argument is evaluated only when it is used.** An argument of an application is a closure (term and environment) until a rule reads it. A rule that does not read an argument, for example `casesOn` on a constructor that does not use a field, never evaluates it. When a rule reads it, the result goes into the closure, so it is evaluated once.

**A6. Equality uses sharing first.** Two values that come from the same term in the same environment are equal at once. Two values that come from a closed term (no loose bound variables) are equal if the terms are the same handle. A value keeps the handle of its term while it is a closure, so this test costs one comparison. This keeps the speed of the official kernel on deep shared terms (smalltt TreeConv, 02.7).

A cache of the value of each closed term is not a good form of A6. On Init, on 2026-11-26, `eval` ran 806 million times, and 102 million of these were on closed terms that are not a leaf. A cache of these values in `eval` gave 408.3 G instructions in place of 402.3 G, and a cache of only the bodies of definitions and the right sides of recursor rules gave 405.3 G. The cost of the lookups was more than the work that the hits saved. A6 must use the handle in the value, as above, and not a table.

Result of A6 on Init, on 2026-11-26 (`rulean check --engine F`, macOS): `same_value` compared two suspended values of the same term only when the two environments were the same handle, and two closures with the same body only when the two environments had the same length and the same form in all values. A term with a loose bound variable range of k reads only the first k values of its environment, and the body of a binder reads only the first k - 1 values of the environment of its closure. `same_value` now compares only these values, so two values of the same term are the same when the values that the term reads are the same. Engine R confirmed 12737 answers in place of 13207, and engine F had 0 faults in place of 1. The run uses 282.7 G instructions in place of 286.0 G, and the 225 Arena tests give the expected verdict.

**A7. Each value keeps its weak head form.** A glued value keeps the folded form and the unfolded form. A second `whnf` of the same value reads the slot and does no work.

**A8. Work across declarations stays.** The type of a constant becomes a value once for each list of levels, and the session keeps it (spec 08.4). The inferred type of a closed term stays in the session. The stamp rule of spec 08.4 applies to each entry.

**A9. No allocation in the hot path.** The arena, the stacks and the scratch buffers are vectors that keep their capacity. A spine is a list in the arena. A temporary list of arguments uses a stack in the worker and not a new `Vec`.

Result of A9 for the arguments of a spine on Init, on 2026-11-26 (`rulean check --engine F`, macOS): before, each read of the arguments of a spine made a new `Vec`, which was 114 million vectors with 168 million arguments in total. The arguments now go on the stack `vstk` of the worker, and the function that pushes them removes them before it returns. The run uses 402.3 G instructions in place of 428.3 G, and the counts of the engine report do not change.

Second result of A9, on Init, on 2026-11-26 (`rulean check --threads 1`, macOS): a sample gave `malloc`, `free` and `realloc` about 3% of the samples of engine F. The largest part came from `whnf_core_app` of engine R, which made a new `Vec` for the arguments of each application, and from `unfold_definition_core`, which copied the levels of the constant before it looked in its caches. The arguments now go on the stack `estk` of the worker, in the same way as `vstk`, and the levels are copied only on a miss of both caches. `is_def_eq_levels` gives "equal" on the same list handle without a copy. Engine F uses 298.8 G instructions in place of 309.8 G, and engine R uses 172.3 G in place of 184.9 G. The counts of the engine report do not change.

**A10. Memory is read in order.** The parser puts the nodes of a term in the order of the input, so the children of a node are before the node. A node has 8 or 12 bytes in a struct of arrays. The arena of values has the same layout. A walk of a term then reads memory mostly forward.

Result of a cache of level instantiation on Init, on 2026-11-26 (`rulean check --engine F`, macOS): a callgrind profile showed that `instantiate_lparams` used 48.8 G of 463.5 G instructions. Most of these calls were on the right side of a recursor rule in an iota step (32.6 G in 3.45 million calls) and on the type of a constant in `infer_constant` (5.7 G). The same term got the same levels many times in one declaration. The cache `c_lps` keeps the result at key (term, levels), and it is cleared with the other caches at the start of each declaration. A term that two constants share uses the cache only for the first constant, because the level parameters of the two constants can have a different order. The run uses 359.9 G instructions in place of 402.3 G. A cache that stays for the full session is not correct, because the scratch tier of the store is cleared after each declaration, and a handle in the cache can then point to a different node.

Result of the structure test before the read-back in `struct_major`, on Init, on 2026-11-26: before, an iota step of engine F read the major premise back to a term each time it was not a constructor application, and only then `cnstr_when_structure` looked at the inductive type. The read-back is now skipped when the type is not a structure without recursion and indices, because then `cnstr_when_structure` gives the term back unchanged. The run uses 348.9 G instructions in place of 359.9 G.

Result of the free variable terms by level, on Init, on 2026-11-26: the read-back of a free variable called `mk_fvar` each time, which was 29.9 million interns of a term that `mk_local` already made. The checker now keeps the term of each level in `lctx_fv`, and `keep_fault` makes it again when it copies the type of the level. The run uses 342.1 G instructions in place of 348.9 G.

Measure of A3 on Init, on 2026-11-26: engine F asked 20165 `conv` queries, and engine R confirmed 13295 answers. 13115 of these came from the type checks of engine F inference, and 180 came from `is_def_eq_shared`. In the confirmed queries, proof irrelevance set `F_TYPED` 9852 times, structure eta 4493 times and K 325 times. A test build that did not confirm the answers of the type checks used 338.4 G instructions in place of 348.9 G. So on Init the confirm set costs about 10 G, and A3 is not the largest item for the target of 04.10.

Second measure of A3, on 2026-11-26, after the inference of projections: engine R confirmed 13207 answers on Init, and the run used 286.0 G instructions. A test build with no confirmation used 277.9 G, so the confirm set costs 8.1 G, or 2.8% of the run. With this build, the 225 Arena tests gave the expected verdict, and these tests include the corner cases of spec 05.1. The run of Init with `--confirm all` gave `r_disagree` 0 on 1814294 queries. This is evidence that the pairs of the confirm set do not change a verdict on these inputs, but it is not a reason in the sense of A3. The reordering table (spec 05.7.3) has no lemma for proof irrelevance, K or structure eta after a delta step, and row O6 has no lemma. So the confirm set does not change until the twin has these lemmas.

Result of A5 on Init, on 2026-11-26 (`rulean check --engine F`, macOS): `eval` now makes a suspended value for an argument that is an application, a projection or a `let`. The first read evaluates it, and the value goes into a slot with the bits of `f_bits` that the evaluation set. Of 27.9 million suspended arguments, 16.6 million were evaluated and 0.7 million were read back as their term with no evaluation, because the term has no loose bound variable. So 40% of these arguments were never evaluated. The run uses 340.0 G instructions in place of 343.8 G for a build of the base on the same day (the result above gave 342.1 G for the same base). The gain is small, because most arguments that are never read are small terms. The first form of the change read the term node of each argument to find its kind, and it used 383.7 G even with no suspended value. The kind is now read from the handle. Three other forms were worse: suspended arguments in the inference of engine F (358.4 G), because the cache of `f_eval` already shares these values, suspended arguments only for closed terms, and a suspended value of a `let` (341.9 G).

Result of suspended binder domains, on Init, on 2026-11-26 (`rulean check --threads 1`, macOS): a sample of engine F showed that about 40% of the samples entered `eval` from `unfold_glued`, and that `eval` evaluated the domain of each lambda and pi at once. Most unfoldings apply the lambda and never read its domain. `eval` now makes a suspended value for a domain that is an application, a projection, a `let`, a pi or a lambda, with the same rule as for an argument under a binder that `quote` opened. A closed suspended domain also reads back as its term. The same sample showed `Nodes::get` as the largest self cost, because the call was not inlined, and it is now inlined into `Store::node`. Engine F uses 285.9 G instructions in place of 312.8 G, and engine R uses 185.0 G in place of 188.1 G for a build of the base in the same machine state.

Result of fixed caches for the term walks, on Init, on 2026-11-26 (`rulean check --threads 1`, macOS): a profile of engine R showed that the build of terms used most of the time. `instantiate` used about 35% of the samples of the check, and the walks of the tables of the two tiers in `intern_expr` used about the same share. Each walk of `Scratch` had a `Memo` on a table that grows and does not get smaller. So after one large walk, each lookup read a large table that was not in the processor cache. The six memos of `Scratch` are now `Lossy` caches with 2^13 slots. A slot keeps one pair, and a new pair replaces the pair in its slot. A miss gives the same result with more work, because the result of a node does not depend on the order of the visits. Also `mk_app` has a front cache with 2^16 slots, keyed by its two fields. A hit gives the handle with no walk of the tables. The cache is empty after `clear_scratch` and after each change of `set_scratch`, so a term keeps one handle. A test build that also walked the tables on each hit found no different handle on Init.

| Build | Engine R | Engine F |
|---|---|---|
| main (after A5) | 227.0 G | 340.0 G |
| `Lossy` caches | 197.3 G | not measured |
| `Lossy` caches and the front cache of `mk_app` | 182.4 G | 312.8 G |

With 2^11 slots the `Lossy` caches gave 194.9 G, and with 2^15 slots they gave 188.0 G. The front cache of `mk_app` gave 186.7 G with 2^12 slots and 184.6 G with 2^14 slots. Two runs of the same build can differ by about 2 G. The peak memory footprint of engine R went down from 492 MB to 463 MB.

## 04.4 Values

The value types of spec 05.4.1 stay. Three changes:

1. **Closures for arguments.** A spine holds argument closures (term, environment) and forced values. A flag tells which. Forcing a closure writes the value into the spine node, so other readers see it.
2. **Source of a value.** A value that comes from the evaluation of a term keeps the term handle and the environment handle. A6 uses them.
3. **Types of free variables.** A free variable is a de Bruijn level and a value for its type, as today. It needs no term in the local context, so a binder costs one arena node and no intern.

## 04.5 Inference

Inference works on a term and a context node (finfer, spec 05.4.5). The result is a value. The changes:

- Projections, literals and free variables are inferred in engine F. For a structure in `Prop`, each field must be a proof, and engine F cannot infer the type of a type. So engine R decides `is_prop` of the field type as one query on its read-back (A2), at the same points as in `infer_proj` of engine R. A projection goes to engine R only when the type of the structure has a form that engine F does not read, and engine R then gives the same faults in the same order.
- The type of a lambda is a pi value that keeps the type of its body as a value under the local of the lambda (`Value::PiOpen`). `conv` compares it with a pi type under that local, so it makes no new local and no read-back. No value outside the body of the lambda has this local, so it is a new variable for the other side too. Each other read of the type reads the body type back once into the body of a closure, and the slot of the value keeps the result.
- A check of an argument type is a `conv` query on two values, as today.
- The cache key is the term and the context node. A closed term uses the root node, so its entry is valid in each context and goes to the session.

Result of the inference of projections, literals and free variables in engine F, on Init, on 2026-11-26 (`rulean check --threads 1 --engine F`, macOS): before, these three forms went to engine R on a term with the free variables of the context in place, and a sample gave this path 0.3% of the samples. Now only `is_prop` of a field of a structure in `Prop` goes to engine R. Now engine F accepts 115085 of 115872 checks in place of 115082, and engine R has 17189 shared queries in place of 20486, because fewer declarations go back to engine R. The run uses 286.0 G instructions in place of 285.9 G, which is inside the noise of about 2 G. So the gain of this item is that engine F does not need engine R for these forms, and not speed.

Result of the lambda type before read-back, on Init, on 2026-11-26 (`rulean check --threads 1 --engine F`, macOS): before, engine F inference read back the type of the body of each lambda, and a sample gave the read-back from inference about 6% of the samples of engine F. Now the run uses 284.8 G instructions in place of 298.8 G. Engine F accepts 115537 of 115871 checks in place of 115522, and engine R confirms 13862 answers in place of 14019. With `--confirm all`, engine R confirmed all 1,882,564 "equal" answers, and `r_disagree` was 0. The 225 Arena tests give the expected verdict.

Measure of the cost of engine F against engine R, on Init, on 2026-11-26, before the lambda type above (a test build with timers around the checks of declarations, one thread): with engine F the checks of values and types took 17.9 s, and with engine R they took 13.7 s. On the 57585 checks that engine F accepts, engine F took 9.69 s and engine R took 10.30 s on the same checks, so engine F was only about 6% faster. On the 349 checks where engine F stops on a full arena, engine F took 3.25 s before it stopped, and engine R then took 3.72 s. The confirmations of engine R took 0.21 s and the read-back for them 0.56 s, so the confirm set (A3) is not a large cost. A smaller arena makes the run use fewer instructions (2^14 nodes: 222.7 G, 2^16: 271.4 G, 2^18: 303.4 G with the timers), but only because more checks go to engine R, which is faster. So the arena size is not a gain for engine F, and the size stays 2^18. The main item for the targets of 04.10 is the cost of engine F on the checks that it accepts. In a sample of these checks, `eval` had 14% of the samples, `Store::node` 14%, the memo lookups 9%, the intern probes 8% and `apply` 6%.

Measure of the delta steps of engine F, on Init, on 2026-11-27 (main at 4e360d4, one thread, counters in a test build): engine F did 23.3 M delta unfoldings and engine R did 5.8 M. The instruction counts were 284.8 G for engine F and 174.7 G for engine R, and the times were almost the same. Of the 21.2 M unfoldings of glued values in engine F, 21.2 M were in `conv` and 35 k were in inference. Lazy delta did 6.2 M of them directly. The other 15.1 M came from `force` in the reduction steps: 8.4 M for the major premise of a recursor, 5.5 M for the structure of a projection and 1.2 M for the arguments of a `Nat` operation. The offset rule, the unfolding of the same head (O12) and `same_value` gave less than 0.9 M together. When each new unfolding was read back to its terms, 67% of them had the same terms as an earlier unfolding of the same declaration. So the main cost of engine F is that it does the same unfolding again with new values. Engine R does not do this, because its terms are shared and its caches use terms as keys. The cost of each step is not the main item.

These changes did not decrease the instruction count, and they are not in the code. Each count is for the full run on Init with engine F:

- An entry of the session for a check of a closed term with no level parameter: 0.99 s of 13.6 s of these checks had a term that an earlier declaration also checked, so the gain is at most 3%.
- A memo of `eval` for a closed application or constant: 299.8 G. For a closed application only: 289.4 G. For a closed application that is not the function of a larger application: 292.9 G. The lookups cost more than the unfoldings that they remove (18.4 M unfoldings in place of 21.2 M).
- A cache of the unfolding by the terms of the arguments, when each argument is a closed suspended argument: 285.8 G. Only 2.8 M unfoldings have such a key, but 93% of them are repeats.
- A memo of the head of an unfolding (`eval` of the body of the definition): at most 0.9 s of gain, because `apply_spine` takes 10.1 s and the head takes 0.9 s.
- `#[inline]` on `Store::node`, `Store::side` and the fields of `ExprId`: 286.0 G.
- An arena of 2^20 nodes: 327.9 G. An arena of 2^22 nodes: 426.6 G.

The allocations are not a large cost either (A9). A test build with a counting allocator, which needs `unsafe` code and is not in the repository, counted 9.4 M allocations and 1.9 M reallocations for engine F on Init, with the parse. Engine R had 17.2 M allocations and 4.2 M reallocations.

So the 80 G target of M9 needs values that share the result of a reduction when they have the same terms, as the terms of engine R do. A value needs a key that is cheap to compute and that is the same for two values of the same term. A closed suspended argument has such a key now (its term). An open value needs a key from its term and the keys of its environment. This is a change of the value model, and it needs a new spec section before the code.

## 04.6 Conversion

The order of the rules does not change. It is the order of spec 05.7.3, and each change of order needs a row in that table and a lemma. The changes are in how each rule runs:

- **Sharing first** (A6), before each other rule.
- **Lazy delta on glued values.** The heights of the definitions decide the side that unfolds, as in the official kernel. The unfolding goes into the slot of the glued value (A7), so the other queries of the declaration reuse it.
- **Arguments before unfolding.** When the two sides have the same head constant, compare the arguments first, as the official kernel does. Use the pair cache for each argument pair.
- **The pair cache.** The successes stay for the declaration. A pair of closed values goes to the session. The failures are for engine R only, as in spec 08.5.

Result of the taken branch, on 2026-11-26 (`rulean check --engine F`, macOS): on `perf/ite-taken-branch`, the three theorems have the form `ite (true = true) piA tA = piA`, where `piA` computes the inverse of a permutation of 300 numbers with a loop. The official order unfolds `piA`, because its height is greater than the height of `ite`. Engine F filled its arena (2^18 nodes, and also 2^24 nodes) on each theorem, and engine R then did the full check with 29 G instructions for each theorem. Now lazy delta unfolds the side with the smaller height first if it has the other side as an argument (row O8 of spec 05.7.3). The branch that the condition takes is `piA`, and the two sides then have the same form. The test uses 1.36 G instructions in place of 87.7 G, and engine F accepts all 2,706 checks of the test.

The same PR lets engine F check an argument of the form `eagerReduce _ _`. Before, engine F stopped and engine R checked the full declaration. Now the hint sets the eager mode of engine R for the query, which engine R uses if it confirms the answer. On `perf/grind-ring-5`, engine F accepts 4,414 of 4,417 checks in place of 4,411, but the test uses 8.57 G instructions in place of 8.43 G.

A note on the measure: `/usr/bin/time -l` counts the instructions of the operating system for the process too. When other jobs use the memory of the machine, the page faults add many instructions. On `perf/magma-list-deep-n36`, two runs of the same binary gave 239 G and 378 G, with the same counts of steps, interns and probes, and 23 s and 98 s of system time. A comparison of two builds must therefore also compare the steps and the interns of the report. On Init, this PR changes the steps by 0.07 percent and the interns by 0.13 percent, and engine F accepts 115,257 checks in place of 115,098.

Result of the cheap projections, on 2026-11-26 (`rulean check --engine F`, macOS): on `perf/proj-applied-struct`, the three theorems have the form `S.fn (gC slowA c) x = S.fn (gC' slowA c) x`, where `gC s c` is `ite (s = c) ...` and `slowA` is a long computation. `eval` reduced the structure of each projection with `force`, so the unfolding of `S.fn` unfolded `gC` at once, and the decision of `slowA = c` evaluated `slowA`. Engine F filled its arena on each theorem, and engine R then did the full check. Now, when a delta step of conversion evaluates an unfolding, `eval` reduces the structure only without delta, as `whnf_core` with cheap projections in the official kernel, and conversion compares the structures `gC slowA c` and `gC' slowA c` before it unfolds them (steps 7 and 8 of spec 05.4.4). The test uses 0.046 G instructions in place of 86 G, and engine F accepts all 110 checks of the test.

The first form of the change used the cheap projections in each `eval`. On Init, engine F then filled its arena on 102 more declarations, most of them proofs by `omega`, and the steps increased by 5 percent. Three changes removed this cost. First, `eval` outside a delta step of conversion reduces the projection with `force` again, as `whnf` in the official kernel. Second, in lazy delta, a neutral projection on one side is reduced before the definition on the other side unfolds (row O9 of spec 05.7.3). Third, the reduction of a neutral projection goes into the force cache. Without the cache, each query on the same projection applied its spine again and made new values, so the caches of conversion did not find the earlier answers. The third change gave most of the gain. Now engine F accepts 115,258 of 115,872 checks on Init in place of 115,257, the steps are 693.0 million in place of 695.1 million, and the interns are 222.1 million in place of 217.7 million.

Result of the waiting `Nat` operations, on 2026-11-26 (`rulean check --engine F`, macOS): on `perf/unfold-before-literal`, the theorems compare `[slowA, 1].sum` with `slowA + (1 + 0)`, where `slowA` evaluates in 2^19 unit steps. The official order of lazy delta can unfold the side with `Nat.add` first, and then the `Nat` extension evaluates `slowA` to a literal. Engine F filled its arena on 3 of the 68 checks, and engine R then evaluated `slowA`. Now a glued binary `Nat` operation with an empty slot waits when an argument is a glued value or a neutral projection, and if only one side waits, the other side unfolds first (row O10 of spec 05.7.3). Both sides then reach `Nat.add slowA _`, and the comparison of the arguments decides. The test uses 0.018 G instructions in place of 89.6 G, and engine F accepts all 68 checks. `perf/unfold-before-literal-bad` still rejects, with 34.2 G, because a sound checker must evaluate `slowA` there. `perf/unfold-before-literal-fallback` still uses 89.5 G: after the unfolding, the arguments `slowA + 1` and `slowA` differ, so engine F declines 3 checks and engine R evaluates `slowA`. The offset rule of `is_def_eq_offset` can remove this cost later. On Init, engine F accepts 115,258 checks on both builds, and the steps are 692.4 million in place of 693.0 million.

Result of the offset rule, on 2026-11-26 (`rulean check --engine F`, macOS): the official kernel peels only `Nat.succ` and literals in `is_def_eq_offset`, so it does not see that `(slowA + 1) + (1 + 0)` and `slowA + (2 + 0)` are both `slowA + 2`. Engine F now views each side as a base and a literal offset before each step of lazy delta (row O11 of spec 05.7.3). The view unfolds `HAdd.hAdd`, `Add.add` and `OfNat.ofNat`, and it peels `Nat.add x n` when the view of `n` is a literal. In `n`, the view can also unfold other definitions, as the `List.foldr` of `List.sum`, for at most 16 steps. The base of the top view is not unfolded, so `slowA` is never evaluated. On `perf/unfold-before-literal-fallback`, engine F accepts all 68 checks with 0.036 G instructions in place of 89.5 G. `perf/unfold-before-literal` uses 0.035 G, and `perf/unfold-before-literal-bad` still rejects, with 33.5 G. On Init, engine F accepts 115,262 checks in place of 115,258, the steps are 691.3 million in place of 692.4 million, and engine R confirms 12,995 queries in place of 12,859.

Result of the unfolding of the same head, on 2026-11-26 (`rulean check --engine F`, macOS): on `perf/short-circuit-and`, the theorems compare `false && a` with `false && b`, where `a` and `b` are open terms that are not equal and are expensive to compare. The official order compares the arguments of the same head `and` before it unfolds the head, so engine F compared `a` with `b`, failed, and engine R did the same work again. Engine F now unfolds both sides first for the same regular head (row O12 of spec 05.7.3). Both sides unfold to `false`, the two values have the same form, and `a` and `b` are not compared. Engine F accepts all checks with 1.07 G instructions in place of 77.3 G, and the official kernel uses 105.6 G. On `perf/discarded-argument` and `perf/discarded-argument-match`, engine F uses 0.03 G in place of 0.46 G and 0.84 G. A `Nat` operation is not unfolded first, because the `Nat` extension evaluates its arguments to literals. A first version of the rule did not have this exception, and on `perf/unfold-before-literal-fallback` it evaluated `slowA` with 33.8 G instructions in place of 0.036 G. A first version also kept the delta bit of the two unfoldings when the arguments gave the answer, so the query went to the confirm set of spec 05.1, and on Init engine R confirmed 15,538 equalities in place of 12,995. Now the bit stays only if the unfoldings give the answer or lazy delta goes on with them. On the Init export, engine F accepts 115,254 checks in place of 115,262, the steps are 697.7 million in place of 691.3 million, and engine R confirms 12,955 equalities in place of 12,995. The extra unfoldings cost the 0.9 percent of steps, and the 8 declarations that engine F does not accept go to engine R.

## 04.7 The fallback and the confirm set

- A "not equal" answer of engine F is a hint (spec 05.1 rule 2). Engine R decides the query on the read-back terms. If engine R says "equal", the answer is "equal" and engine F goes on. If engine R says "not equal", the answer is "not equal".
- A fault of engine F (for example an arena that is full after A4) sends the query to engine R in the same way.
- The bench harness counts the queries of each kind (08.7.3 counters). The report already has `f_fallback`, `f_faults` and `r_confirmed` (03.4).

Result of A2 on Init, on 2026-11-26 (`rulean check --engine F`, macOS): before, a "not equal" answer in the inference of engine F stopped the inference, and engine R checked the declaration again. Then engine F accepted 114129 of 115872 checks, engine R had 44159 shared queries, and the run used 428.9 G instructions. With A2, engine F accepts 114907 checks, engine R has 20099 shared queries, and the run uses 428.3 G instructions. So the full checks again were not a large cost. The cost of engine F is in its evaluation (04.2), and A5 and A1 must give the gain of M9.

Measure of the arena limit on Init, on 2026-11-26 (`rulean check --threads 1 --engine F`, after A5): of the 892 value checks of engine F that failed, 731 failed with a full arena and 160 with an unsupported form. A failed value check goes to engine R for the whole declaration. A smaller `MAX_NODES` makes more checks fail, and each smaller limit made the run faster:

| `MAX_NODES` | Failed checks with a full arena | Engine F |
|---|---|---|
| 2^20 | 181 | 428.2 G |
| 2^18 (today) | 731 | 340.0 G |
| 2^17 | 1372 | 315.7 G |
| 2^16 | 2512 | 298.2 G |
| 2^14 | 5181 | 284.7 G |
| 2^12 | 9898 | 248.8 G |

Engine R alone used 227.0 G on the same build. So on Init, engine F is slower than engine R at each limit, and the large declarations cost engine F more than they cost engine R. A smaller limit only moves work to engine R. The limit stays at 2^18 until A4 and A5 make a value check of engine F cheaper than engine R. Until then, the work on the store and the term walks comes first, because both engines use it.

## 04.8 Literals

- A Nat literal below 2^63 is an inline number in the value, and the extension operations (spec 05.8) on two such numbers use machine arithmetic with an overflow check. A result that overflows becomes a big number.
- A big number is in the literal store of the worker. The limit of spec 05.11 stays.

Result of the `Nat` extension on values, on Init, on 2026-11-26 (`rulean check --engine F`, macOS): `nat_value` made a term for the constant, a literal term for each argument and a term for the application, and then it called `reduce_nat` of engine R, which did a `whnf` of each argument again. Each of these steps interned a term, and the list of the argument terms was a new `Vec`. `nat_value` now reads the literals of the forced argument values and calls the operation of engine R on the handles of the literals, with no term for the application. The name of the operation comes from the table `nat_op_names`, so the lookup makes no term. A fault in the operation has the dummy term, and engine R does the query again with the real term. The run uses 279.3 G instructions in place of 282.7 G, and the 225 Arena tests give the expected verdict. The literals are still in the store, so the inline numbers of the first item are not done.

Result of the inline numbers, on 2026-11-26 (`rulean check --engine F`, macOS): a `Nat` literal below 2^63 is now the value `Small`, which holds the number in two 32-bit halves, so the value has no handle in the store. An operation on two small numbers uses machine arithmetic. A sum, a product or a power that does not fit becomes an interned literal, and `Nat.pow` and `Nat.shiftLeft` use the general path. The iota rule turns a small number into `Nat.succ` of a small number or into `Nat.zero`, and the read-back makes a literal term. On Init the run uses 279.2 G instructions in place of 279.3 G. On `perf/gf3-matrix-product` it uses 41.8 G in place of 42.4 G, and on `perf/grind-ring-5`, `perf/fueled-chain` and `perf/church-numerals` the change is below 1 percent. The gain is small because most `Nat` work of these runs is in engine R. The 225 Arena tests give the expected verdict.

## 04.9 Heartbeats

Engine F counts its steps. The in-process kernel compares the count with the limit of the call (spec 09.6.4). The rule of 09.6.4 stays: rulean must never count more heartbeats than the C++ kernel on a declaration that the C++ kernel finishes. Engine F does less work than engine R on most declarations. Calibration 2 of 09.6.4 is done again with engine F.

## 04.10 Budget for Init

The target G2.a is 22.4 G instructions. The budget is:

| Phase | Today | Budget |
|---|---|---|
| read and SHA-256 | 28.1 G with the parse (03.2) | 0.5 G |
| parse and intern | see the line above | 4.0 G |
| check | about 214 G with engine R (03.2) | 16.0 G |
| report and axioms | small | 0.2 G |
| margin | | 1.7 G |
| total | 242 G | 22.4 G |

The check budget is 16.0 G for 58547 declarations, which is about 270 k instructions for each declaration. Today engine R uses about 3.7 M for each declaration. The budget for Mathlib follows from the same numbers for each byte and for each declaration (07.2).

## 04.11 Proofs

- The arena with marks (A4) needs a lemma: a value that a cache or the caller keeps is not freed, and the promotion keeps the meaning of each value.
- The lazy arguments (A5) need a lemma: a forced closure has the value of its evaluation.
- The sharing test (A6) needs a lemma: two values from the same term and the same environment are equal.
- A2 changes no rule. It changes the engine that decides a query, and both engines are sound.
- A3 changes the confirm set. The twin must show that each removed pair cannot give an answer that the official order does not give, or the pair stays.
