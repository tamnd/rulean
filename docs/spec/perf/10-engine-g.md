# 10. Engine G: a machine for closed terms

This section gives the design of engine G, the step `ground_cmp` that uses it in engine R, and the next work on it. It uses the facts of 09 and a new read of the source of the two fastest rivals on the Arena perf tests.

## 10.1 Why a machine for closed terms

Many perf tests compute a value from closed terms. Examples are `magma-list-deep-n36`, `magma-list-pair-n21`, `gf3-matrix-product` and `ite-taken-branch-bad`. A closed term has no free variables, so the evaluation needs no neutral values, no glued values and no environment of locals. A machine that knows this can use a smaller value, a smaller step, and a shared result for each closed subterm.

## 10.2 The design

Engine G is a call-by-need Krivine machine on closed terms. It is in `crates/rulean-core/src/ground.rs`.

- A value (`GVal`) is a small `Nat`, a big `Nat`, a constructor application, a closure, a partial application, or a type. A constructor application keeps only its fields. The parameters are dropped, because the comparison does not read them.
- A slot of the heap is a thunk, a busy thunk, or a value. A busy thunk that is forced again is a loop, and the machine stops.
- The frames are update, recursor, projection, the two `Nat` operations, and `Quot`.
- Each declaration has a heap of constant values (CAF). A closed argument is shared through its key (term, 1), so the same closed argument gives the same cell in the declaration.
- A copying collector runs each 4096 steps. Its roots are the control, the argument stack, the temporary cells, the frames, the CAF keys and the cells of `ground_cmp`.
- The budgets are 2^25 cells and 2^32 steps for each query. When a budget is used, the machine stops and engine R continues.

## 10.3 The step `ground_cmp`

`ground_cmp` is a refutation step. It never says "equal".

1. It gives two closed terms to engine G and keeps the two cells.
2. It computes the weak head normal form of the two cells. Two different `Nat` values are not equal. Two different constructors of an inductive type that is never a proposition are not equal.
3. For the same constructor, it adds the pairs of fields, the last field first, so that the first field is compared first. Two pairs with the same cell are equal and are not computed.
4. It stops at the first difference, at a lambda, at a type, at a value that can be a proof, or at a budget of 2^22 pairs.

The result is 1 (not equal), 4 (data compared, no difference found) or 0 (no result). The result for each pair of terms is kept in the memo `c_ground_cmp` for the declaration. After a result of 4, the sub-queries of the same query do not run the step again (`gcmp_block`), because a deep equal structure is otherwise compared again at each level.

Engine R runs the step in `lazy_delta_reduction`, after 16 steps on a pair that has no result. A first version ran the step before lazy delta on each closed pair. On Init it computed `Fin`, `BitVec` and `UInt` values that lazy delta proves equal in a few steps, and Init went from 208.6 G to 1846.9 G. With the step after 16 steps, Init is 208.5 G.

Engine F does not run the step. A test made `good/ite-taken-branch` go from 1.07 G to 8.0 G, because an equal pair is computed in full and gives no answer.

## 10.4 What the rivals do

The facts come from a read of the source of each rival. Nothing was built or run.

nano-lean (the `value_checker` engine, run in the Arena as `nl-fast`):

- It uses NbE with strict arguments and lazy delta.
- Values and environments are hash-consed. The cache of `eval` has the key (term, universe substitution, environment), and an environment is cut to the variables that the body reads.
- Each value keeps its `whnf`, its `whnf_core`, its unfolding and its type.
- After 32 unfoldings, a definition is evaluated on new locals, and the result is a case tree (derived rules).
- Argument probes have a budget of steps and a cache of failures.
- A "not equal" result of the comparison is final. There is no second check.

rpylean (revision bbf354d):

- Terms are hash-consed, and each term has slots for its memos.
- `eval_closed_scalar` is a Krivine machine for closed terms, under a tracing JIT.
- A closed constructor application is compiled one time to a constant.
- The arguments are given to a call with no new allocation.

nano-lean (the reference engine `nl-ref`):

- A thunk has the key (term id, keys of the used bound variables). A literal has one canonical key.

## 10.5 The measures

The table gives the sum of the instructions on the 42 perf tests that rulean runs. The rival counts are from the Arena results, on the same 42 tests, for the checkers with correct verdicts.

| Checker | Instructions |
|---|---|
| nano-lean | 86.3 G |
| rulean with `ground_cmp` | 135.7 G |
| gruszka | 142.7 G |
| kefir | 164.4 G |
| lean4lean (29 tests correct) | 182.4 G |
| official-nightly | 902.9 G |

The best rival on each of the slow tests:

| Test | Best rivals |
|---|---|
| `magma-list-deep-n36` | rpylean 1.6 G, nano-lean 2.5 G |
| `magma-list-pair-n21` | rpylean 6.7 G |
| `gf3-matrix-product` | nano-lean 5.0 G |
| `ite-taken-branch-bad` | nano-lean 1.6 G |
| `grind-ring-5` | nano-lean 1.3 G |
| `short-circuit-and-bad` | nano-lean 1.1 G |
| `loop-unfolded-once-bad` | nano-lean 0.3 G |
| `deep-n21` | nano-lean 0.3 G |

## 10.6 Where engine G spends time

A profile of `magma-list-deep-n36` gives 827 samples in `ground_loop`, and 424 of them (about 33%) are in `g_arg`.

- `g_arg` reads `has_loose_bvars` from a side table, and it reads the CAF cache for each closed argument.
- `env_get` walks a linked list.
- `g_iota` calls `rec_shape` and `find_rule` at each step.

`shared-subterm` shows a second problem. Its terms are `ldepth` over a perfect tree of depth 1000 with unary `N.add`. Engine G computes each level from its own thunks, and the time is quadratic in the depth. Engine R is linear on this test, because its cache of `whnf` has the term as key.

## 10.7 The plan

| Step | Change | Expected effect |
|---|---|---|
| G4 | `ground_cmp` in lazy delta, after 16 steps (done) | Cheap refutations of closed data, with no cost on Init |
| G5 | A compiled form of each application, with the kind of each argument found one time. A flat environment in an array. The recursor data kept for each recursor. | A smaller cost for each step of engine G |
| G6 | A memo of thunks at the key (term, cut environment), as in `nl-ref` | Shared work for the same closed subterm, linear `shared-subterm` |
| G7 | After a "not equal" from engine F, engine R does not check the query again (measured, no change, not merged, see 10.8) | No double work on the bad tests |
| G8 | `certain_ne`, a certain refutation of open terms with rigid heads, in lazy delta (done, see 10.8) | Cheap refutations on open terms, for example `loop-unfolded-once-bad` |
| G9 | Derived rules (case trees) | Fewer layers of `brecOn` and matchers |

Each step must keep the verdicts of 07.4 and the Arena tests. Each step is measured on Init and on the perf tests, and a step that does not help is not merged.

## 10.8 The step `certain_ne` (G8)

On each bad perf test, the top query of engine F stops with `ArenaFull`, and engine R then checks the declaration. So the cost of a bad test is the cost of engine R on a query that is not equal. On `loop-unfolded-once-bad`, engine R unfolds the two loops in lock step. At each step, lazy delta finds `Bool.and A B` against `Bool.and A' B'` with the same head, and `is_def_eq_args` compares `B` against `B'` first, because it starts at the last argument. `B` is the rest of the loop, so each step compares the full rest of the loop before it unfolds `Bool.and`. The first arguments are `g w (0 + k)` and `g w (0 + k + 1)`, and these terms are certainly not equal.

`certain_ne(a, b)` is true only if the official kernel returns false for `a =?= b`. It is true if the two terms in weak head normal form have one of these shapes, and the type of `a` is a data type:

- Two different `Nat` literals.
- Two different constructors, or the same constructor with a field that is certainly not equal.
- A constructor or a literal against a rigid term.
- Two rigid terms with different heads, or the same head and an argument that is certainly not equal.

A rigid term is an application of a free variable with no value, a recursor that is stuck on a rigid major premise, or a projection of a rigid term. The recursor must not be K-like, and the type of its major premise must have two or more constructors. A data type is an inductive type with two or more constructors in a sort that is not zero for all values of the level parameters. So structure eta, the unit-like rule and proof irrelevance do not apply. For such terms, lazy delta cannot unfold a head, `is_def_eq_app` finds a pair that is not equal, and no later step of `is_def_eq_core` applies. This is the argument of `ground_cmp` (10.3) for open terms. The search stops at a depth of 3. The type is inferred last, because the shape test is cheaper.

Engine R uses the step in `lazy_delta_both`. If a pair of arguments of the two applications is certainly not equal, `is_def_eq_args` cannot succeed, so the step does not call it and unfolds the two terms. The step only removes a call that returns false, so it does not change a result of the query. At this point the arguments go through `whnf_core` and not `whnf`, so the step does not unfold an argument that lazy delta does not unfold. The arguments under a rigid head go through `whnf`.

A second use in `is_def_eq_app` was tested and not kept. It made `loop-unfolded-once-bad` 0.1 G faster, but it made `refute-cheap-last` go from 0.53 G to 0.64 G, because the search computed the fields of `N.S` chains that `is_def_eq` compares lazily.

Step G7 (no second check after a "not equal" from engine F) was also measured. Engine F stops with `ArenaFull` on all bad perf tests before it gives a "not equal", so G7 gave no change and was not merged. An arena of 2^19 to 2^23 nodes does not help, because the search of engine F on a query that is not equal grows with the arena.

| Test | Before | After | Best rival |
|---|---|---|---|
| `bad/loop-unfolded-once-bad` | 9.37 G | 1.39 G | nano-lean 0.26 G |
| sum of the perf tests | 118.4 G | 110.6 G | nano-lean 86.3 G |
| Init, `--engine F --threads 1` | 208.6 G | 208.9 G | |
