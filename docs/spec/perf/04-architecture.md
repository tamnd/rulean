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

**A5. An argument is evaluated only when it is used.** An argument of an application is a closure (term and environment) until a rule reads it. A rule that does not read an argument, for example `casesOn` on a constructor that does not use a field, never evaluates it. When a rule reads it, the result goes into the closure, so it is evaluated once.

**A6. Equality uses sharing first.** Two values that come from the same term in the same environment are equal at once. Two values that come from a closed term (no loose bound variables) are equal if the terms are the same handle. A value keeps the handle of its term while it is a closure, so this test costs one comparison. This keeps the speed of the official kernel on deep shared terms (smalltt TreeConv, 02.7).

**A7. Each value keeps its weak head form.** A glued value keeps the folded form and the unfolded form. A second `whnf` of the same value reads the slot and does no work.

**A8. Work across declarations stays.** The type of a constant becomes a value once for each list of levels, and the session keeps it (spec 08.4). The inferred type of a closed term stays in the session. The stamp rule of spec 08.4 applies to each entry.

**A9. No allocation in the hot path.** The arena, the stacks and the scratch buffers are vectors that keep their capacity. A spine is a list in the arena. A temporary list of arguments uses a stack in the worker and not a new `Vec`.

**A10. Memory is read in order.** The parser puts the nodes of a term in the order of the input, so the children of a node are before the node. A node has 8 or 12 bytes in a struct of arrays. The arena of values has the same layout. A walk of a term then reads memory mostly forward.

## 04.4 Values

The value types of spec 05.4.1 stay. Three changes:

1. **Closures for arguments.** A spine holds argument closures (term, environment) and forced values. A flag tells which. Forcing a closure writes the value into the spine node, so other readers see it.
2. **Source of a value.** A value that comes from the evaluation of a term keeps the term handle and the environment handle. A6 uses them.
3. **Types of free variables.** A free variable is a de Bruijn level and a value for its type, as today. It needs no term in the local context, so a binder costs one arena node and no intern.

## 04.5 Inference

Inference works on a term and a context node (finfer, spec 05.4.5). The result is a value. The changes:

- Projections, literals and free variables are inferred in engine F. Today they go to engine R (finfer.rs header), and engine R needs a term with the free variables in place.
- The type of a lambda is a pi value whose body is a closure of the inference. Today the body is read back into a term (finfer.rs header), and the read-back makes new terms.
- A check of an argument type is a `conv` query on two values, as today.
- The cache key is the term and the context node. A closed term uses the root node, so its entry is valid in each context and goes to the session.

## 04.6 Conversion

The order of the rules does not change. It is the order of spec 05.7.3, and each change of order needs a row in that table and a lemma. The changes are in how each rule runs:

- **Sharing first** (A6), before each other rule.
- **Lazy delta on glued values.** The heights of the definitions decide the side that unfolds, as in the official kernel. The unfolding goes into the slot of the glued value (A7), so the other queries of the declaration reuse it.
- **Arguments before unfolding.** When the two sides have the same head constant, compare the arguments first, as the official kernel does. Use the pair cache for each argument pair.
- **The pair cache.** The successes stay for the declaration. A pair of closed values goes to the session. The failures are for engine R only, as in spec 08.5.

## 04.7 The fallback and the confirm set

- A "not equal" answer of engine F is a hint (spec 05.1 rule 2). Engine R decides the query on the read-back terms. If engine R says "equal", the answer is "equal" and engine F goes on. If engine R says "not equal", the answer is "not equal".
- A fault of engine F (for example an arena that is full after A4) sends the query to engine R in the same way.
- The bench harness counts the queries of each kind (08.7.3 counters). The report already has `f_fallback`, `f_faults` and `r_confirmed` (03.4).

## 04.8 Literals

- A Nat literal below 2^63 is an inline number in the value, and the extension operations (spec 05.8) on two such numbers use machine arithmetic with an overflow check. A result that overflows becomes a big number.
- A big number is in the literal store of the worker. The limit of spec 05.11 stays.

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
