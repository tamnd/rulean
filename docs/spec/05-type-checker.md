# 05. The type checker

This document specifies the core judgments of rulean: type inference, weak head normalization, and definitional equality. It also specifies the semantics profiles, the literal extensions, the unsafe quarantine, the resource limits and the deviation register. Inductive types and quotients are in 06. The term store is in 04.

The source of truth for official behaviour is research/A-lean-kernel.md, sections 1 and 7. That report read lean4 `master` at ab8894fb (2026-11-21) and the release tags. Each rule below names its source as `A§n`.

## 05.1 Design principle: the same relation, a faster search

The official kernel does not decide a clean mathematical relation. Its definitional equality is a fixed sequence of heuristic steps. It is not transitive (lean4#14806, lean4#12520). Some answers depend on the order of the steps (A§1.8, the proof irrelevance position).

So rulean cannot use "any complete conversion checker" and still match the official verdicts (P2). A more complete checker accepts more, and that breaks P2.b. A different order of steps can accept or reject differently, and that breaks P2.a or P2.b.

rulean therefore has two engines that share one rule set:

| Engine | Purpose | Algorithm | When it runs |
|---|---|---|---|
| **F, fast** | speed (P1) | NbE over glued values (05.4), with sessions and caches (08) | every query, first |
| **R, reference** | parity (P2) | a transcription of the official `is_def_eq_core`, `whnf_core` and `infer_type_core`, step for step, over rulean terms | only when F answers "not equal", or fails |

The rules are:

1. **F uses only official rules.** Each rule that F applies is one of the rules of A§1.6 to A§1.11, with the same preconditions. F may apply them in a different order, and it may skip steps, only where the order cannot change the answer. Each such reordering has a lemma in the twin (10.4) and a row in the reordering table (05.7.3).
2. **A reject needs R.** rulean rejects a declaration only when engine R also rejects it. F's "equal" answers are final. F's "not equal" answers are hints.
3. **Both engines are verified for soundness.** Both are in the twin and in the Rust core. Engine R is short (about 2,000 Rust lines, the size of `type_checker.cpp`), so its proof is cheap.
4. **R is the parity oracle in tests.** In the conformance suite (11), every query is also run in R with `--engine=R`, and the answers are compared.

**Over-acceptance risk.** Rule 2 protects P2.a. It does not fully protect P2.b. The official algorithm is not transitive, so a search that uses only official rules can still find an equality that the official order misses. The known cases are in the Arena corner-case group (eta-struct-major, unit-like, subject-reduction-redex, transitivity through Quot and Acc). rulean handles this with a **confirm set**:

- Engine F records, for each "equal" answer, the rules it used (a small bit set, not a full trace).
- A rule that a cache saves still counts. Engine F keeps the unfolding of a constant in a slot and the result of `force` in a cache, and both live across the queries of a declaration. So a slot hit records a delta step, and a hit in the `force` cache records the rules of the steps that it saves.
- If the set contains a type-directed rule (proof irrelevance, structure eta, unit-like, string expansion) together with a delta step on the same query, engine R confirms the answer.
- If R says "not equal", the answer is "not equal". The case goes into the regression corpus.
- In CI the confirm set is "all queries" (`--confirm=all`). That run shows how often the default confirm set is too small. The target is zero differences on the conformance corpus (11.2).

On Mathlib every declaration is accepted, so R runs only on the rare "not equal" sub-queries that are later rescued by another step (for example a failed argument comparison that lazy delta then resolves). Section 08.6 budgets this.

## 05.2 Semantics profiles

The official kernel changes between releases (A§1.15). rulean names each behaviour set as a **profile**. A profile is a set of flags. The code tests flags, never version strings.

| Profile | Lean releases | Flags that differ |
|---|---|---|
| `v4.35` | v4.35.0, v4.36.0, v4.36.x | baseline |
| `v4.37` | v4.37.0-rc1 and later 4.37 releases | `proof_irrel_first` (#15103), `no_whnf_prop_major` and `eta_subsingleton_major` (#15371), `eta_partial_ctor` (#15373), `count_64` (#16279), `inductive_loose_bvar_check` (#16512) |
| `master` | the lean4 `master` that rulean CI tracks | `v4.37` plus `no_large_elim_rec_prop` (#13851) |

Rules:

- The default profile comes from the `lean.version` field in the export meta line (07.1), or from the `lean_version` field of the `.olean` header (07.3). An unknown version is an error, unless the user passes `--profile`.
- A new Lean release gets a profile within 14 days of its tag (14.4). Until then, rulean reports `unsupported-version` and exits with the decline code.
- Arena "either" tests are pinned per profile: the expected verdict is the verdict of the official kernel of that profile (11.3).
- A flag is never removed. Old profiles stay supported for 12 months after the release that replaced them.

## 05.3 Judgments

rulean implements these judgments. Γ is a local context of free variables (04.4). E is the environment cut of the declaration (08.3).

| Judgment | Function | Meaning |
|---|---|---|
| E; Γ ⊢ e : T | `infer(e, mode)` | infer the type of e. `mode` is `check` or `infer_only` (A§1.9) |
| E; Γ ⊢ e ⇝ w | `whnf(e)` | w is the weak head normal form of e |
| E; Γ ⊢ e ⇝c w | `whnf_core(e, cheap_rec, cheap_proj)` | head reduction without delta and Nat (A§1.6) |
| E; Γ ⊢ a ≡ b | `is_def_eq(a, b)` | a and b are definitionally equal |
| E ⊢ l ≡ l', l ≥ l' | `level::is_equivalent`, `level::is_geq` | level relations (05.6) |

Each function returns `Ok(result)`, `Err(KernelError)` or `Err(Resource)` (05.11). There are no panics on any input (12.4).

## 05.4 Engine F: evaluation by values

### 05.4.1 Values

Values live in a per-worker arena (04.5). They are data, not Rust closures, because the Aeneas subset has no closures (10.6).

```
Value ::= VSort(level)
        | VLit(lit)
        | VLam(binder_info, dom: ValueId, clo: Closure)
        | VPi (binder_info, dom: ValueId, clo: Closure)
        | VNeu(head: Head, spine: SpineId)
        | VGlued(const: ConstApp, spine: SpineId, unfolded: Lazy<ValueId>)
Closure ::= { env: EnvId, body: TermId }               -- body is a stored term (04.2)
Head  ::= HFVar(level: u32, type: ValueId)            -- de Bruijn level, with its type
        | HConst(ConstApp)                            -- axiom, opaque, inductive, constructor, quot, or a stuck recursor
        | HProj(struct_name, idx, value: ValueId)     -- stuck projection
        | HRec(RecApp)                                -- stuck recursor application
Spine ::= list of ValueId (in the arena, as a linked chunk array)
Env   ::= persistent list of ValueId (in the arena)
```

- Free variables are named by de Bruijn level with their type, as in nanoda and con-leche (B§8.1). Levels are stable under binders, so values and cache keys stay valid when the checker goes under a binder.
- `VGlued` keeps both forms of a definition application: the folded form `c.{us} args` and a lazy pointer to its unfolding. This is the glued evaluation of smalltt (B§8.2). Conversion compares folded forms first, which gives the effect of official lazy delta.
- `let` is evaluated by extending the environment. That is zeta reduction (A§1.6). The let-bound value is evaluated lazily (call by need), so an unused let costs nothing.
- Literals stay literals. They become `Nat.succ` or `String.ofList` forms only when a rule needs a constructor (A§1.6 step 4, A§1.7).

### 05.4.2 Evaluation

`eval(env, t)` maps a stored term to a value. `apply(v, arg)` applies a value. `force(v)` unfolds a glued head and reduces until the head is not a redex.

- β: `apply(VLam(_, _, clo), a) = eval(clo.env ++ [a], clo.body)`.
- δ: `force(VGlued(c, sp, u)) = force(apply_spine(u, sp))`. `u` is computed once, from the value of `c` instantiated at its levels. The instantiation is cached per (constant, level list) (`m_unfold`, A§1.5).
- ι: a recursor application whose major premise forces to a constructor (or a literal, or a K-target, or a structure eta-target) steps by the rule of A§1.6 steps 1 to 7. The profile flag `no_whnf_prop_major` decides whether the major is forced when its type is a proposition.
- proj: as in A§1.6. The constructor's inductive must equal the projection's structure name (#14631).
- Quot: `Quot.lift f h (Quot.mk r a) ⇝ f a` and `Quot.ind h (Quot.mk r a) ⇝ h a`, with the argument positions of A§1.6.
- Nat and String: 05.8.

### 05.4.3 Read-back

`quote(k, v)` turns a value back into a stored term at binder depth k. It is used for three things only: the result of `infer` when a type must be stored, the arguments of type-directed rules that need `infer` on a neutral term, and error messages. Read-back of a glued value gives its folded form. This keeps types small, as the official kernel's `cheap_beta_reduce` does.

### 05.4.4 Conversion in engine F

`conv(k, a, b)` on values follows the official order of A§1.8, with the reorderings of 05.7.3:

1. Quick checks: same handle, same value id, a cached success (08.5), sorts by `is_equivalent`, literals by value, binders by domain and body.
2. Bool shortcut (A§1.7).
3. Proof irrelevance. Its position depends on the profile flag `proof_irrel_first` (05.7.1).
4. Head reduction without delta (`force_core`).
5. Lazy delta on glued heads: same head and levels, compare the arguments; if that fails, unfold the side with the greater height, or both if the heights are equal (A§1.8 step 5). Nat offset and Nat reduction are tried here with the fvar guard of A§1.7.
6. Same constant with equivalent levels; same free variable.
7. Projections against projections.
8. Full projection reduction and a recursive call.
9. Neutral against neutral: same head, then the spines pointwise.
10. Function eta, structure eta, string literal expansion, unit-like (05.7.2).
11. Otherwise "not equal". Then engine R runs on the read-back terms (05.1, rule 2).

### 05.4.5 Inference in engine F

Engine F also does the type check and the value check of a declaration (A§1.4, `check_constant_val` and the value check of `add_definition`). The judgments are the judgments of `infer_type_core` in check mode. Engine F only changes the representation: it infers types as values, and it does not substitute.

- **Context tree.** A context is a node in a tree. A binder node has the key (domain term, parent node). A `let` node has the key (value term, parent node), and its type term must also be the same. The nodes are hash-consed, so two binders with the same domain in the same context are one node. Each node keeps the environment of the values of its bound variables and the environment of their types. A binder node has a local of the official local context at the de Bruijn level of the node, with the read-back of its domain as the type. A `let` node gets its local only when a term must be read back in its context.
- **Caches.** The type of a term is cached with the key (term, node, mode), where the mode is infer-only or check. The value of a term is cached with the key (term, node). A closed term uses the root node, so its entries are shared by all contexts. The tree and the caches are cleared with the arena at the end of each declaration (04.5).
- **Rules.** A bound variable gets its type from the environment of the node. A sort, a constant, a pi type and an application follow `infer_type_core`: a pi type gets `imax` of the levels of the domain and of the body, and an application forces the type of the function to a pi value, checks the type of the argument against the domain in check mode, and applies the closure to the value of the argument. A lambda gets the pi value of its domain and of the read-back of the type of its body. A `let` checks in check mode that its type is a sort and that the type of its value is equal to its type. Then the body is inferred in the `let` node. A literal, a projection and a free variable go to `infer_type_core` of engine R, on the term with the locals of the context.
- **Evaluation.** An application and a `let` are evaluated with the context tree, so each node of a long chain is evaluated once in each context. A closure body without loose bound variables does not use its argument, so the argument is not evaluated.
- **Stops.** Each equality check uses conversion of engine F (05.4.4). If the answer is "not equal", or if the check meets `eagerReduce`, engine F stops. A fault, for example a full arena, also stops engine F. The fault is removed, and engine R does the full check of the declaration (05.1, rule 2). So a reject always comes from engine R.
- **Confirm.** If the answer is in the confirm set (05.1), engine F reads back the two values, and engine R compares the terms. If engine R gives "equal", engine F continues. If engine R gives "not equal", engine F stops, and engine R does the full check of the declaration. On the Init export of v4.36.0, a stop at each answer in the confirm set caused 10,310 of the 11,775 stops of engine F.
- **Confirm all.** With `--confirm all`, engine R does not confirm each answer in the confirm set, because engine R checks the full declaration again after engine F accepts it. If engine R rejects a declaration that engine F accepted, the JSON report counts it in `r_disagree`.

Inference in engine F is a reordering of the official algorithm: the order of the checks and the form of the inferred types are different. Its row in 05.7.3 is O6.

## 05.5 Engine R: the reference transcription

Engine R is a direct port of `type_checker.cpp`, `inductive.h` and `quot.cpp` from the release of the profile. It works on stored terms with substitution (`instantiate`, `abstract`), as the official kernel does.

Rules for R:

- Same function names, same step order, same caches with the same keys (A§1.5). Success caches only. No union-find (#14806).
- One Rust function per C++ function where possible. Each function has a comment with the C++ file, line range and commit.
- R has no performance target. It must not time out where the official kernel does not, so its limits are the official limits times 4 (05.11).
- When the official kernel changes, R changes first. F follows after the reordering lemmas are updated (14.4).

R is also the fallback for the whole declaration under `--engine=R`. That mode is for debugging and for the conformance oracle.

## 05.6 Universe levels

Official algorithms, exactly (A§1.10):

- `mk_max` and `mk_imax` simplification, including `imax 1 u = u` (#7631).
- `normalize`: push succ inward, flatten max, sort by `is_norm_lt`, keep the maximum offset for each base, drop subsumed constants.
- `is_equivalent(l1, l2)`: `l1 == l2` or `normalize(l1) == normalize(l2)`. This is incomplete by design. rulean does not use a complete decision procedure by default, because a complete one accepts the Arena corner cases `imax-nested-absorption` and `imax-right-successor`, which the official kernel rejects.
- `is_geq`: the structural algorithm on normalized forms.
- `normalizes_to_zero`: used by `is_prop` and Prop inductive detection.

Levels are hash-consed in their own table (04.3). `normalize` results are cached per level handle for the whole run. Levels are small, so this cache is a plain array indexed by handle.

The con-leche semantic comparison (complete, coNP-hard in general, B§8.2) is available only under `--rules=con-leche` (05.12, D4).

## 05.7 Type-directed rules

### 05.7.1 Proof irrelevance

- If `infer(t)` is a proposition (`is_prop`), then `t ≡ s` holds when `infer(t) ≡ infer(s)` (A§1.8 step 3).
- `is_prop` fails closed on a stuck sort (#14807, #14843). A stuck sort is a reject, not "false".
- Position: with flag `proof_irrel_first`, on the original terms before any reduction. Without it, after `whnf_core` on the reduced terms.

### 05.7.2 Eta rules

- **Function eta**: a lambda against a non-lambda whose type reduces to a Pi (A§1.8 step 10).
- **Structure eta**: one side is a constructor application of a non-recursive structure-like inductive (one constructor, zero indices). The types must be definitionally equal. Then compare the fields with projections of the other side. With flag `eta_partial_ctor`, a partial constructor application is also allowed (#15373).
- **Unit-like**: a non-recursive structure whose constructor has **zero fields**, and the types are equal. The extension #15372 was reverted (#16443). rulean does not implement it in any profile.
- **String literal expansion**: a string literal against an application of `String.ofList` expands the literal (A§1.7).

### 05.7.3 Reordering table

Engine F may change the order of steps only as listed here. Each row has a twin lemma that the reordering gives the same answer as the official order on every input where both terminate. A row without a lemma is not allowed in F.

| ID | Reordering | Why it is safe | Lemma |
|---|---|---|---|
| O1 | Compare glued folded forms before forcing (lazy delta by value) | the official step 5 does the same on terms | `conv_glued_eq_lazyDelta` |
| O2 | Cached success before any step | official step 1 | `cache_true` (10.4.3) |
| O3 | Skip `whnf_core` when both sides are already in head normal form | `whnf_core` is the identity on them | `force_core_idem` |
| O4 | Evaluate `let` lazily | zeta is confluent with all other rules here; the official kernel also substitutes | `zeta_lazy` |
| O5 | Unfold both sides at once when heights are equal | official step 5 does the same | `lazyDelta_equal_height` |
| O7 | Compare two values by their form before any step, and stop lazy delta when both sides have the same form | official step 1 compares two terms by their structure; two values of the same form read back to the same term | `same_true`, `lazyDelta_same` |
| O6 | Infer types as values in a context tree (05.4.5) | the typing rules are the official rules, each equality check is a conversion of engine F, and a reject comes from engine R | not done |

Rows are added only with a lemma, an Arena regression test and a corpus run that shows no verdict change.

Row O6 has no lemma yet. This is an open item of M4. Until the lemma is proved, engine F is not the default engine, and the `arena` CI job runs each Arena test with `--confirm all`.

The lemmas of O1 to O5 and O7 are in `proof/RuleanProof/Twin/Order.lean` and `proof/RuleanProof/Twin/Zeta.lean`. They are proved on a twin of the step order. The terms of this twin have no binders and no types, and the twin has no proof irrelevance and no eta. Theorem R1 (10.3) must still connect this twin to the Aeneas model of engine F.

## 05.8 Nat and String literal extensions

The kernel has exactly 15 built-in Nat operations (A§1.7): `Nat.succ`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`.

Rules, as in the official kernel:

- `Nat.zero` counts as the literal 0.
- `Nat.succ` takes one argument. The other operations take exactly two. Only full applications reduce.
- Each argument is reduced with full `whnf` (including delta) and must then be a literal.
- Size guard: a result above `LEAN_NAT_MAX_SIZE` (default 128 MiB) is an error. `Nat.pow` and `Nat.shiftLeft` need the exponent or shift at most 2^32 − 1, or the step is an error (A§1.7 table).
- `Nat.beq` and `Nat.ble` return the constants `Bool.true` and `Bool.false`.
- In lazy delta, the extension fires only when neither side has free variables, or when the `eagerReduce` hint is set (#9865).
- `Nat.log2`, `Nat.powMod`, `Int`, `Fin`, `UInt*` are **not** kernel operations. They unfold as ordinary definitions.

**Primitive pinning.** The official kernel matches these operations **by name**. It does not check that `Nat.add` has the expected definition (A§1.7). An export that defines its own `Nat.add` with another meaning would make the kernel compute the wrong value. That breaks the model theorem (T1).

rulean therefore checks each primitive constant when it is added to the environment. The check compares the declaration with a reference declaration, built into rulean, for each name in the official `primitiveTargets` list (A§1.7): the `Nat` operations, `String.ofList`, `Char.ofNat`, `List`, `eagerReduce`, `Nat`, `String`, `String.mk`, `Char`. The comparison is structural equality of type and value after name resolution. rulean keeps a SHA-256 digest of each reference declaration, not the declaration itself. The digest covers the level parameters, the type and the value of a definition, and the type, the parameter and index counts and the constructors of an inductive type. It ignores binder names and binder info. It does not look into the constants that the declaration refers to. `scripts/pin-digests.py` computes the reference digests from an export of the profile.

- If the declaration matches, the extension for that name is on.
- If it does not match, the extension is off for that name, and the constant unfolds like any definition. This is deviation D1 (05.12). It can only change the verdict on exports that redefine core primitives. The official kernel itself "makes no guarantees" on them (A§1.7, `lake check` comment).

The bignum `rulean_nat::Nat` is specified in 04.6. Literal hashing uses all bits (lean4#16146).

## 05.9 Declarations

Checks for each declaration kind, exactly as A§1.4:

| Kind | Check |
|---|---|
| common | name not declared; no duplicate level parameters; no metavariables, no free variables, no loose bound variables; every level parameter used is declared |
| axiom | the type is a type (`ensure_sort`) |
| definition (safe) | the type is a sort; the value is checked in E **without** the declaration; `infer(value) ≡ type` |
| definition (partial) | as safe, and it may refer to other partial constants |
| definition (unsafe) | quarantine (05.10) |
| theorem | the type is a proposition (`is_prop`, fails closed); the value is checked; `infer(value) ≡ type` |
| opaque | the value is checked against the type |
| mutual definition | only unsafe or partial; all have the same safety and the same level parameters; no duplicate names |
| quot | 06.5 |
| inductive | 06 |

**Theorems unfold.** `constant_info::has_value()` is true for theorems, and the official `is_delta` uses it (A§1.3). So rulean unfolds theorems, with opaque hints (lowest priority). This differs from con-leche and con-ron. It needs specification extension X3 (10.2.2).

**Infer-only mode.** Infer-only mode skips argument and binder checks. rulean uses it only where the official kernel does: recursor rules, `check_recursors`, and values already checked in the same declaration (A§1.9). The twin proves that infer-only results agree with checked results on well-typed input (10.4).

## 05.10 Unsafe quarantine

The default lean4export run omits `unsafe` and `partial` declarations. With `--export-unsafe` they are present (A§4.1). The official kernel accepts them with weaker checks.

rulean puts every `unsafe` declaration and every `partial` declaration in the **quarantine tier**:

- **Checks**: the same as the official kernel. For an unsafe definition, the header is added first, so the value may refer to the name. For an unsafe inductive, strict positivity is skipped. Every other check is done.
- **Separation**: a safe declaration that refers to a quarantine constant is rejected (the official rule, A§1.9 `infer_constant`). A partial declaration may refer to partial constants but not to unsafe ones.
- **Theorem**: T3 (10.1) proves the separation. The model in T1 is built for the safe tier only.
- **Report**: the JSON report lists quarantine constants in a separate array (09.4).

## 05.11 Resource limits

A resource failure is not a verdict (02.2, P2 exceptions).

| Limit | Official | rulean default | `--limits=official` |
|---|---|---|---|
| recursion depth | 16 × maxRecDepth (#13956) | explicit stacks in a `Vec`; the limit is memory, by default 1 GiB of stack data per worker | 16 × maxRecDepth on the R-engine call depth |
| heartbeats | per declaration (#16548); `leanchecker --from-export` sets no limit | none in external mode | rulean counts R-engine steps and reports `resource:heartbeat` at a calibrated bound (09.6) |
| Nat literal size | 128 MiB | 128 MiB; this is semantics, not a resource limit, so it is never changed | same |
| memory | none | `--max-memory`, default 0.8 × physical memory | same |
| wall time | none | `--timeout`, default none | same |

Rules:

- rulean must not fail with `resource` on any input where the official kernel of the profile succeeds within its limits. This is part of P2.a and is tested on the whole corpus (11).
- When rulean succeeds where the official kernel times out, the declaration is accepted. This is deviation D2. The report flags it when the R engine needed more than the official bound.
- Deep terms are handled with explicit work stacks, never with Rust recursion beyond a fixed bound. Stack overflow is not a possible outcome (12.4).

### 05.11.1 Memory and time limits

- **Values.** `--max-memory <size>` takes a number of bytes with an optional unit `K`, `M`, `G` or `T` (powers of 1024), or `none`. `--timeout <time>` takes a number of seconds with an optional unit `s`, `m` or `h`.
- **Default memory limit.** The default is 0.8 times the physical memory. On Linux, rulean reads `MemTotal` from `/proc/meminfo`. On macOS, rulean reads `hw.memsize` from `sysctl`. On other systems, the default is `none`.
- **Measure.** The measure is the bytes of the arrays and tables of the store, the environment, the local context, the caches, the value arena of engine F and the session. It does not include the allocator overhead, so the resident memory of the process is larger than the measure.
- **Store.** When an array of expressions or the literal array must grow and the store would then be above the budget, the store goes into its full state (04.2.1). The result is the resource code, as for a full array.
- **Checker.** The checker compares the measure with the budget before each declaration and each 4096 calls of `enter`. Above the budget, the declaration fails with `MemoryLimit`, which is a resource failure.
- **Workers.** With `--threads n`, the main checker and the workers share one budget. Each worker has a copy of the store, and the copies count. The core has no shared state, so the driver keeps the total. Before and after each job, a worker adds the change of its memory to the total and reads the memory of the other checkers. Inside a job, the worker compares its own memory plus this value with the budget.
- **Time.** The checker runs on its own thread. At the deadline of `--timeout`, the main thread gives the resource code and the report, and the process stops. The report has the SHA-256 of the input file, which the main thread reads again. A run on standard input and a run of `rulean olean` give no report at a timeout, because the main thread cannot get the SHA-256.
- **Readers.** The readers check the budget before their large buffers grow. The CLI reads an NDJSON input through a read buffer of fixed size (1 MiB). A line that is fully in the read buffer goes to the parser with no copy. A longer line goes into a line buffer, and the CLI checks the line buffer and the buffer of a binary input. The NDJSON parser checks its three index tables and its list of declarations. The olean reader checks the parts of a module and the tables of its decoder before it allocates the tables. Above the budget, the result is `StoreFull`, which is the resource code. During the check, the list of declarations counts in the measure of the checker.
- **Open items.** The vectors inside a declaration (for example the constructors of an inductive), the tables of the binary decoder and the small temporary buffers of the parse are not in the measure. The size of each of these is bounded by the length of the input. Spec 12.3 rule 4 asks for a check of every allocation, and this is not done yet.

## 05.12 Deviation register

Every known difference from the official kernel of the profile is a row here. A release cannot add a deviation without a row. The register is also published as `deviations.json` with the release.

| ID | Input class | Official | rulean default | Option |
|---|---|---|---|---|
| D1 | export that redefines a primitive (`Nat.add`, `String.ofList`, …) with another value | uses the built-in operation | unfolds the user definition (05.8) | `--trust-primitives-by-name` gives official behaviour, outside T1 |
| D2 | declaration where the official kernel hits a resource limit and rulean does not | `resource` error | accept, with a flag | `--limits=official` |
| D3 | Arena "either" corner cases | profile-specific | same verdict as the profile; each test has a row in `deviations.json` with status `same` | none |
| D4 | extra rules that con-leche has and the official kernel does not: semantic level comparison, proof irrelevance fall-through, `And.rec` rescue, extra large elimination | reject | reject | `--rules=con-leche` accepts; still covered by T1 |
| D5 | `.olean` input whose cached hashes or flags disagree with recomputed ones | uses the cached data without checking | recomputes; decline with `malformed-olean` if the structure is invalid (07.3) | none |
| D6 | trust level above 1024 (`lean_add_decl_without_checking`) in in-process mode | adds unchecked | adds unchecked and marks the constant `unchecked` in the report | `--check-all` checks them |

Rows D1 and D5 can only differ from the official kernel on inputs that no Lean program produces without metaprogramming. Each row has at least one regression test in `tests/deviations/` (11.6).
