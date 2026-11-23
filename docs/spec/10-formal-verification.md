# 10. Formal verification

This document specifies promise P3 (02.2): what rulean proves, against which specification, by which method, and what stays trusted. The method is the one that con-ron showed at kernel scale in 2026 (01.6): a pure Lean specification, a Lean "twin" of the algorithm, and a refinement proof from the Rust code (translated by Charon and Aeneas) to the twin. rulean adds two things that con-ron does not have: a faster algorithm (NbE, sessions, parallel scheduling) in the twin, and verdict parity with the official kernel.

## 10.1 The theorems

All theorems are in the Lean package `RuleanProof` in `proof/` (13.2). The statements are in one file, `proof/RuleanProof/Statements.lean`, so that a person can audit them in one place (10.9).

**T1, soundness of the stream checker (required for 1.0).**

```lean
theorem rulean_model_exists (V : Type w) [ConLeche.SetTheory V]
    {b : ByteArray} {st₀ st₁ : RuleanCore.State} {r : RuleanCore.Report}
    (hrun  : RuleanCore.check_stream st₀ b = .ok (r, st₁))     -- the Aeneas model of the Rust function
    (hacc  : r.verdict = .accept)
    (hpool : K1.ParallelAll …)                                 -- contract of the unverified thread pool (10.7)
    (hread : K2.ReadsAs …) :                                   -- contract of file reading (10.7)
    ∃ ds, Spec.parseStream b = .ok ds ∧
      ∃ env, Spec.Elab ds env ∧ Nonempty (ConLeche.Model V env.safe)
```

`env.safe` is the environment without the quarantine tier (05.10). `Spec.parseStream` is the Lean specification of the lean4export 3.x format and of the rulean binary format (07). `Spec.Elab` relates declarations to the constants they add, including the recursors that rulean generates.

**T2, no proof of False.**

```lean
theorem rulean_no_false (V : Type w) [ConLeche.SetTheory V] … (hrun …) (hacc …)
    (hF : ∃ c ∈ env.safe, c.type = .const ``False [] ∧ c.axiomsUsed ⊆ Std3) : False
```

`Std3` is {`propext`, `Quot.sound`, `Classical.choice`}. A declaration that uses another axiom (including `sorryAx` and `_native.…` axioms) is reported with its axioms (P2.c). T1 still covers it: the model interprets each axiom as an assumption of its statement, as con-leche does.

**T3, quarantine (required for 1.0).** No constant in `env.safe` refers, directly or through the types and values of other constants, to a constant in the quarantine tier.

**T4, report fidelity (required for 1.0).** For each accepted theorem, the axiom list in the report equals the set of axiom constants in the transitive closure of its dependencies.

**T5, parallel determinism (required for 1.0).** The verdict and the report do not depend on the thread count or the schedule. This is proved for the twin, given contract K1.

**T6, relative completeness (optional, after lean4lean's verification lands).** If lean4lean's `checkDecl` accepts d within fuel F, rulean accepts d within the resource limits of 05.11. See 10.11.

What the theorems do **not** say:

- They do not say that rulean terminates. A run that does not terminate is not an accept. The CLI has a wall-time limit.
- They do not say that rulean accepts what the official kernel accepts. That is P2, and it is tested (11).
- They do not cover the `.olean` reader in the first release. The `.olean` format has no specification (07.3). The theorem is about the decoded declaration stream, and the reader is checked by cross-validation against the export path (07.3.6).
- They do not cover in-process mode (09.6). There the input comes from Lean objects in memory, not from a byte stream.

## 10.2 The specification

### 10.2.1 Choice

The specification is con-leche's model, imported as a Lean dependency at a pinned commit:

- `ConLeche.SetTheory V`: ZF without infinity and choice, with replacement as a scheme and an ω-chain of Grothendieck universes. `carneiro_implies_conleche` builds an instance from ω inaccessible cardinals (01.6).
- `ConLeche.Model V env`: one set for each pair (constant, list of universe levels). Each constant is a member of the denotation of its type. Each definition equals the denotation of its value. Each recursor computes by its rules.
- `ConLeche.Red`, `ConLeche.DefEq`, `ConLeche.Infer`: the rules of the kernel in the accepting direction, with their soundness lemmas.

Reasons:

1. It is the only finished consistency proof for a production Lean kernel (November 2026). The declarative route through lean4lean still needs unique typing, Π-injectivity and the model construction, which are all `sorry` today.
2. It is a model theorem. It does not depend on unique typing, so it needs no normalization proof. rulean only proves the accepting direction.
3. Lean ships con-leche in `lake check --paranoid`. Users already trust its statement.
4. Two independent kernels (con-leche and rulean) with one shared specification is better than two specifications that nobody can compare.

### 10.2.2 Extensions that rulean needs

con-leche declines or treats differently some inputs that the official kernel accepts (01.6). P2 needs all of them. Each item below is an extension of the specification, written in `proof/RuleanProof/SpecExt/`, proved sound in con-leche's model, and offered upstream to con-leche.

| ID | Official behaviour | con-leche today | Extension |
|---|---|---|---|
| X1 | `let` with a type that depends on the value; zeta reduction in any position (Arena tests 034, 035) | declines | rules `Red.zeta` and `DefEq.letCongr`; soundness by the denotation of `let` as substitution |
| X2 | proof irrelevance under binders (Arena test 107) | declines | `DefEq.proofIrrelUnder`: two terms whose type is a proposition in the extended context are equal |
| X3 | theorem bodies can be unfolded (delta) | theorems are opaque | `Red.deltaThm`; sound because a theorem equals the denotation of its value |
| X4 | `unsafe` and `partial` declarations are accepted with weaker checks | declines | quarantine tier: the model is built for `env.safe` only, and T3 proves the separation (05.10) |
| X5 | axioms outside Std3 are accepted | accepts only Std3 by default | axioms read as assumptions (as con-leche does under `--compare`) |
| X6 | `native_decide` axioms `_native.….ax` | declines Cedar | covered by X5; reported by T4 |
| X7 | sparse name indices and levels out of order in the export (Arena `sparse-name-index`, `level-index-out-of-order`) | declines | a parser matter, not a rule: `Spec.parseStream` accepts them as the official parser does |
| X8 | Nat and String literal extensions with the exact official set of operations (05.8) | pinned variants with certificates | rules `Red.natBin op` for each official operation, each proved against `Nat` in Lean; `Red.strLit` |

Where con-leche **accepts more** than the official kernel (semantic level comparison, proof irrelevance fall-through, the `And.rec` rescue, some large eliminations), rulean does not use the extra rules by default. They are sound, so using them would not break T1, but they would break P2.b. They are available under `--rules=con-leche` (05.12).

### 10.2.3 Upstream policy

- rulean tracks con-leche `main`. A con-leche bump is a pull request that re-runs the whole proof.
- If con-leche changes a statement that rulean uses, rulean keeps the old pin until the bridge lemmas are updated.
- Extensions X1 to X8 are offered to con-leche as pull requests. If they are merged, rulean deletes its local copies.
- If con-leche stops being maintained, rulean keeps a fork in `proof/vendor/con-leche/`. The fork has the same licence and a clear record of differences.

## 10.3 The proof chain

```
 ZF⁻ + ω Grothendieck universes            (assumed; cannot be removed, Gödel II)
   │  carneiro_implies_conleche
   ▼
 L0  Spec: ConLeche.Model, Red/DefEq/Infer + SpecExt X1..X8          [proved: soundness of each rule]
   ▲  refines (Theorem R1)
 L1  Twin: RuleanTwin, the rulean algorithm in Lean, over the rulean data layout
     (stores, handles, NbE values, caches, sessions, scheduler)        [proved: R1]
   ▲  refines (Theorem R2, lockstep)
 L2  Rust core: crates/rulean-core, translated by Charon + Aeneas     [proved: R2]
   ▲  assumes
 L3  Islands: thread pool, file read, frozen-tier sharing, (opt.) SIMD scanner,
     each with a Lean-stated contract K1..Kn                           [discharged outside Lean: Verus, Kani, review]
   ▲  assumes
 L4  rustc + LLVM + std + system allocator + OS                       [trusted; mitigated by kernel diversity]
```

**R1, twin refines spec.** If the twin accepts a declaration list, then there is an environment that the L0 rules derive, with the same constants. The proof is by induction on the order of declarations, as in con-ron's Theorem 1 (`Arena.checkDecl_bridge`). Each optimisation of rulean is a lemma of R1 (10.4, 10.5).

**R2, Rust refines twin.** If the extracted Rust function returns `ok r` in state `st'`, the twin returns the same result in a related state. The proof uses con-ron's `lockstep` tactic and a library of `@[lockstep]` lemmas, one or more for each Rust function. Errors are mirrored: the Rust code may decline or panic where the twin accepts, but it never accepts where the twin rejects.

**Capstone.** T1 is the composition of R2, R1 and the L0 soundness lemmas, under the contracts of L3.

## 10.4 Verifying the fast algorithm

The speed of rulean comes from changes to the algorithm (08.2). Each change needs a proof obligation in L1. The obligations below are partial correctness only. None of them needs a normalization or termination proof.

### 10.4.1 NbE evaluation

rulean's `whnf` and conversion work on values (05.4): closures are records `(env, body)` in an arena, neutral terms have a spine, and glued values keep the folded and the unfolded form of a constant application.

The obligation is **denotation preservation**:

- Define `⟦v⟧ρ` for values in con-leche's model. A closure denotes the function that the model gives to `λ` with the closure environment. A neutral term denotes the model value of its head applied to its spine. A glued value denotes its folded form.
- Lemma `eval_sound`: `⟦eval ρ e⟧ = ⟦e⟧⟦ρ⟧`.
- Lemma `quote_sound`: `⟦quote k v⟧ = ⟦v⟧` (read-back does not change the denotation).
- Lemma `conv_sound`: if `conv k v₁ v₂ = true`, then `⟦v₁⟧ = ⟦v₂⟧` in every model of the environment.
- Lemma `unfold_sound`: unfolding a glued value is sound, because a definition equals the denotation of its value (`ModelOf`).

Type-directed rules (proof irrelevance, struct eta, unit-like types) need the type of a value. The twin infers it with the L0 `Infer` rules on the read-back term, and caches the result. The lemma is that the cached type is a derivable type.

### 10.4.2 Hash-consing and handles

- Handles are integer indices into per-constructor arrays (04.2). Two equal handles in the same tier denote the same term. This is a lemma about the store, proved once.
- Pointer equality is never part of the meaning. Following con-ron, the Aeneas model of any `ptr_eq` returns `false`. Fast paths that use handle equality are proved through the store lemma, not through pointers.
- The store is append-only inside a declaration. The scratch tier is reset after each declaration by an epoch counter, as in con-ron's `HashMap2`. The lemma is that no handle into the old epoch survives the reset. This is a type-level invariant in the twin: scratch handles carry the epoch.

### 10.4.3 Caches

Lean bug #14806 (01.3) was a cache whose result depended on the order of queries. rulean's rule is: **every cache entry is a true judgment.**

- Invariant `CacheTrue`: for each entry `(k, r)` of the infer, whnf and defeq caches, the judgment that the entry states is derivable by the L0 rules in the current environment.
- Lemma: inserting an entry keeps `CacheTrue` when the entry comes from a derivation. Looking up an entry gives a derivation.
- Failure caches (a defeq query that failed) are not judgments. They can only make rulean reject. They cannot break soundness, but they can break P2.a. They are tested, not proved (11.4).

### 10.4.4 Sessions: caches across declarations

rulean keeps some caches across declarations in the same worker (08.4). This is the largest new obligation relative to con-ron, which clears all caches per declaration.

- Lemma `model_extend`: if env' extends env by adding constants, then every judgment derivable in env is derivable in env'. This needs no model theory: the L0 rules are monotone in the environment.
- So a cache entry stays true when the environment grows. An entry is stamped with the index of the newest constant it depends on. A worker uses an entry only when that constant is visible in its environment cut (08.3). The lemma is that the stamp is an upper bound on the dependencies of the derivation.

### 10.4.5 Parallel scheduling

- The scheduler checks declarations in parallel along the dependency graph (08.3). The twin models it as a sequential fold over a topological order of the graph, followed by a merge of the verdicts in declaration order.
- Contract K1 states that the Rust pool runs every job exactly once, with the environment cut of that job, and returns the results in an array indexed by job.
- T5 (determinism) follows: the merge is a function of the array, and each job's result depends only on its declaration and its environment cut.

### 10.4.6 Nat and String literals

- The bignum `rulean_nat::Nat` (05.8) has a refinement proof to Lean's `Nat` for each operation that the kernel uses: succ, add, sub, mul, pow, gcd, div, mod, beq, ble, land, lor, xor, shiftLeft, shiftRight. These are the 15 operations of the official kernel (05.8). `Nat.log2` and `Nat.powMod` are not kernel operations.
- con-ron reports 5.1 proof lines for each Rust line of bignum code. Budget the same.
- The small-number fast path (a `u64` with overflow checks) is the same function as the general path on inputs below 2^64. That is a lemma, so no second proof is needed.

## 10.5 Parser

- The NDJSON reader and the binary reader are in the verified core (07.1, 07.2). Their specification is `Spec.parseStream`, a Lean function that is the reference meaning of the formats. It is written from the lean4export documentation and from the Arena tests.
- The lemma is that the Rust reader and `Spec.parseStream` give the same declaration list, or the Rust reader declines.
- The binary format (07.2) has a second lemma: `decode (encode ds) = ds`, where `encode` is the Rust converter. The encoder is not trusted, because rulean checks what it decodes, not what was encoded.

## 10.6 The Rust subset for the verified core

The verified core is `crates/rulean-core`, `crates/rulean-store`, `crates/rulean-nat` and `crates/rulean-format` (03.3). It must stay inside the subset that Charon and Aeneas translate. The rules below come from con-ron's `AENEAS_FINDINGS.md` (01.7). CI enforces them (13.4).

| Rule | Reason |
|---|---|
| Safe Rust only. `#![forbid(unsafe_code)]` in every verified crate. | Aeneas has no memory model. |
| No closures, no `dyn`, no function pointers. Use enums and explicit `match`. | Aeneas does not translate them well. NbE closures are data records (04.5). |
| No `Cell`, `RefCell`, `Rc`, `Arc` in the verified core. | No interior mutability in Aeneas. The frozen tier is passed by shared reference. |
| No `std::collections`. Use the verified `rulean_store::Table` (open addressing with epochs). | The std models are trusted, and the `Vec::insert` model was wrong. |
| `Vec` only with `push`, `pop`, index, `len`, `with_capacity`, `truncate`. Each is a modelled function with a reviewed model. | Keep the std model small. |
| No `?` operator. No early `return` inside loops. No `break` or `continue` to an outer loop. | Aeneas limits (F16). |
| No `Option<&T>` or other nested borrows in types. | Aeneas limit. |
| No borrow of a container held across a branch that mutates it. | Aeneas F1 (14 of 18 con-ron failures). |
| A function has at most 300 lines. An `if` and `else if` chain has at most 4 branches. Use a `match` for a longer dispatch, and split large dispatch into functions. | Charon and Aeneas run out of memory on very large functions (F12, F18). Long `else if` chains with `&&` conditions make the extraction slow (F19). A `match` on one enum is not a problem, so the rule does not limit the arms of a `match`. |
| No trait impls in recursive groups. Traits only for `Hash`-like small interfaces, or not at all. | Aeneas F6. |
| Strings are `Vec<u8>` with a validated UTF-8 flag. No `&'static str` in enums. | F7. |
| Integer arithmetic is checked. `overflow-checks = true` in all profiles. | The proof treats overflow as a panic. |
| Recursion only where the twin has the same recursion. Deep recursion uses explicit stacks in a `Vec` (05.11). | Stack overflow is not modelled. An explicit stack makes `deepRecursion` a normal error. |

`cargo xtask subset` checks the rules on the syntax of the verified crates, with the rule IDs S1 to S14. It cannot see types or borrows, so it does not check the rule on a borrow held across a branch, and it reports the `Vec` method names on every receiver. The extraction job (13.4) is the final check. Code under `#[cfg(test)]` is not extracted, so the lint skips it.

Unsafe or concurrent code lives only in the island crates `rulean-pool`, `rulean-io` and `rulean-simd` (03.3). The verified crates do not depend on them. The driver links the two worlds.

## 10.7 Islands and their contracts

Each island has a contract stated in Lean, in `proof/RuleanProof/Contracts.lean`. The capstone theorem has one hypothesis per contract. Each contract is discharged outside Lean, as the table says. The list is closed: a new island needs a change to this table and to `Statements.lean`.

| ID | Island | Lean contract (short) | How it is discharged |
|---|---|---|---|
| K1 | `rulean-pool`: the work-claiming thread pool | `ParallelAll n f out`: for each job index i < n, `out[i] = f i` (the twin's sequential job) | Verus proof of the pool (atomics, claim counter, result slots); a loom model test; review |
| K2 | `rulean-io`: file read and mmap | `ReadsAs path bytes`: the byte array given to the core is the content of the file at open time | review; the file is opened read-only and hashed (SHA-256) before and after the run, and the report includes the hash |
| K3 | frozen tier shared across threads | the frozen store does not change after `freeze`; workers get `&Store` | follows from Rust's type system once the store is behind a shared reference; Kani harness for the `freeze` boundary |
| K4 | `rulean-simd` (optional): SIMD line scanner for NDJSON | `scan_simd b = scan_ref b`, where `scan_ref` is in the verified core | Kani bounded equivalence for inputs up to 64 bytes; differential test on all corpus exports; it can be turned off with `--no-simd` |
| K5 | overflow panics | `overflow-checks` is on, so every overflow is a panic, not a wrap | build-profile check in CI (13.4) |
| K6 | allocation failure | allocation either succeeds or aborts the process; no partial state is observable | `panic = "abort"`; the global allocator is the system allocator (01.10) |

If an island is wrong, the theorem does not apply. The mitigation is kernel diversity (10.8, last row) and the tests in 11.

### 10.7.1 Status in rulean 0.0.5

- K1 is stated in Lean as `ParallelAll` in `proof/RuleanProof/Contracts.lean`, with two theorems: the sequential twin satisfies it, and two results that satisfy it for the same jobs are equal. `Interface` in `Statements.lean` has the field `runAll`, the model of `run_all`, and `Interface.K1` says that `runAll` satisfies `ParallelAll` for each thread count, each schedule and each set of jobs. The theorem `Interface.runAll_eq` shows that under K1 two runs of the pool on the same jobs give the same array.
- `proof/verus/pool.rs` is a Verus model of `run_all` of `rulean-pool`. The proof shows that if `run_all` returns, the result has `n` values and the value at each job index `k` is `f k`. The shared counter has no contract in the model, so the proof holds for each schedule of the threads. The proof does not show that `run_all` returns. The CI job `verus` runs the proof with a pinned Verus release.
- The test `each_claim_order_runs_each_job_once` of `rulean-pool` covers the part that the proof does not cover. The worker takes its counter through the trait `Counter`, as in the model. The test gives the worker each order of the claims of at most 3 workers on at most 5 jobs, and it checks that each job runs exactly once and that each worker stops. All `fetch_add` calls on one atomic are in one total order, also with `Ordering::Relaxed`, so an order of the claims is a complete model of a schedule of the threads. For more workers or more jobs, review covers this part. The test replaces the loom model test of the table in 10.7. loom is not used, because its dependency `generator` builds code with `cc`, and the rule of 13.3.1 allows no C in the dependency graph.
- K2 is stated in Lean as `ReadsAs` in `proof/RuleanProof/Contracts.lean`. `Interface` has the field `readInput`, the model of the read of `rulean-io`, and `Interface.K2` says that each byte array that `readInput` gives satisfies `ReadsAs`.
- `rulean-io` opens the input read-only and reads it in blocks of 1 MiB. `rulean check` and `rulean pack` read the input through it. The report gives the SHA-256 digest of the bytes that the core got.
- After the run, `rulean-io` reads the file again and computes its digest. If the digest is not the same, `rulean check` gives exit code 4 and no verdict, and `rulean pack` writes no file. Standard input and a file that is not a regular file cannot be read again, so this check does not apply to them.
- `rulean-io` does not map the file into memory. With the portable SHA-256 code, each read costs about 50 instructions for each byte, 1.5 s on the 584 MB export of Std. With the SHA instructions of the CPU (12.4), the digest costs a few instructions for each byte. On the Init export of v4.36.0 (348 MB), this takes 38 G instructions off the 299 G of `rulean check`.
- The check after the run cannot find a change that was made and then undone during the run. Review covers this case.
- K3 is discharged by the type system and a lint, and it needs no Kani harness. rulean does not share a store across threads. `Checker::worker` gives each worker its own copy of the store and of the environment, and a worker gets the main checker only through a shared reference. The core crates have `#![forbid(unsafe_code)]`, and the subset lint (rule S5) rejects each type with interior mutability in them: `Cell`, `RefCell`, `UnsafeCell`, `OnceCell`, `OnceLock`, `LazyCell`, `LazyLock`, `Rc`, `Arc`, `Weak`, `Mutex`, `RwLock` and each `Atomic` type. So a value of a core crate cannot change behind a shared reference, and the store of the main checker does not change during the parallel stage.
- K4 holds because the island is not there. The crate `rulean-simd` has no code, and no crate depends on it. The NDJSON scanner of the core reads each line. A version that adds a SIMD scanner must discharge K4 before a crate uses the scanner.
- K3 to K6 are stated in Lean in `proof/RuleanProof/Contracts.lean`, each with one theorem. K3 is `Frozen`: a worker gives back the store that it got, and `frozen_seq` shows that the result of a second worker then does not depend on the first worker. K4 is `ScanAgrees`, and `scanAgrees_self` shows that it holds when the core uses its own scanner. K5 is `NoWrap`, and `noWrap_checkedAdd` shows that the model of a checked addition on `UInt64` satisfies it. K6 is `AllOrNothing`, and `allOrNothing_observe` shows that each result that the user can see is the result of the twin. K3 to K6 are not hypotheses of T1 to T5 yet, because the Aeneas model of the core does not have the objects that they talk about.
- `cargo xtask profile` is the build-profile check of K5 and K6 (13.4). It fails if `[profile.release]` or `[profile.dev]` of the workspace manifest does not have `panic = "abort"` and `overflow-checks = true`, if a profile or `.cargo/config.toml` has `panic = "unwind"` or `overflow-checks = false`, or if a file under `crates/` sets a `#[global_allocator]`. The CI job `policy` runs it as part of `cargo xtask all`.

## 10.8 The trusted computing base

| Component | Why it is trusted | Mitigation |
|---|---|---|
| `ConLeche.SetTheory` (ZF⁻ + ω universes) | Gödel's second theorem: a consistency proof needs a stronger theory | standard assumption; equal to Carneiro's ω inaccessibles; reviewed by Hales and others (01.6) |
| The theorem statements in `Statements.lean` and `Spec.parseStream` | a wrong statement proves the wrong thing | one file; human review by two people before each release; the statement is compared with con-leche's `main_json_model` |
| The Lean kernel that checks the proofs | it checks everything in `proof/` | the proofs are also checked by rulean itself, by nanoda and by con-leche (on the export of `RuleanProof`) |
| Charon and Aeneas (Rust → LLBC → Lean) | translation fidelity is not proved | pinned versions; their own papers (ICFP 2022, ICFP 2024); a differential test runs the extracted Lean model (compiled) against the Rust binary on the Init corpus |
| Aeneas std models (`Vec`, integer ops, slices) | the models are written by hand | small model surface (10.6); each model has a test that runs the model and the real function on random inputs |
| Contracts K1 to K6 | outside Aeneas | 10.7 |
| rustc, LLVM, Rust std, the system allocator, the OS | no verified compiler for real Rust (01.7) | pinned toolchain; `panic = "abort"`; **diversity**: `rulean check --paranoid` also runs con-agua (verified to x86, no rustc), or users run `lake check --paranoid` |
| The `.olean` reader (07.3) | the format has no specification | not in T1; cross-checked against the export path; untrusted-input hardening (12) |

## 10.9 Proof engineering

**Size budget.** con-ron has 116 k Rust lines and 389 k Lean lines. The proof-to-code ratio is about 3:1 for the core, from 2.2 (branchy code) to 6.2 (`Expr`). rulean's verified core is planned at 45 k to 60 k Rust lines (03.3), so the budget is 150 k to 350 k Lean lines, plus the extracted model (about 1.3 lines for each Rust line).

**Use of AI agents.** Most proof lines will be written by models, as for con-leche, con-ron and SymCrypt (01.6, 01.7). The rules below follow from what went wrong in those projects ("models still try to cheat", AI-generated documents with wrong counts).

1. No `sorry`, no `admit`, no new `axiom` in `proof/`. CI runs `#print axioms` on T1 to T5 and fails if the set is not exactly Std3. Contracts are hypotheses, not axioms.
2. `Statements.lean`, `Contracts.lean`, `Spec/` and `SpecExt/` are **protected files**. A change to them needs approval from two maintainers (13.5). A model cannot approve.
3. No `native_decide`, `bv_decide` or `implemented_by` in proofs. No `set_option maxHeartbeats 0` without a comment and an issue.
4. A proof that takes more than 10 minutes to elaborate is split.
5. Every agent-made pull request states the model, the prompt class and the human reviewer.

**Independent checking.** The release proof is exported with lean4export and checked by rulean, con-leche and nanoda. A release needs all three to accept.

**CI cost.** Charon takes seconds, Aeneas about 30 s, and the elaboration of the extracted model about 100 s for con-ron's core. The full proof build is planned at under 60 minutes on 32 cores. The pull-request gate re-checks only the changed modules. The full proof runs nightly and on every release branch (13.4).

## 10.10 Toolchains and drift

- Three toolchains are pinned together in `toolchains.toml`: the Rust nightly that Charon needs, the Charon and Aeneas revisions, and the Lean release of `proof/`. Nix pins all three (13.3), as con-ron does.
- The Lean of `proof/` does not need to equal the Lean release that rulean checks. rulean checks exports of v4.35.0 and later (02.5). The proofs build with one pinned Lean.
- con-ron needed a 375-line patch to use the Aeneas library on Lean v4.33 and more for v4.35. Budget one toolchain bump each month, with one person-week each.

## 10.11 Later steps

- **Relative completeness (T6).** When lean4lean's verification lands, state a simulation: every derivation of lean4lean's algorithmic judgment within fuel F has a rulean run that accepts. This needs lean4lean's transcription of the C++ algorithm as a formal object. It does not need the metatheory conjectures.
- **No trusted compiler.** con-agua shows a verified compiler from a first-order language L to x86 (Kraken). The rulean twin is already first-order data with explicit stacks. A later project can compile the twin to L and reuse con-agua's compiler. That removes rustc, LLVM and Aeneas from the trusted base for one build of rulean. It is not part of the Rust promise, so it is a stretch goal (14, M9).
- **Termination.** con-agua proves that its binary always returns. rulean can prove the same for the twin with a fuel bound, if users need it.
- **The `.olean` reader.** When the format gets a specification (lean4#16542 asked for validation), add the reader to T1.
