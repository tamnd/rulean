# 03. Architecture

This document gives the structure of rulean: the data flow, the crates, the trust class of each crate, and the main interfaces. Details are in 04 to 09.

## 03.1 Data flow

```
  .ndjson ──┐
  .rlb ─────┼──► [rulean-format / rulean-olean] ──► frozen store + Decl stream
  .olean ───┘          (07)                               (04)
                                                            │
                                                            ▼
                                            [rulean-core::sched] dependency DAG (08.3)
                                                            │ jobs
                                         ┌──────────────────┼──────────────────┐
                                         ▼                  ▼                  ▼
                                    worker 1           worker 2   …       worker n          (island K1: rulean-pool)
                                   engine F → R       engine F → R        engine F → R      (05)
                                   scratch, values,   session caches                       (04.8, 08.4)
                                         └──────────────────┼──────────────────┘
                                                            ▼
                                       merge in declaration order → Report (verdicts, axioms, deviations)
                                                            │
                                                            ▼
                                             [rulean-cli] JSON / text / exit code (09)
                                             [rulean-ffi] Lean Except value (09.6)
```

`rulean_core::check_stream(state, bytes) → Result<(Report, State)>` is the function that theorem T1 is about (10.1). It takes the bytes of an NDJSON or `.rlb` input and calls the pool through the K1 interface. The CLI calls it. The `.olean` path calls `check_decls` on the decoded stream. That entry point is the same function after parsing.

## 03.2 Layers

| Layer | Content | Trust class |
|---|---|---|
| L-spec | Lean specification: con-leche's model and the extensions (10.2) | proved, and its statements are reviewed |
| L-twin | Lean twin of the algorithm (10.3) | proved |
| L-core | Rust verified core, translated by Aeneas | proved by refinement |
| L-island | Rust code with Lean-stated contracts | contract discharged by Verus, Kani or review (10.7) |
| L-hardened | Rust code outside the theorem that handles hostile input | safe Rust, fuzzed, differentially tested (12) |
| L-tool | build, test and report tools | not trusted for verdicts |

## 03.3 Crates

| Crate | Layer | Lines (estimate) | Content |
|---|---|---|---|
| `rulean-store` | L-core | 6 k | handles, node arrays, interning tables, epoch tables, tiers (04) |
| `rulean-nat` | L-core | 4 k | the bignum (04.6) |
| `rulean-format` | L-core | 5 k | NDJSON scanner, `.rlb` decoder, `Spec.parseStream` counterpart (07.1, 07.2) |
| `rulean-core` | L-core | 30 k to 45 k | levels, engine F (NbE), engine R (official transcription), inductives, quotients, declarations, caches, sessions, scheduler logic, report (05, 06, 08) |
| `rulean-pool` | L-island K1 | 1 k | work-claiming thread pool over `std::thread` and atomics |
| `rulean-io` | L-island K2 | 0.5 k | file read, read-only mapping, input hashing |
| `rulean-simd` | L-island K4 | 1 k | optional SIMD line scanner |
| `rulean-olean` | L-hardened | 6 k | `.olean` reader for versions 2, 3, 4 (07.3) |
| `rulean-pack` | L-tool | 2 k | writes `.rlb` from NDJSON or oleans (07.2) |
| `rulean-cli` | L-hardened | 3 k | command line, configuration, reports, limits (09) |
| `rulean-ffi` | L-hardened | 5 k | in-process kernel: Lean object ABI in pure Rust, `lean_add_decl` and the other entry points (09.6) |
| `rulean-bench` | L-tool | 2 k | instruction-count harness, Arena runner (08.7) |
| `rulean-diff` | L-tool | 2 k | differential testing driver against the official kernel and other checkers (11.3) |
| `proof/` (Lean) | L-spec, L-twin, proofs | 150 k to 350 k | `RuleanProof` package (10) |

The verified core is planned at 45 k to 60 k lines of Rust. That is near con-ron's verified core of 41.5 k lines (B§4.2), plus engine F and sessions.

**Dependency rule.** Crates in L-core depend only on other L-core crates and on `core` and `alloc`. They do not depend on `std`, so the Aeneas model of the standard library stays small (10.6). Islands depend on `std`. The driver functions in `rulean-cli` and `rulean-ffi` join the two.

## 03.4 Interfaces

### 03.4.1 Core API (Rust)

```rust
pub fn check_stream(st: State, input: &[u8], cfg: &Config, pool: &Pool) -> Result<(Report, State), FatalError>;
pub fn check_decls(st: State, decls: DeclSource, cfg: &Config, pool: &Pool) -> Result<(Report, State), FatalError>;

// in-process use (09.6), one declaration at a time
pub fn add_decl(env: &mut Env, d: Decl, limits: Limits) -> Result<(), KernelError>;
pub fn is_def_eq(env: &Env, lctx: &LocalCtx, a: ExprId, b: ExprId, limits: Limits) -> Result<bool, KernelError>;
pub fn whnf(env: &Env, lctx: &LocalCtx, e: ExprId, limits: Limits) -> Result<ExprId, KernelError>;
pub fn check(env: &Env, lctx: &LocalCtx, e: ExprId, limits: Limits) -> Result<ExprId, KernelError>;
```

`Pool` is an opaque type. The verified core declares one external function on it, `run_all(pool, n, job) -> Vec<JobResult>`, with no body. Aeneas translates it as an opaque Lean function, and contract K1 states its meaning (10.7). `rulean-pool` implements it. There are no trait objects in the verified crates.

### 03.4.2 Report

```
Report {
  input: { format, sha256, lean_version, profile },
  verdict: accept | reject | decline | resource,
  decls: [{ name, kind, verdict, axioms: [Name], tier: safe | quarantine | unchecked,
            error?: { class, message, context }, flags: [deviation ids] }],
  summary: { counts, axioms_used, deviations, instructions?, wall_ms, peak_rss },
  tool: { rulean_version, commit, proof_commit, build_profile }
}
```

The JSON form is in 09.4. `verdict` for the run is `accept` only if every declaration is accepted.

### 03.4.3 Error classes

Kernel errors use the names of the official `Kernel.Exception` (A§1.13), so that tools can map them. The class is informative. Only the verdict matters for P2 (A§1.13).

## 03.5 Concurrency model

- Parsing builds the frozen store. Then the store is frozen and shared as `&Store` (contract K3).
- The scheduler splits declarations into jobs along the dependency graph (08.3). A job has a declaration and its environment cut.
- Each worker owns its scratch tier, value arena and session caches. Workers share nothing that is mutable.
- Results go into a slot array indexed by job. The merge is a function of that array (T5, 10.4.5).
- There are no locks in the verified core. The only atomics are in `rulean-pool`.
- In rulean 0.0.5, each worker has a copy of the store and does not share `&Store` (08.3.5).

## 03.6 What runs where in the verified build

The shipped binary is the verified build (02.2, P1 rules). There is no separate fast build. Two build options exist, and both are covered by the theorem:

| Option | Effect | Covered by T1 |
|---|---|---|
| `--threads n` | worker count | yes, by K1 and T5 |
| `--no-simd` | turns island K4 off | yes, K4 is not used |

`--engine=R`, `--confirm=all` and `--rules=con-leche` change the algorithm. All three are in the twin, so they are also covered by T1.
