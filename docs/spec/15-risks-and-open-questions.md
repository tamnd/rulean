# 15. Risks and open questions

## 15.1 Risks

| ID | Risk | Likelihood | Effect | Mitigation |
|---|---|---|---|---|
| R1 | Engine F with its proofs does not reach 1.21 T on Mathlib | medium | P1 missed | the budget has two independent sources of margin, NbE and sessions (08.2); M3 measures F at 2.0 T before sessions; if M4 misses, simplify F and move work to `.rlb` input |
| R2 | The NbE invariants are too hard to prove at the needed scale | medium | M5 late | keep F's value types first-order (04.5); prove `eval_sound` first in M3 before optimising; the confirm set lets a hard rule move to engine R |
| R3 | Engine F accepts where the official kernel rejects, through non-transitivity (05.1) | medium | P2.b broken | confirm set; `--confirm=all` in CI; the Arena corner cases; regression of every finding |
| R4 | Lean semantics change faster than rulean follows | high | old profiles only | profiles and flags (05.2); the 14-day process (14.4); engine R as a direct port is fast to update |
| R5 | Aeneas or Charon cannot translate a needed construct, or break with a new rustc | medium | extraction blocked | the subset lint (10.6); pinned toolchains; con-ron's findings list; keep the core in the subset con-ron already used |
| R6 | con-leche changes its specification, or stops | low | bridge work | pin by commit; offer the extensions upstream; fork rule (10.2.3) |
| R7 | The schedule slips | high | later 1.0 | proofs in the same milestone as the code; M4 (speed) and M5 (proof) are separate exits, so a slip in one is visible early |
| R8 | A soundness bug in an island or in rustc | low | wrong accept | diversity with con-agua and `lake check --paranoid`; island proofs; fuzzing |
| R9 | The `.olean` format changes in a way the reader cannot follow | medium | olean mode declined | NDJSON stays the reference input; the reader is versioned and declines unknown versions |
| R10 | Heartbeat behaviour in in-process mode differs from the official kernel in a way users notice | medium | M6 adoption | the calibration rule of 09.6.4 (never time out where official does not); report D2 cases |
| R11 | The Anthropic FLT corpus or the RH corpus needs more than 2^27 nodes of one kind | high | wide build needed | `--features wide` (04.2.1), tested in the weekly scale job |
| R12 | Upstream does not accept a kernel selection hook | medium | P2.d only through a custom Lean build | the custom build works without upstream change (09.6.2) |

## 15.2 The official kernel gets faster

The 10x target is relative to the official kernel of the same release (02.2). The official kernel used 34% fewer instructions between v4.28.0 (14.92 T) and the 2026-11-14 nightly (9.82 T) (B§9). The renovation issue lean4#14977 plans more work. Parallel checking (lean4#16343, open) does not change instructions, but it will change wall-time comparisons.

Planning assumption: the official kernel reaches 6 T on Mathlib by the time of rulean 1.0, which is another 1.6 times. Then P1.a needs at most 0.6 T. That is the stretch goal of 08.1. It is 1.5 times nano-lean's 0.40 T today.

If the official kernel adopts NbE or a handle store, the 10x target may become impossible for any kernel. In that case rulean keeps the rule "the baseline is the official kernel of the same release", publishes the ratio honestly, and the team decides whether to restate P1. That decision belongs to the project owner (15.4, Q4).

## 15.3 Technical open questions

| ID | Question | When it must be answered |
|---|---|---|
| T1 | What is the semantic split of the official kernel's time on Mathlib (whnf, defeq, infer, instantiate)? No published profile exists (B§9). Measure it in M0. | M0 |
| T2 | How does the #14576 hash collision defeat the official cache? (A§10.1) It affects the cache design only as a test case, because rulean's caches never trust hashes. | M2 |
| T3 | Is `infer_only` used for theorem values in `add_theorem`? (A§10.2) It affects performance only. | M2 |
| T4 | How large is the confirm set in practice (05.1)? If it is large, engine F loses its advantage on some corpora. | M3 |
| T5 | Do sessions give the factor that gruszka's design doc predicts? Only gruszka's simulations exist. | M4 |
| T6 | Should rulean read Susz (gruszka) or BLean (olean-export) as input? | after 1.0 |
| T7 | Can the side record (04.2.2) shrink to 4 bytes without losing speed? | M1 |
| T8 | How should heartbeats be calibrated across machines and releases (09.6.4)? | M6 |
| T9 | Can P1.d hold on the `bad/` tests of `perf/`? Rule 2 of 05.1 says that a reject needs engine R, and engine R follows the official order, so a reject test costs at least the official search for "not equal" with the constant factor of rulean. The official kernel takes 28 to 40 G instructions (5 to 7 virtual seconds) on these tests. In the Arena results of November 2026, no checker keeps all 44 `perf/` tests at or below 6 G instructions: nano-lean keeps 40, gruszka 37 and sokonanoda 36. Options: a faster engine R with the same step order, a "not equal" answer of engine F that is final for some rules with a lemma, or a P1.d that counts only the `good/` tests. | M4 |

## 15.4 Questions for the project owner

| ID | Question | Default if not answered |
|---|---|---|
| Q1 | May rulean copy proof code from con-leche and con-ron? Their licences must be checked. | depend on con-leche as a pinned Lean package; write the `lockstep` tactic again unless the licence allows reuse |
| Q2 | How many Lean releases must be supported at once? | the current stable, the current release candidate, and `master`; older profiles for 12 months (05.2) |
| Q3 | Should rulean ask the Lean FRO for bundling and for a kernel selection hook, and when? | after the first Arena submission with full parity (M3) |
| Q4 | If the official kernel becomes too fast for 10x, is P1 restated or kept? | keep the rule and publish the ratio (15.2) |
| Q5 | What is the bounty for an accepted proof of `False` (11.6)? | decide before M7 |
| Q6 | Is in-process mode (P2.d) required for 1.0, or can it follow? | required for 1.0 as written (M6) |

## 15.5 Things that are not risks

- **The 10x target itself is achievable.** Four unverified Rust kernels already use 13 to 31 times fewer instructions than v4.35.0 (A§5.4). The risk is to reach it **with** verification, which is R1 and R2.
- **The verification method is achievable.** con-ron is a Rust kernel with a complete refinement proof to a consistency model, done in 2026 (B§4.2). rulean extends the algorithm, not the method.
