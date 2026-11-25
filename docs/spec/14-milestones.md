# 14. Milestones

This document gives the plan from an empty repository to rulean 1.0, with exit criteria per milestone. The plan assumes 2 experts in Lean kernels and Rust verification, working with AI agents for most code and proof lines. That is the working mode that produced con-leche and con-ron in 2026 (research/C section 5).

The proof work runs in parallel with the code from M0. Aeneas extraction is green in CI from the first commit of the verified core (10.10). A milestone is done only when its proof obligations are done. There is no "prove it later" stage.

## 14.1 Plan

| Milestone | Weeks (from start) | Content | Exit criteria |
|---|---|---|---|
| **M0 Foundations** | 0 to 3 | repository, Nix, CI jobs lint/unit/extract; Aeneas subset lint; con-leche pinned in `proof/`; `Statements.lean` draft; bench harness with the official baseline | CI green; the official baseline numbers reproduced on our machine within 2% of the Arena numbers; T1 statement reviewed by two people |
| **M1 Store and parser** | 2 to 8 | `rulean-store`, `rulean-nat`, `rulean-format` NDJSON; the twin of each; R2 lemmas for each | all Arena exports and Mathlib parse; parse at most 0.16 T on Mathlib; store memory measured (04.9); R2 proved for store and parser; `Spec.parseStream` reviewed |
| **M2 Engine R** | 6 to 14 | levels, engine R (transcription of `type_checker.cpp`), declarations, inductives, quotients, primitive pinning; Arena wrapper | all 235 decidable Arena tests correct; the 30 either tests match the `v4.35` profile; Mathlib accepted (any speed); R1 and R2 for engine R; first Arena submission |
| **M3 Engine F** | 12 to 22 | NbE values, glued lazy delta, confirm set, reordering lemmas; `lake check` integration | Mathlib at most 2.0 T single-threaded; `--confirm=all` shows no F/R disagreement on Init, Std, Mathlib; `perf/` tests at most 1 virtual second each; R1 for engine F (10.4.1); usable as a `lake check` external kernel |
| **M4 Scale** | 18 to 28 | sessions, parallel scheduler, `rulean-pool` with Verus proof, `.rlb`, `.olean` reader | **P1.a to P1.f met** on the nightly bench; FLT (Anthropic) and RH checked; olean cross-validation clean (07.3.6); K1 to K4 discharged |
| **M5 Capstone** | 24 to 32 | T1 to T5 assembled; no `sorry`; proof export checked by three kernels | `proof-full` green; `#print axioms` on T1 to T5 equals the standard axioms; external review of `Statements.lean`, `Contracts.lean` and `Spec*` by someone outside the project |
| **M6 In-process** | 28 to 36 | `rulean-ffi`, the Lean build with rulean as its kernel, dual-kernel test build | the Lean test suite passes with rulean as kernel; `lake build` of Mathlib passes; dual-kernel build shows no difference; conversion overhead at most 10% |
| **M7 Release 1.0** | 34 to 38 | `v4.37` profile; security review; reproducible release; bounty | the release gate of 11.7; two independent builders give the same binary hash; `SECURITY.md`, `SOUNDNESS.md`, `DEVIATIONS.md` published |

Total: about 38 weeks (9 months). The range is 6 to 12 months (15.1, R7).

The exit criteria of M6 have this meaning. The Lean test suite passes if each test gives the output and the exit code of the C++ kernel, or if the difference is a deviation of 05.12. Deviation D2 lets rulean accept a declaration where the official kernel times out, so the test `kernel_maxheartbeats.lean` is not a failure. The conversion overhead is the time of the conversion of the declarations and of the results, as a part of the time of the C++ kernel for the same declarations (09.6.3). The mirror converts the imported constants that the checks use. Its time is measured and given in 09.6.3, but it is not part of this criterion.

## 14.2 After 1.0

| Milestone | Content |
|---|---|
| M8 Ecosystem | proposal to bundle rulean in Lean's `lake check --paranoid`; kernel selection hook upstream (09.6.2); `master` profile tracked each week; persistent result cache for incremental checks (B§8.3, nano-lean `--cache`) |
| M9 Beyond rustc | compile the twin with con-agua's verified compiler to remove rustc, LLVM and Aeneas from the trusted base of one build (10.11) |
| M10 Completeness | relative completeness against lean4lean (T6, 10.11), when lean4lean's verification lands |
| M11 `.olean` in the theorem | a specification of the `.olean` format and the reader in T1 (10.11) |

## 14.3 Effort

| Item | Estimate | Basis |
|---|---|---|
| verified Rust | 45 k to 60 k lines | con-ron verified core 41.5 k (B§4.2) |
| other Rust | 25 k to 30 k lines | 03.3 |
| Lean proof and twin | 150 k to 350 k lines | con-ron ratio about 3:1, range 2.2 to 6.2 (10.9) |
| people | 2 experts full time, plus 1 reviewer at 20% for protected files | |
| compute | AI agent use at the 2026 rates of con-ron and SymCrypt ("a few dollars per line", C§3.1); CI at about 2,000 core-hours per month | |

## 14.4 Ongoing work after each Lean release

The official kernel changes about once a month (A§3). For each new Lean release:

1. Within 3 days: run the conformance corpus with the new release's exports in the newest profile. List the differences.
2. Within 7 days: change engine R to match the new C++ code. Add flags for each semantic change (05.2).
3. Within 14 days: update engine F and the reordering lemmas, or put the changed rule in the confirm set. Publish the new profile.
4. Within 30 days: the proof for the new flags is complete.

Until step 3 is done, rulean declines exports of the new release (05.2). It never guesses.
