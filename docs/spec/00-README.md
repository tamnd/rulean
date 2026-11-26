# Spec 2148l: rulean

**A verified Lean 4 kernel in Rust that is 10 times faster than the official kernel.** rulean checks Lean 4 environments. It gives the same verdict as the official kernel on every environment that a Lean program can produce. It uses at most one tenth of the instructions of the official kernel of the same release. A machine-checked proof in Lean shows that every environment it accepts has a set-theoretic model, so it cannot accept a proof of `False`. It contains no C or C++ code.

- Repository: `tamnd/rulean` (does not exist yet). The name is "Rust" plus "Lean". The spec number follows 2148 (math2) and 2148r (riemann).
- Date: 2026-11-21. Status: **Draft**. The research is done (01, `research/`). No code exists.
- Baseline: Lean v4.35.0 to v4.37.0-rc1 and the nightly of 2026-11-14. Numbers come from the Lean Kernel Arena live run of 2026-11-21 unless the text says otherwise.

## 00.1 Documents

| # | Document | What it settles |
|---|---|---|
| 00 | README | this index, the settled decisions, the conventions |
| 01 | [research](01-research.md) | the state of the field on 2026-11-21: the official kernel, the 2026 incidents, the Arena, the verified kernels, the tools, the bibliography |
| 02 | [the goal](02-the-goal.md) | the one sentence; the promises P1 (speed), P2 (verdict parity), P3 (soundness); the users; the non-goals |
| 03 | [architecture](03-architecture.md) | the data flow, the layers, the crates, the interfaces, the concurrency model |
| 04 | [terms and store](04-terms-and-store.md) | handles, the arena store, names, levels, local contexts, values, the Nat type, the memory budget |
| 05 | [type checker](05-type-checker.md) | engines F and R, semantics profiles, judgments, levels, type-directed rules, literals, declarations, quarantine, limits, deviations |
| 06 | [inductives and quotients](06-inductives-and-quotients.md) | the inductive checks in the official order, nested inductives, large elimination, quotients, recursors, the ind-models cross-check |
| 07 | [input formats](07-input-formats.md) | lean4export NDJSON, the `.rlb` binary format, the hardened `.olean` reader |
| 08 | [performance](08-performance.md) | the instruction budget, where the factor comes from, scheduling, sessions, caches, measurement |
| 09 | [integration](09-integration.md) | modes, the command line, exit codes, reports, `lake check`, the Arena, the in-process kernel |
| 10 | [formal verification](10-formal-verification.md) | theorems T1 to T6, the specification and its extensions, the proof chain, the Rust subset, islands, the trusted base |
| 11 | [conformance and testing](11-conformance-and-testing.md) | test classes, the corpus, differential testing, fuzzing, adversarial testing, the release gate |
| 12 | [security](12-security.md) | assets, attackers, rules for hostile input, rules for the code, disclosure |
| 13 | [engineering](13-engineering.md) | the repository, the "no C/C++" policy, CI, review, style, licence |
| 14 | [milestones](14-milestones.md) | M0 to M7 (about 38 weeks), the exit criteria, work after 1.0, work after each Lean release |
| 15 | [risks and open questions](15-risks-and-open-questions.md) | risks R1 to R12, a faster official kernel, technical questions, questions for the owner |

Research reports:

| Report | Content |
|---|---|
| [A](research/A-lean-kernel.md) | the official kernel: source, exact semantics, versions, incidents, export, Arena data, the semantics checklist, the audit of older notes |
| [B](research/B-kernels-and-performance.md) | the other Lean kernels, the Arena rankings, performance techniques and their evidence |
| [C](research/C-formal-verification.md) | metatheory, verified kernels in Lean and other systems, Rust verification tools, AI-assisted proof engineering |
| [D](research/D-runtime-formats-rust.md) | the Lean object model, `.olean`, lean4export, plugging into Lean, pure-Rust crates, the "no C" question |

The performance part, [perf/](perf/00-README.md), sets the goal of 10 times fewer instructions than each popular kernel, with the measurements of November 2026 and the milestones M8 to M10. Where it and 08 disagree, the performance part has priority.

Reading order: 02, then 01.1, then 03, then the document for your area.

## 00.2 Settled decisions

1. **"10 times faster" means instructions.** P1 counts user-space instructions over all threads, parser included, as the Arena does. The Mathlib target is at most 1.21 T against v4.35.0 (12.10 T) and at most 0.98 T against the nightly (9.82 T). Wall time alone is not the measure, because threads make a 10 times wall-time gain easy (02.6, 08.1).
2. **"Every Lean program" means every environment.** rulean gives the official verdict on every environment a Lean program can produce, and Lean can run with rulean as its kernel. rulean does not replace the Lean compiler or runtime (02.2, 01.9).
3. **Verdict parity is tested, not proved.** Official definitional equality is heuristic and not transitive, so no theorem can state it today. Parity is a release gate over the conformance corpus (02.2, 11.7).
4. **Soundness is proved.** Theorem T1: every environment that `rulean_core::check_stream` accepts has a model in con-leche's `SetTheory V`. The chain is specification, Lean twin, Aeneas-translated Rust, islands with contracts, rustc (10.1, 10.3).
5. **Two engines.** Engine F (NbE over glued values) is fast. Engine R is a transcription of `type_checker.cpp`. A reject needs engine R to agree. Defeq results in the confirm set are checked again by engine R (05.1).
6. **Semantics profiles.** rulean supports named profiles `v4.35`, `v4.37` and `master`. The minimum release is v4.35.0. rulean declines an export of an unknown release. It never guesses (05.2).
7. **Primitives are pinned.** The Nat and String extensions apply only when the constant matches the reference declaration. This closes the by-name gap of the official kernel and is deviation D1 (05.8, 05.12).
8. **Unsafe and partial declarations go to quarantine** (tier T3). They are checked, but they are not in the theorem (05.10).
9. **The store uses handles.** 32-bit handles with a tier bit, per-kind arrays, an epoch-cleared scratch tier, no reference counts. A `wide` feature gives 64-bit handles (04).
10. **No C or C++.** No C source in the tree or in any dependency build. Only the platform C library and the compiler-rt intrinsics of Rust `std` are allowed. Own bignum, no C allocator (13.3).
11. **Hostile input.** Every input byte is hostile, including `.olean` files. No panics, no recursion on input depth, bounded memory (12.3).
12. **Proofs move with the code.** A milestone is done only when its proofs are done. Extraction is green in CI from the first commit of the verified core (14).

## 00.3 Terms

| Term | Meaning |
|---|---|
| official kernel | the C++ kernel in `leanprover/lean4/src/kernel` of the named release |
| environment | a sequence of declarations, as produced by Lean and exported by lean4export or stored in `.olean` files |
| verdict | accept, reject or decline, for each declaration and for the environment |
| decline | rulean does not give a verdict, for example for an unknown release or a resource limit; it is never an accept |
| T, G | 10^12 and 10^9 instructions |
| virtual time | instructions divided by 6.0 G per second, as in the Arena |
| twin | the Lean model of the Rust algorithm, proved to refine the specification (R1) |
| island | a small Rust crate outside the Aeneas subset (`unsafe`, atomics, SIMD), with a contract K1 to K6 |
| deviation | a documented case where rulean differs from the official kernel on purpose (D1 to D6) |

## 00.4 Conventions

- A section number is `NN.M`, for example 05.4. Subsections are `NN.M.K`. Issues and pull requests refer to sections by number.
- A reference to a research report is the letter and section, for example `A§1.8`.
- Claims carry tags as in the research. **[P]** means a primary source: code, an issue, a release note, an author's post, raw data. **[S]** means a secondary source only. **[U]** means unverified, or an inference of the authors.
- `lean4#N` and `I#N` refer to issues and pull requests in `leanprover/lean4`. `PR#N` in the format sections also refers to `leanprover/lean4`.
- Code names follow the official kernel where the concept is the same (13.6).

Writing rules for this specification and for all repository text (13.7):

- ASD-STE100 Simplified Technical English as a guide.
- Short sentences: at most 25 words in a procedure or a rule.
- Active voice. One idea per sentence.
- One paragraph per line in the Markdown source.
- No em dashes. Use a full stop, a comma or parentheses.
- No marketing words: no "blazing", "seamless", "revolutionary", "best-in-class".
- Numbers with units and a date or a source. A number without a source is tagged [U].
- "Must" is a requirement. "Should" is a recommendation. "Can" is a permission.
