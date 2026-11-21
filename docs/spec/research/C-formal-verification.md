# C. Formally verifying a Lean kernel written in Rust (state as of 2026-11-21)

Research pass for **rulean**: a pure-Rust Lean 4 kernel that should be 10x faster than the official C++ kernel, accept exactly what it accepts, and be formally verified.

Compiled on 2026-11-21. Tags:

- **[P]**: read from the primary source, or measured from the repository on 2026-11-21. Measurements come from shallow clones of `leanprover/con-leche`, `con-ron`, `con-agua` and `lean-kernel-arena` at HEAD.
- **[S]**: secondary source only, or a search-engine summary of a primary source that was not opened.
- **[U]**: unverified, contested, or sources disagree.

Repository HEADs measured:

| Repository | HEAD date | Commit |
|---|---|---|
| con-leche | 2026-11-21 | `11d8ff1` |
| con-ron | 2026-11-17 | `de06320` |
| con-agua | 2026-11-18 | `fa516c1` |

The toolchain is Lean v4.36.0.

---

## 0. Executive findings (read this first)

1. **A verified Lean kernel in Rust already exists: con-ron** [P] https://github.com/leanprover/con-ron
   - It is con-leche's algorithm ported to Rust. A Lean "twin" of the checker is proved to refine con-leche's pure checker (Theorem 1). The Rust code, translated by Charon+Aeneas, is proved to refine the twin (Theorem 2).
   - The capstone `ConRon.Capstone.model_exists` says every stream the Rust binary accepts has a set-theoretic model.
   - The guarantee is partial correctness only. The thread pool (`parallel_all`) and the file reading are trusted.
   - The README says outright: "not a high assurance verification effort, given the reliance on Aeneas as a Rust-to-Lean translator".
   - rulean is therefore not a greenfield problem. **The baseline to beat is con-ron.**
2. **The trust chain can already reach x86 machine code without trusting rustc: con-agua** [P] https://github.com/leanprover/con-agua
   - The same algorithm is written in a tiny first-order language L. A verified compiler takes L to x86-64 against the Kraken x86 semantics, which is written in Lean.
   - The end-to-end theorem `checkerFile_accepts` / `checkerFile_model_exists` covers the committed `checker.s` (about 5 MB, 233,890 lines).
   - That is roughly the Candle/CakeML level of assurance, in Lean.
3. **Speed** [P] https://arena.lean-lang.org/
   - Arena Mathlib wall times (current round):

     | Checker | Mathlib wall time | Notes |
     |---|---|---|
     | official C++ (`leanchecker`, v4.35.0) | 33.7 min | |
     | con-ron | 9.65 min | 4 threads, verified |
     | con-agua | 10.9 min | 4 threads, verified |
     | con-leche | 17.0 min | 4 threads, verified |
     | kefir | 7.17 min | 1 thread, unverified Rust |
     | nano-lean | 65.9 s | 4 threads, unverified Rust |

   - **Unverified Rust has already passed 10x wall-clock** (nano-lean is about 30x at 4 threads). **Verified Rust is at about 3.5x.**
   - Per instruction count on one thread, con-ron executes 43.5% of con-leche's instructions on Mathlib (3,848 G against 8,853 G). The official kernel's count is 10.26 T on a v4.33 Mathlib export (con-leche PERF.md).
   - So verified con-ron needs about 0.38x of the official kernel's instructions, about 2.7x per thread.
4. **Metatheory is not finished.**
   - Unique typing, definitional inversion and Π-injectivity for Lean's declarative theory are still conjectures. Carneiro found a gap in his 2019 thesis: the stratified judgment is not closed under substitution.
   - Lean4Lean's `consistency` theorem is still `sorry` in `lean4lean-model`.
   - con-leche avoids all of this by proving "accepted ⇒ has a model" directly, not via a typing judgment. The price is extra checks that the official kernel does not make (the "certification tax").
5. **"Accept exactly what the official kernel accepts" cannot be fully proved.** It has two halves:
   - *Soundness* (rulean accepts ⇒ consistent model) is provable with con-leche's method.
   - *Completeness relative to the official kernel* has no formal target. The official algorithm has no formal semantics except as transcribed in lean4lean, and con-leche, con-ron and con-agua all decline 6 of 145 good Arena tests.
   - Carneiro: "We will not attempt to prove completeness of the kernel".
   - Completeness has to be a differential-testing property, or a simulation theorem against lean4lean's transcription of the C++ algorithm.
6. **AI changes the cost picture by an order of magnitude** [P]
   - con-leche: first commit 2026-08-19, shipped 2026-10-15, about 8 weeks, 7,949 commits, about 365k lines of Lean.
   - con-ron: first commit 2026-09-12, about 5 weeks to ship, 4,365 commits.
   - con-agua: first commit 2026-10-21, about 4 weeks, 9,991 commits, about 436k lines of Lean.
   - All three were "written by AI under supervision from Joachim Breitner".
   - The Aeneas ratio in con-ron was about 3 proof lines per Rust line.

---

## 1. Metatheory of Lean's type theory

### 1.1 Carneiro, *The Type Theory of Lean* (MSc thesis, CMU, 2019)
Source: https://github.com/digama0/lean-type-theory/releases (thesis PDF). Restated in Carneiro's TYPES 2025 slides: https://msp.cis.strath.ac.uk/types2025/slides/TYPES2025-slides31.pdf

- **Target:** Lean 3. Lean 4 changed the kernel: primitive projections, structure eta, nested-inductive elaboration, Nat/String literal extensions. Hales calls the thesis "out of date" for this reason [P] (Hales post, §1.6).
- **Soundness theorem (slide 15)** [P]. Types are sets; ⟦Prop⟧ = {∅,{•}}; ⟦U_{n+1}⟧ = V_{κ_n}, where κ_n is the n-th inaccessible.
  1. If Γ ⊢ α : P then ⟦α⟧γ ⊆ {•}.
  2. If Γ ⊢ e : α and lvl(α) = 0 then ⟦e⟧γ = •.
  3. If Γ ⊢ e : α then for some k, given k inaccessibles, ⟦e⟧γ ∈ ⟦α⟧γ.
  4. If Γ ⊢ e ≡ e′ then for some k, ⟦e⟧γ = ⟦e′⟧γ.
  - Consequence: Lean is consistent if ZFC + ω inaccessibles is. Lean is in fact *equiconsistent* with ZFC + {there are n inaccessibles | n < ω}.
- **Undecidability** [P] (slide 16). The declarative typing and defeq judgments are undecidable, through the interaction of subsingleton elimination (for `Acc`) with definitional proof irrelevance.
- **Algorithmic judgments** [P] (slide 17). Lean underapproximates: Γ ⊩ e : α ⇒ Γ ⊢ e : α, and Γ ⊢ e ⇔ e′ ⇒ Γ ⊢ e ≡ e′. The algorithmic defeq ⇔ is **not transitive**, and algorithmic typing ⊩ **does not satisfy subject reduction**. "We will not attempt to prove completeness of the kernel."
- **Church–Rosser** [P] (slides 19–20). Proved for κ-reduction, a more aggressive reduction that unfolds subsingleton eliminators even on variables and is not normalizing, modulo ≡ₚ ("equality except at proof arguments", with η). The proof uses the Tait–Martin-Löf parallel-reduction method.
- **The thesis error** [P] (slides 18 and 21). The unique-typing proof breaks the cycle UT → CR → definitional inversion → UT by stratifying ⊢ₙ. But "Γ ⊢ₙ e : α is not closed under substitution."
  - The CR part "seems okay, but we need a smarter induction measure."
  - "There is an alternative path to the proof of soundness, but some of the kernel optimizations depend on this theorem."
  - Carneiro set the proof aside with a `sorry`: "The Lean kernel really depends on this property for correctness."
- Hales [P]: "an error was found in the thesis". The alternate consistency route "has never been written down, beyond a brief statement in the introduction to his thesis." https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/

### 1.2 Lean4Lean (Carneiro)
Paper: "Lean4Lean: Verifying a Typechecker for Lean, in Lean", arXiv 2403.14064. Versions: v1 2024-03-21, v2 2024-12-03, v3 2025-09-14. arXiv comment: "submitted to CPP 2026". **Published in TYPES 2025, LIPIcs vol. 384, 2:1–2:23, dated 2026-07-30** [P]. https://arxiv.org/abs/2403.14064 ; https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2025.2

- **Design** [P] (slides 7–8). "A carbon copy of the C++ code":
  - Same union-find caches, pointer-equality tests, bidirectional checking and defeq heuristics; η for structures; nested inductives.
  - Naive substitution and reduction.
  - Suitable for differential fuzzing: it gets "exactly the same counts for definition unfolding".
- **Speed** (June 2025 slides) [P]: Mathlib 58.79 min against 44.54 min for lean4export/C++, a ratio of 1.32. The paper says 20–50% slower.
- **Project status** (slide 6, June 2025) [P]:
  - Goal 1, a complete and competitive kernel: done.
  - Goal 2, writing the type theory down: done. Proving structural properties: partial.
  - Goal 3, implementation correctness: partial.
- **Proved or in progress** [P] (slide 24, README https://github.com/digama0/lean4lean):
  - The typing relation `VExpr` uses pure de Bruijn indices. The kernel's `Expr` is locally nameless, with literals, mvars/fvars, primitive projections and cached metadata. GMP overrides some Nat functions.
  - Proofs use a one-sided Hoare logic `RecM.WF`. The key statement:
    ```lean
    theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn s.ngen.Reserves) :
      RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty', c.TrExprS e e' ∧ c.TrExprS ty ty' ∧ c.HasType e' ty'
    ```
  - Files: `Theory/Typing/Lemmas.lean`, `Strong.lean`, `UniqueTyping.lean` ("conjectures about the typing relation"), `Experimental/ParallelReduction.lean` (Church–Rosser work in progress).
- **A bug found by verification** [P] (slide 25). `Expr.hasBoundVar`'s 64-bit metadata could overflow. The overflow check used `panic!`, which in pure code returns the default value 0. This gave a concrete proof of False, lean4#8554.
- **Late 2026 status** [P]:
  - Issue #16, Carneiro, 2026-10-22: he is "actively working on a version of the unique typing theorem and injectivity of pi types". LLM-generated versions are "not that helpful and are not likely to be merged". https://github.com/digama0/lean4lean/issues/16
  - In the same thread, a contributor posted a Claude-produced UT proof for the restricted `SExpr` system, covering closed inductives only, with Π-injectivity reflection still `sorry`.
  - De Moura, 2026-10-15: lean4lean verification is expected "in the next few months" [P].
  - **lean4lean-model** (https://github.com/digama0/lean4lean-model) [P] states `theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) …`. It is "`sorry`ed pending the model construction". The build had 3 sorries as of PR #12 (Aug 2026): 2 in `Lean4Lean/Theory/Inductive.lean`, 1 in `consistency`.
  - `OmegaInaccessibles := ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible` [P] (copied in con-leche's `bridge/lean4lean-model/ConLecheBridge/Carneiro.lean`).

### 1.3 New metatheory papers in 2026
- **"Definitional Inversion, Without Normalisation"** (Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès, Weirich), arXiv 2607.13662, 2026-07-15 [P]. https://arxiv.org/abs/2607.13662
  - A domain-theoretic technique for injectivity and no-confusion of type constructors that does not need normalization.
  - It works even with type-in-type, and they claim the first such proof with η. The motivation is explicitly Lean4Lean and MetaRocq.
  - It is shown on a small theory. It does **not** yet cover Lean's full calculus.
- **"Reflections on Trusting Lean"** (Bresolin, Mamino), arXiv 2610.30433, 2026-10-21 [P]. https://arxiv.org/abs/2610.30433 For any formula of second-order arithmetic, it is provable in ZFC + ∞ inaccessibles iff its type is inhabited in Lean. This refines Werner/Carneiro equiconsistency.
- **metalean** (intgrah) [P] https://github.com/intgrah/metalean
  - A "positively sound" but partial checker for an idealised Lean, proved through adequacy of a domain-theoretic model. It derives Π-injectivity, uniqueness of typing and subject reduction *for its idealised theory*.
  - Its consistency covers propext, quotients and choice. It supports mutual inductives but **no nested inductives**. The fast mode uses `implemented_by`.
  - Its Arena entries `metalean-fast` and `metalean-slow` accept 4 and 3 bad tests respectively, so the binaries are not yet sound in practice [P].

### 1.4 con-leche: the first Lean kernel proven consistent (announced 2026-10-15)
Announcement: https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/ [P]
Repository: https://github.com/leanprover/con-leche [P]
Proof write-up: https://leanprover.github.io/con-leche/con-leche-proof-idea.html [P]

- **Who** [P]: "implemented and proven consistent by Claude (Fable and Opus), under heavy supervision by" Joachim Breitner (Lean FRO). The OVERVIEW.md "was written by an AI agent". The README is human-written. "Code contributions are likely not useful."
- **Size and history** [P, measured]:
  - 1,423 `.lean` files, 364,744 lines in total. By directory: `ConLeche/Model` 121k, `Verify` 112k, `whitepaper` 36k, `Frontend` 19k, `Kernel` 15.4k, `Semantics` 12.8k, `Cached` 8.3k, `Driver` 6.8k.
  - 9,757 `theorem`/`lemma` declarations under `ConLeche/`.
  - Outside the intentional spec holes in `ConLeche/Challenge.lean`, there are no `sorry`s.
  - First commit 2026-08-19 (GitHub API), 7,949 commits.
- **Main theorems** (`ConLeche/MainTheorem.lean`) [P, quoted]:
  ```lean
  theorem main_json_model (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
      (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
      ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList)
  theorem main_no_False (V : Type w) [SetTheory V] … (hF : jsonWithTheoremFalse [b]) : False
  ```
  - There are also `main_compare_json_model` (a challenge has a model whatever the solution), `main_oleans`, `main_compare_model`, `main_modular`, and `main_modular_one`.
  - `main_modular` gives a family of per-module models that agree on shared names.
  - The pure-checker form is `model_exists`: `checkDecls .verified pins maxNatSize ds = .ok env → Nonempty (Model V env)`.
  - `IsModel V model C := ∀ c, C c → ModelOf model c`, with one set per (constant, universe-level list).
  - Every constant is a member of the denotation of its type, every definition equals the denotation of its value, and every recursor computes by its rules.
  - `False` and `Eq` are *not* special-cased by name. Their own declarations force ⟦False⟧ = ∅ and ⟦Eq A a b⟧ = (a = b).
- **The set-theory assumption** (`ConLeche/SetTheory/Core.lean`, `class SetTheory (V : Type u)`) [P]:
  - Membership with extensionality, pairing, union, power set, regularity, and replacement as a Lean-level scheme (`image : (V → V) → V → V`).
  - `univChain : Nat → V`, a strictly ∈-increasing ω-chain of Grothendieck universes (`IsTGUniverse`). Infinity is derivable.
  - Choice is inherited from the meta-logic (`Classical.choice`).
  - `carneiro_implies_conleche : OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u+1), ConLeche.SetTheory V)` instantiates it on Mathlib's `ZFSet` [P].
  - The README calls the assumption "maybe unnecessarily strong".
- **The model** (proof idea, §2) [P]:
  - `interp` is total and term-directed, and reads no types. There is no typing judgment.
  - A proposition is a truth value. A single point `pt` is the proof of every true proposition, so definitional proof irrelevance holds in the model.
  - `piV`/`lamV` pick a function space or a truth value by inspecting values.
  - Axioms and `sorry` holes are read as assumptions of their statements.
  - The kernel is specified by three *accepting-direction* inductive relations: `Red`, `DefEq` and `Infer`. **There is no transitivity rule for `DefEq`**; chaining goes through "reduce, then continue".
  - A fragment theorem `soundness` (`whitepaper/Fragment/Sound.lean`) bundles `red_sound`, `defeq_sound` and `infer_sound`.
- **Axioms of the proof** [P]: exactly `propext`, `Classical.choice` and `Quot.sound`, guarded by `#print axioms` tests (`tests/ConLecheTests/Axioms.lean`).
- **What the checker accepts** (README) [P]:
  - Only the three standard axioms in the input. `sorryAx` is ignored but use of it is rejected.
  - `trustCompiler`, `ofReduceBool` and `ofReduceNat` are replaced by trivial definitions.
  - Under `--compare`, a challenge's extra axioms are allowed if the solution justifies them.
- **Coverage** [P]: quotients (via pins), inductive blocks (nothing generated), structure eta, projections, unit-like types, K-like reduction, and Nat literals (with `--max-nat-size`, default 128 MiB, above which numerals are rejected).
  - `Nat.div`/`Nat.mod` fast paths are "pinned" variants with certificates (`natOpPinSets`).
  - The proof-idea *fragment* drops projections, literals, mutual and nested inductives under binders, quotients and opaques. The *real* checker covers them.
- **Deliberate deviations from the official kernel** (OVERVIEW.md) [P]:
  - Proof irrelevance is tried on the unreduced pair. The official kernel reduces first and can loop.
  - A closed constructor application is head-normalized at once.
  - `And.rec` on a proof is rescued via `And.intro`.
  - Full-grade types are compared at the innermost λ, and lambda-congruence/η compares bodies' types. These are extra checks.
  - In `--verified` mode the extra checks "never change a verdict on a stream the official kernel accepts" *on real input*. `--trusted` mode skips them and is **outside the theorems**.
- **Trusted base** [P] (README, OVERVIEW):
  - The `SetTheory V` hypothesis.
  - The Lean kernel that checks the proof.
  - The Lean compiler and runtime, including bignum. "Nat soundness depends on the Lean runtime's Nat implementation".
  - The IO model: files do not change during a run, and `liftIO` has no side effects. "out of reach for a completely rigorous verification".
  - The `.olean` parser is only tested, because the format is not specified.
  - The link from the binary to the theorems is "assumed, not proved".
- **Caching** [P]: the shipped cached checker has memo tables for reduction, inference and defeq, keyed by packed hashes. The fueled pure checker has none. A one-directional simulation proves "whatever the cached checker accepts, the pure checker accepts".
- **Performance** (PERF.md, a single run on a shared 96-core machine, Mathlib v4.33 export of 6.07 GB / 691,203 records) [P]:

  | Measure | Official v4.33 | con-leche `--trusted` | con-leche `--verified` |
  |---|---|---|---|
  | Instructions | 10.26 T | 6.40 T (0.62×) | 7.05 T (0.69×) |
  | Wall, 1 thread | 28.9 min | 9.8 min | 10.7 min |
  | Peak RSS | 11.44 GiB | | 4.27 GiB |

  - Verified wall time at `--jobs=4` is 3.1 min and at `--jobs=8` is 100 s.
  - Allocation and refcounting symbols take **45–48% of con-leche's instructions**, against 25% for the official kernel.
  - Arena, 4 threads: 17.0 min, 4.8 GB.
- **Arena behaviour** [P] (https://arena.lean-lang.org/checker/con-leche): 0 bad tests accepted. 3 bad tests *declined*: `047_inductBadNonSort2`, `140_falseFromUnsafe`, `141_falseFromPartial`. **6 good tests declined**: `cedar`, `level-index-out-of-order`, `sparse-name-index`, `034_letTypeDep`, `035_letRed`, `107_proofIrrelevanceUnderBinder`. **So con-leche is not complete relative to the official kernel.**
- **Third-party assessment** (rbeauchamp/strict-lean #3) [S/P] https://github.com/rbeauchamp/strict-lean/issues/3
  - "con-leche accepted" "must not be renamed" as official-kernel acceptance.
  - The serialized-False theorem covers one concrete JSON template.
  - Frontend statement preservation excludes the inductive, basis and quotient cases.
  - con-leche and con-ron share one design, so they can share a specification error.

### 1.5 ind-models (lean-inductive-models, Breitner)
https://github.com/nomeata/lean-inductive-models [P]
- An NDJSON-to-NDJSON filter that does **translation validation**: it translates each user inductive into an extensional system with a small hard-coded inductive basis. The generated recursors, rules and definitions are then checked by an existing kernel (the official one by default).
- README: "This is translation validation, not a general soundness proof for inductive types and not yet a verified translation."
- It caught bugs #14613, #14616, #14806 and #14807 in the August 2026 hunt [P] (postmortem below).
- Arena: 0/90 bad accepted, 145/145 good accepted, Mathlib 36.0 min [P].
- Early con-leche used this approach and later phased it out [S].

### 1.6 Hales guest post on Tao's blog (2026-10-09)
https://terrytao.wordpress.com/2026/10/09/what-mathematicians-should-know-about-the-lean-theorem-proverquestions-of-reliability-and-ai/ [P]

Claims:
- "About 25 kernels for Lean have been written."
- "an error was found in the thesis".
- "As of October, 2026, I know of no complete, public relative-consistency proof covering Lean abstract type theory."
- "Unique typing is not a property built into Lean's logic" and is still conjectural.
- "Breitner has developed a verified Lean kernel called Con-Leche." It was generated with Claude, assumes ZF with inaccessibles in Lean, and "might suffice for all practical purposes". It "has been checked by more than a dozen other proof-checkers".

Recommendations:
- Use multiple and clean-room kernels.
- Formally verify the kernel, in the HOL Light/Candle tradition.
- Improve the metatheory.
- Require human audit of statement fidelity.
- Foundational work given to AI "is dangerous unless carefully audited by humans". There is a backdoor risk.

### 1.7 Kernel soundness incidents in 2026 (they shape the threat model)
- **#14576** (postmortem 2026-08-01) [P] https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/
  - Nested-inductive elimination dropped phantom parameters, so they "escape type checking". It was reachable only through metaprogramming.
  - Found via Ramana Kumar's AI-assisted Collatz "disproof" (Jul 25) and minimized by Kiran Gopinathan. Fixed one hour after the report.
  - nanoda accepted the exploit through a *separate* bug: a missing check on a projection's type name. lean4lean shared the bug because it ports the C++ inductive code.
  - "an implementation bug, not a hole in Lean's meta-theory."
- **Bug hunt** (postmortem 2026-08-24) [P] https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/
  - Daniel Selsam (OpenAI, internal models) found the following.

    | Fix | Area | Checkers that caught it | Checkers that missed it |
    |---|---|---|---|
    | #14613 | sort-as-Prop up to universe normalization | nanoda, ind-models | |
    | #14616 | `_nested` auxiliary names | nanoda, ind-models | |
    | #14806 | `is_def_eq` cache order-dependence | nanoda, ind-models | |
    | #14807/#14843 | `is_prop` without a sort check | ind-models; lean4lean did not have the bug | nanoda accepted it |
    | #14838 (runtime) | refcount overflow; fix makes overflowed objects sticky, as in Koka | external checkers | |
    | #14833 (runtime) | GMP 6.1.2; GMP 6.3.0 now required | external checkers | |

  - Also #14849, which bounds kernel Nat numeral size.
  - "We could not rule out the possibility that there are other, similar exploits based on GMP 6.3.0."
  - **Lesson for rulean:** runtime and bignum bugs are only caught by checkers outside the Lean runtime. A cache whose result depends on query order is a soundness bug (#14806).
- **Rocq and AI** [P/S]
  - De Moura (2026-03-16): "a skilled researcher using Claude (Opus 4.6), with real-time support from the Rocq development team" found seven Rocq kernel bugs. "The same AI" found two nanoda bugs. Claude "did not manage to find a proof of false in the Lean official kernel." https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/
  - The researcher was Tristan Stérin ("In search of falsehood", 2026-03-05). The run took about 72 h on a $200/month Max plan and produced 7 proofs of False plus 3 more bugs in the guard checker and module system: rocq#21682–21702. For Lean, 4 bugs and 0 proofs of False were reported [S]. https://theweatherreport.ai/posts/seven-proofs-of-false/
  - Further Rocq kernel issues: rocq#22759, #22760 (VM) and #22761 (primitive-projection section discharge), filed on 2026-11-09 [S]. https://github.com/rocq-prover/rocq/issues/22761
  - Phrack #73 requested CVEs for seven kernel soundness failures in Lean 4 and Rocq. CVE-2026-72703 and CVE-2026-72705 are credited to Claude Opus 4.6 [S]. https://phrack.org/issues/73/owning-the-truth-undecidability-unsound-kernels-and-the-forging-of-proof_md

---

## 2. Verified kernels in other systems (what is achievable, and its cost)

| System | What is proved | Assumptions / gaps | Source |
|---|---|---|---|
| **MetaCoq/MetaRocq safe checker** | A type checker for PCUIC (the kernel without modules, template polymorphism or η) proved **sound and complete** with respect to PCUIC typing. Certified erasure with verified compilation to OCaml. Found a completeness bug in Coq, fixed in 8.14. | **Postulates strong normalization**: `Axiom normalization : ∀ Σ Γ t, …` (every well-typed term is accessible for `cored`), used to define algorithmic conversion by well-founded recursion. The guard condition is a parameter assumed to imply SN. The authors call this moving "from a TCB to a trusted theory base" (Gödel). | JACM 72(1):8, pp. 1–74, Jan 2025, https://dl.acm.org/doi/10.1145/3706056 [P]; POPL 2020 "Coq Coq Correct!", https://dl.acm.org/doi/10.1145/3371076 [P]; README https://github.com/MetaRocq/metarocq [P] |
| MetaRocq releases | 1.5.1+9.2 (2026-06-16). PR #1311 (2026-10-30) ports the safe checker to Rocq 9.3 with a new universe loop checker. Verified extraction linked to CertiRocq ANF (internship, Mar–Jul 2026). | No published speed figures for the extracted checker. | https://rocq-prover.org/p/rocq-metarocq/latest/versions [S]; https://github.com/MetaRocq/metarocq/pull/1311 [S] |
| **Lennon-Bertrand, "What does it take to certify a conversion checker?"** | Termination of typed algorithmic conversion, assuming injectivity of type constructors and deep normalization. | Same axiomatized normalization as MetaRocq. | FSCD 2025, LIPIcs 337, 27:1–27:23; arXiv 2502.15500 (v3 2026-07-16) [S] |
| **McTT** | A fully verified kernel for core MLTT with a full cumulative universe hierarchy, in Rocq. NbE with an untyped domain model proves normalization, consistency and constructor injectivity. The extracted checker is sound *and complete*. Every pipeline step is verified except the lexer and pretty-printer. | Core MLTT only: no inductives beyond basics, no Prop, no proof irrelevance. | PACMPL 9(ICFP):190–221, 2025, https://dl.acm.org/doi/10.1145/3747511 [S]; https://github.com/Beluga-lang/McTT |
| **Candle** | HOL Light clone in CakeML. End-to-end theorem: every fact exported by the *machine-code* program is valid in HOL, transported through CakeML compiler correctness. | Not a drop-in replacement for HOL Light. Trusts the HOL4 kernel and the ISA model. | ITP 2022, LIPIcs 237, 3:1–3:17, https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2022.3 [S]; JAR 2025 extended version, https://link.springer.com/article/10.1007/s10817-025-09743-8 [S] |
| **CakeML verified checkers** (cake_lpr, cake_pb, cake_xlrup, cake_vipr) | Proofs down to x64/ARMv8 machine code. If cake_lpr prints "s VERIFIED UNSAT", the DIMACS formula is unsatisfiable. Used to validate SAT Competition proofs since 2020. | Untrusted elaboration from DRAT to LRAT happens beforehand. That is the certificate pattern. | TACAS 2021, https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7984575/ [S]; https://cakeml.org/checkers.html [S] |
| **Metamath Zero** | Designed as a self-verifying checker down to x86-64 ELF, specified in a PA-strength logic. Checks set.mm in about 195 ms. | **The verified-binary goal is still future work** in Carneiro's thesis ("we intend to use Metamath C…"). No evidence it has been completed. | https://arxiv.org/abs/1910.10703 [P]; thesis https://digama0.github.io/mm0/thesis.pdf [S] |
| **Isabelle metalogic checker** (Nipkow, Roßkopf) | Formalizes Isabelle's metalogic, including type classes. An executable proof-term checker is proved correct and run on real theories. Uses the **certificate approach** rather than verifying Isabelle's kernel. CADE 2021 Best Paper. | Inefficient. Needs proof terms. | https://doi.org/10.1007/978-3-030-79876-5_6 [S]; JAR 2023 https://doi.org/10.1007/s10817-022-09648-w; AFP https://www.isa-afp.org/entries/Metalogic_ProofChecker.html |
| **Agda Core** (Cockx et al.) | A correct-by-construction type checker, written in Agda, for a subset of Agda's core. No metatheory: the typing rules are the source of truth. 2025–26 theses add η for functions and records, and termination certificates. | Subset only. | APLAS 2024 (LNCS 2025), pp. 63–83, https://link.springer.com/chapter/10.1007/978-981-97-8943-6_4 [S]; https://github.com/jespercockx/agda-core |
| **Dedukti route for Lean** | Lean4Less (Vaishnav) translates Lean to Lean⁻ by removing definitional proof irrelevance and K-like reduction, inserting casts justified by a lemma. It is built by modifying Lean4Lean. lean2dk exports to Dedukti, which has small independent checkers. | lean2dk is still work in progress. Struct-eta and struct-like reduction are future work. | ICTAC 2025 (LNCS 2026), https://inria.hal.science/hal-05310102 [S]; https://github.com/Deducteam/Lean4Less [S] |

Takeaways:
- (i) No full verified kernel for a CIC-class system avoids assuming SN or a large-cardinal model. con-leche is the first that covers a production-scale CIC with proof irrelevance and quotients.
- (ii) Every verified checker that reached machine code did it through a *verified compiler*: CakeML, or con-agua's L→Kraken. None did it through an unverified production compiler.

---

## 3. Rust verification tools (Nov 2026) and how each fits a Lean kernel

**Key requirement: the spec is in Lean**, so it connects to con-leche or Lean4Lean. Only Aeneas and hax (which now uses Aeneas for its Lean backend) produce Lean. Every other tool lives in its own logic.

### 3.1 Aeneas + Charon (Inria / Microsoft; Son Ho, Jonathan Protzenko et al.)
- **Papers** [P]:
  - "Aeneas: Rust Verification by Functional Translation", ICFP 2022 / PACMPL 6, art. 116. https://arxiv.org/abs/2206.07185
  - "Sound Borrow-Checking for Rust via Symbolic Semantics", ICFP 2024, a proof that Aeneas's symbolic execution implements a sound borrow checker. https://arxiv.org/abs/2404.02680
  - Charon, arXiv 2410.18042 [S].
  - "Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean", draft technical report, arXiv 2609.15648, Sep 2026, by Ho, Fournet, Protzenko, Naehrig, Clune, Longa, Boisseau, Leal Sánchez, Fromherz, Delignat-Lavaud. https://arxiv.org/html/2609.15648v1
- **How it works:**
  - Charon extracts MIR to LLBC, a structured IR with borrows.
  - Aeneas translates safe Rust into a *pure* functional model in a `Result` monad, with panics explicit and no memory model. Mutable borrows become "backward functions" that propagate the final value.
  - Backends are F*, Coq, HOL4 and Lean; Lean and HOL4 are the most mature [P]. https://github.com/AeneasVerif/aeneas
- **Supported, 2026** [P] (arXiv 2609.15648): common nested borrows, loops (as recursive functions or `partial_fixpoint`), traits (as structures), mutable iterators and iterator transformers, and multi-target extraction (per-architecture LLBC merged).
- **Unsupported, 2026** [P]:
  - Raw pointers, interior mutability (`Cell`/`RefCell`), concurrency and most unsafe code must be modelled by hand. The README says "ongoing separation logic work" should lift this.
  - Returns inside nested loops and break/continue to outer loops are not supported.
  - Instantiating generics with `&mut`, e.g. `id(&mut x)`, is not supported.
- **Scale** [P]:
  - SymCrypt: 16.7 KLOC of Rust (ML-KEM, SHA-3, AES-GCM, ML-DSA, FrodoKEM, HPKE) with 237 KLOC of Lean. Of that, 30k is generated and 207k is hand or AI proofs.
  - The new Lean backend library is 29k lines.
  - Agents (Copilot with Claude Opus 4.6 → 4.7 → 4.8 → Opus 5.0, and GPT-5.6) generated about 5.1k theorems, about 125 KLOC.
  - Cost: "a few dollars per line of Rust code". "Six months" for the ML-KEM NTT at first, now "about a week for an agent and a few days of human review" per algorithm.
  - "Models still try to 'cheat' with unsound assumptions or weakened goals".
  - The Microsoft Research blog says the verified Rust ML-KEM and SHA-3 ship in Windows Insider builds [S]. https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/
- **Trusted base per the SymCrypt report** [P]: rustc and its backends, Charon (MIR→LLBC), Aeneas (LLBC→Lean), the Lean kernel (plus `native_decide`/`bv_decide`), hand-written std models, and the specs. **Aeneas's translation is not itself proved end-to-end**. The ICFP papers formalize it on paper or partially.
- **Kernel-scale experience: con-ron's `AENEAS_FINDINGS.md`** [P] https://github.com/leanprover/con-ron/blob/master/AENEAS_FINDINGS.md
  - **Scale:** the verified core is 41,523 Rust lines (1,395 functions), generating 52,574 lines of Lean (`Funs.lean` 51,665).
    - 415 `partial_fixpoint`s. 14 `mutual` blocks; the largest has 84 functions and 6,379 lines.
    - LLBC grew to 179 MB. Charon takes 3.9 s, Aeneas 33 s, and Lean elaboration of `Funs.lean` 101 s.
  - **Translator failures:** 18 Aeneas errors in 42k lines; 14 were F1, a container borrow held across a branch.
    - "Nested borrows are not supported yet" for `Option<&T>`.
    - Trait impls cannot sit in a recursive group (F6), so there is no `CoreFns` trait.
    - `&'static str` in an enum produced `sorry` (F7).
    - 40 GB OOM on a record with a borrowed field (F18). 25 GB OOM on a 12-arm `else if` chain (F19).
    - Charon OOM on a function with 20,183 `let`s (F12). Early returns in loops are unsupported (F16).
    - `!b` emitted as a `Prop`. Charon expands match arms multiplicatively (F11).
  - **Subset the port adopted:** no closures, no `unsafe`, no `std::collections`. It uses its own hash map with `AList` buckets, `Vec<u32>` instead of `String`, and constant arrays instead of `vec![]`.
  - **Std model bug:** the **`Vec::insert` model was wrong** (modelled as `List.set`), so library models are part of the TCB.
  - **`Rc`/`Arc`** are modelled as the identity type, with `ptr_eq` returning `false`. That is sound only because pointer equality is used purely as a fast path.
  - **Proof effort:** 11,557 proof lines for 123 `_refines` lemmas. Ratios run from 2.2 (branchy pure code) to 5.1 (bignum), 5.9 (own hash map) and 6.2 (`Expr`). The rule of thumb is "about 3 proof lines per Rust line".
  - **Versioning:** pinned to an Aeneas revision; needs a 375-line patch to run the Aeneas library on Lean 4.33, and more for 4.35. Toolchain drift is a real cost.
- **Fit for rulean: best available.** The spec, the model and the proofs are all in Lean, and con-ron proves it works at kernel scale. The limits are performance-relevant features: no raw pointers, no interior mutability, no concurrency, no `unsafe`. The thread pool and the arena allocator must stay outside the verified subset or be hand-modelled.

### 3.2 hax (Cryspen)
- Translates Rust to F*, Rocq, ProVerif and Lean. **In July 2026 the Lean backend switched to the Charon+Aeneas pipeline**; the old engine is now `legacy-lean`. hax 0.4 (2026-10-01) targets Lean 4.31.0 [S]. https://hax.cryspen.com/blog/archive/2026/ ; https://github.com/cryspen/hax
- Its F* backend is mature (libcrux ML-KEM).
- For rulean it adds nothing beyond Aeneas, apart from the `hax-lib` annotation vocabulary [S].
- Experience report: the Rust→Lean pipeline (Aeneas or hax) with AI provers (Aristotle, Aleph) on Plonky3 and RISC Zero. The pain points were "Lean 4 toolchain drift across tools, Aeneas/Hax extraction limits, missing lemmas" [P]. https://arxiv.org/abs/2605.30106

### 3.3 Verus (CMU / MSR / VMware et al.)
- Papers [P]:
  - "Verus: Verifying Rust Programs using Linear Ghost Types", OOPSLA 2023.
  - "Verus: A Practical Foundation for Systems Verification", SOSP 2024, pp. 438–454: "verifies code 3–61× faster and with less effort than the state of the art". https://dl.acm.org/doi/10.1145/3694715.3695952
- **Approach:** SMT (Z3). Specs and proofs are written in Rust syntax (`spec`/`proof`/`exec` modes).
  - Linear ghost ("tracked") permissions such as `PointsTo` allow verifying **raw-pointer code**.
  - VerusSync supports **concurrency** (atomics, locks, sharded state machines).
- **Systems verified with it** [S]: VeriSMo (OSDI 2024), CortenMM (SOSP 2025), PoWER (OSDI 2025), AutoMan (SOSP 2025), the Atmosphere and Asterinas pieces. LLM tooling includes AutoVerus, VeruSAGE-Bench (849 tasks) and KVerus.
- **Fit for rulean:**
  - Verus is the strongest option for verifying the *fast, concurrent, unsafe* parts: arena allocator, lock-free hash-cons table, work-stealing pool.
  - But **specs are not Lean**, and there is no Verus→Lean bridge. Connecting to con-leche would need a manual "spec-equivalence" argument or a re-statement of the kernel spec in Verus's `spec` language. That is a semantic gap in the TCB.
  - The Verus tool itself and Z3 are trusted (no verified VC generator).

### 3.4 Creusot (Inria)
- Deductive verifier with **prophecy**-based mutable borrows (RustHornBelt). Translates to Coma/Why3, discharged by SMT solvers or Rocq. ICFEM 2022; active, tied to nightly rustc [P]. https://github.com/creusot-rs/creusot
- Safe Rust; unsafe only through Gillian-Rust.
- **Fit:** good automation, but no Lean target.

### 3.5 Prusti (ETH, Viper)
- NFM 2022. Little evidence of activity in 2025–26 [U]. https://github.com/viperproject/prusti-dev
- **Fit:** not recommended.

### 3.6 Kani (AWS; bounded model checking via CBMC)
- Bit-precise, and supports unsafe. Loops are unrolled to a bound, and there are no termination proofs [P].
- Main 2026 result: the **Rust std verification challenge** ("Verifying the Rust Standard Library", NFM 2026, LNCS 16622, arXiv 2606.17374) [P]. https://arxiv.org/html/2606.17374v1
  - Tools in CI: Kani, ESBMC, VeriFast and Flux. Verus, Creusot, KRust and RAPx are under review.
  - 29 challenges. 16,748 autoharnesses, of which 11,970 verified. 725 manual Kani harnesses. More than 50 VeriFast proofs. 989 functions verified against contracts.
  - Kani does **not** check aliasing (Stacked/Tree Borrows), data races, or all provenance UB.
  - "None of the tools are themselves formally verified."
  - Concurrency challenges 7 and 27 are unsolved.
- **Fit:** use Kani for UB-freedom of rulean's `unsafe` islands and for bounded checks of bit tricks such as packed handles and tag bits. It cannot carry functional correctness to Lean. https://github.com/model-checking/kani

### 3.7 RefinedRust (MPI-SWS / ETH / TU Delft)
- PLDI 2024, PACMPL 8(PLDI) 192. A refinement type system **proved sound in Rocq/Iris on RustBelt's lifetime logic**, giving foundational verification of safe *and unsafe* Rust. Case study: `Vec` [P]. https://dl.acm.org/doi/10.1145/3656422
- **Fit:** the most foundational choice for unsafe data structures. But it is Rocq, not Lean, and slow: 4m36s against 0.04 s for Gillian-Rust on EvenInt (Gillian-Rust paper).

### 3.8 Gillian-Rust (Imperial)
- "A Hybrid Approach to Semi-automated Rust Verification", PLDI 2025, PACMPL 9(PLDI) 186. Gillian-Rust handles unsafe code through a separation logic combining RustBelt and RustHornBelt. Its specs are reusable by Creusot for safe code. It is non-foundational [P]. https://dl.acm.org/doi/10.1145/3729289

### 3.9 Other 2026 work
- **Corten** (arXiv 2609.04372): foundational Rocq/Iris verification by embedding THIR, with an interaction-tree denotation. Case study: a buddy allocator [P]. https://arxiv.org/abs/2609.04372
- **RustCompCert** (arXiv 2602.07455, Feb 2026, Rust Verify 2026): a CompCert/CompCertO-based **verified compiler for a sequential Rust subset** ("Rustlight", with its own RustIR, not rustc MIR). It includes verified drop elaboration and borrow checking. Ongoing: "verifying all features of Rust is not realistic" [S]. https://arxiv.org/abs/2602.07455
- **Polonius verified** in CompCert's abstract-interpretation framework, with AI-generated proofs (arXiv 2611.06319, 2026-11-04) [P]. https://arxiv.org/abs/2611.06319
- **KMIR**: K-framework semantics of Stable MIR. A semantics, not a compiler [S].
- **Ferrocene**: a *qualified* (ISO 26262 / IEC 61508) rustc. It is a certification, not a verification [S]. https://ferrocene.dev

### 3.10 Summary matrix for rulean

| Tool | Logic | Lean spec? | Unsafe | Concurrency | Largest result | Role in rulean |
|---|---|---|---|---|---|---|
| Aeneas/Charon | Lean (pure model) | **yes** | no (hand-model) | no | con-ron, 41.5k Rust lines; SymCrypt, 16.7 KLOC | **the core checker** |
| hax | via Aeneas | yes | no | no | libcrux | none beyond Aeneas |
| Verus | SMT + Rust spec | no | yes (tracked permissions) | yes (VerusSync) | OS and storage systems | allocator, hash-cons table, thread pool (optional) |
| Kani | bounded model checking | no | yes | partial | Rust std challenge | UB-freedom of `unsafe` islands; bit-level lemmas |
| RefinedRust | Rocq/Iris | no | yes | limited | `Vec` | none (wrong logic) |
| Creusot / Gillian-Rust | Why3 / Gillian | no | Gillian only | no | case studies | none |

---

## 4. Verification strategies for a FAST kernel

### 4.1 The four options, with 2026 evidence

**(a) Verify the optimized code directly.**
- Lean4Lean's route: the kernel copies the C++ heuristics, and you prove `checkType.WF` against declarative typing.
- It is blocked on unique typing and Π-injectivity, which the kernel's optimizations depend on (Carneiro, slide 18).
- Even when done, it inherits the C++ design and its bugs: lean4lean had #14576.

**(b) Refinement chain: verified reference checker ⇐ optimized checker.** This is the con-leche → twin → con-ron → con-agua route, **demonstrated in 2026**.
- con-leche: the pure fueled checker is proved sound against the model, and the cached checker simulates it (memo tables keyed by packed hashes).
- con-ron, Theorem 1 (`Arena.checkDecl_bridge`, `Arena.pooledAccepts_bridge`): a twin over Rust-shaped data structures refines con-leche's checker. It is proved by induction in fold order, using `Std.WP` Hoare triples with two spec grades (`PSpec`/`CSpec`), and by induction on fuel for the checker's knot.
- con-ron, Theorem 2 (`Sim₀`): if Rust returns `Ok r` in state `st'`, the twin returns `A r` in a related state (`AStateRel₀`), and mirrored errors match. A custom `lockstep` tactic with `@[lockstep]` lemmas proves it.
- Composition (verbatim from `proof/ConRon/Capstone.lean`):
  ```lean
  theorem model_exists (V : Type w) [ConLeche.SetTheory V] {st1 … st6 : arena.monad.AState}
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1)) …
      (hreads : ReadsAs sinst src chunks.val) …
      (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
        (jobStep tier .Verified ipins prepared.decls)) :
      ∃ env, RustDenotes prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env)
  ```
  - `h1`–`h7` say the extracted Rust functions returned `Ok`.
  - `h8` is the **trusted contract of the unverified thread pool**.
  - `no_False_declaration` concludes `False` from the same premises plus `jsonWithTheoremFalse`.
  - The axioms are the three standard ones. The `_embedded` variant adds `PINS_TEXT._native.decide.ax_1` [P].
- **"Partial correctness"** (OVERVIEW §3.1): "con-ron may decline where con-leche accepts, but it never accepts where con-leche rejects." There is nothing about termination or completeness [P]. https://github.com/leanprover/con-ron/blob/master/OVERVIEW.md
- **Data structures inside the verified subset** [P]:
  - Expressions are hash-consed into **one array per constructor**. `EIdx` is a u32 with 4 tag bits for the constructor plus 1 bit for the tier (persistent vs per-declaration scratch).
  - Names, levels and level lists are hash-consed.
  - The structural-equality memo is keyed by stored hash words, with `ptr_eq` only as a fast path.
  - The bignum is `ron::Nat` = `Vec<u64>` limbs, with refinement lemmas against ℕ in `proof/ConRon/Refine/`.
- **Size, measured** [P]: `crates/con-ron-core` is 110k lines of `.rs`, including tests and comments; the verified core is 41.5k per AENEAS_FINDINGS. `proof/ConRon`: Generated 118k, Refine2 117k, Bridge 94k, Arena twin 34k, Refine 22k. The repository holds 388k lines of Lean in total.
- **con-agua** goes one level lower [P] https://github.com/leanprover/con-agua/blob/master/OVERVIEW.md
  - L is first-order, with 64-bit words, numbered locals, fixed arrays, loops and calls, and *no pointers, closures or allocation*. The checker is about 1,800 L functions.
  - `compileProg` is a one-pass L→x64 compiler. `compile_correct` is a forward simulation against Kraken, proved once for all well-formed programs.
  - Bounds-check elimination removes 1,244 of 7,986 checks (1.9% of instructions). Inlining saves 2.1%.
  - Hand-written x64 `mul_row`/`sub_row` bignum kernels each have their own simulation proof.
  - Hash-consing uses open addressing with linear probing, growth at load 3/4, and an O(1) scratch reset with 15-bit epochs.
  - The end-to-end theorem `checkerFile_accepts` (quoted): for the committed `checker.s`, every run returns to `ra`, and `rdx = 0 → rax = ACCEPT → TwinAccepts [b]`.
    - `Ev` is "every run reaches the postcondition", so **termination is included**.
    - The assumptions are `h64 : System.Platform.numBits = 64` and `AbiCall`.
  - **Trusted**: Kraken's x64 semantics (sequential, without virtual memory or permissions; validated by a differential instruction fuzzer), the assembler, linker and loader, the asm-file parser, the C harness (about 200 lines), the OS, Lean's kernel, and the `SetTheory` assumption.
  - **Threads are unverified**: `ThreadsRun` and `ThreadsFail` are hypotheses, and "L has no atomics".
  - **Performance** relative to con-ron on `Init`: wall time 0.99×, instructions 1.19×, RSS 1.9×. Speedup over one thread is 6.2× at 16 threads.
  - Arena Mathlib: 10.9 min, 11.6 GB.
  - Size: about 1,496 Lean files, 436k lines [P, measured]. First commit 2026-10-21.
  - Kraken: https://github.com/sgraf812/kraken [P via OVERVIEW].

**(c) Certificates and translation validation.** The fast kernel emits a trace that a small verified checker validates.
- Precedents:
  - cake_lpr: untrusted DRAT→LRAT elaboration, then a verified LRAT check. Run at SAT Competition scale.
  - The Isabelle metalogic checker.
  - ind-models, which validates inductive declarations by translation.
  - Lean4Less, which turns definitional proof irrelevance and K-like reduction into explicit casts.
- For Lean, **no defeq-certificate format exists** [U: not found]. A trace of "which rule closed each `is_def_eq`" could be checked by con-leche-style rules (`Red`/`DefEq`/`Infer` are already accepting-direction derivation relations), but trace size on Mathlib is unknown.
- Benefit: the fast kernel stays fully unverified, uses `unsafe` and SIMD, and may take 10x+ liberties.
- Cost: the certificate checker must itself be fast, or it becomes the bottleneck.

**(d) Differential testing, fuzzing, and proof only for critical cores.**
- This is the status quo of the 2026 ecosystem: about 25 kernels, the Arena (90 bad, 145 good and 30 corner tests, plus Mathlib, cedar, cslib, std, navier-stokes and reachability), and `lake check --paranoid`.
- The 2026 bug record shows it works for *detection*: every Lean kernel bug in 2026 was caught by at least one independent checker. It does not give *proof*.
- It is still the only way to establish "accepts exactly what the official kernel accepts".

### 4.2 Building blocks with prior verification work

| Component | Prior work | Notes |
|---|---|---|
| Hash-consing | Braibant, Jourdan, Monniaux, "Implementing and Reasoning About Hash-consed Data Structures in Coq", JAR 2014, 4 approaches [S] https://link.springer.com/article/10.1007/s10817-014-9306-0 | con-ron and con-agua do it inside the verified subset with integer handles [P]. **The pattern: handles are indices into arrays; pointer equality is never semantic.** |
| Union-find | Charguéraud & Pottier, correctness **and amortized complexity** (find costs 2α(n)+4) in CFML separation logic with time credits; ITP 2015, JAR 62(3) 2019 [S] https://link.springer.com/article/10.1007/s10817-017-9431-7 | The C++ and lean4lean kernels use union-find for defeq caching [P, slide 7]. con-leche does without it. |
| Memoization | Wimmer, Hu, Nipkow, "Verified Memoization and Dynamic Programming", ITP 2018 [S] https://www.isa-afp.org/entries/Monad_Memo_DP.html | con-leche: one-directional simulation of the cached checker into the pure checker [P]. **Lean bug #14806 shows caches must be order-independent** [P]. |
| Bignum | WhyMP (Melquiond, Rieu-Helft): a Why3-verified GMP-compatible mpn/mpz subset (Toom-Cook, division, sqrt), competitive with assembly-free GMP, **about 4 person-years**; ISSAC 2020 / JSC [S] https://guillaume.melquiond.fr/doc/20-issac-article.pdf | con-ron's `ron::Nat` was verified at 5.1 proof lines per Rust line [P]. con-agua hand-wrote x64 rows [P]. The Lean runtime's GMP had soundness bugs in 2022 and 2026 [P]. **Kernel Nat ops need only add/sub/mul/div/mod/gcd/beq/ble/land/lor/xor/shift/pow/log2, a much smaller surface than GMP.** |
| Fixed-width arithmetic and crypto style | fiat-crypto (Rocq; generates field arithmetic; fixed-size only) [S] https://github.com/mit-plv/fiat-crypto | Not directly applicable. |
| Concurrency | RustBelt (POPL 2018) and RustHornBelt (PLDI 2022) on Iris; Verus VerusSync (SOSP 2024) [S] | In con-leche, con-ron and con-agua **the parallel layer is trusted in all three** [P]. Verdicts are index-merged and deterministic by design. A Verus-verified work-claiming pool is a realistic target. |

### 4.3 The end-to-end trust chain (what is possible today)

```
ZFC + ω inaccessibles (assumed; Gödel II: cannot be removed)
  └ SetTheory V class  ⇐ carneiro_implies_conleche (OmegaInaccessibles → SetTheory)   [P]
     └ con-leche pure checker: accepted ⇒ IsModel  (Lean proof, 3 axioms)                [P]
        └ cached checker ⊑ pure checker (one-directional simulation)                      [P]
           └ twin ⊑ con-leche (Theorem 1)                                                 [P]
              └ Aeneas model of Rust ⊑ twin (Theorem 2)                                   [P]
                 └ Charon/Aeneas translation fidelity + std models : TRUSTED              [P]
                    └ rustc + LLVM + std + allocator + OS           : TRUSTED              [P]
              └ (alt.) L program ⊑ twin; compile_correct L→Kraken x64   [P, con-agua]
                    └ Kraken x86 semantics + assembler/linker/loader + main.c: TRUSTED
  Lean kernel checking all of the above: TRUSTED (mitigate: check proofs with nanoda,
  con-ron, con-agua themselves)
```

- There is **no verified compiler for real Rust**. RustCompCert is a subset with its own IR; Ferrocene is qualified, not verified.
- So a pure-Rust rulean binary can at best be "verified up to Aeneas, rustc and LLVM", like con-ron.
- Diversity (con-leche on the Lean runtime, con-ron on rustc, con-agua on Kraken) is the 2026 mitigation for compiler and runtime bugs [P].

---

## 5. AI-assisted proof engineering at kernel scale

- **con-leche, con-ron and con-agua** were each "written by AI under supervision from Joachim Breitner". The blog says "Claude (Fable and Opus)" [P].

  | Repository | Wall-clock (first commit → ship or now) | Commits | Lean lines | Other lines |
  |---|---|---|---|---|
  | con-leche | about 8 weeks | 7,949 | 365k | |
  | con-ron | about 5 weeks | 4,365 | 389k | 110k Rust |
  | con-agua | about 4 weeks | 9,991 | 436k | 234k asm |

  - Measured via the GitHub API and `wc` [P].
  - This puts the human cost of a verified kernel at one expert supervisor for months, not a team for years.
  - The cost moves to review and specification fidelity. Hales and Carneiro both stress human understanding [P].
- **SymCrypt/Aeneas**: "a few dollars per line of Rust". About 125 KLOC of agent-written proofs. Opus 5 "is the only model that closes all 7" hard proofs [P] (arXiv 2609.15648).
- **AI as attacker**: Claude Opus 4.6 found Rocq bugs (Mar 2026). OpenAI models found Lean kernel bugs (Aug 2026). An AI-assisted Collatz exploit triggered #14576 [P]. **rulean must assume adversarial, AI-crafted inputs**: per-feature fuzzing, the Arena tests, and the bad tests as regression.
- **Fermat's Last Theorem** [P] https://www.anthropic.com/research/formalizing-fermats-last-theorem ; https://github.com/anthropics/fermats-last-theorem
  - 13M lines of Lean, 29,511 theorems in the final proof (about 30,300 total), about 6B output tokens.
  - The run lasted 11 days (Aug 7–18, 2026) and was announced 2026-09-04. It used Prove2Me (arXiv 2608.28433) and "a general-purpose internal research model roughly comparable to Claude Fable 5.1".
  - It was checked by comparator and nanoda 0.4.13 ("Checked 1052234 declarations"). nanoda took about 30 min on 16 threads and 40 GB, plus a 1 h export at 90 GB.
  - **This is a rulean workload.** The export is 37.8 GB, and nanoda needed patches to avoid "many hours" on some declarations.
  - Follow-up: 1,000 Fable 5.2 agents redid it in 30 hours [S] (Anthropic Fable 5.2 launch post).
- **Limits** [P]:
  - Carneiro will not merge LLM unique-typing proofs he does not understand.
  - SymCrypt models "try to cheat".
  - con-leche's docs flag AI-generated history and inconsistent counts (strict-lean assessment).
  - The theorem *statements* (`Challenge.lean`, `MainTheorem.lean`, `SetTheory`) are the human-audit surface. con-leche puts them in one file with holes, so they can be audited.

---

## 6. Recommended verification architecture for rulean

### 6.1 What can be proved (pin this down in the spec)

**Soundness theorem (formal, required).** Mirror con-ron:

```lean
theorem rulean.model_exists (V) [ConLeche.SetTheory V] … (hrun : <extracted Rust calls return Ok>) :
  ∃ env, RuleanDenotes decls st env ∧ Nonempty (ConLeche.Model V env)
```
plus `rulean.no_False_declaration`.

- Use **con-leche's `SetTheory`/`IsModel` as the specification**. Do not invent a new one. It is the only completed consistency proof for Lean as of November 2026. It is already linked to Carneiro's `OmegaInaccessibles`, and it is what the Lean distribution ships under `--paranoid`.

**Completeness relative to the official kernel (empirical, required).** "Accepts exactly what official accepts" is not formally provable today:
- The official algorithm has no formal semantics.
- Its defeq is non-transitive and incomplete for the undecidable declarative theory.
- The con-* family already declines 6/145 good Arena tests.

Specify it as:
- (i) 100% agreement with the official kernel on Mathlib, the Arena (good, bad and corner), FLT-Anthropic, cslib, std and cedar. Checked in CI per Lean release.
- (ii) Differential fuzzing against official, nanoda and con-ron.
- (iii) Optionally later, a *simulation theorem against lean4lean* (lean4lean accepts within fuel F ⇒ rulean accepts), once lean4lean's verification lands.

**Rejection of what official rejects** follows from soundness only for inconsistent inputs. For ill-typed but consistent inputs it is also empirical (the Arena "bad" tests).

### 6.2 Architecture: refinement chain plus an unverified turbo layer behind a certificate gate

1. **Layer 0, the spec.** Import con-leche's `SetTheory`, `IsModel` and `checkDeclsPure`, pinned by revision. Do not fork the metatheory.
2. **Layer 1, the Lean twin of rulean's algorithm.** Write rulean's algorithm as a Lean twin over rulean's actual data layout: per-constructor arrays, u32 tagged handles, two tiers, hash-consed names and levels, packed-hash memo tables, and an NbE or closure-based whnf if desired. Prove it refines `checkDeclsPure` (as con-ron's Theorem 1).
   - This is where rulean's algorithmic speedups live: better reduction strategy, lazy unfolding, sharing.
   - Each speedup is a refinement obligation in Lean against a pure spec, not in Rust.
   - Use con-ron's `Arena` twin (34k lines) and its `PSpec`/`CSpec` and `lockstep` infrastructure as the starting point.
   - Keep con-leche's "extra checks" only where the soundness proof needs them, and measure their cost. In con-leche, verified mode costs 7.05 T instructions against 6.40 T for trusted mode on Mathlib, about 10%.
3. **Layer 2, the Rust core in the Aeneas subset.**
   - Safe Rust, no closures, no `dyn`, no `RefCell`, no `std::collections`, no early returns inside loops, and `Vec<u32>` instead of `String`.
   - Prove Rust ⊑ twin (as con-ron's Theorem 2) with `lockstep`.
   - Budget about 3–6 proof lines per Rust line, using AI agents.
   - Pin Aeneas, Charon and Lean, and plan for a toolchain bump per Lean release.
4. **Layer 3, unsafe and concurrent islands.** These are outside Aeneas and stay as small and as few as possible:
   - (a) the arena allocator and bump-free scratch reset;
   - (b) the parallel work-claiming pool;
   - (c) optional SIMD hashing and mmap'd export parsing;
   - (d) bignum limb kernels if hand-optimized.

   Each gets a **Lean-stated contract**, like con-ron's `h8 : ParallelAll …`, so the capstone theorem names it as a hypothesis. Each contract is discharged *outside* Lean by Verus (concurrency, raw pointers), Kani (UB-freedom, bounded bit-level lemmas), or a hand model reviewed by people.

   The capstone stays honest: "model exists, assuming contracts C1..Cn", and Cn is listed in the spec.
5. **Layer 4, diversity instead of a verified compiler.**
   - rustc and LLVM stay trusted. Mitigate by shipping rulean alongside con-leche (Lean runtime) and, for the highest assurance, con-agua (Kraken x86).
   - A proof accepted by rulean plus one non-rustc verified kernel is protected from rustc and LLVM miscompilation.
   - Do not try to build a verified Rust compiler: RustCompCert is years from real Rust.
6. **Optional Layer 5, certificate mode for a "turbo" path beyond the verified subset.**
   - An unverified fast path (SIMD, unsafe, aggressive caching) may *propose* defeq successes that the verified core replays, or it emits a trace for a verified trace checker.
   - Only worth doing if measurements show that the Aeneas subset caps performance below target. con-ron's 3.5x and con-leche's 17x at 8 threads suggest it may not.

### 6.3 Tradeoffs

| Choice | For | Against |
|---|---|---|
| Spec = con-leche model (recommended) | Finished, shipped, already linked to Carneiro's model. Avoids the open unique-typing problem. | Requires con-leche's extra checks, which are slower, and its deviations from official. Ties rulean to con-leche's revisions. Shares con-leche's specification errors. |
| Spec = Lean4Lean declarative typing | Closest to the official kernel, so it could support completeness theorems. | Needs unique typing, Π-injectivity and consistency, all still `sorry` (Nov 2026). Timeline [U]. |
| Aeneas for the core (recommended) | Lean-native. Proven at kernel scale (con-ron). AI-friendly (SymCrypt). | Partial correctness only. Translator in the TCB. Subset forbids raw pointers, interior mutability, threads and closures. Toolchain drift (375-line patch). OOMs on large functions. A wrong std model (`Vec::insert`) slips through. |
| Verus for the islands | Handles unsafe and concurrency; fast SMT. | Specs not in Lean, so the semantic gap is manual. Z3 and Verus are trusted. |
| con-agua-style custom IR to x86 | Removes rustc, LLVM and Aeneas from the TCB. Proves termination. | Not Rust, so it violates the project's "pure Rust" premise. Only sequential. Hand-written bignum asm. |
| Certificate checking | Fast path unconstrained. | No Lean defeq-certificate format exists. Trace size unknown. The checker can become the bottleneck. |
| Differential testing only | Cheap. Catches most bugs (2026 record). | Not verification. Does not meet the "MUST BE FORMALLY VERIFIED" requirement. Still needed for completeness. |

### 6.4 Performance feasibility (10x with verification)

- **Unverified Rust**: 10x is already beaten. nano-lean takes 65.9 s against 33.7 min for official (about 30x, 4 threads). kefir is 4.7x on 1 thread [P].
- **Verified Rust today**: con-ron is about 3.5x wall time (4 threads against single-threaded `leanchecker`) and about 2.7x per thread in instructions [P].
- **Biggest known waste**: in con-leche, 45–48% of instructions are Lean-runtime allocation and refcounting [P]. con-ron removed it with arenas and hash-consed handles.
- **Next levers** (all in Layer 1, provable as refinements):
  - Skip unread binder arguments, as gruszka and pestka do.
  - NbE for whnf, as gruszka does.
  - Context-free caches with typed canonical locals, as palladium does.
  - Avoid `let` substitution; con-leche's known gap is its `let` handling.
  - More threads. con-leche's verdict is index-merged and scales to 8 threads at about 17x wall time against official.
- 10x wall time at 8 threads with a verified core is plausible. 10x on a single thread is **not yet demonstrated** by any verified kernel [U].

### 6.5 Effort estimate (AI-assisted, 2026 rates)

- con-ron-class verified port: about 5 weeks, 1 expert plus AI, about 40k verified Rust lines and about 280k Lean lines (generated, twin and refinements) [P-derived].
- rulean adds a new twin and new optimizations, so budget **3–6 months, 1–2 experts plus agents**.
- Ongoing cost: Lean, Aeneas and Charon toolchain bumps every month; Arena regression on every Lean release; and resyncing with con-leche (Breitner keeps it in sync with kernel renovation issue lean4#14977) [P].

---

## 7. Corrections and verification status of claims in the old notes (`2148/01-research-2026.md` §1.2)

| Old claim | Status |
|---|---|
| Arena: "127 good and 72 bad tests plus Mathlib" | **Outdated** [U for the old figure]. The current round has 145 good, 90 bad and 30 corner tests; the March blog said 133 benchmarks. |
| Hales counts about 25 kernels | Confirmed [P]. |
| nanoda: under 5,000 lines; about 15.6 min, 6 GB | Roughly confirmed [P]. The Arena now shows 16.0 min and 6.0 GB. The line count comes from the March blog. |
| **lean4lean about 38.8 min, 11.6 GB** | **Could not be verified.** The current Arena reports no Mathlib time for lean4lean, which ran only 123 good tests. 11.6 GB matches the tenet and con-agua rows, so this may be a mis-copy. Carneiro's own figure is 58.79 min against 44.54 min (1.32×, June 2025). |
| con-leche: "checks Mathlib in about 100 s on 8 threads" | Confirmed, but needs qualifying. It was one run on a shared 96-core machine (PERF.md). It is 10.7 min on one thread and **17.0 min in the Arena at 4 threads**. The 0.69× instruction figure is against the official v4.33 kernel. |
| "con-ron is a Rust translation proved to refine it via Aeneas" | **Overstated.** It is a twin with different data structures, not a direct translation. The guarantee is partial correctness only. The thread pool (`h8`), file IO and the `Arc`/`str` models are trusted. The README says it is "not a high assurance verification effort". |
| "con-leche: every environment it accepts has a set-theoretic model" | Correct, but *relative to the assumed `SetTheory V`* (ZF⁻ plus an ω-chain of Grothendieck universes), and only in `--verified` mode. The binary-to-theorem link (Lean compiler and runtime, IO) is assumed. It is **not complete**: it declines 6 good tests. |
| "ind-models checks that inductive types have models" | Imprecise. It is *translation validation* into an extensional system, "not a general soundness proof… not yet a verified translation". |
| "lean4lean verification expected within months" | Confirmed as de Moura's expectation [P]. But unique typing and Π-injectivity are still conjectures (Carneiro, 2026-10-22), and `lean4lean-model`'s `consistency` is still `sorry`. |
| "Claude Opus 4.6 found 7 Rocq kernel bugs and 2 nanoda bugs, no false proofs in Lean's kernel" | Confirmed with nuance: it was "a skilled researcher" (Tristan Stérin) using Opus 4.6 with Rocq-team support. Secondary sources add 3 non-False Rocq bugs and 4 non-False Lean bugs. |
| Hales: no complete public consistency proof | Confirmed [P]. Also: "an error was found in the thesis" (the unique-typing stratification gap). |
| FLT "about 13M lines in 11 days" | Confirmed [P]. The model was "a general-purpose internal research model roughly comparable to Claude Fable 5.1", not a named public Claude model. The run was Aug 7–18. |
| #14576 and the bug-hunt list (#14613, #14616, #14806, #14807/#14843, refcount, GMP) | Confirmed [P]. All found by Daniel Selsam with OpenAI internal models. nanoda missed #14807. |
| "De Moura: 'AIs are really good at exploiting soundness bugs'" | Not re-verified [S/U]. |
| Not in the old notes, but important | **con-agua** exists: verified down to x86 through Kraken, 10.9 min in the Arena. The Arena has many faster unverified Rust kernels (nano-lean, gruszka, sokonanoda, kefir, palladium). |
