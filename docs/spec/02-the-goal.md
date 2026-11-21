# 02. The goal

This document states what rulean is, what each of its three promises means in measurable terms, and what rulean does not do. Every number here comes from document 01 and has a date. Section 02.6 explains why the promises are stated in this exact form.

## 02.1 One sentence

rulean is a Lean 4 kernel in pure Rust that gives the same verdict as the official kernel on every Lean environment, uses at most one tenth of the official kernel's instructions, and has a machine-checked proof that every environment it accepts has a set-theoretic model.

## 02.2 The three promises

The user request has three requirements. Each one is ambiguous as written. This section gives each one a single, testable meaning.

### P1. "10x faster than the original kernel"

**Definition.** On a corpus C and a Lean release R, the speed ratio is

    ratio(C, R) = instructions(official leanchecker of release R on C) / instructions(rulean on C)

where "instructions" is the sum of retired user-space instructions over all threads, measured with the Lean Kernel Arena method (`perf stat -e instructions:u`, virtual time = instructions / 6.0 G per second). The input is the lean4export NDJSON stream of release R, and parsing is included on both sides.

**Targets.**

| ID | Corpus | Target | Status at 2026-11-21 |
|---|---|---|---|
| P1.a | Mathlib (5.9 GB export, Lean v4.36.0) | ratio ≥ 10 against the stable release; this is at most 1.21 T instructions against v4.35.0 | con-ron 3.5, nano-lean 30.6 (unverified) |
| P1.b | Mathlib, against the official nightly of the same month | ratio ≥ 10; at most 0.98 T today | con-ron 2.8 |
| P1.c | Init, Std, CSLib, Cedar, Navier-Stokes, FLT (Anthropic) | ratio ≥ 10 on each corpus separately | not measured for verified kernels on FLT |
| P1.d | Arena `perf/` tests | no test above 1 virtual second; official takes up to 35 s | NbE kernels meet this; con-ron does not |
| P1.e | Mathlib, wall time, 8 threads, one 2025-class workstation | at most 60 s, including parsing | con-leche 100 s on a 96-core server |
| P1.f | Peak memory on Mathlib | at most 4 GiB | con-ron 4.4 GiB, official 9.9 GiB |

**Rules.**

- The instruction ratio is the main metric. It does not change with the machine, and parallel threads cannot make it better. A 10x result that comes only from threads does not count, because con-ron already has 15x in wall time from 4 threads against the single-threaded official checker.
- The baseline is the official kernel of the same Lean release. When the official kernel gets faster, the target gets harder. The official kernel used 34% fewer instructions between v4.28.0 and the 2026-11-14 nightly. Plan for a further 2x before rulean 1.0 (15.2).
- The verified build is the build that is measured. An unverified "fast mode" does not count toward P1.

### P2. "Must run every Lean program"

The Lean kernel does not run programs. It checks declarations. Since Lean v4.35.0 (PR lean4#14953) the kernel never calls compiled code: `native_decide` makes an auxiliary axiom `_native.….ax` instead of a kernel call. So "run every Lean program" has this meaning for a kernel:

**Definition.** For every environment E that any Lean program can produce (a `.olean` tree, or a lean4export stream), and for every declaration d in E:

- **P2.a, completeness against official.** If the official kernel of release R accepts d, rulean accepts d.
- **P2.b, strictness against official.** If the official kernel of release R rejects d, rulean rejects d.
- **P2.c, same report.** rulean reports the same set of axioms for each theorem as `#print axioms`, including `sorryAx` and `_native` axioms.
- **P2.d, in-process use.** From milestone M6, rulean can replace the C++ kernel inside a Lean process, through `lean_add_decl` and the other kernel entry points (09.6). Then every Lean program (the elaborator, tactics, `lake build`, `#eval` of meta code) runs unchanged with rulean as its kernel.

**What "every" covers.** The conformance corpus (11.2) is the operational meaning of "every": Lean core (Init, Std, Lean, Lake), Batteries, Mathlib, CSLib, Cedar, the two FLT projects, Navier-Stokes, the 17.5 M line RH project of 2026-11-20, all Lean Kernel Arena tests, and the rulean regression and fuzz corpus. The corpus grows. It never shrinks.

**Exceptions.** P2.a and P2.b are equalities of verdicts. Three classes of input need a stated policy, because even the reference behaviour is not defined for them:

1. **Arena "either" tests** (30 tests). rulean follows the official verdict. Each such case is a row in the deviation register (05.12), even when rulean agrees.
2. **Resource limits.** The official kernel can fail with `deterministicTimeout`, `deepRecursion` or `excessiveMemory`. A faster algorithm can succeed where the official kernel times out. Policy: a resource failure is not a verdict. rulean reports `resource` with the limit that was hit. In compatibility mode (`--limits=official`), rulean counts heartbeats in the official way and reports the same failure (05.11).
3. **Unsafe declarations.** The official kernel accepts `unsafe` declarations with weaker checks, and no safe declaration may refer to them. rulean accepts them in a separate quarantine tier (05.10). They are outside the model theorem. The theorem proves that no safe declaration depends on them.

### P3. "Must have formal verification"

**Definition.** The repository contains a Lean proof, checked by the Lean kernel and by at least two independent kernels, of this statement:

> **Theorem (rulean soundness).** Assume ZF set theory with an ω-chain of Grothendieck universes (con-leche's `SetTheory V`), and assume the named contracts K1 to Kn of the unverified islands (10.7). If the Rust function `rulean_core::check_stream`, as translated by Charon and Aeneas, returns `Accept` on a byte stream b, then b parses to a declaration list ds, and the environment of the safe declarations of ds has a model in which every constant denotes an element of the denotation of its type. In particular, no accepted safe declaration has type `False`, unless it uses an axiom outside {`propext`, `Quot.sound`, `Classical.choice`}.

**Rules.**

- The specification is con-leche's model (`ConLeche.SetTheory`, `ConLeche.Model`), pinned by commit. rulean does not invent its own metatheory (10.2).
- The theorem covers the Rust code that is shipped and measured for P1, not a slower copy.
- Each trusted component is named in the trusted computing base table (10.8), with the reason and the mitigation.
- P2 is not a theorem. Completeness against the official kernel cannot be proved today, because the official algorithm has no formal semantics and its definitional equality is not transitive (01.6). P2 is a testing property with a 100% target on the conformance corpus (11). An optional later theorem relates rulean to lean4lean (10.11).

## 02.3 Why rulean, when con-ron exists

As of 2026-11-21, no kernel has all three properties.

| Kernel | P1: instructions vs official | P2: verdict parity | P3: verified |
|---|---|---|---|
| official C++ | 1.0 | reference | no |
| nano-lean (Rust, NbE) | 30.6 | yes on the Arena | no |
| gruszka (Rust, NbE) | 23.6 | yes on the Arena | no |
| con-ron (Rust, Aeneas) | 3.5 | no: declines 6 good tests, Cedar, unsafe, partial; makes theorems opaque | yes, partial correctness |
| con-agua (x86, verified compiler) | 3.1 | no (same algorithm as con-ron) | yes, down to x86 |
| con-leche (Lean) | 2.0 | no (same as con-ron) | yes |
| lean4lean (Lean) | 0.8 | yes (port of the C++ code) | no: key lemmas still `sorry` |

The gap is clear. The fast kernels are not verified. The verified kernels are 3x too slow, and they do not accept every Lean program. rulean closes the gap. It takes the verification method of con-ron and the evaluation method of the NbE kernels, and it adds verdict parity with the official kernel as a first-class requirement.

## 02.4 Who uses rulean

| User | Use | What they need from rulean |
|---|---|---|
| Lean users and Mathlib CI | `lake check --paranoid`, or the kernel inside `lake build` (M6) | parity (P2), speed (P1), the same error messages |
| AI proof pipelines (FLT, RH, Erdős, comparator users) | check 10 M to 50 M line projects made by models | speed at scale, memory limits, robustness against hostile input (12) |
| Competition and benchmark judges (comparator, Lean Eval, MathArena) | an independent verified kernel in the check chain | soundness theorem (P3), a small trusted base, reproducible verdicts |
| Math 2.0 and riemann (specs 2148, 2148r) | the second-kernel replay of their trust reports | a CLI, JSON reports, axiom lists (09.4) |
| Kernel researchers | a fast verified base to try new rules on | readable code, the Lean twin, the deviation register |

## 02.5 Non-goals

- **rulean is not a Lean runtime or compiler.** It does not replace the IR interpreter, the C code generator, GMP in compiled programs, libuv or the 1,013 `@[extern]` primitives. That is a different project, about 100 times larger. See 01.9.
- **rulean is not an elaborator.** It checks the output of elaboration. It does not do unification, type class search or tactics.
- **rulean does not change Lean's logic.** It does not add or remove rules. Where con-leche accepts more than the official kernel (for example semantic level comparison), rulean does not, by default (05.12).
- **rulean does not check statement fidelity.** No kernel can tell if a formal statement says what a person meant. That is the job of comparator and of human review.
- **rulean does not prove completeness.** See P3, rules.
- **rulean does not support Lean 3**, or Lean 4 releases before v4.35.0. Releases before v4.35.0 let the kernel call compiled code (`Lean.reduceBool`), and v4.33.1 is the first release with the 2026 soundness fixes. rulean supports named semantics profiles from v4.35.0 on (05.2).

## 02.6 Why these definitions

- **Instructions, not wall time.** Wall time depends on the machine and the thread count. Verified kernels already beat the single-threaded official checker by 15x in wall time on 4 threads. That does not mean their algorithm is faster. The Arena publishes instructions, so anyone can check the number.
- **Parity, not "accept more".** Users do not want a kernel that accepts a proof the official kernel rejects. Their build uses the official kernel, so that proof is useless to them, and the difference makes people distrust both kernels. They also do not want a kernel that rejects a proof Lean accepted, because then a proof that builds in Lean does not check in rulean.
- **Model theorem, not typing theorem.** The declarative typing of Lean still has open conjectures (unique typing, Π-injectivity). The con-leche model theorem avoids them and is complete today. A model theorem also says directly what users care about: an accepted proof of `False` is impossible.

## 02.7 Reference scale

These numbers set the size of the problem. They come from document 01 and are re-measured in milestone M0.

| Quantity | Value | Date |
|---|---|---|
| Mathlib declarations | about 700,000 | 2026-11 |
| Mathlib export | 5.9 GB, 112.1 M lines | 2026-11-21 |
| Official instructions per Mathlib declaration | about 11.9 M (v4.33) | 2026-10 |
| Target instructions per Mathlib declaration | at most 1.7 M (P1.a); stretch 0.7 M | |
| Largest known project checked by a second kernel | FLT (Anthropic): 1,052,234 declarations, 37.8 GB export; nanoda took about 30 min on 16 threads and 40 GB | 2026-09 |
| Largest known project | RH (Alpöge): about 17.5 M lines, 175,187 modules, about 1.06 M declarations | 2026-11-20 |
| Slowest single Mathlib declaration (con-leche) | 0.73 s | 2026-10 |
| Slowest single FLT declaration (gruszka) | 3.7 s | 2026-11 |
