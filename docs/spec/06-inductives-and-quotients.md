# 06. Inductive types and quotients

This document specifies how rulean checks an inductive declaration, how it generates recursors, and how it adds quotients. Inductive types are the part of the kernel with the most 2026 soundness bugs (#14576, #14582, #14613, #14616, #14806, #14808, #16279, #16512). So this part has the strictest rules on recomputation and on independent cross-checks.

Source: research/A-lean-kernel.md section 1.11 and 1.12 (`inductive.cpp`, 1,415 lines, and `quot.cpp`, 123 lines, on master ab8894fb), and research/C section 1.5 (ind-models).

## 06.1 Input and trust

An inductive declaration in the export (07.1) contains three parts: the types, the constructors and the recursors. Only the first two are input. rulean rebuilds everything else:

| Exported field | rulean use |
|---|---|
| types: name, level params, type, numParams, numIndices | input; numIndices is recomputed and compared |
| ctors: name, type | input |
| ctors: induct, cidx, numParams, numFields | recomputed; a mismatch is a reject |
| types: all, ctors, numNested, isRec, isUnsafe, isReflexive | recomputed; a mismatch is a reject (isUnsafe is input) |
| recs: the whole recursor, with rules and the K flag | regenerated; compared with the export up to α-equivalence; a mismatch is a reject |

leanchecker `--from-export` does the same for Quot (A§4.1). A reject on a mismatch is official-compatible, because a correct exporter always writes the values that the kernel generates.

## 06.2 Checks, in the official order

The order matters for parity, because the first failing check decides whether a malformed input is rejected or whether a later step fails with a resource error.

1. **No metavariables, free variables or loose bound variables** in any type or constructor (#14607, #16512 under profile flag `inductive_loose_bvar_check`).
2. **Counts.** numParams, numIndices and the constructor counts are 64-bit. A count at or above 2^32 is a reject (#16279, flag `count_64`). In profile `v4.35`, the official kernel truncated to 32 bits. rulean rejects those inputs in every profile and records this as a deviation only if a test shows that v4.35 accepted one (none known).
3. **`check_inductive_types`** (A§1.11 step 2):
   - every type has the same parameters, definitionally equal;
   - numIndices is counted after whnf of the type telescope;
   - every type has the same result sort, compared with `is_equivalent` (#14615).
4. **`check_uniform_ind_occs`** (#14582): every occurrence of a type being declared is applied to exactly the declaration's level parameters and the parameter bound variables. Over-applied occurrences are checked inside.
5. **`check_constructors`**, for each constructor:
   - no duplicate names; the parameters match;
   - each field's sort `l` satisfies `is_geq(result_level, l)`, or the result normalizes to zero;
   - strict positivity, unless unsafe: an occurrence of a type being declared appears only as the head of a field type `Π xs, I params idx`, with no occurrence in `xs`;
   - `is_valid_ind_app`: the result has exactly the parameters, and the indices do not mention the types being declared (#2125).
6. **Nested inductives** (06.3).
7. **Large elimination** (06.4).
8. **Recursor generation and `check_recursors`** (06.6, #14808).

## 06.3 Nested inductives

A nested inductive has an occurrence of a type being declared as an argument of another inductive, for example `List Tree` inside `Tree`.

rulean uses the official translation (A§1.11 step 5):

1. `elim_nested_inductive`: for each nested occurrence `J As (I …)`, make an auxiliary inductive named `_nested.J_n`. It is a copy of J specialised to the arguments. User names with the prefix `_nested` are rejected (#14616).
2. **Type-check the parametric arguments `Ds` of each nested occurrence** (#14577, the fix for #14576). This is the check that the Collatz exploit escaped.
3. Check the translated mutual declaration with 06.2.
4. `restore_nested`: map the auxiliary types back to the nested form. A failure throws a reject, never an assert (#14633). The result is checked again (#14621).

The translation is in engine R code only (05.5). There is no fast-path version: inductive declarations are a small share of Mathlib declarations (to be measured in M0), and their checks are close to linear in their size.

## 06.4 Large elimination

The rule `elim_only_at_universe_zero` decides whether the recursor can eliminate into any sort or only into `Prop`. The official order is (A§1.11 step 6):

1. The result level is not zero: large elimination is allowed.
2. The declaration is mutual: only into `Prop`.
3. More than one constructor: only into `Prop`.
4. Zero constructors: large elimination is allowed.
5. **Profile `master` only** (flag `no_large_elim_rec_prop`, #13851): the type is recursive: only into `Prop`. This removes large elimination for `Acc`.
6. Otherwise: every field that is not a proposition must occur in the indices of the result type. If not, only into `Prop`.

Where con-leche allows more large elimination than the official kernel, rulean follows the official rule by default (05.12, D4).

## 06.5 Quotients

`quot` declarations add `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` (A§1.12).

- `Eq` must exist with exactly the expected shape: `Eq.{u} : {α : Sort u} → α → α → Prop`, one constructor `Eq.refl`.
- The four names must be undeclared (#14632).
- The types are built into rulean as reference terms. The exported types are compared with them, and a mismatch is a reject.
- The reduction rules are in 05.4.2.
- `Quot.sound` is an ordinary axiom from Init. rulean reports it as an axiom (P2.c).

## 06.6 Recursor generation

rulean generates, for each type of the declaration (including auxiliary nested types):

- the recursor type, with motives, minor premises with induction hypotheses, indices and the major premise;
- one rule per constructor, with `nfields` and the right-hand side;
- the K flag: true only for a single, non-mutual inductive in `Prop` with one constructor that has zero fields (`Eq` is the main case).

Then `check_recursors` type-checks the generated types and rules (#14808), in infer-only mode where the official kernel uses it.

**The generated recursor is compared with the exported one up to α-equivalence.** Binder names and binder info are not compared. Level parameter names are compared up to a consistent renaming, because later constants refer to level parameters by position.

The generated recursor still has the binder names and the binder info of the C++ kernel, because in the in-process mode (09.6) the elaborator reads them. The C++ kernel makes the name of a minor premise argument with `name::append_after`, which calls `Name.appendAfter` of Lean. rulean does the same as `Name.appendAfter` of v4.36.0. For a name without macro scopes, the suffix goes at the end of the last string part, or after the name if the last part is a number. For a hygienic name `b._@.M._hyg.N`, the suffix goes at the end of `b`, and the macro scopes stay after it. For example, `x.3` becomes `x.3._ih`, and `a._@.M._hyg.5` becomes `a_ih._@.M._hyg.5`. After the recursor type is built, rulean does what `infer_implicit(rec_ty, true)` does in `inductive.cpp`: a binder with the default binder info becomes implicit when its variable occurs in the domain of a later explicit binder, directly or through a later implicit binder. The body after the last binder does not count. In the usual case the parameters, the motives and the indices become implicit, and the minor premises and the major premise are explicit. The four quotient constants have the names and the binder info of `quot.cpp`, for example `Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)`, and each arrow has the binder name `a`.

## 06.7 Independent cross-check with ind-models

ind-models (research C§1.5) is a Lean tool by Joachim Breitner. It builds a set-theoretic model for each inductive declaration, and it rejected the bad recursors of #14613, #14616 and #14806.

rulean uses it in two ways:

1. **In the proof.** con-leche's model construction for inductive types is the L0 specification (10.2). The twin's recursor generator has a lemma that each generated rule holds in the model. This is the same obligation that con-leche discharges, so the proof can follow con-leche's.
2. **In tests.** The conformance suite (11.4) runs ind-models on every inductive declaration of the corpus and compares the result with rulean's. Inductive declarations are cheap to check, so this runs on the full Mathlib corpus in CI each night.

## 06.8 Tests that this document requires

| Group | Content |
|---|---|
| Arena `bugs/` | the 30 bug tests, all reject |
| 2026 regressions | the test of each bug-hunt PR (#14577, #14582, #14613, #14616, #14806, #14807, #14808, #14843, #14847, #16279, #16512). #13851 removed four regression tests from master. Take them from the v4.36.0 tag (A§7) |
| mutation tests | for each check in 06.2, a generator that breaks exactly that check on a valid declaration, which must then be rejected (11.5) |
| nested | `List`, `Array`, `Option`, `Prod` nesting; nesting through two levels; nesting with phantom parameters (the #14576 shape) |
| large elimination | one test for each branch of 06.4, in each profile |
| K | `Eq`, `HEq`, a K-like user type, a near miss with one field |
