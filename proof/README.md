# proof

This directory is the Lean package of the rulean proofs (spec 10). It will hold the theorems T1 to T6, the Lean twin of the verified core and the Lean files that Aeneas extracts from the Rust code.

## Contents

| Module | Contents |
|---|---|
| `RuleanProof.Basic` | the link to `ConLeche.IsModel` of con-leche |
| `RuleanProof.Contracts` | the island contracts K1 to K6 of spec 10.7: K1 of `rulean-pool`, K2 of `rulean-io`, K3 of the frozen tier, K4 of the SIMD scanner, K5 of overflow and K6 of allocation failure |
| `RuleanProof.Statements` | the draft statements of the theorems T1 to T6 of spec 10.1, and the contracts K1 and K2 on the models of the two islands |
| `RuleanProof.Twin.Order` | a twin of the step order of the conversion loop, and the reordering lemmas O1, O2, O3, O5, O7 and O12 of spec 05.7.3 |
| `RuleanProof.Twin.Step` | the reordering lemmas O8, O9, O10 and O11 of spec 05.7.3, with the confluence of the official rules as a hypothesis |
| `RuleanProof.Twin.Zeta` | the reordering lemma O4 (lazy `let`) of spec 05.7.3 |

The twin of `Twin/Order.lean`, `Twin/Step.lean` and `Twin/Zeta.lean` has terms with no binders and no types. Theorem R1 must still connect it to the Aeneas model of engine F.

## Dependencies

| Package | Pin | Use |
|---|---|---|
| [con-leche](https://github.com/leanprover/con-leche) | commit `5ea446d` of 2026-11-21 | the set-theoretic model `ConLeche.IsModel` of theorem T1 (spec 10.2) |

`lean-toolchain` names the Lean release of con-leche at the pinned commit (v4.36.0). A change of the pin must change `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` in one PR.

The Aeneas Lean library comes later, together with the first extracted code. At the Aeneas commit of `flake.nix` it needs Lean v4.31.0 and Mathlib, so it must be moved to the toolchain of con-leche first, as con-ron does.

## Build

```sh
cd proof
lake build
```

The first build also builds the part of con-leche that the package imports. On an Apple M-series laptop it takes less than one minute.

## Rules

The rules of spec 10.9 apply. A proof must not contain `sorry`, `admit`, a new `axiom`, `native_decide`, `bv_decide` or `implemented_by`. `scripts/proof-rules.sh` checks the source. The `proof` CI job also checks the package with the official kernel (`scripts/leanchecker.sh`) and audits the axioms of each declaration under `RuleanProof`. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.

`leanchecker` crashes on some runs when it replays two or more modules in parallel (#15). So `scripts/leanchecker.sh` runs it once, with `--fresh`, on the root module `RuleanProof`. This replays every constant that the package imports, so it also checks con-leche and the Lean core. It takes about 2 minutes. The root module must import each module of the package, and the script fails if it does not.

con-leche is licensed under Apache-2.0. This package uses it as a dependency and copies no code from it.
