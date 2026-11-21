import ConLeche.IsModel

/-!
# The link to con-leche

Theorem T1 of spec 10.2 says that each environment that rulean accepts has a model in `SetTheory V`. The notion of a model is `ConLeche.IsModel`. This file names it in the namespace of rulean, so that `Statements.lean` can use it, and so that a change of the con-leche pin that removes it breaks the build.
-/

namespace RuleanProof

universe w

/-- A model of the constants `C` in the set theory `V`, as con-leche defines it. -/
abbrev IsModel (V : Type w) [ConLeche.SetTheory V] (model : ConLeche.Name → List Nat → V)
    (C : ConLeche.ConstantInfo → Prop) : Prop :=
  ConLeche.IsModel V model C

end RuleanProof
