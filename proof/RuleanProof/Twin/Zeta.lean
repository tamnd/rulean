import RuleanProof.Twin.Order

/-!
# Lazy `let` (O4 of spec 05.7.3)

Engine F evaluates `let x := v; b` lazily. It puts the value of `v` in the environment of `b` and does not substitute (spec 05.4.2). The official kernel substitutes `v` for `x` in `b` (zeta). This file proves that the two give the same value for a closed `v`. The kernel substitutes only closed terms, because it opens binders with free variables first.

`eval` is a twin of `eval` of engine F on the terms of `Twin/Order.lean`. An environment is a list of values, and `bvar i` is entry `i`. A bound variable outside the environment gives the default value `dflt`, so `eval` is total. Both sides give `dflt` at the same places.
-/

namespace RuleanProof.Twin

/-- The value of a bound variable outside the environment. -/
def dflt : Tm := .fvar 0

/-- Evaluation with an environment. `letE v b` puts the value of `v` in the environment of `b`. -/
def eval (ρ : List Tm) : Tm → Tm
  | .bvar i => ρ.getD i dflt
  | .fvar x => .fvar x
  | .const c => .const c
  | .app f a => .app (eval ρ f) (eval ρ a)
  | .letE v b => eval (eval ρ v :: ρ) b

/-- The bound variables of the term are less than `n`. -/
def ClosedAt : Nat → Tm → Prop
  | n, .bvar i => i < n
  | n, .app f a => ClosedAt n f ∧ ClosedAt n a
  | n, .letE v b => ClosedAt n v ∧ ClosedAt (n + 1) b
  | _, _ => True

/-- Substitution of the closed term `v` for the bound variable `k`. The bound variables above `k` go down by one. -/
def inst (k : Nat) (v : Tm) : Tm → Tm
  | .bvar i => if i < k then .bvar i else if i = k then v else .bvar (i - 1)
  | .app f a => .app (inst k v f) (inst k v a)
  | .letE x b => .letE (inst k v x) (inst (k + 1) v b)
  | t => t

/-- The value of a term depends only on the entries of the environment that it uses. -/
theorem eval_append (t : Tm) : ∀ (ρ σ : List Tm), ClosedAt ρ.length t → eval (ρ ++ σ) t = eval ρ t := by
  induction t with
  | bvar i =>
    intro ρ σ h
    simp only [ClosedAt] at h
    simp only [eval, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  | fvar _ => intro _ _ _; rfl
  | const _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro ρ σ h
    simp only [ClosedAt] at h
    simp only [eval, ihf ρ σ h.1, iha ρ σ h.2]
  | letE v b ihv ihb =>
    intro ρ σ h
    simp only [ClosedAt] at h
    simp only [eval, ihv ρ σ h.1]
    exact ihb (eval ρ v :: ρ) σ (by simpa using h.2)

/-- A closed term has the same value in each environment. -/
theorem eval_closed {v : Tm} (hv : ClosedAt 0 v) (ρ : List Tm) : eval ρ v = eval [] v := by
  have := eval_append v [] ρ (by simpa using hv)
  simpa using this

/-- The substitution lemma: to substitute `v` for `k` is to put the value of `v` at position `k` of the environment. -/
theorem eval_inst {v : Tm} (hv : ClosedAt 0 v) (b : Tm) :
    ∀ (k : Nat) (ρ : List Tm), k ≤ ρ.length →
      eval ρ (inst k v b) = eval (ρ.take k ++ eval [] v :: ρ.drop k) b := by
  induction b with
  | bvar i =>
    intro k ρ hk
    have ht : (ρ.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
    simp only [inst]
    by_cases h1 : i < k
    · simp only [h1, ite_true, eval, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt h1]
    · by_cases h2 : i = k
      · subst h2
        simp only [h1, ite_false, ite_true, eval, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), ht, Nat.sub_self]
        simp [eval_closed hv]
      · simp only [h1, h2, ite_false, eval, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), ht]
        have e : i - k = (i - k - 1) + 1 := by omega
        rw [e, List.getElem?_cons_succ, List.getElem?_drop]
        have e2 : k + (i - k - 1) = i - 1 := by omega
        rw [e2]
  | fvar _ => intro _ _ _; rfl
  | const _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k ρ hk
    simp only [inst, eval, ihf k ρ hk, iha k ρ hk]
  | letE x b ihx ihb =>
    intro k ρ hk
    simp only [inst, eval]
    rw [ihb (k + 1) (eval ρ (inst k v x) :: ρ) (by simpa using hk), ihx k ρ hk]
    simp

/-- O4: a lazy `let` gives the value of the official substitution, for a closed value. -/
theorem zeta_lazy {v : Tm} (hv : ClosedAt 0 v) (b : Tm) (ρ : List Tm) :
    eval ρ (.letE v b) = eval ρ (inst 0 v b) := by
  rw [eval_inst hv b 0 ρ (Nat.zero_le _)]
  simp [eval, eval_closed hv ρ]

end RuleanProof.Twin
