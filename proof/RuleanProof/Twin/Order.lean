/-!
# The order of the conversion steps (spec 05.7.3)

This file is a twin of the conversion loop of A§1.8 at the level of its step order. It has the quick check, the head reduction without delta (`whnf_core`), lazy delta with heights and the congruence of applications. It proves the reordering lemmas O1, O2, O3, O5 and O7 of the table in spec 05.7.3. Lemma O4 is in `Twin/Zeta.lean`.

The twin is a model, not the Aeneas model of the Rust code. The terms have no binders and no types, and `whnf_core` is a parameter. The lemmas show that each reordering of engine F gives the answer of the official order on this model. The link to the Rust code comes with the Aeneas model (spec 10.4.1).

A procedure has fuel. The value `none` means "no answer with this fuel". The official procedure `conv` gives the same answer with more fuel (`conv_mono_le`), so two runs that give an answer give the same answer (`conv_det`).

The main theorem is `convF_conv`. If engine F gives the answer `r` and each entry of its cache is a true judgment, then the official order gives `r` with some fuel.
-/

namespace RuleanProof.Twin

/-- The terms of the twin. `bvar` and `letE` are used only by `Twin/Zeta.lean`. -/
inductive Tm where
  | bvar (i : Nat)
  | fvar (x : Nat)
  | const (c : Nat)
  | app (f a : Tm)
  | letE (v b : Tm)
  deriving DecidableEq, Repr

/-- The data of the kernel that the step order uses. -/
structure Kernel where
  /-- The height and the value of each definition. A constant with `none` is not a definition. -/
  defs : Nat → Option (Nat × Tm)
  /-- Head reduction without delta (`whnf_core`). -/
  whnfCore : Tm → Tm

/-- The constant at the head of a term, if any. -/
def headConst : Tm → Option Nat
  | .const c => some c
  | .app f _ => headConst f
  | _ => none

/-- The height of the definition at the head of a term, if the head is a definition. -/
def Kernel.height (K : Kernel) (t : Tm) : Option Nat :=
  match headConst t with
  | some c => (K.defs c).map Prod.fst
  | none => none

/-- One delta step: the definition at the head is replaced by its value. -/
def Kernel.unfold (K : Kernel) : Tm → Tm
  | .const c =>
    match K.defs c with
    | some d => d.2
    | none => .const c
  | .app f a => .app (K.unfold f) a
  | t => t

/-- A procedure for one query: `some true` is "equal", `some false` is "not equal" and `none` is "no answer". -/
abbrev Proc := Tm → Tm → Option Bool

/-- Congruence of applications (A§1.8 step 9). `rec` is the recursive call. -/
def congr (rec : Proc) : Tm → Tm → Option Bool
  | .app f a, .app g b =>
    match rec f g with
    | some true => rec a b
    | r => r
  | t, s => some (decide (t = s))

/-- Lazy delta (A§1.8 step 5). Unfold the side with the greater height. If the heights are equal and the heads are the same, compare the arguments first. If that fails, unfold both sides. -/
def lazyDelta (K : Kernel) (rec : Proc) (t s : Tm) : Option Bool :=
  match K.height t, K.height s with
  | none, none => congr rec t s
  | some _, none => rec (K.unfold t) s
  | none, some _ => rec t (K.unfold s)
  | some a, some b =>
    if a < b then rec t (K.unfold s)
    else if b < a then rec (K.unfold t) s
    else if headConst t = headConst s then
      match congr rec t s with
      | some true => some true
      | some false => rec (K.unfold t) (K.unfold s)
      | none => none
    else rec (K.unfold t) (K.unfold s)

/-- One step of the official order: the quick check, then `whnf_core`, then lazy delta. -/
def offStep (K : Kernel) (rec : Proc) (t s : Tm) : Option Bool :=
  if t = s then some true
  else lazyDelta K rec (K.whnfCore t) (K.whnfCore s)

/-- The official order with fuel `n`. -/
def conv (K : Kernel) : Nat → Proc
  | 0, _, _ => none
  | n + 1, t, s => offStep K (conv K n) t s

/-- `rec'` gives each answer that `rec` gives. -/
def Ext (rec rec' : Proc) : Prop :=
  ∀ a b r, rec a b = some r → rec' a b = some r

theorem congr_ext {rec rec' : Proc} (e : Ext rec rec') {t s : Tm} {r : Bool}
    (h : congr rec t s = some r) : congr rec' t s = some r := by
  match t, s with
  | .app f a, .app g b =>
    simp only [congr] at h ⊢
    cases h1 : rec f g with
    | none => simp [h1] at h
    | some x =>
      rw [e _ _ _ h1]
      cases x with
      | true => simp only [h1] at h; exact e _ _ _ h
      | false => simpa [h1] using h
  | .bvar _, _ | .fvar _, _ | .const _, _ | .letE _ _, _ => simpa [congr] using h
  | .app _ _, .bvar _ | .app _ _, .fvar _ | .app _ _, .const _ | .app _ _, .letE _ _ =>
    simpa [congr] using h

theorem lazyDelta_ext {K : Kernel} {rec rec' : Proc} (e : Ext rec rec') {t s : Tm} {r : Bool}
    (h : lazyDelta K rec t s = some r) : lazyDelta K rec' t s = some r := by
  unfold lazyDelta at h ⊢
  split at h
  · exact congr_ext e h
  · exact e _ _ _ h
  · exact e _ _ _ h
  · rename_i a b _ _
    by_cases hab : a < b
    · simp only [hab, ite_true] at h ⊢; exact e _ _ _ h
    · by_cases hba : b < a
      · simp only [hab, hba, ite_true, ite_false] at h ⊢; exact e _ _ _ h
      · simp only [hab, hba, ite_false] at h ⊢
        by_cases hh : headConst t = headConst s
        · simp only [hh, ite_true] at h ⊢
          cases hc : congr rec t s with
          | none => simp [hc] at h
          | some x =>
            rw [congr_ext e hc]
            cases x with
            | true => simpa [hc] using h
            | false => simp only [hc] at h; exact e _ _ _ h
        · simp only [hh, ite_false] at h ⊢; exact e _ _ _ h

theorem offStep_ext {K : Kernel} {rec rec' : Proc} (e : Ext rec rec') {t s : Tm} {r : Bool}
    (h : offStep K rec t s = some r) : offStep K rec' t s = some r := by
  unfold offStep at h ⊢
  by_cases hts : t = s
  · simpa [hts] using h
  · simp only [hts, ite_false] at h ⊢; exact lazyDelta_ext e h

/-- More fuel keeps an answer. -/
theorem conv_mono (K : Kernel) : ∀ n, Ext (conv K n) (conv K (n + 1))
  | 0 => fun _ _ _ h => by simp [conv] at h
  | n + 1 => fun _ _ _ h => by
    simp only [conv] at h ⊢
    exact offStep_ext (conv_mono K n) h

theorem conv_mono_le (K : Kernel) {n m : Nat} (hnm : n ≤ m) : Ext (conv K n) (conv K m) := by
  induction hnm with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun a b r h => conv_mono K _ a b r (ih a b r h)

/-- Two runs of the official order that give an answer give the same answer. -/
theorem conv_det {K : Kernel} {n m : Nat} {t s : Tm} {r r' : Bool}
    (h : conv K n t s = some r) (h' : conv K m t s = some r') : r = r' := by
  have a := conv_mono_le K (Nat.le_max_left n m) t s r h
  have b := conv_mono_le K (Nat.le_max_right n m) t s r' h'
  rw [a] at b
  exact Option.some.inj b

/-- Each answer of `rec` is an answer of the official order with some fuel. -/
def Sound (K : Kernel) (rec : Proc) : Prop :=
  ∀ a b r, rec a b = some r → ∃ n, conv K n a b = some r

theorem congr_sound {K : Kernel} {rec : Proc} (hs : Sound K rec) {t s : Tm} {r : Bool}
    (h : congr rec t s = some r) : ∃ n, congr (conv K n) t s = some r := by
  match t, s with
  | .app f a, .app g b =>
    simp only [congr] at h
    cases h1 : rec f g with
    | none => simp [h1] at h
    | some x =>
      cases x with
      | true =>
        simp only [h1] at h
        obtain ⟨n1, e1⟩ := hs _ _ _ h1
        obtain ⟨n2, e2⟩ := hs _ _ _ h
        refine ⟨max n1 n2, ?_⟩
        simp only [congr]
        rw [conv_mono_le K (Nat.le_max_left n1 n2) _ _ _ e1]
        exact conv_mono_le K (Nat.le_max_right n1 n2) _ _ _ e2
      | false =>
        simp only [h1] at h
        obtain ⟨n1, e1⟩ := hs _ _ _ h1
        refine ⟨n1, ?_⟩
        simp only [congr, e1]
        exact h
  | .bvar _, _ | .fvar _, _ | .const _, _ | .letE _ _, _ => exact ⟨0, by simpa [congr] using h⟩
  | .app _ _, .bvar _ | .app _ _, .fvar _ | .app _ _, .const _ | .app _ _, .letE _ _ =>
    exact ⟨0, by simpa [congr] using h⟩

theorem lazyDelta_sound {K : Kernel} {rec : Proc} (hs : Sound K rec) {t s : Tm} {r : Bool}
    (h : lazyDelta K rec t s = some r) : ∃ n, lazyDelta K (conv K n) t s = some r := by
  have one : ∀ {x y}, rec x y = some r → ∃ n, conv K n x y = some r := fun e => hs _ _ _ e
  unfold lazyDelta at h ⊢
  cases h1 : K.height t with
  | none =>
    cases h2 : K.height s with
    | none =>
      simp only [h1, h2] at h ⊢
      exact congr_sound hs h
    | some b =>
      simp only [h1, h2] at h ⊢
      exact one h
  | some a =>
    cases h2 : K.height s with
    | none =>
      simp only [h1, h2] at h ⊢
      exact one h
    | some b =>
      simp only [h1, h2] at h ⊢
      by_cases hab : a < b
      · simp only [hab, ite_true] at h ⊢
        exact one h
      · by_cases hba : b < a
        · simp only [hab, hba, ite_true, ite_false] at h ⊢
          exact one h
        · simp only [hab, hba, ite_false] at h ⊢
          by_cases hh : headConst t = headConst s
          · simp only [hh, ite_true] at h ⊢
            cases hc : congr rec t s with
            | none => simp [hc] at h
            | some x =>
              obtain ⟨n1, e1⟩ := congr_sound hs hc
              cases x with
              | true =>
                simp only [hc] at h
                exact ⟨n1, by simp only [e1]; exact h⟩
              | false =>
                simp only [hc] at h
                obtain ⟨n2, e2⟩ := one h
                refine ⟨max n1 n2, ?_⟩
                have c1 := congr_ext (conv_mono_le K (Nat.le_max_left n1 n2)) e1
                simp only [c1]
                exact conv_mono_le K (Nat.le_max_right n1 n2) _ _ _ e2
          · simp only [hh, ite_false] at h ⊢
            exact one h

theorem offStep_sound {K : Kernel} {rec : Proc} (hs : Sound K rec) {t s : Tm} {r : Bool}
    (h : offStep K rec t s = some r) : ∃ n, conv K n t s = some r := by
  unfold offStep at h
  by_cases hts : t = s
  · simp only [hts, ite_true] at h
    subst hts
    exact ⟨1, by simp [conv, offStep, ← h]⟩
  · simp only [hts, ite_false] at h
    obtain ⟨n, e⟩ := lazyDelta_sound hs h
    exact ⟨n + 1, by simp only [conv, offStep, hts, ite_false]; exact e⟩

/-! ## Engine F -/

/-- Each entry of the cache is a true judgment: the official order gives "equal" with some fuel (spec 10.4.3). -/
def CacheTrue (K : Kernel) (C : Tm → Tm → Bool) : Prop :=
  ∀ a b, C a b = true → ∃ n, conv K n a b = some true

/-- Lazy delta of engine F. If the heads are the same definition, F compares the folded forms first, before it looks at the heights (O1). If that fails, it unfolds both sides (O5). Otherwise it uses the official lazy delta. -/
def lazyDeltaF (K : Kernel) (rec : Proc) (t s : Tm) : Option Bool :=
  if headConst t = headConst s ∧ (K.height t).isSome then
    match congr rec t s with
    | some true => some true
    | some false => rec (K.unfold t) (K.unfold s)
    | none => none
  else lazyDelta K rec t s

/-- `whnf_core` in engine F. It skips the call when both sides are already in head normal form (O3). -/
def whnfCoreF (K : Kernel) (t s : Tm) : Tm × Tm :=
  if K.whnfCore t = t ∧ K.whnfCore s = s then (t, s) else (K.whnfCore t, K.whnfCore s)

/-- One step of engine F: a cached success first (O2), then the quick check, `whnf_core` (O3) and lazy delta (O1, O5). -/
def fStep (K : Kernel) (C : Tm → Tm → Bool) (rec : Proc) (t s : Tm) : Option Bool :=
  if C t s then some true
  else if t = s then some true
  else
    let p := whnfCoreF K t s
    lazyDeltaF K rec p.1 p.2

/-- Engine F with fuel `n` and the cache `C`. -/
def convF (K : Kernel) (C : Tm → Tm → Bool) : Nat → Proc
  | 0, _, _ => none
  | n + 1, t, s => fStep K C (convF K C n) t s

/-- The height depends only on the head constant. -/
theorem height_of_head {K : Kernel} {t s : Tm} (h : headConst t = headConst s) :
    K.height t = K.height s := by
  simp only [Kernel.height, h]

/-- O1: compare glued folded forms before forcing. When the heads are the same definition, the comparison of the folded forms is the official step 5. -/
theorem conv_glued_eq_lazyDelta (K : Kernel) (rec : Proc) (t s : Tm) :
    lazyDeltaF K rec t s = lazyDelta K rec t s := by
  unfold lazyDeltaF
  by_cases hc : headConst t = headConst s ∧ (K.height t).isSome
  · obtain ⟨hh, hs⟩ := hc
    simp only [hh, hs, and_self, ite_true]
    have e := height_of_head (K := K) hh
    cases ht : K.height t with
    | none => simp [ht] at hs
    | some a =>
      have es : K.height s = some a := by rw [← e, ht]
      unfold lazyDelta
      simp only [ht, es, Nat.lt_irrefl, ite_false, hh, ite_true]
  · simp only [hc, ite_false]

/-- O5: when the heights are equal and the heads are not the same, the official step 5 unfolds both sides at once. -/
theorem lazyDelta_equal_height (K : Kernel) (rec : Proc) (t s : Tm) (a : Nat)
    (ht : K.height t = some a) (hs : K.height s = some a) (hh : headConst t ≠ headConst s) :
    lazyDelta K rec t s = rec (K.unfold t) (K.unfold s) := by
  unfold lazyDelta
  simp only [ht, hs, Nat.lt_irrefl, ite_false, hh]

/-- O3: `whnf_core` is the identity on terms in head normal form, so to skip it gives the same terms. -/
theorem force_core_idem (K : Kernel) (t s : Tm) :
    whnfCoreF K t s = (K.whnfCore t, K.whnfCore s) := by
  unfold whnfCoreF
  by_cases h : K.whnfCore t = t ∧ K.whnfCore s = s
  · obtain ⟨h1, h2⟩ := h
    simp [h1, h2]
  · simp only [h, ite_false]

/-- Without a cache hit, a step of engine F is a step of the official order. -/
theorem fStep_eq_offStep (K : Kernel) (C : Tm → Tm → Bool) (rec : Proc) (t s : Tm)
    (hc : C t s = false) : fStep K C rec t s = offStep K rec t s := by
  unfold fStep offStep
  simp only [hc, Bool.false_eq_true, ite_false, force_core_idem, conv_glued_eq_lazyDelta]

/-- O2: a cache whose entries are true judgments gives only answers of the official order. -/
theorem cache_true {K : Kernel} {C : Tm → Tm → Bool} (hC : CacheTrue K C) {t s : Tm}
    (h : C t s = true) : ∃ n, conv K n t s = some true :=
  hC t s h

/-- O7: a term is equal to itself at the start of a step. This is the quick check of the official step 1. Engine F uses it on two values of the same form (`same_value`). -/
theorem same_true (K : Kernel) (t : Tm) : conv K 1 t t = some true := by
  simp [conv, offStep]

/-- Congruence gives "equal" on a term and itself. -/
theorem congr_same (K : Kernel) (t : Tm) : congr (conv K 1) t t = some true := by
  cases t <;> simp [congr, same_true]

/-- O7 inside lazy delta: on a term and itself, lazy delta gives "equal". Engine F stops lazy delta when both sides have the same form, so its answer is the answer of the official order. -/
theorem lazyDelta_same (K : Kernel) (t : Tm) : lazyDelta K (conv K 1) t t = some true := by
  unfold lazyDelta
  cases h : K.height t with
  | none => simp [congr_same]
  | some a => simp [congr_same]

/-- The main theorem: each answer of engine F is an answer of the official order. -/
theorem convF_conv {K : Kernel} {C : Tm → Tm → Bool} (hC : CacheTrue K C) :
    ∀ n, Sound K (convF K C n)
  | 0 => fun _ _ _ h => by simp [convF] at h
  | n + 1 => fun t s r h => by
    simp only [convF] at h
    cases hc : C t s with
    | true =>
      unfold fStep at h
      simp only [hc, ite_true] at h
      rw [← h]
      exact cache_true hC hc
    | false =>
      rw [fStep_eq_offStep K C _ t s hc] at h
      exact offStep_sound (convF_conv hC n) h

/-- Engine F and the official order give the same answer when both give one. -/
theorem convF_agrees {K : Kernel} {C : Tm → Tm → Bool} (hC : CacheTrue K C) {n m : Nat}
    {t s : Tm} {r r' : Bool} (h : convF K C n t s = some r) (h' : conv K m t s = some r') :
    r = r' := by
  obtain ⟨k, e⟩ := convF_conv hC n t s r h
  exact conv_det e h'

/-- An entry that engine F adds to the cache after an "equal" answer keeps `CacheTrue`. -/
theorem cacheTrue_insert {K : Kernel} {C : Tm → Tm → Bool} (hC : CacheTrue K C) {n : Nat}
    {t s : Tm} (h : convF K C n t s = some true) :
    CacheTrue K (fun a b => C a b || (decide (a = t) && decide (b = s))) := by
  intro a b hab
  by_cases e : a = t ∧ b = s
  · obtain ⟨rfl, rfl⟩ := e
    exact convF_conv hC n a b true h
  · have : C a b = true := by
      cases hca : C a b with
      | true => rfl
      | false =>
        simp only [hca, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hab
        exact absurd hab e
    exact hC a b this

end RuleanProof.Twin
