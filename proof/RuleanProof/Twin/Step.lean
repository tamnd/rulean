import RuleanProof.Twin.Order

/-!
# A step on one side before the official step (spec 05.7.3, rows O8 to O11)

Rows O8, O9 and O10 of the table in spec 05.7.3 change the side that lazy delta reduces first. Row O8 unfolds the side with the smaller height when it has the other side as an argument. Row O9 reduces a neutral projection before the definition on the other side unfolds. Row O10 unfolds the other side before a binary `Nat` operation that waits. In each row, engine F does one official step on one side, and then it compares the new pair. The official order can do a different step first.

The step order of `Twin/Order.lean` alone does not show that the two orders give the same answer. Two different orders of reduction give the same answer only if the reduction is confluent. So the lemmas of this file have that hypothesis in this form: the official order decides a relation `E` (`Decides`), and the step keeps `E` (`KeepsL` and `KeepsR`). For the kernel, `E` is definitional equality, and the hypothesis is the confluence of the official rules. With this hypothesis, an answer after the step of engine F is the answer of the official order on the first pair, when the official order gives an answer on that pair.

Row O11 gives "equal" when the two sides are `x + k` and `y + k` with the same `k` and equal bases `x` and `y`. Its lemma needs two more hypotheses: `E` is an equivalence, and `E` is a congruence for applications.

As in the lemma of row O12, the lemmas do not show that the official order gives an answer. If the official order has no answer on a pair, the answer of engine F is not compared with it. This is a difference of termination, not a different answer.
-/

namespace RuleanProof.Twin

/-- The official order decides `E`: each answer that it gives is the truth value of `E` on the pair. -/
def Decides (K : Kernel) (E : Tm → Tm → Prop) : Prop :=
  ∀ n t s r, conv K n t s = some r → (r = true ↔ E t s)

/-- The step `f` on the left side keeps `E`. -/
def KeepsL (E : Tm → Tm → Prop) (f : Tm → Tm) : Prop :=
  ∀ t s, E (f t) s ↔ E t s

/-- The step `f` on the right side keeps `E`. -/
def KeepsR (E : Tm → Tm → Prop) (f : Tm → Tm) : Prop :=
  ∀ t s, E t (f s) ↔ E t s

/-- `E` is a congruence for applications. -/
def CongrApp (E : Tm → Tm → Prop) : Prop :=
  ∀ f g a b, E f g → E a b → E (.app f a) (.app g b)

/-- Two answers for two pairs where `E` has the same truth value are the same. -/
theorem answer_eq {K : Kernel} {E : Tm → Tm → Prop} (hd : Decides K E) {n m : Nat}
    {t s t' s' : Tm} {r r' : Bool} (he : E t s ↔ E t' s')
    (h : conv K n t s = some r) (h' : conv K m t' s' = some r') : r = r' := by
  have a := hd _ _ _ _ h
  have b := hd _ _ _ _ h'
  cases r <;> cases r' <;> simp_all

/-- A step on the left side: the official answer on `(f t, s)` is the official answer on `(t, s)`. -/
theorem step_left_eq {K : Kernel} {E : Tm → Tm → Prop} {f : Tm → Tm} (hd : Decides K E)
    (hf : KeepsL E f) {n m : Nat} {t s : Tm} {r r' : Bool}
    (h : conv K n (f t) s = some r) (h' : conv K m t s = some r') : r = r' :=
  answer_eq hd (hf t s) h h'

/-- A step on the right side: the official answer on `(t, f s)` is the official answer on `(t, s)`. -/
theorem step_right_eq {K : Kernel} {E : Tm → Tm → Prop} {f : Tm → Tm} (hd : Decides K E)
    (hf : KeepsR E f) {n m : Nat} {t s : Tm} {r r' : Bool}
    (h : conv K n t (f s) = some r) (h' : conv K m t s = some r') : r = r' :=
  answer_eq hd (hf t s) h h'

/-- Rows O8, O9 and O10 for a step on the left side. `rec` is the recursive call of engine F, and each answer of `rec` is an answer of the official order (`Sound`, for example `convF_conv`). If engine F does the step `f` on the left side and `rec` then gives `r`, the official order gives `r` on the first pair whenever it gives an answer. -/
theorem step_left_sound {K : Kernel} {E : Tm → Tm → Prop} {f : Tm → Tm} {rec : Proc}
    (hd : Decides K E) (hf : KeepsL E f) (hs : Sound K rec) {m : Nat} {t s : Tm}
    {r r' : Bool} (h : rec (f t) s = some r) (h' : conv K m t s = some r') : r = r' := by
  obtain ⟨n, e⟩ := hs _ _ _ h
  exact step_left_eq hd hf e h'

/-- Rows O8, O9 and O10 for a step on the right side. -/
theorem step_right_sound {K : Kernel} {E : Tm → Tm → Prop} {f : Tm → Tm} {rec : Proc}
    (hd : Decides K E) (hf : KeepsR E f) (hs : Sound K rec) {m : Nat} {t s : Tm}
    {r r' : Bool} (h : rec t (f s) = some r) (h' : conv K m t s = some r') : r = r' := by
  obtain ⟨n, e⟩ := hs _ _ _ h
  exact step_right_eq hd hf e h'

/-- Rows O8 and O10 use the delta step of the twin. If the official rules are confluent, a delta step keeps definitional equality, so `K.unfold` is a step of `KeepsL` and `KeepsR`. This lemma gives the form with `K.unfold` on the right side, which is the side that rows O8 and O10 unfold when the left side waits. -/
theorem unfold_right_sound {K : Kernel} {E : Tm → Tm → Prop} {rec : Proc}
    (hd : Decides K E) (hf : KeepsR E K.unfold) (hs : Sound K rec) {m : Nat} {t s : Tm}
    {r r' : Bool} (h : rec t (K.unfold s) = some r) (h' : conv K m t s = some r') : r = r' :=
  step_right_sound hd hf hs h h'

/-- Row O9 uses the head reduction of the twin, which has the reduction of a projection (`whnf_core`, official step 8). This lemma gives the form with `K.whnfCore` on the left side. -/
theorem whnfCore_left_sound {K : Kernel} {E : Tm → Tm → Prop} {rec : Proc}
    (hd : Decides K E) (hf : KeepsL E K.whnfCore) (hs : Sound K rec) {m : Nat} {t s : Tm}
    {r r' : Bool} (h : rec (K.whnfCore t) s = some r) (h' : conv K m t s = some r') : r = r' :=
  step_left_sound hd hf hs h h'

/-- Row O11, the offset rule. The view of `t` is `g x k`, the view of `s` is `g y k`, and the steps of the views keep `E` (`ht` and `hs`). For the kernel, `g` is `Nat.add` and `k` is a literal. If `rec` gives "equal" on the bases `x` and `y`, the official order gives "equal" on `(t, s)` whenever it gives an answer. -/
theorem offset_sound {K : Kernel} {E : Tm → Tm → Prop} {rec : Proc} (hd : Decides K E)
    (heq : Equivalence E) (hc : CongrApp E) (hs : Sound K rec) {g k x y t s : Tm} {m : Nat}
    {r' : Bool} (ht : E t (.app (.app g x) k)) (hs' : E s (.app (.app g y) k))
    (h : rec x y = some true) (h' : conv K m t s = some r') : r' = true := by
  obtain ⟨n, e⟩ := hs _ _ _ h
  have exy : E x y := (hd _ _ _ _ e).mp rfl
  have ev : E (.app (.app g x) k) (.app (.app g y) k) :=
    hc _ _ _ _ (hc _ _ _ _ (heq.refl g) exy) (heq.refl k)
  have ets : E t s := heq.trans ht (heq.trans ev (heq.symm hs'))
  exact (hd _ _ _ _ h').mpr ets

end RuleanProof.Twin
