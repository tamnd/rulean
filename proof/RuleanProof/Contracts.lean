/-!
# The island contracts

Spec 10.7 gives one contract for each island. Each contract is discharged outside Lean. This file states the six contracts K1 to K6, each with a small theorem that shows how the proof uses it. `Statements.lean` defines `Interface.K1` and `Interface.K2` with the statements of this file, on the models `runAll` and `readInput` of the two islands, and the theorems T1, T2 and T5 take them as hypotheses. K3 to K6 are not hypotheses of a theorem yet, because the Aeneas model of the core does not have the objects that they talk about (spec 10.7.1).

## K1, the thread pool

The island is the crate `rulean-pool`. Its function `run_all` runs `n` jobs on a set of threads and gives an array with the result of job `k` at position `k`. The contract says that this array is the array of the sequential twin, in which job `k` gives `f k`.

A Verus proof discharges the safety part of K1: if `run_all` returns, its result satisfies `ParallelAll`. The proof is in `proof/verus/pool.rs`. It holds for each value of the shared counter, so it holds for each schedule of the threads. It does not show that `run_all` returns. The test `each_claim_order_runs_each_job_once` gives the worker each order of the claims of at most 3 workers on at most 5 jobs, and it checks that each job runs exactly once and that each worker stops. Review covers larger cases.

## K2, the file read

The island is the crate `rulean-io`. A run reads the input file once, and the core gets the bytes that it reads. The model of the file system is a function from a path to the content of the file at that path, at one time. The contract says that the bytes are the content of the file at open time.

Review discharges K2. Two checks at run time support the review. The file is opened read-only, and the report gives the SHA-256 digest of the bytes that the core got. After the run, `rulean-io` reads the file again. If the digest is not the same, the run gives the input error and no verdict.

## K3, the frozen tier

A worker of the parallel stage reads the store of the main checker and does not change it. The model of a worker is a function from the shared store to the store after the run and a result. The contract says that the store after the run is the store before the run. The Rust type system and the subset lint discharge K3: each worker gets the main store through a shared reference, and the core crates have no type with interior mutability (spec 10.7.1).

## K4, the SIMD scanner

The optional island `rulean-simd` scans the lines of an NDJSON input. The contract says that it gives the same result as the scanner of the verified core on each input. rulean has no SIMD scanner now, so the scanner of the core is the only scanner, and the contract holds by `scanAgrees_self`.

## K5, overflow

Each arithmetic operation of the core on machine integers is checked, because the build profile has `overflow-checks` on. The model of a checked operation gives `none` for a panic. The contract says that a result that is not a panic is the result of the operation on natural numbers. The theorem `noWrap_checkedAdd` shows that the model of a checked addition on `UInt64` satisfies the contract. CI checks the build profile (spec 13.4).

## K6, allocation failure

An allocation succeeds or the process stops. The model of a run is an outcome that is a value or a stop. The contract says that the run gives the value of the twin, or it stops. With `panic = "abort"`, a stop gives no report, so the user cannot see a partial result. The theorem `allOrNothing_observe` shows that each result that the user can see is the result of the twin.
-/

namespace RuleanProof.Contracts

/-- **Contract K1.** `out` has `n` values, and the value at each job index `i < n` is `f i`, the result of job `i` in the sequential twin. -/
def ParallelAll {α : Type} (n : Nat) (f : Nat → α) (out : Array α) : Prop :=
  out.size = n ∧ ∀ (i : Nat) (h : i < out.size), out[i] = f i

/-- The sequential twin satisfies K1: it computes job `i` at position `i`. -/
theorem parallelAll_ofFn {α : Type} (n : Nat) (f : Nat → α) :
    ParallelAll n f (Array.ofFn fun (i : Fin n) => f i) := by
  refine ⟨Array.size_ofFn, ?_⟩
  intro i h
  simp

/-- Two arrays that satisfy K1 for the same jobs are equal. So the result does not depend on the thread count or the schedule (theorem T5). -/
theorem parallelAll_unique {α : Type} {n : Nat} {f : Nat → α} {a b : Array α}
    (ha : ParallelAll n f a) (hb : ParallelAll n f b) : a = b := by
  apply Array.ext
  · rw [ha.1, hb.1]
  · intro i h1 h2
    rw [ha.2 i h1, hb.2 i h2]

/-- The file system at one time: the content of each path that is a regular file. A path with no regular file gives `none`. -/
abbrev FileSystem := String → Option ByteArray

/-- **Contract K2.** `bytes`, the byte array that the core gets, is the content of the file at `path` in the file system `fs` at open time. -/
def ReadsAs (fs : FileSystem) (path : String) (bytes : ByteArray) : Prop :=
  fs path = some bytes

/-- The check after the run. If the file system at the end has the same content at `path` as the bytes that the core got, and the file was not changed between the open and the end, then the contract holds at open time. The second hypothesis is the part that review discharges, because the check after the run cannot see a change that was made and then undone. -/
theorem readsAs_of_same (start finish : FileSystem) (path : String) (bytes : ByteArray)
    (hend : finish path = some bytes) (hsame : start path = finish path) :
    ReadsAs start path bytes := by
  unfold ReadsAs
  rw [hsame]
  exact hend

/-- **Contract K3.** A worker leaves the shared store as it was. `run s` gives the store after the run and the result of the worker. -/
def Frozen {σ β : Type} (run : σ → σ × β) : Prop :=
  ∀ s, (run s).1 = s

/-- Under K3, the second of two workers sees the store that the first worker saw, so its result does not depend on the order of the two workers. -/
theorem frozen_seq {σ β γ : Type} {r₁ : σ → σ × β} {r₂ : σ → σ × γ}
    (h₁ : Frozen r₁) (h₂ : Frozen r₂) (s : σ) :
    (r₂ (r₁ s).1).1 = s ∧ (r₂ (r₁ s).1).2 = (r₂ s).2 := by
  rw [h₁ s]
  exact ⟨h₂ s, rfl⟩

/-- **Contract K4.** The SIMD scanner `simd` and the scanner `ref` of the verified core give the same result on each input. -/
def ScanAgrees {α : Type} (simd ref : ByteArray → α) : Prop :=
  ∀ b, simd b = ref b

/-- With no SIMD scanner, the core uses its own scanner, and K4 holds. -/
theorem scanAgrees_self {α : Type} (ref : ByteArray → α) : ScanAgrees ref ref :=
  fun _ => rfl

/-- **Contract K5.** The checked operation `op` either panics (`none`) or gives the result of `f` on natural numbers. -/
def NoWrap (op : UInt64 → UInt64 → Option UInt64) (f : Nat → Nat → Nat) : Prop :=
  ∀ a b r, op a b = some r → r.toNat = f a.toNat b.toNat

/-- The model of an addition with `overflow-checks` on: a sum that does not fit is a panic. -/
def checkedAdd (a b : UInt64) : Option UInt64 :=
  if a.toNat + b.toNat < 2 ^ 64 then some (a + b) else none

/-- The checked addition satisfies K5. -/
theorem noWrap_checkedAdd : NoWrap checkedAdd (· + ·) := by
  intro a b r h
  unfold checkedAdd at h
  split at h
  · rename_i hlt
    cases h
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt]
  · cases h

/-- The outcome of a run: a value, or a stop of the process. -/
inductive Outcome (α : Type) where
  | done (a : α)
  | abort

/-- What the user sees: the value of a run that ends, and nothing for a stop. -/
def Outcome.observe {α : Type} : Outcome α → Option α
  | .done a => some a
  | .abort => none

/-- **Contract K6.** The run gives the value `a` of the twin, or it stops. -/
def AllOrNothing {α : Type} (run : Outcome α) (a : α) : Prop :=
  run = .done a ∨ run = .abort

/-- Under K6, each value that the user sees is the value of the twin. -/
theorem allOrNothing_observe {α : Type} {run : Outcome α} {a x : α}
    (h : AllOrNothing run a) (hx : run.observe = some x) : x = a := by
  rcases h with h | h <;> subst h <;> simp [Outcome.observe] at hx
  exact hx.symm

end RuleanProof.Contracts
