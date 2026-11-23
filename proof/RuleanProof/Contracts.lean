/-!
# The island contracts

Spec 10.7 gives one contract for each island. Each contract is discharged outside Lean, and the capstone theorem takes it as a hypothesis. This file states the contracts K1 and K2. K3 and K4 have no statement here: K3 follows from the Rust type system and the subset lint, and K4 holds because rulean has no SIMD scanner (spec 10.7.1). `Statements.lean` defines `Interface.K1` and `Interface.K2` with the statements of this file, on the models `runAll` and `readInput` of the two islands. K5 and K6 are properties of the build profile, and CI checks them (spec 10.7).

## K1, the thread pool

The island is the crate `rulean-pool`. Its function `run_all` runs `n` jobs on a set of threads and gives an array with the result of job `k` at position `k`. The contract says that this array is the array of the sequential twin, in which job `k` gives `f k`.

A Verus proof discharges the safety part of K1: if `run_all` returns, its result satisfies `ParallelAll`. The proof is in `proof/verus/pool.rs`. It holds for each value of the shared counter, so it holds for each schedule of the threads. It does not show that `run_all` returns. The test `each_claim_order_runs_each_job_once` gives the worker each order of the claims of at most 3 workers on at most 5 jobs, and it checks that each job runs exactly once and that each worker stops. Review covers larger cases.

## K2, the file read

The island is the crate `rulean-io`. A run reads the input file once, and the core gets the bytes that it reads. The model of the file system is a function from a path to the content of the file at that path, at one time. The contract says that the bytes are the content of the file at open time.

Review discharges K2. Two checks at run time support the review. The file is opened read-only, and the report gives the SHA-256 digest of the bytes that the core got. After the run, `rulean-io` reads the file again. If the digest is not the same, the run gives the input error and no verdict.
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

end RuleanProof.Contracts
