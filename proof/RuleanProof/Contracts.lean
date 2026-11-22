/-!
# The island contracts

Spec 10.7 gives one contract for each island. Each contract is discharged outside Lean, and the capstone theorem takes it as a hypothesis. This file states the contracts that have an island in the code. The fields `K1` to `K6` of `Interface` in `Statements.lean` are still free propositions. A later PR sets each field to the statement of this file.

## K2, the file read

The island is the crate `rulean-io`. A run reads the input file once, and the core gets the bytes that it reads. The model of the file system is a function from a path to the content of the file at that path, at one time. The contract says that the bytes are the content of the file at open time.

Review discharges K2. Two checks at run time support the review. The file is opened read-only, and the report gives the SHA-256 digest of the bytes that the core got. After the run, `rulean-io` reads the file again. If the digest is not the same, the run gives the input error and no verdict.
-/

namespace RuleanProof.Contracts

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
