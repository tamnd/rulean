-- The smoke test of scripts/lean-build.sh. The lean of the release and the lean with rulean as its kernel must give the same output.
import Lean
open Lean Elab Command

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
deriving Repr, BEq, Inhabited

def Tree.size {α} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

structure Point where
  x : Nat
  y : Nat
deriving Repr, DecidableEq

def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

theorem ack_pos (m n : Nat) : 0 < ack m n := by
  induction m generalizing n with
  | zero => simp [ack]
  | succ m ih => cases n <;> simp [ack, ih]

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
example : (List.range 20).foldl (· + ·) 0 = 190 := by decide
example : isEven 10 = true := by decide
theorem t1 (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

#eval ack 2 3
#eval (Tree.node .leaf 3 .leaf).size
#print axioms ack_pos

-- The kernel must reject this declaration: the value has the type Nat, and the type is Bool.
run_cmd liftTermElabM do
  let d := Declaration.defnDecl { name := `bad, levelParams := [], type := mkConst ``Bool, value := mkNatLit 1, hints := .opaque, safety := .safe }
  try addDecl d catch e => logInfo m!"rejected: {e.toMessageData}"

-- The term functions of the kernel.
run_cmd liftTermElabM do
  let env ← getEnv
  let two := mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 1)
  let r ← ofExceptKernelException (Kernel.whnf env {} two)
  let b ← ofExceptKernelException (Kernel.isDefEq env {} two (mkNatLit 2))
  logInfo m!"whnf: {r}, isDefEq: {b}"
