import RuleanProof.Basic
import RuleanProof.Contracts

/-!
# The statements of the theorems T1 to T6

This file states the theorems of spec 10.1. It is a protected file (spec 10.9). A change needs the approval of two maintainers.

This is a draft. Most objects that the theorems talk about do not exist yet. The Aeneas model of `rulean_core::check_stream` and the specification of the input format come in later milestones. So the draft collects these objects in the structure `Interface`, and each theorem is a `Prop` over an `Interface`. A later PR replaces each field of `Interface` with the real definition, and then each `Prop` becomes a `theorem`.

The island contracts K1 and K2 are not fields. They are the definitions `Interface.K1` and `Interface.K2` below, and they use the statements of `Contracts.lean` on the models of the two islands. K3 to K6 are not hypotheses of a theorem (spec 10.7.1).

The draft has no proofs, so it has no holes. It only shows that the statements are well formed, and it gives a person one place to read them.

The notions of a model, a constant and a declaration are those of con-leche (spec 10.2). They are not part of `Interface`.
-/

namespace RuleanProof

open ConLeche

universe w

/-- The verdict of rulean on a declaration or on an environment (spec 09.3). -/
inductive Verdict where
  | accept
  | reject
  | decline
  deriving DecidableEq, Repr

/-- An environment, split in two tiers (spec 05.10). The safe tier has the constants of safe declarations. The quarantine tier has the `unsafe` and `partial` ones. -/
structure Env where
  safe : ConstantInfo → Prop
  quarantine : ConstantInfo → Prop

/-- The objects that the statements talk about, before they are written. -/
structure Interface where
  /-- The state of the checker between two calls: the stores, the caches and the session. -/
  State : Type
  /-- The report of one run (spec 09.4). -/
  Report : Type
  /-- The error of one run, for example a malformed input or a resource limit. -/
  Error : Type
  /-- The Aeneas model of `rulean_core::check_stream`, run with one thread. -/
  checkStream : State → ByteArray → Except Error (Report × State)
  /-- The same function with `threads` worker threads and the schedule `sched` of the pool. -/
  checkStreamPar : (threads : Nat) → (sched : Nat → Nat) → State → ByteArray → Except Error (Report × State)
  /-- The verdict of a report. -/
  verdict : Report → Verdict
  /-- The axioms that the report gives for the theorem `n`, if `n` is an accepted theorem (spec 09.4, P2.c). -/
  reportedAxioms : Report → Name → Option (List Name)
  /-- `Spec.parseStream`: the specification of the lean4export 3.x format and of the `.rlb` format (spec 07). -/
  parseStream : ByteArray → Option (List Declaration)
  /-- `Spec.Elab`: the declarations make the environment, with the recursors that rulean makes (spec 10.1). -/
  elaborates : List Declaration → Env → Prop
  /-- The axioms that the constant `n` of the environment depends on, through the types and values of other constants. -/
  axiomsOf : Env → Name → List Name
  /-- The constant `c` refers to the constant named `n` in its type or its value. -/
  refersTo : ConstantInfo → Name → Prop
  /-- The result of one job of the parallel stage (spec 08.3). -/
  JobResult : Type
  /-- The model of `rulean_pool::run_all`: with `threads` worker threads and the schedule `sched`, it runs the jobs `0` to `n - 1`, where job `k` gives `f k`, and it gives the array of the results. -/
  runAll : (threads : Nat) → (sched : Nat → Nat) → (n : Nat) → (Nat → JobResult) → Array JobResult
  /-- The model of the read of the input by `rulean-io`: the bytes that the core gets from the file at `path`, in the file system `fs` at open time, or an error. -/
  readInput : Contracts.FileSystem → (path : String) → Except Error ByteArray
  /-- The declaration `d` is accepted by lean4lean within the fuel `fuel` (spec 10.11). -/
  lean4leanAccepts : Declaration → (fuel : Nat) → Prop
  /-- The run is within the resource limits of spec 05.11 for the fuel `fuel`. -/
  withinLimits : Declaration → (fuel : Nat) → Prop

/-- **Contract K1** of the thread pool (spec 10.7). For each thread count, each schedule and each set of jobs, the array of `runAll` is the array of the sequential twin. -/
def Interface.K1 (I : Interface) : Prop :=
  ∀ (threads : Nat) (sched : Nat → Nat) (n : Nat) (f : Nat → I.JobResult),
    0 < threads → Contracts.ParallelAll n f (I.runAll threads sched n f)

/-- **Contract K2** of the file read (spec 10.7). If the read gives bytes, they are the content of the file at open time. -/
def Interface.K2 (I : Interface) : Prop :=
  ∀ (fs : Contracts.FileSystem) (path : String) (bytes : ByteArray),
    I.readInput fs path = .ok bytes → Contracts.ReadsAs fs path bytes

/-- Under K1, two runs of the pool on the same jobs give the same array, for each thread count and each schedule. This is the part of theorem T5 that is about the pool. -/
theorem Interface.runAll_eq (I : Interface) (hk : I.K1) {t₁ t₂ : Nat} (s₁ s₂ : Nat → Nat)
    (n : Nat) (f : Nat → I.JobResult) (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    I.runAll t₁ s₁ n f = I.runAll t₂ s₂ n f :=
  Contracts.parallelAll_unique (hk t₁ s₁ n f h₁) (hk t₂ s₂ n f h₂)

/-- The name `a.b.c` from its parts. -/
def mkName (parts : List String) : Name :=
  parts.foldl Name.str Name.anonymous

/-- The three standard axioms: `propext`, `Quot.sound` and `Classical.choice`. -/
def std3 : List Name :=
  [mkName ["propext"], mkName ["Quot", "sound"], mkName ["Classical", "choice"]]

/-- rulean accepts the input `b`, and `env` is the environment of the declarations of `b`. -/
def Accepted (I : Interface) (b : ByteArray) (env : Env) : Prop :=
  ∃ st₀ st₁ r ds, I.checkStream st₀ b = .ok (r, st₁) ∧ I.verdict r = .accept ∧
    I.parseStream b = some ds ∧ I.elaborates ds env

/-- A constant named `n` is reached from `c` through the references of constants of `C`. -/
inductive Reaches (I : Interface) (C : ConstantInfo → Prop) : ConstantInfo → Name → Prop where
  | direct {c n} : I.refersTo c n → Reaches I C c n
  | step {c d n} : I.refersTo c d.name → C d → Reaches I C d n → Reaches I C c n

/-- **T1, soundness of the stream checker.** If rulean accepts the input `b`, then `b` is a list of declarations, the declarations make an environment, and the safe tier of that environment has a model in each set theory `V`. Required for 1.0. -/
def T1 (I : Interface) : Prop :=
  ∀ (V : Type w) [SetTheory V] (st₀ st₁ : I.State) (b : ByteArray) (r : I.Report),
    I.K1 → I.K2 →
    I.checkStream st₀ b = .ok (r, st₁) → I.verdict r = .accept →
    ∃ ds, I.parseStream b = some ds ∧
      ∃ env, I.elaborates ds env ∧ ∃ model : Name → List Nat → V, IsModel V model env.safe

/-- **T2, no proof of `False`.** No accepted environment has, in its safe tier, a theorem of type `False` that uses only the three standard axioms. -/
def T2 (I : Interface) : Prop :=
  ∀ (b : ByteArray) (env : Env), I.K1 → I.K2 → Accepted I b env →
    ¬ ∃ c, env.safe c ∧ c.toConstantVal.type = .const (mkName ["False"]) [] ∧
      ∀ a ∈ I.axiomsOf env c.toConstantVal.name, a ∈ std3

/-- **T3, quarantine.** No constant of the safe tier reaches a constant of the quarantine tier, directly or through the types and values of other constants. Required for 1.0. -/
def T3 (I : Interface) : Prop :=
  ∀ (b : ByteArray) (env : Env), Accepted I b env →
    ∀ c q, env.safe c → env.quarantine q →
      ¬ Reaches I (fun d => env.safe d ∨ env.quarantine d) c q.toConstantVal.name

/-- **T4, report fidelity.** For each accepted theorem, the axioms in the report are the axioms that the theorem depends on. Required for 1.0. -/
def T4 (I : Interface) : Prop :=
  ∀ (st₀ st₁ : I.State) (b : ByteArray) (r : I.Report) (ds : List Declaration) (env : Env),
    I.checkStream st₀ b = .ok (r, st₁) → I.verdict r = .accept →
    I.parseStream b = some ds → I.elaborates ds env →
    ∀ n axs, I.reportedAxioms r n = some axs →
      ∀ a, a ∈ axs ↔ a ∈ I.axiomsOf env n

/-- **T5, parallel determinism.** The result does not depend on the thread count or the schedule, given contract K1. Required for 1.0. -/
def T5 (I : Interface) : Prop :=
  I.K1 → ∀ (n : Nat) (sched : Nat → Nat) (st : I.State) (b : ByteArray),
    0 < n → I.checkStreamPar n sched st b = I.checkStream st b

/-- **T6, relative completeness.** If lean4lean accepts each declaration of the input within some fuel, and the run stays within the resource limits for that fuel, then rulean accepts the input. Optional. It needs the verification of lean4lean (spec 10.11). -/
def T6 (I : Interface) : Prop :=
  ∀ (st₀ : I.State) (b : ByteArray) (ds : List Declaration) (fuel : Nat),
    I.parseStream b = some ds →
    (∀ d ∈ ds, I.lean4leanAccepts d fuel ∧ I.withinLimits d fuel) →
    ∃ r st₁, I.checkStream st₀ b = .ok (r, st₁) ∧ I.verdict r = .accept

/-- The theorems that release 1.0 needs. -/
def Release (I : Interface) : Prop :=
  T1.{w} I ∧ T2 I ∧ T3 I ∧ T4 I ∧ T5 I

end RuleanProof
