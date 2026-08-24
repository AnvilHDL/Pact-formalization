import Anvilpp.ProofHelpers.Composition
import Anvilpp.ProofHelpers.Objectives

namespace Pact

noncomputable section

open Classical

/-! ## Regularity, checking, and complexity helpers -/

/--
The paper's admissible recursive types: variables are closed, every recursive
backedge is preceded by at least one synchronized clock step, recursive calls
are tail terminating, a message is exchanged at most once per cycle, and
nested parallel binders have lexically disjoint interfaces
(`pactautomatonconstruction.typ`, "Regularity"; unchanged by this
redevelopment).

Tail termination is the finite-control part of regularity.  It ensures that a
shared backedge never has to retain a newly generated sequence, parallel, or
conjunctive-offer context.
-/
def ClosedGuardedRegular (processType : PactType) : Prop :=
  PactType.AllVariablesBound [] processType ∧
    PactType.BinderHygienic [] processType ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.ParallelProgressOwnership processType ∧
    PactType.ParallelFairChoiceOwnership processType ∧
    PactType.InterfaceScoped processType

/-- Types admitted by the canonical construction relative to a fixed alphabet. -/
def AdmissibleType (signature : TypeAlphabet) (processType : PactType) : Prop :=
  signature.WellFormed ∧ signature.Supports processType ∧
    ClosedGuardedRegular processType

/-- `skip` cannot take its silent operational step in a clock environment. -/
theorem skip_has_no_clock_transition :
    ¬ ∃ target,
      TypeTransition TypeEnvironment.tock .skip TypeLabel.silent target := by
  rintro ⟨target, transition⟩
  cases transition with
  | skip _ conditions =>
      simp [TypeEnvironment.tock] at conditions

/-- Proposition 4.1's underlying notion of omega-regularity. -/
def OmegaRegular (initial : PactType) (progress : Finset ProcId) : Prop := by
  sorry

/-- Effective refinement checker used by the decidability theorem. -/
def refinementChecker (precise abstract : PactType) : Bool := by
  sorry

/-- A decision procedure packaged as a Lean `Decidable` instance. -/
noncomputable def dataObliviousCheckingDecidable
    (process : Proc) (claimed : PactType) :
    Decidable (DataObliviousChecks process claimed) := by
  sorry

/-- Abstract cost predicates used to record the paper's asymptotic claims. -/
def RunsInLinearTime {α β : Type} (function : α → β) : Prop := by
  sorry

def RunsInProductTime {α : Type} (relation : α → α → Bool) : Prop := by
  sorry

/-- A decision procedure packaged as a Lean `Decidable` instance. -/
noncomputable def typeCompatibilityDecidable
    (signature : TypeAlphabet) (processType : PactType) (progress : Finset ProcId) :
    Decidable (TypeCompatible signature processType progress) := by
  sorry

/-- The monitored Rabin-game complexity bound from Theorem 4.4:
`O(M N (K!)^{1+o(1)})` for `N` vertices, `M` edges, and
`K = 1 + 2|cal(Eta)(Θ_0)|` Rabin pairs. -/
def CompatibilityGameComplexityBound
    (signature : TypeAlphabet) (processType : PactType) (progress : Finset ProcId) :
    Prop := by
  sorry


end

end Pact
