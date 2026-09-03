import Anvilpp.ProofHelpers.Composition
import Anvilpp.ProofHelpers.Objectives

namespace Pact

noncomputable section

open Classical

/-! ## Regularity, checking, and complexity helpers -/

/-- Closure, hygiene, clock guarding, tail recursion, same-cycle message
linearity, parallel message ownership, and interface scoping. -/
def ClosedGuardedRegular (processType : PactType) : Prop :=
  PactType.AllVariablesBound [] processType ∧
    PactType.BinderHygienic [] processType ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.InterfaceAlphabetScoped processType ∧
    PactType.ConjunctiveMessageOwnership processType

/-- Types admitted by the canonical construction. -/
def AdmissibleType (processType : PactType) : Prop :=
  processType.AlphabetWellFormed ∧
    PactType.ProgressLinear processType ∧
    PactType.FairChoiceLinear processType ∧
    ClosedGuardedRegular processType

/-- `skip` cannot take its silent operational step in a clock environment. -/
theorem skip_has_no_clock_transition {alphabet : PactTypeAlphabet} :
    ¬ ∃ target,
      TypeTransition TypeEnvironment.tock (.skip alphabet) TypeLabel.silent
        target := by
  rintro ⟨target, transition⟩
  cases transition with
  | skip _ _ conditions =>
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

/-- Abstract cost predicates recording the asymptotic claims. -/
def RunsInLinearTime {α β : Type} (function : α → β) : Prop := by
  sorry

def RunsInProductTime {α : Type} (relation : α → α → Bool) : Prop := by
  sorry

/-- A decision procedure packaged as a Lean `Decidable` instance. -/
noncomputable def typeCompatibilityDecidable
     (processType : PactType) (progress : Finset ProcId) :
    Decidable (TypeCompatible processType progress) := by
  sorry

/-- The monitored Rabin-game complexity bound from Theorem 4.4:
`O(M N (K!)^{1+o(1)})` for `N` vertices, `M` edges, and
`K = 1 + 2|cal(Eta)(Θ_0)|` Rabin pairs. -/
def CompatibilityGameComplexityBound
     (processType : PactType) (progress : Finset ProcId) :
    Prop := by
  sorry


end

end Pact
