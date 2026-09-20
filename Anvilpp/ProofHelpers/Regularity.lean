import Anvilpp.ProofHelpers.Composition
import Anvilpp.ProofHelpers.Objectives
import Anvilpp.ProofHelpers.LogRecognizer
import Anvilpp.PactTypes.Spec.Syntax.OfferMenuLinearityDefs

namespace Pact

noncomputable section

open Classical

/-! ## Type admissibility and objective regularity -/

/-- Closed, hygienic, clock-guarded types with linear messages and scoped ownership. -/
def ClosedGuardedRegular (processType : PactType) : Prop :=
  PactType.AllVariablesBound [] processType ∧
    PactType.BinderHygienic [] processType ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.InterfaceAlphabetScoped processType ∧
    PactType.ConjunctiveMessageOwnership processType ∧
    OfferMenuLinear processType

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

end

end Pact
