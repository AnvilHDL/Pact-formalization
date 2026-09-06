import Anvilpp.PactTypes.Proofs.Syntax.TypeCompletionFuelLemmas
import Anvilpp.PactTypes.Proofs.Syntax.PactTypeSubstitutionLemmas

namespace Pact

noncomputable section
open Classical

mutual
  theorem PactType.completionView_replaceVar (ty : PactType) (name : String)
      (replacement : PactType) :
      (ty.replaceVar name replacement).completionView =
        ty.completionView.replaceVar name replacement.completionView := by
    cases ty with
    | message a m d =>
        simp only [replaceVar, completionView]
        split_ifs <;> simp [replaceVar]
    | var a other =>
        by_cases h : name = other
        all_goals simp only [replaceVar, completionView, h, ↓reduceIte]
    | recur a other body =>
        by_cases h : name = other
        · simp only [replaceVar, completionView, h, ↓reduceIte]
        · simp only [replaceVar, completionView, h, ↓reduceIte]
          rw [completionView_replaceVar body name replacement]
    | xoffer a other branches | offer a other branches =>
        simp only [replaceVar, completionView, replaceBranches_head_gate_iff]
        split_ifs <;> simp only [replaceVar]
        all_goals rw [completionView_replaceVar other name replacement,
          completionViewBranches_replaceBranches branches name replacement]
    | progress a p | skip a | tock a => simp only [replaceVar, completionView]
    | choice a l r | fairChoice a b l r | seq a l r | par a l r i =>
        simp only [replaceVar, completionView]
        rw [completionView_replaceVar l name replacement,
          completionView_replaceVar r name replacement]
  termination_by sizeOf ty

  theorem PactType.completionViewBranches_replaceBranches
      (branches : List (BareMessage × PactType)) (name : String) (replacement : PactType) :
      completionViewBranches (replaceBranches branches name replacement) =
        replaceBranches (completionViewBranches branches) name replacement.completionView := by
    cases branches with
    | nil => simp only [replaceBranches, completionViewBranches]
    | cons branch rest =>
        rcases branch with ⟨action, ty⟩
        simp only [replaceBranches, completionViewBranches]
        rw [completionView_replaceVar ty name replacement,
          completionViewBranches_replaceBranches rest name replacement]
  termination_by sizeOf branches
decreasing_by all_goals simp_wf; omega
end

/-- The existing structural substitution evaluator applies to the gated view. -/
theorem PactType.replaceVar_canCompleteDeclared (name : String) (replacement ty : PactType) :
    (ty.replaceVar name replacement).CanCompleteDeclared =
      canCompleteBeforeTockSubst name replacement.CanCompleteDeclared ty.completionView := by
  simp only [CanCompleteDeclared, completionView_replaceVar, replaceVar_canCompleteBeforeTock]

theorem PactType.canCompleteDeclared_replaceVar_of_complete
    (name : String) (replacement ty : PactType) (h : ty.CanCompleteDeclared = true) :
    (ty.replaceVar name replacement).CanCompleteDeclared = true := by
  rw [replaceVar_canCompleteDeclared]
  exact canCompleteBeforeTock_le_subst name _ ty.completionView h

theorem PactType.canCompleteDeclared_recur_unfold (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) :
    (body.replaceVar name (.recur alphabet name body)).CanCompleteDeclared =
      body.CanCompleteDeclared := by
  rw [replaceVar_canCompleteDeclared, canCompleteDeclared_eq (.recur alphabet name body)]
  exact canCompleteBeforeTockSubst_self name body.completionView

theorem PactType.canCompleteDeclaredSubst_eq_of_tailOccurrences_false
    (name : String) (value : Bool) (ty : PactType)
    (hTail : ty.TailOccurrences name False) :
    canCompleteBeforeTockSubst name value ty.completionView = ty.CanCompleteDeclared := by
  let replacement := if value then PactType.skip ty.alphabet else PactType.tock ty.alphabet
  have h := replaceVar_canCompleteDeclared name replacement ty
  rw [replaceVar_eq_self_of_tailOccurrences_false name replacement ty hTail] at h
  cases value <;> simpa only [replacement, Bool.false_eq_true, ↓reduceIte,
    CanCompleteDeclared, completionView, CanCompleteBeforeTock] using h.symm

end
end Pact
