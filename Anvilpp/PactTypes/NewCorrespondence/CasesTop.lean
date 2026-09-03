import Anvilpp.PactTypes.NewCorrespondence.Cases.Offers
import Anvilpp.PactTypes.NewCorrespondence.Cases.Recursion

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section

private theorem branchesAlphabetWellFormed_of_mem
    {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    branchType.AlphabetWellFormed := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact hBranches.2.1
      · exact ih hBranches.2.2 hTail

private theorem tailRecursiveBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.TailRecursiveBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.TailRecursive := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.TailRecursiveBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2 hMemRest

private theorem allBranchVariablesBound_of_mem
    {bound : List String} {branches : List (BareMessage × PactType)}
    (hBranches : PactType.AllBranchVariablesBound bound branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    PactType.AllVariablesBound bound branch.2 := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.AllBranchVariablesBound] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2 hMemRest

private theorem binderHygienicBranches_of_mem
    {bound : List String} {branches : List (BareMessage × PactType)}
    (hBranches : PactType.BinderHygienicBranches bound branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    PactType.BinderHygienic bound branch.2 := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BinderHygienicBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2 hMemRest

private theorem clockGuardedBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.ClockGuardedBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.ClockGuarded := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.ClockGuardedBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2 hMemRest

private theorem sameCycleMessageLinearBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.SameCycleMessageLinearBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.SameCycleMessageLinear := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.SameCycleMessageLinearBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2 hMemRest

private theorem parallelMessageOwnershipBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.ParallelMessageOwnershipBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.ParallelMessageOwnership := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.ParallelMessageOwnershipBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2.2 hMemRest

private theorem parallelProgressOwnershipBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.ParallelProgressOwnershipBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.ParallelProgressOwnership := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.ParallelProgressOwnershipBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2 hMemRest

private theorem parallelFairChoiceOwnershipBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.ParallelFairChoiceOwnershipBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.ParallelFairChoiceOwnership := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2 hMemRest

private theorem interfaceScopedBranches_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.InterfaceScopedBranches branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    branch.2.InterfaceScoped := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.InterfaceScopedBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2 hMemRest

/-- `ClosedGuardedRegular` fixes the bound-name list to `[]`, but `recur`'s
body is only closed relative to its own binder name.  This bound-generic
form lets the size induction below descend into a `recur` body: at that one
constructor it is instantiated at `name :: bound` instead of `bound`, while
every other constructor threads `bound` through unchanged. -/
private def ClosedGuardedRegularWith
    (bound : List String) (processType : PactType) : Prop :=
  PactType.AllVariablesBound bound processType ∧
    PactType.BinderHygienic bound processType ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.InterfaceAlphabetScoped processType

private theorem closedGuardedRegularWith_of_closedGuardedRegular
    {processType : PactType} (h : ClosedGuardedRegular processType) :
    ClosedGuardedRegularWith [] processType := h

/-- Bound-generic form of `correspondence_stepIff`.  `processType` need only
be closed relative to `bound`, not `[]`, so the induction can hand a `recur`
body the wider bound list `name :: bound` at that one constructor instead of
demanding the impossible `AllVariablesBound [] body`. -/
private theorem correspondence_stepIff_aux
     (bound : List String) (processType : PactType)
    (hAlphabetWF : processType.AlphabetWellFormed)
    (hRegular : ClosedGuardedRegularWith bound processType)
    (hTailClosed : processType.TailClosed) :
    StepIffStatement processType := by
  -- TODO: proof invalidated by the 2026-09-01 alphabet/offer spec change.
  sorry

/-- Step correspondence for all constructors, arranged as the Lemma 4.5 induction. -/
theorem correspondence_stepIff
     (processType : PactType)
    (hAdmissible : AdmissibleType processType) :
    StepIffStatement processType := by
  rcases hAdmissible with ⟨hAlphabetWF, _, _, hRegular⟩
  exact correspondence_stepIff_aux [] processType
    hAlphabetWF
    (closedGuardedRegularWith_of_closedGuardedRegular hRegular)
    (PactType.tailClosed_of_allVariablesBound_nil hRegular.1)

end

end Pact
