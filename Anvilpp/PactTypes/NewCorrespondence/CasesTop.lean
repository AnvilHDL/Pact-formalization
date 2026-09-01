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
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.2.2.1
      · exact ih hBranches.2.2.2 hMemRest

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
    PactType.InterfaceScoped processType

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
  have hTailRecursive : processType.TailRecursive := hRegular.2.2.2.1
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound hAlphabetWF hTailRecursive
      hTailClosed hRegular with
  | _ n ih =>
      cases processType with
      | message alphabet msg dir =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_message_stepIff alphabet msg dir
            hRelated hSymbol
      | progress alphabet pid =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_progress_stepIff alphabet pid
            hRelated hSymbol
      | tock alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_tock_stepIff alphabet hRelated hSymbol
      | skip alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_skip_stepIff alphabet hRelated hSymbol
      | choice alphabet left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              left.TailOccurrences other True ∧
                right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => (hClosedSplit other).1,
              fun other => (hClosedSplit other).2⟩
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hLeftIH : StepIffStatement left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize bound left
              hAlphabetWF.2.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.1.1, hRegular.2.2.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.2.2.1⟩
              hClosedFields.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize bound right
              hAlphabetWF.2.2.2.2
              ⟨hRegular.1.2, hRegular.2.1.2, hRegular.2.2.1.2, hTailRecursive.2,
                hRegular.2.2.2.2.1.2, hRegular.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.1.2, hRegular.2.2.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.2.2.2⟩
              hClosedFields.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_choice_stepIff alphabet left right
            hAlphabetWF.2.1 hAlphabetWF.2.2.1 hLeftIH hRightIH hRelated
            hSymbol
      | seq alphabet first second =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              first.TailOccurrences other False ∧
                second.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedFields : first.TailClosed ∧ second.TailClosed :=
            ⟨fun other => PactType.tailOccurrences_mono other False.elim first
                (hClosedSplit other).1,
              fun other => (hClosedSplit other).2⟩
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hFirstIH : StepIffStatement first := by
            have hFirstSize : sizeOf first < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf first) hFirstSize bound first
              hAlphabetWF.2.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.1.1, hRegular.2.2.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.2.2.1⟩
              hClosedFields.1 hTailRecursive.1 rfl hRelated hSymbol
          have hSecondIH : StepIffStatement second := by
            have hSecondSize : sizeOf second < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf second) hSecondSize bound second
              hAlphabetWF.2.2.2.2
              ⟨hRegular.1.2, hRegular.2.1.2, hRegular.2.2.1.2, hTailRecursive.2,
                hRegular.2.2.2.2.1.2.1, hRegular.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.1.2, hRegular.2.2.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.2.2.2⟩
              hClosedFields.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_seq_stepIff alphabet first second
            hAlphabetWF.2.1 hAlphabetWF.2.2.1 hFirstIH hSecondIH hRelated
            hSymbol
      | par alphabet left right interface =>
          intro residual residual' state env label offers hRelated hSymbol
          have hParentCoherent :
              (.par alphabet left right interface : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              left.TailOccurrences other False ∧
                right.TailOccurrences other False := fun other => by
            simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => PactType.tailOccurrences_mono other False.elim left
                (hClosedSplit other).1,
              fun other => PactType.tailOccurrences_mono other False.elim right
                (hClosedSplit other).2⟩
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hLeftIH : StepIffStatement left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize bound left
              hAlphabetWF.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.2.2.1,
                hRegular.2.2.2.2.2.2.1.2.1, hRegular.2.2.2.2.2.2.2.1.2.1,
                hRegular.2.2.2.2.2.2.2.2.2.1⟩
              hClosedFields.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize bound right
              hAlphabetWF.2.2.2
              ⟨hRegular.1.2, hRegular.2.1.2, hRegular.2.2.1.2, hTailRecursive.2,
                hRegular.2.2.2.2.1.2, hRegular.2.2.2.2.2.1.2.2.2,
                hRegular.2.2.2.2.2.2.1.2.2, hRegular.2.2.2.2.2.2.2.1.2.2,
                hRegular.2.2.2.2.2.2.2.2.2.2⟩
              hClosedFields.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_par_stepIff alphabet left right interface
            hAlphabetWF.2.1.parent_eq hAlphabetWF.2.1
            hRegular.2.2.2.2.2.1.2.1
            ⟨hAlphabetWF.2.2.1, hTailRecursive.1, hClosedFields.1,
              offerBranchesDisjoint_of_ownership left hRegular.2.2.2.2.2.1.2.2.1
                hRegular.2.2.2.2.2.2.1.2.1 hRegular.2.2.2.2.2.2.2.1.2.1⟩
            ⟨hAlphabetWF.2.2.2, hTailRecursive.2, hClosedFields.2,
              offerBranchesDisjoint_of_ownership right hRegular.2.2.2.2.2.1.2.2.2
                hRegular.2.2.2.2.2.2.1.2.2 hRegular.2.2.2.2.2.2.2.1.2.2⟩
            hParentCoherent hLeftIH
            hRightIH hRelated hSymbol
      | var alphabet id =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_var_stepIff alphabet id hRelated hSymbol
      | recur alphabet id body =>
          intro residual residual' state env label offers hRelated hSymbol
          -- `AdmissibleType`/`ClosedGuardedRegular` fix the bound-name list
          -- to `[]`, so this reconstruction is only literally available when
          -- this `recur` node itself is not nested under an enclosing
          -- `recur`'s body (`bound = []`).  A `recur` nested that way is a
          -- genuine gap: `Cases/Recursion.lean`'s
          -- `recursion_body_forward_obligation` / `_backward_obligation` /
          -- `correspondence_recur_stepIff` all hardcode `AdmissibleType`
          -- (bound `[]`) for the current node too, so no bound-generic
          -- replacement is available from this file alone.  Pre-existing,
          -- separate proof debt from the `ih`-arity fix this session made,
          -- left as `sorry` pending a bound-generic `Cases/Recursion.lean`.
          have hWholeAdmissible : AdmissibleType (.recur alphabet id body) := by
            rcases bound with _ | ⟨head, tail⟩
            · exact ⟨hAlphabetWF, hRegular⟩
            · sorry
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hBodyClosed : body.TailClosed := by
            intro other
            by_cases hName : id = other
            · exact hName ▸ hTailRecursive.1
            · simpa only [PactType.TailOccurrences, if_neg hName] using
                hTailClosed other
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hBodyIH : StepIffStatement body := by
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf body) hBodySize (id :: bound) body
              hAlphabetWF.2.2
              ⟨hRegular.1, hRegular.2.1.2, hRegular.2.2.1.2, hTailRecursive.2,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1,
                hRegular.2.2.2.2.2.2.1, hRegular.2.2.2.2.2.2.2.1,
                hRegular.2.2.2.2.2.2.2.2⟩
              hBodyClosed hTailRecursive.2 rfl hRelated hSymbol
          have hBodyForward :
              RecursionBodyForwardObligation alphabet id body :=
            recursion_body_forward_obligation alphabet id body
              hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
          have hBodyBackward :
              RecursionBodyBackwardObligation alphabet id body :=
            recursion_body_backward_obligation alphabet id body
              hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
          exact correspondence_recur_stepIff alphabet id body
            hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
            hBodyForward hBodyBackward
            hRelated hSymbol
      | fairChoice alphabet id left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              left.TailOccurrences other True ∧
                right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => (hClosedSplit other).1,
              fun other => (hClosedSplit other).2⟩
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hLeftIH : StepIffStatement left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize bound left
              hAlphabetWF.2.2.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.1.1, hRegular.2.2.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.2.2.1⟩
              hClosedFields.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize bound right
              hAlphabetWF.2.2.2.2.2
              ⟨hRegular.1.2, hRegular.2.1.2, hRegular.2.2.1.2, hTailRecursive.2,
                hRegular.2.2.2.2.1.2, hRegular.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.1.2, hRegular.2.2.2.2.2.2.2.1.2,
                hRegular.2.2.2.2.2.2.2.2.2⟩
              hClosedFields.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_fairChoice_stepIff alphabet id left right
            hAlphabetWF.2.2.1 hAlphabetWF.2.2.2.1 hLeftIH hRightIH hRelated
            hSymbol
      | xoffer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              elseType.TailOccurrences other True ∧
                PactType.TailBranchOccurrences other True branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedElse : elseType.TailClosed :=
            fun other => (hClosedSplit other).1
          have hClosedBranches : PactType.TailClosedBranches branches :=
            fun other => (hClosedSplit other).2
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hElseIH : StepIffStatement elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize bound elseType
              hAlphabetWF.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.1.1, hRegular.2.2.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.2.2.1⟩
              hClosedElse hTailRecursive.1 rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            have hBranchAllVarsBound :
                PactType.AllVariablesBound bound branchType :=
              allBranchVariablesBound_of_mem hRegular.1.2 hMember
            have hBranchBinderHyg : PactType.BinderHygienic bound branchType :=
              binderHygienicBranches_of_mem hRegular.2.1.2 hMember
            have hBranchClockGuarded : PactType.ClockGuarded branchType :=
              clockGuardedBranches_of_mem hRegular.2.2.1.2 hMember
            have hBranchSameCycle :
                PactType.SameCycleMessageLinear branchType :=
              sameCycleMessageLinearBranches_of_mem hRegular.2.2.2.2.1.2.1 hMember
            have hBranchMsgOwnership :
                PactType.ParallelMessageOwnership branchType :=
              parallelMessageOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.1.2 hMember
            have hBranchProgressOwnership :
                PactType.ParallelProgressOwnership branchType :=
              parallelProgressOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.2.1.2 hMember
            have hBranchFairChoiceOwnership :
                PactType.ParallelFairChoiceOwnership branchType :=
              parallelFairChoiceOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.2.2.1.2 hMember
            have hBranchInterfaceScoped : PactType.InterfaceScoped branchType :=
              interfaceScopedBranches_of_mem hRegular.2.2.2.2.2.2.2.2.2 hMember
            have hBranchTailRecursive : branchType.TailRecursive :=
              tailRecursiveBranches_of_mem hTailRecursive.2 hMember
            have hBranchTailClosed : branchType.TailClosed := fun other =>
              PactType.tailOccurrences_of_mem_branches other True
                (hClosedBranches other) hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize bound branchType
              hBranchAlphabetWF
              ⟨hBranchAllVarsBound, hBranchBinderHyg, hBranchClockGuarded,
                hBranchTailRecursive,
                hBranchSameCycle, hBranchMsgOwnership, hBranchProgressOwnership,
                hBranchFairChoiceOwnership, hBranchInterfaceScoped⟩
              hBranchTailClosed hBranchTailRecursive rfl hRelated hSymbol
          exact correspondence_xoffer_stepIff alphabet elseType branches
            hAlphabetWF.2.1
            (fun action branchType hMember =>
              PactType.branch_alphabet_eq_of_mem hAlphabetWF.2.2.2 hMember)
            (fun b hMem =>
              branch_action_mem_fixedAlphabet_of_mem hAlphabetWF.2.2.2 (by simpa using hMem))
            hElseIH hBranchesIH hRelated hSymbol
      | offer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          have hOfferCoherent :
              (.offer alphabet elseType branches : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetCoherent] at hOfferCoherent
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hClosedSplit : ∀ other : String,
              elseType.TailOccurrences other True ∧
                PactType.TailBranchOccurrences other False branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hTailClosed other
          have hClosedElse : elseType.TailClosed :=
            fun other => (hClosedSplit other).1
          have hClosedBranchesFalse : ∀ other : String,
              PactType.TailBranchOccurrences other False branches :=
            fun other => (hClosedSplit other).2
          have hClosedBranches : PactType.TailClosedBranches branches :=
            fun other => PactType.tailBranchOccurrences_mono other False.elim
              branches (hClosedBranchesFalse other)
          simp only [ClosedGuardedRegularWith, PactType.AllVariablesBound,
            PactType.BinderHygienic, PactType.ClockGuarded,
            PactType.SameCycleMessageLinear, PactType.ParallelMessageOwnership,
            PactType.ParallelProgressOwnership,
            PactType.ParallelFairChoiceOwnership,
            PactType.InterfaceScoped] at hRegular
          have hElseIH : StepIffStatement elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize bound elseType
              hAlphabetWF.2.2.1
              ⟨hRegular.1.1, hRegular.2.1.1, hRegular.2.2.1.1, hTailRecursive.1,
                hRegular.2.2.2.2.1.1, hRegular.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.1.1, hRegular.2.2.2.2.2.2.2.1.1,
                hRegular.2.2.2.2.2.2.2.2.1⟩
              hClosedElse hTailRecursive.1 rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            have hBranchAllVarsBound :
                PactType.AllVariablesBound bound branchType :=
              allBranchVariablesBound_of_mem hRegular.1.2 hMember
            have hBranchBinderHyg : PactType.BinderHygienic bound branchType :=
              binderHygienicBranches_of_mem hRegular.2.1.2 hMember
            have hBranchClockGuarded : PactType.ClockGuarded branchType :=
              clockGuardedBranches_of_mem hRegular.2.2.1.2 hMember
            have hBranchSameCycle :
                PactType.SameCycleMessageLinear branchType :=
              sameCycleMessageLinearBranches_of_mem hRegular.2.2.2.2.1.2.1 hMember
            have hBranchMsgOwnership :
                PactType.ParallelMessageOwnership branchType :=
              parallelMessageOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.1.2 hMember
            have hBranchProgressOwnership :
                PactType.ParallelProgressOwnership branchType :=
              parallelProgressOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.2.1.2 hMember
            have hBranchFairChoiceOwnership :
                PactType.ParallelFairChoiceOwnership branchType :=
              parallelFairChoiceOwnershipBranches_of_mem
                hRegular.2.2.2.2.2.2.2.1.2 hMember
            have hBranchInterfaceScoped : PactType.InterfaceScoped branchType :=
              interfaceScopedBranches_of_mem hRegular.2.2.2.2.2.2.2.2.2 hMember
            have hBranchTailRecursive : branchType.TailRecursive :=
              tailRecursiveBranches_of_mem hTailRecursive.2 hMember
            have hBranchTailClosed : branchType.TailClosed := fun other =>
              PactType.tailOccurrences_of_mem_branches other True
                (hClosedBranches other) hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize bound branchType
              hBranchAlphabetWF
              ⟨hBranchAllVarsBound, hBranchBinderHyg, hBranchClockGuarded,
                hBranchTailRecursive,
                hBranchSameCycle, hBranchMsgOwnership, hBranchProgressOwnership,
                hBranchFairChoiceOwnership, hBranchInterfaceScoped⟩
              hBranchTailClosed hBranchTailRecursive rfl hRelated hSymbol
          -- The branches own disjoint declarations, so the generated product
          -- can hand each of them its own part of the offer alphabet.
          have hPairwise : List.Pairwise BranchDeclarationsDisjoint branches :=
            branchDeclarationsDisjoint_pairwise branches
              hRegular.2.2.2.2.2.1.2 hRegular.2.2.2.2.2.2.1.2
              hRegular.2.2.2.2.2.2.2.1.2
          -- TODO(offer-reannotation-gap): the callee asks for the branch
          -- induction hypothesis at every reannotated alphabet, which needs
          -- the admissibility bundle to transport under `reannotate`.
          have hBranchRegular : ∀ branch ∈ branches,
              branch.2.TailRecursive ∧
                (∀ other : String, branch.2.TailOccurrences other False) ∧
                branch.2.OfferBranchesDisjoint := by
            intro branch hMember
            exact ⟨tailRecursiveBranches_of_mem hTailRecursive.2 hMember,
              (fun other => PactType.tailOccurrences_of_mem_branches other False
                (hClosedBranchesFalse other) hMember),
              offerBranchesDisjoint_of_ownership branch.2
                (parallelMessageOwnershipBranches_of_mem
                  hRegular.2.2.2.2.2.1.2 hMember)
                (parallelProgressOwnershipBranches_of_mem
                  hRegular.2.2.2.2.2.2.1.2 hMember)
                (parallelFairChoiceOwnershipBranches_of_mem
                  hRegular.2.2.2.2.2.2.2.1.2 hMember)⟩
          exact correspondence_offer_stepIff alphabet elseType branches
            hAlphabetWF.1 hAlphabetWF.2.2.2 hPairwise hBranchRegular
            hAlphabetWF.2.1 hElseIH (fun action branchType hMember _ => by sorry)
            hRelated hSymbol

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
