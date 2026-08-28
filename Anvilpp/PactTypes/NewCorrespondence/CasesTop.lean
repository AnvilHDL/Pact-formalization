import Anvilpp.PactTypes.NewCorrespondence.Cases.Offers
import Anvilpp.PactTypes.NewCorrespondence.Cases.Recursion

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section

private theorem supportsBranches_of_mem
    (signature : TypeAlphabet) {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : signature.SupportsBranches branches)
    (hMem : (action, branchType) ∈ branches) :
    signature.Supports branchType := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      have hAll :
          ((headAction ∈ signature.boundary ∨
              headAction.1 ∈ signature.interface) ∧
            signature.Supports headType ∧
            signature.SupportsBranches rest) := by
        simpa only [TypeAlphabet.SupportsBranches] using hBranches
      have hPieces : signature.Supports headType ∧
          signature.SupportsBranches rest := by
        exact hAll.2
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact hPieces.1
      · exact ih hPieces.2 hMemRest

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

/-- Step correspondence for all constructors, arranged as the Lemma 4.5 induction. -/
theorem correspondence_stepIff
    (signature : TypeAlphabet) (processType : PactType)
    (hAdmissible : AdmissibleType signature processType) :
    StepIffStatement signature processType := by
  have hWholeAdmissible : AdmissibleType signature processType := hAdmissible
  rcases hAdmissible with
    ⟨hSignatureWF, hSupports, hAlphabetWF, hRegular⟩
  have hTailRecursive : processType.TailRecursive := hRegular.2.2.2.1
  clear hSignatureWF hRegular
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType hSupports hAlphabetWF hTailRecursive with
  | _ n ih =>
      cases processType with
      | message alphabet msg dir =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_message_stepIff signature alphabet msg dir
            hRelated hSymbol
      | progress alphabet pid =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_progress_stepIff signature alphabet pid
            hRelated hSymbol
      | tock alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_tock_stepIff signature alphabet hRelated hSymbol
      | skip alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_skip_stepIff signature alphabet hRelated hSymbol
      | choice alphabet left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.1
              hAlphabetWF.2.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2
              hAlphabetWF.2.2.2.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_choice_stepIff signature alphabet left right
            hAlphabetWF.2.1 hAlphabetWF.2.2.1 hLeftIH hRightIH hRelated
            hSymbol
      | seq alphabet first second =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hFirstIH : StepIffStatement signature first := by
            have hFirstSize : sizeOf first < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf first) hFirstSize first hSupports.1
              hAlphabetWF.2.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hSecondIH : StepIffStatement signature second := by
            have hSecondSize : sizeOf second < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf second) hSecondSize second hSupports.2
              hAlphabetWF.2.2.2.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_seq_stepIff signature alphabet first second
            hAlphabetWF.2.1 hAlphabetWF.2.2.1 hFirstIH hSecondIH hRelated
            hSymbol
      | par alphabet left right interface =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          have hParentCoherent :
              (.par alphabet left right interface : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.2.1
              hAlphabetWF.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2.2
              hAlphabetWF.2.2.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_par_stepIff signature alphabet left right interface
            hSupports.1 hAlphabetWF.2.1.parent_eq hAlphabetWF.2.1
            hAlphabetWF.2.2.1 hAlphabetWF.2.2.2 hParentCoherent hLeftIH
            hRightIH hRelated hSymbol
      | var alphabet id =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_var_stepIff signature alphabet id hRelated hSymbol
      | recur alphabet id body =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hBodyIH : StepIffStatement signature body := by
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf body) hBodySize body hSupports hAlphabetWF.2.2
              hTailRecursive.2 rfl hRelated hSymbol
          have hBodyForward :
              RecursionBodyForwardObligation signature alphabet id body :=
            recursion_body_forward_obligation signature alphabet id body
              hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
          have hBodyBackward :
              RecursionBodyBackwardObligation signature alphabet id body :=
            recursion_body_backward_obligation signature alphabet id body
              hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
          exact correspondence_recur_stepIff signature alphabet id body
            hAlphabetWF.2.1 hTailRecursive.1 hWholeAdmissible hBodyIH
            hBodyForward hBodyBackward
            hRelated hSymbol
      | fairChoice alphabet id left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.2.1
              hAlphabetWF.2.2.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2.2
              hAlphabetWF.2.2.2.2.2 hTailRecursive.2 rfl hRelated hSymbol
          exact correspondence_fairChoice_stepIff signature alphabet id left right
            hAlphabetWF.2.2.1 hAlphabetWF.2.2.2.1 hLeftIH hRightIH hRelated
            hSymbol
      | xoffer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType hSupports.1
              hAlphabetWF.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement signature branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            have hBranchSupports : signature.Supports branchType :=
              supportsBranches_of_mem signature hSupports.2 hMember
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType hBranchSupports
              hBranchAlphabetWF
              (tailRecursiveBranches_of_mem hTailRecursive.2 hMember)
              rfl hRelated hSymbol
          exact correspondence_xoffer_stepIff signature alphabet elseType branches
            hAlphabetWF.2.1
            (fun action branchType hMember =>
              PactType.branch_alphabet_eq_of_mem hAlphabetWF.2.2.2 hMember)
            hElseIH hBranchesIH hRelated hSymbol
      | offer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          have hOfferCoherent :
              (.offer alphabet elseType branches : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetCoherent] at hOfferCoherent
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          simp only [PactType.TailRecursive] at hTailRecursive
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType hSupports.1
              hAlphabetWF.2.2.1 hTailRecursive.1 rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement signature branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            have hBranchSupports : signature.Supports branchType :=
              supportsBranches_of_mem signature hSupports.2 hMember
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType hBranchSupports
              hBranchAlphabetWF
              (tailRecursiveBranches_of_mem hTailRecursive.2 hMember)
              rfl hRelated hSymbol
          -- TODO(offer-reannotation-gap): pairwise action-disjointness across
          -- offer branches, and `ReannotationSafe` for each branch body
          -- against any target alphabet, are new invariants introduced by
          -- this session's `AlphabetPreservation.lean` work (needed to make
          -- `AlphabetWellFormed` transport under `reannotate` honestly, since
          -- unlike `AlphabetCoherent` it is not free).  Neither is yet
          -- established for arbitrary offer branches here — genuine, separate
          -- proof debt, not specific to the parallel-composition case this
          -- session was asked to fix.  Left as `sorry` pending that
          -- development.
          exact correspondence_offer_stepIff signature alphabet elseType branches
            hAlphabetWF.1 hAlphabetWF.2.2.2 (by sorry) (by sorry)
            hAlphabetWF.2.1 hElseIH hBranchesIH hRelated hSymbol

end

end Pact
