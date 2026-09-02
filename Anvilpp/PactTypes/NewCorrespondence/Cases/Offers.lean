import Anvilpp.PactTypes.NewCorrespondence.Cases.Parallel

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section

/-- A branch's own actions stay clear of every later branch's, so a head
singleton and the product generated from the rest own disjoint actions. -/
private theorem headBranch_messageActions_disjoint
    {branch : BareMessage × PactType} {rest : List (BareMessage × PactType)}
    (hDisjoint : ∀ other ∈ rest, BranchDeclarationsDisjoint branch other) :
    Disjoint ({branch.1} ∪ PactType.MessageActions branch.2)
      (PactType.BranchMessageActions rest) := by
  induction rest with
  | nil => simp [PactType.BranchMessageActions]
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      rw [PactType.BranchMessageActions.eq_def]
      exact Finset.disjoint_union_right.mpr
        ⟨(hDisjoint (headAction, headType) (by simp)).1,
          ih (fun other hOther => hDisjoint other (by simp [hOther]))⟩

/-- Step correspondence for the worker that partitions an offer alphabet over
its generated singleton components. -/
theorem correspondence_parallelTypeBranchesWithin_stepIff
     :
    ∀ (alphabet : PactTypeAlphabet)
      (branches : List (BareMessage × PactType)),
      alphabet.WellFormed →
      (∀ branch ∈ branches, BranchAlphabetCarried alphabet branch ∧
        branch.2.TailRecursive ∧
        (∀ other : String, branch.2.TailOccurrences other False) ∧
        branch.2.OfferBranchesDisjoint) →
      List.Pairwise BranchDeclarationsDisjoint branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement
            (branchType.reannotate branchAlphabet)) →
      StepIffStatement
        (parallelTypeBranchesWithin alphabet branches) := by
  -- TODO: proof invalidated by the 2026-09-01 offer-law / alphabet spec change.
  sorry

/-- Step correspondence for the generated, fully unselected branch product. -/
theorem correspondence_parallelTypeBranches_stepIff
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise BranchDeclarationsDisjoint branches)
    (hBranchRegular : ∀ branch ∈ branches,
      branch.2.TailRecursive ∧
        (∀ other : String, branch.2.TailOccurrences other False) ∧
        branch.2.OfferBranchesDisjoint)
    (hBranchesIH : ∀ action branchType,
      (action, branchType) ∈ branches → ∀ branchAlphabet,
        StepIffStatement (branchType.reannotate branchAlphabet)) :
    StepIffStatement (parallelTypeBranches alphabet branches) := by
  -- TODO: proof invalidated by the 2026-09-01 offer-law / alphabet spec change.
  sorry

/-- Step correspondence for the generated branch product after one branch is
selected. -/
theorem correspondence_parallelTypeBranchesSelectingWithin_stepIff
     :
    ∀ (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      selected ∈ branches →
      alphabet.WellFormed →
      (∀ branch ∈ branches, BranchAlphabetCarried alphabet branch ∧
        branch.2.TailRecursive ∧
        (∀ other : String, branch.2.TailOccurrences other False) ∧
        branch.2.OfferBranchesDisjoint) →
      List.Pairwise BranchDeclarationsDisjoint branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement
            (branchType.reannotate branchAlphabet)) →
      StepIffStatement
        (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  -- TODO: proof invalidated by the 2026-09-01 offer-law / alphabet spec change.
  sorry

/-- Step correspondence for the public selected-branch product. -/
theorem correspondence_parallelTypeBranchesSelecting_stepIff
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise BranchDeclarationsDisjoint branches)
    (hBranchRegular : ∀ branch ∈ branches,
      branch.2.TailRecursive ∧
        (∀ other : String, branch.2.TailOccurrences other False) ∧
        branch.2.OfferBranchesDisjoint)
    (hBranchesIH : ∀ action branchType,
      (action, branchType) ∈ branches → ∀ branchAlphabet,
        StepIffStatement (branchType.reannotate branchAlphabet))
    (selected : BareMessage × PactType) (hSelected : selected ∈ branches) :
    StepIffStatement
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  -- TODO: proof invalidated by the 2026-09-01 offer-law / alphabet spec change.
  sorry
/-- Step correspondence for conjunctive offer `⋀(τ0,B)`. -/
theorem correspondence_offer_stepIff
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hAlphaWF : alphabet.WellFormed)
    (hAlphabetBranches :
      PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise BranchDeclarationsDisjoint branches)
    (hBranchRegular : ∀ branch ∈ branches,
      branch.2.TailRecursive ∧
        (∀ other : String, branch.2.TailOccurrences other False) ∧
        branch.2.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hElseIH : StepIffStatement elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        ∀ branchAlphabet,
          StepIffStatement
            (branchType.reannotate branchAlphabet)) :
    StepIffStatement (.offer alphabet elseType branches) := by
  -- TODO: proof invalidated by the 2026-09-01 offer-law / alphabet spec change.
  sorry

end

end Pact
