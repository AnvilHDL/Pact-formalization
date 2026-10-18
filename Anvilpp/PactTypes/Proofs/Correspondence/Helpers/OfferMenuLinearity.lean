import Anvilpp.PactTypes.Spec.Syntax.OfferMenuLinearityDefs
import Anvilpp.PactTypes.Proofs.Syntax.CompletionReannotation
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.OwnershipTransport

namespace Pact

noncomputable section

open Classical

theorem offerMenuLinearBranches_iff (branches : List (BareMessage × PactType)) :
    OfferMenuLinearBranches branches ↔ ∀ branch ∈ branches, OfferMenuLinear branch.2 := by
  induction branches with
  | nil => simp [OfferMenuLinearBranches]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp [OfferMenuLinearBranches, ih]

/-- Re-signing by a covered alphabet cannot introduce a forbidden future head. -/
theorem offerMenuLinear_reannotate :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.AlphabetWellFormed →
      alphabet.actions ⊆ processType.alphabet.actions →
      OfferMenuLinear processType → OfferMenuLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro target hWF hSub hLinear
      cases processType with
      | skip alphabet | var alphabet name | message alphabet msg dir
      | tock alphabet | progress alphabet pid =>
          simp [PactType.reannotate, OfferMenuLinear]
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, OfferMenuLinear] at hLinear ⊢
          exact ih (sizeOf body) (by rw [← hSize]; simp_wf; omega) body rfl
            target hWF.2.2 (by rw [hWF.2.1]; exact hSub) hLinear
      | choice alphabet left right | fairChoice alphabet bid left right
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, OfferMenuLinear] at hLinear ⊢
          exact ⟨ih (sizeOf left) (by rw [← hSize]; simp_wf; omega) left rfl
              target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hSub) hLinear.1,
            ih (sizeOf right) (by rw [← hSize]; simp_wf; omega) right rfl
              target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hSub) hLinear.2⟩
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, OfferMenuLinear] at hLinear ⊢
          have hLeftSub : (PactTypeAlphabet.projectParallel target left.alphabet interface).actions ⊆
              left.alphabet.actions := by
            intro action hAction
            rcases Finset.mem_union.mp hAction with hAction | hAction
            · exact (Finset.mem_filter.mp hAction).1
            · exact PactTypeAlphabet.parent_actions_subset_left hWF.2.1 (hSub hAction)
          have hRightSub : (PactTypeAlphabet.projectParallel target right.alphabet interface).actions ⊆
              right.alphabet.actions := by
            intro action hAction
            rcases Finset.mem_union.mp hAction with hAction | hAction
            · exact (Finset.mem_filter.mp hAction).1
            · exact PactTypeAlphabet.parent_actions_subset_right hWF.2.1 (hSub hAction)
          exact ⟨ih (sizeOf left) (by rw [← hSize]; simp_wf; omega) left rfl
              _ hWF.2.2.1 hLeftSub hLinear.1,
            ih (sizeOf right) (by rw [← hSize]; simp_wf; omega) right rfl
              _ hWF.2.2.2 hRightSub hLinear.2⟩
      | xoffer alphabet other branches | offer alphabet other branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [OfferMenuLinear] at hLinear
          have hEvery : ∀ branch ∈ branches,
              branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed := by
            first
              | exact branchesWF_mem branches hWF.2.2.2
              | exact offerBranchesWF_mem branches hWF.2.2.2
          have hHeads : ∀ child, child.AlphabetWellFormed →
              child.alphabet = alphabet → BranchHeadsAbsentFromMenu branches child →
              BranchHeadsAbsentFromMenu
                (branches.map fun branch => (branch.1, branch.2.reannotate target))
                (child.reannotate target) := by
            intro child hChild hAlphabet hAbsent branch hBranch action hAction
            obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hBranch
            exact hAbsent original hOriginal action
              (typeFutureOffers_reannotate_subset child target hChild
                (by rw [hAlphabet]; exact hSub) hAction)
          have hBranches : ∀ branch ∈ branches,
              OfferMenuLinear (branch.2.reannotate target) := by
            intro branch hBranch
            have hLt : sizeOf branch.2 < n := by
              have hLe := List.sizeOf_lt_of_mem hBranch
              have hBody : sizeOf branch.2 < sizeOf branch := by
                rcases branch with ⟨action, body⟩
                simp_wf
                omega
              rw [← hSize]
              simp_wf
              omega
            exact ih _ hLt branch.2 rfl target (hEvery branch hBranch).2
              (by rw [(hEvery branch hBranch).1]; exact hSub)
              ((offerMenuLinearBranches_iff branches).mp hLinear.2.2.2 branch hBranch)
          simp only [PactType.reannotate, PactType.reannotateBranches_map,
            PactType.reannotateOfferBranches_map, OfferMenuLinear]
          refine ⟨hHeads other hWF.2.2.1 hWF.2.1 hLinear.1, ?_, ?_, ?_⟩
          · intro branch hBranch
            obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hBranch
            exact hHeads original.2 (hEvery original hOriginal).2
              (hEvery original hOriginal).1 (hLinear.2.1 original hOriginal)
          · exact ih (sizeOf other) (by rw [← hSize]; simp_wf; omega) other rfl
              target hWF.2.2.1 (by rw [hWF.2.1]; exact hSub) hLinear.2.2.1
          · rw [offerMenuLinearBranches_iff]
            intro branch hBranch
            obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hBranch
            exact hBranches original hOriginal

/-- Generated singleton offers inherit the head exclusion of the written offer. -/
theorem parallelTypeBranchesSelecting_offerMenuLinear
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed)
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hLinear : ∀ branch ∈ branches, OfferMenuLinear branch.2)
    (hHeads : ∀ branch ∈ branches, BranchHeadsAbsentFromMenu branches branch.2) :
    OfferMenuLinear (parallelTypeBranchesSelecting alphabet selected branches) := by
  have hFixed : ∀ branch ∈ branches, branch.2.reannotate alphabet = branch.2 := by
    intro branch hBranch
    rw [← hAlphabet branch hBranch]
    exact PactType.reannotate_own_alphabet branch.2 (hWF branch hBranch)
  have hSingleton : ∀ branch ∈ branches,
      OfferMenuLinear (singletonTypeXOfferAt alphabet branch) := by
    intro branch hBranch
    simp only [singletonTypeXOfferAt, hFixed branch hBranch, OfferMenuLinear,
      OfferMenuLinearBranches]
    refine ⟨?_, ?_, trivial, hLinear branch hBranch, trivial⟩
    · simp [BranchHeadsAbsentFromMenu, typeFutureOffers, typeFutureOffersFuel]
    · intro candidate hCandidate
      have hEq : candidate = branch := by simpa using hCandidate
      subst candidate
      intro head hHead action hAction
      have hEq : head = branch := by simpa using hHead
      subst head
      exact hHeads branch hBranch branch hBranch action hAction
  have hSelected : ∀ branch ∈ branches,
      OfferMenuLinear (selectedTypeBranchAt alphabet branch) := by
    intro branch hBranch
    simp only [selectedTypeBranchAt, hFixed branch hBranch, OfferMenuLinear]
    exact ⟨trivial, hLinear branch hBranch⟩
  have hWithin : ∀ list : List (BareMessage × PactType),
      (∀ branch ∈ list, branch ∈ branches) →
      OfferMenuLinear (parallelTypeBranchesWithin alphabet list) := by
    intro list
    induction list with
    | nil => intro _; simp [parallelTypeBranchesWithin, OfferMenuLinear]
    | cons head tail ih =>
        intro hSub
        have hHead := hSingleton head (hSub head (by simp))
        have hTail := ih (fun branch hBranch => hSub branch (by simp [hBranch]))
        cases tail with
        | nil => exact hHead
        | cons next rest =>
            simpa only [parallelTypeBranchesWithin, OfferMenuLinear] using And.intro hHead hTail
  have hSelecting : ∀ list : List (BareMessage × PactType),
      (∀ branch ∈ list, branch ∈ branches) →
      OfferMenuLinear (parallelTypeBranchesSelectingWithin alphabet selected list) := by
    intro list
    induction list with
    | nil => intro _; simp [parallelTypeBranchesSelectingWithin, OfferMenuLinear]
    | cons head tail ih =>
        intro hSub
        have hHead := hSingleton head (hSub head (by simp))
        have hChosen := hSelected head (hSub head (by simp))
        have hTail := ih (fun branch hBranch => hSub branch (by simp [hBranch]))
        have hRest := hWithin tail (fun branch hBranch => hSub branch (by simp [hBranch]))
        cases tail with
        | nil =>
            simp only [parallelTypeBranchesSelectingWithin]
            split_ifs <;> assumption
        | cons next rest =>
            simp only [parallelTypeBranchesSelectingWithin]
            split_ifs <;>
              simp only [OfferMenuLinear] <;> exact ⟨by assumption, by assumption⟩
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, OfferMenuLinear]
  | cons head tail => exact hSelecting _ (fun _ hMem => hMem)

/-- Generated singleton offers inherit the head exclusion of the written offer. -/
theorem parallelTypeBranchesFiring_offerMenuLinear
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed)
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hLinear : ∀ branch ∈ branches, OfferMenuLinear branch.2)
    (hHeads : ∀ branch ∈ branches, BranchHeadsAbsentFromMenu branches branch.2) :
    OfferMenuLinear (parallelTypeBranchesFiring alphabet selected branches) := by
  have hFixed : ∀ branch ∈ branches, branch.2.reannotate alphabet = branch.2 := by
    intro branch hBranch
    rw [← hAlphabet branch hBranch]
    exact PactType.reannotate_own_alphabet branch.2 (hWF branch hBranch)
  have hSingleton : ∀ branch ∈ branches,
      OfferMenuLinear (singletonTypeXOfferAt alphabet branch) := by
    intro branch hBranch
    simp only [singletonTypeXOfferAt, hFixed branch hBranch, OfferMenuLinear,
      OfferMenuLinearBranches]
    refine ⟨?_, ?_, trivial, hLinear branch hBranch, trivial⟩
    · simp [BranchHeadsAbsentFromMenu, typeFutureOffers, typeFutureOffersFuel]
    · intro candidate hCandidate
      have hEq : candidate = branch := by simpa using hCandidate
      subst candidate
      intro head hHead action hAction
      have hEq : head = branch := by simpa using hHead
      subst head
      exact hHeads branch hBranch branch hBranch action hAction
  have hFrom : ∀ list : List (BareMessage × PactType),
      (∀ branch ∈ list, branch ∈ branches) → ∀ index,
      OfferMenuLinear (parallelTypeBranchesFiringFrom alphabet selected index list) := by
    intro list
    induction list with
    | nil => intro _ index; simp [parallelTypeBranchesFiringFrom, OfferMenuLinear]
    | cons head tail ih =>
        intro hSub index
        have hFactor : OfferMenuLinear
            (if index ∈ selected then head.2.reannotate alphabet
              else singletonTypeXOfferAt alphabet head) := by
          split_ifs
          · rw [hFixed head (hSub head (by simp))]
            exact hLinear head (hSub head (by simp))
          · exact hSingleton head (hSub head (by simp))
        cases tail with
        | nil => exact hFactor
        | cons next rest =>
            rw [parallelTypeBranchesFiringFrom, OfferMenuLinear]
            exact ⟨hFactor, ih (fun b hb => hSub b (by simp [hb])) (index + 1)⟩
  exact hFrom branches (fun _ h => h) 0

end
end Pact
