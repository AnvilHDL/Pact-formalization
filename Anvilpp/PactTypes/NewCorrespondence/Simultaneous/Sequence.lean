import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Base
import Anvilpp.PactTypes.NewCorrespondence.Helpers.SequenceMenus

namespace Pact

noncomputable section

open Classical

/-- Sequence menus follow from the child menus and backward propagation of the
left completion flag along execution references and optimistic dependencies. -/
theorem futureOffersAgree_seq
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftMenus : FutureOffersAgree left)
    (hRightMenus : FutureOffersAgree right)
    (hComplete : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left) left).states,
      ∀ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).referencedStates q,
      (∃ residual, (residual, r) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) →
      ∃ residual, (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) :
    FutureOffersAgree (.seq alphabet left right) := by
  intro residual state hRelated
  rcases relationMembership_seq_cases alphabet left right hRelated with hLeft | hRight
  · obtain ⟨q, residualLeft, hPair, hRelatedLeft, hRetained⟩ := hLeft
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
    have hKeep : q ∉ sequenceDeleted
        (compileTypeFuel (typeCompilationFuel left) left) := by
      rcases hRetained with hNotFinal | hInitial
      · exact not_mem_sequenceDeleted_of_not_accepting hNotFinal
      · exact hInitial ▸ initial_not_mem_sequenceDeleted _
    -- The left equation has exactly the completion flag of its related residual.
    rw [computeFutureOf_sequence_left alphabet left right hLeftDisjoint hRightDisjoint
      hLeftAlphabet hRightAlphabet q
      (relationMembership_state_mem left residualLeft q hLeftDisjoint hRelatedLeft)
      hKeep hComplete]
    have hFlag : (∃ candidate, (candidate, q) ∈
          buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
          typeCanCompleteThisCycleFuel (sizeOf candidate + 1) candidate = true) ↔
        typeCanCompleteThisCycleFuel (sizeOf residualLeft + 1) residualLeft = true := by
      constructor
      · rintro ⟨candidate, hCandidate, hComplete⟩
        have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel left)
          left hCandidate hRelatedLeft
        simpa only [hEq] using hComplete
      · intro hComplete
        exact ⟨residualLeft, hRelatedLeft, hComplete⟩
    rw [hFlag, hLeftMenus hRelatedLeft,
      hRightMenus (buildRelationSetCoreFuel_initial_mem _ right
        (typeCompilationFuel_sufficient right))]
    -- Apply the two child hypotheses to obtain the syntax's sequence clause.
    rw [typeFutureOffers_sequence,
      ← typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
        (sizeOf residualLeft + 1) residualLeft (by omega)]
    split_ifs <;> simp
  · obtain ⟨q, hState, hRelatedRight⟩ := hRight
    change state = .child 1 q at hState
    subst state
    -- Right states use the unchanged copied-child menu equation.
    rw [computeFutureOf_sequence_right alphabet left right hRightDisjoint hRightAlphabet q
      (relationMembership_state_mem right residual q hRightDisjoint hRelatedRight)]
    exact hRightMenus hRelatedRight

end

end Pact
