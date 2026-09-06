import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.CompletionFlag
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SequenceMenus
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MarkerMenus

namespace Pact

noncomputable section

open Classical

/-- With no left marker, a sequence reaches a marker exactly by taking its
optimistic continuation and then a right-component path. -/
theorem menuMarkerReachable_sequence_left
    (alphabet : PactTypeAlphabet) (left right : PactType) (name : String)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hNoMarker : (compileTypeFuel (typeCompilationFuel left) left).NoMarkerFor name)
    (source : TypeAutomatonState)
    (hSource : source ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hRetained : source ∉ sequenceDeleted (compileTypeFuel (typeCompilationFuel left) left))
    (hComplete : ∀ q ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).futureReachable source,
      ∀ r ∈ (compiledMenuGraphFuel (typeCompilationFuel left) left).referencedStates q,
      (∃ residual, (residual, r) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) →
      ∃ residual, (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) :
    (∃ q ∈ (compiledMenuGraphFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)).futureReachable (.child 0 source),
      MarkerSource (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)) name q) ↔
      (∃ residual, (residual, source) ∈ buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) ∧
      (∃ q ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable
        (compileTypeFuel (typeCompilationFuel right) right).initial,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name q) := by
  let observe := fun (fragment : AutomatonFragment) q =>
    if MarkerSource fragment name q then ({("", MessageDir.send)} : Finset BareMessage) else ∅
  have hLeftEmpty : ∀ q, observe (compileTypeFuel (typeCompilationFuel left) left) q = ∅ := by
    intro q
    apply if_neg
    rintro ⟨edge, hEdge, _, hLabel⟩
    exact hNoMarker edge hEdge hLabel
  have hLeftCopy : ∀ q, observe
      (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)) (.child 0 q) = ∅ := by
    intro q
    apply if_neg
    rw [compileTypeFuel_sequence_eq_build]
    intro hMarker
    obtain ⟨edge, hEdge, _, hLabel⟩ := buildSequenceAutomaton_markerSource_child0
      _ _ name q hMarker
    exact hNoMarker edge hEdge hLabel
  have hRightCopy : ∀ q, observe
      (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)) (.child 1 q) =
      observe (compileTypeFuel (typeCompilationFuel right) right) q := by
    intro q
    simp only [observe, compileTypeFuel_sequence_eq_build]
    congr 1
    exact propext (buildSequenceAutomaton_markerSource_child1 _ _ name q)
  have hMenus := compiledMenuFrom_sequence_left alphabet left right hLeftDisjoint hRightDisjoint
    (observe (compileTypeFuel (typeCompilationFuel left) left))
    (observe (compileTypeFuel (typeCompilationFuel right) right))
    (observe (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
      (.seq alphabet left right))) source hSource hRetained hComplete
    (fun q _ => hLeftEmpty q)
    (fun q _ _ => (hLeftCopy q).trans (hLeftEmpty q).symm)
    (fun q _ => hRightCopy q)
  have hObserve : ∀ (graph : FiniteMenuGraph) fragment q,
      ("", MessageDir.send) ∈ graph.menuFrom (observe fragment) q ↔
        ∃ reached ∈ graph.futureReachable q, MarkerSource fragment name reached := by
    intro graph fragment q
    simp only [FiniteMenuGraph.menuFrom, Finset.mem_biUnion]
    apply exists_congr
    intro reached
    apply and_congr_right
    intro _
    dsimp only [observe]
    split_ifs with h <;> simp [h]
  have hLeftMenu : (compiledMenuGraphFuel (typeCompilationFuel left) left).menuFrom
      (observe (compileTypeFuel (typeCompilationFuel left) left)) source = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hAction
    obtain ⟨q, _, hAction⟩ := Finset.mem_biUnion.mp hAction
    rw [hLeftEmpty] at hAction
    exact Finset.notMem_empty action hAction
  rw [← hObserve]
  rw [hMenus, hLeftMenu, Finset.empty_union]
  split_ifs with hFlag
  · simpa only [hFlag, true_and] using hObserve
      (compiledMenuGraphFuel (typeCompilationFuel right) right)
      (compileTypeFuel (typeCompilationFuel right) right) _
  · simp only [Finset.notMem_empty, hFlag, false_and]

/-- Right-component paths are copied unchanged, including inherited L links. -/
theorem menuMarkerReachable_sequence_right
    (alphabet : PactTypeAlphabet) (left right : PactType) (name : String)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (source : TypeAutomatonState)
    (hSource : source ∈ (compileTypeFuel (typeCompilationFuel right) right).states) :
    (∃ q ∈ (compiledMenuGraphFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)).futureReachable (.child 1 source),
      MarkerSource (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)) name q) ↔
      ∃ q ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable source,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name q := by
  let parent := compiledMenuGraphFuel (typeCompilationFuel (.seq alphabet left right))
    (.seq alphabet left right)
  let child := compiledMenuGraphFuel (typeCompilationFuel right) right
  have hRefs : ∀ q, parent.referencedStates (.child 1 q) =
      (child.referencedStates q).image (.child 1) := by
    intro q
    change (⟨(compileTypeFuel _ _).states, (compileTypeFuel _ _).edges⟩ :
      PendingAutomaton).menuStep (.child 1 q) ∪ menuDependencyTargets _ _ = _
    rw [compileTypeFuel_sequence_eq_build]
    simp only [Nat.min_self]
    rw [buildSequenceAutomaton_menuStep_right,
      menuDependencyTargets_seq_right alphabet left right]
    simp only [child, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      Nat.min_self, Finset.image_union]
  have hCard : child.states.card ≤ parent.states.card := by
    change (compileTypeFuel _ right).states.card ≤ (compileTypeFuel _ (.seq alphabet left right)).states.card
    rw [compileTypeFuel_sequence_eq_build]
    rw [← Finset.card_image_of_injective
      (compileTypeFuel (typeCompilationFuel right) right).states
      (show Function.Injective (childState 1) from fun _ _ h => by simpa [childState] using h)]
    apply Finset.card_le_card
    intro q hq
    exact Finset.mem_union_right _ hq
  have hReach := FiniteMenuGraph.futureReachable_eq_of_embedding child parent
    (.child 1) hRefs
    (compiledMenuGraphFuel_referencesClosed _ right le_rfl hRightDisjoint) source hSource hCard
  rw [hReach]
  simp only [Finset.mem_image, exists_exists_and_eq_and, compileTypeFuel_sequence_eq_build]
  apply exists_congr
  intro q
  apply and_congr_right
  intro _
  simpa only [childState] using buildSequenceAutomaton_markerSource_child1
    (compileTypeFuel (typeCompilationFuel left) left)
    (compileTypeFuel (typeCompilationFuel right) right) name q

/-- The sequence case of the paper's marker induction. -/
theorem markerReachable_iff_menuReachesVar_seq
    (alphabet : PactTypeAlphabet) (left right : PactType) (name : String)
    {bound : List String} (hWF : TypeWellFormedIn bound (.seq alphabet left right))
    (hLeftCurrent : CurrentOfferCorrespondence left)
    (hRight : ∀ {rho q}
      (_ : relationMembership (buildRelationSet right (compileType right)) rho q),
      (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel right) right).futureReachable q,
        MarkerSource (compileTypeFuel (typeCompilationFuel right) right) name reached) ↔
        menuReachesVar name rho = true)
    {rho q} (hRelated : relationMembership
      (buildRelationSet (.seq alphabet left right) (compileType (.seq alphabet left right))) rho q) :
    (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)).futureReachable q,
      MarkerSource (compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right)) name reached) ↔ menuReachesVar name rho = true := by
  obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
  have hLeftDisjoint := offerBranchesDisjoint_of_wellFormedIn hLeftWF
  have hRightDisjoint := offerBranchesDisjoint_of_wellFormedIn hRightWF
  have hLeftTail : ∀ name, left.TailOccurrences name False := fun name =>
    (show left.TailOccurrences name False ∧ right.TailOccurrences name True from
      by simpa only [PactType.TailOccurrences] using hWF.2.2.2.1 name).1
  rcases relationMembership_seq_cases alphabet left right hRelated with hLeft | hRightCase
  · obtain ⟨source, residual, hPair, hChild, hRetained⟩ := hLeft
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hPair
    have hKeep : source ∉ sequenceDeleted (compileTypeFuel (typeCompilationFuel left) left) := by
      rcases hRetained with hNotFinal | hInitial
      · exact not_mem_sequenceDeleted_of_not_accepting hNotFinal
      · exact hInitial ▸ initial_not_mem_sequenceDeleted _
    rw [menuMarkerReachable_sequence_left alphabet left right name hLeftDisjoint hRightDisjoint
      (compileTypeFuel_noMarkerFor name _ left (hLeftTail name)) source
      (relationMembership_state_mem left residual source hLeftDisjoint hChild) hKeep
      (completionFlag_backward_of_menuReachable left hLeftWF hLeftDisjoint
        (fun x => compileTypeFuel_noMarkerFor x _ left (hLeftTail x)) hLeftCurrent hChild),
      hRight (buildRelationSetCoreFuel_initial_mem _ right (typeCompilationFuel_sufficient right)),
      menuReachesVar_seq name alphabet residual right
        (relationMembership_tailOccurrences left residual source name False
          hLeftWF.2.2.2.2.2.1 (hLeftTail name) hChild) (hRightWF.2.2.2.1 name)]
    have hFlag : (∃ candidate, (candidate, source) ∈
        buildRelationSetCoreFuel (typeCompilationFuel left) left ∧
        typeCanCompleteThisCycleFuel (sizeOf candidate + 1) candidate = true) ↔
        residual.CanCompleteDeclared = true := by
      constructor
      · rintro ⟨candidate, hCandidate, hComplete⟩
        have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel left)
          left hCandidate hChild
        subst candidate
        rwa [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ residual (by omega)] at hComplete
      · intro hComplete
        refine ⟨residual, hChild, ?_⟩
        rwa [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ residual (by omega)]
    simp only [hFlag, Bool.and_eq_true]
  · obtain ⟨source, rfl, hChild⟩ := hRightCase
    rw [menuMarkerReachable_sequence_right alphabet left right name hRightDisjoint source
      (relationMembership_state_mem right rho source hRightDisjoint hChild)]
    exact hRight hChild

end

end Pact
