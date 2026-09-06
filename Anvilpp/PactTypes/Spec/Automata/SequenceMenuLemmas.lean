import Anvilpp.PactTypes.Spec.Automata.MenuDependencies

namespace Pact

noncomputable section

open Classical

namespace FiniteMenuGraph

/-- Saturate fixed contributions over the existing finite reference closure. -/
def menuFrom (graph : FiniteMenuGraph)
    (contribution : TypeAutomatonState → Finset BareMessage)
    (source : TypeAutomatonState) : Finset BareMessage :=
  (graph.futureReachable source).biUnion contribution

/-- The sequence equation in the paper, including optimistic continuation
links and the redirection of inherited links to left final states. -/
theorem menuFrom_sequence_left
    (left right parent : FiniteMenuGraph)
    (final deleted : Finset TypeAutomatonState)
    (initial source : TypeAutomatonState)
    (complete : TypeAutomatonState → Bool)
    (leftOffer rightOffer parentOffer : TypeAutomatonState → Finset BareMessage)
    (hLeftClosed : left.ReferencesClosed)
    (hRightClosed : right.ReferencesClosed)
    (hParentClosed : parent.ReferencesClosed)
    (hSource : source ∈ left.states)
    (hRetained : source ∉ deleted)
    (hInitial : initial ∈ right.states)
    (hDeleted : deleted ⊆ final)
    (hLeftStates : ∀ q ∈ left.states, q ∉ deleted →
      TypeAutomatonState.child 0 q ∈ parent.states)
    (hRightStates : ∀ q ∈ right.states,
      TypeAutomatonState.child 1 q ∈ parent.states)
    (hFinalClosed : ∀ q ∈ final, left.referencedStates q ⊆ final)
    (hFinalEmpty : ∀ q ∈ final, leftOffer q = ∅)
    (hFinalComplete : ∀ q ∈ final, complete q = true)
    (hComplete : ∀ q ∈ left.futureReachable source, ∀ r ∈ left.referencedStates q,
      complete r = true → complete q = true)
    (hLeftReferences : ∀ q ∈ left.states, q ∉ deleted →
      parent.referencedStates (.child 0 q) =
        (left.referencedStates q).image (fun r =>
          if r ∈ final then TypeAutomatonState.child 1 initial else .child 0 r) ∪
        if complete q then {TypeAutomatonState.child 1 initial} else ∅)
    (hRightReferences : ∀ q,
      parent.referencedStates (.child 1 q) =
        (right.referencedStates q).image (.child 1))
    (hLeftOffer : ∀ q ∈ left.states, q ∉ deleted →
      parentOffer (.child 0 q) = leftOffer q)
    (hRightOffer : ∀ q ∈ right.states,
      parentOffer (.child 1 q) = rightOffer q) :
    parent.menuFrom parentOffer (.child 0 source) =
      left.menuFrom leftOffer source ∪
        if complete source then right.menuFrom rightOffer initial else ∅ := by
  let leftReach := left.futureReachable source
  let rightReach := right.futureReachable initial
  let parentReach := parent.futureReachable (.child 0 source)
  have hParentSource := hLeftStates source hSource hRetained
  have hLeftCarrier : leftReach ⊆ left.states :=
    left.futureReachable_subset_of_reference_closed source left.states hSource hLeftClosed
  have hRightCarrier : rightReach ⊆ right.states :=
    right.futureReachable_subset_of_reference_closed initial right.states hInitial hRightClosed
  have hParentCarrier : parentReach ⊆ parent.states :=
    parent.futureReachable_subset_of_reference_closed _ parent.states hParentSource hParentClosed
  have hLeftStep : ∀ q ∈ leftReach, left.referencedStates q ⊆ leftReach := by
    intro q hq r hr
    exact left.futureReachable_subset_of_mem hLeftClosed hSource hq
      (left.referencedStates_subset_futureReachable q hLeftClosed (hLeftCarrier hq) hr)
  have hRightStep : ∀ q ∈ rightReach, right.referencedStates q ⊆ rightReach := by
    intro q hq r hr
    exact right.futureReachable_subset_of_mem hRightClosed hInitial hq
      (right.referencedStates_subset_futureReachable q hRightClosed (hRightCarrier hq) hr)
  have hParentStep : ∀ q ∈ parentReach, parent.referencedStates q ⊆ parentReach := by
    intro q hq r hr
    exact parent.futureReachable_subset_of_mem hParentClosed hParentSource hq
      (parent.referencedStates_subset_futureReachable q hParentClosed (hParentCarrier hq) hr)
  -- A crossing flag propagates backwards along a finite left derivation.
  have hFlag : ∀ q ∈ leftReach, complete q = true → complete source = true := by
    have hBound := left.futureReachable_subset_of_reference_closed source
      (leftReach.filter fun q => complete q = true → complete source = true)
      (by simp [leftReach, left.mem_futureReachable_self]) (by
        intro q hq r hr
        obtain ⟨hqReach, hqFlag⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨hLeftStep q hqReach hr, fun hc => hqFlag (hComplete q hqReach r hr hc)⟩)
    intro q hq
    exact (Finset.mem_filter.mp (hBound hq)).2
  apply Finset.Subset.antisymm
  · -- Forward: a contribution stays on the left or crosses when the flag holds.
    let allowed := (leftReach \ deleted).image (TypeAutomatonState.child 0) ∪
      if complete source then rightReach.image (TypeAutomatonState.child 1) else ∅
    have hBound : parentReach ⊆ allowed := by
      apply parent.futureReachable_subset_of_reference_closed _ allowed
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨source, Finset.mem_sdiff.mpr ⟨left.mem_futureReachable_self source, hRetained⟩, rfl⟩)
      · intro q hq r hr
        rcases Finset.mem_union.mp hq with hq | hq
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
          obtain ⟨hpReach, hpRetained⟩ := Finset.mem_sdiff.mp hp
          rw [hLeftReferences p (hLeftCarrier hpReach) hpRetained] at hr
          rcases Finset.mem_union.mp hr with hr | hr
          · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
            have htReach := hLeftStep p hpReach ht
            by_cases htFinal : t ∈ final
            · have hc := hFlag t htReach (hFinalComplete t htFinal)
              simp only [if_pos htFinal]
              exact Finset.mem_union_right _ (by
                simp only [hc, ↓reduceIte]
                exact Finset.mem_image.mpr
                  ⟨initial, right.mem_futureReachable_self initial, rfl⟩)
            · simp only [if_neg htFinal]
              exact Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨t, Finset.mem_sdiff.mpr ⟨htReach, fun h => htFinal (hDeleted h)⟩, rfl⟩)
          · by_cases hc : complete p = true
            · simp only [hc, ↓reduceIte, Finset.mem_singleton] at hr
              subst r
              exact Finset.mem_union_right _ (by
                simp only [hFlag p hpReach hc, ↓reduceIte]
                exact Finset.mem_image.mpr
                  ⟨initial, right.mem_futureReachable_self initial, rfl⟩)
            · simp [hc] at hr
        · by_cases hc : complete source = true
          · simp only [hc, ↓reduceIte] at hq
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
            rw [hRightReferences p] at hr
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
            exact Finset.mem_union_right _ (by
              simp only [hc, ↓reduceIte]
              exact Finset.mem_image.mpr ⟨t, hRightStep p hp ht, rfl⟩)
          · simp [hc] at hq
    intro action hAction
    obtain ⟨q, hq, ha⟩ := Finset.mem_biUnion.mp hAction
    rcases Finset.mem_union.mp (hBound hq) with hq | hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hpReach, hpRetained⟩ := Finset.mem_sdiff.mp hp
      rw [hLeftOffer p (hLeftCarrier hpReach) hpRetained] at ha
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, hpReach, ha⟩)
    · by_cases hc : complete source = true
      · simp only [hc, ↓reduceIte] at hq ⊢
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        rw [hRightOffer p (hRightCarrier hp)] at ha
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, ha⟩)
      · simp [hc] at hq
  · -- Backward: deleted finals offer nothing; the new link supplies the right menu.
    have hLift : ∀ q ∈ leftReach, q ∈ final ∨ .child 0 q ∈ parentReach := by
      have hBound := left.futureReachable_subset_of_reference_closed source
        (left.states.filter fun q => q ∈ final ∨ .child 0 q ∈ parentReach)
        (Finset.mem_filter.mpr ⟨hSource, Or.inr (parent.mem_futureReachable_self _)⟩) (by
          intro q hq r hr
          obtain ⟨hqState, hq⟩ := Finset.mem_filter.mp hq
          refine Finset.mem_filter.mpr ⟨hLeftClosed q hqState hr, ?_⟩
          by_cases hrFinal : r ∈ final
          · exact Or.inl hrFinal
          · rcases hq with hqFinal | hqReach
            · exact (hrFinal (hFinalClosed q hqFinal hr)).elim
            · by_cases hqFinal : q ∈ final
              · exact (hrFinal (hFinalClosed q hqFinal hr)).elim
              · right
                apply hParentStep (.child 0 q) hqReach
                rw [hLeftReferences q hqState (fun h => hqFinal (hDeleted h))]
                apply Finset.mem_union_left
                exact Finset.mem_image.mpr ⟨r, hr, by simp [hrFinal]⟩)
      intro q hq
      exact (Finset.mem_filter.mp (hBound hq)).2
    intro action hAction
    rcases Finset.mem_union.mp hAction with ha | ha
    · obtain ⟨q, hq, ha⟩ := Finset.mem_biUnion.mp ha
      by_cases hqFinal : q ∈ final
      · rw [hFinalEmpty q hqFinal] at ha
        exact (Finset.notMem_empty _ ha).elim
      · have hqReach := (hLift q hq).resolve_left hqFinal
        apply Finset.mem_biUnion.mpr
        refine ⟨.child 0 q, hqReach, ?_⟩
        rwa [hLeftOffer q (hLeftCarrier hq) (fun h => hqFinal (hDeleted h))]
    · by_cases hc : complete source = true
      · simp only [hc, ↓reduceIte] at ha
        obtain ⟨q, hq, ha⟩ := Finset.mem_biUnion.mp ha
        have hEntry : .child 1 initial ∈ parentReach := by
          apply parent.referencedStates_subset_futureReachable _ hParentClosed hParentSource
          rw [hLeftReferences source hSource hRetained]
          exact Finset.mem_union_right _ (by simp [hc])
        have hRightLift := right.futureReachable_image_subset_of_embedding parent (.child 1)
          (fun p => by rw [hRightReferences p]) hParentClosed initial (hRightStates initial hInitial)
        have hqParent : .child 1 q ∈ parentReach :=
          parent.futureReachable_subset_of_mem hParentClosed hParentSource hEntry
            (hRightLift (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
        apply Finset.mem_biUnion.mpr
        refine ⟨.child 1 q, hqParent, ?_⟩
        rwa [hRightOffer q (hRightCarrier hq)]
      · simp [hc] at ha

end FiniteMenuGraph

end

end Pact
