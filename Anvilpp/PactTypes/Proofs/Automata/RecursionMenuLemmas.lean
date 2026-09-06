import Anvilpp.PactTypes.Proofs.Automata.MenuDependenciesLemmas
import Anvilpp.PactTypes.Spec.Automata.SequenceMenuLemmas
import Anvilpp.PactTypes.Proofs.Automata.BuildRecursionAutomatonLemmas

namespace Pact

noncomputable section

open Classical

/-- Recursion copies L unchanged. Only an installed marker adds a reference
to the body entry. -/
theorem mem_buildRecursionAutomaton_menuReferences_child
    (alphabet : PactTypeAlphabet) (name : String) (body : AutomatonFragment)
    (links : Finset (TypeAutomatonState × TypeAutomatonState))
    (q target : TypeAutomatonState) :
    target ∈ ((buildRecursionAutomaton alphabet name body).toPending.withMenuDependencies
      (links.image fun link => (.child 0 link.1, .child 0 link.2))).referencedStates
        (.child 0 q) ↔
      (∃ inner ∈ ((markerStoppedFragment body name).toPending.withMenuDependencies
        links).referencedStates q, target = .child 0 inner) ∨
      (MarkerSource body name q ∧ target = .child 0 body.initial) := by
  simp only [PendingAutomaton.withMenuDependencies, Finset.mem_union,
    menuDependencyTargets_child, ite_true, Finset.mem_image]
  have hOld := mem_buildRecursionAutomaton_referencedStates_child alphabet name body q target
  change (target ∈ (buildRecursionAutomaton alphabet name body).toPending.referencedStates
    (.child 0 q) ↔ _) at hOld
  rw [hOld]
  simp only [childState]
  aesop

namespace FiniteMenuGraph

/-- Removing references from states with empty menus loses no contribution.
The retained paths carry `represented`; a discarded path has an empty menu. -/
theorem menuFrom_eq_of_pruning (original retained : FiniteMenuGraph)
    (contribution : TypeAutomatonState → Finset BareMessage)
    (represented : TypeAutomatonState → Prop)
    (hStates : retained.states = original.states)
    (hClosed : original.ReferencesClosed)
    (hSubset : ∀ q, retained.referencedStates q ⊆ original.referencedStates q)
    (hStep : ∀ q, represented q → ∀ t ∈ original.referencedStates q,
      (represented t ∧ t ∈ retained.referencedStates q) ∨
        original.menuFrom contribution q = ∅)
    (source : TypeAutomatonState) (hSource : source ∈ original.states)
    (hRepresented : represented source) :
    retained.menuFrom contribution source = original.menuFrom contribution source := by
  have hRetainedClosed : retained.ReferencesClosed := by
    intro q hq t ht
    rw [hStates] at hq ⊢
    exact hClosed q hq (hSubset q ht)
  have hMenuMono : ∀ q ∈ original.states, ∀ t ∈ original.referencedStates q,
      original.menuFrom contribution t ⊆ original.menuFrom contribution q := by
    intro q hq t ht
    have hReach := original.futureReachable_subset_of_mem hClosed hq
      (original.referencedStates_subset_futureReachable q hClosed hq ht)
    intro action ha
    obtain ⟨s, hs, ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨s, hReach hs, ha⟩
  have hEmpty : ∀ q ∈ original.states, original.menuFrom contribution q = ∅ →
      ∀ t ∈ original.referencedStates q, original.menuFrom contribution t = ∅ := by
    intro q hq he t ht
    exact Finset.eq_empty_iff_forall_notMem.mpr fun a ha => by
      have h := hMenuMono q hq t ht ha
      rw [he] at h
      exact Finset.notMem_empty a h
  let allowed := original.states.filter fun q =>
    (q ∈ retained.futureReachable source ∧ represented q) ∨
      original.menuFrom contribution q = ∅
  have hBound : original.futureReachable source ⊆ allowed := by
    apply original.futureReachable_subset_of_reference_closed source allowed
    · exact Finset.mem_filter.mpr ⟨hSource,
        Or.inl ⟨retained.mem_futureReachable_self source, hRepresented⟩⟩
    · intro q hq t ht
      obtain ⟨hqState, hq⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨hClosed q hqState ht, ?_⟩
      rcases hq with ⟨hReach, hRep⟩ | he
      · rcases hStep q hRep t ht with ⟨hRepT, hRetained⟩ | he
        · exact Or.inl ⟨retained.futureReachable_subset_of_mem hRetainedClosed
            (hStates.symm ▸ hSource) hReach
            (retained.referencedStates_subset_futureReachable q hRetainedClosed
              (hStates.symm ▸ hqState) hRetained), hRepT⟩
        · exact Or.inr (hEmpty q hqState he t ht)
      · exact Or.inr (hEmpty q hqState he t ht)
  apply Finset.Subset.antisymm
  · have hReach := futureReachable_image_subset_of_embedding retained original id
      (by intro q; simpa using hSubset q) hClosed source hSource
    have hSubsetReach : retained.futureReachable source ⊆ original.futureReachable source :=
      by simpa using hReach
    intro action ha
    obtain ⟨s, hs, ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨s, hSubsetReach hs, ha⟩
  · intro action ha
    obtain ⟨q, hq, ha⟩ := Finset.mem_biUnion.mp ha
    rcases (Finset.mem_filter.mp (hBound hq)).2 with ⟨hReach, _⟩ | he
    · exact Finset.mem_biUnion.mpr ⟨q, hReach, ha⟩
    · have hSelf : action ∈ original.menuFrom contribution q :=
        Finset.mem_biUnion.mpr ⟨q, original.mem_futureReachable_self q, ha⟩
      rw [he] at hSelf
      exact False.elim (Finset.notMem_empty action hSelf)

/-- Cut a finite reference path at its first installed backedge. -/
theorem futureReachable_recur_child (body parent : FiniteMenuGraph)
    (entry source : TypeAutomatonState) (marker : TypeAutomatonState → Prop)
    (hBodyClosed : body.ReferencesClosed) (hParentClosed : parent.ReferencesClosed)
    (hEntry : entry ∈ body.states) (hSource : source ∈ body.states)
    (hCarrier : ∀ q ∈ body.states, TypeAutomatonState.child 0 q ∈ parent.states)
    (hReferences : ∀ q target,
      target ∈ parent.referencedStates (.child 0 q) ↔
        (∃ inner ∈ body.referencedStates q, target = .child 0 inner) ∨
        (marker q ∧ target = .child 0 entry)) :
    parent.futureReachable (.child 0 source) =
      ((body.futureReachable source) ∪
        if ∃ q ∈ body.futureReachable source, marker q
        then body.futureReachable entry else ∅).image (.child 0) := by
  have hLift : ∀ q ∈ body.states,
      (body.futureReachable q).image (.child 0) ⊆
        parent.futureReachable (.child 0 q) := by
    intro q hq
    apply futureReachable_image_subset_of_embedding body parent (.child 0)
      _ hParentClosed q (hCarrier q hq)
    intro s t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact (hReferences s _).mpr (Or.inl ⟨u, hu, rfl⟩)
  have hClosed : ∀ q ∈ body.states, ∀ s ∈ body.futureReachable q,
      body.referencedStates s ⊆ body.futureReachable q := by
    intro q hq s hs
    have hS := body.futureReachable_subset_of_reference_closed q body.states
      hq hBodyClosed hs
    exact (body.referencedStates_subset_futureReachable s hBodyClosed hS).trans
      (body.futureReachable_subset_of_mem hBodyClosed hq hs)
  by_cases hMarker : ∃ q ∈ body.futureReachable source, marker q
  · rw [if_pos hMarker]
    apply Finset.Subset.antisymm
    · apply parent.futureReachable_subset_of_reference_closed
      · exact Finset.mem_image.mpr ⟨source,
          Finset.mem_union_left _ (body.mem_futureReachable_self _), rfl⟩
      · intro s hs t ht
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
        rcases (hReferences u t).mp ht with ⟨v, hv, rfl⟩ | ⟨_, rfl⟩
        · refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          rcases Finset.mem_union.mp hu with hu | hu
          · exact Finset.mem_union_left _ (hClosed source hSource u hu hv)
          · exact Finset.mem_union_right _ (hClosed entry hEntry u hu hv)
        · exact Finset.mem_image.mpr ⟨entry,
            Finset.mem_union_right _ (body.mem_futureReachable_self _), rfl⟩
    · rw [Finset.image_union]
      apply Finset.union_subset (hLift source hSource)
      obtain ⟨q, hq, hm⟩ := hMarker
      have hqReach := hLift source hSource (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      have hqState := body.futureReachable_subset_of_reference_closed source body.states
        hSource hBodyClosed hq
      have hBack := parent.referencedStates_subset_futureReachable (.child 0 q)
        hParentClosed (hCarrier q hqState)
        ((hReferences q _).mpr (Or.inr ⟨hm, rfl⟩))
      have hEntryReach := parent.futureReachable_subset_of_mem hParentClosed
        (hCarrier source hSource) hqReach hBack
      exact (hLift entry hEntry).trans
        (parent.futureReachable_subset_of_mem hParentClosed
          (hCarrier source hSource) hEntryReach)
  · rw [if_neg hMarker, Finset.union_empty]
    apply Finset.Subset.antisymm
    · apply parent.futureReachable_subset_of_reference_closed
      · exact Finset.mem_image.mpr ⟨source, body.mem_futureReachable_self _, rfl⟩
      · intro s hs t ht
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
        rcases (hReferences u t).mp ht with ⟨v, hv, rfl⟩ | ⟨hm, _⟩
        · exact Finset.mem_image.mpr ⟨v, hClosed source hSource u hu hv, rfl⟩
        · exact False.elim (hMarker ⟨u, hu, hm⟩)
    · exact hLift source hSource

end FiniteMenuGraph

/-- The first visit to a marker source precedes any reference removed there.
The same argument applies when the graph also contains optimistic L links. -/
theorem markerStoppedFragment_menuMarkerReachable_self
    (fragment : AutomatonFragment) (name : String)
    (links : Finset (TypeAutomatonState × TypeAutomatonState))
    (hClosed : fragment.toPending.ReferencesClosed)
    (hTargets : ∀ link ∈ links, link.2 ∈ fragment.states)
    (source : TypeAutomatonState) (hSource : source ∈ fragment.states) :
    (∃ q ∈ ((markerStoppedFragment fragment name).toPending.withMenuDependencies
      links).futureReachable source, MarkerSource fragment name q) ↔
    (∃ q ∈ (fragment.toPending.withMenuDependencies links).futureReachable source,
      MarkerSource fragment name q) := by
  let original := fragment.toPending.withMenuDependencies links
  let stopped := (markerStoppedFragment fragment name).toPending.withMenuDependencies links
  have hOriginalClosed : original.ReferencesClosed :=
    PendingAutomaton.referencesClosed_withMenuDependencies _ links hClosed hTargets
  have hSubset : ∀ q, stopped.referencedStates q ⊆ original.referencedStates q :=
    fun q => Finset.union_subset_union
      (markerStoppedFragment_referencedStates_subset fragment name q) (Finset.Subset.refl _)
  have hStoppedClosed : stopped.ReferencesClosed := by
    intro q hq t ht
    exact hOriginalClosed q hq (hSubset q ht)
  constructor
  · rintro ⟨q, hq, hm⟩
    have hReach := FiniteMenuGraph.futureReachable_image_subset_of_embedding stopped original id
      (by intro q; simpa using hSubset q) hOriginalClosed source hSource
    exact ⟨q, hReach (by simpa using hq), hm⟩
  · rintro ⟨q, hq, hm⟩
    by_contra hNone
    have hBound : original.futureReachable source ⊆ stopped.futureReachable source := by
      apply original.futureReachable_subset_of_reference_closed source
        (stopped.futureReachable source) (stopped.mem_futureReachable_self source)
      intro s hs t ht
      have hNot : ¬ MarkerSource fragment name s := fun h => hNone ⟨s, hs, h⟩
      have hRefs : original.referencedStates s = stopped.referencedStates s := by
        change fragment.toPending.referencedStates s ∪ _ =
          (markerStoppedFragment fragment name).toPending.referencedStates s ∪ _
        rw [markerStoppedFragment_referencedStates_eq_of_not_markerSource fragment name s hNot]
      rw [hRefs] at ht
      have hState := stopped.futureReachable_subset_of_reference_closed source stopped.states
        hSource hStoppedClosed hs
      exact stopped.futureReachable_subset_of_mem hStoppedClosed hSource hs
        (stopped.referencedStates_subset_futureReachable s hStoppedClosed hState ht)
    exact hNone ⟨q, hBound hq, hm⟩

/-- Instantiate the path split with the unchanged recursion construction. -/
theorem buildRecursionAutomaton_menuReachable_child
    (alphabet : PactTypeAlphabet) (name : String) (body : AutomatonFragment)
    (links : Finset (TypeAutomatonState × TypeAutomatonState))
    (hBodyClosed : body.toPending.ReferencesClosed)
    (hTargets : ∀ link ∈ links, link.2 ∈ body.states)
    (hInitial : body.initial ∈ body.states)
    (source : TypeAutomatonState) (hSource : source ∈ body.states) :
    let stopped := (markerStoppedFragment body name).toPending.withMenuDependencies links
    let parent := (buildRecursionAutomaton alphabet name body).toPending.withMenuDependencies
      (links.image fun link => (.child 0 link.1, .child 0 link.2))
    parent.futureReachable (.child 0 source) =
      (stopped.futureReachable source ∪
        if ∃ q ∈ stopped.futureReachable source, MarkerSource body name q
        then stopped.futureReachable body.initial else ∅).image (.child 0) := by
  intro stopped parent
  have hStoppedClosed : stopped.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_withMenuDependencies
    · intro q hq t ht
      exact hBodyClosed q hq
        (markerStoppedFragment_referencedStates_subset body name q ht)
    · exact hTargets
  have hCarrier : ∀ q ∈ stopped.states, TypeAutomatonState.child 0 q ∈ parent.states := by
    intro q hq
    change TypeAutomatonState.child 0 q ∈ (buildRecursionAutomaton alphabet name body).states
    simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hRefs := mem_buildRecursionAutomaton_menuReferences_child alphabet name body links
  have hParentClosed : parent.ReferencesClosed := by
    intro q hq t ht
    have hq' : q = .root ∨ ∃ s ∈ body.states, q = .child 0 s := by
      change q ∈ (buildRecursionAutomaton alphabet name body).states at hq
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_singleton] at hq
      rcases hq with hq | hq
      · exact Or.inl hq
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
        exact Or.inr ⟨s, hs, rfl⟩
    rcases hq' with rfl | ⟨s, hs, rfl⟩
    · have hRoot : parent.referencedStates .root = {.child 0 body.initial} := by
        change (buildRecursionAutomaton alphabet name body).toPending.referencedStates .root ∪
          menuDependencyTargets _ .root = _
        rw [menuDependencyTargets_child_root, Finset.union_empty]
        exact buildRecursionAutomaton_referencedStates_root alphabet name body
      rw [hRoot, Finset.mem_singleton] at ht
      subst t
      exact hCarrier body.initial hInitial
    · rcases (hRefs s t).mp ht with ⟨u, hu, rfl⟩ | ⟨_, rfl⟩
      · exact hCarrier u (hStoppedClosed s hs hu)
      · exact hCarrier body.initial hInitial
  exact FiniteMenuGraph.futureReachable_recur_child stopped parent body.initial source
    (MarkerSource body name) hStoppedClosed hParentClosed hInitial hSource hCarrier hRefs

end

end Pact
