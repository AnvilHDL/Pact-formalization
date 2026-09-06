import Anvilpp.PactTypes.Spec.Automata.MarkerReachabilityDefs

namespace Pact

noncomputable section

theorem markerStoppedFragment_referencedStates_subset
    (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) :
    (markerStoppedFragment fragment name : AutomatonFragment).toPending.referencedStates
        state ⊆
      (fragment : AutomatonFragment).toPending.referencedStates state := by
  classical
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
    markerStoppedFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image] at hTarget ⊢
  rcases hTarget with
    ⟨edge, ⟨⟨original, hOriginal, hEdge⟩, hSource⟩, hReference⟩
  rw [← hEdge] at hSource hReference
  by_cases hMarker : original.label =
      AutomatonConstructionLabel.variable name
  · simp [hMarker] at hReference
  · simp only [if_neg hMarker] at hSource hReference
    exact ⟨original, ⟨hOriginal, hSource⟩, hReference⟩

theorem markerStoppedFragment_referencedStates_eq_of_not_markerSource
    (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState)
    (hNoMarker : ¬ MarkerSource fragment name state) :
    (markerStoppedFragment fragment name).toPending.referencedStates state =
      fragment.toPending.referencedStates state := by
  classical
  apply Finset.Subset.antisymm
  · exact markerStoppedFragment_referencedStates_subset fragment name state
  · intro target hTarget
    simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
      Finset.mem_biUnion, Finset.mem_filter] at hTarget
    rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    have hNotMarker : edge.label ≠
        AutomatonConstructionLabel.variable name := by
      intro hLabel
      exact hNoMarker ⟨edge, hEdge, hSource, hLabel⟩
    simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
      markerStoppedFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image]
    exact ⟨edge, ⟨⟨edge, hEdge, by simp [hNotMarker]⟩,
      by simp [hNotMarker, hSource]⟩, by simpa [hNotMarker] using hReference⟩

/-- Same-cycle references at a tagged child state are the tagged images of the
child's own references, whenever the constructor's outgoing edges there are
exactly the tagged child edges.  `childPendingEdge` preserves the label — hence
the clock test — and retags only `.at` references. -/
theorem referencedStates_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat)
    (state : TypeAutomatonState)
    (hOutgoing : ∀ edge : PendingAutomatonEdge,
      (edge ∈ parent.edges ∧ edge.source = childState index state) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧ edge = childPendingEdge index childEdge) :
    (⟨parent.states, parent.edges⟩ : PendingAutomaton).referencedStates
        (childState index state) =
      ((⟨child.states, child.edges⟩ : PendingAutomaton).referencedStates
        state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ :=
      (hOutgoing edge).mp ⟨hEdge, hSource⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos (by simpa [childPendingEdge] using hTock)] at hTarget
      simp at hTarget
    · rw [if_neg (by simpa [childPendingEdge] using hTock)] at hTarget
      cases hSpec : childEdge.future with
      | explicit offers =>
          rw [show (childPendingEdge index childEdge).future = .explicit offers
            by simp [childPendingEdge, hSpec, childFutureSpec]] at hTarget
          simp at hTarget
      | «at» inner removed =>
          rw [show (childPendingEdge index childEdge).future =
            .at (childState index inner) removed by
              simp [childPendingEdge, hSpec, childFutureSpec]] at hTarget
          rw [Finset.mem_singleton] at hTarget
          subst hTarget
          exact ⟨inner, ⟨childEdge, ⟨hChildEdge, hChildSource⟩, by
            simp [if_neg hTock, hSpec]⟩, rfl⟩
  · rintro ⟨inner, ⟨childEdge, ⟨hChildEdge, hChildSource⟩, hInner⟩, rfl⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hInner
      simp at hInner
    · rw [if_neg hTock] at hInner
      cases hSpec : childEdge.future with
      | explicit offers =>
          rw [hSpec] at hInner
          simp at hInner
      | «at» dest removed =>
          rw [hSpec, Finset.mem_singleton] at hInner
          obtain ⟨hEdge, hSource⟩ :=
            (hOutgoing (childPendingEdge index childEdge)).mpr
              ⟨childEdge, hChildEdge, hChildSource, rfl⟩
          refine ⟨childPendingEdge index childEdge, ⟨hEdge, hSource⟩, ?_⟩
          rw [if_neg (by simpa [childPendingEdge] using hTock),
            show (childPendingEdge index childEdge).future =
              .at (childState index dest) removed by
                simp [childPendingEdge, hSpec, childFutureSpec]]
          simp [hInner]

end

end Pact
