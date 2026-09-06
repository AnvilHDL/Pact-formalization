import Anvilpp.PactTypes.Spec.Automata.BuildChoiceAutomatonDefs

namespace Pact

noncomputable section

theorem buildChoiceAutomaton_outgoing_left
     (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ left.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

theorem buildChoiceAutomaton_outgoing_right
     (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

/-- Selection edges carry an explicit `clock = false` guard, and both tagged
child copies preserve their child's environment and label. -/
theorem buildChoiceAutomaton_clockEdgesAreTock
     (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftClock : left.ClockEdgesAreTock)
    (hRightClock : right.ClockEdgesAreTock) :
    (buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, hChildEdge, rfl⟩
    exact hLeftClock childEdge hChildEdge hClock
  · rcases hRight with ⟨childEdge, hChildEdge, rfl⟩
    exact hRightClock childEdge hChildEdge hClock
  · rcases hSelection with ⟨environment, ⟨_, hNotClock⟩, rfl | rfl⟩ <;>
      · exfalso
        rw [hNotClock] at hClock
        exact absurd hClock (by simp)

theorem buildChoiceAutomaton_futureTargetsInStates
     (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight).FutureTargetsInStates := by
  classical
  intro edge hEdge target hFuture
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hLeftTargets childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
    | atUnion offers childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hLeftTargets childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hRight with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hRightTargets childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
    | atUnion offers childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hRightTargets childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hLeftInitial]
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hRightInitial]

/-- The edges leaving a binary-choice root are exactly its two selection edges,
one per non-clock local environment. -/
theorem buildChoiceAutomaton_outgoing_root
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    (edge ∈ choice.edges ∧ edge.source = .root) ↔
      ∃ environment ∈ alphabet.localEnvironments.filter
          fun environment => environment.clock = false,
        edge = { source := TypeAutomatonState.root
                 environment := environment
                 label := .visible selectionLeft
                 current := ∅
                 future := .at TypeAutomatonState.root ∅
                 target := childState 0 left.initial } ∨
          edge = { source := TypeAutomatonState.root
                   environment := environment
                   label := .visible selectionRight
                   current := ∅
                   future := .at TypeAutomatonState.root ∅
                   target := childState 1 right.initial } := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, hEnvironment, hEdge | hEdge⟩
      · exact ⟨environment, Finset.mem_filter.mpr hEnvironment, Or.inl hEdge⟩
      · exact ⟨environment, Finset.mem_filter.mpr hEnvironment, Or.inr hEdge⟩
  · rintro ⟨environment, hEnvironment, hEdge | hEdge⟩ <;>
      subst hEdge <;>
      refine ⟨?_, rfl⟩ <;>
      · simp only [buildChoiceAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton]
        refine Or.inr ⟨environment, Finset.mem_filter.mp hEnvironment, ?_⟩
        simp

/-- A binary-choice root offers nothing directly: both selection edges carry an
empty current offer and a symbolic future. -/
theorem buildChoiceAutomaton_offersAt_root
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    ({ states := choice.states, edges := choice.edges } :
      PendingAutomaton).offersAt TypeAutomatonState.root = ∅ := by
  classical
  intro choice
  refine Finset.eq_empty_of_forall_notMem ?_
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hAction
  obtain ⟨environment, -, hShape | hShape⟩ :=
    (buildChoiceAutomaton_outgoing_root alphabet left right selectionLeft
      selectionRight edge).mp ⟨hEdge, hSource⟩ <;>
    · subst hShape
      simp at hIn

/-- Both selection fields refer to the unresolved source menu. -/
theorem buildChoiceAutomaton_referencedStates_root
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftNotTock : selectionLeft ≠ TypeLabel.tock)
    (hRightNotTock : selectionRight ≠ TypeLabel.tock)
    (hEnvironment : ∃ environment ∈ alphabet.localEnvironments,
      environment.clock = false) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    ({ states := choice.states, edges := choice.edges } :
        PendingAutomaton).referencedStates TypeAutomatonState.root =
      {TypeAutomatonState.root} := by
  classical
  intro choice
  obtain ⟨environment, hMem, hClock⟩ := hEnvironment
  have hFilter : environment ∈ alphabet.localEnvironments.filter
      fun environment => environment.clock = false :=
    Finset.mem_filter.mpr ⟨hMem, hClock⟩
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hIn⟩
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hIn
      exact absurd hIn (Finset.notMem_empty _)
    · rw [if_neg hTock] at hIn
      obtain ⟨environment', -, hShape | hShape⟩ :=
        (buildChoiceAutomaton_outgoing_root alphabet left right selectionLeft
          selectionRight edge).mp ⟨hEdge, hSource⟩ <;>
        · subst hShape
          simp only [Finset.mem_singleton] at hIn
          simp [hIn]
  · intro hTarget
    rcases hTarget with rfl
    refine ⟨{ source := TypeAutomatonState.root
              environment := environment
              label := .visible selectionLeft
              current := ∅
              future := .at TypeAutomatonState.root ∅
              target := childState 0 left.initial }, ?_, ?_⟩
    · exact (buildChoiceAutomaton_outgoing_root alphabet left right
        selectionLeft selectionRight _).mpr ⟨environment, hFilter, Or.inl rfl⟩
    · rw [if_neg (by simpa using hLeftNotTock)]
      exact Finset.mem_singleton_self _

/-- The menu graph nevertheless reaches both branch entries. -/
theorem buildChoiceAutomaton_menuStep_root
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftNotTock : selectionLeft ≠ TypeLabel.tock)
    (hRightNotTock : selectionRight ≠ TypeLabel.tock)
    (hEnvironment : ∃ environment ∈ alphabet.localEnvironments,
      environment.clock = false) :
    let choice := buildChoiceAutomaton alphabet left right
      selectionLeft selectionRight
    ({ states := choice.states, edges := choice.edges } :
        PendingAutomaton).menuStep .root =
      {childState 0 left.initial, childState 1 right.initial} := by
  classical
  intro choice
  obtain ⟨environment, hMem, hClock⟩ := hEnvironment
  have hFilter : environment ∈ alphabet.localEnvironments.filter
      fun environment => environment.clock = false :=
    Finset.mem_filter.mpr ⟨hMem, hClock⟩
  ext target
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hIn⟩
    obtain ⟨environment', -, hShape | hShape⟩ :=
      (buildChoiceAutomaton_outgoing_root alphabet left right selectionLeft
        selectionRight edge).mp ⟨hEdge, hSource⟩
    · subst edge
      exact Or.inl (by simpa [AutomatonConstructionLabel.semantic, hLeftNotTock] using hIn)
    · subst edge
      exact Or.inr (by simpa [AutomatonConstructionLabel.semantic, hRightNotTock] using hIn)
  · rintro (rfl | rfl)
    · refine ⟨{ source := .root, environment := environment,
                label := .visible selectionLeft, current := ∅,
                future := .at .root ∅, target := childState 0 left.initial }, ?_, ?_⟩
      · exact (buildChoiceAutomaton_outgoing_root alphabet left right
          selectionLeft selectionRight _).mpr ⟨environment, hFilter, Or.inl rfl⟩
      · simpa [AutomatonConstructionLabel.semantic, hLeftNotTock]
    · refine ⟨{ source := .root, environment := environment,
                label := .visible selectionRight, current := ∅,
                future := .at .root ∅, target := childState 1 right.initial }, ?_, ?_⟩
      · exact (buildChoiceAutomaton_outgoing_root alphabet left right
          selectionLeft selectionRight _).mpr ⟨environment, hFilter, Or.inr rfl⟩
      · simpa [AutomatonConstructionLabel.semantic, hRightNotTock]

end

end Pact
