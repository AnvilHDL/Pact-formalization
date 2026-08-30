import Anvilpp.PactTypes.Automata.BuildRecursionAutomaton

/-!
# buildChoiceAutomaton
-/

namespace Pact

noncomputable section

/--
Build a binary choice.

`Q` contains a fresh root and tagged copies of both child state sets. Selection
edges leave the root, and the accepting states are the union of both children.
The supplied labels distinguish ordinary epsilon choice from fair choice.
-/
def buildChoiceAutomaton (signature : TypeAlphabet)
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment) (selectionLeft selectionRight : TypeLabel) :
    AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 left ∪ childStates 1 right
  let accepting := childAccepting 0 left ∪ childAccepting 1 right
  let selections := ((signature.localEnvironmentsFor alphabet).filter
      fun environment => environment.clock = false).biUnion fun environment =>
    { { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionLeft
        current := ∅
        future := .at (childState 0 left.initial) ∅
        target := childState 0 left.initial },
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionRight
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial } }
  finishAutomatonFragment states .root accepting
    (childPendingEdges 0 left ∪ childPendingEdges 1 right ∪ selections)

theorem buildChoiceAutomaton_outgoing_left
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature alphabet left right
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature alphabet left right
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

private theorem buildChoiceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature alphabet left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.referencedStates (.child 0 state) =
      (child.referencedStates state).image (.child 0) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_left signature alphabet left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature alphabet left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_right signature alphabet left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_left
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature alphabet left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.offersAt (.child 0 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_left signature alphabet left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_right
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature alphabet left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_right signature alphabet left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind



/-- Marker reachability inside the left tagged child of a choice is exactly the
child fragment's own marker reachability. -/
theorem buildChoiceAutomaton_markerReachable_left
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (state : TypeAutomatonState)
    (hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ left.states)
    (hCard : left.states.card ≤
      (buildChoiceAutomaton signature alphabet left right
        selectionLeft selectionRight).states.card) :
    MarkerReachable (buildChoiceAutomaton signature alphabet left right
        selectionLeft selectionRight) name (.child 0 state) ↔
      MarkerReachable left name state := by
  have hResult := markerReachable_of_embedding left
    (buildChoiceAutomaton signature alphabet left right selectionLeft selectionRight)
    name (childState 0)
    (fun current => buildChoiceAutomaton_referencedStates_left signature alphabet left
      right selectionLeft selectionRight current)
    hClosed hCard
    (fun current _ => markerSource_of_outgoing_childPendingEdge _ left 0 name
      current (fun edge => buildChoiceAutomaton_outgoing_left signature alphabet left
        right selectionLeft selectionRight current edge))
    state hState
  simpa [childState] using hResult

/-- Marker reachability inside the right tagged child of a choice is exactly
the child fragment's own marker reachability. -/
theorem buildChoiceAutomaton_markerReachable_right
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildChoiceAutomaton signature alphabet left right
        selectionLeft selectionRight).states.card) :
    MarkerReachable (buildChoiceAutomaton signature alphabet left right
        selectionLeft selectionRight) name (.child 1 state) ↔
      MarkerReachable right name state := by
  have hResult := markerReachable_of_embedding right
    (buildChoiceAutomaton signature alphabet left right selectionLeft selectionRight)
    name (childState 1)
    (fun current => buildChoiceAutomaton_referencedStates_right signature alphabet left
      right selectionLeft selectionRight current)
    hClosed hCard
    (fun current _ => markerSource_of_outgoing_childPendingEdge _ right 1 name
      current (fun edge => buildChoiceAutomaton_outgoing_right signature alphabet left
        right selectionLeft selectionRight current edge))
    state hState
  simpa [childState] using hResult

/-- Selection edges carry an explicit `clock = false` guard, and both tagged
child copies preserve their child's environment and label. -/
theorem buildChoiceAutomaton_clockEdgesAreTock
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftClock : left.ClockEdgesAreTock)
    (hRightClock : right.ClockEdgesAreTock) :
    (buildChoiceAutomaton signature alphabet left right
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton signature alphabet left right
      selectionLeft selectionRight).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hLeftTargets childEdge hChildEdge
          childTarget removed hSpec
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hRight with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hRightTargets childEdge hChildEdge
          childTarget removed hSpec
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

end

end Pact
