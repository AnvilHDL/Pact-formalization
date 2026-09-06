import Anvilpp.PactTypes.Spec.Automata.BuildSequenceAutomatonDefs

namespace Pact

noncomputable section

theorem mem_sequenceDeleted_iff {left : AutomatonFragment}
    {state : TypeAutomatonState} :
    state ∈ sequenceDeleted left ↔
      state ∈ left.accepting ∧ state ≠ left.initial := by
  simp [sequenceDeleted]

/-- The left entry survives the deletion even when it is itself accepting. -/
@[simp] theorem initial_not_mem_sequenceDeleted (left : AutomatonFragment) :
    left.initial ∉ sequenceDeleted left := by
  simp [sequenceDeleted]

theorem not_mem_sequenceDeleted_of_not_accepting {left : AutomatonFragment}
    {state : TypeAutomatonState} (hNotAccepting : state ∉ left.accepting) :
    state ∉ sequenceDeleted left := fun hDeleted =>
  hNotAccepting (mem_sequenceDeleted_iff.mp hDeleted).1

/-- Edges leaving a right-child state are exactly the copied edges of the
right fragment. Neither the left-edge nor redirect clause can have a
`.child 1` source. -/
theorem buildSequenceAutomaton_outgoing_right
     (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    edge ∈ (buildSequenceAutomaton left right).edges ∧
        edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceLeftEdges,
      sequenceRightEdges, sequenceRedirectEdges, childPendingEdges,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with (hLeft | hRight) | hRedirect
    · rcases hLeft with ⟨childEdge, _, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [sequenceKeptLeftEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rcases hRedirect with ⟨childEdge, _, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [sequenceRedirectEdge, childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment, sequenceRightEdges,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

/-! ### `sequenceRedirect` / sequence edge API

The two rewrite lemmas below let downstream proofs avoid ever unfolding the
`if`, and the field lemmas record that the sequence clauses preserve the
environment, label, and current offers from the left child. -/

@[simp] theorem sequenceRedirect_of_accepting {left right : AutomatonFragment}
    {state : TypeAutomatonState} (hAccepting : state ∈ left.accepting) :
    sequenceRedirect left right state = childState 1 right.initial := by
  simp [sequenceRedirect, hAccepting]

@[simp] theorem sequenceRedirect_of_not_accepting {left right : AutomatonFragment}
    {state : TypeAutomatonState} (hKept : state ∉ left.accepting) :
    sequenceRedirect left right state = childState 0 state := by
  simp [sequenceRedirect, hKept]

@[simp] theorem sequenceLeftEdge_source (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).source = childState 0 edge.source := by
  by_cases hAccepting : edge.target ∈ left.accepting
  · simp [sequenceLeftEdge, sequenceRedirectEdge, hAccepting]
  · simp [sequenceLeftEdge, sequenceKeptLeftEdge, hAccepting]

@[simp] theorem sequenceLeftEdge_environment (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).environment = edge.environment := by
  by_cases hAccepting : edge.target ∈ left.accepting
  · simp [sequenceLeftEdge, sequenceRedirectEdge, hAccepting]
  · simp [sequenceLeftEdge, sequenceKeptLeftEdge, hAccepting]

@[simp] theorem sequenceLeftEdge_label (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).label = edge.label := by
  by_cases hAccepting : edge.target ∈ left.accepting
  · simp [sequenceLeftEdge, sequenceRedirectEdge, hAccepting]
  · simp [sequenceLeftEdge, sequenceKeptLeftEdge, hAccepting]

@[simp] theorem sequenceLeftEdge_current (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).current = edge.current := by
  by_cases hAccepting : edge.target ∈ left.accepting
  · simp [sequenceLeftEdge, sequenceRedirectEdge, hAccepting]
  · simp [sequenceLeftEdge, sequenceKeptLeftEdge, hAccepting]

@[simp] theorem sequenceLeftEdge_target (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).target =
      sequenceRedirect left right edge.target := by
  by_cases hAccepting : edge.target ∈ left.accepting
  · simp [sequenceLeftEdge, sequenceRedirectEdge, sequenceRedirect, hAccepting]
  · simp [sequenceLeftEdge, sequenceKeptLeftEdge, sequenceRedirect, hAccepting]

/-- Invariant 2, in the form every reachability lemma needs: a redirected
state is always a state of the sequence fragment, provided the original was a
left state or a left edge target. -/
theorem sequenceRedirect_mem_states
    (left right : AutomatonFragment)
    (hRightInitial : right.initial ∈ right.states)
    (state : TypeAutomatonState)
    (hState : state ∈ left.states) :
    sequenceRedirect left right state ∈
      (buildSequenceAutomaton left right).states := by
  classical
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, childStates, childState,
    sequenceRedirect]
  by_cases hAccepting : state ∈ left.accepting
  · rw [if_pos hAccepting]
    exact Or.inr ⟨right.initial, hRightInitial, rfl⟩
  · rw [if_neg hAccepting]
    have hKept : state ∉ sequenceDeleted left :=
      not_mem_sequenceDeleted_of_not_accepting hAccepting
    exact Or.inl ⟨state, Finset.mem_sdiff.mpr ⟨hState, hKept⟩, rfl⟩

/-- All three sequence clauses copy the child edge's environment, label, and
current offers verbatim; only the target and future field are rebuilt. -/
theorem buildSequenceAutomaton_clockEdgesAreTock
     (left right : AutomatonFragment)
    (hLeftClock : left.ClockEdgesAreTock)
    (hRightClock : right.ClockEdgesAreTock) :
    (buildSequenceAutomaton left right).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · rcases hLeft with ⟨leftEdge, ⟨hLeftEdge, _⟩, rfl⟩
    exact hLeftClock leftEdge hLeftEdge hClock
  · rcases hRight with ⟨rightEdge, hRightEdge, rfl⟩
    exact hRightClock rightEdge hRightEdge hClock
  · rcases hRedirect with ⟨leftEdge, ⟨hLeftEdge, _⟩, rfl⟩
    exact hLeftClock leftEdge hLeftEdge hClock

theorem buildSequenceAutomaton_futureTargetsInStates
     (left right : AutomatonFragment)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftEdgeTargets : ∀ edge ∈ left.edges, edge.target ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    simp only [sequenceKeptLeftEdge, sequenceRedirectFutureSpec] at hFuture
    by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [hClock] at hFuture
    · rw [if_neg hClock] at hFuture
      injection hFuture with hTargetEq _
      subst hTargetEq
      apply sequenceRedirect_mem_states left right hRightInitial
      exact hLeftEdgeTargets leftEdge hLeftEdge.1
  · rcases hRight with ⟨rightEdge, hRightEdge, rfl⟩
    cases hSpec : rightEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» rightTarget rightRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hRightTarget := hRightTargets rightEdge hRightEdge
          rightTarget removed hSpec
        simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
          childState, hRightTarget]
  · rcases hRedirect with ⟨leftEdge, _hLeftEdge, rfl⟩
    simp only [sequenceRedirectEdge, sequenceRedirectFutureSpec] at hFuture
    by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [hClock] at hFuture
    · rw [if_neg hClock] at hFuture
      cases hFuture
      simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
        childState, hRightInitial]

end

end Pact
