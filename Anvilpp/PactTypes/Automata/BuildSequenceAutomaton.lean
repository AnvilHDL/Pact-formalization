import Anvilpp.PactTypes.Automata.BuildChoiceAutomaton

/-!
# buildSequenceAutomaton
-/

namespace Pact

noncomputable section

/-! ### Sequential composition by the paper's left/redirect/right clauses. -/

/-- The left states the sequence construction drops: every accepting state of
`left` other than its own entry.  The entry is kept even when it is accepting
itself, so the sequence still has an initial state. -/
def sequenceDeleted (left : AutomatonFragment) : Finset TypeAutomatonState :=
  left.accepting \ {left.initial}

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

theorem accepting_of_mem_sequenceDeleted {left : AutomatonFragment}
    {state : TypeAutomatonState} (hDeleted : state ∈ sequenceDeleted left) :
    state ∈ left.accepting := (mem_sequenceDeleted_iff.mp hDeleted).1

/-- Where a left-child edge target lands in the sequence carrier: accepting
targets enter `right`, while non-accepting targets keep their `0`-tag. -/
def sequenceRedirect (left right : AutomatonFragment)
    (state : TypeAutomatonState) : TypeAutomatonState :=
  if state ∈ left.accepting then childState 1 right.initial
  else childState 0 state

/-- Future spec used by sequence redirect edges.

A clock edge ends the current cycle, so it must not expose the right entry's
same-cycle future menu.  Non-clock redirects keep the usual symbolic reference
to the target state's `OF` equation. -/
def sequenceRedirectFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

/-- The image of a left edge whose target is not final.

This is the paper's `δ_seq^left` clause.  The edge stays in the left copy,
retagged.  The future field is rebuilt as a fresh `OF(q')` reference at the
retagged target — never the original edge's own `.future` retargeted in
place, since that original reference was resolved against `left` alone and
may carry an unrelated `removed` set.  `edge.current` is always a safe
choice of `removed`: it is exactly what a same-cycle self-loop needs
(`OF` of the loop's own state would otherwise double-count the offer this
edge already reports as current), and a no-op everywhere else, since
`edge.current` then generally is not present in the target's own menu
anyway. -/
def sequenceKeptLeftEdge (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := .at (sequenceRedirect left right edge.target) edge.current
    target := childState 0 edge.target }

/-- The image of a left edge whose target is final.

This is the paper's `δ_seq^redirect` clause.  The source, environment, label,
and current offers are copied from the left edge.  The target becomes the
right entry, and the future field is `OF(i₂)` — with `removed := edge.current`
for the same self-loop-safety reason as `sequenceKeptLeftEdge`. -/
def sequenceRedirectEdge (_left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := sequenceRedirectFutureSpec edge.label (childState 1 right.initial)
      edge.current
    target := childState 1 right.initial }

/-- `δ_seq^left`: keep exactly the left edges whose target is not accepting. -/
def sequenceLeftEdges (left right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge => edge.target ∉ left.accepting).image
    (sequenceKeptLeftEdge left right)

/-- `δ_seq^right`: copy all right edges into the right component. -/
def sequenceRightEdges (right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  childPendingEdges 1 right

/-- `δ_seq^redirect`: redirect exactly the left edges whose target is accepting. -/
def sequenceRedirectEdges (left right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (left.edges.filter fun edge => edge.target ∈ left.accepting).image
    (sequenceRedirectEdge left right)

/-- Compatibility helper for older correspondence proofs.

The construction below does not use this combined helper.  It is just the case
split between `δ_seq^left` and `δ_seq^redirect`. -/
def sequenceLeftEdge (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  if edge.target ∈ left.accepting then
    sequenceRedirectEdge left right edge
  else
    sequenceKeptLeftEdge left right edge

def buildSequenceAutomaton (_signature : TypeAlphabet)
    (left right : AutomatonFragment) : AutomatonFragment :=
  let states := (left.states \ sequenceDeleted left).image (childState 0) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  finishAutomatonFragment states (childState 0 left.initial) accepting
    ((sequenceLeftEdges left right ∪ sequenceRightEdges right) ∪
      sequenceRedirectEdges left right)

/-- Edges leaving a right-child state are exactly the copied edges of the
right fragment. Neither the left-edge nor redirect clause can have a
`.child 1` source. -/
theorem buildSequenceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    edge ∈ (buildSequenceAutomaton signature left right).edges ∧
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

theorem sequenceRedirect_eq_or (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    sequenceRedirect left right state = childState 1 right.initial ∨
      sequenceRedirect left right state = childState 0 state := by
  by_cases hAccepting : state ∈ left.accepting
  · exact Or.inl (sequenceRedirect_of_accepting hAccepting)
  · exact Or.inr (sequenceRedirect_of_not_accepting hAccepting)

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
theorem sequenceRedirect_mem_states (signature : TypeAlphabet)
    (left right : AutomatonFragment)
    (hRightInitial : right.initial ∈ right.states)
    (state : TypeAutomatonState)
    (hState : state ∈ left.states) :
    sequenceRedirect left right state ∈
      (buildSequenceAutomaton signature left right).states := by
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

theorem buildSequenceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftEdgeTargets : ∀ edge ∈ left.edges, edge.target ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton signature left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with (hLeft | hRight) | hRedirect
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    simp only [sequenceKeptLeftEdge] at hFuture
    injection hFuture with hTargetEq _
    subst hTargetEq
    apply sequenceRedirect_mem_states signature left right hRightInitial
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
