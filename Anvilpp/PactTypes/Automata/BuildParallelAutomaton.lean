import Anvilpp.PactTypes.Automata.BuildSequenceAutomaton

/-!
# Reachable-fragment restriction and buildParallelAutomaton
-/

namespace Pact

noncomputable section

private def fragmentSuccessors (automaton : AutomatonFragment)
    (state : TypeAutomatonState) : Finset TypeAutomatonState :=
  (automaton.edges.filter fun edge => edge.source = state).image
    PendingAutomatonEdge.target

private def fragmentReachableAux (automaton : AutomatonFragment) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      fragmentReachableAux automaton fuel
        (reached ∪ reached.biUnion (fragmentSuccessors automaton))

private theorem mem_fragmentReachableAux
    (automaton : AutomatonFragment) (state : TypeAutomatonState) :
    ∀ fuel reached,
      state ∈ reached → state ∈ fragmentReachableAux automaton fuel reached := by
  intro fuel
  induction fuel with
  | zero => simp [fragmentReachableAux]
  | succ fuel ih =>
      intro reached hState
      apply ih
      exact Finset.mem_union_left _ hState

private def restrictReachableFragment (automaton : AutomatonFragment) :
    AutomatonFragment :=
  let reachable := fragmentReachableAux automaton automaton.states.card {automaton.initial}
  { states := automaton.states.filter fun state => state ∈ reachable
    initial := automaton.initial
    accepting := automaton.accepting.filter fun state => state ∈ reachable
    skipping := automaton.skipping.filter fun state => state ∈ reachable
    completing := automaton.completing.filter fun state => state ∈ reachable
    edges := automaton.edges.filter fun edge =>
      edge.source ∈ reachable ∧ edge.target ∈ reachable }

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂`, the initial state is `(i₁,i₂)`, and accepting states are pairs
of accepting component states. Pairs of synchronizing transition edges are
retained as semantic edges, with their interface actions hidden. In addition,
each product state receives non-exported observation self-loops containing the
two component `computeFuture` menus. These internal edges preserve optimistic
same-cycle offers such as
the `{b!}` continuation of `skip |[{a}]| (a! ; b!)` without inventing a
semantic parallel step. The full finite Cartesian carrier is retained:
`TypeCompilationRelation` also relates syntactic product pairs that are
unreachable from the initial pair, and its step correspondence is intentionally
valid at those states as well.
-/
def buildParallelAutomaton (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let allLeftEdges := resolvedAutomatonEdges left
  let allRightEdges := resolvedAutomatonEdges right
  let leftEdges := allLeftEdges.filter fun edge => edge.label ≠ .future
  let rightEdges := allRightEdges.filter fun edge => edge.label ≠ .future
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let states : Finset TypeAutomatonState :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let accepting : Finset TypeAutomatonState :=
    left.accepting.biUnion fun leftState =>
      right.accepting.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let completing : Finset TypeAutomatonState :=
    left.completing.biUnion fun leftState =>
      right.completing.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let transitionEdges : Finset PendingAutomatonEdge :=
    leftEdges.biUnion fun leftEdge =>
    (rightEdges.filter fun rightEdge =>
      syncAutomatonEdges interface leftEdges rightEdges
        leftEdge rightEdge).image fun rightEdge =>
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := AutomatonConstructionLabel.combine interface
            leftEdge.label rightEdge.label
          current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
          future := .explicit
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := .pair leftEdge.target rightEdge.target }
  let leftFutureEdges : Finset PendingAutomatonEdge :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface (computeFuture leftPending leftState)
          future := .explicit ∅
          target := .pair leftState rightState }
  let rightFutureEdges : Finset PendingAutomatonEdge :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface (computeFuture rightPending rightState)
          future := .explicit ∅
          target := .pair leftState rightState }
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting ∅ completing
      (transitionEdges ∪ (leftFutureEdges ∪ rightFutureEdges))
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with hTransition | hObservation
  · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
    simp at hFuture
  · rcases hObservation with hLeft | hRight
    · rcases hLeft with ⟨leftEdge, _, rightState, _, rfl⟩
      simp at hFuture
    · rcases hRight with ⟨leftState, _, rightEdge, _, rfl⟩
      simp at hFuture

/-- Every offer reachable in the left component during the current cycle is
retained at the corresponding product state, independently of whether that
component currently has a synchronizable transition. -/
theorem buildParallelAutomaton_leftFuture_subset
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states) :
    hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState) ⊆
      computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) := by
  classical
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  rw [show computeFuture
      { states := (buildParallelAutomaton interface left right).states
        edges := (buildParallelAutomaton interface left right).edges }
      (.pair leftState rightState) = productPending.offersAt
        (.pair leftState rightState) by
      exact computeFuture_eq_offersAt_of_all_explicit productPending hExplicit _]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  let observation : PendingAutomatonEdge :=
    { source := .pair leftState rightState
      environment := .empty
      label := .future
      current := hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState)
      future := .explicit ∅
      target := .pair leftState rightState }
  refine ⟨observation, ⟨?_, rfl⟩, ?_⟩
  · simp [observation, productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, hLeftState, hRightState]
  · simpa [observation, AutomatonConstructionLabel.semantic] using hAction

/-- Symmetric optimistic-future preservation for the right component. -/
theorem buildParallelAutomaton_rightFuture_subset
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states) :
    hideOffers interface
        (computeFuture { states := right.states, edges := right.edges } rightState) ⊆
      computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) := by
  classical
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  rw [show computeFuture
      { states := (buildParallelAutomaton interface left right).states
        edges := (buildParallelAutomaton interface left right).edges }
      (.pair leftState rightState) = productPending.offersAt
        (.pair leftState rightState) by
      exact computeFuture_eq_offersAt_of_all_explicit productPending hExplicit _]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  let observation : PendingAutomatonEdge :=
    { source := .pair leftState rightState
      environment := .empty
      label := .future
      current := hideOffers interface
        (computeFuture { states := right.states, edges := right.edges } rightState)
      future := .explicit ∅
      target := .pair leftState rightState }
  refine ⟨observation, ⟨?_, rfl⟩, ?_⟩
  · simp [observation, productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, hLeftState, hRightState]
  · simpa [observation, AutomatonConstructionLabel.semantic] using hAction

/-- The future menu of a product state is exactly the hidden union of the two
component menus.  Synchronization controls semantic transitions, but does not
discard optimistic same-cycle continuations from either component. -/
theorem buildParallelAutomaton_computeFuture
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates) :
    computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) =
      hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState ∪
          computeFuture { states := right.states, edges := right.edges }
            rightState) := by
  classical
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hLeftClosed : leftPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hRightTargets
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  change computeFuture productPending (.pair leftState rightState) = _
  rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with
        ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge,
          ⟨⟨hRightEdge, _⟩, hSync⟩, rfl⟩
      injection hSource with hLeftSource hRightSource
      subst leftState
      subst rightState
      by_cases hClock :
          (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock
      · simp [hClock] at hOffer
      · simp only [hClock, if_false, FutureSpec.explicit,
          Finset.mem_union] at hOffer
        rcases hSync with
          ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
        have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
            rightEdge.label.semantic := by
          exact hWitnesses.2.2.2
        have hNonClock :=
          AutomatonConstructionLabel.component_nonclock_of_sync interface
            leftEdge.label rightEdge.label hLabelSync hClock
        have hLeftSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture left leftEdge
            hLeftEdge hLeftClosed hLeftState hNonClock.1
        have hRightSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture right rightEdge
            hRightEdge hRightClosed hRightState hNonClock.2
        simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hOffer ⊢
        rcases hOffer with hCurrent | hFuture
        · rcases hCurrent with ⟨hLeft | hRight, hOutside⟩
          · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_left _ hLeft)), hOutside⟩
          · exact ⟨Or.inr (hRightSubset (Finset.mem_union_left _ hRight)), hOutside⟩
        · rcases hFuture with ⟨hLeft | hRight, hOutside⟩
          · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_right _ hLeft)), hOutside⟩
          · exact ⟨Or.inr (hRightSubset (Finset.mem_union_right _ hRight)), hOutside⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent,
          hideOffers] at hOffer ⊢
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        exact ⟨Or.inl hOffer.1, hOffer.2⟩
      · rcases hRight with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent,
          hideOffers] at hOffer ⊢
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        exact ⟨Or.inr hOffer.1, hOffer.2⟩
  · intro action hAction
    simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hAction
    rcases hAction with ⟨hLeft | hRight, hOutside⟩
    · have hHidden : action ∈ hideOffers interface
          (computeFuture { states := left.states, edges := left.edges }
            leftState) := Finset.mem_filter.mpr ⟨hLeft, hOutside⟩
      have hIncluded :=
        buildParallelAutomaton_leftFuture_subset interface left right
          leftState rightState hLeftState hRightState
          hHidden
      rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
        at hIncluded
      simpa [productPending, product] using hIncluded
    · have hHidden : action ∈ hideOffers interface
          (computeFuture { states := right.states, edges := right.edges }
            rightState) := Finset.mem_filter.mpr ⟨hRight, hOutside⟩
      have hIncluded :=
        buildParallelAutomaton_rightFuture_subset interface left right
          leftState rightState hLeftState hRightState
          hHidden
      rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
        at hIncluded
      simpa [productPending, product] using hIncluded

end

end Pact
