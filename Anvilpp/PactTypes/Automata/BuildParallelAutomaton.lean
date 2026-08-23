import Anvilpp.PactTypes.Automata.BuildSequenceAutomaton
import Anvilpp.PactTypes.Automata.SyncEdges

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

private def edgeSuccessors (edges : Finset PendingAutomatonEdge)
    (state : TypeAutomatonState) : Finset TypeAutomatonState :=
  (edges.filter fun edge => edge.source = state).image PendingAutomatonEdge.target

private def reachableAux (edges : Finset PendingAutomatonEdge) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      reachableAux edges fuel
        (reached ∪ reached.biUnion (edgeSuccessors edges))

private def reachableStates (states : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) (initial : TypeAutomatonState) :
    Finset TypeAutomatonState :=
  reachableAux edges states.card {initial}

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂ ∪ {q_done}`, the initial state is `(i₁,i₂)`, and
`F_τ = {q_done}`.  Synchronized component edges become product edges.  Their
interface offers are hidden from the product edge.  If both component targets
are accepting, the product edge is redirected to `q_done`; otherwise its
target is the target pair.  Finally, only product edges whose source is
reachable from `(i₁,i₂)` are retained, and `q_done` receives the usual
non-clock silent idle self-loop.
-/
def buildParallelAutomaton (signature : TypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let allLeftEdges := resolvedAutomatonEdges left
  let allRightEdges := resolvedAutomatonEdges right
  let states : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      (left.states.biUnion fun leftState =>
        right.states.image fun rightState =>
          TypeAutomatonState.pair leftState rightState)
  -- `F_τ = {q_done}` exactly: a raw product state is not accepting on its own.
  let accepting : Finset TypeAutomatonState := {TypeAutomatonState.final}
  let rawTransitionEdges : Finset PendingAutomatonEdge :=
    allLeftEdges.biUnion fun leftEdge =>
    (allRightEdges.filter fun rightEdge =>
      syncAutomatonEdges interface leftEdge rightEdge).image fun rightEdge =>
        let bothAccept :=
          leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := AutomatonConstructionLabel.combine interface
            leftEdge.label rightEdge.label
          current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
          future :=
            if bothAccept then .at TypeAutomatonState.final ∅
            else .explicit (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target :=
            if bothAccept then .final
            else .pair leftEdge.target rightEdge.target }
  let doneEdges : Finset PendingAutomatonEdge :=
    let idleEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false
    idleEnvironments.image fun environment =>
      { source := TypeAutomatonState.final
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }
  let rawEdges := rawTransitionEdges ∪ doneEdges
  let reachable := reachableStates states rawEdges
    (.pair left.initial right.initial)
  let transitionEdges := rawTransitionEdges.filter fun edge =>
    edge.source ∈ reachable
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting
      (transitionEdges ∪ doneEdges)
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton signature interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with ⟨⟨leftEdge, _, rightEdge, _, rfl⟩, _⟩ | ⟨environment, _, rfl⟩
  · by_cases hAccept :
      leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
    · simp [hAccept] at hFuture
      obtain ⟨hTarget, _⟩ := hFuture
      subst target
      simp [buildParallelAutomaton, finishAutomatonFragment]
    · simp [hAccept] at hFuture
  · simp at hFuture

end

end Pact
