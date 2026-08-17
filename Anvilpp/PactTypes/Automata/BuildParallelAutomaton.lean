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
    completing := automaton.completing.filter fun state => state ∈ reachable
    edges := automaton.edges.filter fun edge =>
      edge.source ∈ reachable ∧ edge.target ∈ reachable }

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂`, the initial state is `(i₁,i₂)`, and accepting states are pairs
of accepting component states. Pairs of synchronizing transition edges are
retained as semantic edges, with their interface actions hidden. Unlike the
earlier version of this construction, product states carry *no* extra
bookkeeping edges: the optimistic same-cycle menu each component still offers
on its own (needed e.g. for the `{b!}` continuation of
`skip |[{a}]| (a! ; b!)`) is supplied natively by `computeFutureOf`'s
product-state case (`CompileType.lean`, "Native product-aware future
resolution") instead, per `pactautomatonconstruction.typ`'s `Φ` — "without
inventing any new kind of edge." The full finite Cartesian carrier is
retained: `TypeCompilationRelation` also relates syntactic product pairs that
are unreachable from the initial pair, and its step correspondence is
intentionally valid at those states as well.
-/
def buildParallelAutomaton (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let allLeftEdges := resolvedAutomatonEdges left
  let allRightEdges := resolvedAutomatonEdges right
  let leftEdges := allLeftEdges.filter fun edge => edge.label ≠ .future
  let rightEdges := allRightEdges.filter fun edge => edge.label ≠ .future
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
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting completing
      transitionEdges
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with ⟨leftEdge, _, rightEdge, _, rfl⟩
  simp at hFuture

end

end Pact
