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

`Q = Q₁ × Q₂ ∪ {q_done}`, the initial state is `(i₁,i₂)`, and accepting
states are pairs of accepting component states together with `q_done`
(reused as `.final`, the same dedicated completion marker every atomic base
case already compiles to). Pairs of synchronizing transition edges are
retained as semantic edges, with their interface actions hidden — *except*
when both raw targets are accepting, in which case the compiler redirects
the edge to `q_done` directly rather than leaving the raw completed pair as
its own, separate state: the semantic `par` rule fuses two completed targets
into bare `skip`, and `q_done` is `skip`'s unique representative, exactly as
`pactproofs.typ`'s own construction does ("The compiler removes this raw
target and places the edge in `δ_par^redirect`. Its new target is
`q_done`."). `q_done` gets the same non-clock silent idle self-loop every
`.final` state carries elsewhere. Unlike the earlier version of this
construction, product states carry *no* extra bookkeeping edges: the
optimistic same-cycle menu each component still offers on its own (needed
e.g. for the `{b!}` continuation of `skip |[{a}]| (a! ; b!)`) is supplied
natively by `computeFutureOf`'s product-state case (`CompileType.lean`,
"Native product-aware future resolution") instead, per
`pactautomatonconstruction.typ`'s `Φ` — "without inventing any new kind of
edge." The full finite Cartesian carrier is retained: `TypeCompilationRelation`
also relates syntactic product pairs that are unreachable from the initial
pair, and its step correspondence is intentionally valid at those states as
well.
-/
def buildParallelAutomaton (signature : TypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let allLeftEdges := resolvedAutomatonEdges left
  let allRightEdges := resolvedAutomatonEdges right
  let leftEdges := allLeftEdges.filter fun edge => edge.label ≠ .future
  let rightEdges := allRightEdges.filter fun edge => edge.label ≠ .future
  let states : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      (left.states.biUnion fun leftState =>
        right.states.image fun rightState =>
          TypeAutomatonState.pair leftState rightState)
  let accepting : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      (left.accepting.biUnion fun leftState =>
        right.accepting.image fun rightState =>
          TypeAutomatonState.pair leftState rightState)
  let completing : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      (left.completing.biUnion fun leftState =>
        right.completing.image fun rightState =>
          TypeAutomatonState.pair leftState rightState)
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
          target :=
            if leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting then
              .final
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
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting completing
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
  rcases hEdge with ⟨leftEdge, _, rightEdge, _, rfl⟩ | ⟨environment, _, rfl⟩ <;> simp at hFuture

end

end Pact
