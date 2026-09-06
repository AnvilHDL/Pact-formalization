import Anvilpp.PactTypes.Proofs.Automata.BuildSequenceAutomatonLemmas
import Anvilpp.PactTypes.Proofs.Automata.SyncEdgesLemmas

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

/-- Parallel edges retain the future offers of their component witnesses. -/
def parallelFutureSpec (label : AutomatonConstructionLabel)
    (offers : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .explicit offers

/-- The unfiltered synchronized edges of a parallel product. Completing
component pairs are redirected to the dedicated `.final` state.  A
non-redirecting edge realizes the ordinary rule and so needs both sources
live; a redirecting one realizes the fusing rule, whose sources are
unconstrained. -/
def parallelRawTransitionEdges
    (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  let allLeftEdges := resolveAutomatonEdgesWith left leftFuture
  let allRightEdges := resolveAutomatonEdgesWith right rightFuture
  exact
    allLeftEdges.biUnion fun leftEdge =>
    (allRightEdges.filter fun rightEdge =>
      syncAutomatonEdges leftAlphabet rightAlphabet interface
        leftEdge rightEdge ∧
        (¬ (leftEdge.target ∈ left.accepting ∧
              rightEdge.target ∈ right.accepting) →
          leftEdge.source ∉ left.accepting ∧
          rightEdge.source ∉ right.accepting)).image fun rightEdge =>
        let bothAccept :=
          leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
        let target : TypeAutomatonState :=
          if bothAccept then .final
          else .pair leftEdge.target rightEdge.target
        let current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        let label := AutomatonConstructionLabel.combine interface
          leftEdge.label rightEdge.label
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := label
          current := current
          future := parallelFutureSpec label
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := target }

/-- Survivor entry for a completed left component: `δ_par^left`.

The edge is a synchronized product edge of `SyncEdges_I`, so it carries both
component edges, both local environments and their `Sync_I` premise.  The
finished left component stays accepting across its own edge — in practice its
silent idle loop — while the surviving right component is live at both ends.
Only the target is replaced by the survivor state; the component may still
advertise an interface action, which `hideOffers` removes from the published
current offer. -/
def parallelLeftCompleteEdges
    (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  let allLeftEdges := resolveAutomatonEdgesWith left leftFuture
  let allRightEdges := resolveAutomatonEdgesWith right rightFuture
  exact
    allLeftEdges.biUnion fun leftEdge =>
    (allRightEdges.filter fun rightEdge =>
      syncAutomatonEdges leftAlphabet rightAlphabet interface
        leftEdge rightEdge ∧
        leftEdge.source ∈ left.accepting ∧ leftEdge.target ∈ left.accepting ∧
        rightEdge.source ∉ right.accepting ∧
        rightEdge.target ∉ right.accepting).image fun rightEdge =>
        let target : TypeAutomatonState := .survivor 1 rightEdge.target
        let current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        let label := AutomatonConstructionLabel.combine interface
          leftEdge.label rightEdge.label
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := label
          current := current
          future := parallelFutureSpec label
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := target }

/-- Survivor entry for a completed right component: `δ_par^right`.  Mirror of
`parallelLeftCompleteEdges`. -/
def parallelRightCompleteEdges
    (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  let allLeftEdges := resolveAutomatonEdgesWith left leftFuture
  let allRightEdges := resolveAutomatonEdgesWith right rightFuture
  exact
    allLeftEdges.biUnion fun leftEdge =>
    (allRightEdges.filter fun rightEdge =>
      syncAutomatonEdges leftAlphabet rightAlphabet interface
        leftEdge rightEdge ∧
        rightEdge.source ∈ right.accepting ∧ rightEdge.target ∈ right.accepting ∧
        leftEdge.source ∉ left.accepting ∧
        leftEdge.target ∉ left.accepting).image fun rightEdge =>
        let target : TypeAutomatonState := .survivor 0 leftEdge.target
        let current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        let label := AutomatonConstructionLabel.combine interface
          leftEdge.label rightEdge.label
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := label
          current := current
          future := parallelFutureSpec label
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := target }

/-- The continuation of `parallelLeftCompleteEdges` inside the survivor
region: the surviving right component keeps stepping from `survivor 1`. -/
def parallelLeftCompleteSurvivorEdges
    (interface : Interface)
    (restampedRight : AutomatonFragment)
    (restampedRightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith restampedRight restampedRightFuture).filter
        fun rightEdge =>
        rightEdge.target ∉ restampedRight.accepting).image
      fun rightEdge =>
        let target : TypeAutomatonState := .survivor 1 rightEdge.target
        { source := .survivor 1 rightEdge.source
          environment := rightEdge.environment
          label := rightEdge.label
          current := rightEdge.current
          future := parallelFutureSpec rightEdge.label rightEdge.future
          target := target }

/-- The survivor's completing step: the re-stamped right component reaches an
accepting state, so the product enters `q_done`. -/
def parallelLeftCompleteDoneEdges
    (interface : Interface)
    (restampedRight : AutomatonFragment)
    (restampedRightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith restampedRight restampedRightFuture).filter
        fun rightEdge =>
        rightEdge.target ∈ restampedRight.accepting).image
      fun rightEdge =>
        { source := .survivor 1 rightEdge.source
          environment := rightEdge.environment
          label := rightEdge.label
          current := rightEdge.current
          future := parallelFutureSpec rightEdge.label rightEdge.future
          target := .final }

/-- The mirror of `parallelLeftCompleteSurvivorEdges` for a surviving left
component, stepping from `survivor 0`. -/
def parallelRightCompleteSurvivorEdges
    (interface : Interface)
    (restampedLeft : AutomatonFragment)
    (restampedLeftFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith restampedLeft restampedLeftFuture).filter
        fun leftEdge =>
        leftEdge.target ∉ restampedLeft.accepting).image
      fun leftEdge =>
        let target : TypeAutomatonState := .survivor 0 leftEdge.target
        { source := .survivor 0 leftEdge.source
          environment := leftEdge.environment
          label := leftEdge.label
          current := leftEdge.current
          future := parallelFutureSpec leftEdge.label leftEdge.future
          target := target }

/-- The mirror of `parallelLeftCompleteDoneEdges` for a surviving left
component. -/
def parallelRightCompleteDoneEdges
    (interface : Interface)
    (restampedLeft : AutomatonFragment)
    (restampedLeftFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith restampedLeft restampedLeftFuture).filter
        fun leftEdge =>
        leftEdge.target ∈ restampedLeft.accepting).image
      fun leftEdge =>
        { source := .survivor 0 leftEdge.source
          environment := leftEdge.environment
          label := leftEdge.label
          current := leftEdge.current
          future := parallelFutureSpec leftEdge.label leftEdge.future
          target := .final }

/-- The non-clock idle edges attached to the completed parallel state. -/
def parallelDoneEdges
    (alphabet : PactTypeAlphabet) : Finset PendingAutomatonEdge := by
  classical
  exact ((alphabet.localEnvironments).filter fun environment =>
    environment.clock = false).image fun environment =>
      { source := TypeAutomatonState.final
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }

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
def buildParallelAutomaton
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage) :
    AutomatonFragment := by
  classical
  let states : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      ((left.states.biUnion fun leftState =>
        right.states.image fun rightState =>
          TypeAutomatonState.pair leftState rightState) ∪
        (left.states.image (TypeAutomatonState.survivor 0)) ∪
        (right.states.image (TypeAutomatonState.survivor 1)))
  -- `F_τ = {q_done}` exactly: a raw product state is not accepting on its own.
  let accepting : Finset TypeAutomatonState := {TypeAutomatonState.final}
  let transitionEdges :=
    (parallelRawTransitionEdges leftAlphabet rightAlphabet interface
      left right
      leftFuture rightFuture ∪
      parallelLeftCompleteEdges leftAlphabet rightAlphabet
        interface left right leftFuture rightFuture ∪
      parallelRightCompleteEdges leftAlphabet rightAlphabet
        interface left right leftFuture rightFuture ∪
      parallelLeftCompleteSurvivorEdges interface restampedRight
        restampedRightFuture ∪
      parallelRightCompleteSurvivorEdges interface restampedLeft
        restampedLeftFuture ∪
      parallelLeftCompleteDoneEdges interface restampedRight
        restampedRightFuture ∪
      parallelRightCompleteDoneEdges interface restampedLeft
        restampedLeftFuture)
  let completes : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      ((left.completes.biUnion fun leftState =>
        right.completes.image fun rightState =>
          TypeAutomatonState.pair leftState rightState) ∪
        (restampedLeft.completes.image (TypeAutomatonState.survivor 0)) ∪
        (restampedRight.completes.image (TypeAutomatonState.survivor 1)))
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting completes
      (transitionEdges ∪ parallelDoneEdges parentAlphabet)
  exact product

end
end Pact
