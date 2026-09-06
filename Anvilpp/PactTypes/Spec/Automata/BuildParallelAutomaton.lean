import Anvilpp.PactTypes.Proofs.Automata.BuildSequenceAutomatonLemmas
import Anvilpp.PactTypes.Proofs.Automata.SyncEdgesLemmas

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

/-- Future spec used by parallel product edges.

A synchronized clock edge ends the current cycle, so its public future offers
are empty — whether or not it redirects to the completed state.  All other
product edges keep the usual symbolic reference to the target product state's
global `OF` equation. -/
def parallelFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

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
          future := parallelFutureSpec label target current
          target := target }

/-- The unpartnered edges of a product state whose left component has already
reached an accepting state.  The step is taken in the written right component
under its projected local environment, and only the interface has to be empty
on both its offer fields. -/
def parallelLeftCompleteEdges
    (parentAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((left.accepting ∩ left.states).biUnion fun leftState =>
      ((resolveAutomatonEdgesWith right rightFuture).filter
          fun rightEdge =>
          rightEdge.source ∉ right.accepting ∧
          rightEdge.target ∉ right.accepting ∧
          restrictTypeOffers interface rightEdge.current = ∅ ∧
          restrictTypeOffers interface rightEdge.future = ∅).biUnion
        fun rightEdge =>
          ((parentAlphabet.localEnvironments).filter
            fun environment =>
              projectAutomatonEnvironment rightAlphabet environment =
                rightEdge.environment).image
            fun environment =>
              let target : TypeAutomatonState := .survivor 1 rightEdge.target
              { source := .pair leftState rightEdge.source
                environment := environment
                label := rightEdge.label
                current := rightEdge.current
                future := parallelFutureSpec rightEdge.label target rightEdge.current
                target := target })

/-- The mirror of `parallelLeftCompleteEdges` for a completed right
component. -/
def parallelRightCompleteEdges
    (parentAlphabet leftAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((right.accepting ∩ right.states).biUnion fun rightState =>
      ((resolveAutomatonEdgesWith left leftFuture).filter
          fun leftEdge =>
          leftEdge.source ∉ left.accepting ∧
          leftEdge.target ∉ left.accepting ∧
          restrictTypeOffers interface leftEdge.current = ∅ ∧
          restrictTypeOffers interface leftEdge.future = ∅).biUnion
        fun leftEdge =>
          ((parentAlphabet.localEnvironments).filter
            fun environment =>
              projectAutomatonEnvironment leftAlphabet environment =
                leftEdge.environment).image
            fun environment =>
              let target : TypeAutomatonState := .survivor 0 leftEdge.target
              { source := .pair leftEdge.source rightState
                environment := environment
                label := leftEdge.label
                current := leftEdge.current
                future := parallelFutureSpec leftEdge.label target leftEdge.current
                target := target })

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
          future := parallelFutureSpec rightEdge.label target rightEdge.current
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
          future := parallelFutureSpec rightEdge.label .final rightEdge.current
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
          future := parallelFutureSpec leftEdge.label target leftEdge.current
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
          future := parallelFutureSpec leftEdge.label .final leftEdge.current
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
      parallelLeftCompleteEdges parentAlphabet rightAlphabet
        interface left right rightFuture ∪
      parallelRightCompleteEdges parentAlphabet leftAlphabet
        interface left right leftFuture ∪
      parallelLeftCompleteSurvivorEdges interface restampedRight
        restampedRightFuture ∪
      parallelRightCompleteSurvivorEdges interface restampedLeft
        restampedLeftFuture ∪
      parallelLeftCompleteDoneEdges interface restampedRight
        restampedRightFuture ∪
      parallelRightCompleteDoneEdges interface restampedLeft
        restampedLeftFuture)
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting
      (transitionEdges ∪ parallelDoneEdges parentAlphabet)
  exact product

end
end Pact
