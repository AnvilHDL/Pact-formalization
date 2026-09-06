import Anvilpp.PactTypes.Proofs.Automata.MarkerReachabilityLemmas

namespace Pact

noncomputable section

/--
Build a recursion binder with an explicit silent header step.

The fresh root represents the binder itself. Matching variable edges inside
the tagged body are replaced by silent back-edges to the body entry, which is
the graph representation of substituting the binder at those occurrences.
-/
def buildRecursionAutomaton
    (alphabet : PactTypeAlphabet) (name : String)
    (body : AutomatonFragment) : AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 body
  let accepting := childAccepting 0 body
  let headerEdges : Finset PendingAutomatonEdge :=
    ((alphabet.localEnvironments).filter fun environment =>
      environment.clock = false).image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
  let bodyEdges : Finset PendingAutomatonEdge := body.edges.image fun edge =>
    if edge.label = .variable name then
      { source := childState 0 edge.source
        environment := edge.environment
        label := AutomatonConstructionLabel.visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
    else
      { source := childState 0 edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := childFutureSpec 0 edge.future
        target := childState 0 edge.target }
  finishAutomatonFragment states .root accepting
    (headerEdges ∪ bodyEdges)

end

end Pact
