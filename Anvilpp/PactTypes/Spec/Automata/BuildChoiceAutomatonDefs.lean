import Anvilpp.PactTypes.Proofs.Automata.BuildRecursionAutomatonLemmas

namespace Pact

noncomputable section

/--
Build a binary choice.

`Q` contains a fresh root and tagged copies of both child state sets. Selection
edges leave the root, and the accepting states are the union of both children.
The supplied labels distinguish ordinary epsilon choice from fair choice.
-/
def buildChoiceAutomaton
    (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment) (selectionLeft selectionRight : TypeLabel) :
    AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 left ∪ childStates 1 right
  let accepting := childAccepting 0 left ∪ childAccepting 1 right
  let selections := ((alphabet.localEnvironments).filter
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

end

end Pact
