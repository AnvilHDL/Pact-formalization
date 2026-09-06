import Anvilpp.PactTypes.Spec.Automata.AutomatonFragment

namespace Pact

noncomputable section

/-! ### Future-offer computation -/

namespace PendingAutomaton

  /-- States whose offers are referenced by outgoing edges from `state`. -/
  def referencedStates (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      -- A clock transition ends the current cycle.  Its decorated `future`
      -- field describes the offers after taking that transition, but those
      -- offers must not be used while computing the menu still reachable
      -- from `state` in the current cycle.
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        match edge.future with
        | .explicit _ => ∅
        | .at target _ => {target}
        | .atUnion _ target _ => {target}

  /-- Non-clock execution targets in the paper's menu equation. -/
  def menuStep (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      if edge.label.semantic = TypeLabel.tock then ∅ else {edge.target}

  /-- Direct contributions to the menu equation come only from current offers. -/
  def offersAt (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset BareMessage :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      if edge.label.semantic = TypeLabel.tock then ∅ else edge.current

  def futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
    reached ∪ reached.biUnion automaton.menuStep

  def futureReachableAux (automaton : PendingAutomaton) :
      Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
    | 0, reached => reached
    | fuel + 1, reached =>
        futureReachableAux automaton fuel (futureStep automaton reached)

  /-- Every symbolic reference in the graph points to a declared state. -/
  def ReferencesClosed (automaton : PendingAutomaton) : Prop :=
    ∀ state ∈ automaton.states,
      automaton.referencedStates state ⊆ automaton.states

  /-- Every non-clock execution target is a declared state. -/
  def MenuClosed (automaton : PendingAutomaton) : Prop :=
    ∀ state ∈ automaton.states, automaton.menuStep state ⊆ automaton.states

  /-- Saturate non-clock execution targets for at most `|Q|` rounds. -/
  def futureReachable (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    futureReachableAux automaton automaton.states.card {state}

end PendingAutomaton

end

end Pact
