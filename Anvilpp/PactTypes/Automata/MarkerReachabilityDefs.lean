import Anvilpp.PactTypes.Automata.PendingAutomatonFutureLemmas

namespace Pact

noncomputable section

/-- Forget fragment metadata and retain the pending graph. -/
def AutomatonFragment.toPending (fragment : AutomatonFragment) :
    PendingAutomaton :=
  { states := fragment.states, edges := fragment.edges }


def markerAugmentedPending (fragment : AutomatonFragment) (name : String)
    (menu : Finset BareMessage) : PendingAutomaton :=
  { states := fragment.states
    edges := fragment.edges.image fun edge =>
      if edge.label = AutomatonConstructionLabel.variable name then
        { edge with future := .explicit menu }
      else edge }

/-- A state is a marker source when it has an outgoing `.variable name` edge. -/
def MarkerSource (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = state ∧ edge.label = AutomatonConstructionLabel.variable name

/-- The shape every compiled `.variable` marker edge has: no offers at all. -/
def MarkerEdgesInert (fragment : AutomatonFragment) (name : String) : Prop :=
  ∀ edge ∈ fragment.edges,
    edge.label = AutomatonConstructionLabel.variable name →
      edge.current = ∅ ∧ edge.future = FutureSpec.explicit ∅

/-- Stop unresolved calls of one name without changing the carrier or any
other edge.  This is useful when an execution view has followed a temporary
variable edge to its bookkeeping target, while an enclosing recursion
constructor is about to replace that edge by a backedge. -/
def markerStoppedFragment (fragment : AutomatonFragment) (name : String) :
    AutomatonFragment :=
  { states := fragment.states
    initial := fragment.initial
    accepting := fragment.accepting
    edges := fragment.edges.image fun edge =>
      if edge.label = AutomatonConstructionLabel.variable name then
        { edge with current := ∅, future := .explicit ∅ }
      else edge }


/-! ### Same-cycle marker reachability

The relevant side condition is whether any same-cycle reachable state still
carries an outgoing `.variable name` edge. The predicate is named here,
together with the transport lemmas used to compute it constructor by
constructor. -/

/-- Some state reachable in the same cycle still calls the enclosing binder. -/
def MarkerReachable (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∃ reached ∈ (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).futureReachable state,
    MarkerSource fragment name reached


/-- Package a constructor graph without resolving its future references. -/
def finishAutomatonFragment
    (states : Finset TypeAutomatonState) (initial : TypeAutomatonState)
    (accepting : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) : AutomatonFragment :=
  { states := states
    initial := initial
    accepting := accepting
    edges := edges }

/-- Resolve symbolic future fields with the supplied global future-menu
function. Constructor code instantiates this with the type-aware
`computeFutureOf` function. -/
def resolveAutomatonEdgesWith
    (automaton : AutomatonFragment)
    (futureAt : TypeAutomatonState → Finset BareMessage) :
    Finset AutomatonFragmentEdge :=
  automaton.edges.image fun edge =>
      let resolvedFuture :=
        match edge.future with
        | .explicit offers => offers
        | .at state removed => futureAt state \ removed
      { source := edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := resolvedFuture
        target := edge.target }

def childState (index : Nat) (state : TypeAutomatonState) :
    TypeAutomatonState := .child index state

def childStates (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.states.image (childState index)

def childAccepting (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.accepting.image (childState index)

def childFutureSpec (index : Nat) : FutureSpec → FutureSpec
  | .explicit offers => .explicit offers
  | .at state removed => .at (childState index state) removed

def childPendingEdge (index : Nat)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState index edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := childFutureSpec index edge.future
    target := childState index edge.target }

def childPendingEdges (index : Nat) (automaton : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  automaton.edges.image (childPendingEdge index)

end

end Pact
