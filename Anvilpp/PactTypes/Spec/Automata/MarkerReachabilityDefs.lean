import Anvilpp.PactTypes.Proofs.Automata.PendingAutomatonFutureLemmas

namespace Pact

noncomputable section

/-- Forget fragment metadata and retain the pending graph. -/
def AutomatonFragment.toPending (fragment : AutomatonFragment) :
    PendingAutomaton :=
  { states := fragment.states, edges := fragment.edges }


/-- A state is a marker source when it has an outgoing `.variable name` edge. -/
def MarkerSource (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = state ∧ edge.label = AutomatonConstructionLabel.variable name

/-- No edge of the fragment is an unresolved call of `name`. -/
def AutomatonFragment.NoMarkerFor (fragment : AutomatonFragment)
    (name : String) : Prop :=
  ∀ edge ∈ fragment.edges,
    edge.label ≠ AutomatonConstructionLabel.variable name

/-- A marker edge adds nothing to the same-cycle menu at its source: it carries
no current offer, and its future is symbolic rather than an explicit menu. -/
def AutomatonFragment.MarkerOffersInert (fragment : AutomatonFragment)
    (name : String) : Prop :=
  ∀ edge ∈ fragment.edges,
    edge.label = AutomatonConstructionLabel.variable name →
      edge.current = ∅ ∧ ∀ offers, edge.future = .explicit offers → offers = ∅

/-- Auxiliary graph for paths before the first call of `name`.
The actual recursion compiler still installs a backedge at each such call. -/
def markerStoppedFragment (fragment : AutomatonFragment) (name : String) :
    AutomatonFragment :=
  { states := fragment.states
    initial := fragment.initial
    accepting := fragment.accepting
    completes := fragment.completes
    edges := fragment.edges.filter fun edge =>
      edge.label ≠ AutomatonConstructionLabel.variable name }


/-! ### Same-cycle marker reachability

The relevant side condition is whether any same-cycle reachable state still
carries an outgoing `.variable name` edge. The predicate is named here,
together with the transport lemmas used to compute it constructor by
constructor. -/

/-- Package a constructor graph without resolving its future references. -/
def finishAutomatonFragment
    (states : Finset TypeAutomatonState) (initial : TypeAutomatonState)
    (accepting : Finset TypeAutomatonState)
    (completes : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) : AutomatonFragment :=
  { states := states
    initial := initial
    accepting := accepting
    edges := edges
    completes := completes }

/-- Resolve symbolic future fields with the supplied global future-menu
function. Constructor code instantiates this with the type-aware
`computeFutureOf` function. -/
def resolveAutomatonEdgesWith
    (automaton : AutomatonFragment)
    (futureAt : TypeAutomatonState → Finset BareMessage) :
    Finset AutomatonFragmentEdge :=
  automaton.edges.image fun edge =>
      let resolvedFuture := resolveFutureSpec futureAt edge.future
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

/-- `κ` transported into child copy `index`. -/
def childCompletes (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.completes.image (childState index)

def childFutureSpec (index : Nat) : FutureSpec → FutureSpec
  | .explicit offers => .explicit offers
  | .at state removed => .at (childState index state) removed
  | .atUnion offers state removed =>
      .atUnion offers (childState index state) removed

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
