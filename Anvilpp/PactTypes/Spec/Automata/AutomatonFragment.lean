import Anvilpp.PactTypes.Proofs.Automata.TypeAlphabetLemmas

/-!
# Automaton state/edge/fragment representation used by every constructor
-/

namespace Pact

noncomputable section

/-! ### Construction representation -/

/-- Constructor states, tagged child copies, parallel products, and survivors. -/
inductive TypeAutomatonState : Type where
  /-- Fresh entry state introduced by a constructor. -/
  | root
  /-- Completed state used by atomic constructors. -/
  | final
  /-- State `state` embedded into child automaton `index`. -/
  | child : Nat → TypeAutomatonState → TypeAutomatonState
  /-- Product state containing one state from each parallel component. -/
  | pair : TypeAutomatonState → TypeAutomatonState → TypeAutomatonState
  /-- State of the surviving component `index` of a parallel product whose
  sibling has already completed. -/
  | survivor : Nat → TypeAutomatonState → TypeAutomatonState
  deriving DecidableEq

/-- A visible semantic label or an unresolved recursion-variable marker. -/
inductive AutomatonConstructionLabel : Type where
  | visible : TypeLabel → AutomatonConstructionLabel
  | variable : String → AutomatonConstructionLabel
  deriving DecidableEq

/-- A future-offer field resolved after the parent graph's menus are computed. -/
inductive FutureSpec : Type where
  /-- A stored future set. -/
  | explicit : Finset BareMessage → FutureSpec
  /-- A referenced menu with specified actions removed. -/
  | at : TypeAutomatonState → Finset BareMessage → FutureSpec
  /-- Stored offers unioned with a referenced menu, then restricted by removal. -/
  | atUnion : Finset BareMessage → TypeAutomatonState → Finset BareMessage →
      FutureSpec
  deriving DecidableEq

/-- The state a symbolic future field refers to, if any. -/
def FutureSpec.referenced : FutureSpec → Option TypeAutomatonState
  | .explicit _ => none
  | .at state _ => some state
  | .atUnion _ state _ => some state

/-- Resolve a future field against a menu function. -/
def resolveFutureSpec (futureAt : TypeAutomatonState → Finset BareMessage) :
    FutureSpec → Finset BareMessage
  | .explicit offers => offers
  | .at state removed => futureAt state \ removed
  | .atUnion offers state removed => (offers ∪ futureAt state) \ removed

/-- An edge whose future-offer field has not necessarily been resolved yet. -/
structure PendingAutomatonEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : FutureSpec
  target : TypeAutomatonState
  deriving DecidableEq

/--
A constructor fragment whose future references remain symbolic.

Keeping `FutureSpec.at` references unresolved is essential for recursion:
an enclosing binder can add a back-edge, changing the future offers reachable
from a child state.  Resolution therefore happens only when an operation
actually needs decorated edges, and once more for the final automaton.
-/
structure AutomatonFragment : Type where
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge
  /-- `κ_τ`: the states whose canonical annotation passes the optimistic
  completion test.  Retained by the fragment because it is computed from the
  constructor tags and final sets, without inspecting menus or reachability. -/
  completes : Finset TypeAutomatonState

/-- Every symbolic future reference in a fragment points to a declared state. -/
def AutomatonFragment.FutureTargetsInStates
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ target,
    edge.future.referenced = some target → target ∈ fragment.states

/-- Every edge target of a fragment belongs to its declared state carrier. -/
def AutomatonFragment.EdgeTargetsInStates
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, edge.target ∈ fragment.states


/-- A constructor edge after its future-offer field has been computed. -/
structure AutomatonFragmentEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : Finset BareMessage
  target : TypeAutomatonState
  deriving DecidableEq

/-- Complete state/edge graph used while resolving pending future fields. -/
structure PendingAutomaton : Type where
  states : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

namespace AutomatonConstructionLabel

  /-- Treat a temporary recursion edge as silent for local synchronization. -/
  def semantic : AutomatonConstructionLabel → TypeLabel
    | .visible label => label
    | .variable _ => TypeLabel.silent

  /-- Combine product labels while preserving an unresolved recursion marker. -/
  def combine (interface : Interface)
      (left right : AutomatonConstructionLabel) : AutomatonConstructionLabel :=
    match left, right with
    | .variable name, _ => .variable name
    | _, .variable name => .variable name
    | .visible leftLabel, .visible rightLabel =>
        .visible (TypeLabel.combine interface leftLabel rightLabel)

end AutomatonConstructionLabel

/-- In a clock environment only the clock itself can fire, with no offers.

This is the automaton-side mirror of the semantic `TypeOffers` facts
`typeOffers_label_eq_tock_of_clock` and `typeOffers_current_empty_of_clock`:
a compiled edge guarded by a clocked environment is tock-labelled and
exposes no current offers.  Every rule with a non-tock label either needs an
immediate need a clocked environment cannot supply, or carries an explicit
`clock = false` guard. -/
def AutomatonFragment.ClockEdgesAreTock
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, edge.environment.clock = true →
    edge.label.semantic = TypeLabel.tock ∧ edge.current = ∅

end

end Pact
