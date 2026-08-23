import Anvilpp.PactTypes.Automata.MarkerReachability

/-!
# Interface hiding and synchronized-edge construction for parallel products
-/

namespace Pact

noncomputable section

/-! ### Interface operations for parallel products -/

/-- Remove offers whose message identifier belongs to the internal interface. -/
def hideOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

/-- Keep only offers whose message identifier belongs to the interface. -/
def interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Hide the interface from the union of two component environments. -/
def combineAutomatonEnvironment (interface : Interface)
    (left right : TypeEnvironment) : TypeEnvironment :=
  if left.clock && right.clock then TypeEnvironment.tock
  else
    { immediate := hideOffers interface (left.immediate ∪ right.immediate)
      future := hideOffers interface (left.future ∪ right.future)
      clock := false }

/-- Equality after restriction to the internal interface. -/
def sameOnInterface (interface : Interface)
    (left right : Finset BareMessage) : Prop :=
  restrictTypeOffers interface left = restrictTypeOffers interface right

/-- The paper's `SyncEdges_I` side condition for a pair of component edges. -/
def syncAutomatonEdges (interface : Interface)
    (left right : AutomatonFragmentEdge) : Prop :=
  sameOnInterface interface left.current right.environment.immediate ∧
    sameOnInterface interface right.current left.environment.immediate ∧
    sameOnInterface interface left.future right.environment.future ∧
    sameOnInterface interface right.future left.environment.future ∧
    TypeLabel.Sync interface left.label.semantic right.label.semantic

end

end Pact
