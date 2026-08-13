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

/-- A local-environment witness may choose a different target and offer
summary from the actual component transition, but it must start at the same
residual under the same environment and semantic label. -/
def matchesAutomatonOfferWitness
    (actual witness : AutomatonFragmentEdge) : Prop :=
  witness.source = actual.source ∧
    witness.environment = actual.environment ∧
    witness.label.semantic = actual.label.semantic

/-- Exact automaton counterpart of the two `LocalTypeEnvironment` premises.

The actual edges determine the product target and its exposed current/future
summary.  The two witness edges justify the sibling-local environments; this
mirrors the semantic rule's existential sibling target and offer summary.
Using the equations verbatim is important because the future equation removes
the local immediate set and therefore does not require current/future
disjointness. -/
def syncAutomatonEdgeWitnesses (interface : Interface)
    (left right leftWitness rightWitness : AutomatonFragmentEdge) : Prop :=
  let outer := combineAutomatonEnvironment interface
    left.environment right.environment
  matchesAutomatonOfferWitness left leftWitness ∧
    matchesAutomatonOfferWitness right rightWitness ∧
    (if left.environment.clock then
      left.environment = TypeEnvironment.tock ∧
        right.environment = TypeEnvironment.tock
    else
      left.environment.clock = false ∧
        right.environment.clock = false ∧
        left.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface rightWitness.current ∧
        left.environment.future =
          (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
            left.environment.immediate ∧
        right.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface leftWitness.current ∧
        right.environment.future =
          (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
            right.environment.immediate) ∧
    TypeLabel.Sync interface left.label.semantic right.label.semantic

/-- Component edges synchronize when suitable local-environment offer
witnesses occur in their respective resolved edge relations. -/
def syncAutomatonEdges (interface : Interface)
    (leftEdges rightEdges : Finset AutomatonFragmentEdge)
    (left right : AutomatonFragmentEdge) : Prop :=
  ∃ leftWitness ∈ leftEdges, ∃ rightWitness ∈ rightEdges,
    syncAutomatonEdgeWitnesses interface left right leftWitness rightWitness

/-- Regression: interface synchronization alone cannot pair edges that see
different boundary environments. -/
theorem syncAutomatonEdges_rejects_boundary_environment_mismatch :
    let action : BareMessage := ("b", .send)
    let left : AutomatonFragmentEdge :=
      { source := .root
        environment :=
          { immediate := {typeNeed action}, future := ∅, clock := false }
        label := .visible (TypeLabel.message action.1 action.2)
        current := {action}
        future := ∅
        target := .final }
    let right : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := ∅
        future := ∅
        target := .root }
    ¬ syncAutomatonEdges ∅ {left} {right} left right := by
  classical
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, typeNeed]

/-- Regression for the existential local-environment reading: the actual left
edge may select the `a` branch while a distinct silent edge from the same
source/environment witnesses the `b` offer used to construct the right local
environment. -/
theorem syncAutomatonEdges_accepts_independent_offer_witness :
    let aSend : BareMessage := ("a", .send)
    let aRecv : BareMessage := ("a", .recv)
    let bSend : BareMessage := ("b", .send)
    let interface : Interface := {"a"}
    let leftEnvironment : TypeEnvironment :=
      { immediate := {aRecv}, future := ∅, clock := false }
    let leftActual : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {aSend}
        target := .child 0 .root }
    let leftWitness : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {bSend}
        target := .child 1 .root }
    let rightActual : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := {aRecv}
        future := ∅
        target := .root }
    syncAutomatonEdges interface {leftActual, leftWitness} {rightActual}
      leftActual rightActual := by
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, TypeLabel.Sync,
    TypeLabel.silent, AutomatonConstructionLabel.semantic, TypeLabel.sends,
    TypeLabel.recvs, TypeLabel.messageIdsWith]
  native_decide

end

end Pact
