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

/-- Restrict a parent environment to the actions one child alphabet declares.
A clocked environment projects to `tock`; otherwise both menus are filtered by
`projectTypeEnvironmentOffers`, exactly as `AutomatonLocalEnvironment.ordinary`
projects the outer environment onto a component. -/
def projectAutomatonEnvironment (alphabet : PactTypeAlphabet)
    (environment : TypeEnvironment) : TypeEnvironment :=
  if environment.clock then TypeEnvironment.tock
  else
    { immediate := projectTypeEnvironmentOffers alphabet environment.immediate
      future := projectTypeEnvironmentOffers alphabet environment.future
      clock := false }

/-- A clocked parent environment projects to `tock`. -/
theorem projectAutomatonEnvironment_of_clock {alphabet : PactTypeAlphabet}
    {environment : TypeEnvironment} (hClock : environment.clock = true) :
    projectAutomatonEnvironment alphabet environment = TypeEnvironment.tock := by
  simp [projectAutomatonEnvironment, hClock]

/-- Only a clocked parent environment has a clocked projection. -/
theorem clock_of_projectAutomatonEnvironment_clock {alphabet : PactTypeAlphabet}
    {environment : TypeEnvironment}
    (hClock : (projectAutomatonEnvironment alphabet environment).clock = true) :
    environment.clock = true := by
  by_cases hParent : environment.clock
  · exact hParent
  · simp [projectAutomatonEnvironment, hParent] at hClock

/-- Equality after restriction to the internal interface. -/
def sameOnInterface (interface : Interface)
    (left right : Finset BareMessage) : Prop :=
  restrictTypeOffers interface left = restrictTypeOffers interface right

/-- The automaton-only part of `LocalTypeEnvironment`.  It records the exact
projection equations using the sibling edge's resolved offer fields.  The
semantic sibling `TypeOffers` witness is supplied later by correspondence. -/
inductive AutomatonLocalEnvironment
    (outer : TypeEnvironment) (interface : Interface)
    (localAlphabet : PactTypeAlphabet)
    (sibling localEdge : AutomatonFragmentEdge) : Prop where
  | clock :
      outer.clock = true →
      sibling.environment = TypeEnvironment.tock →
      localEdge.environment = TypeEnvironment.tock →
      AutomatonLocalEnvironment outer interface localAlphabet sibling localEdge
  | ordinary :
      outer.clock = false →
      sibling.environment.clock = false →
      localEdge.environment.clock = false →
      localEdge.environment.immediate =
        projectTypeEnvironmentOffers localAlphabet outer.immediate ∪
          restrictTypeOffers interface sibling.current →
      localEdge.environment.future =
        (projectTypeEnvironmentOffers localAlphabet outer.future ∪
          restrictTypeOffers interface sibling.future) \
            localEdge.environment.immediate →
      AutomatonLocalEnvironment outer interface localAlphabet sibling localEdge

/-- The paper's `SyncEdges_I` side condition for a pair of component edges. -/
def syncAutomatonEdges (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragmentEdge) : Prop :=
  let outer := combineAutomatonEnvironment interface
    left.environment right.environment
  AutomatonLocalEnvironment outer interface leftAlphabet right left ∧
    AutomatonLocalEnvironment outer interface rightAlphabet left right ∧
    sameOnInterface interface left.current right.environment.immediate ∧
    sameOnInterface interface right.current left.environment.immediate ∧
    sameOnInterface interface left.future right.environment.future ∧
    sameOnInterface interface right.future left.environment.future ∧
    TypeLabel.Sync interface left.label.semantic right.label.semantic

end

end Pact
