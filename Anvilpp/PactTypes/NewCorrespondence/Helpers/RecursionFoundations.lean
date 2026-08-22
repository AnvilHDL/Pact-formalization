import Anvilpp.PactTypes.NewCorrespondence.Helpers.ExclusiveOffer

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

theorem decoratedTypeTransition_replaceVar_iff
    (name : String) (body : PactType) (residual : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType} :
    DecoratedTypeTransition env (residual.replaceVar name (.recur name body)) label
      offers target ↔
      ∃ residual', target = residual'.replaceVar name (.recur name body) ∧
        DecoratedTypeTransition env residual label offers residual' := by
  sorry

/-- States that a marker-labelled body edge is always sourced at a state representing the open variable it marks. -/
theorem compileTypeFuel_marker_represents_var
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {q : TypeAutomatonState} {residual : PactType}
    (hMem :
      relationMembership (buildRelationSet body (compileType signature body))
        residual q)
    {bodyEdge : PendingAutomatonEdge}
    (hBodyEdge : bodyEdge ∈
      (compileTypeFuel signature (typeCompilationFuel body) body).edges)
    (hSource : bodyEdge.source = q)
    (hMarkerLabel : bodyEdge.label = .variable name) :
    residual = .var name := by
  sorry

/-- Proves a `.child 0`-tagged state's future menu, in a compiled recursion, agrees with the body's own. -/
theorem computeFutureOf_recursion_child
    (signature : TypeAlphabet) (name : String) (body : PactType) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body))
    (hFuelBody : typeCompilationFuel body + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel body)
      body).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature body state := by
  sorry

/-- Proves H15's future agreement for a recursion-tagged state, substituted for the open variable. -/
lemma helper_h15_recursion_future_offers_agree
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {residual : PactType} {q : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet body (compileType signature body))
        residual q) :
    computeFutureOf signature (.recur name body) (.child 0 q) =
      typeFutureOffers (residual.replaceVar name (.recur name body)) := by
  sorry


end

end Pact
