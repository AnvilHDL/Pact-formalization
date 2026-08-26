import Anvilpp.PactTypes.NewCorrespondence.Helpers.ExclusiveOffer

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Lift a body relation pair through the recursion substitution and child
state tag. -/
lemma relationMembership_recur_child
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet body (compileType signature body)) residual state) :
    relationMembership
      (buildRelationSet (.recur alphabet name body)
        (compileType signature (.recur alphabet name body)))
      (residual.replaceVar name (.recur alphabet name body)) (.child 0 state) := by
  show (residual.replaceVar name (.recur alphabet name body), .child 0 state) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.recur alphabet name body))
      (.recur alphabet name body)
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]
    omega
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image,
    Prod.mk.injEq]
  exact Or.inr ⟨(residual, state), hRelated, rfl, rfl⟩

theorem decoratedTypeTransition_replaceVar_iff
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (residual : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType} :
    DecoratedTypeTransition env
      (residual.replaceVar name (.recur alphabet name body)) label
      offers target ↔
      ∃ residual',
        target = residual'.replaceVar name (.recur alphabet name body) ∧
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
    residual = .var residual.alphabet name := by
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {residual : PactType} {q : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet body (compileType signature body))
        residual q) :
    computeFutureOf signature (.recur alphabet name body) (.child 0 q) =
      typeFutureOffers
        (residual.replaceVar name (.recur alphabet name body)) := by
  exact helper_h15_future_offers_agree signature
    (relationMembership_recur_child signature alphabet name body residual
      hRelated)


end

end Pact
