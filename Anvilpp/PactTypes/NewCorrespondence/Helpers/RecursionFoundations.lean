import Anvilpp.PactTypes.NewCorrespondence.Helpers.ExclusiveOffer
import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionLemmas

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Lift a body relation pair through the recursion substitution and child
state tag. -/
lemma relationMembership_recur_child
     (alphabet : PactTypeAlphabet)
    (name : String) (body residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet body (compileType body)) residual state) :
    relationMembership
      (buildRelationSet (.recur alphabet name body)
        (compileType (.recur alphabet name body)))
      (residual.replaceVar name (.recur alphabet name body)) (.child 0 state) := by
  show (residual.replaceVar name (.recur alphabet name body), .child 0 state) ∈
    buildRelationSetCoreFuel
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

def recurRelationShape
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.recur alphabet name body, TypeAutomatonState.root) ∨
    (∃ q residual,
      entry =
        (residual.replaceVar name (.recur alphabet name body), .child 0 q) ∧
      relationMembership (buildRelationSet body (compileType body))
        residual q)

/-- Proves every related recursion pair has the recursion shape. -/
lemma relationMembership_recur_cases
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.recur alphabet name body)
          (compileType (.recur alphabet name body)))
        residual state) :
    recurRelationShape alphabet name body (residual, state) := by
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · have hBodyRelated : relationMembership
        (buildRelationSet body (compileType body))
        entry.1 entry.2 := hEntry
    exact Or.inr ⟨entry.2, entry.1,
      Prod.ext hResidual.symm hState.symm, hBodyRelated⟩

/-- Substitution rewrites branch bodies only, so any predicate reading just the
branch heads is invariant. -/
theorem PactType.typeBranchNeeds_replaceBranches
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) :
    typeBranchNeeds (PactType.replaceBranches branches name replacement) =
      typeBranchNeeds branches := by
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, typeBranchNeeds, List.map_cons] at *
      simp [ih]

/-- A non-`skip` stays a non-`skip` under substitution, provided the replacement
is not itself a `skip`.  The recursion caller instantiates the replacement with
`μX.body`, which is never a `skip`. -/
theorem PactType.replaceVar_ne_skip
    (name : String) (replacement : PactType)
    (hRepl : ∀ a, replacement ≠ .skip a) :
    ∀ t : PactType, t ≠ .skip t.alphabet →
      t.replaceVar name replacement ≠
        .skip (t.replaceVar name replacement).alphabet := by
  intro t hNot
  cases t with
  | skip a => exact absurd rfl hNot
  | var a other =>
      simp only [PactType.replaceVar]
      split
      · intro h; exact hRepl _ h
      · simp [PactType.alphabet]
  | recur a other b =>
      simp only [PactType.replaceVar]
      split <;> simp [PactType.alphabet]
  | _ => simp [PactType.replaceVar, PactType.alphabet]

/-- Branch membership survives substitution, at the substituted body. -/
theorem PactType.mem_replaceBranches
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (name : String) (replacement : PactType)
    (hMem : (action, branchType) ∈ branches) :
    (action, branchType.replaceVar name replacement) ∈
      PactType.replaceBranches branches name replacement := by
  induction branches with
  | nil => cases hMem
  | cons branch rest ih =>
      rcases branch with ⟨headAction, headType⟩
      simp only [PactType.replaceBranches, List.mem_cons] at hMem ⊢
      rcases hMem with hHead | hRest
      · injection hHead with hAction hType
        subst hAction; subst hType
        exact Or.inl rfl
      · exact Or.inr (ih hRest)

/-- Substitution is harmless in a residual where the recursive variable has no
active occurrence.

This intentionally replaces the old unconditional
`decoratedTypeTransition_replaceVar_iff`.  That old statement is false:
substituting `μX.body` for `X` can create an unfold step and can also change
the future-offer component of a decorated step.  At the recursion call site,
use this lemma only for copied body residuals whose tail-regularity premise
gives `residual.TailOccurrences name False`.  The marker/backedge case must be
handled separately by the recursion unfold rule. -/
theorem decoratedTypeTransition_replaceVar_eq_of_tailOccurrences_false
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType)
    (residual : PactType)
    (hTail : residual.TailOccurrences name False)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType} :
    DecoratedTypeTransition env
      (residual.replaceVar name (.recur alphabet name body)) label
      offers target ↔
      DecoratedTypeTransition env residual label offers target := by
  rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
    (.recur alphabet name body) residual hTail]

/-- Atomic marker-source fact for a bare variable.

For an arbitrary recursion body, the analogous statement needs the
tail-recursion premise.  A marker labelled `name` can be copied
through choices and offers, but tail regularity is what rules out marker
sources under sequence-left, parallel, and conjunctive-offer contexts.  The
recursion correspondence caller should therefore first split the copied
non-marker edge from the marker/backedge edge, then prove the arbitrary-body
marker case by induction using `body.TailOccurrences name True`, reducing the
base case to this lemma. -/
theorem compileTypeFuel_var_marker_represents_var
     (alphabet : PactTypeAlphabet) (name : String)
    {q : TypeAutomatonState} {residual : PactType}
    (hMem :
      relationMembership
        (buildRelationSet (.var alphabet name)
          (compileType (.var alphabet name)))
        residual q)
    {bodyEdge : PendingAutomatonEdge}
    (_hBodyEdge : bodyEdge ∈
      (compileTypeFuel (typeCompilationFuel (.var alphabet name))
        (.var alphabet name)).edges)
    (_hSource : bodyEdge.source = q)
    (_hMarkerLabel : bodyEdge.label = .variable name) :
    residual = .var residual.alphabet name := by
  have hRelated : (residual, q) ∈
      buildRelationSetCoreFuel (typeCompilationFuel (.var alphabet name))
        (.var alphabet name) := hMem
  simp only [typeCompilationFuel, buildRelationSetCoreFuel,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  obtain ⟨hResidual, _⟩ := hRelated
  subst hResidual
  rfl

/-- Future agreement for a recursion child in the form used by the relation.

This intentionally replaces the old "child future equals body future" lemma.
That old statement ignores installed recursion backedges.  The useful fact is
the H15-shaped one below: once a body state is related to `residual`, the
future menu at the tagged recursion state is the future menu of the substituted
residual.  Copied non-marker edges and marker/backedge edges should both
normalize their future fields through this relation-aware statement. -/
theorem computeFutureOf_recursion_child_related
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {state : TypeAutomatonState} {residual : PactType}
    (hRelated :
      relationMembership (buildRelationSet body (compileType body))
        residual state) :
    computeFutureOf (.recur alphabet name body) (.child 0 state) =
      typeFutureOffers
        (residual.replaceVar name (.recur alphabet name body)) := by
  exact helper_h15_future_offers_agree
    (relationMembership_recur_child alphabet name body residual
      hRelated)

/-- Proves H15's future agreement for a recursion-tagged state, substituted for the open variable. -/
lemma helper_h15_recursion_future_offers_agree
     (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {residual : PactType} {q : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet body (compileType body))
        residual q) :
    computeFutureOf (.recur alphabet name body) (.child 0 q) =
      typeFutureOffers
        (residual.replaceVar name (.recur alphabet name body)) := by
  exact computeFutureOf_recursion_child_related alphabet name body
    hRelated


end

end Pact
