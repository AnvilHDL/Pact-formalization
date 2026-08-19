import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore

namespace Pact

open Classical

noncomputable section

/-- Step correspondence for the `skip` constructor, stated for the new
relation-set presentation used by `PactSafety.type_automaton_correspondence`.

This is the Section 7.2/Lemma 4.5 base case: the compiled `skip` automaton
has exactly the non-clock silent self-loop that the operational `skip` type
has, and no clock step. -/
theorem correspondence_skip_stepIff
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet .skip (compileType signature .skip))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ (compileType signature .skip).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature .skip).HasEdge state env label offers state' ∧
        relationMembership
          (buildRelationSet .skip (compileType signature .skip))
          residual' state') := by
  sorry -- TODO(redevelopment): prove directly from the PDF skip case:
  -- `skip` has exactly the non-clock silent self-loop with empty current and
  -- future offers, and the compiled skip automaton exports exactly that edge.

end

end Pact
