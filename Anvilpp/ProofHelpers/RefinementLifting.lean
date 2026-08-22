import Anvilpp.ProofHelpers.CompatibilityBridge

namespace Pact

noncomputable section

open Classical

/-- Helper Lemma H21: componentwise refinement lifts through a fixed
composition. -/
lemma helper_h21_componentwise_product_lifting
    {precise abstract : List PactType} {interfaces : List Interface}
    {preciseComposition abstractComposition : PactType}
    (hComponentwise : ComponentwiseRefines precise abstract)
    (hPrecise :
      composeTypes precise interfaces = some preciseComposition)
    (hAbstract :
      composeTypes abstract interfaces = some abstractComposition) :
    Refines preciseComposition abstractComposition := by
  sorry -- TODO(section7): induction on the parenthesized composition.

/-- Helper Lemma H22: histories can be matched along refinement. -/
lemma helper_h22_matching_histories_along_refinement
    {precise abstract : PactType}
    (hRefines : Refines precise abstract)
    (abstractStrategy : TypeStrategy) :
    ∃ preciseStrategy : TypeStrategy, True := by
  sorry -- TODO(section7): copy environments and answer steps via refinement.

/-- Helper Lemma H23: refinement is reflexive. -/
lemma helper_h23_refinement_refl (processType : PactType) :
    Refines processType processType := by
  refine ⟨{
    relation := Eq
    initial := rfl
    skipIff := ?_
    availability := ?_
    response := ?_
  }⟩
  · intro left right hRelated
    subst right
    simp
  · intro left right right' env label offers hRelated hStep
    subst right
    exact ⟨right', hStep⟩
  · intro left right left' env label offers hRelated hStep
    subst right
    exact ⟨left', hStep, rfl⟩

/-- Helper Lemma H23: refinement is transitive. -/
lemma helper_h23_refinement_trans
    {left middle right : PactType}
    (hLeft : Refines left middle) (hRight : Refines middle right) :
    Refines left right := by
  sorry -- TODO(section7): compose refinement witnesses.

end

end Pact
