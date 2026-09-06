import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.RecursionFoundations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def binaryChoiceRelationShape
     (whole left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (whole, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership (buildRelationSet left (compileType left))
        entry.1 q) ∨
    (∃ q, entry.2 = .child 1 q ∧
      relationMembership (buildRelationSet right (compileType right))
        entry.1 q)

/-- Lift a left-child relation pair through a constructor whose relation has
the binary-choice shape. -/
lemma relationMembership_binaryChoice_left
     (whole left right residual : PactType)
    (hUnfold :
      buildRelationSetCoreFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType left)) residual state) :
    relationMembership (buildRelationSet whole (compileType whole))
      residual (.child 0 state) := by
  show (residual, .child 0 state) ∈
    buildRelationSetCoreFuel (typeCompilationFuel whole) whole
  rw [hFuelEq, hUnfold]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Prod.mk.injEq]
  right
  left
  refine ⟨(residual, state), ?_, rfl, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient left
    (le_max_left _ _) le_rfl]
  exact hRelated

/-- Lift a right-child relation pair through a constructor whose relation has
the binary-choice shape. -/
lemma relationMembership_binaryChoice_right
     (whole left right residual : PactType)
    (hUnfold :
      buildRelationSetCoreFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet right (compileType right)) residual state) :
    relationMembership (buildRelationSet whole (compileType whole))
      residual (.child 1 state) := by
  show (residual, .child 1 state) ∈
    buildRelationSetCoreFuel (typeCompilationFuel whole) whole
  rw [hFuelEq, hUnfold]
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Prod.mk.injEq]
  right
  right
  refine ⟨(residual, state), ?_, rfl, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient right
    (le_max_right _ _) le_rfl]
  exact hRelated

lemma relationMembership_choice_left
     (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType left)) residual state) :
    relationMembership
      (buildRelationSet (.choice alphabet left right)
        (compileType (.choice alphabet left right)))
      residual (.child 0 state) := by
  apply relationMembership_binaryChoice_left
    (.choice alphabet left right)
    left right residual (by simp only [buildRelationSetCoreFuel])
  · simp only [typeCompilationFuel]
    omega
  · exact hRelated

lemma relationMembership_choice_right
     (alphabet : PactTypeAlphabet)
    (left right residual : PactType)
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet right (compileType right)) residual state) :
    relationMembership
      (buildRelationSet (.choice alphabet left right)
        (compileType (.choice alphabet left right)))
      residual (.child 1 state) := by
  apply relationMembership_binaryChoice_right
    (.choice alphabet left right)
    left right residual (by simp only [buildRelationSetCoreFuel])
  · simp only [typeCompilationFuel]
    omega
  · exact hRelated

lemma relationMembership_fairChoice_left
     (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right residual : PactType) {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet left (compileType left)) residual state) :
    relationMembership
      (buildRelationSet (.fairChoice alphabet bid left right)
        (compileType (.fairChoice alphabet bid left right)))
      residual (.child 0 state) := by
  apply relationMembership_binaryChoice_left
    (.fairChoice alphabet bid left right) left right residual (by simp only [buildRelationSetCoreFuel])
  · simp only [typeCompilationFuel]
    omega
  · exact hRelated

lemma relationMembership_fairChoice_right
     (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right residual : PactType) {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet right (compileType right)) residual state) :
    relationMembership
      (buildRelationSet (.fairChoice alphabet bid left right)
        (compileType (.fairChoice alphabet bid left right)))
      residual (.child 1 state) := by
  apply relationMembership_binaryChoice_right
    (.fairChoice alphabet bid left right) left right residual (by simp only [buildRelationSetCoreFuel])
  · simp only [typeCompilationFuel]
    omega
  · exact hRelated

/-- Every pair in a relation with the structural binary-choice clause is the
fresh root, a state copied from the left relation, or a state copied from the
right relation. -/

lemma relationMembership_binaryChoice_cases
     (whole left right : PactType)
    (hRelationUnfold :
      buildRelationSetCoreFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType whole))
        residual state) :
    binaryChoiceRelationShape whole left right (residual, state) := by
  rcases helper_h12_binaryChoice_shape whole left right
      hRelationUnfold hFuelEq hRelated with hRoot | hLeft | hRight
  · exact Or.inl (Prod.ext hRoot.1 hRoot.2)
  · exact Or.inr (Or.inl hLeft)
  · exact Or.inr (Or.inr hRight)

/-- Proves every related choice pair has the binary-choice shape. -/
lemma relationMembership_choice_cases
     (alphabet : PactTypeAlphabet)
    (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.choice alphabet left right)
          (compileType (.choice alphabet left right)))
        residual state) :
    binaryChoiceRelationShape (.choice alphabet left right) left right
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  exact relationMembership_binaryChoice_cases
    (.choice alphabet left right) left right (by simp only [buildRelationSetCoreFuel]) hFuelEq hRelated

/-- Proves every related fair-choice pair has the binary-choice shape. -/
lemma relationMembership_fairChoice_cases
     (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.fairChoice alphabet bid left right)
          (compileType (.fairChoice alphabet bid left right)))
        residual state) :
    binaryChoiceRelationShape (.fairChoice alphabet bid left right) left
      right (residual, state) := by
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel
        (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
        buildChoiceAutomaton alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildChoiceAutomaton alphabet
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton alphabet (compileTypeFuel
        (typeCompilationFuel left) left) (compileTypeFuel
        (typeCompilationFuel right) right) (TypeLabel.fair bid true)
        (TypeLabel.fair bid false)
    rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  exact relationMembership_binaryChoice_cases
    (.fairChoice alphabet bid left right) left right (by simp only [buildRelationSetCoreFuel]) hFuelEq hRelated


end

end Pact
