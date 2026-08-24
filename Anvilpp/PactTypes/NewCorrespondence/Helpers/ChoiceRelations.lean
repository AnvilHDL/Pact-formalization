import Anvilpp.PactTypes.NewCorrespondence.Helpers.RecursionFoundations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def binaryChoiceRelationShape
    (signature : TypeAlphabet) (whole left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (whole, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership (buildRelationSet left (compileType signature left))
        entry.1 q) ∨
    (∃ q, entry.2 = .child 1 q ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q)

/-- Every pair in a relation with the structural binary-choice clause is the
fresh root, a state copied from the left relation, or a state copied from the
right relation. -/

lemma relationMembership_binaryChoice_cases
    (signature : TypeAlphabet) (whole left right : PactType)
    (hRelationUnfold :
      buildRelationSetCoreFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1) whole =
        insert (whole, TypeAutomatonState.root)
          ((buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left).image
              (fun entry => (entry.1, TypeAutomatonState.child 0 entry.2)) ∪
            (buildRelationSetCoreFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right).image
              (fun entry => (entry.1, TypeAutomatonState.child 1 entry.2))))
    (hFuelEq : typeCompilationFuel whole =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType signature whole))
        residual state) :
    binaryChoiceRelationShape signature whole left right (residual, state) := by
  rcases helper_h12_binaryChoice_shape signature whole left right
      hRelationUnfold hFuelEq hRelated with hRoot | hLeft | hRight
  · exact Or.inl (Prod.ext hRoot.1 hRoot.2)
  · exact Or.inr (Or.inl hLeft)
  · exact Or.inr (Or.inr hRight)

/-- Proves every related choice pair has the binary-choice shape. -/
lemma relationMembership_choice_cases
    (signature : TypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.choice left right)
          (compileType signature (.choice left right)))
        residual state) :
    binaryChoiceRelationShape signature (.choice left right) left right
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.choice left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  exact relationMembership_binaryChoice_cases signature
    (.choice left right) left right rfl hFuelEq hRelated

/-- Proves every related fair-choice pair has the binary-choice shape. -/
lemma relationMembership_fairChoice_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.fairChoice bid left right)
          (compileType signature (.fairChoice bid left right)))
        residual state) :
    binaryChoiceRelationShape signature (.fairChoice bid left right) left
      right (residual, state) := by
  have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
        (.fairChoice bid left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    show buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton signature (compileTypeFuel signature
        (typeCompilationFuel left) left) (compileTypeFuel signature
        (typeCompilationFuel right) right) (TypeLabel.fair bid true)
        (TypeLabel.fair bid false)
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
  exact relationMembership_binaryChoice_cases signature
    (.fairChoice bid left right) left right rfl hFuelEq hRelated


end

end Pact
