import Anvilpp.PactTypes.NewCorrespondence.Helpers.Offers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def varRelationShape
    (name : String) (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.var name, TypeAutomatonState.root)

/-- Proves no decorated step is ever available at a variable marker. -/
lemma var_not_decoratedTypeTransition
    (name : String) {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : PactType} :
    ¬ DecoratedTypeTransition env (.var name) label offers target := by
  rintro ⟨hTrans, -⟩
  cases hTrans

/-- Proves the relation builder never grows past a variable-marker entry. -/
lemma relationSuccessors_var_eq_empty
    (signature : TypeAlphabet) (name : String)
    (entry : PactType × TypeAutomatonState) (hEntry : entry.1 = .var name) :
    relationSuccessors (compileType signature (.var name)) entry = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro pair hPair
  simp only [relationSuccessors, Finset.mem_biUnion] at hPair
  obtain ⟨edge, -, hPair⟩ := hPair
  split at hPair
  · split at hPair
    · rename_i hStep
      obtain ⟨residual', hStep'⟩ := hStep
      rw [hEntry] at hStep'
      exact var_not_decoratedTypeTransition name hStep'
    · simp at hPair
  · simp at hPair

/-- Proves every related variable-marker pair is the seed pair. -/
lemma relationMembership_var_cases
    (signature : TypeAlphabet) (name : String)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.var name) (compileType signature (.var name)))
        residual state) :
    residual = .var name ∧ state = TypeAutomatonState.root := by
  have hShape :=
    buildRelationSet_preserves (.var name) (compileType signature (.var name))
      (varRelationShape name)
      (by
        simp [varRelationShape, compileType, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment])
      (by
        intro entry hEntry successor hSuccessor
        rw [relationSuccessors_var_eq_empty signature name entry
          (by rw [hEntry])] at hSuccessor
        exact absurd hSuccessor (by simp))
      (residual, state) hRelated
  simpa [varRelationShape, Prod.ext_iff] using hShape

end

end Pact
