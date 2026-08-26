import Anvilpp.PactTypes.NewCorrespondence.Helpers.Parallel

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def recurRelationShape
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.recur alphabet name body, TypeAutomatonState.root) ∨
    (∃ q residual,
      entry =
        (residual.replaceVar name (.recur alphabet name body), .child 0 q) ∧
      relationMembership (buildRelationSet body (compileType signature body))
        residual q)

/-- Proves every related recursion pair has the recursion shape. -/
lemma relationMembership_recur_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.recur alphabet name body)
          (compileType signature (.recur alphabet name body)))
        residual state) :
    recurRelationShape signature alphabet name body (residual, state) := by
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · have hBodyRelated : relationMembership
        (buildRelationSet body (compileType signature body))
        entry.1 entry.2 := hEntry
    exact Or.inr ⟨entry.2, entry.1,
      Prod.ext hResidual.symm hState.symm, hBodyRelated⟩


end

end Pact
