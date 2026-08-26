import Anvilpp.PactTypes.NewCorrespondence.Helpers.Offers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

lemma relationMembership_var_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (name : String)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.var alphabet name)
          (compileType signature (.var alphabet name)))
        residual state) :
    residual = .var alphabet name ∧ state = TypeAutomatonState.root := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
    Prod.mk.injEq] at hRelated
  exact hRelated

end

end Pact
