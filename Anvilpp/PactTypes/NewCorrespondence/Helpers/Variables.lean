import Anvilpp.PactTypes.NewCorrespondence.Helpers.Offers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

lemma relationMembership_var_cases
    (signature : TypeAlphabet) (name : String)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.var name) (compileType signature (.var name)))
        residual state) :
    residual = .var name ∧ state = TypeAutomatonState.root := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
    Prod.mk.injEq] at hRelated
  exact hRelated

end

end Pact
