import Anvilpp.PactTypes.Syntax.DeclaredCompletionDefs

namespace Pact

noncomputable section

/-- Optimistic completion before the next clock, subject to the written
message and offer-head declarations. Fuel bounds syntax traversal; variables
and clocks stop the search. -/
def typeCanCompleteThisCycleFuel : Nat → PactType → Bool
  | 0, _ => false
  | fuel + 1, processType =>
      match processType with
      | .message alphabet msg dir => decide ((msg, dir) ∈ alphabet.actions)
      | .progress _ _ | .skip _ => true
      | .tock _ | .var _ _ => false
      | .recur _ _ body => typeCanCompleteThisCycleFuel fuel body
      | .choice _ left right | .fairChoice _ _ left right =>
          typeCanCompleteThisCycleFuel fuel left ||
            typeCanCompleteThisCycleFuel fuel right
      | .seq _ left right =>
          typeCanCompleteThisCycleFuel fuel left &&
            typeCanCompleteThisCycleFuel fuel right
      | .par _ left right _ =>
          typeCanCompleteThisCycleFuel fuel left &&
            typeCanCompleteThisCycleFuel fuel right
      | .xoffer alphabet elseType branches | .offer alphabet elseType branches =>
          decide (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) &&
            (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2)

end

end Pact
