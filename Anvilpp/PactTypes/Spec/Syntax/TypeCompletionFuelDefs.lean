import Anvilpp.PactTypes.Spec.Syntax.DeclaredCompletionDefs

namespace Pact

noncomputable section

/-- Alphabet-independent optimistic completion before the next clock.
Fuel bounds syntax traversal; variables and clocks stop the search. -/
def typeCanCompleteThisCycleFuel : Nat → PactType → Bool
  | 0, _ => false
  | fuel + 1, processType =>
      match processType with
      | .message _ _ _ => true
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
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          typeCanCompleteThisCycleFuel fuel elseType ||
            branches.any fun branch =>
              typeCanCompleteThisCycleFuel fuel branch.2

end

end Pact
