import Anvilpp.PactTypes.Syntax.TypeDynamicsCoreLemmas

namespace Pact

noncomputable section

/--
Whether a type may complete before the next clock.  Fuel bounds recursive
unfolding; a variable stops the search, which is exact for guarded recursion
when computing the offers visible before the next guard.
-/
def typeCanCompleteThisCycleFuel : Nat → PactType → Bool
  | 0, _ => false
  | fuel + 1, processType =>
      match processType with
      | .message _ _ _ | .progress _ _ | .skip _ => true
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
