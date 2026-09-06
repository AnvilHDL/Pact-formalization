import Anvilpp.PactTypes.Proofs.Syntax.TypeFutureOffersFuelLemmas

/-!
# The offer clause of same-cycle message linearity

Every branch continuation, including the default, excludes all branch-head
message names from its optimistic same-cycle future menu.  The check erases
polarity and reads `typeFutureOffers`, so it also covers offers that no
execution reaches.
-/

namespace Pact

noncomputable section

/-- No branch head's message name occurs in `FutOff(processType)`. -/
def BranchHeadsAbsentFromMenu (branches : List (BareMessage × PactType))
    (processType : PactType) : Prop :=
  ∀ branch ∈ branches, ∀ action ∈ typeFutureOffers processType,
    branch.1.1 ≠ action.1

mutual
  def OfferMenuLinear : PactType → Prop
    | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .recur _ _ body => OfferMenuLinear body
    | .choice _ left right | .seq _ left right =>
        OfferMenuLinear left ∧ OfferMenuLinear right
    | .par _ left right _ =>
        OfferMenuLinear left ∧ OfferMenuLinear right
    | .fairChoice _ _ left right =>
        OfferMenuLinear left ∧ OfferMenuLinear right
    | .xoffer _ elseType branches | .offer _ elseType branches =>
        BranchHeadsAbsentFromMenu branches elseType ∧
          (∀ branch ∈ branches, BranchHeadsAbsentFromMenu branches branch.2) ∧
          OfferMenuLinear elseType ∧
          OfferMenuLinearBranches branches
  termination_by processType => sizeOf processType

  def OfferMenuLinearBranches : List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        OfferMenuLinear processType ∧ OfferMenuLinearBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end

end Pact
