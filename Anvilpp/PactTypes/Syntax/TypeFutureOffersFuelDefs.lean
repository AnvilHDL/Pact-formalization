import Anvilpp.PactTypes.Syntax.TypeCompletionFuelLemmas

namespace Pact

noncomputable section

/-- Syntactic future-offer menu, bounded by the depth of the finite type term. -/
def typeFutureOffersFuel : Nat → PactType → Finset BareMessage
  | 0, _ => ∅
  | fuel + 1, processType =>
      match processType with
      | .message alphabet msg dir =>
          if (msg, dir) ∈ alphabet.actions then {(msg, dir)} else ∅
      | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => typeFutureOffersFuel fuel body
      | .choice _ left right | .fairChoice _ _ left right =>
          typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right
      | .seq _ left right =>
          let leftOffers := typeFutureOffersFuel fuel left
          if typeCanCompleteThisCycleFuel fuel left then
            leftOffers ∪ typeFutureOffersFuel fuel right
          else leftOffers
      | .par _ left right interface =>
          hideTypeOffers interface
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
      | .xoffer alphabet elseType branches | .offer alphabet elseType branches =>
          if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
              (typeFutureOffersFuel fuel elseType)
          else ∅

/-- All message actions that may still be offered before the next clock. -/
def typeFutureOffers (processType : PactType) : Finset BareMessage :=
  typeFutureOffersFuel (sizeOf processType + 1) processType

end

end Pact
