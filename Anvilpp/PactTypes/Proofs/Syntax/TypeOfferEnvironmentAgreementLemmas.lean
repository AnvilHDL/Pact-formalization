import Anvilpp.PactTypes.Proofs.Syntax.PactTypeFutureOffersLemmas

namespace Pact

set_option maxHeartbeats 1000000

@[simp] theorem hideTypeOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideTypeOffers interface (left ∪ right) =
      hideTypeOffers interface left ∪ hideTypeOffers interface right := by
  simp [hideTypeOffers, Finset.filter_union]

/-! ### Hiding a union of interfaces, and commuting with projection -/

end Pact
