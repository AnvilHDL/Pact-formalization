import Anvilpp.PactTypes.Syntax.PactTypeFutureOffersLemmas

namespace Pact

set_option maxHeartbeats 1000000

/-! ### Environments agreeing away from a hidden set -/

/-- Two environments agree away from the hidden set `H`. -/
structure EnvAgreeOutside (H : Interface) (env₁ env₂ : TypeEnvironment) : Prop where
  immediate : hideTypeOffers H env₁.immediate = hideTypeOffers H env₂.immediate
  future : hideTypeOffers H env₁.future = hideTypeOffers H env₂.future
  clock : env₁.clock = env₂.clock

end Pact
