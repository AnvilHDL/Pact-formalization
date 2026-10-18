# Type Laws

| Module | Results |
|---|---|
| `PactTypeSyntaxLemmas` | Alphabet compatibility and bound-variable laws |
| `PactTypeSubstitutionLemmas` | Completion under substitution and substitution at absent variables |
| `PactTypeRegularityLemmas` | Monotonicity of guarding and tail-position conditions |
| `TypeDynamicsCoreLemmas` | Reannotation and generated branch-product invariants |
| `ConjunctiveResiduals` | Enabled-index bounds, subset enumeration, and residual alphabets |
| `ConjunctiveResidualMenus` | Menus and optimistic completion of atomic offer residuals |
| `ConjunctiveResidualRegularity` | Tail recursion, clock guarding, and binder freshness of residuals |
| `PactTypeFutureOffersLemmas` | Constructor equations for future menus |
| `TypeCompletionFuelLemmas`, `TypeFutureOffersFuelLemmas` | Fuel-based completion/menu agreement |
| `DeclaredCompletionLemmas` | Completion under substitution and recursion unfolding |
| `CompletionReannotation` | Reannotation idempotence and completion transport |
| `LiveEquivalenceLemmas` | Completion and menu agreement under live equivalence |
| `TypeTransitionSystemLemmas` | Offer witnesses for undecorated transitions |
| `TypeOffersAlphabet` | Preservation of the source alphabet |
| `TypeOfferEnvironmentAgreementLemmas` | Distribution of offer hiding over union |
| `TypeLabelOwnershipLemmas` | Branch message bounds and clock-label ownership |

These results supply the semantic invariants used by
[correspondence](../Correspondence/README.md) and
[refinement](../../../ProofHelpers/README.md).
