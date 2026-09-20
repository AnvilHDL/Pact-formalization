# Correspondence Helpers

Structural facts used by the simultaneous step/menu induction.

| Modules | Results |
|---|---|
| `Sequence`, `Variables`, `Offers`, `ChoiceRelations` | Constructor-specific relation inversion |
| `RecursionFoundations` | Recursion relation clauses and substitution infrastructure |
| `Parallel` | Product/survivor relation inversion and parallel edge families |
| `MainHelpers` | Residual shapes and ownership data for generated branch products |
| `NewMainHelpers` | Accepting states represent exactly completed residuals; marker sources represent variables |
| `AlphabetPreservation` | Alphabet, binding, tail-recursion, and residual invariants |
| `TypeWellFormedIn` | Well-formedness bundles and descent to constructor children |
| `SurvivorTransport` | Reannotation transport for survivor states |
| `CompiledShape` | Structural shape under compilation and reannotation |
| `FutureClosure` | Edge/reference closure and compiled future-menu bounds |
| `MenuMetadata`, `MarkerMenus` | Menu links and marker-dependent menu components |
| `SequenceMenus`, `MenuLinkCompletion` | Sequence fields and completion along menu links |
| `CompletionFlag`, `CompletionNormalization` | Completion and annotation invariants under steps |
| `OwnershipTransport`, `OfferMenuLinearity` | Ownership and offer-menu separation under the relation |
| `OfferLocality`, `EnvironmentAndAlphabet` | Offer support and local-environment properties |
| `ExclusiveOffer` | Exclusive-offer residual and edge properties |
| `LiveStepLemmas` | Step transport between live-equivalent residuals |
| `FutureFieldShape`, `MenuReferenceShape` | Stored and referenced future-field shapes |

The environment-indexed marker result `markerSourceFor_of_var_residual` is in
[Recursion](../Simultaneous/Recursion.lean). It supplies a marker carrying the
same environment as the semantic unfolding step.
