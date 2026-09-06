# Anvilpp.PactTypes.Proofs.Correspondence.Helpers

Paper helpers 1–15 — the results the simultaneous induction assumes.

## Shape lemmas (helper 9)

Given `q ≈_σ ρ`, the relation clause that introduced `q` determines the shape
of `ρ`.

| Module | Provides |
|---|---|
| `Sequence` | `relationMembership_seq_cases` |
| `Variables` | `relationMembership_var_cases` |
| `Offers` | `relationMembership_xoffer_cases`, `..._offer_cases` |
| `RecursionFoundations` | `relationMembership_recur_cases`, `..._recur_child` |
| `Parallel` | `relationMembership_par_cases` |
| `ChoiceRelations` | `relationMembership_choice_cases`, `..._fairChoice_cases` |
| `MainHelpers` | `helper_h12_compiled_state_shape` and per-constructor wrappers |

## Principal modules

| Module | Lines | Main results |
|---|---:|---|
| `Parallel` | 3,639 | `decoratedTypeTransition_par_cases` (inverting a product step), survivor edge families, `relationMembership_par_final` |
| `AlphabetPreservation` | 3,359 | `relationMembership_alphabet_eq` (helper 6); transports of `AllVariablesBound`, `TailOccurrences`, `TailRecursive` through the relation |
| `TypeWellFormedIn` | 2,428 | `TypeWellFormedIn` and the descent lemmas `typeWellFormedIn_choice`/`_seq`/`_par`/`_recur`/`_xoffer`/`_offer` |
| `FutureClosure` | 2,310 | `edgeTargetsInStates` per builder; closure results for `computeFutureOf` |
| `SurvivorTransport` | 2,088 | `survivorTransport_all` (helper 7), `ExactSurvivorTransport` |
| `NewMainHelpers` | 1,038 | `final_states_completion` (helper 10), `TypeOffers.future_eq_sdiff_of_label_ne_tock` (helper 11), `markerSource_iff_var_residual` (helper 15) |
| `CompiledShape` | 918 | `ShapeEq` and the re-signing shape equalities |
| `MenuMetadata` | 779 | `compileTypeMenuLinksFuel_*`, the menu-dependency graph `L_σ` |

Also: `MarkerMenus` (`menuReachesVar`), `SequenceMenus`
(`sequenceLeftEdge_future`), `MenuLinkCompletion` (`completionAfter`),
`CompletionFlag`, `OwnershipTransport`, `ExclusiveOffer`,
`CompletionNormalization`, `EnvironmentAndAlphabet`, `LiveStepLemmas`.

## Note on helper 15

`markerSource_iff_var_residual` produces *some* marker edge. The paper's
statement fixes a non-clock `E_σ ∈ Env_σ`, and helper 12 needs that form:
`markerSourceFor_of_var_residual`, in
[`../Simultaneous/Recursion.lean`](../Simultaneous/Recursion.lean). It is
stated against the call's own alphabet, so it propagates through the induction
without alphabet side conditions.
