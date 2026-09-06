# Anvilpp.PactTypes.Spec.Syntax

The type language and its operational semantics.

| Module | Defines |
|---|---|
| `PactTypeSyntaxDefs` | `PactTypeAlphabet`, the `PactType` tree, `alphabet`, `replaceVar` and branch substitution |
| `PactTypeRegularityDefs` | `ClockGuarded`, `TailOccurrences`/`TailRecursive`, `CanCompleteBeforeTock`, `PrefixMessageIds`/`SuffixMessageIds`, `SameCycleMessageLinear`, `InterfaceAlphabetScoped` |
| `TypeTransitionSystemDefs` | `TypeTransition`, `TypeOfferSummary`, `DecoratedTypeTransition`, conformance and refinement |
| `PactTypeFutureOffersDefs` | `TypeOffers`, `typeWaitingOffers`, `LocalTypeOfferEnvironment` |
| `TypeDynamicsCoreDefs` | branch enabling, re-signing (`reannotate`), interface hiding, `parallelTypeBranchesSelecting` |
| `TypeErasure` | `TypeObservation`, `TypeLabel`, environments, process-to-type erasure |
| `TypeFutureOffersFuelDefs` | `typeFutureOffers`, the same-cycle menu |
| `TypeCompletionFuelDefs` | `typeCanCompleteThisCycleFuel`, the optimistic completion test |
| `DeclaredCompletionDefs` | `CanCompleteDeclared`, the alphabet-aware completion test |
| `PactTypeCompletionEval` | completion under an open recursion binder |
| `LiveEquivalenceDefs` | `LiveEq` — residuals differing only on unused alphabet entries |
| `PactTypeSubstitutionDefs` | `TailClosed` |
| `TypeLabelOwnershipDefs` | `LabelOwned` |

## Two completion tests

`CanCompleteBeforeTock` is structural. `CanCompleteDeclared` additionally
requires message actions and offer heads to be declared in the alphabet. The
menu equations read the declared form.

Both are *optimistic*: a sequence is the conjunction of its parts, a variable
is `false`, and no environment is consulted. This is not the same as "some
clock-free execution reaches `skip`".

## Capture safety

`BinderHygienic bound τ` grows its context on descent, so unfolding `μy.μx.y`
to `μx.μy.μx.y` breaks it. `BinderFreshFor forbidden τ` is a flat membership
condition and survives. Helper 12 is therefore stated with `BinderFreshFor`,
which it needs twice: to avoid capture of an inner binder against `FV(S)`, and
to rule out an inner binder of the same name.
