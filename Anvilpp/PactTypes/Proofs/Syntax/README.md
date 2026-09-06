# Anvilpp.PactTypes.Proofs.Syntax

Laws of the type language, independent of the compiler.

| Module | Main results |
|---|---|
| `PactTypeSubstitutionLemmas` | `replaceVar_canCompleteBeforeTock` — completion commutes with capture-avoiding substitution; `replaceVar_eq_self_of_tailOccurrences_false` — substitution is the identity where the variable does not occur |
| `TypeDynamicsCoreLemmas` | re-signing (`reannotate_alphabet`, `reannotate_tailOccurrences`) and the conjunctive-offer product (`parallelTypeBranchesSelecting_tailOccurrences`) |
| `PactTypeFutureOffersLemmas` | constructor equations for `typeFutureOffers`; the sequence clause reads the completion flag |
| `PactTypeRegularityLemmas` | `guardedOccurrences_mono`, `tailOccurrences_mono` |
| `TypeCompletionFuelLemmas` | `typeCanCompleteThisCycleFuel_eq_canCompleteDeclared` |
| `TypeFutureOffersFuelLemmas` | `typeFutureOffersFuel_eq_typeFutureOffers` |
| `DeclaredCompletionLemmas` | `replaceVar_canCompleteDeclared`, `canCompleteDeclared_recur_unfold` |
| `CompletionReannotation` | `reannotate_idem` and its interaction with completion |
| `LiveEquivalenceLemmas` | `liveEq_preserves_futOff` (helper 5) |
| `TypeTransitionSystemLemmas` | `TypeTransition.exists_typeOffers`, `.exists_decorated` |
| `TypeOffersAlphabet` | `TypeOffers.preserves_alphabet` (helper 1) |
| `PactTypeSyntaxLemmas` | `parent_actions_subset_left`/`_right`, `allVariablesBound_mono` |

## Note

`TailOccurrences`, `TailRecursive`, `BinderHygienic` and the other regularity
predicates are defined by well-founded recursion, so `h.1` and `h.2` do not
apply to them directly. Unfold with `simp only [P] at h` first; `rw` will not
work.
