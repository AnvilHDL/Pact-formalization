# Type Syntax and Semantics

| Module | Definitions |
|---|---|
| `PactTypeSyntaxDefs` | Alphabet-annotated types, substitution, and alphabet compatibility |
| `PactTypeRegularityDefs` | Binding, guarding, tail recursion, message linearity, and ownership |
| `TypeTransitionSystemDefs` | Transitions, decorated transitions, conformance, and refinement |
| `PactTypeFutureOffersDefs` | Current/future offer judgments and local offer environments |
| `TypeDynamicsCoreDefs` | Enabling, reannotation, hiding, and generated branch products |
| `TypeErasure` | Erased observations, labels, environments, and process abstraction |
| `TypeFutureOffersFuelDefs` | Alphabet-projected optimistic future menus |
| `TypeCompletionFuelDefs`, `DeclaredCompletionDefs` | Alphabet-independent optimistic completion |
| `PactTypeCompletionEval` | Completion with open recursion variables |
| `LiveEquivalenceDefs` | Equivalence allowing differences in unused annotations |
| `PactTypeSubstitutionDefs` | Tail closure |
| `TypeLabelOwnershipDefs` | Label ownership |
| `OfferMenuLinearityDefs` | Separation of offer heads from continuation menus |

Completion does not consult an environment or require alphabet membership.
`CanCompleteDeclared` retains its name but is alphabet-independent. Future
menus are projected to the alphabet. Environment well-formedness constrains
which communications can fire; waiting has no separate declaration gate.

`BinderHygienic` checks nested binding contexts. `BinderFreshFor` checks a
fixed forbidden set and supports capture-safe substitution of residuals.
