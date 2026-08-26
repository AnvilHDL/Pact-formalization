# Pact type syntax modules

This directory defines the Pact type language, its static regularity
conditions, its operational semantics, and the syntax-side completion/future
computations used by the compiler correspondence proof.

The files are arranged in dependency order. Later files import the preceding
syntax layer rather than redefining its concepts.

| File | Summary |
|---|---|
| [`PactTypeSyntax.lean`](PactTypeSyntax.lean) | Defines the explicitly alphabet-annotated `PactType` grammar and capture-avoiding substitution (`replaceVar`, `replaceBranches`). It also defines the fixed alphabet discipline used by admissible syntax, together with `AllVariablesBound`, `BinderHygienic`, and `BinderFreshFor`. |
| [`PactTypeRegularity.lean`](PactTypeRegularity.lean) | Defines the admissibility-side syntax predicates: guarded recursion, tail occurrences and `TailRecursive`, same-cycle prefix/suffix message sets and `SameCycleMessageLinear`, parallel-interface collection, and lexical `InterfaceScoped`. It also transports bound-variable and tail facts through constructors. |
| [`TypeErasure.lean`](TypeErasure.lean) | Defines type-level observations, labels, and environments and erases process-level observations, labels, and environments into them. This is the boundary between process semantics and the value-oblivious type semantics. |
| [`TypeDynamicsCore.lean`](TypeDynamicsCore.lean) | Defines offer and branch machinery used by the transition rules: needs, branch enabling/resolution, selected branches, parallel branch combinations, offer restriction, interface hiding, and local parallel environments. |
| [`TypeCompletionFuel.lean`](TypeCompletionFuel.lean) | Implements same-cycle completion as the fuel-bounded Boolean function `typeCanCompleteThisCycleFuel`, proves stabilization, and exposes `CanCompleteBeforeTock`. |
| [`TypeFutureOffersFuel.lean`](TypeFutureOffersFuel.lean) | Implements the fuel-bounded syntactic future-offer menu and proves that sufficient fuel produces a stable result. This is the computational basis of `typeFutureOffers`. |
| [`PactTypeCompletionEval.lean`](PactTypeCompletionEval.lean) | Defines valuation-polymorphic `completionEval`, allowing open recursion variables to be assigned completion behavior. It proves congruence, substitution, bound-variable, freshness, and hygiene transport. |
| [`PactTypeSubstitutionLemmas.lean`](PactTypeSubstitutionLemmas.lean) | Relates substitution to `CanCompleteBeforeTock`, `completionEval`, and tail occurrences. It contains the injectivity and no-occurrence results used to invert recursion unfolding safely. |
| [`PactTypeFutureOffers.lean`](PactTypeFutureOffers.lean) | Gives per-constructor equations for `typeFutureOffers` and defines the environment-indexed `TypeOffers` judgment used to decorate type transitions with current/future offer menus. |
| [`TypeTransitionSystem.lean`](TypeTransitionSystem.lean) | Defines `TypeTransition` and `DecoratedTypeTransition`, followed by type conformance/refinement and data-oblivious checking definitions. This is the operational side matched by compiled automaton edges. |

## How the correspondence proof uses this directory

The compiler proof treats `typeFutureOffers`, `CanCompleteBeforeTock`, and
`DecoratedTypeTransition` as the three primary syntax-side observations.
`AllVariablesBound` and `BinderHygienic` are not presentation-only well-formedness
conditions: they supply the exact capture-safety premises required when a
represented recursion-body residual is substituted under nested binders.

See the [PactTypes overview](../README.md), the
[automata module summary](../Automata/README.md), and the
[top-down theorem reference](../CORRESPONDENCE_THEOREMS.md).
