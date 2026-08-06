# Pact Theory

## New Extensions Task

- [x] Match the syntax to the paper
- [x] Scaffold the updated environment-indexed process semantics from the paper
- [x] Scaffold the updated type grammar and value erasure
- [x] Scaffold the environment-indexed type semantics
- [x] Scaffold finite semantic automata and correspondence witnesses
- [x] Define process communication safety and type compatibility
- [x] State type compatibility implies process compatibility
- [x] Define process-type conformance and type refinement
- [x] State the paper's inference, checking, game, soundness, and optimality results
- [ ] Discharge the new `sorry` proof and construction obligations


### Remaining proof obligations

- [x] Define the state/residual relation for every type constructor.
- [x] Prove that sufficient compilation fuel is positive.
- [x] Prove that the initial state represents the original type.
- [x] Prove that the initial state belongs to the compiled state set, including
  after parallel reachability restriction.
- [x] Prove the complete `skip` correspondence case.
- [ ] Give a usable, non-`sorry` definition of `ClosedGuardedRegular`, including
  closed variables, clock-guarded recursion, and the regularity assumptions
  needed for finite shared recursion states.
- [ ] Prove fuel irrelevance: two sufficient fuel values produce the same
  constructor fragment. Parent constructors currently give children surplus
  fuel, while standalone compilation uses the child's calculated fuel.
- [ ] Prove future-offer correctness: resolving `FutureSpec.at q removed` with
  `computeFuture` gives the semantic `typeFutureOffers` set for the residual
  represented by `q`, minus `removed`.
- [ ] Prove the remaining atomic cases: message action/wait, clock action/wait,
  progress, and an unresolved variable.
- [ ] Prove ordinary and fair choice preservation, including selection edges
  and child-state tagging.
- [ ] Prove sequence preservation, including left steps, literal-`skip`
  bridge edges, switching to the right child, and the associated future offers.
- [ ] Prove recursion preservation: the unfolding epsilon edge, substitution
  in `TypeCompilationRelation.recur_body`, matching-variable back-edges, and
  preservation of future references after the back-edge is installed.
- [ ] Prove parallel preservation in both directions: reconstruct the two
  local environments, match sibling current/future interface offers, combine
  labels, hide interface offers, and show reachable-product restriction does
  not remove a required edge.
- [ ] Prove exclusive-offer branch, else, and wait edges, including the
  correspondence between `List.zipIdx` child tags and branch membership.
- [ ] Prove conjunctive-offer enabled, else, and wait edges and connect child
  `0` to `parallelTypeBranches`.
- [ ] Combine the constructor lemmas into the general `stepIff` induction and
  remove the remaining `sorry` from `type_automaton_correspondence`.

## Structure

- [Anvilpp/Base.lean](Anvilpp/Base.lean): Some basic definitions/abbreviations
- [Anvilpp/Proc.lean](Anvilpp/Proc.lean): Pact process syntax
- [Anvilpp/PactSemantics.lean](Anvilpp/PactSemantics.lean): Pact Semantics
- [Anvilpp/PactTypes.lean](Anvilpp/PactTypes.lean): Type Syntax and Semantics
- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean): Safety and Compatibility Theorems

## Main Theorems

- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean#L232): `strategy_transfer`
- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean#L247): `inferred_type_soundness`
- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean#L333): `compatibility_game_correct`
- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean#L344): `type_compatibility_soundness`
- [Anvilpp/PactSafety.lean](Anvilpp/PactSafety.lean#L383): `inferred_types_optimal`

## Checking Proofs

- Ensure the Lean toolchain from `lean-toolchain` is installed (via `elan`).
- From the repository root, check all proofs:

```bash
lake build
```

- To check a single module while iterating:

```bash
lake build Anvilpp.PactSafety
```

- In VS Code, open a `.lean` file and use `Restart File` if diagnostics become stale after large refactors.
