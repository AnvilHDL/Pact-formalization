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
- [x] Enforce the paper's boundary/internal separation in `AdmissibleType`:
  a boundary action's message identifier cannot also occur in the interface.
- [x] Prove that compiled parallel edges hide immediate interface actions.
- [x] Define `ClosedGuardedRegular`: all variables are bound, every recursive
  backedge crosses a clock, recursive calls are tail terminating, and a message
  identifier is exchanged at most once per clock cycle.
- [x] Prove that a mandatory clock prevents same-cycle completion, semantic
  completion/future-offer fuel stabilizes, and unfolding a clock-guarded
  recursion preserves the public `typeFutureOffers` menu.
- [x] Prove the complete atomic-message correspondence in both directions,
  including an inversion theorem classifying every compiled message edge as
  fire, wait, or completed-idle.
- [x] Prove compiler fuel irrelevance: two sufficient fuel values produce the
  same constructor fragment, so parent-compiled children can be rewritten to
  their standalone compilations.
- [ ] Prove future-offer correctness: resolving `FutureSpec.at q removed` with
  `computeFuture` gives the semantic `typeFutureOffers` set for the residual
  represented by `q`, minus `removed`.
  Clock guarding and tail termination rule out premature recursion-dependent
  resolution inside retained products. The remaining obligation is to connect
  graph-based `computeFuture` to `typeFutureOffers` for every related
  admissible residual.
- [x] Prove the remaining closed atomic cases: clock action/wait and progress.
  Unresolved variables remain an internal fragment case consumed by recursion.
- [x] Prove ordinary and fair choice preservation, including selection edges
  and child-state tagging.
- [x] Prove sequence step preservation, including exact left/right edge
  classifiers, literal-`skip` bridge edges, switching to the right child, and
  re-decoration from the syntax future of the residual.  The constructor
  theorem consumes the global future-correctness invariant listed above.
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
- [Anvilpp/PactTypes.lean](Anvilpp/PactTypes.lean): Compatibility façade for
  the complete Pact type development
- [Anvilpp/PactTypes/Syntax.lean](Anvilpp/PactTypes/Syntax.lean): Type syntax,
  erasure, operational semantics, and syntax-derived future offers
- [Anvilpp/PactTypes/Automata.lean](Anvilpp/PactTypes/Automata.lean): Finite
  constructor automata and the type compiler
- [Anvilpp/PactTypes/CorrespondenceCore.lean](Anvilpp/PactTypes/CorrespondenceCore.lean):
  State/residual invariants and atomic correspondence cases
- [Anvilpp/PactTypes/CorrespondenceCombinators.lean](Anvilpp/PactTypes/CorrespondenceCombinators.lean):
  Choice, fair-choice, sequence, and recursion correspondence lemmas
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
