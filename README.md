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
