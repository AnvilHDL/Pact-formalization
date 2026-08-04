# Anvil++ Theory

## New Extensions Task

- [x] Match the syntax to the paper
- [ ] Define the operational semantics same as the paper
- [ ] Types
- [ ] Type Semantics
- [ ] Operational Semantics for types
- [ ] Definition of Automata for types
- [ ] Bisimulation between types and automata
- [ ] Process Compatiblity Definition
- [ ] Type Compatiblity Definition
- [ ] Type Compat => Process Compat
- [ ] Type Satisfaction Definition
- [ ] Soundness of Type Satisfaction

## Structure

- [Anvilpp/Base.lean](Anvilpp/Base.lean): Some basic common definitions.
- [Anvilpp/Proc.lean](Anvilpp/Proc.lean): Process syntax and operational semantics.
- [Anvilpp/Types.lean](Anvilpp/Types.lean): Type syntax and well-formedness definition.
- [Anvilpp/Typing.lean](Anvilpp/Typing.lean): Type satisfiability judgements.
- [Anvilpp/Automata.lean](Anvilpp/Automata.lean): Type-level labelled transition system.
- [Anvilpp/Subtyping.lean](Anvilpp/Subtyping.lean): Congruence/subtyping meta-theory and refinement lemmas for type transitions.
- [Anvilpp/Helpers.lean](Anvilpp/Helpers.lean): Common helper lemmas.
- [Anvilpp/Trans.lean](Anvilpp/Trans.lean): Some helper lemmas related to type transitions.
- [Anvilpp/Refinement.lean](Anvilpp/Refinement.lean): Main process-to-type simulation/refinement development.
- [Anvilpp/Deadend.lean](Anvilpp/Deadend.lean): Dead-end preservation definitions and theorems.
- [Anvilpp/Reachable.lean](Anvilpp/Reachable.lean): Reachability-related definitions and theorems.

## Main Theorems

- [Anvilpp/Refinement.lean](Anvilpp/Refinement.lean#L1075): `process_refines_type`.
	If a process takes an action-level step, a well-typed type process can match that same action step, preserving the process/type correspondence.
- [Anvilpp/Deadend.lean](Anvilpp/Deadend.lean#L739): `type_preserves_deadends`.
	Well-typed processes cannot get stuck in ways their types disallow; dead-end freedom is preserved by the typing discipline.
- [Anvilpp/Reachable.lean](Anvilpp/Reachable.lean#L444): `reachable_finite_of_tailrec`.
	From any well-formed (tail-recursive) type, the reachable type-state space is finite, enabling finite-state reasoning.

## Checking Proofs

- Ensure the Lean toolchain from `lean-toolchain` is installed (via `elan`).
- From the repository root, check all proofs:

```bash
lake build
```

- To check a single module while iterating:

```bash
lake build Anvilpp.Refinement
```

- In VS Code, open a `.lean` file and use `Restart File` if diagnostics become stale after large refactors.

