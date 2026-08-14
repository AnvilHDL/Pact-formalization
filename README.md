# Pact Theory

Lean formalization of the Pact process/type theory, including the operational
type semantics, the finite constructor-automaton compiler, and the type-level
step correspondence from Lemma 4.5 of the paper.

## Proof status

- [x] Pact type syntax, regularity conditions, completion, future offers, and
  decorated type transitions.
- [x] Finite constructor automata and the canonical `compileType` compiler.
- [x] A state/residual relation for every type constructor.
- [x] Initial-state representation and membership in the compiled automaton.
- [x] Future-offer, completing-state, scoped-step, and sequence-execution
  correctness for every constructor.
- [x] Atomic, choice, fair-choice, sequence, parallel, exclusive-offer,
  conjunctive-offer, and guarded-recursion correspondence leaves.
- [x] The complete type/compiled-automaton correspondence theorem
  `type_automaton_correspondence` (Lemma 4.5).
- [ ] The process-to-type-automaton simulation
  `process_automaton_correspondence` (Lemma 4.6).
- [ ] Other paper-level results that are currently stated with admitted proofs
  in `Proc.lean`, `PactSemantics.lean`, `TypeTransitionSystem.lean`, or
  `PactSafety.lean`.

The completed type correspondence is assembled structurally through
`CompilationProofBundle`. Its four fields prove that compilation preserves:

1. same-cycle future offers;
2. completion before the next `tock`;
3. decorated operational steps in interface-scoped local environments; and
4. the non-clock execution closure needed when a type occurs to the left of a
   sequence.

An axiom audit of `Pact.type_automaton_correspondence` reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; it does not depend on
`sorryAx`. This does **not** mean the entire repository is free of `sorry`,
because the separate process-level and other paper results above remain open.

## Documentation

- [Pact type development](Anvilpp/PactTypes/README.md) describes the module
  layout and proof architecture.
- [Correspondence theorem reference](Anvilpp/PactTypes/CORRESPONDENCE_THEOREMS.md)
  lists the principal definitions and theorems in top-down proof order, with
  English statements and their role in the proof.
- [AGENT.md](AGENT.md) is the chronological proof-engineering log, including
  failed approaches, counterexamples, and the final recursion proof.
- `pact.pdf` is the paper; `Pact.pdf` contains the accompanying notes.

## Main entry points

- [`Anvilpp/PactTypes.lean`](Anvilpp/PactTypes.lean) is the public import façade
  for the Pact type development.
- [`Anvilpp/PactSafety.lean`](Anvilpp/PactSafety.lean) contains the paper-level
  theorem statements, including `type_automaton_correspondence`.
- [`CorrespondenceAssembly.lean`](Anvilpp/PactTypes/Correspondence/CorrespondenceAssembly.lean)
  performs the terminating constructor-by-constructor bundle assembly.
- [`CorrespondenceRecursionLeaf.lean`](Anvilpp/PactTypes/Correspondence/CorrespondenceRecursionLeaf.lean)
  closes the guarded-recursion bundle, including the two former proof leaves.

## Repository structure

- [`Anvilpp/Base.lean`](Anvilpp/Base.lean): basic definitions and abbreviations.
- [`Anvilpp/Proc.lean`](Anvilpp/Proc.lean): Pact process syntax.
- [`Anvilpp/PactSemantics.lean`](Anvilpp/PactSemantics.lean): process semantics.
- [`Anvilpp/PactTypes/Syntax/`](Anvilpp/PactTypes/Syntax/): type syntax,
  substitution, regularity, operational semantics, completion, and future
  offers.
- [`Anvilpp/PactTypes/Automata/`](Anvilpp/PactTypes/Automata/): finite
  automaton fragments, constructor builders, future resolution, and compiler.
- [`Anvilpp/PactTypes/Correspondence/`](Anvilpp/PactTypes/Correspondence/):
  compiler/semantics correspondence proof.
- [`Anvilpp/PactSafety.lean`](Anvilpp/PactSafety.lean): safety, compatibility,
  and paper-level theorem statements.

## Checking the development

Install the Lean toolchain specified by `lean-toolchain`, then from the
repository root run:

```bash
lake build Anvilpp
```

For a single public module:

```bash
lake build Anvilpp.PactSafety
```

To locate remaining admitted declarations independently of a successful build:

```bash
rg -n '\bsorry\b' Anvilpp
```
