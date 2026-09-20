# Pact Theory

Lean formalization of Pact processes, type inference, finite constructor
automata, compatibility, and optimality.

## Results

The following results are proved in [PactSafety.lean](Anvilpp/PactSafety.lean):

- Inferred-type and type-checking soundness.
- Type-automaton and process-automaton correspondence.
- Omega-regularity of the completed-log objective over the finite boundary alphabet.
- Equivalence of game-based and completed-log compatibility.
- Compatibility soundness for conforming processes.
- Compatibility monotonicity under componentwise refinement.
- Optimality of inferred types and its failure corollary.

Compatibility soundness requires equal process/type fair-choice and progress
identifier sets. Optimality compares well-formed compositions whose corresponding
components have equal message alphabets, fair-choice IDs, and progress IDs.

Complexity and algorithmic decidability claims are not part of the Lean development.

## Modules

| Module | Contents |
|---|---|
| [Proc](Anvilpp/Proc.lean) | Process syntax |
| [PactSemantics](Anvilpp/PactSemantics.lean) | Process transitions and offers |
| [PactTypes/Spec](Anvilpp/PactTypes/Spec/README.md) | Type semantics and automaton construction |
| [PactTypes/Proofs](Anvilpp/PactTypes/Proofs/README.md) | Type, compiler, and correspondence proofs |
| [ProofHelpers](Anvilpp/ProofHelpers/README.md) | Inference, strategy transfer, compatibility, and refinement |
| [PactSafetyStructures](Anvilpp/PactSafetyStructures.lean) | Correspondence witnesses and finite paths |
| [PactSafety](Anvilpp/PactSafety.lean) | Public safety and optimality theorems |

The [type development](Anvilpp/PactTypes/README.md) describes the simultaneous
correspondence proof. Operational notes and historical verification records are
kept separately in `status.md` and `HANDOFF.md`.

## Verification

Use the toolchain in `lean-toolchain`. From the repository root:

```bash
lake build Anvilpp.PactSafety
```

To check theorem dependencies, run a Lean file containing:

```lean
import Anvilpp.PactSafety

#print axioms Pact.type_automaton_correspondence
#print axioms Pact.type_compatibility_soundness
#print axioms Pact.inferred_types_optimal
```

These results use only `propext`, `Classical.choice`, and `Quot.sound`.
A successful build alone does not establish the absence of admitted dependencies.

## Documentation conventions

Declaration comments describe the definition or result in one or two lines.
They do not refer to external theorem numbering, proof history, or implementation
plans. Inline comments are reserved for non-obvious proof arguments.
