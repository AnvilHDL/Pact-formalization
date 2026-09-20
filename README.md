# Pact Theory

Lean definitions and proofs for Pact processes, inferred types, constructor
automata, compatibility, and inferred-type optimality.

## Results

[PactSafety](Anvilpp/PactSafety.lean) proves inference/checking soundness,
type-automaton correspondence, process simulation and readiness agreement,
log-objective regularity, game reduction, compatibility soundness, and
inferred-type optimality. [Results and proofs](RESULTS.md) lists their
statements, assumptions, and supporting proof chains.

Compatibility soundness requires equal process/type fair-choice and progress
IDs. Optimality also requires equal message alphabets componentwise.
Complexity and algorithmic decidability claims are not formalized.

## Modules

| Module | Contents |
|---|---|
| [Base](Anvilpp/Base.lean), [Alphabet](Anvilpp/Alphabet.lean) | Identifiers, message actions, and alphabets |
| [Proc](Anvilpp/Proc.lean), [PactSemantics](Anvilpp/PactSemantics.lean) | Processes, evaluation, transitions, and offers |
| [PactTypes](Anvilpp/PactTypes/README.md) | Type semantics, compilation, and correspondence |
| [ProofHelpers](Anvilpp/ProofHelpers/README.md) | Inference, strategies, monitors, refinement, and compatibility |
| [PactSafetyStructures](Anvilpp/PactSafetyStructures.lean) | Correspondence witnesses and finite paths |
| [PactSafety](Anvilpp/PactSafety.lean) | Public results |

## Verification

Use the toolchain pinned in `lean-toolchain`:

```bash
lake build
lake env lean ProofAudit.lean
```

[ProofAudit](ProofAudit.lean) checks the public results' axiom dependencies.
They use only `propext`, `Classical.choice`, and `Quot.sound`.

Declaration comments describe their result in one or two lines. Module READMEs
describe the current development; `status.md` and `HANDOFF.md` hold work records.
