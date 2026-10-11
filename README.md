# Pact Theory

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23301148.svg)](https://doi.org/10.5281/zenodo.23301148)

Lean definitions and proofs for Pact processes, inferred types, constructor
automata, compatibility, and inferred-type optimality.

> For artifact reviewers, [Updates since submission](Update.md) summarizes the main updates relative to the submitted paper.

This mechanization is part of the POPL 2027 artifact, archived on Zenodo: [10.5281/zenodo.23301148](https://doi.org/10.5281/zenodo.23301148).

## Results

[PactSafety](Anvilpp/PactSafety.lean) proves inference/checking soundness,
type-automaton correspondence, process simulation and readiness agreement,
log-objective regularity, game reduction, compatibility soundness, and
inferred-type optimality. [Results and proofs](RESULTS.md) lists their
precise statements, explicit premises, and supporting proof chains.

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
