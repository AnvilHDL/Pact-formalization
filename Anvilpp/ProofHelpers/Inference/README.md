# Process Abstraction and Inference

| Module | Results |
|---|---|
| `AbstractionSubstitution` | Process abstraction commutes with substitution |
| `AbstractionMenus` | Process/type completion and future-menu agreement |
| `AbstractionIdentifiers` | Preservation of fair-choice and progress IDs |
| `ErasureSideConditions` | Erasure of enabling, synchronization, and environment premises |
| `AlphabetInvariant` | Alphabet and erasure invariants |
| `ConjunctiveCommitment` | Abstraction of generated conjunctive branch products |
| `ConjunctiveConsumption` | Enabled-index, batch-label, residual, and menu erasure; joint payload witnesses |
| `OneStepAbstraction` | Every process step erases to an inferred-type step |
| `DataPreservation`, `ConjunctPreservation` | Data and conjunctive invariants of reachable processes |
| `LiftingPrelude` | Evaluation and inferred-constructor inversion |
| `ParallelLifting` | Assembly of concrete parallel offer steps |
| `DecoratedLifting` | Realization of abstract offer pairs and clock readiness |
| `RepresentedResiduals` | Represented-step closure and alphabet well-formedness of reachable process residuals |

Forward abstraction matches the erased label and inferred target. Reverse
lifting establishes a concrete step with matching offers, not an arbitrary
abstract branch target. Together they establish conformance and readiness in
[PactSafety](../../PactSafety.lean).
