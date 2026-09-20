# Safety and Optimality Helpers

Supporting definitions and proofs for [PactSafety](../PactSafety.lean).

## Inference and Conformance

| Module | Contents |
|---|---|
| `Process`, `TypeSemantics` | Executions, completed logs, fairness, and objectives |
| `ConformanceTransfer` | Matching process/type histories and transferring strategies |
| `Inference/OneStepAbstraction` | Erasure of process steps |
| `Inference/DecoratedLifting` | Concrete realization of abstract offer pairs and readiness |
| `Inference/AbstractionIdentifiers` | Preservation of fair-choice and progress IDs |
| `Inference/DataPreservation`, `Inference/ConjunctPreservation` | Structural invariants of reachable processes |

## Compatibility

| Module | Contents |
|---|---|
| `CompatibilityGame` | Game construction and compatibility |
| `ObjectiveMonitor`, `RoundRobin` | Acceptance monitors |
| `LogRecognizer`, `ObjectiveRegularity` | Finite Rabin recognizability of the log objective |
| `CompatibilityBridge`, `StrategyExtension` | Game/semantic strategy correspondence |
| `PrefixPlayMatch` | Matching finite executions and game plays |
| `CompatibilitySoundness` | Log erasure and failure completion |

## Refinement and Optimality

| Module | Contents |
|---|---|
| `Composition` | Fixed compositions and identifier agreement |
| `Resigning` | Completion and menu laws under alphabet restriction |
| `ResigningSteps` | Forward/backward step transport and structural preservation |
| `ResigningRefinement` | Common-restriction closure and parallel refinement |
| `RefinementLifting` | Componentwise lifting, matching logs, and strategy transfer |

Refinement matches decorated steps and preserves the `skip` test. Parallel
lifting additionally requires equal component alphabets and structural
well-formedness. Compatibility transfer requires equal fair-choice and progress
identifier sets. These boundary conditions do not require identifier equality
between every pair of residuals.

`Regularity` defines compiler admissibility. `OmegaRegular` states finite Rabin
recognizability over the type's boundary environment/label alphabet.
`ObjectiveRegularity` proves it by combining bounded honesty memory with the
existing round-robin monitors. No operational states or transitions are added.
