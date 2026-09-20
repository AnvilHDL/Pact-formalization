# Safety and Optimality Helpers

Supporting definitions and proofs for [PactSafety](../PactSafety.lean).

## Inference and Conformance

| Module | Contents |
|---|---|
| `Process`, `TypeSemantics` | Executions, completed logs, fairness, and objectives |
| `Objectives` | Value-oblivious objectives and erased-log membership |
| `ConformanceTransfer` | Matching process/type histories and transferring strategies |
| [Inference](Inference/README.md) | Abstraction, offer realization, identifiers, and reachable-process invariants |

## Compatibility

| Module | Contents |
|---|---|
| `CompatibilityGame` | Game construction and compatibility |
| `ObjectiveMonitor`, `RoundRobin` | Acceptance monitors |
| `SameCycleHonesty` | Equivalence of adjacent-step and same-cycle honesty |
| `LogRecognizer`, `ObjectiveRegularity` | Finite Rabin recognizability of the log objective |
| `CompatibilityBridge`, `StrategyExtension` | Game/semantic strategy correspondence |
| `PrefixPlayMatch` | Matching finite executions and game plays |
| `CompatibilitySoundness` | Log erasure and failure completion |
| `Regularity` | Compiler admissibility |

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

See the [results index](../../RESULTS.md) for public statements and proof chains.
