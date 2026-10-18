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
| `Honesty` | Consumption of boundary actions and retention of unconsumed offers |
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
| `WeakRefinement` | Fixed-environment silent paths and an obstruction to weak parallel lifting |
| `WeakRefinementLogs` | Recurrence under finite regrouping and honesty under silent insertion |
| `WeakRefinementComparison` | Honest strategy comparison with clock-aligned blocks and compatibility transfer |
| `WeakRefinementEnvironments` | Causal removal of consumed offers and agreement at block boundaries |
| `WeakRefinementParallel` | Two-round delay matching for independent enabled message prefixes |
| `WeakRefinementStrategies` | Whole-type compatibility equivalence under a leading skip |
| `WeakRefinementOfferDelay` | Shared-interface delay examples and declared-head default regression checks |

Refinement matches decorated steps and preserves the `skip` test. Parallel
lifting additionally requires equal component alphabets and structural
well-formedness. Compatibility transfer requires equal fair-choice and progress
identifier sets. These boundary conditions do not require identifier equality
between every pair of residuals.

`WeakRefinement` proves that allowing a leading silent step to disappear does
not preserve exact-label matching through synchronous parallel composition.
Its example satisfies type well-formedness and has matching alphabets and
identifier sets. The public refinement and checking definitions retain their
single-step clauses.

`WeakRefinementLogs` proves that matching finite blocks preserve clock,
fairness, and progress recurrence. Finite silent insertion under unchanged
environments also preserves honesty and the complete winning objective.
These are log-level results; they do not supply matching semantic executions
or a strategy transfer through parallel composition.

The independent-prefix case constructs both rounds from the existing parallel
rules and proves that every response has the stated label and target. Its
second environment drops the first round's consumed offer. Both rounds leave
the same honesty remainder as the original joint response.

`WeakRefinementStrategies.compatible_skipPrefix_iff` proves
`TypeCompatible (skip; source) T ↔ TypeCompatible source T` for every well-formed
source. Both directions construct strategies and cover completed failure logs.
The added first round may precede a clock round. This whole-type result does
not establish skip elimination inside an arbitrary parallel component.

`HonestBlockRefinement` is an experimental strategy comparison. It fixes the
alphabet and identifier sets, chooses a precise strategy before its replies,
and matches all completed logs in finite blocks with clocks at block ends.
`honestBlockRefinement_skipPrefix` supplies this comparison for any leading
skip, including honest strategies that are not winning. `typeFutureOffers_skipPrefix`
and `skipPrefix_offers_iff` give its unchanged static menu and its initial
offer pair `(empty, typeFutureOffers source)`. Parallel closure and transitivity
of the new comparison are not established; production refinement is unchanged.

`WeakRefinementOfferDelay` checks a three-component shared-interface example.
It proves the undelayed first response is forced and checks the first two
delayed rounds. Exclusive defaults now advertise declared heads, excluding
the former simultaneous-default step. The old incompatibility argument is
commented out. General parallel lifting remains open; the whole-type skip
theorem is unchanged.

See the [results index](../../RESULTS.md) for public statements and proof chains.
