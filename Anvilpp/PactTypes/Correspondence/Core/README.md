# Extracted correspondence core modules

This directory is the finer-grained extraction of the large aggregate
`CorrespondenceCore.lean` concern. The modules build as an independent import
chain and expose the same declarations in namespace `Pact`.

The public `Anvilpp.PactTypes` façade currently follows the aggregate module
path. Until that façade is migrated, do not import these extracted modules and
`CorrespondenceCore.lean` into the same Lean module, because both define the
same declaration names.

| File | Summary |
|---|---|
| [`TypeCompilationRelation.lean`](TypeCompilationRelation.lean) | Defines the compiler-state/residual relation for every constructor, proves residual uniqueness, and establishes initial-state representation/membership plus future-target and reference closure for sufficient compilation. |
| [`CompilationStateCorrect.lean`](CompilationStateCorrect.lean) | Defines and proves compiled-state membership correctness, the skipping/completing child-state classifiers, compiler skipping correctness, and the core correctness predicate interfaces. |
| [`AtomicCompletingFuture.lean`](AtomicCompletingFuture.lean) | Proves `CompilationCompletingCorrect` and `CompilationFutureCorrect` for `skip`, message, `tock`, progress, and free-variable marker fragments. |
| [`ParallelEnvironment.lean`](ParallelEnvironment.lean) | Defines `TypeEnvironment.AvoidsInterface`, scoped fragment-step correctness, resolved-offer witness correctness, local-environment well-formedness, and interface-avoidance transport. |
| [`SyncEdgeReconstruction.lean`](SyncEdgeReconstruction.lean) | Reconstructs synchronized automaton edges from paired `LocalTypeEnvironment` witnesses and reconstructs local semantic environments from synchronization witnesses. |
| [`AtomicMessageCorrespondence.lean`](AtomicMessageCorrespondence.lean) | Defines `TypeAutomatonCorrespondence` and proves complete public correspondence for `skip` and message actions, including fire, wait, and final edge directions. |
| [`AtomicClockCorrespondence.lean`](AtomicClockCorrespondence.lean) | Proves complete public correspondence for `tock`, including clock action, waiting, final edges, and their semantic inversions. |
| [`AtomicProgressCorrespondence.lean`](AtomicProgressCorrespondence.lean) | Proves complete public correspondence for progress markers and supplies resolved-edge target representation uniformly for every atomic constructor. |

Import order is:

```text
TypeCompilationRelation
  → CompilationStateCorrect
  → AtomicCompletingFuture
  → ParallelEnvironment
  → SyncEdgeReconstruction
  → AtomicMessageCorrespondence
  → AtomicClockCorrespondence
  → AtomicProgressCorrespondence
```

See the [parent correspondence summary](../README.md), the
[PactTypes overview](../../README.md), and the
[top-down theorem reference](../../CORRESPONDENCE_THEOREMS.md).
