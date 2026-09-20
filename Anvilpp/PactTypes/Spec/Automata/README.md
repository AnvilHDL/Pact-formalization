# Constructor Automata

| Module | Definitions |
|---|---|
| `AutomatonFragment` | Tagged states, pending edges, symbolic future fields, and finite fragments |
| `TypeAlphabetDefs` | Finite environment, label, and offer alphabets |
| `PendingAutomatonFutureDefs` | Execution-target closure, current offers, and reference closure |
| `MarkerReachabilityDefs` | Recursion markers and stopped fragments |
| `MenuDependencies` | Separate optimistic menu dependencies |
| `SyncEdgesDefs` | Synchronization, hiding, and local environments |
| `CompileTypeDefs` | Compilation fuel, constructor dispatch, resolved edges, and future menus |
| `BuildChoiceAutomatonDefs` | Ordinary and fair choice |
| `BuildSequenceAutomatonDefs` | Sequence copies and accepting-state redirection |
| `BuildParallelAutomaton` | Product, survivor-entry, survivor-continuation, and done edges |
| `BuildRecursionAutomatonDefs` | Recursion header and backedges |
| `BuildOfferAutomataDefs` | Exclusive and conjunctive offers |
| `SequenceMenuLemmas` | Menu aggregation from a chosen state |

Public edges are resolved visible edges. Variable markers are construction
labels used to install recursion backedges, not public execution steps.

Menu aggregation follows non-clock execution targets and separate menu
dependencies. Dependencies add neither execution states nor transitions.
Future fields may be stored sets, menu references, or unions with a menu;
their references do not determine the aggregation graph.

Recursive backedges retain the environments of their variable markers.
`compileType` does not apply an additional alphabet filter to its edges.
