# Anvilpp.PactTypes.Spec.Automata

The automaton representation and the constructor compiler.

| Module | Defines |
|---|---|
| `AutomatonFragment` | `TypeAutomatonState`, `AutomatonConstructionLabel`, `FutureSpec`, `PendingAutomatonEdge`, `AutomatonFragment` and its shape invariants |
| `TypeAlphabetDefs` | `localEnvironments`, `localOfferSummaries`, `TypeAutomatonSymbol`, `transitionAlphabet` |
| `PendingAutomatonFutureDefs` | `referencedStates`, `offersAt`, `futureReachable`, `ReferencesClosed` |
| `MarkerReachabilityDefs` | `MarkerSource`, `NoMarkerFor`, `markerStoppedFragment`, and the child-tagging helpers |
| `MenuDependencies` | `menuDependencyTargets`, `withMenuDependencies` — the optimistic menu edges `L_σ` |
| `SyncEdgesDefs` | interface hiding, `AutomatonLocalEnvironment`, `syncAutomatonEdges` |
| `CompileTypeDefs` | `typeCompilationFuel`, `compileTypeFuel`, `compileType`, `computeFutureOf`, `HasEdge` |
| `BuildChoiceAutomatonDefs` | `buildChoiceAutomaton` (ordinary and fair) |
| `BuildSequenceAutomatonDefs` | `buildSequenceAutomaton` and its redirect edges |
| `BuildParallelAutomaton` | the synchronized product, survivor and done edge families |
| `BuildRecursionAutomatonDefs` | `buildRecursionAutomaton` |
| `BuildOfferAutomataDefs` | `buildExclusiveOfferAutomaton`, `buildSelectedConjunctiveOfferAutomaton` |
| `SequenceMenuLemmas` | `menuFrom` |

## Notes

**`compileType` does not filter by alphabet.** Its edges are exactly the
`.visible` edges of the constructed fragment, resolved: `.variable` labels map
to `∅`, `.visible` to a singleton. `transitionAlphabet` names the automaton's
alphabet without restricting its edges. So raw fragment edges and public
`HasEdge`s differ only by the recursion markers.

**`FutureSpec.at q removed` resolves to `computeFutureOf q \ removed`.**
Construction-only `.future` edges contribute to the menu but are not steps.

**Markers carry environments.** `buildRecursionAutomaton` copies a marker
edge's environment onto the backedge it installs, so matching a semantic step
with a specific `E` requires a marker edge carrying that same `E`.
