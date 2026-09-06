# Anvilpp.PactTypes.Proofs.Automata

Laws of the compiler and of compiled fragments, independent of the type
semantics.

| Module | Main results |
|---|---|
| `CompileTypeLemmas` | `typeCompilationFuel_sufficient` and `compileTypeFuel_eq_of_sufficient` (fuel irrelevance); `compileType_hasEdge_iff_hasResolvedEdge`, identifying a public edge with a resolved pending edge |
| `MarkerAbsenceLemmas` | where recursion markers cannot occur: `compileTypeFuel_noMarkerFor`, one `_noMarkerFor` per builder, and the `markerSource` transports |
| `FiniteMenuGraph` | `futureReachable` as a finite fixed point, with its embedding invariance |
| `PendingAutomatonFutureLemmas` | `referencesClosed_of_futureTargetsInStates` and the `futureReachableAux` equations |
| `BuildOfferAutomataLemmas` | offer-graph edge shape; `mem_foldl_union_iff` for the `foldl`-built branch edge sets |
| `BuildRecursionAutomatonLemmas` | `buildRecursionAutomaton_markerSource_child`, `not_..._markerSource_root` |
| `BuildSequenceAutomatonLemmas` | `sequenceRedirect_of_accepting`, `mem_sequenceDeleted_iff` |
| `BuildChoiceAutomatonLemmas` | outgoing-edge characterisations for the children and the root |
| `BuildParallelAutomatonLemmas` | `buildParallelAutomaton_clockEdgesAreTock`, `_futureTargetsInStates` |
| `RecursionMenuLemmas` | `futureReachable_recur_child`, `menuFrom_eq_of_pruning` |
| `MenuDependenciesLemmas` | laws of the optimistic menu edges |
| `TypeAlphabetLemmas` | `empty_mem_localEnvironments`, `environment_wellFormed` |

## Note

`compileTypeFuel` takes a fuel argument so the compiler is structurally
recursive. `compileTypeFuel_eq_of_sufficient` says any sufficient budget gives
the same fragment; `compileType` fixes the canonical one. Proofs about compound
constructors normally begin by normalising fuel with it.
