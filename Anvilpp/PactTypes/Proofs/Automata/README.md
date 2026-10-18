# Compiler Laws

| Module | Results |
|---|---|
| `CompileTypeLemmas` | Sufficient-fuel stability and resolved/public edge agreement |
| `FiniteMenuGraph` | Finite reference closure and embedding invariance |
| `PendingAutomatonFutureLemmas` | Non-clock execution closure and future-reference closure |
| `MenuDependenciesLemmas` | Optimistic menu-dependency transport |
| `RecursionMenuLemmas` | Menu closure under recursive copying and pruning |
| `MarkerAbsenceLemmas`, `MarkerReachabilityLemmas` | Marker exclusion and reachability through constructors |
| `BuildChoiceAutomatonLemmas` | Root and child edge characterizations |
| `BuildSequenceAutomatonLemmas` | Accepting redirection and copied-edge membership |
| `BuildOfferAutomataLemmas` | Offer-root and indexed-branch edge membership |
| `AtomicConjunctiveOffer` | Exact batch firing, root menus, copied targets, and clock exclusion |
| `BuildParallelAutomatonLemmas` | Product shape, clock edges, and target closure |
| `BuildRecursionAutomatonLemmas` | Header, body, and recursive backedge membership |
| `SyncEdgesLemmas` | Synchronized edge and local-environment properties |
| `TypeAlphabetLemmas` | Finite environment membership and well-formedness |

`compileTypeFuel_eq_of_sufficient` makes the compiler independent of the
chosen sufficient fuel. Constructor proofs use it to compare child fragments
with their canonical compilations.
