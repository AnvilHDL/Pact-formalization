# Pact type automata modules

This directory defines the finite graph representation, the constructor
automata, the future/completion fixed points, and the canonical compiler from
`PactType` to `TypeAutomaton`.

| File | Summary |
|---|---|
| [`TypeAlphabet.lean`](TypeAlphabet.lean) | Defines the finite `TypeAlphabet`, its well-formedness/support predicates, and the `TypeAutomatonSymbol` encoding of an environment, semantic label, and current/future offer summary. |
| [`AutomatonFragment.lean`](AutomatonFragment.lean) | Defines construction states and labels, `FutureSpec`, pending edges, pending automata, automaton fragments, finished edges, and the state/edge invariants shared by all builders. |
| [`PendingAutomatonFuture.lean`](PendingAutomatonFuture.lean) | Defines future-reference reachability and `computeFuture`, the finite same-cycle offer closure used to resolve `FutureSpec.at`. It proves unfolding, closure, embedding, and same-edge invariance results. |
| [`MarkerReachability.lean`](MarkerReachability.lean) | Defines temporary recursion-marker sources, marker-augmented and marker-stopped graphs, `MarkerReachable`, resolved fragment edges, and the indexed child-state/edge tagging helpers used by constructor builders. |
| [`SyncEdges.lean`](SyncEdges.lean) | Defines interface offer hiding and the synchronized-edge construction used by parallel products, together with its witness projections and basic invariants. |
| [`CompletingBackClosure.lean`](CompletingBackClosure.lean) | Defines the finite backward closure that repeatedly adds sources of non-clock edges reaching a completion seed. It proves fixed-point, monotonicity, predecessor-closure, graph-agreement, and tagged-fragment transport lemmas. |
| [`BuildRecursionAutomaton.lean`](BuildRecursionAutomaton.lean) | Builds recursion headers and installs matching variable backedges. It proves exact future equations for marker/no-marker states, marker reachability equations, future-target closure, and the completing-set equation. |
| [`BuildChoiceAutomaton.lean`](BuildChoiceAutomaton.lean) | Builds ordinary and fair-choice graphs by adding a fresh root and tagging both child fragments, including the root selection edges and state/future-target invariants. |
| [`BuildSequenceAutomaton.lean`](BuildSequenceAutomaton.lean) | Builds sequence graphs from tagged left/right fragments, including completion bridge edges from the left into the right entry and the relevant future-target invariant. |
| [`BuildParallelAutomaton.lean`](BuildParallelAutomaton.lean) | Builds the synchronized product, adds construction-only optimistic future-observation edges, and restricts the result to states reachable from the product entry. |
| [`BuildOfferAutomata.lean`](BuildOfferAutomata.lean) | Defines indexed branch-fragment folds and builds exclusive offers, all-branch conjunctive offers, and selected conjunctive offers with their tagged entries and root edges. |
| [`CompileType.lean`](CompileType.lean) | Defines structural compilation fuel, proves fuel sufficiency and irrelevance, implements `compileTypeFuel`, finishes the canonical fragment as `compileType`, and connects public automaton edges to resolved fragment edges. |

## Construction pipeline

```text
PactType
  └─ compileTypeFuel signature fuel
       └─ constructor-specific AutomatonFragment
            ├─ pending edges with FutureSpec
            ├─ skipping/completing metadata
            └─ construction-only marker/future edges
                 │
                 ▼
       finishAutomatonFragment / resolve with computeFuture
                 │
                 ▼
              TypeAutomaton
```

Construction-only `.variable` and `.future` labels are graph devices, not
public type transitions. Variable edges are consumed when recursion backedges
are installed; future-observation edges remain available to optimistic future
resolution but are excluded from the public resolved-edge relation.

See the [PactTypes overview](../README.md), the
[syntax module summary](../Syntax/README.md), and the
[top-down theorem reference](../CORRESPONDENCE_THEOREMS.md).
