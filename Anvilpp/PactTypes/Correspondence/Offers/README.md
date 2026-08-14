# Extracted offer-correspondence modules

This directory is the finer-grained extraction of the large aggregate
`CorrespondenceOffers.lean` concern. It separates graph structure, resolved
edge classification, future correctness, step correctness, and target
representation for exclusive and conjunctive offers.

The public `Anvilpp.PactTypes` façade currently follows the aggregate module
path. Until that path is migrated, do not import these extracted modules and
`CorrespondenceOffers.lean` together, because they expose the same declarations
under namespace `Pact`.

| File | Summary |
|---|---|
| [`ParallelInterfaceTransport.lean`](ParallelInterfaceTransport.lean) | Proves interface-subset and `InterfaceScoped` transport for `parallelTypeBranches` and `parallelTypeBranchesSelecting`. |
| [`ExclusiveOfferGraph.lean`](ExclusiveOfferGraph.lean) | Describes exclusive-offer child/root outgoing edges, entry states, root `offersAt`, root reference bounds, and root/child `computeFuture` behavior. |
| [`ExclusiveOfferResolvedEdge.lean`](ExclusiveOfferResolvedEdge.lean) | Gives the exact `HasResolvedEdge` classifier at the fresh exclusive-offer root, separating enabled branch, else, and unresolved waiting behavior. |
| [`ConjunctiveOfferGraph.lean`](ConjunctiveOfferGraph.lean) | Describes the all-branches conjunctive helper graph, its tagged entries, root offers/references, and root/child future computations. |
| [`ConjunctiveOfferResolvedEdge.lean`](ConjunctiveOfferResolvedEdge.lean) | Gives the exact resolved-edge classifier at the fresh conjunctive-helper root. |
| [`SelectedConjunctiveOfferGraph.lean`](SelectedConjunctiveOfferGraph.lean) | Describes the graph for a selected conjunctive branch plus else path and proves its root outgoing-edge, offer, reference, future, and resolved-edge equations. |
| [`OfferEdgeClassifiers.lean`](OfferEdgeClassifiers.lean) | Classifies tagged child edges for `xoffer` and `offer`, translating indexed compiler states back to branch-list membership and the appropriate selected branch type. |
| [`XOfferStepCorrect.lean`](XOfferStepCorrect.lean) | Proves raw, scoped, and public step correctness for exclusive offers by matching enabled branch, else, and wait cases. |
| [`XOfferFutureCorrect.lean`](XOfferFutureCorrect.lean) | Proves `compilationFutureCorrect_xoffer_of_children`, lifting correct child future menus through the exclusive-offer graph. |
| [`OfferFutureCorrect.lean`](OfferFutureCorrect.lean) | Proves `compilationFutureCorrect_offer_of_children`, including future menus of selected conjunctive branch combinations. |
| [`OfferStepCorrect.lean`](OfferStepCorrect.lean) | Proves scoped fragment-step correctness for conjunctive offers, matching enabled conjunction, resolved else, and unresolved wait cases. |
| [`ResolvedEdgeTargetsRelated.lean`](ResolvedEdgeTargetsRelated.lean) | Proves that resolved `xoffer` and `offer` edges from represented sources always reach states representing the corresponding semantic residuals. |

Import order is:

```text
ParallelInterfaceTransport
  → ExclusiveOfferGraph
  → ExclusiveOfferResolvedEdge
  → ConjunctiveOfferGraph
  → ConjunctiveOfferResolvedEdge
  → SelectedConjunctiveOfferGraph
  → OfferEdgeClassifiers
  → XOfferStepCorrect
  → XOfferFutureCorrect
  → OfferFutureCorrect
  → OfferStepCorrect
  → ResolvedEdgeTargetsRelated
```

The final four-field offer bundles live in the parent directory:
`CorrespondenceXOfferLeaf.lean`, `CorrespondenceOfferBranchLeaf.lean`, and
`CorrespondenceOfferLeaf.lean`.

See the [parent correspondence summary](../README.md), the
[PactTypes overview](../../README.md), and the
[top-down theorem reference](../../CORRESPONDENCE_THEOREMS.md).
