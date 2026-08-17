# Type/automaton correspondence modules

This directory proves that `DecoratedTypeTransition` and the automaton produced
by `compileType` have exactly the same public steps at related states.

The development is mid-redevelopment against a doc-accurate `computeFutureOf`
automaton construction; most declarations below carry a `sorry` proof with
their statement kept where it is still a documented, general fact.

| File | Summary |
|---|---|
| [`CorrespondenceCore.lean`](CorrespondenceCore.lean) | Aggregate core layer: defines `TypeCompilationRelation`, initial/state/future-target invariants, future/completing/step correctness predicates, parallel environment reconstruction helpers, `TypeAutomatonCorrespondence`, and the complete atomic correspondence cases. |
| [`CorrespondenceVisibility.lean`](CorrespondenceVisibility.lean) | Proves compiler-label and alphabet-visibility facts, especially that relevant pending edges become public visible labels and that public resolved edges satisfy the required filters. |
| [`CorrespondenceParallel.lean`](CorrespondenceParallel.lean) | Classifies resolved synchronized product edges and proves both directions between semantic parallel steps and compiled product edges, including target representation. |
| [`CorrespondenceOffers.lean`](CorrespondenceOffers.lean) | Aggregate exclusive/conjunctive offer proof: graph classifiers, future equations, step correctness, parallel-interface transport, and resolved-target representation. |
| [`CorrespondenceChoice.lean`](CorrespondenceChoice.lean) | Proves future and public step correctness for ordinary and fair choice, including tagged child edges, root selection edges, and reverse edge classification. |
| [`CorrespondenceSequenceGraph.lean`](CorrespondenceSequenceGraph.lean) | Defines the non-clock `sequenceExecutionAutomaton`/fragment and develops the graph reachability, future, completion-witness, and root/child equations needed by sequence and recursion. |
| [`CorrespondenceSequence.lean`](CorrespondenceSequence.lean) | Classifies sequence left/right/bridge edges and proves raw/public step correctness and completing correctness for sequence. |
| [`CorrespondenceCompleting.lean`](CorrespondenceCompleting.lean) | Proves completing correctness for choice, fair choice, parallel, exclusive offers, branch combinations, and conjunctive offers; also proves the main parallel future-correctness theorem. |
| [`CorrespondenceRecursionHeader.lean`](CorrespondenceRecursionHeader.lean) | Proves the recursion header edge and its semantic unfolding step, classifies installed recursion-body edges, and defines the body future/step contracts used by later recursion leaves. |
| [`CorrespondenceBundle.lean`](CorrespondenceBundle.lean) | Defines `CompilationSequenceExecutionCorrect` and the four-field `CompilationProofBundle`; transports regularity into branches and supplies auxiliary nested-recursion completion results. |
| [`CorrespondenceSequenceExecutionLeaves.lean`](CorrespondenceSequenceExecutionLeaves.lean) | Proves the execution-view invariant for atomic types, ordinary/fair choice, and sequence. |
| [`CorrespondenceFragmentStepLeaves.lean`](CorrespondenceFragmentStepLeaves.lean) | Proves raw fragment step leaves for atomic types, ordinary choice, and fair choice, with exact constructor edge classifications. |
| [`CorrespondenceSequenceAssembly.lean`](CorrespondenceSequenceAssembly.lean) | Assembles sequence future/scoped-step correctness, proves resolved-edge target representation for constructor families, and packages parallel scoped-step/execution leaves. |
| [`CorrespondenceRegularityCore.lean`](CorrespondenceRegularityCore.lean) | Transports all-bound, binder-freshness, and tail-occurrence invariants through `TypeCompilationRelation`; proves variable-edge and marker-inertness facts used by recursion. |
| [`CorrespondenceMarkerSkipping.lean`](CorrespondenceMarkerSkipping.lean) | Establishes first-wave marker reachability facts, proves every compiled skipping state represents literal `skip`, and develops completion-evaluation lemmas for branch combinations. |
| [`CorrespondenceCompletingRepresented.lean`](CorrespondenceCompletingRepresented.lean) | Mutually proves non-clock predecessor soundness for `completionEval` and that every compiled completing state represents a semantically completing residual. |
| [`CorrespondenceRecursionClosureCore.lean`](CorrespondenceRecursionClosureCore.lean) | Proves the soundness direction for recursion-body completion closure and the substitution/tail/evaluation invariants used by closure completeness. |
| [`CorrespondenceRecursionClosureLift.lean`](CorrespondenceRecursionClosureLift.lean) | Lifts completing-back-closure witnesses through child tags, nested recursion, and branch-selection structures. |
| [`CorrespondenceRecursionClosureSuperset.lean`](CorrespondenceRecursionClosureSuperset.lean) | Proves the structural completeness theorem `recursionBodyCompletingClosure_superset_aux`: semantic substituted completion implies membership in the compiler closure. |
| [`CorrespondenceRecursionClosure.lean`](CorrespondenceRecursionClosure.lean) | Combines closure soundness/completeness into `recursionBodyCompletingClosure_iff` and derives completing correctness for a regular recursion binder. |
| [`CorrespondenceMarkerReachability.lean`](CorrespondenceMarkerReachability.lean) | Proves that syntax marker analysis exactly matches marker reachability in both the raw compiled fragment and its sequence-execution view. It also proves that marker-stopping preserves execution future menus. |
| [`CorrespondenceRecursionLeaf.lean`](CorrespondenceRecursionLeaf.lean) | Proves exact future-policy transport through capture-safe recursion substitution, closes marker/non-marker scoped body steps, proves recursion execution correctness with a shadow graph, and packages the bounded recursion bundle. |
| [`CorrespondenceXOfferLeaf.lean`](CorrespondenceXOfferLeaf.lean) | Combines child bundles and regularity facts into the complete four-field bundle for an exclusive offer. |
| [`CorrespondenceOfferBranchLeaf.lean`](CorrespondenceOfferBranchLeaf.lean) | Builds bundles for `parallelTypeBranches` and `parallelTypeBranchesSelecting`, shared by exclusive and conjunctive offer constructors. |
| [`CorrespondenceOfferLeaf.lean`](CorrespondenceOfferLeaf.lean) | Proves the selected-conjunction execution invariant and combines all child/branch facts into the complete conjunctive-offer bundle. |
| [`CorrespondenceAssembly.lean`](CorrespondenceAssembly.lean) | Performs the terminating constructor-by-constructor construction `compilationProofBundle_of_boundedRegular`, specializes it to closed regular types, and exports public step correctness used by Lemma 4.5. |

## Main proof flow

```text
TypeCompilationRelation
  └─ constructor future/completing/scopedStep/execution leaves
       └─ CompilationProofBundle
            └─ compilationProofBundle_of_boundedRegular
                 └─ compilationProofBundle_of_closedGuardedRegular
                      └─ compilationStepCorrect_of_closedGuardedRegular
                           └─ Pact.type_automaton_correspondence
```

For theorem statements and English explanations, start with the
[top-down theorem reference](../CORRESPONDENCE_THEOREMS.md). See also the
[PactTypes overview](../README.md), [syntax summary](../Syntax/README.md), and
[automata summary](../Automata/README.md).
