# Anvilpp.PactTypes

Formalization of the Pact type system (paper §4): the type grammar and its
operational semantics, the constructor-automaton compiler, and the
correspondence proof between the two. `Anvilpp/PactTypes.lean` is the import
façade for the whole development — external code should `import
Anvilpp.PactTypes` and not reach into individual submodules.

## Layout

```
Anvilpp/PactTypes.lean          facade — imports Correspondence.CorrespondenceAssembly

Anvilpp/PactTypes/
├── Syntax/                     type grammar, substitution, operational semantics
├── Automata/                   constructor-automaton compiler
├── Correspondence/             compiler ↔ operational-semantics correspondence proof
└── README.md                   this file
```

Each subdirectory is one namespace's worth of Lean modules, split by proof
concern rather than kept as a single file. Every declaration lives in exactly
one file; nothing is duplicated across the split.

## Dependency order

Imports form a single linear chain across all three directories:

```
Syntax/PactTypeSyntax
  → Syntax/PactTypeRegularity → Syntax/TypeErasure → Syntax/TypeDynamicsCore
  → Syntax/TypeCompletionFuel → Syntax/TypeFutureOffersFuel
  → Syntax/PactTypeCompletionEval → Syntax/PactTypeSubstitutionLemmas
  → Syntax/PactTypeFutureOffers → Syntax/TypeTransitionSystem
  → Automata/TypeAlphabet → Automata/AutomatonFragment
  → Automata/PendingAutomatonFuture → Automata/MarkerReachability
  → Automata/SyncEdges → Automata/CompletingBackClosure
  → Automata/BuildRecursionAutomaton → Automata/BuildChoiceAutomaton
  → Automata/BuildSequenceAutomaton → Automata/BuildParallelAutomaton
  → Automata/BuildOfferAutomata → Automata/CompileType
  → Correspondence/CorrespondenceCore → Correspondence/CorrespondenceVisibility
  → Correspondence/CorrespondenceParallel → Correspondence/CorrespondenceOffers
  → Correspondence/CorrespondenceChoice → Correspondence/CorrespondenceSequenceGraph
  → Correspondence/CorrespondenceSequence → Correspondence/CorrespondenceCompleting
  → Correspondence/CorrespondenceRecursionHeader → Correspondence/CorrespondenceBundle
  → Correspondence/CorrespondenceSequenceExecutionLeaves
  → Correspondence/CorrespondenceFragmentStepLeaves
  → Correspondence/CorrespondenceSequenceAssembly
  → Correspondence/CorrespondenceRegularityCore
  → Correspondence/CorrespondenceMarkerSkipping
  → Correspondence/CorrespondenceCompletingRepresented
  → Correspondence/CorrespondenceRecursionClosureCore
  → Correspondence/CorrespondenceRecursionClosureLift
  → Correspondence/CorrespondenceRecursionClosureSuperset
  → Correspondence/CorrespondenceRecursionClosure
  → Correspondence/CorrespondenceMarkerReachability
  → Correspondence/CorrespondenceRecursionLeaf
  → Correspondence/CorrespondenceXOfferLeaf
  → Correspondence/CorrespondenceOfferBranchLeaf
  → Correspondence/CorrespondenceOfferLeaf
  → Correspondence/CorrespondenceAssembly
```

Each file imports only its immediate predecessor, which transitively imports
everything before it. This means, in every file, "what's available" is
exactly "everything defined earlier in this list" — reading the reference
tables below top to bottom is reading the development in dependency order.

The one structural exception: `Correspondence/CorrespondenceCompletingRepresented.lean`
holds a `mutual` block (`compiledFragmentNonClockPredecessor_eval` together
with `compiledFragmentCompleting_represented`) — Lean requires mutually
recursive declarations to stay in one file, so this is the one file in the
chain that cannot be split further along its current proof structure.

## `Syntax/` — type grammar and operational semantics

| Module | Contents |
|---|---|
| `PactTypeSyntax` | The `PactType` grammar (§4.1); capture-avoiding substitution (`replaceVar`, `replaceBranches`); `BinderFreshFor`; `MustTockBeforeCompletion`; `GuardedOccurrences`; `AllVariablesBound`; `BinderHygienic`; and their transport lemmas (`binderHygienic_mono`, `replaceVar_comm`, `binderFreshFor_mono`, ...). |
| `PactTypeRegularity` | The regularity predicates the correspondence proof's leaf theorems assume: `ClockGuarded`, `TailOccurrences`/`AllTailOccurrences`, `TailRecursive`, `CanCompleteBeforeTock`, `Prefix`/`SuffixMessageIds`, `SameCycleMessageLinear`, `ParallelInterfaces`, `InterfaceScoped`. |
| `TypeErasure` | `TypeObservation`, `TypeLabel`, erasure of process-level `Observation`/`Label` to their type-level counterparts, `TypeEnvironment` and its erasure. |
| `TypeDynamicsCore` | Offer/branch helpers: `typeNeed`, `typeBranchNeeds`, `TypeResolved`, `TypeNoImmediateBranch`, `TypeBranchEnabled`, `singletonTypeXOffer`, `selectedTypeBranch`, `parallelTypeBranches(Selecting)`, `typeBranchActions`, interface restriction/hiding. |
| `TypeCompletionFuel` | `typeCanCompleteThisCycleFuel`, the fuel-bounded implementation behind `CanCompleteBeforeTock`, and its stability/substitution lemmas. |
| `TypeFutureOffersFuel` | `typeFutureOffersFuel` and its stability lemmas; `typeFutureOffers`, the fuel-independent closure. |
| `PactTypeCompletionEval` | The valuation-polymorphic `completionEval` (needed because `TypeCompilationRelation`'s recursion case cannot fix the motive to one bound name) and its congruence/substitution/hygiene transport. |
| `PactTypeSubstitutionLemmas` | How substitution and tail-occurrence facts interact with `CanCompleteBeforeTock`/`completionEval`. |
| `PactTypeFutureOffers` | Per-constructor `typeFutureOffers_*` equations; `replaceVar_typeFutureOffers`; `futureOffersSubst_eq_union_marker`; `markerReachableSubst_replaceVar`. |
| `TypeTransitionSystem` | The operational judgment `TypeTransition`, `DecoratedTypeTransition`, `Conforms`/`Refines`/`DataObliviousChecks`. |

## `Automata/` — constructor automaton compiler

| Module | Contents |
|---|---|
| `TypeAlphabet` | The fixed finite alphabet `TypeAlphabet` and the transition-symbol encoding `TypeAutomatonSymbol`. |
| `AutomatonFragment` | Core representation: `TypeAutomatonState`, `AutomatonConstructionLabel`, `FutureSpec`, `PendingAutomatonEdge`, `AutomatonFragment`, `AutomatonFragmentEdge`, `PendingAutomaton`. |
| `PendingAutomatonFuture` | `computeFuture`: the finite future-offer closure over a `PendingAutomaton`, and its stability/embedding lemmas. |
| `MarkerReachability` | Marker-augmented future resolution (`markerAugmentedPending`, `MarkerSource`, `MarkerEdgesInert`) and same-cycle marker reachability (`MarkerReachable`); the indexed child-fragment helpers (`childState`, `childPendingEdge`, ...). |
| `SyncEdges` | Interface hiding and synchronized-edge construction for parallel products (`hideOffers`, `syncAutomatonEdges`). |
| `CompletingBackClosure` | Backward completion closure (`completingBackClosure` and its fixed-point/monotonicity lemmas) used to seed recursion-body completing sets; `taggedFragment`. |
| `BuildRecursionAutomaton` | `buildRecursionAutomaton` and its future/marker/completing correspondence lemmas. |
| `BuildChoiceAutomaton` | `buildChoiceAutomaton`. |
| `BuildSequenceAutomaton` | `buildSequenceAutomaton`. |
| `BuildParallelAutomaton` | Reachable-fragment restriction and `buildParallelAutomaton`. |
| `BuildOfferAutomata` | Indexed branch-fragment helpers and `buildExclusiveOfferAutomaton`/`buildConjunctiveOfferAutomaton`/`buildSelectedConjunctiveOfferAutomaton`. |
| `CompileType` | The constructor compiler proper: `typeCompilationFuel`, `compileTypeFuel`, `compileType`, `AutomatonFragment.HasResolvedEdge`, and resolved-edge helpers. |

## `Correspondence/` — compiler ↔ operational-semantics correspondence

| Module | Contents |
|---|---|
| `CorrespondenceCore` | `TypeCompilationRelation` (state ↔ residual), `CompilationStateCorrect`, `CompilationFutureCorrect`, `CompilationStepCorrect`, and the atomic-constructor base cases. |
| `CorrespondenceVisibility` | Visibility/alphabet-filtering lemmas for compiled edges. |
| `CorrespondenceParallel` | Resolved product-edge classifiers and synchronization reconstruction. |
| `CorrespondenceOffers` | Correspondence for the exclusive/conjunctive offer constructors. |
| `CorrespondenceChoice` | Ordinary and fair-choice future/step correspondence. |
| `CorrespondenceSequenceGraph` | `sequenceExecutionEdge`/`Automaton`/`Fragment` and the graph-reachability scaffolding (`sequenceExecution_*`, `buildSequenceAutomaton_*`) sequence completion is built on. |
| `CorrespondenceSequence` | Sequence correspondence: future, step, and completing correctness. |
| `CorrespondenceCompleting` | Completing correctness for choice/fairChoice/parallel/xoffer/parallelTypeBranches/offer, and the parallel future-correspondence theorem. |
| `CorrespondenceRecursionHeader` | The recursion header edge and closed recursion-fragment correspondence: `RecursionHeaderFutureCorrect`, `RecursionBodyFutureCorrect`, `RecursionBodyStepCorrect`, `compilationStepCorrect_recursion`. |
| `CorrespondenceBundle` | `CompilationSequenceExecutionCorrect`, the `CompilationProofBundle` structure, branch-regularity transport lemmas, and vanilla (unsubstituted) nested-recursion completing correctness. |
| `CorrespondenceSequenceExecutionLeaves` | `CompilationSequenceExecutionCorrect` leaves: skip/progress/var/tock/message/choice/fairChoice/sequence. |
| `CorrespondenceFragmentStepLeaves` | `CompilationFragmentStepCorrect` leaves: skip/message/tock/progress/choice/fairChoice. |
| `CorrespondenceSequenceAssembly` | `compilationFutureCorrect_sequence`, the `compilationResolvedEdgeTargetsRelated_*` family, and the parallel leaf assembly. |
| `CorrespondenceRegularityCore` | Regularity transport: `compileTypeFuel_skipping_subset_completing`, `compilationRelation_allVariablesBound`/`binderFreshFor`/`tailOccurrences_false`, `compileTypeFuel_variableEdge_source_var`, `compileTypeFuel_markerEdgesInert`. |
| `CorrespondenceMarkerSkipping` | First-wave marker reachability vs. the syntactic marker analysis, and `compiledFragmentSkipping_represented`. |
| `CorrespondenceCompletingRepresented` | `compiledFragmentCompleting_represented`, proved by mutual induction with `compiledFragmentNonClockPredecessor_eval`. |
| `CorrespondenceRecursionClosureCore` | Substituted-completion regularity lemmas feeding the recursion completing-closure argument (`canCompleteBeforeTockSubst_false`, `completionEval_eq_canCompleteBeforeTock_of_tailFalse`, `compilationRelation_tailOccurrences_true`, ...). |
| `CorrespondenceRecursionClosureLift` | The completing-back-closure lifting lemmas (`completingBackClosure_lift_*`). |
| `CorrespondenceRecursionClosureSuperset` | `recursionBodyCompletingClosure_superset_aux`. |
| `CorrespondenceRecursionClosure` | `recursionBodyCompletingClosure_iff` and `compilationCompletingCorrect_recursion_regular_leaf`. |
| `CorrespondenceMarkerReachability` | Marker reachability vs. the syntactic marker analysis for the remaining constructors, and the main induction `compilationMarkerReachable_iff`. |
| `CorrespondenceRecursionLeaf` | `compileTypeFuel_futureReferencesTarget`, `RecursionBodyScopedStepCorrect`, and the bounded (open-body) recursion leaf assembly. |
| `CorrespondenceXOfferLeaf` | The `xoffer` regular leaf. |
| `CorrespondenceOfferBranchLeaf` | `parallelTypeBranches`/`parallelTypeBranchesSelecting` leaves shared by `xoffer` and `offer`. |
| `CorrespondenceOfferLeaf` | The `offer` regular leaf. |
| `CorrespondenceAssembly` | Top-level assembly: `compilationProofBundle_of_boundedRegular`, `compilationProofBundle_of_closedGuardedRegular`, `compilationStepCorrect_of_closedGuardedRegular`, `ProcessAutomatonCorrespondence`. |

## Conventions

- **One file per proof concern**, not per fixed line budget. A module
  boundary always falls between complete declarations (and outside every
  `mutual` block), never mid-theorem.
- **Import order is dependency order.** A module imports exactly its
  predecessor in the chain above; there is no back-referencing or forward
  declaration anywhere in the development.
- **Visibility.** A declaration is `private` unless something outside its
  own file needs it. When in doubt, check the importing file rather than
  assuming — `private` here always means "used only within this module."
- **Proof status.** The live account of what's proved, what's open, and why
  — including the two outstanding `sorry`s, both in
  `Correspondence/CorrespondenceRecursionLeaf.lean` — is `AGENT.md` at the
  repository root. This README describes structure, not proof state; it does
  not go stale as the proof progresses.
