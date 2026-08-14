# Anvilpp.PactTypes

Formalization of the Pact type system from paper §4: type syntax and
operational semantics, the constructor-automaton compiler, and the proof that
the operational type and compiled automaton take exactly the same decorated
steps. External modules should normally import the façade:

```lean
import Anvilpp.PactTypes
```

## Current result

The type-level correspondence is complete. For every `AdmissibleType
signature processType`, theorem `type_automaton_correspondence` constructs a
`TypeAutomatonCorrespondence processType (compileType signature processType)`.
The relation used by that witness is `TypeCompilationRelation`.

The proof is not merely a top-level step induction. It builds a reusable
`CompilationProofBundle` for every bounded regular syntax tree. The bundle
contains:

| Field | Meaning |
|---|---|
| `future` | `computeFuture` at a compiled state equals the syntax-derived `typeFutureOffers` of its represented residual. |
| `completing` | Compiled completing metadata agrees with `CanCompleteBeforeTock`. |
| `scopedStep` | Decorated semantic steps are equivalent to resolved fragment edges in local environments that avoid nested parallel interfaces. |
| `execution` | The non-clock execution view has the right future menu and reaches a skipping/completing state exactly when the residual can complete this cycle. |

`compilationProofBundle_of_boundedRegular` constructs these fields together by
well-founded recursion on syntax size. The closed specialization
`compilationProofBundle_of_closedGuardedRegular` feeds
`compilationStepCorrect_of_closedGuardedRegular`, which supplies the `stepIff`
field of the final correspondence witness.

The separate `process_automaton_correspondence` theorem is still admitted; its
status must not be conflated with the completed type-level theorem.

For a top-down list of the important declarations and English statements, see
[`CORRESPONDENCE_THEOREMS.md`](CORRESPONDENCE_THEOREMS.md). For the chronological
proof-engineering record and failed approaches, see [`AGENT.md`](../../AGENT.md).

Each implementation directory also has a per-file summary:

- [`Syntax/README.md`](Syntax/README.md)
- [`Automata/README.md`](Automata/README.md)
- [`Correspondence/README.md`](Correspondence/README.md)
- [`Correspondence/Core/README.md`](Correspondence/Core/README.md)
- [`Correspondence/Offers/README.md`](Correspondence/Offers/README.md)

## Layout

```text
Anvilpp/PactTypes.lean          public façade; imports final assembly

Anvilpp/PactTypes/
├── Syntax/                    type language and operational semantics
├── Automata/                  graph representation and compiler
├── Correspondence/            compiler/semantics proof
│   ├── Core/                  finer-grained core extraction modules
│   └── Offers/                finer-grained offer extraction modules
├── CORRESPONDENCE_THEOREMS.md theorem-oriented proof guide
└── README.md                  this structural overview
```

The live public assembly path currently ends at
`Correspondence/CorrespondenceAssembly.lean`. The flat
`CorrespondenceCore.lean` and `CorrespondenceOffers.lean` modules remain on
that path. The `Correspondence/Core/` and `Correspondence/Offers/` trees are
the finer-grained extraction of those large proof concerns and build as
separate module chains. Until the public assembly is migrated to those chains,
do not import an aggregate module and its extracted mirror into the same Lean
module: they expose the same Pact declarations under different module names.

## Syntax layer

| Module | Main responsibility |
|---|---|
| `PactTypeSyntax` | `PactType`, `replaceVar`, branch substitution, `AllVariablesBound`, `BinderHygienic`, `BinderFreshFor`, and capture-safe substitution laws such as `replaceVar_comm`. |
| `PactTypeRegularity` | `ClockGuarded`, `TailRecursive`, `SameCycleMessageLinear`, `ParallelInterfaces`, and `InterfaceScoped`. |
| `TypeErasure` | Type observations, labels, environments, and process-to-type erasure. |
| `TypeDynamicsCore` | Branch enabling, offer summaries, parallel branch types, and interface restriction/hiding. |
| `TypeCompletionFuel` | Fuel-bounded implementation of completion before `tock`. |
| `TypeFutureOffersFuel` | Fuel-bounded implementation of same-cycle future offers. |
| `PactTypeCompletionEval` | Valuation-parametric completion evaluation used under open recursion binders. |
| `PactTypeSubstitutionLemmas` | Completion and tail-occurrence transport through substitution. |
| `PactTypeFutureOffers` | Constructor equations for `typeFutureOffers`, marker analysis, and recursion substitution equations. |
| `TypeTransitionSystem` | `TypeTransition`, `DecoratedTypeTransition`, conformance, and refinement definitions. |

The capture-safety predicates are proof-relevant. In particular,
`BinderHygienic` is transported through `TypeCompilationRelation` to obtain
`BinderFreshFor`, which is the premise needed to commute substitutions through
nested recursion binders.

## Automata layer

| Module | Main responsibility |
|---|---|
| `TypeAlphabet` | Finite type environments, labels, offer summaries, and `TypeAutomatonSymbol`. |
| `AutomatonFragment` | Construction states, pending edges, `FutureSpec`, fragments, and finished edges. |
| `PendingAutomatonFuture` | `futureReachable`, `computeFuture`, same-edge and embedding invariance. |
| `MarkerReachability` | Temporary recursion markers, marker-stopped fragments, and marker reachability. |
| `SyncEdges` | Interface hiding and synchronized parallel edges. |
| `CompletingBackClosure` | Finite non-clock predecessor closure used for recursion completion. |
| `BuildRecursionAutomaton` | Installs recursive backedges and proves their future/completing equations. |
| `BuildChoiceAutomaton` | Ordinary and fair-choice constructor graphs. |
| `BuildSequenceAutomaton` | Sequence constructor graph and bridge edges. |
| `BuildParallelAutomaton` | Reachable synchronized product and future-observation edges. |
| `BuildOfferAutomata` | Exclusive and conjunctive offer graphs. |
| `CompileType` | `typeCompilationFuel`, `compileTypeFuel`, fuel irrelevance, `compileType`, and public resolved edges. |

`FutureSpec.at q removed` is resolved as `computeFuture q \ removed`.
Construction-only `.future` edges participate in optimistic future
computation but do not become public semantic steps.

## Correspondence layer

The aggregate public dependency path is:

```text
CorrespondenceCore
  → CorrespondenceVisibility
  → CorrespondenceParallel
  → CorrespondenceOffers
  → CorrespondenceChoice
  → CorrespondenceSequenceGraph
  → CorrespondenceSequence
  → CorrespondenceCompleting
  → CorrespondenceRecursionHeader
  → CorrespondenceBundle
  → CorrespondenceSequenceExecutionLeaves
  → CorrespondenceFragmentStepLeaves
  → CorrespondenceSequenceAssembly
  → CorrespondenceRegularityCore
  → CorrespondenceMarkerSkipping
  → CorrespondenceCompletingRepresented
  → CorrespondenceRecursionClosureCore
  → CorrespondenceRecursionClosureLift
  → CorrespondenceRecursionClosureSuperset
  → CorrespondenceRecursionClosure
  → CorrespondenceMarkerReachability
  → CorrespondenceRecursionLeaf
  → CorrespondenceXOfferLeaf
  → CorrespondenceOfferBranchLeaf
  → CorrespondenceOfferLeaf
  → CorrespondenceAssembly
```

`CorrespondenceChoice.lean` also imports `CorrespondenceParallel.lean`; the
diagram records dependency order, not a claim that every file has exactly one
import.

| Concern | Principal modules |
|---|---|
| State/residual representation, atomic cases, public correspondence record | `CorrespondenceCore` |
| Parallel local-environment reconstruction and synchronization | `CorrespondenceVisibility`, `CorrespondenceParallel` |
| Exclusive/conjunctive offer graph and step correctness | `CorrespondenceOffers`, `CorrespondenceXOfferLeaf`, `CorrespondenceOfferBranchLeaf`, `CorrespondenceOfferLeaf` |
| Choice and fair choice | `CorrespondenceChoice`, `CorrespondenceFragmentStepLeaves` |
| Sequence graph, future, step, completion, execution view | `CorrespondenceSequenceGraph`, `CorrespondenceSequence`, `CorrespondenceSequenceExecutionLeaves`, `CorrespondenceSequenceAssembly` |
| Recursion header, marker reachability, completion closure, scoped body step, execution view | `CorrespondenceRecursionHeader`, `CorrespondenceRegularityCore`, `CorrespondenceMarkerSkipping`, `CorrespondenceCompletingRepresented`, `CorrespondenceRecursionClosure*`, `CorrespondenceMarkerReachability`, `CorrespondenceRecursionLeaf` |
| Structural bundle and public step assembly | `CorrespondenceBundle`, `CorrespondenceAssembly` |

## Recursion proof in one page

The recursion constructor is the only branch where all four bundle fields must
be solved simultaneously.

1. The body is compiled open under `name :: bound`; it is not incorrectly
   treated as a closed type.
2. `compilationMarkerReachable_iff` relates raw-graph marker reachability to
   `markerReachableSubst`. The execution analogue
   `compilationSequenceExecutionMarkerReachable_iff` proves the same fact for
   the sequence-execution view.
3. `recursionBodyFutureCorrect_of_bundle` combines marker reachability with
   `futureOffersSubst_eq_union_marker`: if the marker is reachable, the
   recursion-entry menu is unioned into the residual menu.
4. `recursionBodyScopedStep_marker` handles the bare recursive call and its
   installed silent backedge. `recursionBodyScopedStep_nonMarker` transports
   all other steps through capture-safe substitution and matches the exact
   compiler future policy.
5. `compilationCompletingCorrect_recursion_regular_leaf` identifies the
   constructor's backward non-clock completion closure with substituted
   semantic completion.
6. The execution proof compares the installed execution graph with a shadow
   recursion graph built over a marker-stopped execution body. Same edges give
   the same `computeFuture`; marker/no-marker fixed-point equations then match
   the syntax equation. Completion reachability is propagated backward with
   `compiledFragmentNonClockPredecessor_eval`.
7. `compilationProofBundle_recursion_bounded_leaf` packages the four results.

The successful non-marker step proof uses an explicit semantic future policy:
either a future is explicit, or it is the target menu minus the exact semantic
removed set. This avoids the invalid shortcut that attempted to derive a
general disjointness fact from `SameCycleMessageLinear`; the current
`SuffixMessageIds` definition is too weak for that shortcut.

## Verification

From the repository root:

```bash
lake build Anvilpp
git diff --check
```

The completed type-correspondence modules, including
`CorrespondenceRecursionLeaf.lean`, contain no remaining `sorry`. A successful
whole-project build still reports admitted declarations elsewhere, most
notably `process_automaton_correspondence`; consult the root README for the
repository-wide status. `#print axioms Pact.type_automaton_correspondence`
reports `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
