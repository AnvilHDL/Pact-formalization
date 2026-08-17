# Type/Automaton Correspondence Theorem Reference

This document presents the Pact type/compiled-automaton proof from its public
result down to its constructor and graph-theoretic leaves. It is a theorem map,
not a chronological log: hypotheses that are repeated throughout the Lean
statements are summarized in English, while the linked source remains the
authoritative statement.

The list is intentionally selective about tiny inversion and finite-set
helpers, but extensive about every declaration that carries semantic content
or connects two proof layers. Names marked **private** are implementation
leaves in their source module; they are documented because they explain the
finished proof even though downstream Lean files cannot invoke them directly.

## 1. Main theorem: exact statement

Source: [`PactSafety.lean`](../PactSafety.lean) and
[`CorrespondenceCore.lean`](Correspondence/CorrespondenceCore.lean).

The result proved by this development is Lemma 4.5:

```lean
/-- Lemma 4.5: operational types and their finite semantic automata correspond. -/
theorem type_automaton_correspondence
    {signature : TypeAlphabet} {processType : PactType}
    (hAdmissible : AdmissibleType signature processType) :
    Nonempty
      (TypeAutomatonCorrespondence processType
        (compileType signature processType))
```

Its assumption expands to:

```lean
def ClosedGuardedRegular (processType : PactType) : Prop :=
  PactType.AllVariablesBound [] processType ∧
    PactType.BinderHygienic [] processType ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.InterfaceScoped processType

def AdmissibleType
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  signature.WellFormed ∧
    signature.Supports processType ∧
    ClosedGuardedRegular processType
```

In English: for every closed, capture-safe, clock-guarded, tail-recursive,
same-cycle message-linear, interface-scoped type supported by a well-formed
finite alphabet, the operational type transition system corresponds
step-for-step to the finite automaton produced by `compileType`.

### 1.1 What “correspond” means

The theorem returns a witness of the following structure:

```lean
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel}
      {offers : TypeOfferSummary},
      relation residual state →
      TypeAutomatonSymbol.mk env label offers ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')
```

Thus the proof must construct a relation `R` and establish three facts:

1. `R processType automaton.initial`: the compiled entry state represents the
   original type;
2. `automaton.initial ∈ automaton.states`: the entry is a genuine state of the
   finite automaton;
3. for every related residual/state pair and every symbol in the fixed public
   alphabet, a decorated semantic transition exists **if and only if** a
   compiled edge with the same environment, label, current offers, and future
   offers reaches another related pair.

The third field contains both simulation directions. It is therefore stronger
than merely saying that every semantic step can be compiled: every public
compiled edge must also reconstruct a semantic step.

### 1.2 The witness used by the proof

The theorem instantiates the structure as follows:

```lean
relation    := fun residual state =>
  TypeCompilationRelation processType state residual
initial     := compileType_initial_relation signature processType
initial_mem := compileType_initial_mem signature processType
stepIff     := compilationStepCorrect_of_closedGuardedRegular ...
```

Here `TypeCompilationRelation original state residual` is the central
representation invariant: `state` is a compiler state generated from
`original`, and it currently denotes the operational residual `residual`.

### 1.3 Proof breakdown

The top-level Lean proof separates five impossible or direct base cases from
the structural argument:

1. `.message msg dir`, `.skip`, `.tock`, and `.progress pid` use their direct
   complete correspondence witnesses;
2. `.var name` is impossible because `AdmissibleType` requires
   `AllVariablesBound []`;
3. every remaining constructor obtains public step correctness from the
   structurally assembled four-field proof bundle.

For the structural branch, the dependency chain is:

```text
AdmissibleType signature processType
  │
  ├─ signature.WellFormed
  ├─ signature.Supports processType
  └─ ClosedGuardedRegular processType
       │
       ▼
compilationProofBundle_of_closedGuardedRegular
       │
       ├─ future
       ├─ completing
       ├─ scopedStep
       └─ execution
       │
       ▼
compilationStepCorrect_of_scopedFragmentStepCorrect
       │
       ▼
CompilationStepCorrect signature processType
       │
       ▼
TypeAutomatonCorrespondence.stepIff
```

Only `scopedStep` is exported directly into the final `stepIff`. The other
three bundle fields are nevertheless necessary to construct `scopedStep`
compositionally: sequence needs child execution information, recursion needs
future and completion fixed points, and enclosing constructors need related
targets with correct future decorations.

### 1.4 Top-level declarations

| Declaration | English statement | Proof role |
|---|---|---|
| `ClosedGuardedRegular` | A type has no free variables, uses fresh recursion binders, guards recursive calls by `tock`, uses recursion only in tail-compatible positions, is same-cycle message-linear, and scopes nested parallel interfaces lexically. | Collects the syntax restrictions under which the canonical finite compiler is sound and complete. |
| `AdmissibleType` | The alphabet is well formed, supports the type, and the type is `ClosedGuardedRegular`. | Public hypothesis of Lemma 4.5. |
| `TypeAutomatonCorrespondence` | There is a relation between semantic residual types and automaton states; it relates the two initial objects, the initial state belongs to the automaton, and a decorated semantic step exists iff a matching automaton edge reaches a related state. | Formal statement of step-for-step type bisimulation. |
| `type_automaton_correspondence` | Every admissible type is related to its canonical compiled automaton by a `TypeAutomatonCorrespondence`. | Lemma 4.5; statement complete, proof `sorry` pending the `Correspondence/*` redevelopment against the `computeFutureOf` automaton construction. |
| `ProcessAutomatonCorrespondence` | A related process step can be simulated by an edge of the type automaton, preserving a process/state relation. | Record used to state the separate process simulation. |
| `process_automaton_correspondence` | A conforming process should simulate into the automaton compiled from its admissible type. | Lemma 4.6; `sorry`, not part of the type proof. |

## 2. Top-down assembly

Source: [`CorrespondenceAssembly.lean`](Correspondence/CorrespondenceAssembly.lean),
[`CorrespondenceBundle.lean`](Correspondence/CorrespondenceBundle.lean), and
[`CorrespondenceCore.lean`](Correspondence/CorrespondenceCore.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `CompilationFutureCorrect` | At every compiled state representing residual `r`, resolving pending future references with `computeFuture` gives exactly `typeFutureOffers r`. | Ordinary same-cycle menu invariant. |
| `CompilationCompletingCorrect` | A represented compiled state is marked completing exactly when its residual can complete before the next `tock`. | Completion metadata invariant. |
| `CompilationFragmentStepCorrect` | In a compiler-local environment, a decorated semantic step exists iff the unresolved constructor fragment has a matching resolved edge to a related state. | Raw compositional step invariant. |
| `CompilationScopedFragmentStepCorrect` | The raw step equivalence holds when the environment additionally avoids every parallel interface nested under the current syntax node. | Induction-facing step invariant that survives nested parallel composition. |
| `CompilationSequenceExecutionCorrect` | In the non-clock execution view, future resolution equals the syntax menu; moreover an execution-reachable skipping/completing state exists exactly when the residual can complete this cycle. | Extra invariant required when a fragment becomes the left operand of sequence. |
| `CompilationProofBundle` | Packages `future`, `completing`, `scopedStep`, and `execution` correctness for one type. | Mutually supporting induction result. |
| `compilationScopedFragmentStepCorrect_of_fragmentStepCorrect` | Raw fragment correctness implies the scoped form by ignoring the additional avoidance premise. | Adapter for leaves that need no parallel scoping. |
| `compilationStepCorrect_of_scopedFragmentStepCorrect` | A scoped raw-fragment proof exports to the public `compileType` edge relation after applying the fixed public alphabet filter. | Uniform raw-to-public bridge. |
| `compilationProofBundle_of_boundedRegular` | For a type whose free recursion variables are among an ambient `bound` list and whose occurrences/regularity facts are available, construct the complete proof bundle by well-founded recursion on syntax size. | Main constructor induction. |
| `compilationProofBundle_of_closedGuardedRegular` | Specialize the bounded assembly to `bound = []`; the ambient tail-occurrence obligation is then vacuous. | Closed top-level bundle. |
| `compilationStepCorrect_of_closedGuardedRegular` | A well-formed alphabet and closed guarded regular type satisfy the public one-step equivalence. | Supplies `stepIff` to Lemma 4.5. |

The proof dependency is:

```text
type_automaton_correspondence
  └─ compilationStepCorrect_of_closedGuardedRegular
      └─ compilationProofBundle_of_closedGuardedRegular
          └─ compilationProofBundle_of_boundedRegular
              ├─ atomic bundle fields
              ├─ choice/fair-choice bundle fields
              ├─ sequence bundle fields
              ├─ parallel bundle fields
              ├─ xoffer/offer bundle leaves
              └─ compilationProofBundle_recursion_bounded_leaf
```

## 3. State/residual representation and compiler well-formedness

Source: [`CorrespondenceCore.lean`](Correspondence/CorrespondenceCore.lean)
and [`CompileType.lean`](Automata/CompileType.lean).

### 3.1 Representation relation

`TypeCompilationRelation original state residual` says that `state` in the
fragment compiled from `original` denotes the current operational residual.
Its constructors are the canonical representation cases:

| Constructor | English statement |
|---|---|
| `skip` | The root of compiled `skip` represents `skip`. |
| `message_source`, `message_final` | A message fragment's root represents the message action and its final state represents `skip`. |
| `cycle_source`, `cycle_final` | A `tock` fragment's root represents `tock` and its final state represents `skip`. |
| `progress_source`, `progress_final` | A progress fragment's root represents the progress action and its final state represents `skip`. |
| `variable` | A free-variable marker root represents that variable. |
| `recur_source` | The fresh recursion root represents the whole binder. |
| `recur_body` | A tagged body state represents the body's residual after capture-safe substitution of the enclosing binder. |
| `choice_source`, `choice_left`, `choice_right` | The root represents the choice; tagged child states represent the selected child's residual. |
| `fair_source`, `fair_left`, `fair_right` | The fair-choice root and tagged child states have the analogous interpretation. |
| `sequence_left` | A tagged left state representing `r` denotes `r ; right`. |
| `sequence_right` | A tagged right state denotes the right residual directly. |
| `parallel` | A product state denotes the parallel composition of the two represented residuals. |
| `xoffer_source`, `xoffer_else`, `xoffer_branch` | Exclusive-offer root, else child, and indexed branch children represent the corresponding semantic residuals. |
| `offer_source`, `offer_branches`, `offer_else` | Conjunctive-offer root, selected-conjunction child, and else child represent the corresponding semantic residuals. |

### 3.2 Representation facts

| Declaration | English statement | Proof role |
|---|---|---|
| `TypeCompilationRelation.residual_unique` | A fixed state in a fixed compiled syntax represents at most one semantic residual. | Converts existence witnesses back to the residual already in the bisimulation hypothesis. |
| `compileTypeFuel_initial_relation` | With sufficient fuel, the fragment's distinguished initial state represents the input syntax. | Fuel-parametric initialization. |
| `compileType_initial_relation` | The public compiler's initial state represents the original type. | Final witness initialization. |
| `compileTypeFuel_initial_mem` | With sufficient fuel, the fragment initial state belongs to its state set. | Graph well-formedness. |
| `compileType_initial_mem` | The public compiled initial state belongs to the final automaton. | `initial_mem` field of the final witness. |
| `compileTypeFuel_futureTargetsInStates` | Every symbolic future reference produced by sufficient compilation points to a state inside the fragment. | Makes future reachability closed and finite. |
| `compileTypeFuel_referencesClosed` | The pending automaton underlying a sufficient fragment is closed under its future references. | Hypothesis for fixed-point and reachability theorems. |
| `CompilationStateCorrect` | Every state related to a residual belongs to the compiled fragment. | Abstract state-membership invariant. |
| `compilationStateCorrect_of_compilation` | `TypeCompilationRelation` implies `CompilationStateCorrect` for the canonical fuel. | Used throughout child and recursion arguments. |
| `CompilationResolvedEdgeTargetsRelated` | Every visible resolved edge from a related source has some related target residual. | Separates target representation from full semantic step correctness. |
| `CompilationPendingEdgesVisible` | Every pending compiler edge other than a construction-only future edge has a visible label; recursion variable markers must have been consumed. | Justifies public edge export. |

### 3.3 Fuel and public edges

| Declaration | English statement |
|---|---|
| `TypeCompilationFuelSufficient` | The chosen natural-number fuel is large enough to compile a syntax tree and every constructor-generated child. |
| `typeCompilationFuel_sufficient` | The structural `typeCompilationFuel` function always supplies sufficient fuel. |
| `typeCompilationFuel_positive` | Canonical compilation fuel is positive. |
| `compileTypeFuel_eq_of_sufficient` | Any two sufficient fuel values produce the same fragment. |
| `compileType` | Finish the canonical sufficient fragment into the finite public type automaton. |
| `AutomatonFragment.HasResolvedEdge` | A pending fragment edge is visible and its future specification has been resolved into a concrete offer summary. |
| `compileType_hasEdge_iff_hasResolvedEdge` | A public automaton edge is exactly a resolved fragment edge whose symbol survives the public alphabet filter. |
| `compileType_edge_source_mem`, `compileType_edge_target_mem` | Every public edge starts and ends in the public state set. |

## 4. Capture safety and regularity transport

Sources: [`PactTypeSyntax.lean`](Syntax/PactTypeSyntax.lean),
[`PactTypeSubstitutionLemmas.lean`](Syntax/PactTypeSubstitutionLemmas.lean),
[`PactTypeCompletionEval.lean`](Syntax/PactTypeCompletionEval.lean), and
[`CorrespondenceRegularityCore.lean`](Correspondence/CorrespondenceRegularityCore.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `PactType.AllVariablesBound` | Every variable occurrence is included in the ambient active-binder list. | Tracks deliberately open recursion bodies. |
| `PactType.BinderHygienic` | Every nested binder is fresh for the active binder context, recursively. | Global no-capture condition. |
| `PactType.BinderFreshFor` | No binder in a type reuses any name in a fixed forbidden list. | Exact local condition needed by substitution commutation. |
| `PactType.binderHygienic_mono` | Removing names from the ambient context preserves binder hygiene. | Obtains closed-context hygiene from stronger bounded hygiene. |
| `PactType.allVariablesBound_mono` | Enlarging the active-binder context preserves the all-bound property. | Context weakening. |
| `PactType.binderFreshFor_mono` | Shrinking the forbidden-name list preserves binder freshness. | Localizes freshness assumptions. |
| `PactType.binderHygienic_binderFreshFor` | Binder hygiene implies binder freshness for the same list. | Connects the public regularity predicate to substitution lemmas. |
| `PactType.replaceVar_comm` | Substitutions for distinct variables commute if the outer replacement is closed for the inner name and the term cannot rebind the outer name. | Capture-safe nested-recursion step transport. |
| `PactType.replaceVar_recur_injective_of_binderFreshFor` | Under binder freshness, unfolding substitution by a recursion binder is injective. | Recovers pre-substitution residuals. |
| `compilationRelation_allVariablesBound` | A represented residual inherits the ambient all-bound invariant from the compiled original. | Threads binding context to leaves. |
| `compilationRelation_binderFreshFor` | A represented residual inherits binder freshness from hygienic compiled syntax. | Supplies `replaceVar_comm` in the non-marker recursion leaf. |
| `compilationRelation_tailOccurrences_false` | If the original has no relevant tail occurrence of a name, neither does any represented residual. | Prevents spurious markers/substitution effects. |
| `compilationRelation_tailOccurrences_true` | Under tail-recursive compilation, represented residuals preserve permitted tail occurrence of the active binder. | Enables recursion future substitution. |
| `compileTypeFuel_variableEdge_source_var` | A matching compiler variable edge originates at a state representing the corresponding variable, under tail occurrence. | Identifies recursion backedge sources. |
| `compileTypeFuel_markerEdgesInert` | Matching variable-marker edges carry no current offers and have inert target behavior before installation. | Marker-stopped and recursion fixed-point proofs. |

## 5. Syntax-side completion and future equations

Sources: [`PactTypeFutureOffers.lean`](Syntax/PactTypeFutureOffers.lean),
[`PactTypeSubstitutionLemmas.lean`](Syntax/PactTypeSubstitutionLemmas.lean), and
[`PactTypeCompletionEval.lean`](Syntax/PactTypeCompletionEval.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `typeFutureOffers_sequence` | The future menu of `left ; right` is the left menu, union the right menu when the left can complete before `tock`. | Matches sequence graph propagation. |
| `typeFutureOffers_choice`, `typeFutureOffers_fairChoice` | Choice menus are the appropriate union of child menus. | Choice future leaves. |
| `typeFutureOffers_parallel` | A parallel menu is the interface-hidden union of component menus. | Matches optimistic product observations. |
| `typeFutureOffers_xoffer`, `typeFutureOffers_offer` | Offer menus combine the root action needs with the relevant branch/else future menus. | Offer future leaves. |
| `typeFutureOffers_recur` | The future menu at a recursion header is the menu of the unfolded body. | Header future equality. |
| `PactType.replaceVar_typeFutureOffers` | Describes future offers after a general substitution. | Core syntax substitution bridge. |
| `PactType.futureOffersSubst_eq_union_marker` | Under tail occurrence, substituting a recursion binder leaves the residual menu unchanged unless the binder marker is reachable; in that case it unions the body-entry menu. | Syntax half of recursion future correctness. |
| `PactType.markerReachableSubst_replaceVar` | Marker reachability through substitution obeys the corresponding Boolean substitution equation. | Nested marker induction. |
| `PactType.replaceVar_typeFutureOffers_recur` | Rewrites the future menu of a residual after replacing a variable by its recursion binder. | Normal form used in both recursion future proofs. |
| `PactType.completionEval_eq_canCompleteBeforeTock_of_all_false` | Evaluating all free variables as non-completing equals ordinary `CanCompleteBeforeTock`. | Converts the valuation-parametric backward-closure invariant to the public predicate. |
| `PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst` | Evaluating one variable with a supplied Boolean equals the corresponding completion-after-substitution computation. | Recursion completion bridge. |
| `PactType.replaceVar_canCompleteBeforeTock` | Completion of a substituted residual is characterized by the syntactic substitution completion function. | Final recursion completion rewrite. |
| `PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false` | If a name has no tail occurrence, changing its completion valuation has no effect. | Eliminates irrelevant ambient binders. |

## 6. Fixed-point graph infrastructure

Sources: [`PendingAutomatonFuture.lean`](Automata/PendingAutomatonFuture.lean),
[`MarkerReachability.lean`](Automata/MarkerReachability.lean), and
[`CompletingBackClosure.lean`](Automata/CompletingBackClosure.lean).

### 6.1 Future resolution

| Declaration | English statement |
|---|---|
| `computeFuture` | Starting at a state, follow same-cycle symbolic future references and union the current offers observed along the finite closure. |
| `computeFuture_subset_of_mem_futureReachable` | Every offer in `computeFuture q` is witnessed at some state in the future-reachable closure of `q`. |
| `computeFuture_unfold` | Future computation satisfies its one-step fixed-point unfolding equation. |
| `computeFuture_eq_of_embedding` | An embedding that preserves the reachable future graph preserves `computeFuture`. |
| `computeFuture_eq_of_same_edges` | Two reference-closed pending automata with the same edges have the same `computeFuture` at states contained in both. |
| `computeFuture_eq_offersAt_of_all_explicit` | If every future specification is explicit, `computeFuture` reduces to the offers directly available at the state. |

### 6.2 Marker reachability

| Declaration | English statement |
|---|---|
| `MarkerSource` | A state has an outgoing temporary variable edge for the selected recursion name. |
| `MarkerEdgesInert` | Selected variable-marker edges contribute no ordinary same-cycle offers. |
| `markerStoppedFragment` | Replace selected marker references by stopped/sink behavior while retaining the surrounding graph. |
| `MarkerReachable` | The same-cycle future-reference closure from a state reaches a selected marker source. |
| `markerStoppedFragment_markerReachable_self` | For a closed graph, stopping selected markers preserves whether the original state reaches such a marker. |
| `markerStoppedFragment_computeFuture_of_target_sinks` | If selected marker targets are sinks and marker edges carry no offers, stopping them preserves `computeFuture`. |
| `markerReachable_iff_of_same_edges` | Marker reachability depends only on the relevant graph edges. |
| `markerReachable_root_of_entries` | A constructor root reaches a marker exactly when one of its referenced entry states does. |

### 6.3 Backward completion closure

| Declaration | English statement |
|---|---|
| `completingBackClosure` | Starting with a seed set, repeatedly add sources of non-clock edges whose targets are already included, for a finite number of iterations bounded by graph size. |
| `completingBackClosure_superset_seed` | Every seed state belongs to the closure. |
| `completingBackClosure_mem_of_nonClockEdge` | A non-clock predecessor of a closure member is also in the closure. |
| `completingBackClosure_subset_of_predecessor_closed` | Any predecessor-closed superset of the seed contains the entire computed closure. |
| `completingBackClosure_mono` | Enlarging the seed enlarges the closure. |
| `completingBackClosure_taggedFragment_image` | Backward closure commutes with tagging a child fragment. |
| `completingBackClosure_eq_of_edges_agree` | Graphs whose relevant non-clock edges agree have the same backward closure. |

## 7. Atomic constructor leaves

Source: [`CorrespondenceCore.lean`](Correspondence/CorrespondenceCore.lean),
[`CorrespondenceFragmentStepLeaves.lean`](Correspondence/CorrespondenceFragmentStepLeaves.lean),
and [`CorrespondenceSequenceExecutionLeaves.lean`](Correspondence/CorrespondenceSequenceExecutionLeaves.lean).

| Declaration family | English statement |
|---|---|
| `compilationFutureCorrect_skip/message/tock/progress/var` | Each atomic fragment's computed future menu equals the menu of its represented source/final residual. |
| `compilationCompletingCorrect_skip/message/tock/progress/var` | Each atomic fragment's completing metadata exactly matches semantic completion. |
| `compilationFragmentStepCorrect_skip_leaf` | The raw `skip` fragment has exactly the silent completion step allowed by the semantics. |
| `compilationFragmentStepCorrect_message_leaf` | Message fire, wait, and completed-idle edges are exactly the message semantic cases. |
| `compilationFragmentStepCorrect_tock_leaf` | Clock action/wait/final edges are exactly the `tock` semantic cases. |
| `compilationFragmentStepCorrect_progress_leaf` | Progress action and final edges are exactly the progress semantic cases. |
| `compilationScopedFragmentStepCorrect_var` | A bare variable has neither a semantic step nor a visible resolved edge. |
| `compilationSequenceExecutionCorrect_skip/progress/var/tock/message` | Every atomic fragment also has the correct non-clock execution menu and completion reachability. |
| `compileType_skip_correspondence` | The public compiled `skip` automaton directly satisfies the full correspondence record. |
| `compileType_message_correspondence` | The public compiled message automaton directly satisfies the full correspondence record. |
| `compileType_tock_correspondence` | The public compiled clock automaton directly satisfies the full correspondence record. |
| `compileType_progress_correspondence` | The public compiled progress automaton directly satisfies the full correspondence record. |

## 8. Choice and fair choice

Source: [`CorrespondenceChoice.lean`](Correspondence/CorrespondenceChoice.lean),
[`CorrespondenceFragmentStepLeaves.lean`](Correspondence/CorrespondenceFragmentStepLeaves.lean),
and [`CorrespondenceCompleting.lean`](Correspondence/CorrespondenceCompleting.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `ChoiceFutureCorrect`, `FairChoiceFutureCorrect` | Constructor-specific interfaces recording the expected root/child future equations. | Intermediate graph contracts. |
| `choiceFutureCorrect_of_compilation`, `fairChoiceFutureCorrect_of_compilation` | Child future correctness implies the constructor-specific graph future contract. | Lifts child menus through tagging. |
| `compilationFutureCorrect_choice`, `compilationFutureCorrect_fairChoice` | Every represented choice/fair-choice state has the correct syntax menu. | Bundle `future` fields. |
| `compileType_choice_*_child_edge_iff` | A tagged child edge exists exactly when the corresponding child fragment edge exists. | Edge transport. |
| `compileType_choice_*_selection_edge` | The root has the expected silent selection edge into each child. | Root forward direction. |
| `compileType_choice_*_selection_step_iff` | A root selection semantic step exists exactly when the compiled selection edge exists. | Root step correspondence. |
| `compilationFragmentStepCorrect_choice_leaf`, `compilationFragmentStepCorrect_fairChoice_leaf` | Raw fragment step equivalence for all root and tagged-child cases. | Bundle `scopedStep` fields. |
| `compilationCompletingCorrect_choice`, `compilationCompletingCorrect_fairChoice` | A choice state is completing exactly when its represented residual can complete. | Bundle `completing` fields. |
| `compilationSequenceExecutionCorrect_choice`, `compilationSequenceExecutionCorrect_fairChoice` | Execution-view future and completion reachability are preserved through both tagged alternatives and the root. | Bundle `execution` fields. |

## 9. Sequence

Sources: [`CorrespondenceSequenceGraph.lean`](Correspondence/CorrespondenceSequenceGraph.lean),
[`CorrespondenceSequence.lean`](Correspondence/CorrespondenceSequence.lean), and
[`CorrespondenceSequenceAssembly.lean`](Correspondence/CorrespondenceSequenceAssembly.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `sequenceExecutionAutomaton` | View a fragment as a graph whose references follow every non-clock execution target, including construction-only future observations. | Captures information needed by an enclosing sequence. |
| `sequenceExecutionAutomaton_referencesClosed` | If raw future targets stay in the fragment, execution references also stay in the execution state set. | Makes execution closure well formed. |
| `compileTypeFuel_sequence_left_child_edge_iff` | A tagged left sequence edge is exactly a decorated edge of the left child. | Left edge classifier. |
| `compileTypeFuel_sequence_right_child_edge_iff` | A tagged right sequence edge is exactly a decorated edge of the right child. | Right edge classifier. |
| `compileTypeFuel_sequence_bridge_edge_iff` | A bridge edge from a completing left state to the right entry exists exactly under the builder's bridge conditions. | Handoff classifier. |
| `compileTypeFuel_sequence_left_edge_cases`, `compileTypeFuel_sequence_right_edge_cases` | Every compiled sequence edge belongs to the expected left/right/bridge family. | Reverse step direction. |
| `compilationCompletingCorrect_sequence` | A represented sequence state is marked completing exactly when the semantic sequence can complete this cycle. | Bundle `completing`. |
| `buildSequenceAutomaton_computeFuture_left_formula` | The future of a left state is its left future plus the right entry future when an execution completion witness exists. | Graph half of syntax sequence future. |
| `buildSequenceAutomaton_computeFuture_right` | The future of a tagged right state is the child's future. | Right future transport. |
| `compilationFutureCorrect_sequence` | Child bundles plus the left execution invariant imply future correctness of the whole sequence. | Bundle `future`. |
| `compilationScopedFragmentStepCorrect_sequence_leaf` | Child bundles and sequence future correctness imply interface-scoped raw step correctness. | Bundle `scopedStep`. |
| `compilationSequenceExecutionCorrect_sequence` | The execution view of a sequence has the right menu and completion reachability. | Bundle `execution`. |
| `compilationResolvedEdgeTargetsRelated_sequence` | Every visible resolved sequence edge reaches a represented target. | Used by parent constructors and recursion. |

## 10. Parallel composition

Sources: [`CorrespondenceParallel.lean`](Correspondence/CorrespondenceParallel.lean),
[`CorrespondenceCompleting.lean`](Correspondence/CorrespondenceCompleting.lean), and
[`CorrespondenceSequenceAssembly.lean`](Correspondence/CorrespondenceSequenceAssembly.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `TypeEnvironment.AvoidsInterface` | Neither immediate nor future environment offers mention a message hidden by the selected interface. | Lexical scoping premise. |
| `LocalTypeEnvironment.avoidsInterface_of_disjoint` | Passing into a sibling-local environment preserves avoidance of a disjoint descendant interface. | Nested parallel induction. |
| `localTypeEnvironments_to_syncAutomatonEdges_local` | Compatible semantic local environments reconstruct the synchronized child edges used by the product builder. | Forward synchronization. |
| `syncAutomatonEdgeWitnesses_to_localTypeEnvironments` | Synchronized compiled edge witnesses reconstruct semantic local environments. | Reverse synchronization. |
| `parallel_semantic_step_to_resolved_edge` | Every semantic parallel step yields a matching resolved product edge. | Forward step direction; needs re-deriving against `buildParallelAutomaton`'s native `computeFutureOf`-resolved product edges. |
| `parallel_resolved_edge_to_semantic_step` | Every resolved product edge yields the corresponding semantic parallel step. | Reverse step direction; same redevelopment gap. |
| `compilationResolvedEdgeTargetsRelated_parallel` | A resolved product edge from related components reaches a product state representing the semantic targets. | Target preservation; same gap. |
| `compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible` | Scoped child step correctness plus target visibility gives the semantic offer witness needed by synchronization. | Bridge from child bundles to product reconstruction; same gap. |
| `compilationFutureCorrect_parallel` | Product-state `computeFuture` is the interface-hidden union of the represented component menus. | Bundle `future`; needs re-deriving against `computeFutureOf`'s native `.pair`-state case, which replaced the deleted synthetic-future-edge mechanism this proof used. |
| `compilationCompletingCorrect_parallel` | Product completing metadata agrees with semantic parallel completion. | Bundle `completing`. |
| `compilationFragmentStepCorrect_parallel_leaf` | Scoped semantic parallel steps and resolved product edges are equivalent. | Bundle `scopedStep`. |
| `compilationSequenceExecutionCorrect_parallel_regular_leaf` | The product execution view has the right future menu and completion reachability for closed components. | Bundle `execution`. |
| `compileType_parallel_edge_hides_immediate_interface` | Every public parallel edge hides actions belonging to the synchronization interface from its immediate offers. | Paper boundary/internal separation; needs re-deriving against `buildParallelAutomaton`'s single-arm edge union (the old two-arm transition/future-edge split it was proved against is gone). |

## 11. Exclusive and conjunctive offers

Sources: [`CorrespondenceOffers.lean`](Correspondence/CorrespondenceOffers.lean),
[`CorrespondenceXOfferLeaf.lean`](Correspondence/CorrespondenceXOfferLeaf.lean),
[`CorrespondenceOfferBranchLeaf.lean`](Correspondence/CorrespondenceOfferBranchLeaf.lean),
and [`CorrespondenceOfferLeaf.lean`](Correspondence/CorrespondenceOfferLeaf.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `parallelTypeBranches_interfaceScoped` | The parallel combination of branch types has the expected lexical interface-scoping property. | Regularity transport. |
| `parallelTypeBranchesSelecting_interfaceScoped` | The selected conjunctive branch combination preserves interface scoping. | Selected-branch bundle premise. |
| `exclusiveOfferEntryStates`, `conjunctiveOfferEntryStates`, `selectedConjunctiveOfferEntryStates` | Identify the tagged entry states referenced by each offer constructor root. | Root future/marker graph descriptions. |
| `buildExclusiveOfferAutomaton_outgoing_else`, `buildExclusiveOfferAutomaton_outgoing_branch` | Classify outgoing else and selected-branch edges of an exclusive offer. | Exclusive edge inversion. |
| `buildConjunctiveOfferAutomaton_outgoing_child` | Classify outgoing child edges of the all-branches conjunctive graph. | Conjunctive edge inversion. |
| `buildSelectedConjunctiveOfferAutomaton_outgoing_else`, `buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction` | Classify the else and selected-conjunction outgoing edges. | Public offer edge inversion. |
| `compilationFutureCorrect_xoffer_of_children` | Correct future menus for else/branch children imply future correctness of `xoffer`. | Exclusive future constructor theorem. |
| `compilationFutureCorrect_offer_of_children` | Correct child menus imply future correctness of conjunctive `offer`. | Conjunctive future theorem. |
| `compilationFragmentStepCorrect_xoffer`, `compilationScopedFragmentStepCorrect_xoffer` | Exclusive-offer semantic cases match the raw graph, with the scoped version usable under parallel composition. | Exclusive step theorem. |
| `compilationScopedFragmentStepCorrect_offer` | Conjunctive offer enabled/else/wait semantic cases match raw graph edges. | Conjunctive step theorem. |
| `compilationResolvedEdgeTargetsRelated_xoffer`, `compilationResolvedEdgeTargetsRelated_offer` | Every resolved offer edge reaches a state represented by the selected semantic residual. | Parent/recursion target preservation. |
| `compilationCompletingCorrect_xoffer`, `compilationCompletingCorrect_offer` | Offer completing metadata agrees with the syntax completion predicate. | Bundle `completing`. |
| `compilationProofBundle_parallelTypeBranchesSelecting_leaf` | Given bundles for the selected branch components, build a bundle for the semantic parallel combination selected by a conjunctive offer. | Internal conjunctive branch assembly. |
| `compilationProofBundle_xoffer_leaf` | Regular exclusive-offer syntax plus child bundles yields the complete four-field bundle. | Constructor bundle leaf. |
| `compilationProofBundle_offer_leaf` | Regular conjunctive-offer syntax plus child bundles yields the complete four-field bundle. | Constructor bundle leaf. |
| `conjunctiveOffer_execution_completion_regression` | Records a concrete execution/completion behavior that any offer execution proof must preserve. | Regression theorem. |
| `conjunctiveOffer_not_sequenceExecutionCorrect` | Records why a tempting stronger, context-free execution claim for the raw conjunctive helper is false. | Guards the chosen selected-conjunction formulation. |

## 12. Recursion header and installed graph

Sources: [`CorrespondenceRecursionHeader.lean`](Correspondence/CorrespondenceRecursionHeader.lean)
and [`BuildRecursionAutomaton.lean`](Automata/BuildRecursionAutomaton.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `RecursionHeaderFutureCorrect` | The future menu at the tagged body entry in the installed recursion graph equals the syntax menu of the unfolded body. | Decoration required by the header edge. |
| `compileType_recursion_header_edge` | The compiled recursion root has the silent edge into the tagged body entry with exactly the unfolded body's future menu. | Header forward edge; needs re-deriving against `compileType`'s native `resolvedAutomatonEdgesNative` resolution. |
| `compileType_recursion_header_step_iff` | The semantic unfolding step at the recursion root exists exactly when the compiled header edge exists, and its target is related. | Header bisimulation. |
| `buildRecursionAutomaton_root_hasResolvedEdge_iff` | A resolved edge from the fresh recursion root is exactly the silent header edge to the tagged body initial state. | Header edge classifier; statement's RHS still describes the old local-closure `computeFuture` and needs reconciling against the global `computeFutureOf` fixed point. |
| `buildRecursionAutomaton_variable_marker_hasResolvedEdge` | A matching body variable marker becomes a silent installed backedge to the tagged body entry. | Recursive-call edge constructor; same reconciling gap. |
| `buildRecursionAutomaton_body_hasResolvedEdge_iff` | Every resolved edge from a tagged body state is either an installed matching-variable backedge or a lifted non-matching body edge. | Central recursion edge inversion; same reconciling gap. |
| `RecursionBodyFutureCorrect` | At every body state/residual, future resolution in the installed graph at the tagged state equals the menu of the residual after substituting the recursion binder. | Recursion future contract. |
| `buildRecursionAutomaton_computeFuture_root` | The fresh recursion root and tagged body entry compute the same future menu. | Lifts body future correctness to the header. |
| `compilationFutureCorrect_recursion` | Guarded occurrences plus `RecursionBodyFutureCorrect` imply ordinary future correctness of the whole recursion fragment. | Bundle `future`. |
| `RecursionBodyStepCorrect` | Semantic steps of substituted body residuals correspond to installed edges from tagged body states. | Original unscoped body-step contract. |
| `decoratedTypeTransition_recur_iff` | A recursion binder's decorated transition is exactly its silent, empty-current unfolding step with the target future menu. | Semantic header inversion. |
| `compilationFragmentStepCorrect_recursion_root` | The raw recursion header step is correct. | Root half of recursion raw step. |
| `buildRecursionAutomaton_completing_eq` | The installed graph's completing set is the tagged non-clock backward closure of the body seed, plus the root precisely when the body entry completes. | Graph definition exposed as a usable equation. |
| `computeFuture_buildRecursionAutomaton_child_of_no_marker` | If a body state cannot reach the selected marker, installing the backedge does not add the entry menu. | No-recursive-call fixed-point case. |
| `computeFuture_buildRecursionAutomaton_child_of_marker` | If a body state reaches the selected marker, installing the backedge adds the recursion-entry menu to that state's future menu. | Recursive-call fixed-point case. |
| `computeFuture_buildRecursionAutomaton_child_at_initial` | The installed tagged entry has the same menu as the body initial state under the appropriate marker fixed point. | Entry equation. |

## 13. Recursion marker correspondence

Sources: [`CorrespondenceMarkerSkipping.lean`](Correspondence/CorrespondenceMarkerSkipping.lean)
and [`CorrespondenceMarkerReachability.lean`](Correspondence/CorrespondenceMarkerReachability.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `not_markerReachable_of_tailOccurrences_false` | If the selected variable has no permitted tail occurrence, its compiler marker is not same-cycle reachable. | Negative base fact. |
| `buildChoiceAutomaton_markerReachable_root` | Choice-root marker reachability is the disjunction of the reachable child-entry cases. | Choice marker induction. |
| `compiledFragmentAccepting_represented` | Every skipping state of a sufficient compiled fragment represents literal `skip`. | Turns graph completion witnesses into semantic witnesses. |
| `completionEval_unfold_recur_of_hygienic` | Under hygiene, the completion valuation of a recursion unfolding agrees with the corresponding body substitution valuation. | Completion/marker interaction. |
| `markerStopped_sequenceExecution_computeFuture` | Stopping a compiled free-variable marker in the sequence-execution view preserves the execution future menu because the marker has no offers and its target is a sink. | Shadow-graph construction. |
| `compilationMarkerReachable_iff` | For an ambient bound name occurring only in allowed tail positions, raw compiled marker reachability at a represented state is equivalent to syntax `markerReachableSubst = true`. | Raw graph/syntax marker theorem. |
| `compilationSequenceExecutionMarkerReachable_iff` | The same equivalence holds in the non-clock sequence-execution view. | Marker theorem needed by the recursion `execution` field. |

Both marker theorems are strong inductions over syntax size. Their branch
premise supplies closed proof bundles only for structurally smaller children;
the active body itself remains open under the ambient binder list.

## 14. Recursion completion closure

Sources: [`CorrespondenceCompletingRepresented.lean`](Correspondence/CorrespondenceCompletingRepresented.lean)
and [`CorrespondenceRecursionClosure*.lean`](Correspondence/CorrespondenceRecursionClosure.lean).

| Declaration | English statement | Proof role |
|---|---|---|
| `compiledFragmentNonClockPredecessor_eval` | If a non-clock compiler edge reaches a represented residual whose `completionEval` is true, then its source also represents a residual whose evaluation is true. | Semantic predecessor closure. |
| `compiledFragmentCompleting_represented` | Every compiled completing state represents some residual that can complete before `tock`. | Soundness of compiler completion metadata. |
| `compiledFragmentNonClockPredecessor_subst` | The analogous non-clock predecessor fact holds for the recursion-specific completion-after-substitution predicate. | Backward recursion closure soundness. |
| `recursionBodyCompletingClosure_subset` | Every state in the compiler's recursion-body backward closure satisfies the syntax completion-after-substitution predicate. | Closure soundness. |
| `completingBackClosure_lift_taggedChild` | A child closure witness lifts through constructor state tagging. | Structural closure induction. |
| `completingBackClosure_lift_recursion_nonmatching` | Closure transport through a nested recursion works for a different binder name. | Nested binder case. |
| `completingBackClosure_lift_recursion_matching` | Closure transport through a nested recursion works for the matching binder case under the corresponding valuation equation. | Matching nested binder case. |
| `recursionBodyCompletingClosure_superset_aux` | If the syntax completion-after-substitution predicate holds, the represented body state belongs to the compiler's backward closure. | Closure completeness. |
| `recursionBodyCompletingClosure_iff` (**private**) | At every represented body state, membership in the seeded non-clock backward closure is equivalent to semantic completion after substituting the enclosing recursion binder. | Exact recursion completion bridge. |
| `compilationCompletingCorrect_recursion_regular_leaf` | For a supported guarded tail-recursive hygienic binder, installed completing metadata agrees with `CanCompleteBeforeTock` at every represented recursion state. | Recursion bundle `completing` field. |

## 15. Final recursion step and execution leaves

Source: [`CorrespondenceRecursionLeaf.lean`](Correspondence/CorrespondenceRecursionLeaf.lean).

This module closes the two leaves that previously blocked the complete bundle.
The important declarations, in proof order, are:

| Declaration | English statement | Proof role |
|---|---|---|
| `compileTypeFuel_futureReferencesTarget` (**private**) | Whenever a compiled edge uses `FutureSpec.at inner removed`, the referenced `inner` state is exactly that edge's target. | Identifies execution references with semantic edge targets. |
| `SemanticFuturePolicy` (**private**) | A semantic step's future decoration is classified as either an explicit menu or a target menu with a removed set subtracted. | Makes exact future transport inductive. |
| `PolicyTypeOffers` (**private**) | A version of `TypeOffers` indexed by `SemanticFuturePolicy`. | Carries exact removed-set information through syntax cases. |
| `PolicyTypeOffers.toTypeOffers` (**private**) | Forgetting the policy yields an ordinary semantic offer derivation. | Connects the strengthened relation to public semantics. |
| `typeOffers_toPolicy` (**private**) | Every ordinary semantic offer derivation admits a compatible explicit/subtractive policy. | Introduces the strengthened invariant. |
| `policyTypeOffers_replaceVar_forward` (**private**) | A policy-indexed body offer derivation transports forward through recursion substitution with the correct future decoration. | Reverse compiled-edge-to-semantic direction. |
| `policyTypeOffers_replaceVar_backward` (**private**) | A step of a non-marker substituted residual comes from a policy-indexed step of the unsubstituted body residual. | Semantic-to-compiled direction. |
| `compilationRelation_futureSpecMatchesPolicy` (**private**) | The pending compiler edge corresponding to a policy-indexed semantic step uses the same explicit menu or the same `at target removed` policy. | Exact compiler/semantic future match. |
| `recursionBodyFutureCorrect_of_bundle` (**private**) | Body future correctness plus raw marker correspondence implies future correctness after installing recursive backedges. | Builds `RecursionBodyFutureCorrect`. |
| `RecursionBodyScopedStepCorrect` (**private**) | In an interface-avoiding local environment, steps of substituted body residuals correspond exactly to installed resolved edges from tagged states. | Scoped body-step contract. |
| `recursionBodyScopedStep_marker` (**private**) | If the represented residual is the bare recursive variable, substitution produces the whole binder and its only step matches the installed silent backedge. | Marker half of body step correctness. |
| `recursionBodyScopedStep_nonMarker` (**private**) | Away from the marker, capture-safe substitution neither creates nor destroys a step, and the installed edge has exactly the substituted semantic future policy. | First former `sorry` leaf. |
| `recursionBodyScopedStepCorrect_of_bundle` (**private**) | Splitting on whether the residual is the marker combines the previous two leaves. | Body step assembly. |
| `compilationScopedFragmentStepCorrect_recursion_of_body` (**private**) | The correct header plus the correct tagged body gives scoped step correctness for the whole recursion constructor. | Header/body composition. |
| `compilationSequenceExecutionCorrect_recursion_bounded_leaf` (**private**) | The installed recursion execution view has the syntax future menu and reaches skipping/completing metadata exactly when the represented residual can complete this cycle. | Second former `sorry` leaf. |
| `compilationScopedFragmentStepCorrect_recursion_bounded_leaf` (**private**) | The bounded/hygienic body facts and body bundle discharge whole-recursion scoped step correctness. | Recursion bundle `scopedStep`. |
| `compilationProofBundle_recursion_bounded_leaf` | For an open body bounded by `name :: bound`, regularity, its body bundle, and the raw/execution marker correspondences produce the complete recursion bundle. | Final recursion constructor leaf consumed by structural assembly. |

### 15.1 Why the non-marker step proof works

The proof cannot simply rewrite a semantic transition through substitution.
Nested recursion binders make that unsound unless capture facts are carried
explicitly. The landed proof performs the following chain:

1. derive `AllVariablesBound (name :: bound)` and `BinderFreshFor (name ::
   bound)` for the represented residual;
2. strengthen the substituted semantic step to `PolicyTypeOffers`;
3. invert substitution using `policyTypeOffers_replaceVar_backward`;
4. use the body bundle's scoped step field to obtain the exact body edge;
5. prove that edge's `FutureSpec` matches the semantic future policy;
6. resolve the same policy in the installed recursion graph using body future
   correctness;
7. lift the edge target with `TypeCompilationRelation.recur_body`.

The reverse direction inverts the installed edge. A marker edge contradicts
the non-marker hypothesis; an ordinary lifted body edge is converted back to a
body semantic step, strengthened to a policy, transported forward through
substitution, and then forgotten back to ordinary `TypeOffers`.

This is the exact-removed-set route. A proposed shortcut based on proving the
entry menu disjoint from the current offers was rejected: with the current
`SuffixMessageIds`, `SameCycleMessageLinear` does not imply that disjointness.

### 15.2 Why the execution proof works

For future menus, define:

```text
bodyFragment          = compileTypeFuel body
bodyExecutionFragment = sequenceExecutionFragment bodyFragment
stoppedBody           = markerStoppedFragment bodyExecutionFragment name
shadowFragment        = buildRecursionAutomaton signature name stoppedBody
```

`sequenceExecution_buildRecursion_edges` shows that the actual installed
execution graph and `shadowFragment` have the same edges. Therefore
`computeFuture_eq_of_same_edges` transfers future computation to the shadow.
The marker/no-marker equations of `buildRecursionAutomaton`, together with
`compilationSequenceExecutionMarkerReachable_iff` and
`futureOffersSubst_eq_union_marker`, then reproduce the syntax future equation
exactly.

For completion reachability, let `C` be the set of execution states that
represent some residual whose `completionEval (fun _ => false)` is true.
Skipping and completing metadata lie in `C` by
`compiledFragmentAccepting_represented` and
`compiledFragmentCompleting_represented`. The complement of `C` is closed
under execution references because every such reference comes from a
non-clock raw edge and `compiledFragmentNonClockPredecessor_eval` propagates
truth backward. Hence any execution path ending in completion metadata starts
at a state in `C`; residual uniqueness and the all-false completion equation
give `CanCompleteBeforeTock`. The reverse implication uses self-reachability
and `compilationCompletingCorrect_recursion_regular_leaf`.

## 16. Reading and extending the proof

For a new type constructor, the reusable route is:

1. add its `TypeCompilationRelation` cases;
2. prove initial/state/future-target compiler well-formedness;
3. prove edge classifiers before proving step correspondence;
4. prove target representation independently as
   `CompilationResolvedEdgeTargetsRelated`;
5. prove `future` and `completing` equations;
6. prove scoped raw steps, transporting `AvoidsInterface` where necessary;
7. prove the sequence-execution field, even if the constructor itself is not a
   sequence, because an enclosing sequence may inspect it;
8. package the four results in a constructor leaf and add that leaf to
   `compilationProofBundle_of_boundedRegular`.

The key architectural rule is that recursion bodies are open terms. Carry the
ambient binder list, `AllVariablesBound`, `BinderHygienic`, and tail-occurrence
facts down to the exact leaf that needs them; do not attempt to manufacture a
closed proof bundle for the active body.
