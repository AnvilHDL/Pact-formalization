import Anvilpp.PactTypes.Correspondence.CorrespondenceChoice

/-!
# Sequence-execution automaton: graph-reachability scaffolding
-/

namespace Pact

noncomputable section

/-! ### Sequence entry and literal-skip bridge -/

/-- The compiled entry of a sequence is the tagged entry of its left child. -/
theorem compileType_sequence_initial_eq
    (signature : TypeAlphabet) (left right : PactType) :
    (compileType signature (.seq left right)).initial =
      .child 0 (compileType signature left).initial := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  simp only [compileType]
  rw [hFragment]
  simp [fragment, buildSequenceAutomaton, finishAutomatonFragment,
    childState, hInitial]

/-- Outgoing edges at a tagged left sequence state are exactly the redirected
images of the left child's own outgoing edges, plus two narrow bridge
families the redirect alone cannot produce: — only at the left entry, and
only when that entry is itself accepting (provably only `left = .skip`, see
`sequenceEntryBridgeEdges`) — one `skip_seq` edge per local environment
straight into `right`'s entry; and — at every `left.accepting ∪
left.completing` state — one bookkeeping-only `.future` edge into `right`'s
entry (redirect only ever rewrites *in*-edges, so a state's own route into
`right` for `computeFuture` purposes would otherwise depend on it happening to
carry a self-referencing edge of its own; see `sequenceCompletingBridgeEdges`).

This replaces the old three-way disjunction (child edge / silent skip-bridge /
`.future` bridge) with a structurally identical one, now derived rather than
built in directly: a left edge landing on a deleted (accepting, but not the
entry) state is *fused* with the administrative step and now lands on
`right`'s entry directly, carrying its own label rather than a fresh silent
one, and the `.future` bridge for an ordinary `.future`-labeled edge is
subsumed by redirecting the `FutureSpec.at` target — the dedicated
`sequenceCompletingBridgeEdges` family only remains needed for the closure
`computeFuture` performs independently of any literal outgoing edge.  The
right child contributes nothing here because `childPendingEdges 1 right`
sources are all `1`-tagged. -/
theorem buildSequenceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 0 state ↔
      (∃ childEdge ∈ left.edges,
        childEdge.source = state ∧
        edge = sequenceLeftEdge left right childEdge) ∨
      (state = left.initial ∧ left.initial ∈ left.accepting ∧
        ∃ environment ∈ signature.localEnvironments,
          edge =
            { source := childState 0 left.initial
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 1 right.initial) ∅
              target := childState 1 right.initial }) ∨
      ((state ∈ left.accepting ∨ state ∈ left.completing) ∧
        edge =
          { source := childState 0 state
            environment := .empty
            label := .future
            current := ∅
            future := .at (childState 1 right.initial) ∅
            target := childState 1 right.initial }) := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((hLeft | hRight) | hEntryBridge) | hCompletingBridge
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [sequenceLeftEdge, childState] using hChildSource
      exact Or.inl ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · simp only [sequenceEntryBridgeEdges] at hEntryBridge
      split at hEntryBridge
      · rename_i hAccepting
        simp only [Finset.mem_image] at hEntryBridge
        obtain ⟨environment, hEnvironment, hEdge⟩ := hEntryBridge
        have hBridgeSource := hSource
        rw [← hEdge] at hBridgeSource
        have hState : state = left.initial := by
          simpa [childState] using hBridgeSource.symm
        exact Or.inr (Or.inl ⟨hState, hAccepting, environment, hEnvironment,
          hEdge.symm⟩)
      · simp at hEntryBridge
    · simp only [sequenceCompletingBridgeEdges, Finset.mem_union,
        Finset.mem_image] at hCompletingBridge
      obtain ⟨completingState, hCompletingState, hEdge⟩ := hCompletingBridge
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : state = completingState := by
        simpa [childState] using hBridgeSource.symm
      subst hState
      exact Or.inr (Or.inr ⟨hCompletingState, hEdge.symm⟩)
  · rintro (⟨childEdge, hChildEdge, hChildSource, rfl⟩ |
      ⟨rfl, hAccepting, environment, hEnvironment, rfl⟩ |
      ⟨hCompleting, rfl⟩)
    · constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩))
      · simp [sequenceLeftEdge, childState, hChildSource]
    · constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        refine Or.inl (Or.inr ?_)
        simp only [sequenceEntryBridgeEdges]
        rw [if_pos hAccepting]
        exact Finset.mem_image_of_mem _ hEnvironment
      · rfl
    · constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        refine Or.inr ?_
        simp only [sequenceCompletingBridgeEdges]
        exact Finset.mem_image_of_mem _ (Finset.mem_union.mpr hCompleting)
      · rfl

private def sequenceExecutionEdge
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := match edge.label with
      | .future => edge.future
      | _ => .at edge.target edge.current
    target := edge.target }

@[simp] private theorem sequenceExecutionEdge_source
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).source = edge.source := rfl

@[simp] private theorem sequenceExecutionEdge_environment
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).environment = edge.environment := rfl

@[simp] private theorem sequenceExecutionEdge_label
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).label = edge.label := rfl

@[simp] private theorem sequenceExecutionEdge_current
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).current = edge.current := rfl

@[simp] private theorem sequenceExecutionEdge_target
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).target = edge.target := rfl

@[simp] private theorem sequenceExecutionEdge_future
    (edge : PendingAutomatonEdge) :
    (sequenceExecutionEdge edge).future =
      match edge.label with
      | .future => edge.future
      | _ => .at edge.target edge.current := rfl

/-- The child graph followed by a sequence left component.  Ordinary
constructor edges are re-decorated by their transition target, exactly as in
`buildSequenceAutomaton`; construction-only `.future` edges retain their
original symbolic decoration. -/
def sequenceExecutionAutomaton
    (child : AutomatonFragment) : PendingAutomaton :=
  { states := child.states ∪ child.edges.image PendingAutomatonEdge.target
    edges := child.edges.image sequenceExecutionEdge }

/-- Repackage the execution view as a constructor fragment while retaining
the syntax metadata of the represented child.  This is used only to compose
an outer sequence closure; it does not alter the public compiler. -/
def sequenceExecutionFragment
    (child : AutomatonFragment) : AutomatonFragment :=
  { states := (sequenceExecutionAutomaton child).states
    initial := child.initial
    accepting := child.accepting
    completing := child.completing
    edges := (sequenceExecutionAutomaton child).edges }

theorem sequenceExecutionFragment_markerSource
    (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) :
    MarkerSource (sequenceExecutionFragment fragment) name state ↔
      MarkerSource fragment name state := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
      Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    exact ⟨raw, hRaw, by simpa using hSource, by simpa using hLabel⟩
  · rintro ⟨raw, hRaw, hSource, hLabel⟩
    refine ⟨sequenceExecutionEdge raw, ?_, by simpa, by simpa⟩
    exact Finset.mem_image.mpr ⟨raw, hRaw, rfl⟩

@[simp] private theorem sequenceExecutionEdge_idempotent
    (edge : PendingAutomatonEdge) :
    sequenceExecutionEdge (sequenceExecutionEdge edge) =
      sequenceExecutionEdge edge := by
  cases hLabel : edge.label <;> cases hFuture : edge.future <;>
    simp [sequenceExecutionEdge, hLabel, hFuture]

private theorem sequenceExecutionEdge_childPendingEdge
    (index : Nat) (edge : PendingAutomatonEdge) :
    sequenceExecutionEdge (childPendingEdge index edge) =
      childPendingEdge index (sequenceExecutionEdge edge) := by
  cases hLabel : edge.label <;> cases hFuture : edge.future <;>
    simp [sequenceExecutionEdge, childPendingEdge, childFutureSpec,
      childState, hLabel, hFuture]

theorem sequenceExecutionFragment_futureTargetsInStates
    (child : AutomatonFragment)
    (hTargets : child.FutureTargetsInStates) :
    (sequenceExecutionFragment child).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
    Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hLabel : childEdge.label with
  | future =>
      cases hSpec : childEdge.future with
      | explicit offers =>
          simp [sequenceExecutionEdge, hLabel, hSpec] at hFuture
      | «at» referenced childRemoved =>
          have hTarget : target = referenced := by
            have hFields : referenced = target ∧ childRemoved = removed := by
              simpa [sequenceExecutionEdge, hLabel, hSpec] using hFuture
            exact hFields.1.symm
          subst target
          have hReferenced := hTargets childEdge hChildEdge referenced
            childRemoved hSpec
          exact Finset.mem_union_left _ hReferenced
  | visible label =>
      have hTarget : target = childEdge.target := by
        have hFields : childEdge.target = target ∧
            childEdge.current = removed := by
          simpa [sequenceExecutionEdge, hLabel] using hFuture
        exact hFields.1.symm
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)

  | «variable» name =>
      have hTarget : target = childEdge.target := by
        have hFields : childEdge.target = target ∧
            childEdge.current = removed := by
          simpa [sequenceExecutionEdge, hLabel] using hFuture
        exact hFields.1.symm
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)

/-- A redirected left edge is already in execution-normal form.  This is
Invariant 1 doing the work: `sequenceLeftEdge` copies `label`/`current`
verbatim and sets `future := .at target current` for non-`.future` labels —
which is precisely what `sequenceExecutionEdge` computes — while `.future`
edges keep their (redirected) symbolic spec, which it leaves alone. -/
@[simp] private theorem sequenceExecutionEdge_sequenceLeftEdge
    (left right : AutomatonFragment) (edge : PendingAutomatonEdge) :
    sequenceExecutionEdge (sequenceLeftEdge left right edge) =
      sequenceLeftEdge left right edge := by
  cases hLabel : edge.label <;>
    simp [sequenceExecutionEdge, sequenceLeftEdge, hLabel]

/-- The left component of a sequence depends on the right fragment only
through its entry state, and the execution view preserves that entry. -/
private theorem sequenceLeftEdge_sequenceExecutionFragment
    (left right : AutomatonFragment) (edge : PendingAutomatonEdge) :
    sequenceLeftEdge left (sequenceExecutionFragment right) edge =
      sequenceLeftEdge left right edge := by
  cases hLabel : edge.label <;>
    simp [sequenceLeftEdge, sequenceRedirect, sequenceExecutionFragment,
      hLabel]

/-- The entry bridge likewise only depends on `right` through its entry
state, so it is unaffected by taking the execution view. -/
private theorem sequenceEntryBridgeEdges_sequenceExecutionFragment
    (signature : TypeAlphabet) (left right : AutomatonFragment) :
    sequenceEntryBridgeEdges signature left (sequenceExecutionFragment right) =
      sequenceEntryBridgeEdges signature left right := by
  simp [sequenceEntryBridgeEdges, sequenceExecutionFragment]

/-- An entry bridge edge is already in execution-normal form: it carries a
`.visible` label with `future := .at target ∅`, exactly what
`sequenceExecutionEdge` computes. -/
@[simp] private theorem sequenceExecutionEdge_of_mem_sequenceEntryBridgeEdges
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    {edge : PendingAutomatonEdge}
    (hEdge : edge ∈ sequenceEntryBridgeEdges signature left right) :
    sequenceExecutionEdge edge = edge := by
  simp only [sequenceEntryBridgeEdges] at hEdge
  split at hEdge
  · simp only [Finset.mem_image] at hEdge
    obtain ⟨environment, _, rfl⟩ := hEdge
    simp [sequenceExecutionEdge]
  · simp at hEdge

/-- The completing bridge likewise only depends on `right` through its entry
state, so it is unaffected by taking the execution view. -/
private theorem sequenceCompletingBridgeEdges_sequenceExecutionFragment
    (left right : AutomatonFragment) :
    sequenceCompletingBridgeEdges left (sequenceExecutionFragment right) =
      sequenceCompletingBridgeEdges left right := by
  simp [sequenceCompletingBridgeEdges, sequenceExecutionFragment]

/-- A completing bridge edge is already in execution-normal form: it carries
a `.future` label, so `sequenceExecutionEdge` leaves its `future` field (and
every other field) untouched. -/
@[simp] private theorem
    sequenceExecutionEdge_of_mem_sequenceCompletingBridgeEdges
    (left right : AutomatonFragment) {edge : PendingAutomatonEdge}
    (hEdge : edge ∈ sequenceCompletingBridgeEdges left right) :
    sequenceExecutionEdge edge = edge := by
  simp only [sequenceCompletingBridgeEdges, Finset.mem_image] at hEdge
  obtain ⟨state, _, rfl⟩ := hEdge
  simp [sequenceExecutionEdge]

theorem sequenceExecution_buildSequence_edges
    (signature : TypeAlphabet) (left right : AutomatonFragment) :
    (sequenceExecutionAutomaton
        (buildSequenceAutomaton signature left right)).edges =
      (buildSequenceAutomaton signature left
        (sequenceExecutionFragment right)).edges := by
  classical
  ext edge
  simp only [sequenceExecutionAutomaton, buildSequenceAutomaton,
    finishAutomatonFragment, childPendingEdges, Finset.mem_image,
    Finset.mem_union]
  constructor
  · rintro ⟨raw, (((⟨rawChild, hRawChild, rfl⟩ | ⟨rawChild, hRawChild, rfl⟩) |
      hEntryRaw) | hCompletingRaw), rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨rawChild, hRawChild, by
        rw [sequenceExecutionEdge_sequenceLeftEdge,
          sequenceLeftEdge_sequenceExecutionFragment]⟩))
    · refine Or.inl (Or.inl (Or.inr ⟨sequenceExecutionEdge rawChild, ?_,
        (sequenceExecutionEdge_childPendingEdge 1 rawChild).symm⟩))
      simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
        Finset.mem_image]
      exact ⟨rawChild, hRawChild, rfl⟩
    · refine Or.inl (Or.inr ?_)
      rw [sequenceEntryBridgeEdges_sequenceExecutionFragment,
        sequenceExecutionEdge_of_mem_sequenceEntryBridgeEdges
          signature left right hEntryRaw]
      exact hEntryRaw
    · refine Or.inr ?_
      rw [sequenceCompletingBridgeEdges_sequenceExecutionFragment,
        sequenceExecutionEdge_of_mem_sequenceCompletingBridgeEdges
          left right hCompletingRaw]
      exact hCompletingRaw
  · rintro (((⟨rawChild, hRawChild, rfl⟩ | ⟨e, hE, rfl⟩) | hEntryEdge) |
      hCompletingEdge)
    · exact ⟨sequenceLeftEdge left right rawChild,
        Or.inl (Or.inl (Or.inl ⟨rawChild, hRawChild, rfl⟩)), by
          rw [sequenceExecutionEdge_sequenceLeftEdge,
            sequenceLeftEdge_sequenceExecutionFragment]⟩
    · simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
        Finset.mem_image] at hE
      obtain ⟨rawChild, hRawChild, rfl⟩ := hE
      exact ⟨childPendingEdge 1 rawChild,
        Or.inl (Or.inl (Or.inr ⟨rawChild, hRawChild, rfl⟩)),
        sequenceExecutionEdge_childPendingEdge 1 rawChild⟩
    · rw [sequenceEntryBridgeEdges_sequenceExecutionFragment] at hEntryEdge
      exact ⟨edge, Or.inl (Or.inr hEntryEdge),
        sequenceExecutionEdge_of_mem_sequenceEntryBridgeEdges
          signature left right hEntryEdge⟩
    · rw [sequenceCompletingBridgeEdges_sequenceExecutionFragment]
        at hCompletingEdge
      exact ⟨edge, Or.inr hCompletingEdge,
        sequenceExecutionEdge_of_mem_sequenceCompletingBridgeEdges
          left right hCompletingEdge⟩

/-- Executing an installed recursion is edge-for-edge the recursion
constructor applied to the body's execution view after its still-symbolic
calls of the installed binder have been stopped.  Those calls are immediately
rewritten as backedges, so their temporary execution targets are irrelevant. -/
theorem sequenceExecution_buildRecursion_edges
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment) :
    (sequenceExecutionAutomaton
        (buildRecursionAutomaton signature name body)).edges =
      (buildRecursionAutomaton signature name
        (markerStoppedFragment (sequenceExecutionFragment body) name)).edges := by
  classical
  let header : Finset PendingAutomatonEdge :=
    signature.localEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := AutomatonConstructionLabel.visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
  let backedge : PendingAutomatonEdge → PendingAutomatonEdge := fun edge =>
    { source := childState 0 edge.source
      environment := edge.environment
      label := AutomatonConstructionLabel.visible TypeLabel.silent
      current := ∅
      future := .at (childState 0 body.initial) ∅
      target := childState 0 body.initial }
  let install : PendingAutomatonEdge → PendingAutomatonEdge := fun edge =>
    if edge.label = AutomatonConstructionLabel.variable name then
      backedge edge
    else childPendingEdge 0 edge
  let stop : PendingAutomatonEdge → PendingAutomatonEdge := fun edge =>
    if edge.label = AutomatonConstructionLabel.variable name then
      { edge with current := ∅, future := .explicit ∅ }
    else edge
  have hPoint : ∀ edge,
      sequenceExecutionEdge (install edge) =
        install (stop (sequenceExecutionEdge edge)) := by
    intro edge
    cases hLabel : edge.label <;> cases hFuture : edge.future <;>
      simp [install, stop, backedge, sequenceExecutionEdge,
        childPendingEdge, childFutureSpec, childState, hLabel, hFuture]
    case variable.explicit marker offers =>
      by_cases hName : marker = name <;>
        simp_all [install, stop, backedge, sequenceExecutionEdge,
          childPendingEdge, childFutureSpec, childState, hName]
    case variable.at marker target removed =>
      by_cases hName : marker = name <;>
        simp_all [install, stop, backedge, sequenceExecutionEdge,
          childPendingEdge, childFutureSpec, childState, hName]
  have hHeader : header.image sequenceExecutionEdge = header := by
    ext edge
    simp [header, sequenceExecutionEdge, TypeLabel.silent]
  change (header ∪ body.edges.image install).image sequenceExecutionEdge =
    header ∪ ((body.edges.image sequenceExecutionEdge).image stop).image
      install
  rw [Finset.image_union, hHeader, Finset.image_image, Finset.image_image,
    Finset.image_image]
  congr 1
  apply congrArg (Finset.image · body.edges)
  funext edge
  exact hPoint edge

private theorem sequenceExecution_buildChoice_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    edge ∈ parent.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .child 0 state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (buildChoiceAutomaton_outgoing_left signature left right
      selectionLeft selectionRight state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge 0 childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge 0 childRaw, ?_, rfl⟩
      exact (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight childRaw.source
          (childPendingEdge 0 childRaw)).mpr
            ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_buildChoice_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    edge ∈ parent.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .child 1 state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (buildChoiceAutomaton_outgoing_right signature left right
      selectionLeft selectionRight state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge 1 childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge 1 childRaw, ?_, rfl⟩
      exact (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight childRaw.source
          (childPendingEdge 1 childRaw)).mpr
            ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_buildChoice_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.referencedStates (.child 0 state) =
      (child.referencedStates state).image (.child 0) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_buildChoice_outgoing_left signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_buildChoice_outgoing_right signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.offersAt (.child 0 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_buildChoice_outgoing_left signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_buildChoice_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_buildChoice_outgoing_right signature left right
    selectionLeft selectionRight state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

theorem sequenceExecutionAutomaton_referencesClosed
    (child : AutomatonFragment)
    (hTargets : child.FutureTargetsInStates) :
    (sequenceExecutionAutomaton child).ReferencesClosed := by
  classical
  intro source hSource target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hLabel : childEdge.label with
  | future =>
      cases hSpec : childEdge.future with
      | explicit offers => simp [hLabel, hSpec,
          AutomatonConstructionLabel.semantic] at hFuture
      | «at» referenced removed =>
          simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
            TypeLabel.silent] at hFuture
          have hTarget : target = referenced := by
            simpa using hFuture
          subst target
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          simp [sequenceExecutionAutomaton, hReferenced]
  | visible label =>
      by_cases hTock : label = TypeLabel.tock
      · subst label
        simp [hLabel, AutomatonConstructionLabel.semantic] at hFuture
      · have hTarget : target = childEdge.target := by
          simpa [hLabel, AutomatonConstructionLabel.semantic, hTock]
            using hFuture
        subst target
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)
  | «variable» name =>
      have hTarget : target = childEdge.target := by
        simpa [hLabel, AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩)

/-- A non-clock resolved edge is followed by the execution view, independently
of how its original symbolic future was resolved. -/
theorem sequenceExecution_resolvedEdge_target_referenced
    (fragment : AutomatonFragment) (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hVisible : edge.label ≠ .future)
    (hNonClock : edge.label.semantic ≠ TypeLabel.tock) :
    edge.target ∈ (sequenceExecutionAutomaton fragment).referencedStates
      edge.source := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, rfl⟩
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter]
  refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨raw, hRaw, rfl⟩
  · cases hLabel : raw.label <;>
      simp_all [sequenceExecutionEdge, AutomatonConstructionLabel.semantic]

theorem resolvedAutomatonEdge_visible_of_pending_visible
    (fragment : AutomatonFragment)
    (hVisible : ∀ raw ∈ fragment.edges, raw.label ≠ .future →
      ∃ label, raw.label = .visible label)
    (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hSemantic : edge.label ≠ .future) :
    ∃ label, edge.label = .visible label := by
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, rfl⟩
  exact hVisible raw hRaw hSemantic

private theorem sequenceExecution_taggedChild_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    edge ∈ parentExecution.edges ∧
        edge.source = childState index state ↔
      ∃ childEdge ∈ childExecution.edges,
        childEdge.source = state ∧
          edge = childPendingEdge index childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = childState index state := by
      simpa [sequenceExecutionEdge] using hSource
    rcases (hOutgoing state raw).mp ⟨hRaw, hRawSource⟩ with
      ⟨childRaw, hChildRaw, hChildSource, rfl⟩
    refine ⟨sequenceExecutionEdge childRaw, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨childRaw, hChildRaw, rfl⟩
    · simpa [sequenceExecutionEdge] using hChildSource
    · exact sequenceExecutionEdge_childPendingEdge index childRaw
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childRaw, hChildRaw, rfl⟩
    rw [← sequenceExecutionEdge_childPendingEdge]
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨childPendingEdge index childRaw, ?_, rfl⟩
      exact (hOutgoing childRaw.source (childPendingEdge index childRaw)).mpr
        ⟨childRaw, hChildRaw, rfl, rfl⟩ |>.1
    · simpa [sequenceExecutionEdge, childPendingEdge, childState] using
        hChildSource

private theorem sequenceExecution_taggedChild_referencedStates
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.referencedStates (childState index state) =
      (childExecution.referencedStates state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [sequenceExecution_taggedChild_outgoing parent child index
    hOutgoing state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_taggedChild_offersAt
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.offersAt (childState index state) =
      childExecution.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [sequenceExecution_taggedChild_outgoing parent child index
    hOutgoing state]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem sequenceExecution_taggedChild_states_subset
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    childExecution.states.image (childState index) ⊆
      parentExecution.states := by
  classical
  dsimp only
  intro tagged hTagged
  rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · exact Or.inl (hStates (Finset.mem_image.mpr ⟨_, hState, rfl⟩))
  · right
    refine ⟨childPendingEdge index edge, ?_, ?_⟩
    · exact (hOutgoing edge.source (childPendingEdge index edge)).mpr
        ⟨edge, hEdge, rfl, rfl⟩ |>.1
    · simp [childPendingEdge, childState]

theorem sequenceExecution_taggedChild_futureReachable
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states)
    (hTargets : child.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    parentExecution.futureReachable (childState index state) =
      (childExecution.futureReachable state).image (childState index) := by
  let parentExecution := sequenceExecutionAutomaton parent
  let childExecution := sequenceExecutionAutomaton child
  have hClosed : childExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed child hTargets
  have hChildState : state ∈ childExecution.states :=
    Finset.mem_union_left _ hState
  have hSubset := sequenceExecution_taggedChild_states_subset parent child
    index hOutgoing hStates
  have hCard : childExecution.states.card ≤ parentExecution.states.card := by
    calc
      childExecution.states.card =
          (childExecution.states.image (childState index)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parentExecution.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding childExecution
    parentExecution (childState index)
      (sequenceExecution_taggedChild_referencedStates parent child index
        hOutgoing) hClosed state hChildState hCard

/-- Marker reachability follows the same tagged-child embedding as ordinary
execution reachability. -/
theorem sequenceExecution_taggedChild_markerReachable
    (parent child : AutomatonFragment) (index : Nat) (name : String)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states)
    (hTargets : child.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    MarkerReachable (sequenceExecutionFragment parent) name
        (childState index state) ↔
      MarkerReachable (sequenceExecutionFragment child) name state := by
  classical
  have hReach := sequenceExecution_taggedChild_futureReachable parent child
    index hOutgoing hStates hTargets state hState
  have hMarkerSource : ∀ q,
      MarkerSource (sequenceExecutionFragment parent) name
          (childState index q) ↔
        MarkerSource (sequenceExecutionFragment child) name q := by
    intro q
    apply markerSource_of_outgoing_childPendingEdge
      (sequenceExecutionFragment parent) (sequenceExecutionFragment child)
      index name q
    intro edge
    simpa [sequenceExecutionFragment] using
      (sequenceExecution_taggedChild_outgoing parent child index hOutgoing q
        edge)
  simp only [MarkerReachable]
  change (∃ reached ∈ (sequenceExecutionAutomaton parent).futureReachable
      (childState index state),
        MarkerSource (sequenceExecutionFragment parent) name reached) ↔ _
  rw [hReach]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨reached, hReached, rfl⟩, hMarker⟩
    exact ⟨reached, hReached, (hMarkerSource reached).mp hMarker⟩
  · rintro ⟨reached, hReached, hMarker⟩
    exact ⟨childState index reached, ⟨reached, hReached, rfl⟩,
      (hMarkerSource reached).mpr hMarker⟩

theorem sequenceExecution_taggedChild_computeFuture
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hStates : child.states.image (childState index) ⊆ parent.states)
    (hTargets : child.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    let parentExecution := sequenceExecutionAutomaton parent
    let childExecution := sequenceExecutionAutomaton child
    computeFuture parentExecution (childState index state) =
      computeFuture childExecution state := by
  let parentExecution := sequenceExecutionAutomaton parent
  let childExecution := sequenceExecutionAutomaton child
  have hClosed : childExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed child hTargets
  have hChildState : state ∈ childExecution.states :=
    Finset.mem_union_left _ hState
  have hSubset := sequenceExecution_taggedChild_states_subset parent child
    index hOutgoing hStates
  have hCard : childExecution.states.card ≤ parentExecution.states.card := by
    calc
      childExecution.states.card =
          (childExecution.states.image (childState index)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parentExecution.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding childExecution parentExecution
    (childState index)
      (sequenceExecution_taggedChild_referencedStates parent child index
        hOutgoing)
      (sequenceExecution_taggedChild_offersAt parent child index hOutgoing)
      hClosed state hChildState hCard

theorem taggedCompletionWitness_iff
    (parent child : AutomatonFragment) (index : Nat)
    (reached : Finset TypeAutomatonState)
    (hAccepting : ∀ state,
      childState index state ∈ parent.accepting ↔ state ∈ child.accepting)
    (hCompleting : ∀ state,
      childState index state ∈ parent.completing ↔
        state ∈ child.completing) :
    (∃ completed ∈ reached.image (childState index),
        completed ∈ parent.accepting ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reached,
        completed ∈ child.accepting ∨ completed ∈ child.completing := by
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with ⟨completed, hReached, rfl⟩
    exact ⟨completed, hReached,
      hCompleted.imp (hAccepting completed).mp (hCompleting completed).mp⟩
  · rintro ⟨completed, hReached, hCompleted⟩
    exact ⟨childState index completed,
      Finset.mem_image.mpr ⟨completed, hReached, rfl⟩,
      hCompleted.imp (hAccepting completed).mpr (hCompleting completed).mpr⟩

private theorem sequenceExecution_root_offersAt_eq
    (fragment : AutomatonFragment)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed) :
    (sequenceExecutionAutomaton fragment).offersAt .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).offersAt .root := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .root := by
      simpa using hSource
    rcases hShape raw hRaw hRawSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨raw, ⟨hRaw, hRawSource⟩, ?_⟩
    cases hLabel : raw.label with
    | future => exact (hNotFuture hLabel).elim
    | visible label => simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
    | «variable» name =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    rcases hShape edge hEdge hSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨sequenceExecutionEdge edge, ⟨?_, by simpa⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    · cases hLabel : edge.label with
      | future => exact (hNotFuture hLabel).elim
      | visible label =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer
      | «variable» name =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hOffer

theorem sequenceExecution_root_referencedStates_eq
    (fragment : AutomatonFragment)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed) :
    (sequenceExecutionAutomaton fragment).referencedStates .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    have hRawSource : raw.source = .root := by
      simpa using hSource
    rcases hShape raw hRaw hRawSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨raw, ⟨hRaw, hRawSource⟩, ?_⟩
    cases hLabel : raw.label with
    | future => exact (hNotFuture hLabel).elim
    | visible label =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
    | «variable» name =>
        simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    rcases hShape edge hEdge hSource with ⟨hNotFuture, removed, hFuture⟩
    refine ⟨sequenceExecutionEdge edge, ⟨?_, by simpa⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    · cases hLabel : edge.label with
      | future => exact (hNotFuture hLabel).elim
      | visible label =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference
      | «variable» name =>
          simpa [sequenceExecutionEdge, hLabel, hFuture] using hReference

theorem sequenceExecution_computeFuture_root_eq
    (fragment : AutomatonFragment)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hUpper :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root ⊆ insert .root entries)
    (hEntries : entries ⊆
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root)
    (hEntryFuture : ∀ entry ∈ entries,
      computeFuture (sequenceExecutionAutomaton fragment) entry =
        computeFuture
          ({ states := fragment.states, edges := fragment.edges } :
            PendingAutomaton) entry) :
    computeFuture (sequenceExecutionAutomaton fragment) .root =
      computeFuture
        ({ states := fragment.states, edges := fragment.edges } :
          PendingAutomaton) .root := by
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  have hPendingClosed : pending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
      hTargets
  have hExecutionClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hExecutionRoot : (.root : TypeAutomatonState) ∈ execution.states :=
    Finset.mem_union_left _ hRoot
  have hOffers : execution.offersAt .root = pending.offersAt .root := by
    simpa [execution, pending] using
      sequenceExecution_root_offersAt_eq fragment hShape
  have hReferences : execution.referencedStates .root =
      pending.referencedStates .root := by
    simpa [execution, pending] using
      sequenceExecution_root_referencedStates_eq fragment hShape
  have hExecutionUpper : execution.referencedStates .root ⊆
      insert .root entries := by simpa [hReferences] using hUpper
  have hExecutionEntries : entries ⊆ execution.referencedStates .root := by
    simpa [hReferences] using hEntries
  rw [computeFuture_eq_offersAt_union_biUnion execution .root entries
      hExecutionClosed hExecutionRoot hExecutionUpper hExecutionEntries,
    computeFuture_eq_offersAt_union_biUnion pending .root entries
      hPendingClosed hRoot hUpper hEntries,
    hOffers]
  congr 1
  ext action
  simp only [Finset.mem_biUnion]
  constructor <;> rintro ⟨entry, hEntry, hAction⟩ <;>
    refine ⟨entry, hEntry, ?_⟩
  · rw [← hEntryFuture entry hEntry]
    exact hAction
  · rw [hEntryFuture entry hEntry]
    exact hAction

theorem sequenceExecution_futureReachable_root
    (fragment : AutomatonFragment)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hUpper :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root ⊆ insert .root entries)
    (hEntries : entries ⊆
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root) :
    (sequenceExecutionAutomaton fragment).futureReachable .root =
      {.root} ∪ entries.biUnion
        (sequenceExecutionAutomaton fragment).futureReachable := by
  let execution := sequenceExecutionAutomaton fragment
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hExecutionRoot : (.root : TypeAutomatonState) ∈ execution.states :=
    Finset.mem_union_left _ hRoot
  have hReferences : execution.referencedStates .root =
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).referencedStates .root := by
    simpa [execution] using
      sequenceExecution_root_referencedStates_eq fragment hShape
  apply execution.futureReachable_eq_self_union_biUnion .root entries
    hClosed hExecutionRoot
  · simpa [hReferences] using hUpper
  · simpa [hReferences] using hEntries

theorem sequenceExecution_markerReachable_root_of_entries
    (fragment : AutomatonFragment) (name : String)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hUpper : fragment.toPending.referencedStates .root ⊆
      insert .root entries)
    (hEntries : entries ⊆ fragment.toPending.referencedStates .root) :
    MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
      MarkerSource (sequenceExecutionFragment fragment) name .root ∨
        ∃ entry ∈ entries,
          MarkerReachable (sequenceExecutionFragment fragment) name entry := by
  classical
  have hReach := sequenceExecution_futureReachable_root fragment entries
    hTargets hRoot hShape hUpper hEntries
  simp only [MarkerReachable]
  change (∃ reached ∈ (sequenceExecutionAutomaton fragment).futureReachable
      .root, MarkerSource (sequenceExecutionFragment fragment) name reached) ↔ _
  rw [hReach]
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
  constructor
  · rintro ⟨reached, rfl | ⟨entry, hEntry, hReached⟩, hMarker⟩
    · exact Or.inl hMarker
    · exact Or.inr ⟨entry, hEntry, reached, hReached, hMarker⟩
  · rintro (hMarker | ⟨entry, hEntry, reached, hReached, hMarker⟩)
    · exact ⟨.root, Or.inl rfl, hMarker⟩
    · exact ⟨reached, Or.inr ⟨entry, hEntry, hReached⟩, hMarker⟩

theorem sequenceExecution_buildExclusiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    rcases hElse with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

theorem sequenceExecution_buildConjunctiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElseChild) | hEnabled) | hWait) |
    hElse)
  · simp only [childPendingEdges, Finset.mem_image] at hConjunction
    rcases hConjunction with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [childPendingEdges, Finset.mem_image] at hElseChild
    rcases hElseChild with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hElse
    rcases hElse with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

theorem sequenceExecution_buildSelectedConjunctiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildSelectedConjunctiveOfferAutomaton,
    finishAutomatonFragment, Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    rcases hElse with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

theorem buildExclusiveOffer_child0_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).accepting ↔
      state ∈ elseAutomaton.accepting := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentAccepting
    branchAutomata state
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childAccepting 0 elseAutomaton ↔
      state ∈ elseAutomaton.accepting := by
    simp [childAccepting, childState]
  rw [hChild]
  simp [hNotIndexed]

theorem buildExclusiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).completing ↔
      state ∈ elseAutomaton.completing := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentCompleting
    branchAutomata state
  have hNotHeader : childState 0 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childCompleting 0 elseAutomaton ↔
      state ∈ elseAutomaton.completing := by
    simp [childCompleting, childState]
  rw [hChild]
  simp [hNotHeader, hNotIndexed]

theorem buildExclusiveOffer_root_not_accepting
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    (.root : TypeAutomatonState) ∉
      (buildExclusiveOfferAutomaton signature branches elseAutomaton
        branchAutomata).accepting := by
  have hNotIndexed := root_not_mem_indexedFragmentAccepting branchAutomata
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, not_or]
  exact ⟨by simp [childAccepting, childState], hNotIndexed⟩

theorem buildExclusiveOffer_branch_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).accepting ↔
      state ∈ entry.2.accepting := by
  have hNotElse : childState (index + 1) state ∉
      childAccepting 0 elseAutomaton := by
    simp [childAccepting, childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotElse, false_or]
  exact childState_mem_indexedFragmentAccepting_iff branchAutomata index
    entry hEntry state

theorem buildExclusiveOffer_branch_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).completing ↔
      state ∈ entry.2.completing := by
  have hNotHeader : childState (index + 1) state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotElse : childState (index + 1) state ∉
      childCompleting 0 elseAutomaton := by
    simp [childCompleting, childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotElse, false_or]
  exact childState_mem_indexedFragmentCompleting_iff branchAutomata index
    entry hEntry state

private theorem buildConjunctiveOffer_child0_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).accepting ↔
      state ∈ conjunction.accepting := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childAccepting, childState]

private theorem buildConjunctiveOffer_child1_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).accepting ↔
      state ∈ elseAutomaton.accepting := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childAccepting, childState]

theorem buildConjunctiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).completing ↔
      state ∈ conjunction.completing := by
  have hNotHeader : childState 0 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotElse : childState 0 state ∉ childCompleting 1 elseAutomaton := by
    simp [childCompleting, childState]
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotElse, false_or, or_false]
  simp [childCompleting, childState]

private theorem buildConjunctiveOffer_child1_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).completing ↔
      state ∈ elseAutomaton.completing := by
  have hNotHeader : childState 1 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotConjunction : childState 1 state ∉
      childCompleting 0 conjunction := by
    simp [childCompleting, childState]
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotConjunction, false_or]
  simp [childCompleting, childState]

private theorem buildConjunctiveOffer_root_not_accepting
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    (.root : TypeAutomatonState) ∉
      (buildConjunctiveOfferAutomaton signature branches elseAutomaton
        conjunction).accepting := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childAccepting, childState]

private theorem sequenceExecution_buildChoice_states_left_subset
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    child.states.image (.child 0) ⊆ parent.states := by
  classical
  dsimp only
  intro target hTarget
  rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · left
    simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
      childState, hState]
  · right
    refine ⟨childPendingEdge 0 edge, ?_, ?_⟩
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childPendingEdges, Finset.mem_image,
        Finset.mem_biUnion]
      exact Or.inl (Or.inl ⟨edge, hEdge, rfl⟩)
    · simp [childPendingEdge, childState]

private theorem sequenceExecution_buildChoice_states_right_subset
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    child.states.image (.child 1) ⊆ parent.states := by
  classical
  dsimp only
  intro target hTarget
  rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_union,
    Finset.mem_image] at hState ⊢
  rcases hState with hState | ⟨edge, hEdge, rfl⟩
  · left
    simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
      childState, hState]
  · right
    refine ⟨childPendingEdge 1 edge, ?_, ?_⟩
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childPendingEdges, Finset.mem_image,
        Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨edge, hEdge, rfl⟩)
    · simp [childPendingEdge, childState]

theorem sequenceExecution_buildChoice_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : left.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ left.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    parent.futureReachable (.child 0 state) =
      (child.futureReachable state).image (.child 0) := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton left
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed left hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_left_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 0)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding child parent
    (.child 0)
    (sequenceExecution_buildChoice_referencedStates_left signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

theorem sequenceExecution_buildChoice_futureReachable_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : right.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ right.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    parent.futureReachable (.child 1 state) =
      (child.futureReachable state).image (.child 1) := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton right
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed right hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_right_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 1)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact PendingAutomaton.futureReachable_eq_of_embedding child parent
    (.child 1)
    (sequenceExecution_buildChoice_referencedStates_right signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

theorem sequenceExecution_buildChoice_computeFuture_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : left.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ left.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton left
    computeFuture parent (.child 0 state) = computeFuture child state := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton left
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed left hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_left_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 0)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding child parent (.child 0)
    (sequenceExecution_buildChoice_referencedStates_left signature left right
      selectionLeft selectionRight)
    (sequenceExecution_buildChoice_offersAt_left signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

theorem sequenceExecution_buildChoice_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hTargets : right.FutureTargetsInStates)
    (state : TypeAutomatonState) (hState : state ∈ right.states) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    let child := sequenceExecutionAutomaton right
    computeFuture parent (.child 1 state) = computeFuture child state := by
  let parent := sequenceExecutionAutomaton
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
  let child := sequenceExecutionAutomaton right
  have hClosed : child.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed right hTargets
  have hChildState : state ∈ child.states := by
    exact Finset.mem_union_left _ hState
  have hCard : child.states.card ≤ parent.states.card := by
    have hSubset := sequenceExecution_buildChoice_states_right_subset signature
      left right selectionLeft selectionRight
    calc
      child.states.card = (child.states.image (.child 1)).card := by
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ parent.states.card := Finset.card_le_card hSubset
  exact computeFuture_eq_of_embedding child parent (.child 1)
    (sequenceExecution_buildChoice_referencedStates_right signature left right
      selectionLeft selectionRight)
    (sequenceExecution_buildChoice_offersAt_right signature left right
      selectionLeft selectionRight) hClosed state hChildState hCard

private theorem sequenceExecution_buildChoice_referencedStates_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    parent.referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, sequenceExecutionAutomaton, Finset.mem_image,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hTarget
    rcases hTarget with
      ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hFuture⟩
    rcases hExecutionEdge with ⟨raw, hRaw, hEdge⟩
    rw [← hEdge] at hSource hFuture
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hRaw
    rcases hRaw with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨edge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨edge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
      rcases hEdge with hEdge | hEdge
      · left
        rw [hEdge] at hFuture
        simpa [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          hSelectionLeft, childState] using hFuture
      · right
        rw [hEdge] at hFuture
        simpa [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          hSelectionRight, childState] using hFuture
  · intro hTarget
    rcases hTarget with rfl | rfl
    · let raw : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionLeft
          current := ∅
          future := .at (.child 0 left.initial) ∅
          target := .child 0 left.initial }
      have hRaw : raw ∈ (buildChoiceAutomaton signature left right
          selectionLeft selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion]
        right
        refine ⟨TypeEnvironment.tock, ?_, ?_⟩
        · simp [TypeAlphabet.localEnvironments]
        · simp [raw, childState]
      refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
      · exact ⟨raw, hRaw, rfl⟩
      · simp [raw, sequenceExecutionEdge,
          AutomatonConstructionLabel.semantic, hSelectionLeft]
    · let raw : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionRight
          current := ∅
          future := .at (.child 1 right.initial) ∅
          target := .child 1 right.initial }
      have hRaw : raw ∈ (buildChoiceAutomaton signature left right
          selectionLeft selectionRight).edges := by
        simp only [buildChoiceAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_biUnion]
        right
        refine ⟨TypeEnvironment.tock, ?_, ?_⟩
        · simp [TypeAlphabet.localEnvironments]
        · simp [raw, childState]
      refine ⟨sequenceExecutionEdge raw, ⟨?_, rfl⟩, ?_⟩
      · exact ⟨raw, hRaw, rfl⟩
      · simp [raw, sequenceExecutionEdge,
          AutomatonConstructionLabel.semantic, hSelectionRight]

private theorem sequenceExecution_buildChoice_offersAt_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) :
    let parent := sequenceExecutionAutomaton
      (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    parent.offersAt .root = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter, sequenceExecutionAutomaton, Finset.mem_image]
    at hAction
  rcases hAction with
    ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hOffer⟩
  rcases hExecutionEdge with ⟨raw, hRaw, hEdge⟩
  rw [← hEdge] at hSource hOffer
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at hRaw
  rcases hRaw with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨edge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hRight with ⟨edge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hSelection with ⟨environment, _, hEdge⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with hEdge | hEdge <;> rw [hEdge] at hOffer <;>
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic]
        at hOffer

theorem sequenceExecution_buildChoice_computeFuture_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    computeFuture parent .root =
      computeFuture (sequenceExecutionAutomaton left) left.initial ∪
        computeFuture (sequenceExecutionAutomaton right) right.initial := by
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hClosed : parent.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ parent.states := by
    simp [parent, parentFragment, sequenceExecutionAutomaton,
      buildChoiceAutomaton, finishAutomatonFragment]
  change computeFuture parent .root = _
  rw [computeFuture_unfold parent .root hClosed hRoot,
    sequenceExecution_buildChoice_offersAt_root signature left right
      selectionLeft selectionRight,
    sequenceExecution_buildChoice_referencedStates_root signature left right
      selectionLeft selectionRight hSelectionLeft hSelectionRight]
  simp only [Finset.empty_union, Finset.biUnion_insert,
    Finset.biUnion_singleton]
  have hLeftEmbedding :=
    sequenceExecution_buildChoice_computeFuture_left signature left right
      selectionLeft selectionRight hLeftTargets left.initial hLeftInitial
  have hRightEmbedding :=
    sequenceExecution_buildChoice_computeFuture_right signature left right
      selectionLeft selectionRight hRightTargets right.initial hRightInitial
  refine congrArg₂ (fun first second => first ∪ second)
    hLeftEmbedding ?_
  simpa using hRightEmbedding

private theorem sequenceExecution_buildChoice_futureReachable_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    parent.futureReachable .root =
      {.root} ∪
        ((sequenceExecutionAutomaton left).futureReachable
          left.initial).image (.child 0) ∪
        ((sequenceExecutionAutomaton right).futureReachable
          right.initial).image (.child 1) := by
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hClosed : parent.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ parent.states := by
    simp [parent, parentFragment, sequenceExecutionAutomaton,
      buildChoiceAutomaton, finishAutomatonFragment]
  change parent.futureReachable .root = _
  rw [parent.futureReachable_unfold .root hClosed hRoot,
    sequenceExecution_buildChoice_referencedStates_root signature left right
      selectionLeft selectionRight hSelectionLeft hSelectionRight]
  simp only [Finset.biUnion_insert, Finset.biUnion_singleton]
  have hLeftEmbedding :=
    sequenceExecution_buildChoice_futureReachable_left signature left right
      selectionLeft selectionRight hLeftTargets left.initial hLeftInitial
  have hRightEmbedding :=
    sequenceExecution_buildChoice_futureReachable_right signature left right
      selectionLeft selectionRight hRightTargets right.initial hRightInitial
  rw [hLeftEmbedding]
  have hRightSingleton :
      ({.child 1 right.initial} : Finset TypeAutomatonState).biUnion
          parent.futureReachable =
        ((sequenceExecutionAutomaton right).futureReachable
          right.initial).image (.child 1) := by
    simpa using hRightEmbedding
  rw [hRightSingleton]
  simp [Finset.union_assoc]

theorem sequenceExecution_buildChoice_markerReachable_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    MarkerReachable
        (sequenceExecutionFragment (buildChoiceAutomaton signature left right
          selectionLeft selectionRight)) name .root ↔
      MarkerReachable (sequenceExecutionFragment left) name left.initial ∨
        MarkerReachable (sequenceExecutionFragment right) name right.initial := by
  classical
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  have hReach := sequenceExecution_buildChoice_futureReachable_root signature
    left right selectionLeft selectionRight hSelectionLeft hSelectionRight
      hLeftTargets hRightTargets hLeftInitial hRightInitial
  have hRootNo : ¬ MarkerSource (sequenceExecutionFragment parentFragment)
      name .root := by
    rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
      Finset.mem_image] at hEdge
    rcases hEdge with ⟨raw, hRaw, rfl⟩
    simp only [parentFragment, buildChoiceAutomaton,
      finishAutomatonFragment, childPendingEdges, Finset.mem_union,
      Finset.mem_image, Finset.mem_biUnion] at hRaw
    rcases hRaw with (⟨childEdge, _, rfl⟩ | ⟨childEdge, _, rfl⟩) |
      ⟨environment, _, hSelection⟩
    · simp [childPendingEdge, childState] at hSource
    · simp [childPendingEdge, childState] at hSource
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hSelection
      rcases hSelection with hSelection | hSelection <;>
        rw [hSelection] at hLabel <;> simp at hLabel
  have hLeftSource : ∀ q,
      MarkerSource (sequenceExecutionFragment parentFragment) name (.child 0 q) ↔
        MarkerSource (sequenceExecutionFragment left) name q := by
    intro q
    apply markerSource_of_outgoing_childPendingEdge
    intro edge
    simpa [parentFragment, sequenceExecutionFragment] using
      (sequenceExecution_buildChoice_outgoing_left signature left right
        selectionLeft selectionRight q edge)
  have hRightSource : ∀ q,
      MarkerSource (sequenceExecutionFragment parentFragment) name (.child 1 q) ↔
        MarkerSource (sequenceExecutionFragment right) name q := by
    intro q
    apply markerSource_of_outgoing_childPendingEdge
    intro edge
    simpa [parentFragment, sequenceExecutionFragment] using
      (sequenceExecution_buildChoice_outgoing_right signature left right
        selectionLeft selectionRight q edge)
  simp only [MarkerReachable]
  change (∃ reached ∈ (sequenceExecutionAutomaton parentFragment).futureReachable
      .root, MarkerSource (sequenceExecutionFragment parentFragment) name reached) ↔ _
  constructor
  · rintro ⟨reached, hReached, hMarker⟩
    rw [hReach] at hReached
    rcases Finset.mem_union.mp hReached with hRootOrLeft | hRight
    · rcases Finset.mem_union.mp hRootOrLeft with hRoot | hLeft
      · have : reached = .root := Finset.mem_singleton.mp hRoot
        subst reached
        exact absurd hMarker hRootNo
      · rcases Finset.mem_image.mp hLeft with ⟨q, hq, hqEq⟩
        subst reached
        exact Or.inl ⟨q, hq, (hLeftSource q).mp hMarker⟩
    · rcases Finset.mem_image.mp hRight with ⟨q, hq, hqEq⟩
      subst reached
      exact Or.inr ⟨q, hq, (hRightSource q).mp hMarker⟩
  · rintro (⟨q, hq, hMarker⟩ | ⟨q, hq, hMarker⟩)
    · refine ⟨.child 0 q, ?_, (hLeftSource q).mpr hMarker⟩
      rw [hReach]
      exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <|
        Or.inr <| Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · refine ⟨.child 1 q, ?_, (hRightSource q).mpr hMarker⟩
      rw [hReach]
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨q, hq, rfl⟩

theorem buildChoiceAutomaton_completionWitness_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (reachable : Finset TypeAutomatonState) :
    let parent := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (∃ completed ∈ reachable.image (.child 0),
        completed ∈ parent.accepting ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ left.accepting ∨ completed ∈ left.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 0 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hInitial] using hCompleted

theorem buildChoiceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (reachable : Finset TypeAutomatonState) :
    let parent := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ parent.accepting ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.accepting ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hInitial] using hCompleted

theorem sequenceExecution_buildChoice_completionWitness_root_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let parentFragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent := sequenceExecutionAutomaton parentFragment
    let leftExecution := sequenceExecutionAutomaton left
    let rightExecution := sequenceExecutionAutomaton right
    ((∃ completed ∈ parent.futureReachable .root,
        completed ∈ parentFragment.accepting ∨
          completed ∈ parentFragment.completing) ↔
      (∃ completed ∈ leftExecution.futureReachable left.initial,
        completed ∈ left.accepting ∨ completed ∈ left.completing) ∨
      (∃ completed ∈ rightExecution.futureReachable right.initial,
        completed ∈ right.accepting ∨ completed ∈ right.completing)) := by
  classical
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  let leftExecution := sequenceExecutionAutomaton left
  let rightExecution := sequenceExecutionAutomaton right
  change ((∃ completed ∈ parent.futureReachable .root,
      completed ∈ parentFragment.accepting ∨
        completed ∈ parentFragment.completing) ↔ _)
  rw [sequenceExecution_buildChoice_futureReachable_root signature left right
    selectionLeft selectionRight hSelectionLeft hSelectionRight hLeftTargets
    hRightTargets hLeftInitial hRightInitial]
  have hLeftSelf : left.initial ∈ leftExecution.futureReachable left.initial :=
    leftExecution.mem_futureReachable_self left.initial
  have hRightSelf : right.initial ∈
      rightExecution.futureReachable right.initial :=
    rightExecution.mem_futureReachable_self right.initial
  constructor
  · rintro ⟨completed, hReachable, hCompleted⟩
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
      at hReachable
    rcases hReachable with (rfl | ⟨child, hChild, rfl⟩) |
        ⟨child, hChild, rfl⟩
    · have hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing := by
        by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing
        · exact hInitial
        · simp [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childAccepting,
            childState, hInitial] at hCompleted
      rcases hInitial with hLeft | hRight
      · left
        exact ⟨left.initial, hLeftSelf, Or.inr hLeft⟩
      · right
        exact ⟨right.initial, hRightSelf, Or.inr hRight⟩
    · left
      refine ⟨child, hChild, ?_⟩
      by_cases hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing <;>
        simpa [parentFragment, buildChoiceAutomaton,
          finishAutomatonFragment, childCompleting, childAccepting,
          childState, hInitial] using hCompleted
    · right
      refine ⟨child, hChild, ?_⟩
      by_cases hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing <;>
        simpa [parentFragment, buildChoiceAutomaton,
          finishAutomatonFragment, childCompleting, childAccepting,
          childState, hInitial] using hCompleted
  · rintro (hLeft | hRight)
    · rcases hLeft with ⟨child, hChild, hCompleted⟩
      refine ⟨.child 0 child, ?_, ?_⟩
      · simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        exact Or.inl (Or.inr ⟨child, hChild, rfl⟩)
      · by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing <;>
          simpa [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childAccepting,
            childState, hInitial] using hCompleted
    · rcases hRight with ⟨child, hChild, hCompleted⟩
      refine ⟨.child 1 child, ?_, ?_⟩
      · simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        exact Or.inr ⟨child, hChild, rfl⟩
      · by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing <;>
          simpa [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childAccepting,
            childState, hInitial] using hCompleted

/-- References transfer through `sequenceRedirect`: a raw reference from
`state`'s own execution-normalized edges lands wherever the redirect sends it
(itself, if kept; `right`'s entry, if the referenced state is deleted), and
the two bridge families each contribute the same `right`-entry singleton
exactly when `state` is itself accepting or completing — matching Invariant 1
(redirect touches only targets, never the fields `referencedStates` reads to
decide tock-ness) and Invariant 2 (a redirected reference is always a real
target). -/
private theorem buildSequenceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.referencedStates (.child 0 state) =
      ((sequenceExecutionAutomaton left).referencedStates state).image
          (sequenceRedirect left right) ∪
        if state ∈ left.accepting ∨ state ∈ left.completing then
          {.child 1 right.initial}
        else ∅ := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  constructor
  · rintro ⟨edge, hEdge, hFuture⟩
    rcases hEdge with hLeft | hEntry | hCompleting
    · obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ := hLeft
      simp only [sequenceLeftEdge_label] at hFuture
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [hLabel, hSpec, sequenceLeftEdge,
                AutomatonConstructionLabel.semantic, TypeLabel.silent]
                at hFuture
          | «at» referenced removed =>
              have hTarget : target = sequenceRedirect left right referenced := by
                simpa [hLabel, hSpec, sequenceLeftEdge,
                  AutomatonConstructionLabel.semantic, TypeLabel.silent]
                  using hFuture
              subst target
              left
              refine ⟨referenced, ?_, rfl⟩
              simp only [sequenceExecutionAutomaton,
                PendingAutomaton.referencedStates, Finset.mem_biUnion,
                Finset.mem_filter, Finset.mem_image]
              refine ⟨sequenceExecutionEdge childEdge,
                ⟨⟨childEdge, hChildEdge, rfl⟩, ?_⟩, ?_⟩
              · simpa using hChildSource
              · simp [sequenceExecutionEdge, hLabel, hSpec,
                  AutomatonConstructionLabel.semantic, TypeLabel.silent]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · subst label
            simp [hLabel, sequenceLeftEdge,
              AutomatonConstructionLabel.semantic] at hFuture
          · have hTarget :
                target = sequenceRedirect left right childEdge.target := by
              simpa [hLabel, sequenceLeftEdge,
                AutomatonConstructionLabel.semantic, hTock]
                using hFuture
            subst target
            left
            refine ⟨childEdge.target, ?_, rfl⟩
            simp only [sequenceExecutionAutomaton,
              PendingAutomaton.referencedStates, Finset.mem_biUnion,
              Finset.mem_filter, Finset.mem_image]
            refine ⟨sequenceExecutionEdge childEdge,
              ⟨⟨childEdge, hChildEdge, rfl⟩, ?_⟩, ?_⟩
            · simpa using hChildSource
            · simp [sequenceExecutionEdge, hLabel, hTock,
                AutomatonConstructionLabel.semantic]
      | «variable» name =>
          have hTarget :
              target = sequenceRedirect left right childEdge.target := by
            simpa [hLabel, sequenceLeftEdge,
              AutomatonConstructionLabel.semantic, TypeLabel.silent]
              using hFuture
          subst target
          left
          refine ⟨childEdge.target, ?_, rfl⟩
          simp only [sequenceExecutionAutomaton,
            PendingAutomaton.referencedStates, Finset.mem_biUnion,
            Finset.mem_filter, Finset.mem_image]
          refine ⟨sequenceExecutionEdge childEdge,
            ⟨⟨childEdge, hChildEdge, rfl⟩, ?_⟩, ?_⟩
          · simpa using hChildSource
          · simp [sequenceExecutionEdge, hLabel,
              AutomatonConstructionLabel.semantic, TypeLabel.silent]
    · obtain ⟨hState, hAccepting, environment, hEnvironment, rfl⟩ := hEntry
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      subst hState
      right
      simp [childState, hAccepting]
    · obtain ⟨hCond, rfl⟩ := hCompleting
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hCond]
  · rintro (⟨referenced, hReferenced, rfl⟩ | hCond)
    · simp only [sequenceExecutionAutomaton, PendingAutomaton.referencedStates,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hReferenced
      obtain ⟨execEdge, ⟨⟨childEdge, hChildEdge, rfl⟩, hSource⟩, hFuture⟩ :=
        hReferenced
      have hChildSource : childEdge.source = state := by simpa using hSource
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [sequenceExecutionEdge, hLabel, hSpec] at hFuture
          | «at» innerReferenced removed =>
              have hEq : referenced = innerReferenced := by
                simpa [sequenceExecutionEdge, hLabel, hSpec,
                  AutomatonConstructionLabel.semantic, TypeLabel.silent]
                  using hFuture
              subst hEq
              refine ⟨sequenceLeftEdge left right childEdge, Or.inl
                ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
              simp [sequenceLeftEdge, hLabel, hSpec,
                AutomatonConstructionLabel.semantic, TypeLabel.silent]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · exfalso
            simp [sequenceExecutionEdge, hLabel, hTock,
              AutomatonConstructionLabel.semantic] at hFuture
          · have hEq : referenced = childEdge.target := by
              simpa [sequenceExecutionEdge, hLabel, hTock,
                AutomatonConstructionLabel.semantic] using hFuture
            subst hEq
            refine ⟨sequenceLeftEdge left right childEdge, Or.inl
              ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
            simp [sequenceLeftEdge, hLabel, hTock,
              AutomatonConstructionLabel.semantic]
      | «variable» name =>
          have hEq : referenced = childEdge.target := by
            simpa [sequenceExecutionEdge, hLabel,
              AutomatonConstructionLabel.semantic, TypeLabel.silent]
              using hFuture
          subst hEq
          refine ⟨sequenceLeftEdge left right childEdge, Or.inl
            ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
          simp [sequenceLeftEdge, hLabel, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
    · by_cases hAccepting : state ∈ left.accepting
      · simp only [hAccepting, true_or, if_true, Finset.mem_singleton]
          at hCond
        subst hCond
        refine ⟨_, Or.inr (Or.inr ⟨Or.inl hAccepting, rfl⟩), ?_⟩
        simp [childState, AutomatonConstructionLabel.semantic,
          TypeLabel.silent]
      · by_cases hCompleting : state ∈ left.completing
        · simp only [hAccepting, false_or, hCompleting, if_true,
            Finset.mem_singleton] at hCond
          subst hCond
          refine ⟨_, Or.inr (Or.inr ⟨Or.inr hCompleting, rfl⟩), ?_⟩
          simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
        · simp [hAccepting, hCompleting] at hCond

/-- Redirecting a `.future` reference never changes whether the offer
computation reads it: both sides discard the target entirely in the `.at`
case, so the redirect (which only ever touches that discarded target) is
invisible to `offersAt`. -/
private theorem sequenceLeftEdge_offersAt_eq (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) (action : BareMessage) :
    action ∈ (if (sequenceLeftEdge left right edge).label.semantic =
          TypeLabel.tock then
        (∅ : Finset BareMessage)
      else
        (sequenceLeftEdge left right edge).current ∪
          match (sequenceLeftEdge left right edge).future with
          | .explicit offers => offers
          | .at _ _ => ∅) ↔
      action ∈ (if (sequenceExecutionEdge edge).label.semantic =
            TypeLabel.tock then
          (∅ : Finset BareMessage)
        else
          (sequenceExecutionEdge edge).current ∪
            match (sequenceExecutionEdge edge).future with
            | .explicit offers => offers
            | .at _ _ => ∅) := by
  cases hLabel : edge.label <;> cases hFuture : edge.future <;>
    simp [sequenceLeftEdge, sequenceExecutionEdge, hLabel, hFuture]

/-- Sequence-left tagging preserves direct offers; the two bridge families
carry empty current offers. -/
private theorem buildSequenceAutomaton_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.offersAt (.child 0 state) =
      (sequenceExecutionAutomaton left).offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hAction⟩
    rcases hEdge with hLeft | hEntry | hCompleting
    · obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ := hLeft
      refine ⟨sequenceExecutionEdge childEdge, ⟨?_, ?_⟩, ?_⟩
      · exact ⟨childEdge, hChildEdge, rfl⟩
      · simpa using hChildSource
      · exact (sequenceLeftEdge_offersAt_eq left right childEdge action).mp
          hAction
    · obtain ⟨hState, hAccepting, environment, hEnvironment, rfl⟩ := hEntry
      simp at hAction
    · obtain ⟨hCond, rfl⟩ := hCompleting
      simp at hAction
  · rintro ⟨execEdge, ⟨⟨childEdge, hChildEdge, rfl⟩, hSource⟩, hAction⟩
    have hChildSource : childEdge.source = state := by simpa using hSource
    refine ⟨sequenceLeftEdge left right childEdge, ?_, ?_⟩
    · exact Or.inl ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    · exact (sequenceLeftEdge_offersAt_eq left right childEdge action).mpr
        hAction

theorem buildSequenceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with ((hLeft | hRight) | hEntry) | hCompleting
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [sequenceLeftEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childPendingEdge, childState] using hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · simp only [sequenceEntryBridgeEdges] at hEntry
      split at hEntry
      · simp only [Finset.mem_image] at hEntry
        obtain ⟨environment, _, hEdge⟩ := hEntry
        rw [← hEdge] at hSource
        simp [childState] at hSource
      · simp at hEntry
    · simp only [sequenceCompletingBridgeEdges, Finset.mem_image]
        at hCompleting
      obtain ⟨completingState, _, hEdge⟩ := hCompleting
      rw [← hEdge] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩))
    · simp [childPendingEdge, childState, hChildSource]

theorem buildSequenceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildSequenceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

/-- The pruned-and-tagged-`.child 0` reachable set (`keep`, in
`buildSequenceAutomaton_futureReachable_left`) is always a subset of the raw
execution closure it prunes from — dropping edges sourced at a deleted
intermediate, and dropping deleted targets afterward, only ever removes
elements. Callers that still need `canBridge`'s own witness (stated over the
*unpruned* closure) use this to promote a `keep`-membership fact back up. -/
private theorem sequenceKeep_subset_leftReach
    (left : AutomatonFragment) (state : TypeAutomatonState)
    (hLeftTargets : left.FutureTargetsInStates)
    (hState : state ∈ (sequenceExecutionAutomaton left).states) :
    (({ states := (sequenceExecutionAutomaton left).states
        edges := (sequenceExecutionAutomaton left).edges.filter fun edge =>
          edge.source ∉ sequenceDeleted left ∨ edge.source = state } :
        PendingAutomaton).futureReachable state) \ sequenceDeleted left ⊆
      (sequenceExecutionAutomaton left).futureReachable state := by
  set execution := sequenceExecutionAutomaton left with hExecDef
  set prunedExecution : PendingAutomaton :=
    { states := execution.states
      edges := execution.edges.filter fun edge =>
        edge.source ∉ sequenceDeleted left ∨ edge.source = state } with
    hPrunedDef
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed left hLeftTargets
  have hReachClosed : ∀ {source target},
      source ∈ execution.futureReachable state →
        target ∈ execution.referencedStates source →
          target ∈ execution.futureReachable state := by
    intro source target hSourceReach hReference
    have hSourceState : source ∈ execution.states :=
      execution.futureReachable_subset_of_reference_closed state
        execution.states hState (fun cur hCur => hClosed cur hCur)
        hSourceReach
    exact execution.futureReachable_subset_of_mem hClosed hState hSourceReach
      (execution.referencedStates_subset_futureReachable source hClosed
        hSourceState hReference)
  have hRefSubset : ∀ c, prunedExecution.referencedStates c ⊆
      execution.referencedStates c := by
    intro c
    apply Finset.biUnion_subset_biUnion_of_subset_left
    intro edge hEdge
    simp only [Finset.mem_filter] at hEdge ⊢
    exact ⟨(Finset.filter_subset _ _) hEdge.1, hEdge.2⟩
  intro c hc
  obtain ⟨hcPruned, _⟩ := Finset.mem_sdiff.mp hc
  apply prunedExecution.futureReachable_subset_of_reference_closed state
    (execution.futureReachable state)
  · exact execution.mem_futureReachable_self state
  · intro s hs t ht
    exact hReachClosed hs (hRefSubset s ht)
  · exact hcPruned

/-- References transfer through `sequenceRedirect`, and a redirected state can
collapse several distinct left states onto `right`'s entry — so `state`'s own
tagged reachability set is not simply `leftReach` tagged with `.child 0`: a
left state reachable *only* by passing through a deleted (accepting,
non-initial) intermediate is never actually visited in the merged graph,
since every edge landing on a deleted state is redirected away before it
manifests as a `.child 0`-tagged target. `keep` computes reachability with
that pruning already applied (edges sourced at a deleted, non-`state`
intermediate are dropped first), then discards any deleted state still
picked up as a plain *target*. `hNotDeleted` rules out the one remaining
edge case (the seed itself being deleted), which needs the entry bridge
rather than this closure argument — see `sequenceEntryBridgeEdges`. -/
theorem buildSequenceAutomaton_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hNotDeleted : state ∉ sequenceDeleted left)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let prunedExecution : PendingAutomaton :=
      { states := execution.states
        edges := execution.edges.filter fun edge =>
          edge.source ∉ sequenceDeleted left ∨ edge.source = state }
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let keep := prunedExecution.futureReachable state \ sequenceDeleted left
    let canBridge := ∃ completed ∈ execution.futureReachable state,
      completed ∈ left.accepting ∨ completed ∈ left.completing
    parent.futureReachable (.child 0 state) =
      keep.image (.child 0) ∪
        if canBridge then
          (rightPending.futureReachable right.initial).image (.child 1)
        else ∅ := by
  -- TODO(unfinished): the statement above is the corrected one (see the
  -- doc comment) — `leftReach.image (.child 0)` is provably false in
  -- general (counterexample: `left = .choice .skip .skip`, where both
  -- branches' entries are simultaneously same-cycle-referenced from
  -- `left.initial` and both collapse onto the same redirected bridge
  -- target, so tagging each with `.child 0` separately overclaims). This
  -- `keep`-based statement is correct, but completing the proof needs a
  -- lemma not yet in `PendingAutomatonFuture.lean`: every non-seed member
  -- of a `futureReachable` closure has an immediate predecessor *within*
  -- that same closure (used here to show the first deleted state hit along
  -- any path has a `keep`-membership predecessor, hence the bridge fires
  -- from something already known reachable).
  sorry

theorem buildSequenceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (reachable : Finset TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ sequence.accepting ∨ completed ∈ sequence.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.accepting ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hRight] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childAccepting,
        childCompleting, childState, hRight] using hCompleted

theorem buildSequenceAutomaton_completionWitness_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hNotDeleted : state ∉ sequenceDeleted left)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let leftExecution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := leftExecution.futureReachable state
    let rightReach := rightPending.futureReachable right.initial
    let canBridge := ∃ completed ∈ leftReach,
      completed ∈ left.accepting ∨ completed ∈ left.completing
    let rightCanComplete := ∃ completed ∈ rightReach,
      completed ∈ right.accepting ∨ completed ∈ right.completing
    ((∃ completed ∈ parent.futureReachable (.child 0 state),
        completed ∈ sequence.accepting ∨ completed ∈ sequence.completing) ↔
      canBridge ∧ rightCanComplete) := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let leftExecution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := leftExecution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ left.accepting ∨ completed ∈ left.completing
  let rightCanComplete := ∃ completed ∈ rightReach,
    completed ∈ right.accepting ∨ completed ∈ right.completing
  change ((∃ completed ∈ parent.futureReachable (.child 0 state),
      completed ∈ sequence.accepting ∨ completed ∈ sequence.completing) ↔
    canBridge ∧ rightCanComplete)
  rw [buildSequenceAutomaton_futureReachable_left signature left right state
    hLeftState hNotDeleted hLeftTargets hRightTargets hRightInitial]
  have hRightSelf : right.initial ∈ rightReach := by
    exact rightPending.mem_futureReachable_self right.initial
  have hExecutionState : state ∈ leftExecution.states := by
    simp [leftExecution, sequenceExecutionAutomaton, hLeftState]
  constructor
  · rintro ⟨completed, hReachable, hCompleted⟩
    by_cases hBridge : canBridge
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.accepting ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_true, Finset.mem_union,
        Finset.mem_image]
        at hReachable
      constructor
      · exact hBridge
      · rcases hReachable with ⟨child, hChild, hTagged⟩ |
            ⟨child, hChild, hTagged⟩
        · rw [← hTagged] at hCompleted
          have hFields : child ∈ left.completing ∧
              right.initial ∈ right.completing := by
            by_cases hRight : right.initial ∈ right.completing
            · simpa [sequence, buildSequenceAutomaton,
                finishAutomatonFragment, childAccepting, childCompleting,
                childState, hRight] using hCompleted
            · simp [sequence, buildSequenceAutomaton,
                finishAutomatonFragment, childAccepting, childCompleting,
                childState, hRight] at hCompleted
          exact ⟨right.initial, hRightSelf, Or.inr hFields.2⟩
        · rw [← hTagged] at hCompleted
          refine ⟨child, hChild, ?_⟩
          by_cases hRight : right.initial ∈ right.completing <;>
            simpa [sequence, buildSequenceAutomaton,
              finishAutomatonFragment, childAccepting, childCompleting,
              childState, hRight] using hCompleted
    · have hBridgeExpanded : ¬ ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.accepting ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_false, Finset.union_empty,
        Finset.mem_image]
        at hReachable
      rcases hReachable with ⟨child, hChild, hTagged⟩
      rw [← hTagged] at hCompleted
      have hLeftComplete : child ∈ left.completing := by
        by_cases hRight : right.initial ∈ right.completing
        · simpa [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childAccepting, childCompleting,
            childState, hRight] using hCompleted
        · simp [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childAccepting, childCompleting,
            childState, hRight] at hCompleted
      have hChildLeftReach : child ∈ leftReach :=
        sequenceKeep_subset_leftReach left state hLeftTargets hExecutionState
          hChild
      exact (hBridge ⟨child, hChildLeftReach, Or.inr hLeftComplete⟩).elim
  · rintro ⟨hBridge, child, hChild, hCompleted⟩
    refine ⟨.child 1 child, ?_, ?_⟩
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.accepting ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_true, Finset.mem_union,
        Finset.mem_image]
      exact Or.inr ⟨child, hChild, rfl⟩
    · by_cases hRight : right.initial ∈ right.completing <;>
        simpa [sequence, buildSequenceAutomaton,
          finishAutomatonFragment, childAccepting, childCompleting,
          childState, hRight] using hCompleted

/-- Future offers at a tagged sequence-left state are the offers of the
child's non-clock execution closure, together with the right-entry menu
exactly when that closure can cross either sequence bridge. -/
theorem buildSequenceAutomaton_computeFuture_left_formula
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hNotDeleted : state ∉ sequenceDeleted left)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := execution.futureReachable state
    let canBridge := ∃ completed ∈ leftReach,
      completed ∈ left.accepting ∨ completed ∈ left.completing
    computeFuture parent (.child 0 state) =
      computeFuture execution state ∪
        if canBridge then computeFuture rightPending right.initial else ∅ := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let execution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := execution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach,
    completed ∈ left.accepting ∨ completed ∈ left.completing
  change computeFuture parent (childState 0 state) =
    computeFuture execution state ∪
      if canBridge then computeFuture rightPending right.initial else ∅
  -- TODO(unfinished): `buildSequenceAutomaton_futureReachable_left` now
  -- gives its `.child 0`-tagged part as `keep`, not `leftReach`, matching
  -- the corrected reachability set. Restating `hReach'` in terms of
  -- `leftReach` (as below) needs "every accepting/deleted state's own
  -- `offersAt` is empty" to bridge `keep.biUnion execution.offersAt` back up
  -- to `leftReach.biUnion execution.offersAt` — plausible (accepting states
  -- represent a literal `skip` residual, whose own edges always carry empty
  -- `current`/`future`), but not yet proven for every constructor (`.par`'s
  -- synchronized product is the one case not checked).
  have hReach' : parent.futureReachable (childState 0 state) =
      leftReach.image (childState 0) ∪
        if canBridge then rightReach.image (childState 1) else ∅ := by
    sorry
  have hLeftOffers : ∀ child,
      parent.offersAt (childState 0 child) = execution.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_left signature left right child
  have hRightOffers : ∀ child,
      parent.offersAt (childState 1 child) = rightPending.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_right signature left right child
  unfold computeFuture
  change (parent.futureReachable (childState 0 state)).biUnion
      parent.offersAt =
        leftReach.biUnion execution.offersAt ∪
          if canBridge then rightReach.biUnion rightPending.offersAt else ∅
  rw [hReach']
  by_cases hCanBridge : canBridge
  · simp only [hCanBridge, if_true]
    have hBiUnion :
        (leftReach.image (childState 0) ∪
            rightReach.image (childState 1)).biUnion parent.offersAt =
          (leftReach.image (childState 0)).biUnion parent.offersAt ∪
            (rightReach.image (childState 1)).biUnion parent.offersAt := by
      ext action
      simp only [Finset.mem_biUnion, Finset.mem_union]
      constructor
      · rintro ⟨source, hSource, hOffer⟩
        rcases hSource with hLeftSource | hRightSource
        · exact Or.inl ⟨source, hLeftSource, hOffer⟩
        · exact Or.inr ⟨source, hRightSource, hOffer⟩
      · rintro (⟨source, hSource, hOffer⟩ |
          ⟨source, hSource, hOffer⟩)
        · exact ⟨source, Or.inl hSource, hOffer⟩
        · exact ⟨source, Or.inr hSource, hOffer⟩
    rw [hBiUnion]
    rw [PendingAutomaton.biUnion_offersAt_image_of_embedding execution parent
        (childState 0) hLeftOffers leftReach,
      PendingAutomaton.biUnion_offersAt_image_of_embedding rightPending parent
        (childState 1) hRightOffers rightReach]
  · simp only [hCanBridge, if_false, Finset.union_empty,
      Finset.biUnion_empty]
    exact PendingAutomaton.biUnion_offersAt_image_of_embedding execution
      parent (childState 0) hLeftOffers leftReach

theorem buildSequenceAutomaton_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildSequenceAutomaton signature left right).states.card) :
    computeFuture
        { states := (buildSequenceAutomaton signature left right).states
          edges := (buildSequenceAutomaton signature left right).edges }
        (.child 1 state) =
      computeFuture { states := right.states, edges := right.edges } state := by
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let child : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  apply computeFuture_eq_of_embedding child parent (.child 1)
  · exact buildSequenceAutomaton_referencedStates_right signature left right
  · exact buildSequenceAutomaton_offersAt_right signature left right
  · exact hClosed
  · exact hState
  · exact hCard

/-- A syntactically completing left state exposes the entire right-entry menu
through its construction-only future bridge.  This is the crucial lower-bound
half of optimistic sequence future correctness; it does not create a public
transition. -/
theorem buildSequenceAutomaton_rightFuture_subset_of_completing
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hCompleting : state ∈ left.completing)
    (hLeftState : state ∈ left.states)
    (hNotDeleted : state ∉ sequenceDeleted left)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    computeFuture { states := right.states, edges := right.edges } right.initial ⊆
      computeFuture
        { states := (buildSequenceAutomaton signature left right).states
          edges := (buildSequenceAutomaton signature left right).edges }
        (.child 0 state) := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  have hClosed : parent.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates sequence
    exact buildSequenceAutomaton_futureTargetsInStates signature left right
      hLeftTargets hRightTargets hRightInitial
  have hSource : childState 0 state ∈ parent.states := by
    simp only [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
    left; left
    exact ⟨state, ⟨hLeftState, hNotDeleted⟩, rfl⟩
  have hRightCard : right.states.card ≤ sequence.states.card := by
    have hSubset : childStates 1 right ⊆ sequence.states := by
      intro child hChild
      simp only [sequence, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      exact Or.inr hChild
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ sequence.states.card := Finset.card_le_card hSubset
  have hRightEmbedding := buildSequenceAutomaton_computeFuture_right signature
    left right right.initial
    (PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets)
    hRightInitial hRightCard
  have hReference : childState 1 right.initial ∈
      parent.referencedStates (childState 0 state) := by
    let bridge : PendingAutomatonEdge :=
      { source := childState 0 state
        environment := .empty
        label := .future
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨bridge, ⟨?_, rfl⟩, ?_⟩
    · simp only [bridge, parent, sequence, buildSequenceAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        sequenceCompletingBridgeEdges]
      right
      exact ⟨state, Or.inr hCompleting, rfl⟩
    · simp [bridge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  change computeFuture rightPending right.initial ⊆
    computeFuture parent (childState 0 state)
  rw [computeFuture_unfold parent (childState 0 state) hClosed hSource]
  intro action hAction
  simp only [Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨childState 1 right.initial, hReference, ?_⟩
  have hRightEmbedding' :
      computeFuture parent (childState 1 right.initial) =
        computeFuture rightPending right.initial := by
    simpa [parent, sequence, rightPending] using hRightEmbedding
  rw [hRightEmbedding']
  exact hAction

end

end Pact
