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

theorem buildSequenceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 0 state ↔
      (∃ childEdge ∈ left.edges,
        childEdge.source = state ∧
        edge =
          { source := childState 0 childEdge.source
            environment := childEdge.environment
            label := childEdge.label
            current := childEdge.current
            future := match childEdge.label with
              | .future => childFutureSpec 0 childEdge.future
              | _ => .at (childState 0 childEdge.target) childEdge.current
            target := childState 0 childEdge.target }) ∨
      (state ∈ left.skipping ∧
        ∃ environment ∈ signature.localEnvironments,
          edge =
            { source := childState 0 state
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 1 right.initial) ∅
              target := childState 1 right.initial }) ∨
      (state ∈ left.completing ∧
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
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childState] using hChildSource
      left
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hBridge with ⟨bridgeState, hSkipping, environment,
        hEnvironment, hEdge⟩
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : bridgeState = state := by
        simpa [childState] using hBridgeSource
      subst bridgeState
      right
      left
      exact ⟨hSkipping, environment, hEnvironment, hEdge.symm⟩
    · rcases hFutureBridge with ⟨bridgeState, hCompleting, hEdge⟩
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : bridgeState = state := by
        simpa [childState] using hBridgeSource
      subst bridgeState
      right
      right
      exact ⟨hCompleting, hEdge.symm⟩
  · rintro (hLeft | hBridge | hFutureBridge)
    · rcases hLeft with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩))
      · simp [childState, hChildSource]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        left
        right
        exact ⟨state, hSkipping, environment, hEnvironment, rfl⟩
      · rfl
    · rcases hFutureBridge with ⟨hCompleting, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        right
        exact ⟨state, hCompleting, rfl⟩
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
    skipping := child.skipping
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

theorem sequenceExecution_buildSequence_edges
    (signature : TypeAlphabet) (left right : AutomatonFragment) :
    (sequenceExecutionAutomaton
        (buildSequenceAutomaton signature left right)).edges =
      (buildSequenceAutomaton signature left
        (sequenceExecutionFragment right)).edges := by
  classical
  ext edge
  simp [sequenceExecutionAutomaton, sequenceExecutionFragment,
    buildSequenceAutomaton, finishAutomatonFragment, childPendingEdges,
    childPendingEdge, childFutureSpec, childStates, childState,
    sequenceExecutionEdge, Finset.image_union, Function.comp_def]
  grind

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

/-- At a product state, the execution view already sees the whole optimistic
menu directly through the two construction-only observation edges.  Ordinary
product transitions add only offers that are contained in those observations. -/
theorem sequenceExecution_buildParallel_offersAt
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates) :
    (sequenceExecutionAutomaton
        (buildParallelAutomaton interface left right)).offersAt
        (.pair leftState rightState) =
      hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState ∪
          computeFuture { states := right.states, edges := right.edges }
            rightState) := by
  classical
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  have hLeftClosed : leftPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hOffer⟩
    simp only [sequenceExecutionAutomaton, Finset.mem_image] at hExecutionEdge
    rcases hExecutionEdge with ⟨edge, hEdge, rfl⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with
        ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge,
          ⟨⟨hRightEdge, _⟩, hSync⟩, rfl⟩
      injection hSource with hLeftSource hRightSource
      subst leftState
      subst rightState
      by_cases hClock :
          (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock
      · simp [sequenceExecutionEdge, hClock] at hOffer
      · have hCombinedNotFuture :
            AutomatonConstructionLabel.combine interface leftEdge.label
                rightEdge.label ≠ .future := by
          cases hLeftLabel : leftEdge.label <;>
            cases hRightLabel : rightEdge.label <;>
              simp_all [AutomatonConstructionLabel.combine]
        have hOfferCurrent : action ∈
            hideOffers interface (leftEdge.current ∪ rightEdge.current) := by
          simpa [sequenceExecutionEdge, hClock, hCombinedNotFuture] using hOffer
        rcases hSync with
          ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
        have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
            rightEdge.label.semantic := hWitnesses.2.2.2
        have hNonClock :=
          AutomatonConstructionLabel.component_nonclock_of_sync interface
            leftEdge.label rightEdge.label hLabelSync hClock
        have hLeftSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture left leftEdge
            hLeftEdge hLeftClosed hLeftState hNonClock.1
        have hRightSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture right rightEdge
            hRightEdge hRightClosed hRightState hNonClock.2
        simp only [hideOffers, Finset.mem_filter, Finset.mem_union]
          at hOfferCurrent ⊢
        rcases hOfferCurrent with ⟨hCurrent, hOutside⟩
        rcases hCurrent with hLeft | hRight
        · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_left _ hLeft)),
            hOutside⟩
        · exact ⟨Or.inr (hRightSubset (Finset.mem_union_left _ hRight)),
            hOutside⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent, hideOffers] at hOffer
        simpa [hideOffers, leftPending, rightPending] using
          (show (action ∈ computeFuture leftPending leftState ∨
              action ∈ computeFuture rightPending rightState) ∧
                action.1 ∉ interface from ⟨Or.inl hOffer.1, hOffer.2⟩)
      · rcases hRight with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent, hideOffers] at hOffer
        simpa [hideOffers, leftPending, rightPending] using
          (show (action ∈ computeFuture leftPending leftState ∨
              action ∈ computeFuture rightPending rightState) ∧
                action.1 ∉ interface from ⟨Or.inr hOffer.1, hOffer.2⟩)
  · intro action hAction
    simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hAction
    rcases hAction with ⟨hLeft | hRight, hOutside⟩
    · simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let observation : PendingAutomatonEdge :=
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface
            (computeFuture leftPending leftState)
          future := .explicit ∅
          target := .pair leftState rightState }
      refine ⟨sequenceExecutionEdge observation, ⟨?_, rfl⟩, ?_⟩
      · simp only [sequenceExecutionAutomaton, Finset.mem_image]
        refine ⟨observation, ?_, rfl⟩
        simp only [buildParallelAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter]
        exact Or.inr (Or.inl
          ⟨leftState, hLeftState, rightState, hRightState, by
            simp [observation, leftPending]⟩)
      · simp [sequenceExecutionEdge, observation,
          AutomatonConstructionLabel.semantic, TypeLabel.silent, hideOffers,
          leftPending, hLeft, hOutside]
    · simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let observation : PendingAutomatonEdge :=
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface
            (computeFuture rightPending rightState)
          future := .explicit ∅
          target := .pair leftState rightState }
      refine ⟨sequenceExecutionEdge observation, ⟨?_, rfl⟩, ?_⟩
      · simp only [sequenceExecutionAutomaton, Finset.mem_image]
        refine ⟨observation, ?_, rfl⟩
        simp only [buildParallelAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter]
        exact Or.inr (Or.inr
          ⟨leftState, hLeftState, rightState, hRightState, by
            simp [observation, rightPending]⟩)
      · simp [sequenceExecutionEdge, observation,
          AutomatonConstructionLabel.semantic, TypeLabel.silent, hideOffers,
          rightPending, hRight, hOutside]

/-- Every symbolic reference introduced by the execution view of a product is
the pair of targets of two non-clock resolved component edges.  The optimistic
`.future` observations remain explicit and therefore introduce no reference. -/
theorem sequenceExecution_buildParallel_reference_cases
    (interface : Interface) (left right : AutomatonFragment)
    (leftSource rightSource target : TypeAutomatonState)
    (hReference : target ∈
      (sequenceExecutionAutomaton
        (buildParallelAutomaton interface left right)).referencedStates
          (.pair leftSource rightSource)) :
    ∃ leftEdge ∈ resolvedAutomatonEdges left,
      ∃ rightEdge ∈ resolvedAutomatonEdges right,
        leftEdge.source = leftSource ∧
        rightEdge.source = rightSource ∧
        target = .pair leftEdge.target rightEdge.target ∧
        leftEdge.label ≠ .future ∧
        rightEdge.label ≠ .future ∧
        leftEdge.label.semantic ≠ TypeLabel.tock ∧
        rightEdge.label.semantic ≠ TypeLabel.tock := by
  classical
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hReference
  rcases hReference with
    ⟨executionEdge, ⟨hExecutionEdge, hSource⟩, hFuture⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hExecutionEdge
  rcases hExecutionEdge with ⟨edge, hEdge, rfl⟩
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with hTransition | hObservation
  · rcases hTransition with
      ⟨leftEdge, ⟨hLeftEdge, hLeftSemantic⟩, rightEdge,
        ⟨⟨hRightEdge, hRightSemantic⟩, hSync⟩, rfl⟩
    injection hSource with hLeftSource hRightSource
    have hCombinedNotFuture :
        AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label ≠ .future := by
      cases hLeftLabel : leftEdge.label <;>
        cases hRightLabel : rightEdge.label <;>
          simp_all [AutomatonConstructionLabel.combine]
    have hCombinedNonClock :
        (AutomatonConstructionLabel.combine interface leftEdge.label
          rightEdge.label).semantic ≠ TypeLabel.tock := by
      intro hClock
      simp [sequenceExecutionEdge, hCombinedNotFuture, hClock] at hFuture
    have hTarget : target = .pair leftEdge.target rightEdge.target := by
      simpa [sequenceExecutionEdge, hCombinedNotFuture, hCombinedNonClock]
        using hFuture
    rcases hSync with
      ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
    have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
        rightEdge.label.semantic := hWitnesses.2.2.2
    have hNonClock :=
      AutomatonConstructionLabel.component_nonclock_of_sync interface
        leftEdge.label rightEdge.label hLabelSync hCombinedNonClock
    exact ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hLeftSource,
      hRightSource, hTarget, hLeftSemantic, hRightSemantic, hNonClock⟩
  · rcases hObservation with hLeft | hRight
    · rcases hLeft with ⟨leftState, _, rightState, _, rfl⟩
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hFuture
    · rcases hRight with ⟨leftState, _, rightState, _, rfl⟩
      simp [sequenceExecutionEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hFuture

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

theorem hasResolvedEdge_of_mem_visible_resolved
    (fragment : AutomatonFragment) (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (label : TypeLabel) (hLabel : edge.label = .visible label) :
    fragment.HasResolvedEdge edge.source edge.environment label
      { current := edge.current, future := edge.future } edge.target := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, hResolved⟩
  subst edge
  refine ⟨raw, hRaw, rfl, rfl, ?_, rfl, ?_, rfl⟩
  · simpa using hLabel
  · cases hFuture : raw.future <;> simp [hFuture]

/- A constructor-independent execution-view embedding for a tagged child.
Offer constructors have an unbounded number of children, so keeping this
lemma generic avoids reproducing the binary-choice closure proof for every
indexed branch. -/
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
    (hSkipping : ∀ state,
      childState index state ∈ parent.skipping ↔ state ∈ child.skipping)
    (hCompleting : ∀ state,
      childState index state ∈ parent.completing ↔
        state ∈ child.completing) :
    (∃ completed ∈ reached.image (childState index),
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reached,
        completed ∈ child.skipping ∨ completed ∈ child.completing := by
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with ⟨completed, hReached, rfl⟩
    exact ⟨completed, hReached,
      hCompleted.imp (hSkipping completed).mp (hCompleting completed).mp⟩
  · rintro ⟨completed, hReached, hCompleted⟩
    exact ⟨childState index completed,
      Finset.mem_image.mpr ⟨completed, hReached, rfl⟩,
      hCompleted.imp (hSkipping completed).mpr (hCompleting completed).mpr⟩

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

theorem buildExclusiveOffer_child0_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).skipping ↔
      state ∈ elseAutomaton.skipping := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentSkipping
    branchAutomata state
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childSkipping 0 elseAutomaton ↔
      state ∈ elseAutomaton.skipping := by
    simp [childSkipping, childState]
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

theorem buildExclusiveOffer_root_not_skipping
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    (.root : TypeAutomatonState) ∉
      (buildExclusiveOfferAutomaton signature branches elseAutomaton
        branchAutomata).skipping := by
  have hNotIndexed := root_not_mem_indexedFragmentSkipping branchAutomata
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, not_or]
  exact ⟨by simp [childSkipping, childState], hNotIndexed⟩

theorem buildExclusiveOffer_branch_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildExclusiveOfferAutomaton signature branches elseAutomaton
          branchAutomata).skipping ↔
      state ∈ entry.2.skipping := by
  have hNotElse : childState (index + 1) state ∉
      childSkipping 0 elseAutomaton := by
    simp [childSkipping, childState]
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotElse, false_or]
  exact childState_mem_indexedFragmentSkipping_iff branchAutomata index
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

private theorem buildConjunctiveOffer_child0_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).skipping ↔
      state ∈ conjunction.skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

private theorem buildConjunctiveOffer_child1_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildConjunctiveOfferAutomaton signature branches elseAutomaton
          conjunction).skipping ↔
      state ∈ elseAutomaton.skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

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

private theorem buildConjunctiveOffer_root_not_skipping
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    (.root : TypeAutomatonState) ∉
      (buildConjunctiveOfferAutomaton signature branches elseAutomaton
        conjunction).skipping := by
  simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    childSkipping, childState]

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
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ left.skipping ∨ completed ∈ left.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 0 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted

theorem buildChoiceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (reachable : Finset TypeAutomatonState) :
    let parent := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ parent.skipping ∨ completed ∈ parent.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.skipping ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hInitial] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hInitial : left.initial ∈ left.completing ∨
        right.initial ∈ right.completing <;>
      simpa [buildChoiceAutomaton, finishAutomatonFragment, childSkipping,
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
        completed ∈ parentFragment.skipping ∨
          completed ∈ parentFragment.completing) ↔
      (∃ completed ∈ leftExecution.futureReachable left.initial,
        completed ∈ left.skipping ∨ completed ∈ left.completing) ∨
      (∃ completed ∈ rightExecution.futureReachable right.initial,
        completed ∈ right.skipping ∨ completed ∈ right.completing)) := by
  classical
  let parentFragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent := sequenceExecutionAutomaton parentFragment
  let leftExecution := sequenceExecutionAutomaton left
  let rightExecution := sequenceExecutionAutomaton right
  change ((∃ completed ∈ parent.futureReachable .root,
      completed ∈ parentFragment.skipping ∨
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
            finishAutomatonFragment, childCompleting, childSkipping,
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
          finishAutomatonFragment, childCompleting, childSkipping,
          childState, hInitial] using hCompleted
    · right
      refine ⟨child, hChild, ?_⟩
      by_cases hInitial : left.initial ∈ left.completing ∨
          right.initial ∈ right.completing <;>
        simpa [parentFragment, buildChoiceAutomaton,
          finishAutomatonFragment, childCompleting, childSkipping,
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
            finishAutomatonFragment, childCompleting, childSkipping,
            childState, hInitial] using hCompleted
    · rcases hRight with ⟨child, hChild, hCompleted⟩
      refine ⟨.child 1 child, ?_, ?_⟩
      · simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_image]
        exact Or.inr ⟨child, hChild, rfl⟩
      · by_cases hInitial : left.initial ∈ left.completing ∨
            right.initial ∈ right.completing <;>
          simpa [parentFragment, buildChoiceAutomaton,
            finishAutomatonFragment, childCompleting, childSkipping,
            childState, hInitial] using hCompleted

/-- Immediate same-cycle references from a tagged sequence-left state are the
tagged execution-child references, plus the right entry exactly when the
state is skipping or optimistically completing. -/
private theorem buildSequenceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.referencedStates (.child 0 state) =
      ((sequenceExecutionAutomaton left).referencedStates state).image
          (.child 0) ∪
        if state ∈ left.skipping ∨ state ∈ left.completing then
          {.child 1 right.initial}
        else ∅ := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hFuture⟩
    rcases hEdge with hLeft | hBridge | hFutureBridge
    · rcases hLeft with
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [hLabel, hSpec, childFutureSpec,
                AutomatonConstructionLabel.semantic, TypeLabel.silent]
                at hFuture
          | «at» referenced removed =>
              have hTarget : target = childState 0 referenced := by
                simpa [hLabel, hSpec, childFutureSpec,
                  AutomatonConstructionLabel.semantic, TypeLabel.silent]
                  using hFuture
              subst target
              left
              refine ⟨referenced, ?_, rfl⟩
              refine ⟨
                { source := childEdge.source
                  environment := childEdge.environment
                  label := childEdge.label
                  current := childEdge.current
                  future := match childEdge.label with
                    | .future => childEdge.future
                    | _ => .at childEdge.target childEdge.current
                  target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
              · exact ⟨childEdge, hChildEdge, rfl⟩
              · simpa using hChildSource
              · simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · subst label
            simp [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic] at hFuture
          · have hTarget : target = childState 0 childEdge.target := by
              simpa [hLabel, childFutureSpec,
                AutomatonConstructionLabel.semantic, hTock]
                using hFuture
            subst target
            left
            refine ⟨childEdge.target, ?_, rfl⟩
            refine ⟨
              { source := childEdge.source
                environment := childEdge.environment
                label := childEdge.label
                current := childEdge.current
                future := match childEdge.label with
                  | .future => childEdge.future
                  | _ => .at childEdge.target childEdge.current
                target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
            · exact ⟨childEdge, hChildEdge, rfl⟩
            · simpa using hChildSource
            · simp [hLabel, AutomatonConstructionLabel.semantic, hTock]
      | «variable» name =>
          have hTarget : target = childState 0 childEdge.target := by
            simpa [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic, TypeLabel.silent]
              using hFuture
          subst target
          left
          refine ⟨childEdge.target, ?_, rfl⟩
          refine ⟨
            { source := childEdge.source
              environment := childEdge.environment
              label := childEdge.label
              current := childEdge.current
              future := match childEdge.label with
                | .future => childEdge.future
                | _ => .at childEdge.target childEdge.current
              target := childEdge.target }, ⟨?_, ?_⟩, ?_⟩
          · exact ⟨childEdge, hChildEdge, rfl⟩
          · simpa using hChildSource
          · simp [hLabel, AutomatonConstructionLabel.semantic,
              TypeLabel.silent]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hSkipping]
    · rcases hFutureBridge with ⟨hCompleting, rfl⟩
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hCompleting]
  · intro hTarget
    rcases hTarget with hLeft | hBridge
    · rcases hLeft with ⟨childTarget, hChildTarget, rfl⟩
      rcases hChildTarget with ⟨edge, ⟨hEdge, hSource⟩, hFuture⟩
      rcases hEdge with ⟨childEdge, hChildEdge, hEdge⟩
      rw [← hEdge] at hSource hFuture
      have hChildSource : childEdge.source = state := by simpa using hSource
      cases hLabel : childEdge.label with
      | future =>
          cases hSpec : childEdge.future with
          | explicit offers =>
              simp [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                TypeLabel.silent] at hFuture
          | «at» referenced removed =>
              have hChildTarget : childTarget = referenced := by
                simpa [hLabel, hSpec, AutomatonConstructionLabel.semantic,
                  TypeLabel.silent] using hFuture
              subst childTarget
              refine ⟨_, Or.inl
                ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
              simp [hLabel, hSpec, childFutureSpec,
                AutomatonConstructionLabel.semantic, TypeLabel.silent,
                childState]
      | visible label =>
          by_cases hTock : label = TypeLabel.tock
          · subst label
            simp [hLabel, AutomatonConstructionLabel.semantic] at hFuture
          · have hChildTarget : childTarget = childEdge.target := by
              simpa [hLabel, AutomatonConstructionLabel.semantic, hTock]
                using hFuture
            subst childTarget
            refine ⟨_, Or.inl
              ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
            simp [hLabel, childFutureSpec,
              AutomatonConstructionLabel.semantic, hTock, childState]
      | «variable» name =>
          have hChildTarget : childTarget = childEdge.target := by
            simpa [hLabel, AutomatonConstructionLabel.semantic,
              TypeLabel.silent] using hFuture
          subst childTarget
          refine ⟨_, Or.inl
            ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
          simp [hLabel, childFutureSpec,
            AutomatonConstructionLabel.semantic, TypeLabel.silent,
            childState]
    · by_cases hSkipping : state ∈ left.skipping
      · simp only [hSkipping, true_or, if_true, Finset.mem_singleton]
          at hBridge
        subst target
        let environment := TypeEnvironment.tock
        refine ⟨_, Or.inr (Or.inl
          ⟨hSkipping, environment, ?_, rfl⟩), ?_⟩
        · simp [environment, TypeAlphabet.localEnvironments]
        · simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
      · by_cases hCompleting : state ∈ left.completing
        · simp only [hSkipping, false_or, hCompleting, if_true,
            Finset.mem_singleton] at hBridge
          subst target
          refine ⟨_, Or.inr (Or.inr ⟨hCompleting, rfl⟩), ?_⟩
          simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
        · simp [hSkipping, hCompleting] at hBridge

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
  simp [childFutureSpec, childState]
  grind

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
    rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childPendingEdge, childState] using hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hBridge with ⟨bridgeState, _, environment, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
    · rcases hFutureBridge with ⟨bridgeState, _, hEdge⟩
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

/-- Exact same-cycle reachability from a tagged sequence-left state.  The
left execution closure is always present.  The right closure is present
exactly when that closure reaches either a literal-skip state or a state marked
as optimistically completing by the child compiler. -/
theorem buildSequenceAutomaton_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
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
      completed ∈ left.skipping ∨ completed ∈ left.completing
    parent.futureReachable (.child 0 state) =
      leftReach.image (.child 0) ∪
        if canBridge then
          (rightPending.futureReachable right.initial).image (.child 1)
        else ∅ := by
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
    completed ∈ left.skipping ∨ completed ∈ left.completing
  change parent.futureReachable (childState 0 state) =
    leftReach.image (childState 0) ∪
      if canBridge then rightReach.image (childState 1) else ∅
  have hExecutionClosed : execution.ReferencesClosed := by
    exact sequenceExecutionAutomaton_referencesClosed left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed := by
    exact PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  have hParentClosed : parent.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates sequence
    exact buildSequenceAutomaton_futureTargetsInStates signature left right
      hLeftTargets hRightTargets hRightInitial
  have hExecutionState : state ∈ execution.states := by
    simp [execution, sequenceExecutionAutomaton, hLeftState]
  have hParentLeftState : childState 0 state ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hLeftState]
  have hParentRightState : childState 1 right.initial ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hRightInitial]
  have hLeftReferences : ∀ child,
      parent.referencedStates (childState 0 child) =
        (execution.referencedStates child).image (childState 0) ∪
          if child ∈ left.skipping ∨ child ∈ left.completing then
            {childState 1 right.initial}
          else ∅ := by
    intro child
    exact buildSequenceAutomaton_referencedStates_left signature left right
      child
  have hRightReferences : ∀ child,
      parent.referencedStates (childState 1 child) =
        (rightPending.referencedStates child).image (childState 1) := by
    intro child
    exact buildSequenceAutomaton_referencedStates_right signature left right
      child
  have hExecutionReachClosed : ∀ {source target},
      source ∈ leftReach → target ∈ execution.referencedStates source →
        target ∈ leftReach := by
    intro source target hSourceReach hReference
    have hSourceState : source ∈ execution.states :=
      (execution.futureReachable_subset_of_reference_closed state
        execution.states hExecutionState
        (fun current hCurrent => hExecutionClosed current hCurrent))
        hSourceReach
    have hTargetFromSource :=
      execution.referencedStates_subset_futureReachable source
        hExecutionClosed hSourceState hReference
    exact (execution.futureReachable_subset_of_mem hExecutionClosed
      hExecutionState hSourceReach) hTargetFromSource
  have hRightReachClosed : ∀ {source target},
      source ∈ rightReach → target ∈ rightPending.referencedStates source →
        target ∈ rightReach := by
    intro source target hSourceReach hReference
    have hSourceState : source ∈ rightPending.states :=
      (rightPending.futureReachable_subset_of_reference_closed right.initial
        rightPending.states hRightInitial
        (fun current hCurrent => hRightClosed current hCurrent))
        hSourceReach
    have hTargetFromSource :=
      rightPending.referencedStates_subset_futureReachable source
        hRightClosed hSourceState hReference
    exact (rightPending.futureReachable_subset_of_mem hRightClosed
      hRightInitial hSourceReach) hTargetFromSource
  have hStateReach : state ∈ leftReach := by
    change state ∈ execution.futureReachable state
    rw [execution.futureReachable_unfold state hExecutionClosed
      hExecutionState]
    simp
  have hLeftReachSubset : leftReach.image (childState 0) ⊆
      parent.futureReachable (childState 0 state) := by
    apply PendingAutomaton.futureReachable_image_subset_of_embedding
      execution parent (childState 0)
    · intro child
      rw [hLeftReferences child]
      exact Finset.subset_union_left
    · exact hParentClosed
    · exact hParentLeftState
  by_cases hCanBridge : canBridge
  · have hBridgeStart : childState 1 right.initial ∈
        parent.futureReachable (childState 0 state) := by
      rcases hCanBridge with
        ⟨completed, hCompletedReach, hBridgeable⟩
      have hTaggedCompleted : childState 0 completed ∈
          parent.futureReachable (childState 0 state) :=
        hLeftReachSubset (Finset.mem_image.mpr
          ⟨completed, hCompletedReach, rfl⟩)
      have hBridgeReference : childState 1 right.initial ∈
          parent.referencedStates (childState 0 completed) := by
        rw [hLeftReferences completed]
        simp [hBridgeable]
      have hCompletedState : childState 0 completed ∈ parent.states :=
        (parent.futureReachable_subset_of_reference_closed
          (childState 0 state) parent.states hParentLeftState
          (fun current hCurrent => hParentClosed current hCurrent))
          hTaggedCompleted
      have hReferenceFromCompleted :=
        parent.referencedStates_subset_futureReachable
          (childState 0 completed) hParentClosed hCompletedState
          hBridgeReference
      exact (parent.futureReachable_subset_of_mem hParentClosed
        hParentLeftState hTaggedCompleted) hReferenceFromCompleted
    have hRightFromEntry : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 1 right.initial) := by
      apply PendingAutomaton.futureReachable_image_subset_of_embedding
        rightPending parent (childState 1)
      · intro child
        rw [hRightReferences child]
      · exact hParentClosed
      · exact hParentRightState
    have hRightEntryToRoot :
        parent.futureReachable (childState 1 right.initial) ⊆
          parent.futureReachable (childState 0 state) :=
      parent.futureReachable_subset_of_mem hParentClosed hParentLeftState
        hBridgeStart
    have hRightReachSubset : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 0 state) :=
      hRightFromEntry.trans hRightEntryToRoot
    simp only [hCanBridge, if_true]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state)
        (leftReach.image (childState 0) ∪
          rightReach.image (childState 1))
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩)
      · intro source hSource target hReference
        simp only [Finset.mem_union, Finset.mem_image] at hSource ⊢
        rcases hSource with ⟨child, hChildReach, rfl⟩ |
            ⟨child, hChildReach, rfl⟩
        · rw [hLeftReferences child] at hReference
          rcases Finset.mem_union.mp hReference with hChildReference |
            hBridgeReference
          · rcases Finset.mem_image.mp hChildReference with
              ⟨childTarget, hChildTarget, rfl⟩
            left
            refine ⟨childTarget, ?_, rfl⟩
            exact hExecutionReachClosed hChildReach hChildTarget
          · by_cases hBridgeable :
                child ∈ left.skipping ∨ child ∈ left.completing
            · simp [hBridgeable] at hBridgeReference
              subst target
              right
              refine ⟨right.initial, ?_, rfl⟩
              exact rightPending.mem_futureReachable_self right.initial
            · simp [hBridgeable] at hBridgeReference
        · rw [hRightReferences child] at hReference
          rcases Finset.mem_image.mp hReference with
            ⟨childTarget, hChildTarget, rfl⟩
          right
          refine ⟨childTarget, ?_, rfl⟩
          exact hRightReachClosed hChildReach hChildTarget
    · intro target hTarget
      simp only [Finset.mem_union] at hTarget
      rcases hTarget with hLeftTarget | hRightTarget
      · exact hLeftReachSubset hLeftTarget
      · exact hRightReachSubset hRightTarget
  · simp only [hCanBridge, if_false, Finset.union_empty]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state) (leftReach.image (childState 0))
      · exact Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩
      · intro source hSource target hReference
        rcases Finset.mem_image.mp hSource with ⟨child, hChildReach, rfl⟩
        rw [hLeftReferences child] at hReference
        rcases Finset.mem_union.mp hReference with hChildReference |
          hBridgeReference
        · rcases Finset.mem_image.mp hChildReference with
            ⟨childTarget, hChildTarget, rfl⟩
          apply Finset.mem_image.mpr
          refine ⟨childTarget, ?_, rfl⟩
          exact hExecutionReachClosed hChildReach hChildTarget
        · by_cases hBridgeable :
              child ∈ left.skipping ∨ child ∈ left.completing
          · exact (hCanBridge
              ⟨child, hChildReach, hBridgeable⟩).elim
          · simp [hBridgeable] at hBridgeReference
    · exact hLeftReachSubset

theorem buildSequenceAutomaton_completionWitness_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (reachable : Finset TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    (∃ completed ∈ reachable.image (.child 1),
        completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
      ∃ completed ∈ reachable,
        completed ∈ right.skipping ∨ completed ∈ right.completing := by
  classical
  constructor
  · rintro ⟨tagged, hTagged, hCompleted⟩
    rcases Finset.mem_image.mp hTagged with
      ⟨completed, hReachable, hTagged⟩
    rw [← hTagged] at hCompleted
    refine ⟨completed, hReachable, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hRight] using hCompleted
  · rintro ⟨completed, hReachable, hCompleted⟩
    refine ⟨.child 1 completed, Finset.mem_image.mpr
      ⟨completed, hReachable, rfl⟩, ?_⟩
    by_cases hRight : right.initial ∈ right.completing <;>
      simpa [buildSequenceAutomaton, finishAutomatonFragment, childSkipping,
        childCompleting, childState, hRight] using hCompleted

theorem buildSequenceAutomaton_completionWitness_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
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
      completed ∈ left.skipping ∨ completed ∈ left.completing
    let rightCanComplete := ∃ completed ∈ rightReach,
      completed ∈ right.skipping ∨ completed ∈ right.completing
    ((∃ completed ∈ parent.futureReachable (.child 0 state),
        completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
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
    completed ∈ left.skipping ∨ completed ∈ left.completing
  let rightCanComplete := ∃ completed ∈ rightReach,
    completed ∈ right.skipping ∨ completed ∈ right.completing
  change ((∃ completed ∈ parent.futureReachable (.child 0 state),
      completed ∈ sequence.skipping ∨ completed ∈ sequence.completing) ↔
    canBridge ∧ rightCanComplete)
  rw [buildSequenceAutomaton_futureReachable_left signature left right state
    hLeftState hLeftTargets hRightTargets hRightInitial]
  have hRightSelf : right.initial ∈ rightReach := by
    exact rightPending.mem_futureReachable_self right.initial
  constructor
  · rintro ⟨completed, hReachable, hCompleted⟩
    by_cases hBridge : canBridge
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
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
                finishAutomatonFragment, childSkipping, childCompleting,
                childState, hRight] using hCompleted
            · simp [sequence, buildSequenceAutomaton,
                finishAutomatonFragment, childSkipping, childCompleting,
                childState, hRight] at hCompleted
          exact ⟨right.initial, hRightSelf, Or.inr hFields.2⟩
        · rw [← hTagged] at hCompleted
          refine ⟨child, hChild, ?_⟩
          by_cases hRight : right.initial ∈ right.completing <;>
            simpa [sequence, buildSequenceAutomaton,
              finishAutomatonFragment, childSkipping, childCompleting,
              childState, hRight] using hCompleted
    · have hBridgeExpanded : ¬ ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_false, Finset.union_empty,
        Finset.mem_image]
        at hReachable
      rcases hReachable with ⟨child, hChild, hTagged⟩
      rw [← hTagged] at hCompleted
      have hLeftComplete : child ∈ left.completing := by
        by_cases hRight : right.initial ∈ right.completing
        · simpa [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childCompleting,
            childState, hRight] using hCompleted
        · simp [sequence, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childCompleting,
            childState, hRight] at hCompleted
      exact (hBridge ⟨child, hChild, Or.inr hLeftComplete⟩).elim
  · rintro ⟨hBridge, child, hChild, hCompleted⟩
    refine ⟨.child 1 child, ?_, ?_⟩
    · have hBridgeExpanded : ∃ completed ∈
          (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.skipping ∨ completed ∈ left.completing := by
        simpa [canBridge, leftReach, leftExecution] using hBridge
      simp only [hBridgeExpanded, if_true, Finset.mem_union,
        Finset.mem_image]
      exact Or.inr ⟨child, hChild, rfl⟩
    · by_cases hRight : right.initial ∈ right.completing <;>
        simpa [sequence, buildSequenceAutomaton,
          finishAutomatonFragment, childSkipping, childCompleting,
          childState, hRight] using hCompleted

/-- Future offers at a tagged sequence-left state are the offers of the
child's non-clock execution closure, together with the right-entry menu
exactly when that closure can cross either sequence bridge. -/
theorem buildSequenceAutomaton_computeFuture_left_formula
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
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
      completed ∈ left.skipping ∨ completed ∈ left.completing
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
    completed ∈ left.skipping ∨ completed ∈ left.completing
  change computeFuture parent (childState 0 state) =
    computeFuture execution state ∪
      if canBridge then computeFuture rightPending right.initial else ∅
  have hReach := buildSequenceAutomaton_futureReachable_left signature left
    right state hLeftState hLeftTargets hRightTargets hRightInitial
  have hReach' : parent.futureReachable (childState 0 state) =
      leftReach.image (childState 0) ∪
        if canBridge then rightReach.image (childState 1) else ∅ := by
    simpa [sequence, parent, execution, rightPending, leftReach, rightReach,
      canBridge] using hReach
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
    simp [parent, sequence, buildSequenceAutomaton,
      finishAutomatonFragment, childStates, childState, hLeftState]
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
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
      right
      exact ⟨state, hCompleting, rfl⟩
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

/-- Right-child resolved edges are preserved by the one-way sequence
embedding. -/
theorem buildSequenceAutomaton_hasResolvedEdge_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : right.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildSequenceAutomaton signature left right)
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge right source env label offers target := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  have hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hTargets
  have hCard : right.states.card ≤ sequence.states.card := by
    have hSubset : childStates 1 right ⊆ sequence.states := by
      intro state hState
      simp [sequence, buildSequenceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ sequence.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      simpa [childState] using hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
          left right referenced hClosed hReferenced hCard
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right source
        (childPendingEdge 1 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
            left right referenced hClosed hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

/-- A left-child edge is re-decorated from the future menu at its tagged
target.  Its original resolved future remains existentially available for the
child fragment correspondence, while its current offers are preserved. -/
theorem buildSequenceAutomaton_hasResolvedEdge_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 0 target) ↔
      ∃ childFuture,
        left.HasResolvedEdge source env label
            { current := offers.current, future := childFuture } target ∧
          computeFuture pending (.child 0 target) \ offers.current =
            offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge | hFutureBridge
    · rcases hChild with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      have hChildTarget : childEdge.target = target := by
        simpa [childState] using hTarget
      let childFuture : Finset BareMessage :=
        match childEdge.future with
        | .explicit future => future
        | .at state removed =>
            computeFuture { states := left.states, edges := left.edges }
              state \ removed
      refine ⟨childFuture, ?_, ?_⟩
      · refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment,
          hLabel, hCurrent, ?_, hChildTarget⟩
        rfl
      · rw [hCurrent] at hFuture
        have hChildVisible : childEdge.label = .visible label := hLabel
        simpa [hChildVisible, childState, hChildTarget] using hFuture
    · rcases hBridge with ⟨_, _, _, _, rfl⟩
      simp [childState] at hTarget
    · rcases hFutureBridge with ⟨_, rfl⟩
      simp at hLabel
  · rintro ⟨childFuture,
      ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
        hCurrent, _, hChildTarget⟩, hFuture⟩
    let lifted : PendingAutomatonEdge :=
      { source := childState 0 childEdge.source
        environment := childEdge.environment
        label := childEdge.label
        current := childEdge.current
        future := match childEdge.label with
          | .future => childFutureSpec 0 childEdge.future
          | _ => .at (childState 0 childEdge.target) childEdge.current
        target := childState 0 childEdge.target }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        lifted).mpr (Or.inl
          ⟨childEdge, hChildEdge, hChildSource, rfl⟩)
    refine ⟨lifted, hOutgoing.1, hOutgoing.2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lifted] using hEnvironment
    · simpa [lifted] using hLabel
    · simpa [lifted] using hCurrent
    · simpa [lifted, hLabel, childState, hChildTarget, hCurrent] using hFuture
    · simp [lifted, childState, hChildTarget]

/-- Exact classification of an administrative sequence bridge. -/
theorem buildSequenceAutomaton_hasResolvedEdge_bridge_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 1 right.initial) ↔
      source ∈ left.skipping ∧ env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 1 right.initial) = offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge | hFutureBridge
    · rcases hChild with ⟨childEdge, _, _, rfl⟩
      simp [childState] at hTarget
    · rcases hBridge with ⟨hSkipping, bridgeEnvironment,
        hBridgeEnvironment, rfl⟩
      simp only at hEnvironment hLabel hCurrent hFuture hTarget
      have hEnvironmentEq : bridgeEnvironment = env := hEnvironment
      subst bridgeEnvironment
      refine ⟨hSkipping, hBridgeEnvironment, ?_, ?_, ?_⟩
      · simpa using hLabel.symm
      · simpa using hCurrent.symm
      · simpa using hFuture
    · rcases hFutureBridge with ⟨_, rfl⟩
      simp at hLabel
  · rintro ⟨hSkipping, hEnvironment, rfl, hCurrent, hFuture⟩
    let bridge : PendingAutomatonEdge :=
      { source := childState 0 source
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        bridge).mpr (Or.inr (Or.inl
          ⟨hSkipping, env, hEnvironment, rfl⟩))
    refine ⟨bridge, hOutgoing.1, hOutgoing.2, rfl, rfl, ?_, ?_, rfl⟩
    · simpa [bridge] using hCurrent.symm
    · simpa [bridge] using hFuture

end

end Pact
