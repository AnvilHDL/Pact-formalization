import Anvilpp.PactTypes.CorrespondenceCore

/-!
# Exclusive and conjunctive offer correspondence

Constructor-edge classifiers and raw semantic correspondence for offer nodes.
The operational future menu remains syntax-derived; whole-node future
correctness is supplied explicitly to the raw step theorems below.
-/

namespace Pact

noncomputable section

private theorem mem_parallelBranchInterfaces_iff_exists
    (message : MessageId) : ∀ branches,
    message ∈ PactType.ParallelBranchInterfaces branches ↔
      ∃ entry ∈ branches, message ∈ entry.2.ParallelInterfaces := by
  intro branches
  induction branches with
  | nil => simp [PactType.ParallelBranchInterfaces]
  | cons entry rest ih =>
      rcases entry with ⟨action, processType⟩
      simp [PactType.ParallelBranchInterfaces, ih]

private theorem parallelInterfaces_subset_parallelBranchInterfaces_of_mem
    {branches : List (BareMessage × PactType)}
    {entry : BareMessage × PactType} (hEntry : entry ∈ branches) :
    entry.2.ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  intro message hMessage
  exact (mem_parallelBranchInterfaces_iff_exists message branches).mpr
    ⟨entry, hEntry, hMessage⟩

theorem parallelTypeBranches_parallelInterfaces_subset
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranches branches).ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
            using Finset.union_subset_union (fun _ h => h) ih

theorem parallelTypeBranches_interfaceScoped
    (branches : List (BareMessage × PactType))
    (hScoped : PactType.InterfaceScopedBranches branches) :
    PactType.InterfaceScoped (parallelTypeBranches branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.InterfaceScoped]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.InterfaceScopedBranches] at hScoped
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.InterfaceScoped, PactType.InterfaceScopedBranches]
            using hScoped.1
      | cons next tail =>
          have hRest := ih hScoped.2
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
            hScoped.1, hRest]

/-! ### Exclusive and conjunctive offer correspondence -/

/- The following two observations package the common part of every tagged
child embedding.  Offer constructors use more than two children, so the
binary-choice-specific embedding lemmas above cannot be applied directly. -/
private theorem taggedChild_referencedStates_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    parent.referencedStates (childState index state) =
      (child.referencedStates state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [hOutgoing]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem taggedChild_offersAt_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    parent.offersAt (childState index state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [hOutgoing]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem taggedChild_computeFuture_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hClosed : child.ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ child.states)
    (hCard : child.states.card ≤ parent.states.card) :
    computeFuture parent (childState index state) =
      computeFuture child state := by
  apply computeFuture_eq_of_embedding child parent (childState index)
  · exact taggedChild_referencedStates_of_outgoing parent child index
      hOutgoing
  · exact taggedChild_offersAt_of_outgoing parent child index hOutgoing
  · exact hClosed
  · exact hState
  · exact hCard

private theorem taggedChild_hasResolvedEdge_iff_of_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hTargets : child.FutureTargetsInStates)
    (hCard : child.states.card ≤ parent.states.card)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    parent.HasResolvedEdge (childState index source) env label offers
        (childState index target) ↔
      child.HasResolvedEdge source env label offers target := by
  classical
  let parentPending : PendingAutomaton :=
    { states := parent.states, edges := parent.edges }
  let childPending : PendingAutomaton :=
    { states := child.states, edges := child.edges }
  have hClosed : childPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates child hTargets
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hEmbedded := (hOutgoing source edge).mp ⟨hEdge, hSource⟩
    rcases hEmbedded with
      ⟨childEdge, hChildEdge, hChildSource, hEdgeEquality⟩
    have hChildTarget : childEdge.target = target := by
      rw [hEdgeEquality] at hTarget
      simpa [childPendingEdge, childState] using hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, ?_, ?_, ?_, ?_,
      hChildTarget⟩
    · simpa [hEdgeEquality, childPendingEdge] using hEnvironment
    · simpa [hEdgeEquality, childPendingEdge] using hLabel
    · simpa [hEdgeEquality, childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [hEdgeEquality, childPendingEdge, childFutureSpec, hSpec]
            using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          have hComputed := taggedChild_computeFuture_of_outgoing
            parentPending childPending index hOutgoing hClosed referenced
            hReferenced hCard
          simp only [hEdgeEquality, childPendingEdge, childFutureSpec, hSpec,
            childState] at hFuture
          have hRemoved := congrArg (fun available => available \ removed)
            hComputed
          simpa [hSpec, parentPending, childPending] using
            hRemoved.symm.trans hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hEmbedded := (hOutgoing source
      (childPendingEdge index childEdge)).mpr
      ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge index childEdge, hEmbedded.1, hEmbedded.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          have hComputed := taggedChild_computeFuture_of_outgoing
            parentPending childPending index hOutgoing hClosed referenced
            hReferenced hCard
          simp only [hSpec] at hFuture
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          have hRemoved := congrArg (fun available => available \ removed)
            hComputed
          simpa [hSpec, parentPending, childPending] using
            hRemoved.trans hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem taggedChild_hasResolvedEdge_cases_of_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hTargets : child.FutureTargetsInStates)
    (hCard : child.states.card ≤ parent.states.card)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : parent.HasResolvedEdge (childState index source) env label offers
      target) :
    ∃ childTarget,
      target = childState index childTarget ∧
        child.HasResolvedEdge source env label offers childTarget := by
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  have hEmbedded := (hOutgoing source edge).mp ⟨hPending, hSource⟩
  rcases hEmbedded with
    ⟨childEdge, _, _, hEdgeEquality⟩
  have hTargetEquality : target = childState index childEdge.target := by
    rw [hEdgeEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (taggedChild_hasResolvedEdge_iff_of_outgoing parent child index
    hOutgoing hTargets hCard source childEdge.target env label offers).mp
  rw [← hTargetEquality]
  exact ⟨edge, hPending, hSource, hEnvironment, hLabel, hCurrent,
    hFuture, hTarget⟩

/- Every edge from the else child of an exclusive offer is exactly the
corresponding tagged child edge. -/
private theorem buildExclusiveOfferAutomaton_outgoing_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = childState 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · simp only [childPendingEdges, Finset.mem_image] at hElse
      rcases hElse with ⟨childEdge, hChildEdge, hEquality⟩
      have hChildSource := hSource
      rw [← hEquality] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      left
      left
      exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
    · simp [childPendingEdge, childState, hChildSource]

/- Every edge from an indexed branch child of an exclusive offer is exactly
the corresponding tagged child edge. -/
private theorem buildExclusiveOfferAutomaton_outgoing_branch
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = childState (index + 1) state ↔
      ∃ childEdge ∈ entry.2.edges,
        childEdge.source = state ∧
          edge = childPendingEdge (index + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · simp only [childPendingEdges, Finset.mem_image] at hElse
      rcases hElse with ⟨childEdge, _, hEquality⟩
      rw [← hEquality] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        have hIndex : indexed.2 = index := by
          simp [childPendingEdge, childState] at hChildSource
          omega
        have hInnerSource : childEdge.source = state := by
          simp [childPendingEdge, childState, hIndex] at hChildSource
          exact hChildSource
        have hIndexedFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
          at hIndexedFields
        rcases hIndexedFields with ⟨hBound, hValue⟩
        have hIndexedEntry : branchAutomata[indexed.2]? =
            some indexed.1 := by
          rw [List.getElem?_eq_getElem hBound, ← hValue]
        have hEntryEq : indexed.1 = entry := by
          have hOptions := congrArg
            (fun position => branchAutomata[position]?) hIndex
          change branchAutomata[indexed.2]? = branchAutomata[index]? at hOptions
          rw [hIndexedEntry, hEntry] at hOptions
          exact Option.some.inj hOptions
        rw [hEntryEq] at hChildEdge
        rw [hIndex] at hEquality
        exact ⟨childEdge, hChildEdge, hInnerSource, hEquality.symm⟩
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hZipBound : index < branchAutomata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ branchAutomata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      left
      right
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      right
      exact ⟨(entry, index), hIndexed,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/- The two tagged child families of a conjunctive offer are disjoint from all
fresh root edges. -/
private theorem buildConjunctiveOfferAutomaton_outgoing_child
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (index : Nat) (child : AutomatonFragment)
    (hIndex : (index = 0 ∧ child = conjunction) ∨
      (index = 1 ∧ child = elseAutomaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    edge ∈ offer.edges ∧ edge.source = childState index state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge index childEdge := by
  classical
  rcases hIndex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · rintro ⟨hEdge, hSource⟩
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hChild | hOther) | hEnabled) | hWait) | hElse)
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
      · simp only [childPendingEdges, Finset.mem_image] at hOther
        rcases hOther with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
        rcases hEnabled with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hElse
        rcases hElse with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        left
        left
        left
        left
        exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
      · simp [childPendingEdge, childState, hChildSource]
  · constructor
    · rintro ⟨hEdge, hSource⟩
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hOther | hChild) | hEnabled) | hWait) | hElse)
      · simp only [childPendingEdges, Finset.mem_image] at hOther
        rcases hOther with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
        rcases hEnabled with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hElse
        rcases hElse with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        left
        left
        left
        right
        exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
      · simp [childPendingEdge, childState, hChildSource]

/- Exact resolved-edge classifier at the fresh exclusive-offer root. -/
private theorem buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (∃ indexed ∈ branchAutomata.zipIdx,
        env ∈ signature.localEnvironments ∧
          typeNeed indexed.1.1 ∈ env.immediate ∧
          typeBranchNeeds branches ∩ env.future = ∅ ∧
          label = TypeLabel.message indexed.1.1.1 indexed.1.1.2 ∧
          offers.current = {indexed.1.1} ∧
          computeFuture pending
              (childState (indexed.2 + 1) indexed.1.2.initial) =
            offers.future ∧
          target = childState (indexed.2 + 1) indexed.1.2.initial) ∨
      (env ∈ signature.localEnvironments ∧ env.clock = false ∧
        typeBranchNeeds branches ∩ env.future ≠ ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeWaitingOffers env branches ∧
        computeFuture pending .root \ typeWaitingOffers env branches =
          offers.future ∧ target = .root) ∨
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future = ∅ ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (childState 0 elseAutomaton.initial) =
          offers.future ∧ target = childState 0 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hElse | hIndexed) | hBranch) | hWait) | hElseEdge),
      hSource, hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
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
      rcases hBranch with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨edgeEnvironment, hConditions, rfl⟩
        left
        simp only [Finset.sdiff_empty] at hFuture
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        rcases hConditions with ⟨hLocal, hEnabled, hResolved⟩
        subst env
        have hSemanticLabel : label =
            TypeLabel.message indexed.1.1.1 indexed.1.1.2 := by
          have hCongruence :=
            congrArg AutomatonConstructionLabel.semantic hLabel
          simpa using hCongruence.symm
        exact ⟨indexed, hIndexed, hLocal, hEnabled, hResolved,
          hSemanticLabel, hCurrent.symm, hFuture, hTarget.symm⟩
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      left
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hClock, hFutureBranches⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      refine ⟨hLocal, hClock, hFutureBranches, hSemanticLabel, ?_, ?_,
        hTarget.symm⟩
      · simpa only [typeWaitingOffers] using hCurrent.symm
      · simpa only [typeWaitingOffers, Finset.union_assoc,
          Finset.singleton_union] using hFuture
    · simp only [Finset.mem_image, Finset.mem_filter] at hElseEdge
      rcases hElseEdge with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      right
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate, hResolved⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hResolved, hSemanticLabel,
        hCurrent.symm, hFuture, hTarget.symm⟩
  · rintro (hBranch | hWait | hElse)
    · rcases hBranch with ⟨indexed, hIndexed, hLocal, hEnabled,
        hResolved, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible
            (TypeLabel.message indexed.1.1.1 indexed.1.1.2)
          current := {indexed.1.1}
          future := .at
            (childState (indexed.2 + 1) indexed.1.2.initial) ∅
          target := childState (indexed.2 + 1) indexed.1.2.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        rw [mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hEnabled, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hWait with ⟨hLocal, hClock, hFutureBranches, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeWaitingOffers env branches
          future := .at .root (typeWaitingOffers env branches)
          target := .root }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hClock, hFutureBranches⟩⟩, by
              simp [typeWaitingOffers]⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hElse with ⟨hLocal, hImmediate, hResolved, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 elseAutomaton.initial) ∅
          target := childState 0 elseAutomaton.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hImmediate, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
/- Exact resolved-edge classifier at the fresh conjunctive-offer root. -/
private theorem buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate ≠ ∅ ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (childState 0 conjunction.initial) =
          offers.future ∧ target = childState 0 conjunction.initial) ∨
      (env ∈ signature.localEnvironments ∧ env.clock = false ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future ≠ ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeWaitingOffers env branches ∧
        computeFuture pending .root \ typeWaitingOffers env branches =
          offers.future ∧ target = .root) ∨
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future = ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeBranchActions branches ∧
        computeFuture pending (childState 1 elseAutomaton.initial) =
          offers.future ∧ target = childState 1 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hConjunction | hElseChild) | hEnabled) | hWait) |
      hElseEdge), hSource, hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · simp only [childPendingEdges, Finset.mem_image] at hConjunction
      rcases hConjunction with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [childPendingEdges, Finset.mem_image] at hElseChild
      rcases hElseChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
      rcases hEnabled with ⟨edgeEnvironment, hConditions, rfl⟩
      left
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hSemanticLabel, hCurrent.symm,
        hFuture, hTarget.symm⟩
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      left
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with
        ⟨hLocal, hClock, hImmediate, hFutureBranches⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      refine ⟨hLocal, hClock, hImmediate, hFutureBranches, hSemanticLabel,
        ?_, ?_, hTarget.symm⟩
      · simpa only [typeWaitingOffers] using hCurrent.symm
      · simpa only [typeWaitingOffers, Finset.union_assoc,
          Finset.singleton_union] using hFuture
    · simp only [Finset.mem_image, Finset.mem_filter] at hElseEdge
      rcases hElseEdge with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      right
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate, hResolved⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hResolved, hSemanticLabel,
        hCurrent.symm, hFuture, hTarget.symm⟩
  · rintro (hEnabled | hWait | hElse)
    · rcases hEnabled with ⟨hLocal, hImmediate, hLabel, hCurrent,
        hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 conjunction.initial) ∅
          target := childState 0 conjunction.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr ⟨hLocal, hImmediate⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hWait with ⟨hLocal, hClock, hImmediate, hFutureBranches,
        hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeWaitingOffers env branches
          future := .at .root (typeWaitingOffers env branches)
          target := .root }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hClock, hImmediate, hFutureBranches⟩⟩, by
              simp [typeWaitingOffers]⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hElse with ⟨hLocal, hImmediate, hResolved, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeBranchActions branches
          future := .at (childState 1 elseAutomaton.initial) ∅
          target := childState 1 elseAutomaton.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hImmediate, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm

private theorem compileTypeFuel_xoffer_else_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches)).HasResolvedEdge
          (childState 0 source) env label offers (childState 0 target) ↔
      (compileTypeFuel signature (typeCompilationFuel elseType) elseType).HasResolvedEdge
        source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hCard : elseFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      elseFragment.states.card = (childStates 0 elseFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge :=
    buildExclusiveOfferAutomaton_outgoing_else signature branches
      elseFragment branchAutomata
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    elseFragment 0 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature elseType
    hElseFuel (typeCompilationFuel_sufficient elseType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, branchAutomata, fuel, hStable] using hRaw

private theorem compileTypeFuel_xoffer_branch_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (action : BareMessage) (branchType : PactType) (index : Nat)
    (hEntry : branches[index]? = some (action, branchType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches)).HasResolvedEdge
          (childState (index + 1) source) env label offers
          (childState (index + 1) target) ↔
      (compileTypeFuel signature
        (typeCompilationFuel branchType) branchType).HasResolvedEdge
          source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchFragment := compileTypeFuel signature fuel branchType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hBranchMember : (action, branchType) ∈ branches := by
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hMember := List.getElem_mem hBound
    simpa [hValue] using hMember
  have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
    exact le_trans
      (typeCompilationFuel_le_typeBranchCompilationFuel branches
        (action, branchType) hBranchMember)
      (by simp [fuel])
  have hTargets : branchFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel branchType
      hBranchFuel
  have hAutomatonEntry : branchAutomata[index]? =
      some (action, branchFragment) := by
    simp [branchAutomata, branchFragment, hEntry]
  have hZipEntry : ((action, branchFragment), index) ∈
      branchAutomata.zipIdx := by
    rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < branchAutomata.zipIdx.length := by
      simpa using hBound
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  have hCard : branchFragment.states.card ≤ fragment.states.card := by
    have hIndexedSubset : childStates (index + 1) branchFragment ⊆
        indexedFragmentStates branchAutomata := by
      intro state hState
      rw [indexedFragmentStates, mem_foldl_union_iff]
      right
      exact ⟨((action, branchFragment), index), hZipEntry, hState⟩
    have hSubset : childStates (index + 1) branchFragment ⊆
        fragment.states := by
      intro state hState
      have hIndexed := hIndexedSubset hState
      simp [fragment, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, hIndexed]
    calc
      branchFragment.states.card =
          (childStates (index + 1) branchFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧
          edge.source = childState (index + 1) state ↔
        ∃ childEdge ∈ branchFragment.edges,
          childEdge.source = state ∧
            edge = childPendingEdge (index + 1) childEdge :=
    buildExclusiveOfferAutomaton_outgoing_branch signature branches
      elseFragment branchAutomata index (action, branchFragment)
      hAutomatonEntry
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    branchFragment (index + 1) hOutgoing hTargets hCard source target env
    label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature branchType
    hBranchFuel (typeCompilationFuel_sufficient branchType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, branchFragment, branchAutomata, fuel, hStable] using hRaw

private theorem compileTypeFuel_offer_conjunction_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState 0 source) env label offers (childState 0 target) ↔
      (compileTypeFuel signature
        (typeCompilationFuel (parallelTypeBranches branches))
        (parallelTypeBranches branches)).HasResolvedEdge
          source env label offers target := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel]
  have hTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hCard : conjunction.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 conjunction ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      conjunction.states.card = (childStates 0 conjunction).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ conjunction.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge :=
    buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    conjunction 0 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature conjunctionType
    hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    conjunction, conjunctionType, elseFragment, fuel, hStable] using hRaw

private theorem compileTypeFuel_offer_else_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState 1 source) env label offers (childState 1 target) ↔
      (compileTypeFuel signature (typeCompilationFuel elseType) elseType).HasResolvedEdge
        source env label offers target := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hCard : elseFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      elseFragment.states.card = (childStates 1 elseFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 1 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 1 childEdge :=
    buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 1 elseFragment (Or.inr ⟨rfl, rfl⟩)
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    elseFragment 1 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature elseType
    hElseFuel (typeCompilationFuel_sufficient elseType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    conjunction, conjunctionType, elseFragment, fuel, hStable] using hRaw

private theorem compileTypeFuel_xoffer_else_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches)).HasResolvedEdge
        (childState 0 source) env label offers target) :
    ∃ childTarget,
      target = childState 0 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel elseType) elseType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildExclusiveOfferAutomaton_outgoing_else signature branches
      elseFragment branchAutomata source pendingEdge).mp
      ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 0 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_xoffer_else_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_xoffer_branch_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (action : BareMessage) (branchType : PactType) (index : Nat)
    (hEntry : branches[index]? = some (action, branchType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches)).HasResolvedEdge
        (childState (index + 1) source) env label offers target) :
    ∃ childTarget,
      target = childState (index + 1) childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel branchType) branchType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchFragment := compileTypeFuel signature fuel branchType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hAutomatonEntry : branchAutomata[index]? =
      some (action, branchFragment) := by
    simp [branchAutomata, branchFragment, hEntry]
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildExclusiveOfferAutomaton_outgoing_branch signature branches
      elseFragment branchAutomata index (action, branchFragment)
      hAutomatonEntry source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target =
      childState (index + 1) childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_xoffer_branch_child_edge_iff signature elseType
    branches action branchType index hEntry source childEdge.target env label
    offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_offer_conjunction_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches)).HasResolvedEdge
        (childState 0 source) env label offers target) :
    ∃ childTarget,
      target = childState 0 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranches branches))
          (parallelTypeBranches branches)).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
      source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 0 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_offer_conjunction_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_offer_else_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches)).HasResolvedEdge
        (childState 1 source) env label offers target) :
    ∃ childTarget,
      target = childState 1 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel elseType) elseType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 1 elseFragment (Or.inr ⟨rfl, rfl⟩)
      source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 1 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_offer_else_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem typeBranchEnabled_exists_iff
    (env : TypeEnvironment) (branches : List (BareMessage × PactType)) :
    (∃ enabled ∈ branches, TypeBranchEnabled env enabled) ↔
      typeBranchNeeds branches ∩ env.immediate ≠ ∅ := by
  classical
  constructor
  · rintro ⟨enabled, hEnabledMember, hEnabled⟩ hEmpty
    have hNeed : typeNeed enabled.1 ∈ typeBranchNeeds branches := by
      simp only [typeBranchNeeds, List.mem_toFinset, List.mem_map]
      exact ⟨enabled, hEnabledMember, rfl⟩
    have hIntersection : typeNeed enabled.1 ∈
        typeBranchNeeds branches ∩ env.immediate :=
      Finset.mem_inter.mpr ⟨hNeed, hEnabled⟩
    rw [hEmpty] at hIntersection
    simp at hIntersection
  · intro hNonempty
    have hWitness := Finset.nonempty_iff_ne_empty.mpr hNonempty
    rcases hWitness with ⟨need, hNeed⟩
    rcases Finset.mem_inter.mp hNeed with ⟨hBranchNeed, hImmediate⟩
    simp only [typeBranchNeeds, List.mem_toFinset, List.mem_map]
      at hBranchNeed
    rcases hBranchNeed with ⟨enabled, hEnabledMember, hNeedEquality⟩
    refine ⟨enabled, hEnabledMember, ?_⟩
    unfold TypeBranchEnabled
    rw [hNeedEquality]
    exact hImmediate

private theorem List.exists_getElem?_eq_some_of_mem
    {Element : Type} {element : Element} {items : List Element}
    (hMember : element ∈ items) :
    ∃ index : Nat, items[index]? = some element := by
  rcases List.mem_iff_getElem.mp hMember with ⟨index, hBound, hValue⟩
  refine ⟨index, ?_⟩
  rw [List.getElem?_eq_getElem hBound, hValue]

private theorem TypeLabel.message_injective
    {first second : BareMessage}
    (hEquality : TypeLabel.message first.1 first.2 =
      TypeLabel.message second.1 second.2) :
    first = second := by
  rcases first with ⟨firstMessage, firstDirection⟩
  rcases second with ⟨secondMessage, secondDirection⟩
  simp [TypeLabel.message] at hEquality
  simp [hEquality.1, hEquality.2]

private theorem TypeLabel.message_ne_silent (action : BareMessage) :
    TypeLabel.message action.1 action.2 ≠ TypeLabel.silent := by
  rcases action with ⟨message, direction⟩
  simp [TypeLabel.message, TypeLabel.silent]

private theorem TypeOffers.xoffer_branch_fields
    {env : TypeEnvironment} {elseType branchType : PactType}
    {branches : List (BareMessage × PactType)} {action : BareMessage}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      (TypeLabel.message action.1 action.2) branchType current future) :
    current = {action} ∧ future = typeFutureOffers branchType := by
  generalize hLabel : TypeLabel.message action.1 action.2 = actualLabel
    at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ actualAction _ _ =>
      have hAction := TypeLabel.message_injective hLabel
      subst actualAction
      exact ⟨rfl, rfl⟩
  | xoffer_else =>
      exact (TypeLabel.message_ne_silent action hLabel).elim
  | xoffer_wait =>
      exact (TypeLabel.message_ne_silent action hLabel).elim

private theorem TypeOffers.xoffer_else_fields
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      TypeLabel.silent elseType current future) :
    current = ∅ ∧ future = typeFutureOffers elseType := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ action _ _ =>
      exact (TypeLabel.message_ne_silent action hLabel.symm).elim
  | xoffer_else => exact ⟨rfl, rfl⟩

private theorem TypeOffers.xoffer_wait_fields
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      TypeLabel.silent (.xoffer elseType branches) current future) :
    current = typeWaitingOffers env branches ∧
      future = typeFutureOffers (.xoffer elseType branches) \
        typeWaitingOffers env branches := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ action _ _ =>
      exact (TypeLabel.message_ne_silent action hLabel.symm).elim
  | xoffer_wait => exact ⟨rfl, rfl⟩

/-- Exclusive offers preserve raw pending-fragment step correspondence. -/
theorem compilationFragmentStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationFragmentStepCorrect signature (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | xoffer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | xoffer_branch _ _ _ action _ hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled, hResolved⟩
            rcases TypeOffers.xoffer_branch_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient residual' fuel := by
              exact le_trans
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, residual') hBranchMember)
                (by simp [fuel])
            let branchFragment := compileTypeFuel signature fuel residual'
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation signature fuel residual'
                hBranchFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            have hAutomatonEntry : branchAutomata[index]? =
                some (action, branchFragment) := by
              simp [branchAutomata, branchFragment, hEntry]
            rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
              ⟨hBound, hValue⟩
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa using hBound
            have hZipEntry : ((action, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            refine ⟨childState (index + 1) branchFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              (TypeLabel.message action.1 action.2) ⟨current, future⟩
              (childState (index + 1) branchFragment.initial)).mpr
            left
            exact ⟨((action, branchFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hImmediate, hResolved⟩
            rcases TypeOffers.xoffer_else_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hImmediate, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_wait _ _ _ hConditions =>
            rcases hConditions with ⟨_, hUnresolved, hClock⟩
            rcases TypeOffers.xoffer_wait_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.xoffer elseType branches) .root
                (.xoffer elseType branches) :=
              TypeCompilationRelation.xoffer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, by
                simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent,
              hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment branchAutomata env label
          ⟨current, future⟩
          target).mp hEdge with hBranch | hWait | hElse
        · rcases hBranch with ⟨indexed, hIndexed, _, hEnabled, hResolved,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [branchAutomata] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel branch.2) := by
            rw [hValue]
            simp [branchAutomata, branch]
          rw [hIndexedValue] at hEnabled hLabel hCurrent hEdgeFuture hTargetState
          subst target
          have hBranchMember : branch ∈ branches :=
            List.getElem_mem hBranchBound
          have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                branch hBranchMember)
              (by simp [fuel])
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation signature fuel branch.2
              hBranchFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel branch.2).initial)
              branch.2 :=
            TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
              branches branch.1 indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers branch.2 := hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
          · exact
              (TypeOffers.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
        · rcases hWait with ⟨_, hClock, hFutureBranches, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.xoffer elseType branches) .root
              (.xoffer elseType branches) :=
            TypeCompilationRelation.xoffer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
          · exact
              (TypeOffers.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
        · rcases hElse with ⟨_, hImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
          · exact
              (TypeOffers.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr
            hChildEdge
        · exact TypeCompilationRelation.xoffer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      constructor
      · intro hSemanticStep
        rcases (hStep hChildRelated hLocalEnvironment).mp hSemanticStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_branch_child_edge_iff signature
            elseType branches action branchType index hEntry childQ
            childTarget env label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.xoffer_branch elseType branchType
            residual' branches action index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
          elseType branches action branchType index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_branch _ targetBranchType _ _ targetAction _ _
            hTargetEntry hChildTarget =>
            have hEntryEquality : (action, branchType) =
                (targetAction, targetBranchType) :=
              Option.some.inj (hEntry.symm.trans hTargetEntry)
            cases hEntryEquality
            exact (hStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Exclusive offers preserve scoped pending-fragment step correspondence. -/
theorem compilationScopedFragmentStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationScopedFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationScopedFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationScopedFragmentStepCorrect signature (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | xoffer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | xoffer_branch _ _ _ action _ hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled, hResolved⟩
            rcases TypeOffers.xoffer_branch_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient residual' fuel := by
              exact le_trans
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, residual') hBranchMember)
                (by simp [fuel])
            let branchFragment := compileTypeFuel signature fuel residual'
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation signature fuel residual'
                hBranchFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            have hAutomatonEntry : branchAutomata[index]? =
                some (action, branchFragment) := by
              simp [branchAutomata, branchFragment, hEntry]
            rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
              ⟨hBound, hValue⟩
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa using hBound
            have hZipEntry : ((action, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            refine ⟨childState (index + 1) branchFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              (TypeLabel.message action.1 action.2) ⟨current, future⟩
              (childState (index + 1) branchFragment.initial)).mpr
            left
            exact ⟨((action, branchFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hImmediate, hResolved⟩
            rcases TypeOffers.xoffer_else_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hImmediate, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_wait _ _ _ hConditions =>
            rcases hConditions with ⟨_, hUnresolved, hClock⟩
            rcases TypeOffers.xoffer_wait_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.xoffer elseType branches) .root
                (.xoffer elseType branches) :=
              TypeCompilationRelation.xoffer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, by
                simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent,
              hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment branchAutomata env label
          ⟨current, future⟩
          target).mp hEdge with hBranch | hWait | hElse
        · rcases hBranch with ⟨indexed, hIndexed, _, hEnabled, hResolved,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [branchAutomata] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel branch.2) := by
            rw [hValue]
            simp [branchAutomata, branch]
          rw [hIndexedValue] at hEnabled hLabel hCurrent hEdgeFuture hTargetState
          subst target
          have hBranchMember : branch ∈ branches :=
            List.getElem_mem hBranchBound
          have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                branch hBranchMember)
              (by simp [fuel])
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation signature fuel branch.2
              hBranchFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel branch.2).initial)
              branch.2 :=
            TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
              branches branch.1 indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers branch.2 := hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
          · exact
              (TypeOffers.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
        · rcases hWait with ⟨_, hClock, hFutureBranches, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.xoffer elseType branches) .root
              (.xoffer elseType branches) :=
            TypeCompilationRelation.xoffer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
          · exact
              (TypeOffers.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
        · rcases hElse with ⟨_, hImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
          · exact
              (TypeOffers.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hStep
        rcases (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr
            hChildEdge
        · exact TypeCompilationRelation.xoffer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationScopedFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      have hMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hAt := List.getElem_mem hBound
        simpa [hValue] using hAt
      have hAvoidsBranch : env.AvoidsInterface
          branchType.ParallelInterfaces :=
        hAvoids.mono (by
          intro message hMessage
          simp only [PactType.ParallelInterfaces, Finset.mem_union]
          right
          exact parallelInterfaces_subset_parallelBranchInterfaces_of_mem
            hMember hMessage)
      constructor
      · intro hSemanticStep
        rcases (hStep hChildRelated hLocalEnvironment hAvoidsBranch).mp hSemanticStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_branch_child_edge_iff signature
            elseType branches action branchType index hEntry childQ
            childTarget env label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.xoffer_branch elseType branchType
            residual' branches action index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
          elseType branches action branchType index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_branch _ targetBranchType _ _ targetAction _ _
            hTargetEntry hChildTarget =>
            have hEntryEquality : (action, branchType) =
                (targetAction, targetBranchType) :=
              Option.some.inj (hEntry.symm.trans hTargetEntry)
            cases hEntryEquality
            exact (hStep hChildRelated hLocalEnvironment hAvoidsBranch).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Public exclusive-offer correspondence follows by alphabet export. -/
theorem compilationStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationStepCorrect signature (.xoffer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_xoffer signature elseType
    branches hElseStep hBranchStep hFuture (residual := residual)
    (residual' := residual') (state := state) (env := env) (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mpr hEdge, hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mp hEdge, hTarget⟩

private theorem TypeOffers.offer_some_fields_of_enabled
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hEnabled : ∃ enabled ∈ branches, TypeBranchEnabled env enabled)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      (parallelTypeBranches branches) current future) :
    current = ∅ ∧
      future = typeFutureOffers (parallelTypeBranches branches) := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : parallelTypeBranches branches = actualTarget at hOffers
  cases hOffers with
  | offer_some => exact ⟨rfl, rfl⟩
  | offer_else _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim
  | offer_wait _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim

private theorem TypeOffers.offer_else_fields_of_resolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hResolved : TypeResolved env branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      elseType current future) :
    current = typeBranchActions branches ∧
      future = typeFutureOffers elseType := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : elseType = actualTarget at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else => exact ⟨rfl, rfl⟩

private theorem TypeOffers.offer_wait_fields_of_unresolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {target : PactType} {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hUnresolved : ¬ TypeResolved env branches)
    (hTarget : target = .offer elseType branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      target current future) :
    current = typeWaitingOffers env branches ∧
      future = typeFutureOffers (.offer elseType branches) \
        typeWaitingOffers env branches := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else _ _ _ hConditions =>
      exact (hUnresolved hConditions.2.2).elim
  | offer_wait => exact ⟨rfl, rfl⟩

/-- Conjunctive offers preserve raw pending-fragment step correspondence. -/
theorem compilationFragmentStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : CompilationFragmentStepCorrect signature
      (parallelTypeBranches branches))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationFragmentStepCorrect signature (.offer elseType branches) := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness hOffers with ⟨hCurrent, hOfferFuture⟩
            have hConjunctionFuel :
                TypeCompilationFuelSufficient conjunctionType fuel := by
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranches]
              simp [fuel]
            have hInitial : TypeCompilationRelation conjunctionType
                conjunction.initial conjunctionType :=
              compileTypeFuel_initial_relation signature fuel conjunctionType
                hConjunctionFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 conjunction.initial) conjunctionType :=
              TypeCompilationRelation.offer_branches elseType conjunctionType
                branches conjunction.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 conjunction.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 conjunction.initial)).mpr
            left
            exact ⟨hLocalEnvironment,
              (typeBranchEnabled_exists_iff env branches).mp
                hEnabledWitness,
              rfl, hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 1 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 1 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 1 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment conjunction env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨_, hImmediate, hLabel, hCurrent,
            hEdgeFuture, hTargetState⟩
          subst target
          have hConjunctionFuel :
              TypeCompilationFuelSufficient conjunctionType fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [fuel]
          have hInitial : TypeCompilationRelation conjunctionType
              conjunction.initial conjunctionType :=
            compileTypeFuel_initial_relation signature fuel conjunctionType
              hConjunctionFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 conjunction.initial) conjunctionType :=
            TypeCompilationRelation.offer_branches elseType conjunctionType
              branches conjunction.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers conjunctionType :=
            hEdgeFuture.symm.trans hComputed
          rcases (typeBranchEnabled_exists_iff env branches).mpr hImmediate
            with ⟨enabled, hBranchMember, hBranchEnabled⟩
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 1 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep hChildRelated hLocalEnvironment).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ _ hChildTarget =>
            exact (hConjunctionStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

theorem compilationScopedFragmentStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : CompilationScopedFragmentStepCorrect signature
      (parallelTypeBranches branches))
    (hElseStep : CompilationScopedFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationScopedFragmentStepCorrect signature
      (.offer elseType branches) := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
  have hAvoidsConjunction : env.AvoidsInterface
      (parallelTypeBranches branches).ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp only [PactType.ParallelInterfaces, Finset.mem_union]
      right
      exact parallelTypeBranches_parallelInterfaces_subset branches hMessage)
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness hOffers with ⟨hCurrent, hOfferFuture⟩
            have hConjunctionFuel :
                TypeCompilationFuelSufficient conjunctionType fuel := by
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranches]
              simp [fuel]
            have hInitial : TypeCompilationRelation conjunctionType
                conjunction.initial conjunctionType :=
              compileTypeFuel_initial_relation signature fuel conjunctionType
                hConjunctionFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 conjunction.initial) conjunctionType :=
              TypeCompilationRelation.offer_branches elseType conjunctionType
                branches conjunction.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 conjunction.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 conjunction.initial)).mpr
            left
            exact ⟨hLocalEnvironment,
              (typeBranchEnabled_exists_iff env branches).mp
                hEnabledWitness,
              rfl, hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 1 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 1 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 1 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment conjunction env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨_, hImmediate, hLabel, hCurrent,
            hEdgeFuture, hTargetState⟩
          subst target
          have hConjunctionFuel :
              TypeCompilationFuelSufficient conjunctionType fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [fuel]
          have hInitial : TypeCompilationRelation conjunctionType
              conjunction.initial conjunctionType :=
            compileTypeFuel_initial_relation signature fuel conjunctionType
              hConjunctionFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 conjunction.initial) conjunctionType :=
            TypeCompilationRelation.offer_branches elseType conjunctionType
              branches conjunction.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers conjunctionType :=
            hEdgeFuture.symm.trans hComputed
          rcases (typeBranchEnabled_exists_iff env branches).mpr hImmediate
            with ⟨enabled, hBranchMember, hBranchEnabled⟩
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 1 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep hChildRelated hLocalEnvironment hAvoidsConjunction).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ _ hChildTarget =>
            exact (hConjunctionStep hChildRelated hLocalEnvironment hAvoidsConjunction).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩


end

end Pact
