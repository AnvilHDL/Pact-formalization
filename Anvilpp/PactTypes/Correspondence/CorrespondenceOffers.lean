import Anvilpp.PactTypes.Correspondence.CorrespondenceCore

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

theorem parallelTypeBranchesSelecting_parallelInterfaces_subset
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranchesSelecting selected branches).ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · rw [show parallelTypeBranchesSelecting selected
                [(action, processType)] = selectedTypeBranch (action, processType)
              by simp [parallelTypeBranchesSelecting, hEq]]
            simp [selectedTypeBranch, PactType.ParallelInterfaces,
              PactType.ParallelBranchInterfaces]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            rw [show parallelTypeBranchesSelecting (action, processType)
                ((action, processType) :: next :: tail) =
                .par (selectedTypeBranch (action, processType))
                  (parallelTypeBranches (next :: tail)) ∅
              by simp [parallelTypeBranchesSelecting]]
            simp only [PactType.ParallelInterfaces, selectedTypeBranch,
              PactType.ParallelBranchInterfaces, Finset.empty_union]
            exact Finset.union_subset_union (fun _ h => h)
              (parallelTypeBranches_parallelInterfaces_subset (next :: tail))
          · simpa [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
              using Finset.union_subset_union (fun _ h => h) ih

theorem parallelTypeBranchesSelecting_interfaceScoped
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hScoped : PactType.InterfaceScopedBranches branches) :
    PactType.InterfaceScoped (parallelTypeBranchesSelecting selected branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.InterfaceScoped]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.InterfaceScopedBranches] at hScoped
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hEq, selectedTypeBranch,
              PactType.InterfaceScoped, hScoped.1]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
              hScoped.1]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.InterfaceScoped, hScoped.1,
              parallelTypeBranches_interfaceScoped (next :: tail) hScoped.2]
          · have hRest := ih hScoped.2
            simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
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
theorem buildExclusiveOfferAutomaton_outgoing_else
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
theorem buildExclusiveOfferAutomaton_outgoing_branch
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

def exclusiveOfferEntryStates
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  {childState 0 elseAutomaton.initial} ∪
    branchAutomata.zipIdx.foldl (fun states indexed =>
      states ∪ {childState (indexed.2 + 1) indexed.1.2.initial}) ∅

/- The direct offers stored at an exclusive-offer root are exactly its branch
heads.  Waiting edges only repeat a subset of these heads. -/
theorem buildExclusiveOfferAutomaton_offersAt_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hActions : branchAutomata.map Prod.fst = branches.map Prod.fst)
    (hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.offersAt .root = typeBranchActions branches := by
  classical
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseAutomaton branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  ext action
  constructor
  · intro hOffer
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hOffer
    rcases hOffer with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, fragment, buildExclusiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union] at hEdge
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
      rcases hBranch with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨environment, _, rfl⟩
        simp only at hSource
        cases hSource
        simp [AutomatonConstructionLabel.semantic, TypeLabel.message]
          at hOffer
        subst action
        have hEntry : indexed.1 ∈ branchAutomata := by
          have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
            List.mem_map_of_mem hIndexed
          simpa using hMapped
        have hAction : indexed.1.1 ∈ branchAutomata.map Prod.fst :=
          List.mem_map.mpr ⟨indexed.1, hEntry, rfl⟩
        rw [hActions] at hAction
        simpa [typeBranchActions] using hAction
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      have hWaiting : action ∈
          (environment.future.image typeNeed) ∩ typeBranchActions branches := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hOffer
      exact (Finset.mem_inter.mp hWaiting).2
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _, rfl⟩
      simp at hOffer
  · intro hAction
    have hBranchAction : action ∈ branches.map Prod.fst := by
      simpa [typeBranchActions] using hAction
    rw [← hActions] at hBranchAction
    rcases List.mem_map.mp hBranchAction with
      ⟨entry, hEntry, hEntryAction⟩
    have hIndexedFields := List.mem_iff_getElem.mp hEntry
    rcases hIndexedFields with ⟨index, hBound, hValue⟩
    have hZipBound : index < branchAutomata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ branchAutomata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    have hEntryAction' : entry.1 = action := hEntryAction
    let environment : TypeEnvironment :=
      { immediate := {typeNeed action}, future := ∅, clock := false }
    have hLocal : environment ∈ signature.localEnvironments := by
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image]
      right
      refine ⟨{typeNeed action}, ?_, ∅, by simp, rfl⟩
      intro needed hNeeded
      simp only [Finset.mem_singleton] at hNeeded
      subst needed
      rw [← hEntryAction']
      exact hAvailable entry hEntry
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible (TypeLabel.message action.1 action.2)
        current := {action}
        future := .at (childState (index + 1) entry.2.initial) ∅
        target := childState (index + 1) entry.2.initial }
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [pending, fragment, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      left
      left
      right
      rw [mem_foldl_union_iff]
      right
      refine ⟨(entry, index), hIndexed, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨hLocal, ?_⟩, ?_⟩
      · constructor
        · simp [environment, hEntryAction']
        · change typeBranchNeeds branches ∩ ∅ = ∅
          simp
      · simp [edge, hEntryAction']
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.message]

/- Every same-cycle reference from the exclusive-offer root is either its
waiting self-reference or one of the declared child entries. -/
theorem buildExclusiveOfferAutomaton_root_references_upper
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.referencedStates .root ⊆
      insert .root (exclusiveOfferEntryStates elseAutomaton branchAutomata) := by
  classical
  dsimp only
  intro target hTarget
  unfold PendingAutomaton.referencedStates at hTarget
  simp only [Finset.mem_biUnion, Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
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
    rcases hBranch with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      have hTarget : target =
          childState (indexed.2 + 1) indexed.1.2.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.message]
          using hReference
      subst target
      simp only [Finset.mem_insert]
      right
      rw [exclusiveOfferEntryStates, Finset.mem_union,
        mem_foldl_union_iff]
      right
      right
      exact ⟨indexed, hIndexed, by simp⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = .root := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    exact Finset.mem_insert.mpr (Or.inl hTarget)
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 0 elseAutomaton.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    simp [exclusiveOfferEntryStates]

/- Every declared exclusive-offer child entry is referenced from the fresh
root.  Branch availability follows from membership of the complementary
action in the local environment alphabet. -/
theorem buildExclusiveOfferAutomaton_entries_referenced
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    exclusiveOfferEntryStates elseAutomaton branchAutomata ⊆
      pending.referencedStates .root := by
  classical
  dsimp only
  intro target hTarget
  unfold exclusiveOfferEntryStates at hTarget
  simp only [Finset.mem_union, Finset.mem_singleton] at hTarget
  rcases hTarget with rfl | hBranchTarget
  · let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · constructor <;>
          change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  · rw [mem_foldl_union_iff] at hBranchTarget
    rcases hBranchTarget with hEmpty |
      ⟨indexed, hIndexed, hBranchTarget⟩
    · simp at hEmpty
    simp only [Finset.mem_singleton] at hBranchTarget
    subst target
    have hEntry : indexed.1 ∈ branchAutomata := by
      have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem hIndexed
      simpa using hMapped
    let environment : TypeEnvironment :=
      { immediate := {typeNeed indexed.1.1}, future := ∅, clock := false }
    have hLocal : environment ∈ signature.localEnvironments := by
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image]
      right
      refine ⟨{typeNeed indexed.1.1}, ?_, ∅, by simp, rfl⟩
      simpa using hAvailable indexed.1 hEntry
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible
          (TypeLabel.message indexed.1.1.1 indexed.1.1.2)
        current := {indexed.1.1}
        future := .at
          (childState (indexed.2 + 1) indexed.1.2.initial) ∅
        target := childState (indexed.2 + 1) indexed.1.2.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      right
      rw [mem_foldl_union_iff]
      right
      refine ⟨indexed, hIndexed, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨hLocal, ?_⟩, rfl⟩
      simp [environment]
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.message]

/- The root menu is the syntactic branch-head set union the complete menus of
the else entry and every branch entry.  Optional waiting self-references do
not contribute an additional component. -/
private theorem buildExclusiveOfferAutomaton_computeFuture_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hActions : branchAutomata.map Prod.fst = branches.map Prod.fst)
    (hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeBranchActions branches ∪
        (exclusiveOfferEntryStates elseAutomaton branchAutomata).biUnion
          (computeFuture pending) := by
  classical
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseAutomaton branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildExclusiveOfferAutomaton_futureTargetsInStates signature branches
      elseAutomaton branchAutomata hElseTargets hBranchTargets hElseInitial
        hBranchInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildExclusiveOfferAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = typeBranchActions branches := by
    simpa [pending, fragment] using
      buildExclusiveOfferAutomaton_offersAt_root signature branches
        elseAutomaton branchAutomata hActions hAvailable
  have hUpper : pending.referencedStates .root ⊆
      insert .root (exclusiveOfferEntryStates elseAutomaton branchAutomata) := by
    simpa [pending, fragment] using
      buildExclusiveOfferAutomaton_root_references_upper signature branches
        elseAutomaton branchAutomata
  have hEntries : exclusiveOfferEntryStates elseAutomaton branchAutomata ⊆
      pending.referencedStates .root := by
    simpa [pending, fragment] using
      buildExclusiveOfferAutomaton_entries_referenced signature branches
        elseAutomaton branchAutomata hAvailable
  change computeFuture pending .root =
    typeBranchActions branches ∪
      (exclusiveOfferEntryStates elseAutomaton branchAutomata).biUnion
        (computeFuture pending)
  rw [computeFuture_eq_offersAt_union_biUnion pending .root
    (exclusiveOfferEntryStates elseAutomaton branchAutomata) hClosed hRoot
      hUpper hEntries, hOffers]

private theorem buildExclusiveOfferAutomaton_computeFuture_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState)
    (hTargets : elseAutomaton.FutureTargetsInStates)
    (hState : state ∈ elseAutomaton.states)
    (hCard : elseAutomaton.states.card ≤
      (buildExclusiveOfferAutomaton signature branches elseAutomaton
        branchAutomata).states.card) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    computeFuture { states := fragment.states, edges := fragment.edges }
        (childState 0 state) =
      computeFuture
        { states := elseAutomaton.states, edges := elseAutomaton.edges }
        state := by
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseAutomaton branchAutomata
  apply taggedChild_computeFuture_of_outgoing
    ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
    ({ states := elseAutomaton.states, edges := elseAutomaton.edges } :
      PendingAutomaton) 0
  · exact buildExclusiveOfferAutomaton_outgoing_else signature branches
      elseAutomaton branchAutomata
  · exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
      elseAutomaton hTargets
  · exact hState
  · exact hCard

private theorem buildExclusiveOfferAutomaton_computeFuture_branch
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState)
    (hTargets : entry.2.FutureTargetsInStates)
    (hState : state ∈ entry.2.states)
    (hCard : entry.2.states.card ≤
      (buildExclusiveOfferAutomaton signature branches elseAutomaton
        branchAutomata).states.card) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    computeFuture { states := fragment.states, edges := fragment.edges }
        (childState (index + 1) state) =
      computeFuture { states := entry.2.states, edges := entry.2.edges }
        state := by
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseAutomaton branchAutomata
  apply taggedChild_computeFuture_of_outgoing
    ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
    ({ states := entry.2.states, edges := entry.2.edges } : PendingAutomaton)
    (index + 1)
  · exact buildExclusiveOfferAutomaton_outgoing_branch signature branches
      elseAutomaton branchAutomata index entry hEntry
  · exact PendingAutomaton.referencesClosed_of_futureTargetsInStates entry.2
      hTargets
  · exact hState
  · exact hCard

private theorem mem_futureOfferBranchFold_iff
    (action : BareMessage) (branches : List (BareMessage × PactType))
    (initial : Finset BareMessage) :
    action ∈ branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial ↔
      action ∈ initial ∨ ∃ branch ∈ branches,
        action = branch.1 ∨ action ∈ typeFutureOffers branch.2 := by
  induction branches generalizing initial with
  | nil => simp
  | cons branch rest ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, Finset.mem_singleton, List.mem_cons]
      aesop

private theorem typeFutureOffers_parallelTypeBranches_eq_fold :
    ∀ branches : List (BareMessage × PactType),
      typeFutureOffers (parallelTypeBranches branches) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
  intro branches
  induction branches with
  | nil =>
      simp [parallelTypeBranches, typeFutureOffers, typeFutureOffersFuel]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          rw [show parallelTypeBranches [branch] =
              singletonTypeXOffer branch by rfl,
            show singletonTypeXOffer branch =
              PactType.xoffer .skip [branch] by rfl,
            typeFutureOffers_xoffer]
          simp [typeFutureOffers, typeFutureOffersFuel]
      | cons next tail =>
          have hHideEmpty : ∀ offers : Finset BareMessage,
              hideTypeOffers ∅ offers = offers := by
            intro offers
            apply Finset.filter_eq_self.mpr
            simp
          have hSingleton : typeFutureOffers (singletonTypeXOffer branch) =
              {branch.1} ∪ typeFutureOffers branch.2 := by
            rw [show singletonTypeXOffer branch =
                PactType.xoffer .skip [branch] by rfl,
              typeFutureOffers_xoffer]
            simp [typeFutureOffers, typeFutureOffersFuel]
          rw [show parallelTypeBranches (branch :: next :: tail) =
              .par (singletonTypeXOffer branch)
                (parallelTypeBranches (next :: tail)) ∅ by rfl,
            typeFutureOffers_parallel, hHideEmpty, hSingleton, ih]
          ext action
          rw [Finset.mem_union,
            mem_futureOfferBranchFold_iff action (next :: tail) ∅,
            mem_futureOfferBranchFold_iff action (branch :: next :: tail) ∅]
          simp

private theorem typeFutureOffers_message (msg : MessageId) (dir : MessageDir) :
    typeFutureOffers (.message msg dir) = {(msg, dir)} := by
  simp [typeFutureOffers, typeFutureOffersFuel]

/-- Forcing one singleton branch mandatory does not change its future-offer
contribution: `selectedTypeBranch` reports exactly the same head-plus-
continuation menu as `singletonTypeXOffer` would, since `.message` always
completes before the next clock. -/
private theorem typeFutureOffers_selectedTypeBranch_eq_singleton
    (branch : BareMessage × PactType) :
    typeFutureOffers (selectedTypeBranch branch) =
      {branch.1} ∪ typeFutureOffers branch.2 := by
  rw [selectedTypeBranch, typeFutureOffers_sequence]
  rcases branch with ⟨action, processType⟩
  simp only [PactType.CanCompleteBeforeTock, if_true]
  rw [typeFutureOffers_message]

private theorem typeFutureOffers_parallelTypeBranchesSelecting_eq_fold
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      typeFutureOffers (parallelTypeBranchesSelecting selected branches) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
  intro branches
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, typeFutureOffers,
        typeFutureOffersFuel]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          by_cases hSelected : branch = selected
          · rw [show parallelTypeBranchesSelecting selected [branch] =
                selectedTypeBranch branch by
              simp [parallelTypeBranchesSelecting, hSelected]]
            rw [typeFutureOffers_selectedTypeBranch_eq_singleton]
            simp
          · rw [show parallelTypeBranchesSelecting selected [branch] =
                singletonTypeXOffer branch by
              simp [parallelTypeBranchesSelecting, hSelected]]
            rw [show singletonTypeXOffer branch =
                PactType.xoffer .skip [branch] by rfl,
              typeFutureOffers_xoffer]
            simp [typeFutureOffers, typeFutureOffersFuel]
      | cons next tail =>
          have hHideEmpty : ∀ offers : Finset BareMessage,
              hideTypeOffers ∅ offers = offers := by
            intro offers
            apply Finset.filter_eq_self.mpr
            simp
          by_cases hSelected : branch = selected
          · rw [show parallelTypeBranchesSelecting selected
                (branch :: next :: tail) =
              .par (selectedTypeBranch branch)
                (parallelTypeBranches (next :: tail)) ∅ by
              simp [parallelTypeBranchesSelecting, hSelected]]
            rw [typeFutureOffers_parallel, hHideEmpty,
              typeFutureOffers_selectedTypeBranch_eq_singleton,
              typeFutureOffers_parallelTypeBranches_eq_fold]
            ext action
            rw [Finset.mem_union,
              mem_futureOfferBranchFold_iff action (next :: tail) ∅,
              mem_futureOfferBranchFold_iff action (branch :: next :: tail) ∅]
            simp
          · rw [show parallelTypeBranchesSelecting selected
                (branch :: next :: tail) =
              .par (singletonTypeXOffer branch)
                (parallelTypeBranchesSelecting selected (next :: tail)) ∅ by
              simp [parallelTypeBranchesSelecting, hSelected]]
            have hSingleton : typeFutureOffers (singletonTypeXOffer branch) =
                {branch.1} ∪ typeFutureOffers branch.2 := by
              rw [show singletonTypeXOffer branch =
                  PactType.xoffer .skip [branch] by rfl,
                typeFutureOffers_xoffer]
              simp [typeFutureOffers, typeFutureOffersFuel]
            rw [typeFutureOffers_parallel, hHideEmpty, hSingleton, ih]
            ext action
            rw [Finset.mem_union,
              mem_futureOfferBranchFold_iff action (next :: tail) ∅,
              mem_futureOfferBranchFold_iff action (branch :: next :: tail) ∅]
            simp

theorem supportedBranchNeed_mem_localEnvironmentActions
    (signature : TypeAlphabet) : ∀ branches,
    signature.SupportsBranches branches → ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions := by
  intro branches hSupports branch hBranch
  have hLocalAction : branch.1 ∈ signature.localActions := by
    induction branches with
    | nil => simp at hBranch
    | cons head rest ih =>
        rcases head with ⟨headAction, headType⟩
        rcases headAction with ⟨headMessage, headDirection⟩
        simp only [TypeAlphabet.SupportsBranches.eq_2] at hSupports
        simp only [List.mem_cons] at hBranch
        rcases hBranch with rfl | hBranch
        · rcases hSupports.1 with hBoundary | hInterface
          · exact Finset.mem_union_left _ hBoundary
          · apply Finset.mem_union_right
            simp only [TypeAlphabet.interfaceActions, Finset.mem_biUnion]
            refine ⟨headMessage, hInterface, ?_⟩
            cases headDirection <;> simp
        · exact ih hSupports.2.2 hBranch
  exact Finset.mem_image.mpr ⟨branch.1, hLocalAction, rfl⟩

/- The two tagged child families of a conjunctive offer are disjoint from all
fresh root edges. -/
theorem buildConjunctiveOfferAutomaton_outgoing_child
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
def conjunctiveOfferEntryStates
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    Finset TypeAutomatonState :=
  {childState 1 elseAutomaton.initial} ∪
    if branches = [] then ∅ else {childState 0 conjunction.initial}

theorem buildConjunctiveOfferAutomaton_offersAt_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.offersAt .root = typeBranchActions branches := by
  classical
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  ext action
  constructor
  · intro hOffer
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hOffer
    rcases hOffer with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union] at hEdge
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
      simp at hOffer
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      have hWaiting : action ∈
          (environment.future.image typeNeed) ∩ typeBranchActions branches := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hOffer
      exact (Finset.mem_inter.mp hWaiting).2
    · simp only [Finset.mem_image, Finset.mem_filter] at hElse
      rcases hElse with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hOffer
  · intro hAction
    let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := typeBranchActions branches
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [pending, fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · constructor <;>
          change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent,
        hAction]

theorem buildConjunctiveOfferAutomaton_root_references_upper
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.referencedStates .root ⊆
      insert .root
        (conjunctiveOfferEntryStates branches elseAutomaton conjunction) := by
  classical
  dsimp only
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
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
    rcases hEnabled with ⟨environment, hConditions, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 0 conjunction.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    have hNonempty : branches ≠ [] := by
      intro hEmpty
      subst branches
      simp [typeBranchNeeds] at hConditions
    simp [conjunctiveOfferEntryStates, hNonempty]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = .root := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    exact Finset.mem_insert.mpr (Or.inl hTarget)
  · simp only [Finset.mem_image, Finset.mem_filter] at hElse
    rcases hElse with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 1 elseAutomaton.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    simp [conjunctiveOfferEntryStates]

theorem buildConjunctiveOfferAutomaton_entries_referenced
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    conjunctiveOfferEntryStates branches elseAutomaton conjunction ⊆
      pending.referencedStates .root := by
  classical
  dsimp only
  intro target hTarget
  by_cases hEmpty : branches = []
  · subst branches
    simp only [conjunctiveOfferEntryStates, ↓reduceIte, Finset.union_empty,
      Finset.mem_singleton] at hTarget
    subst target
    let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · simp [typeBranchNeeds, environment, TypeEnvironment.empty]
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  · simp only [conjunctiveOfferEntryStates, hEmpty, if_false,
      Finset.mem_union, Finset.mem_singleton] at hTarget
    rcases hTarget with hElse | hConjunction
    · subst target
      let environment : TypeEnvironment := .empty
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := typeBranchActions branches
          future := .at (childState 1 elseAutomaton.initial) ∅
          target := childState 1 elseAutomaton.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        right
        apply Finset.mem_image.mpr
        refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
        · simp [environment, TypeEnvironment.empty,
            TypeAlphabet.localEnvironments]
        · constructor <;>
            change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
    · subst target
      rcases List.exists_cons_of_ne_nil hEmpty with ⟨branch, rest, rfl⟩
      let environment : TypeEnvironment :=
        { immediate := {typeNeed branch.1}, future := ∅, clock := false }
      have hLocal : environment ∈ signature.localEnvironments := by
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨{typeNeed branch.1}, ?_, ∅, by simp, rfl⟩
        simpa using hAvailable branch (by simp)
      have hEnabled : typeBranchNeeds (branch :: rest) ∩
          environment.immediate ≠ ∅ := by
        intro hIntersection
        have hMember : typeNeed branch.1 ∈
            typeBranchNeeds (branch :: rest) ∩ environment.immediate := by
          simp [typeBranchNeeds, environment]
        rw [hIntersection] at hMember
        simp at hMember
      let edge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 conjunction.initial) ∅
          target := childState 0 conjunction.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [buildConjunctiveOfferAutomaton,
          finishAutomatonFragment, Finset.mem_union]
        left
        left
        right
        exact Finset.mem_image.mpr ⟨environment,
          Finset.mem_filter.mpr ⟨hLocal, hEnabled⟩, rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]

private theorem buildConjunctiveOfferAutomaton_computeFuture_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : conjunction.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : conjunction.initial ∈ conjunction.states) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeBranchActions branches ∪
        (conjunctiveOfferEntryStates branches elseAutomaton conjunction).biUnion
          (computeFuture pending) := by
  classical
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildConjunctiveOfferAutomaton_futureTargetsInStates signature
      branches elseAutomaton conjunction hElseTargets hConjunctionTargets
        hElseInitial hConjunctionInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = typeBranchActions branches := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_offersAt_root signature branches
        elseAutomaton conjunction
  have hUpper : pending.referencedStates .root ⊆ insert .root
      (conjunctiveOfferEntryStates branches elseAutomaton conjunction) := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_root_references_upper signature branches
        elseAutomaton conjunction
  have hEntries : conjunctiveOfferEntryStates branches elseAutomaton
      conjunction ⊆ pending.referencedStates .root := by
    simpa [pending, fragment] using
      buildConjunctiveOfferAutomaton_entries_referenced signature branches
        elseAutomaton conjunction hAvailable
  change computeFuture pending .root = typeBranchActions branches ∪
    (conjunctiveOfferEntryStates branches elseAutomaton conjunction).biUnion
      (computeFuture pending)
  rw [computeFuture_eq_offersAt_union_biUnion pending .root
    (conjunctiveOfferEntryStates branches elseAutomaton conjunction) hClosed
      hRoot hUpper hEntries, hOffers]

private theorem buildConjunctiveOfferAutomaton_computeFuture_child
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (index : Nat) (child : AutomatonFragment)
    (hIndex : (index = 0 ∧ child = conjunction) ∨
      (index = 1 ∧ child = elseAutomaton))
    (state : TypeAutomatonState)
    (hTargets : child.FutureTargetsInStates)
    (hState : state ∈ child.states)
    (hCard : child.states.card ≤
      (buildConjunctiveOfferAutomaton signature branches elseAutomaton
        conjunction).states.card) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    computeFuture { states := fragment.states, edges := fragment.edges }
        (childState index state) =
      computeFuture { states := child.states, edges := child.edges } state := by
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseAutomaton conjunction
  apply taggedChild_computeFuture_of_outgoing
    ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
    ({ states := child.states, edges := child.edges } : PendingAutomaton) index
  · exact buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseAutomaton conjunction index child hIndex
  · exact PendingAutomaton.referencesClosed_of_futureTargetsInStates child
      hTargets
  · exact hState
  · exact hCard

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

/- Every edge from the else child of a conjunctive offer is exactly the
corresponding tagged child edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = childState 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
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
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
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
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      left
      left
      exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
    · simp [childPendingEdge, childState, hChildSource]

/- Every edge from an indexed selected-conjunction child of a conjunctive
offer is exactly the corresponding tagged child edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[index]? = some entry)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = childState (index + 1) state ↔
      ∃ childEdge ∈ entry.2.edges,
        childEdge.source = state ∧
          edge = childPendingEdge (index + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
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
        have hIndexedEntry : selectedConjunctions[indexed.2]? =
            some indexed.1 := by
          rw [List.getElem?_eq_getElem hBound, ← hValue]
        have hEntryEq : indexed.1 = entry := by
          have hOptions := congrArg
            (fun position => selectedConjunctions[position]?) hIndex
          change selectedConjunctions[indexed.2]? =
            selectedConjunctions[index]? at hOptions
          rw [hIndexedEntry, hEntry] at hOptions
          exact Option.some.inj hOptions
        rw [hEntryEq] at hChildEdge
        rw [hIndex] at hEquality
        exact ⟨childEdge, hChildEdge, hInnerSource, hEquality.symm⟩
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
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
    have hZipBound : index < selectedConjunctions.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ selectedConjunctions.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := selectedConjunctions) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
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

def selectedConjunctiveOfferEntryStates
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  {childState 0 elseAutomaton.initial} ∪
    selectedConjunctions.zipIdx.foldl (fun states indexed =>
      states ∪ {childState (indexed.2 + 1) indexed.1.2.initial}) ∅

/- The direct offers stored at a conjunctive-offer root are exactly its
branch heads: every enabled witness fires immediately without waiting for
the remaining conjuncts, so no extra `needs ∩ future = ∅` side condition is
needed at the enabling edge (unlike the exclusive-offer branch edges). -/
theorem buildSelectedConjunctiveOfferAutomaton_offersAt_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.offersAt .root ⊆ typeBranchActions branches := by
  classical
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseAutomaton selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  dsimp only
  intro action hOffer
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hOffer
  rcases hOffer with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
  simp only [pending, fragment, buildSelectedConjunctiveOfferAutomaton,
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
      simp only at hSource
      cases hSource
      simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hOffer
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hWaiting : action ∈
        (environment.future.image typeNeed) ∩ typeBranchActions branches := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hOffer
    exact (Finset.mem_inter.mp hWaiting).2
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent] using hOffer

/- Whenever some environment leaves every branch neither immediately nor
eventually enabled, the else edge exposes the full branch-head menu directly
at the root.  The idle environment always witnesses this. -/
theorem buildSelectedConjunctiveOfferAutomaton_offersAt_root_supset
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    typeBranchActions branches ⊆ pending.offersAt .root := by
  classical
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseAutomaton selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  dsimp only
  intro action hAction
  let environment : TypeEnvironment := .empty
  have hLocal : environment ∈ signature.localEnvironments := by
    simp [environment, TypeEnvironment.empty, TypeAlphabet.localEnvironments]
  let edge : PendingAutomatonEdge :=
    { source := .root
      environment := environment
      label := .visible TypeLabel.silent
      current := typeBranchActions branches
      future := .at (childState 0 elseAutomaton.initial) ∅
      target := childState 0 elseAutomaton.initial }
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
  refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
  · simp only [pending, fragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union]
    right
    apply Finset.mem_image.mpr
    refine ⟨environment, Finset.mem_filter.mpr ⟨hLocal, ?_, ?_⟩, rfl⟩
    · change typeBranchNeeds branches ∩ environment.immediate = ∅
      simp [environment, TypeEnvironment.empty]
    · change typeBranchNeeds branches ∩ environment.future = ∅
      simp [environment, TypeEnvironment.empty]
  · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent, hAction]

/- Every same-cycle reference from the conjunctive-offer root is either its
waiting self-reference or one of the declared child entries. -/
theorem buildSelectedConjunctiveOfferAutomaton_root_references_upper
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.referencedStates .root ⊆
      insert .root
        (selectedConjunctiveOfferEntryStates elseAutomaton
          selectedConjunctions) := by
  classical
  dsimp only
  intro target hTarget
  unfold PendingAutomaton.referencedStates at hTarget
  simp only [Finset.mem_biUnion, Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
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
    rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hSource
      cases hSource
      have hTarget : target =
          childState (indexed.2 + 1) indexed.1.2.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hReference
      subst target
      simp only [Finset.mem_insert]
      right
      rw [selectedConjunctiveOfferEntryStates, Finset.mem_union,
        mem_foldl_union_iff]
      right
      right
      exact ⟨indexed, hIndexed, by simp⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = .root := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    exact Finset.mem_insert.mpr (Or.inl hTarget)
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hSource
    cases hSource
    have hTarget : target = childState 0 elseAutomaton.initial := by
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
    subst target
    simp [selectedConjunctiveOfferEntryStates]

/- Every declared conjunctive-offer child entry is referenced from the fresh
root.  Branch availability follows from membership of the complementary
action in the local environment alphabet. -/
theorem buildSelectedConjunctiveOfferAutomaton_entries_referenced
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    selectedConjunctiveOfferEntryStates elseAutomaton selectedConjunctions ⊆
      pending.referencedStates .root := by
  classical
  dsimp only
  intro target hTarget
  unfold selectedConjunctiveOfferEntryStates at hTarget
  simp only [Finset.mem_union, Finset.mem_singleton] at hTarget
  rcases hTarget with rfl | hBranchTarget
  · let environment : TypeEnvironment := .empty
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := typeBranchActions branches
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp [environment, TypeEnvironment.empty,
          TypeAlphabet.localEnvironments]
      · constructor <;>
          change typeBranchNeeds branches ∩ ∅ = ∅ <;> simp
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]
  · rw [mem_foldl_union_iff] at hBranchTarget
    rcases hBranchTarget with hEmpty |
      ⟨indexed, hIndexed, hBranchTarget⟩
    · simp at hEmpty
    simp only [Finset.mem_singleton] at hBranchTarget
    subst target
    have hEntry : indexed.1 ∈ selectedConjunctions := by
      have hMapped : indexed.1 ∈ selectedConjunctions.zipIdx.map Prod.fst :=
        List.mem_map_of_mem hIndexed
      simpa using hMapped
    let environment : TypeEnvironment :=
      { immediate := {typeNeed indexed.1.1}, future := ∅, clock := false }
    have hLocal : environment ∈ signature.localEnvironments := by
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image]
      right
      refine ⟨{typeNeed indexed.1.1}, ?_, ∅, by simp, rfl⟩
      simpa using hAvailable indexed.1 hEntry
    let edge : PendingAutomatonEdge :=
      { source := .root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at
          (childState (indexed.2 + 1) indexed.1.2.initial) ∅
        target := childState (indexed.2 + 1) indexed.1.2.initial }
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter]
    refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      right
      rw [mem_foldl_union_iff]
      right
      refine ⟨indexed, hIndexed, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨environment, Finset.mem_filter.mpr ⟨hLocal, ?_⟩, rfl⟩
      simp [environment]
    · simp [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent]

/- The root menu is the syntactic branch-head set union the complete menus of
the else entry and every selected-conjunction entry.  Optional waiting
self-references do not contribute an additional component. -/
private theorem buildSelectedConjunctiveOfferAutomaton_computeFuture_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeBranchActions branches ∪
        (selectedConjunctiveOfferEntryStates elseAutomaton
          selectedConjunctions).biUnion (computeFuture pending) := by
  classical
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseAutomaton selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
      signature branches elseAutomaton selectedConjunctions hElseTargets
        hConjunctionTargets hElseInitial hConjunctionInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hOffers : pending.offersAt .root = typeBranchActions branches := by
    apply Finset.Subset.antisymm
    · simpa [pending, fragment] using
        buildSelectedConjunctiveOfferAutomaton_offersAt_root signature
          branches elseAutomaton selectedConjunctions
    · simpa [pending, fragment] using
        buildSelectedConjunctiveOfferAutomaton_offersAt_root_supset signature
          branches elseAutomaton selectedConjunctions
  have hUpper : pending.referencedStates .root ⊆
      insert .root (selectedConjunctiveOfferEntryStates elseAutomaton
        selectedConjunctions) := by
    simpa [pending, fragment] using
      buildSelectedConjunctiveOfferAutomaton_root_references_upper signature
        branches elseAutomaton selectedConjunctions
  have hEntries : selectedConjunctiveOfferEntryStates elseAutomaton
      selectedConjunctions ⊆ pending.referencedStates .root := by
    simpa [pending, fragment] using
      buildSelectedConjunctiveOfferAutomaton_entries_referenced signature
        branches elseAutomaton selectedConjunctions hAvailable
  change computeFuture pending .root =
    typeBranchActions branches ∪
      (selectedConjunctiveOfferEntryStates elseAutomaton
        selectedConjunctions).biUnion (computeFuture pending)
  rw [computeFuture_eq_offersAt_union_biUnion pending .root
    (selectedConjunctiveOfferEntryStates elseAutomaton selectedConjunctions)
      hClosed hRoot hUpper hEntries, hOffers]

/- Root edges of the selected conjunctive-offer builder: an enabled witness
fires silently into its indexed selected-conjunction entry with no direct
current offer (the mandatory message fires one level down, inside the
generated `selectedTypeBranch`); waiting and else edges are unchanged from
the exclusive-offer shape. -/
private theorem buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (∃ indexed ∈ selectedConjunctions.zipIdx,
        env ∈ signature.localEnvironments ∧
          typeNeed indexed.1.1 ∈ env.immediate ∧
          label = TypeLabel.silent ∧
          offers.current = ∅ ∧
          computeFuture pending
              (childState (indexed.2 + 1) indexed.1.2.initial) =
            offers.future ∧
          target = childState (indexed.2 + 1) indexed.1.2.initial) ∨
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
        label = TypeLabel.silent ∧ offers.current = typeBranchActions branches ∧
        computeFuture pending (childState 0 elseAutomaton.initial) =
          offers.future ∧ target = childState 0 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved),
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
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨edgeEnvironment, hConditions, rfl⟩
        left
        simp only [Finset.sdiff_empty] at hFuture
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        subst env
        have hSemanticLabel : label = TypeLabel.silent := by
          have hCongruence :=
            congrArg AutomatonConstructionLabel.semantic hLabel
          simpa using hCongruence.symm
        exact ⟨indexed, hIndexed, hConditions.1, hConditions.2,
          hSemanticLabel, hCurrent.symm, hFuture, hTarget.symm⟩
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
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨edgeEnvironment, hConditions, rfl⟩
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
    · rcases hEnabled with ⟨indexed, hIndexed, hLocal, hImmediate, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at
            (childState (indexed.2 + 1) indexed.1.2.initial) ∅
          target := childState (indexed.2 + 1) indexed.1.2.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        rw [mem_foldl_union_iff]
        right
        exact ⟨indexed, hIndexed, Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr ⟨hLocal, hImmediate⟩, rfl⟩⟩
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

private theorem compileTypeFuel_offer_conjunction_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (selected : BareMessage × PactType) (index : Nat)
    (hEntry : branches[index]? = some selected)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState (index + 1) source) env label offers
            (childState (index + 1) target) ↔
      (compileTypeFuel signature
        (typeCompilationFuel
          (parallelTypeBranchesSelecting selected branches))
        (parallelTypeBranchesSelecting selected branches)).HasResolvedEdge
          source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let selectedFragment := compileTypeFuel signature fuel
    (parallelTypeBranchesSelecting selected branches)
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hSelectedMember : selected ∈ branches := by
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hMember := List.getElem_mem hBound
    simpa [hValue] using hMember
  have hSelectedFuel : TypeCompilationFuelSufficient
      (parallelTypeBranchesSelecting selected branches) fuel := by
    simp only [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
    exact le_max_right _ _
  have hTargets : selectedFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel
      (parallelTypeBranchesSelecting selected branches) hSelectedFuel
  have hAutomatonEntry : selectedConjunctions[index]? =
      some (selected.1, selectedFragment) := by
    simp [selectedConjunctions, selectedFragment, hEntry]
  have hZipEntry : ((selected.1, selectedFragment), index) ∈
      selectedConjunctions.zipIdx := by
    rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < selectedConjunctions.zipIdx.length := by
      simpa using hBound
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := selectedConjunctions) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  have hCard : selectedFragment.states.card ≤ fragment.states.card := by
    have hIndexedSubset : childStates (index + 1) selectedFragment ⊆
        indexedFragmentStates selectedConjunctions := by
      intro state hState
      rw [indexedFragmentStates, mem_foldl_union_iff]
      right
      exact ⟨((selected.1, selectedFragment), index), hZipEntry, hState⟩
    have hSubset : childStates (index + 1) selectedFragment ⊆
        fragment.states := by
      intro state hState
      have hIndexed := hIndexedSubset hState
      simp [fragment, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, hIndexed]
    calc
      selectedFragment.states.card =
          (childStates (index + 1) selectedFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧
          edge.source = childState (index + 1) state ↔
        ∃ childEdge ∈ selectedFragment.edges,
          childEdge.source = state ∧
            edge = childPendingEdge (index + 1) childEdge :=
    buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction signature
      branches elseFragment selectedConjunctions index
      (selected.1, selectedFragment) hAutomatonEntry
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    selectedFragment (index + 1) hOutgoing hTargets hCard source target env
    label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature
    (parallelTypeBranchesSelecting selected branches)
    hSelectedFuel
    (typeCompilationFuel_sufficient
      (parallelTypeBranchesSelecting selected branches))
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, selectedFragment, selectedConjunctions, fuel, hStable]
    using hRaw

private theorem compileTypeFuel_offer_else_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState 0 source) env label offers (childState 0 target) ↔
      (compileTypeFuel signature (typeCompilationFuel elseType) elseType).HasResolvedEdge
        source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hCard : elseFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildSelectedConjunctiveOfferAutomaton,
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
    buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
      elseFragment selectedConjunctions
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    elseFragment 0 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature elseType
    hElseFuel (typeCompilationFuel_sufficient elseType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, selectedConjunctions, fuel, hStable] using hRaw

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
    (selected : BareMessage × PactType) (index : Nat)
    (hEntry : branches[index]? = some selected)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches)).HasResolvedEdge
        (childState (index + 1) source) env label offers target) :
    ∃ childTarget,
      target = childState (index + 1) childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel
            (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches)).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedFragment := compileTypeFuel signature fuel
    (parallelTypeBranchesSelecting selected branches)
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hAutomatonEntry : selectedConjunctions[index]? =
      some (selected.1, selectedFragment) := by
    simp [selectedConjunctions, selectedFragment, hEntry]
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
    (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction signature
      branches elseFragment selectedConjunctions index
      (selected.1, selectedFragment) hAutomatonEntry source
      pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target =
      childState (index + 1) childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_offer_conjunction_child_edge_iff signature elseType
    branches selected index hEntry source childEdge.target env label
    offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_offer_else_child_edge_cases
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
          (typeCompilationFuel elseType) elseType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
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
    (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
      elseFragment selectedConjunctions source pendingEdge).mp
      ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 0 childEdge.target := by
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
  intro hCanonical residual residual' state env label offers hRelated
    hLocalEnvironment
  have hElseCanonical : elseType.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hBranchesCanonical : PactType.EntryCanonicalBranches branches := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
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
            have hResidualCanonical : residual'.EntryCanonical :=
              PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation_of_canonical signature fuel
                residual' hBranchFuel
                (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                  hResidualCanonical)
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
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
              compileTypeFuel_initial_relation_of_canonical signature fuel
                elseType hElseFuel
                (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                  hElseCanonical)
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
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
            have hComputed := hFuture hCanonical _ _ hSourceRelation
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
          have hBranchCanonical : branch.2.EntryCanonical :=
            PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation_of_canonical signature fuel
              branch.2 hBranchFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hBranchCanonical)
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
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
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
          have hComputed := hFuture hCanonical _ _ hSourceRelation
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
            compileTypeFuel_initial_relation_of_canonical signature fuel
              elseType hElseFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hElseCanonical)
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
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
        rcases (hElseStep hElseCanonical hChildRelated
            hLocalEnvironment).mp hStep with
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
            exact (hElseStep hElseCanonical hChildRelated
              hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      have hBranchTypeCanonical : branchType.EntryCanonical :=
        PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
      constructor
      · intro hSemanticStep
        rcases (hStep hBranchTypeCanonical hChildRelated
            hLocalEnvironment).mp hSemanticStep with
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
            exact (hStep hBranchTypeCanonical hChildRelated
              hLocalEnvironment).mpr
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
  intro hCanonical residual residual' state env label offers hRelated
    hLocalEnvironment hAvoids
  have hElseCanonical : elseType.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hBranchesCanonical : PactType.EntryCanonicalBranches branches := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
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
            have hResidualCanonical : residual'.EntryCanonical :=
              PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation_of_canonical signature fuel
                residual' hBranchFuel
                (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                  hResidualCanonical)
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
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
              compileTypeFuel_initial_relation_of_canonical signature fuel
                elseType hElseFuel
                (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                  hElseCanonical)
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
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
            have hComputed := hFuture hCanonical _ _ hSourceRelation
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
          have hBranchCanonical : branch.2.EntryCanonical :=
            PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation_of_canonical signature fuel
              branch.2 hBranchFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hBranchCanonical)
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
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
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
          have hComputed := hFuture hCanonical _ _ hSourceRelation
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
            compileTypeFuel_initial_relation_of_canonical signature fuel
              elseType hElseFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hElseCanonical)
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
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
        rcases (hElseStep hElseCanonical hChildRelated hLocalEnvironment
            hAvoidsElse).mp hStep with
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
            exact (hElseStep hElseCanonical hChildRelated hLocalEnvironment
              hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationScopedFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      have hBranchTypeCanonical : branchType.EntryCanonical :=
        PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
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
        rcases (hStep hBranchTypeCanonical hChildRelated hLocalEnvironment
            hAvoidsBranch).mp hSemanticStep with
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
            exact (hStep hBranchTypeCanonical hChildRelated hLocalEnvironment
              hAvoidsBranch).mpr
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
      (.xoffer elseType branches))
    (hCanonical : (PactType.xoffer elseType branches).EntryCanonical) :
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
    branches hElseStep hBranchStep hFuture hCanonical (residual := residual)
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

/-- Whole-fragment future correctness for exclusive offers, composed from the
else continuation and every indexed branch continuation.  The operational
menu on the right remains the syntax-derived `typeFutureOffers_xoffer`. -/
theorem compilationFutureCorrect_xoffer_of_children
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.SupportsBranches branches)
    (hElseFuture : CompilationFutureCorrect signature elseType)
    (hBranchFuture : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationFutureCorrect signature branchType) :
    CompilationFutureCorrect signature (.xoffer elseType branches) := by
  classical
  intro hCanonical state residual hRelated
  have hElseCanonical : elseType.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hBranchesCanonical : PactType.EntryCanonicalBranches branches := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hSupportedLocal : ∀ rest : List (BareMessage × PactType),
      signature.SupportsBranches rest → ∀ branch ∈ rest,
        branch.1 ∈ signature.localActions := by
    intro rest hRest
    induction rest with
    | nil => simp
    | cons head tail ih =>
        rcases head with ⟨headAction, headType⟩
        rcases headAction with ⟨headMessage, headDirection⟩
        intro branch hBranch
        simp only [TypeAlphabet.SupportsBranches.eq_2] at hRest
        simp only [List.mem_cons] at hBranch
        rcases hBranch with rfl | hBranch
        · rcases hRest.1 with hBoundary | hInterface
          · exact Finset.mem_union_left _ hBoundary
          · apply Finset.mem_union_right
            simp only [TypeAlphabet.interfaceActions,
              Finset.mem_biUnion]
            refine ⟨headMessage, hInterface, ?_⟩
            cases headDirection <;> simp
        · exact ih hRest.2.2 branch hBranch
  have hAvailableOriginal : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions := by
    intro branch hBranch
    have hSupportedAction : branch.1 ∈ signature.localActions :=
      hSupportedLocal branches hSupports branch hBranch
    exact Finset.mem_image.mpr ⟨branch.1, hSupportedAction, rfl⟩
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailableOriginal branch hBranch
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
      (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel])
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      hBranchFuel
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
      (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel])
    exact compileTypeFuel_initial_mem signature fuel branch.2 hBranchFuel
  cases hRelated with
  | xoffer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (exclusiveOfferEntryStates elseFragment branchAutomata).biUnion
              (computeFuture pending) := by
        simpa [pending, fragment] using
          buildExclusiveOfferAutomaton_computeFuture_root signature branches
            elseFragment branchAutomata (by simp [branchAutomata]) hAvailable
              hElseTargets hBranchTargets hElseInitial hBranchInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding := buildExclusiveOfferAutomaton_computeFuture_else
        signature branches elseFragment branchAutomata elseFragment.initial
          hElseTargets hElseInitial hElseCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation_of_canonical signature elseType
            (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
              hElseCanonical)
      have hElseSemantic := hElseFuture hElseCanonical elseFragment.initial
        elseType hElseRelation
      have hElseMenu : computeFuture pending
          (childState 0 elseFragment.initial) =
          typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        simpa [pending, fragment] using hElseEmbedding.trans hStandalone
      have hIndexedMenu : ∀ indexed ∈ branchAutomata.zipIdx,
          ∃ branchType,
            branches[indexed.2]? = some (indexed.1.1, branchType) ∧
              computeFuture pending
                  (childState (indexed.2 + 1) indexed.1.2.initial) =
                typeFutureOffers branchType := by
        intro indexed hIndexed
        rcases indexed with ⟨entry, index⟩
        have hFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
        rcases hFields with ⟨hAutomatonBound, hValue⟩
        have hBound : index < branches.length := by
          simpa [branchAutomata] using hAutomatonBound
        let branch := branches[index]
        have hBranchEntry : branches[index]? = some branch := by
          rw [List.getElem?_eq_getElem hBound]
        let branchFragment := compileTypeFuel signature fuel branch.2
        have hExpectedEntry : branchAutomata[index]? =
            some (branch.1, branchFragment) := by
          simp [branchAutomata, branchFragment, hBranchEntry]
        have hActualEntry : branchAutomata[index]? = some entry := by
          rw [List.getElem?_eq_getElem hAutomatonBound, ← hValue]
        have hEntryEquality : entry = (branch.1, branchFragment) :=
          Option.some.inj (hActualEntry.symm.trans hExpectedEntry)
        subst entry
        have hBranchMember : branch ∈ branches :=
          List.getElem_mem hBound
        have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
          (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
            hBranchMember).trans (by simp [fuel])
        have hBranchStable : branchFragment = compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2 :=
          compileTypeFuel_eq_of_sufficient signature branch.2 hBranchFuel
            (typeCompilationFuel_sufficient branch.2)
        have hBranchTargets' : branchFragment.FutureTargetsInStates :=
          compileTypeFuel_futureTargetsInStates signature fuel branch.2
            hBranchFuel
        have hBranchInitial' : branchFragment.initial ∈
            branchFragment.states :=
          compileTypeFuel_initial_mem signature fuel branch.2 hBranchFuel
        have hCard : branchFragment.states.card ≤ fragment.states.card := by
          have hIndexedSubset : childStates (index + 1) branchFragment ⊆
              indexedFragmentStates branchAutomata := by
            intro child hChild
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            exact ⟨((branch.1, branchFragment), index), hIndexed, hChild⟩
          have hSubset : childStates (index + 1) branchFragment ⊆
              fragment.states := by
            intro child hChild
            have hChild' := hIndexedSubset hChild
            simp [fragment, buildExclusiveOfferAutomaton,
              finishAutomatonFragment, hChild']
          calc
            branchFragment.states.card =
                (childStates (index + 1) branchFragment).card := by
              simp only [childStates]
              symm
              apply Finset.card_image_of_injective
              intro first second hEqual
              injection hEqual
            _ ≤ fragment.states.card := Finset.card_le_card hSubset
        have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_branch
          signature branches elseFragment branchAutomata index
            (branch.1, branchFragment) hExpectedEntry branchFragment.initial
              hBranchTargets' hBranchInitial' hCard
        have hBranchCanonical : branch.2.EntryCanonical :=
          PactType.EntryCanonicalBranches.get hBranchesCanonical hBranchEntry
        have hBranchRelation : TypeCompilationRelation branch.2
            branchFragment.initial branch.2 := by
          simpa [branchFragment, hBranchStable] using
            compileType_initial_relation_of_canonical signature branch.2
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hBranchCanonical)
        have hSemantic := hBranchFuture branch.1 branch.2 index
          hBranchEntry hBranchCanonical branchFragment.initial branch.2
          hBranchRelation
        have hStandalone : computeFuture
            { states := branchFragment.states, edges := branchFragment.edges }
            branchFragment.initial = typeFutureOffers branch.2 := by
          simpa [branchFragment, hBranchStable] using hSemantic
        refine ⟨branch.2, ?_, ?_⟩
        · simpa using hBranchEntry
        · simpa [pending, fragment] using hEmbedding.trans hStandalone
      have hEntryMenus : ∀ action,
          action ∈
              (exclusiveOfferEntryStates elseFragment branchAutomata).biUnion
                (computeFuture pending) ↔
            action ∈ typeFutureOffers elseType ∨
              ∃ branch ∈ branches,
                action ∈ typeFutureOffers branch.2 := by
        intro action
        constructor
        · intro hAction
          rcases Finset.mem_biUnion.mp hAction with
            ⟨entryState, hEntryState, hEntryOffer⟩
          unfold exclusiveOfferEntryStates at hEntryState
          simp only [Finset.mem_union, Finset.mem_singleton] at hEntryState
          rcases hEntryState with hElse | hBranch
          · subst entryState
            exact Or.inl (by simpa [hElseMenu] using hEntryOffer)
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty |
              ⟨indexed, hIndexed, hEntryState⟩
            · simp at hEmpty
            simp only [Finset.mem_singleton] at hEntryState
            subst entryState
            rcases hIndexedMenu indexed hIndexed with
              ⟨branchType, hBranchEntry, hMenu⟩
            have hBranchMember : (indexed.1.1, branchType) ∈ branches := by
              rcases List.getElem?_eq_some_iff.mp hBranchEntry with
                ⟨hBound, hValue⟩
              have hMember := List.getElem_mem hBound
              simpa [hValue] using hMember
            exact Or.inr ⟨(indexed.1.1, branchType), hBranchMember,
              by simpa [hMenu] using hEntryOffer⟩
        · rintro (hElseOffer | ⟨branch, hBranch, hBranchOffer⟩)
          · apply Finset.mem_biUnion.mpr
            refine ⟨childState 0 elseFragment.initial, ?_, ?_⟩
            · simp [exclusiveOfferEntryStates]
            · simpa [hElseMenu] using hElseOffer
          · rcases List.mem_iff_getElem.mp hBranch with
              ⟨index, hBound, hValue⟩
            let branchFragment := compileTypeFuel signature fuel branch.2
            have hBranchEntry : branches[index]? = some branch := by
              rw [List.getElem?_eq_getElem hBound, hValue]
            have hAutomatonEntry : branchAutomata[index]? =
                some (branch.1, branchFragment) := by
              simp [branchAutomata, branchFragment, hBranchEntry]
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa [branchAutomata] using hBound
            have hZipEntry : ((branch.1, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hAutomatonBound : index < branchAutomata.length := by
                simpa [branchAutomata] using hBound
              have hValue' : branchAutomata[index] =
                  (branch.1, branchFragment) := by
                exact (List.getElem?_eq_some_iff.mp hAutomatonEntry).2
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt] at hMember
              rw [hValue'] at hMember
              exact hMember
            rcases hIndexedMenu ((branch.1, branchFragment), index)
              hZipEntry with ⟨targetType, hTargetEntry, hMenu⟩
            have hTargetType : targetType = branch.2 := by
              have hOptions := hTargetEntry.symm.trans hBranchEntry
              exact (Prod.mk.inj (Option.some.inj hOptions)).2
            subst targetType
            apply Finset.mem_biUnion.mpr
            refine ⟨childState (index + 1) branchFragment.initial, ?_, ?_⟩
            · unfold exclusiveOfferEntryStates
              simp only [Finset.mem_union, Finset.mem_singleton]
              right
              rw [mem_foldl_union_iff]
              right
              exact ⟨((branch.1, branchFragment), index), hZipEntry, by simp⟩
            · simpa [hMenu] using hBranchOffer
      have hSyntax := typeFutureOffers_xoffer elseType branches
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.xoffer elseType branches) := by
        rw [hRootGraph, hSyntax]
        ext action
        rw [Finset.mem_union, mem_futureOfferBranchFold_iff,
          hEntryMenus action]
        constructor
        · rintro (hHead | hElse | ⟨branch, hBranch, hFuture⟩)
          · right
            have hMapped : action ∈ branches.map Prod.fst := by
              simpa [typeBranchActions] using hHead
            rcases List.mem_map.mp hMapped with
              ⟨branch, hBranch, hAction⟩
            exact ⟨branch, hBranch, Or.inl hAction.symm⟩
          · exact Or.inl hElse
          · exact Or.inr ⟨branch, hBranch, Or.inr hFuture⟩
        · rintro (hElse | ⟨branch, hBranch, hHead | hFuture⟩)
          · exact Or.inr (Or.inl hElse)
          · left
            simpa [typeBranchActions, hHead] using
              (List.mem_map_of_mem (f := Prod.fst) hBranch)
          · exact Or.inr (Or.inr ⟨branch, hBranch, hFuture⟩)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, fuel] using
          hMenuEquality
  | xoffer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_else
        signature branches elseFragment branchAutomata childState hElseTargets
          hChildState hCard
      have hSemantic := hElseFuture hElseCanonical childState residual
        hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, fuel] using
          hEmbedding.trans hSemanticShared
  | xoffer_branch _ branchType _ _ action index childState
      hEntry hChildRelated =>
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hBranchMember).trans (by simp [fuel])
      let branchFragment := compileTypeFuel signature fuel branchType
      have hBranchStable : branchFragment = compileTypeFuel signature
          (typeCompilationFuel branchType) branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, branchFragment) := by
        simp [branchAutomata, branchFragment, hEntry]
      have hChildState : childState ∈ branchFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          branchType childState residual hChildRelated
        simpa [branchFragment, hBranchStable] using hCanonical
      have hTargets : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
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
          intro child hChild
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry, hChild⟩
        have hSubset : childStates (index + 1) branchFragment ⊆
            fragment.states := by
          intro child hChild
          have hIndexed := hIndexedSubset hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hIndexed]
        calc
          branchFragment.states.card =
              (childStates (index + 1) branchFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_branch
        signature branches elseFragment branchAutomata index
          (action, branchFragment) hAutomatonEntry childState hTargets
            hChildState hCard
      have hBranchTypeCanonical : branchType.EntryCanonical :=
        PactType.EntryCanonicalBranches.get hBranchesCanonical hEntry
      have hSemantic := hBranchFuture action branchType index hEntry
        hBranchTypeCanonical childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := branchFragment.states, edges := branchFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [branchFragment, hBranchStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, branchFragment,
        fuel] using hEmbedding.trans hSemanticShared

/-- `parallelTypeBranches`'s output is never a degenerate `.par`, provided
every branch continuation is itself canonical: every node it builds is either
`singletonTypeXOffer` (`.xoffer`-rooted — canonical exactly when its one
branch's continuation is, and never `.skip` regardless) or a `.par` of two
such non-collapsing pieces. -/
private theorem parallelTypeBranches_entryCanonical_and_ne_skip :
    ∀ branches : List (BareMessage × PactType), branches ≠ [] →
      PactType.EntryCanonicalBranches branches →
      (parallelTypeBranches branches).EntryCanonical ∧
        parallelTypeBranches branches ≠ .skip
  | [], hNonempty, _ => absurd rfl hNonempty
  | [branch], _, hBranchesCanonical => by
      have hBranchCanonical : branch.2.EntryCanonical :=
        PactType.EntryCanonicalBranches.head hBranchesCanonical
      refine ⟨?_, by simp [parallelTypeBranches, singletonTypeXOffer]⟩
      simp only [parallelTypeBranches, singletonTypeXOffer,
        PactType.EntryCanonical]
      exact ⟨trivial, PactType.EntryCanonicalBranches.singleton
        hBranchCanonical⟩
  | branch :: b2 :: rest, _, hBranchesCanonical => by
      have hBranchCanonical : branch.2.EntryCanonical :=
        PactType.EntryCanonicalBranches.head hBranchesCanonical
      have hRestCanonical : PactType.EntryCanonicalBranches (b2 :: rest) :=
        PactType.EntryCanonicalBranches.tail hBranchesCanonical
      obtain ⟨hTailCanonical, hTailNeSkip⟩ :=
        parallelTypeBranches_entryCanonical_and_ne_skip (b2 :: rest) (by simp)
          hRestCanonical
      have hTailFixed :=
        PactType.canonicalEntryResidual_eq_self_of_entryCanonical hTailCanonical
      refine ⟨?_, by simp [parallelTypeBranches]⟩
      have hGoal : (PactType.par (singletonTypeXOffer branch)
          (parallelTypeBranches (b2 :: rest)) ∅).EntryCanonical := by
        simp only [PactType.EntryCanonical]
        refine ⟨?_, ?_, hTailCanonical⟩
        · simp only [PactType.canonicalEntryResidual, singletonTypeXOffer,
            hTailFixed]
          rintro ⟨_, hEq⟩
          exact hTailNeSkip hEq
        · simp only [singletonTypeXOffer, PactType.EntryCanonical]
          exact ⟨trivial, PactType.EntryCanonicalBranches.singleton
            hBranchCanonical⟩
      simpa [parallelTypeBranches] using hGoal

/-- `parallelTypeBranchesSelecting`'s output is likewise never a degenerate
`.par` once every branch continuation is canonical: it differs from
`parallelTypeBranches` only by substituting `selectedTypeBranch` (`.seq`-
rooted, canonical exactly when its continuation is, and also never `.skip`)
for one singleton, so the same non-collapsing argument applies at every
recursive step. -/
private theorem parallelTypeBranchesSelecting_entryCanonical_and_ne_skip
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType), branches ≠ [] →
      PactType.EntryCanonicalBranches branches →
      (parallelTypeBranchesSelecting selected branches).EntryCanonical ∧
        parallelTypeBranchesSelecting selected branches ≠ .skip
  | [], hNonempty, _ => absurd rfl hNonempty
  | [branch], _, hBranchesCanonical => by
      have hBranchCanonical : branch.2.EntryCanonical :=
        PactType.EntryCanonicalBranches.head hBranchesCanonical
      unfold parallelTypeBranchesSelecting
      split
      · refine ⟨?_, by simp [selectedTypeBranch]⟩
        simp only [selectedTypeBranch, PactType.EntryCanonical]
        exact ⟨trivial, hBranchCanonical⟩
      · refine ⟨?_, by simp [singletonTypeXOffer]⟩
        simp only [singletonTypeXOffer, PactType.EntryCanonical]
        exact ⟨trivial, PactType.EntryCanonicalBranches.singleton
          hBranchCanonical⟩
  | branch :: b2 :: rest, _, hBranchesCanonical => by
      have hBranchCanonical : branch.2.EntryCanonical :=
        PactType.EntryCanonicalBranches.head hBranchesCanonical
      have hRestCanonical : PactType.EntryCanonicalBranches (b2 :: rest) :=
        PactType.EntryCanonicalBranches.tail hBranchesCanonical
      unfold parallelTypeBranchesSelecting
      split
      · obtain ⟨hTailCanonical, hTailNeSkip⟩ :=
          parallelTypeBranches_entryCanonical_and_ne_skip (b2 :: rest)
            (by simp) hRestCanonical
        have hTailFixed :=
          PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hTailCanonical
        refine ⟨?_, by simp [selectedTypeBranch]⟩
        have hGoal : (PactType.par (selectedTypeBranch branch)
            (parallelTypeBranches (b2 :: rest)) ∅).EntryCanonical := by
          simp only [PactType.EntryCanonical]
          refine ⟨?_, ?_, hTailCanonical⟩
          · simp only [PactType.canonicalEntryResidual, selectedTypeBranch,
              hTailFixed]
            rintro ⟨_, hEq⟩
            exact hTailNeSkip hEq
          · simp only [selectedTypeBranch, PactType.EntryCanonical]
            exact ⟨trivial, hBranchCanonical⟩
        exact hGoal
      · obtain ⟨hTailCanonical, hTailNeSkip⟩ :=
          parallelTypeBranchesSelecting_entryCanonical_and_ne_skip selected
            (b2 :: rest) (by simp) hRestCanonical
        have hTailFixed :=
          PactType.canonicalEntryResidual_eq_self_of_entryCanonical
            hTailCanonical
        refine ⟨?_, by simp [singletonTypeXOffer]⟩
        have hGoal : PactType.EntryCanonical (PactType.par
            (singletonTypeXOffer branch)
            (parallelTypeBranchesSelecting selected (b2 :: rest)) ∅) := by
          simp only [PactType.EntryCanonical]
          refine ⟨?_, ?_, hTailCanonical⟩
          · simp only [PactType.canonicalEntryResidual, singletonTypeXOffer,
              hTailFixed]
            rintro ⟨_, hEq⟩
            exact hTailNeSkip hEq
          · simp only [singletonTypeXOffer, PactType.EntryCanonical]
            exact ⟨trivial, PactType.EntryCanonicalBranches.singleton
              hBranchCanonical⟩
        exact hGoal

/-- Whole-fragment future correctness for conjunctive offers.  Each enabled
witness's selected conjunction is treated as an indexed child and the else
continuation as child `0`; the root calculation is then identified with the
syntax-derived `typeFutureOffers_offer` fold.  Selection does not change the
fold value at any index, so a single per-index future hypothesis suffices. -/
theorem compilationFutureCorrect_offer_of_children
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.SupportsBranches branches)
    (hElseFuture : CompilationFutureCorrect signature elseType)
    (hConjunctionFuture : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationFutureCorrect signature
          (parallelTypeBranchesSelecting selected branches)) :
    CompilationFutureCorrect signature (.offer elseType branches) := by
  classical
  intro hCanonical state residual hRelated
  have hElseCanonical : elseType.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hBranchesCanonical : PactType.EntryCanonicalBranches branches := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hActions : selectedConjunctions.map Prod.fst = branches.map Prod.fst := by
    simp [selectedConjunctions]
  have hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupports
  have hSelectedAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailable branch hBranch
  have hEntryFuel : ∀ entry ∈ branches,
      TypeCompilationFuelSufficient
        (parallelTypeBranchesSelecting entry branches) fuel := by
    intro entry _
    simp only [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
    exact le_max_right _ _
  have hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel
      (parallelTypeBranchesSelecting branch branches) (hEntryFuel branch hBranch)
  have hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel
      (parallelTypeBranchesSelecting branch branches) (hEntryFuel branch hBranch)
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | offer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (selectedConjunctiveOfferEntryStates elseFragment
              selectedConjunctions).biUnion (computeFuture pending) := by
        simpa [pending, fragment] using
          buildSelectedConjunctiveOfferAutomaton_computeFuture_root signature
            branches elseFragment selectedConjunctions hSelectedAvailable
              hElseTargets hConjunctionTargets hElseInitial hConjunctionInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding : computeFuture pending (childState 0 elseFragment.initial) =
          computeFuture { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
          ({ states := elseFragment.states, edges := elseFragment.edges } :
            PendingAutomaton) 0
          (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
            elseFragment selectedConjunctions)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            elseFragment hElseTargets)
          elseFragment.initial hElseInitial hElseCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation_of_canonical signature elseType
            (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
              hElseCanonical)
      have hElseSemantic := hElseFuture hElseCanonical elseFragment.initial
        elseType hElseRelation
      have hElseMenu : computeFuture pending
          (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        exact hElseEmbedding.trans hStandalone
      have hConjunctionMenu : ∀ index entry, selectedConjunctions[index]? =
          some entry → computeFuture pending (childState (index + 1) entry.2.initial) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
        intro index entry hEntry
        have hEntryMem : entry ∈ selectedConjunctions := by
          rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
          have hMember := List.getElem_mem hBound
          simpa [hValue] using hMember
        have hCard : entry.2.states.card ≤ fragment.states.card := by
          have hIndexedSubset : childStates (index + 1) entry.2 ⊆
              indexedFragmentStates selectedConjunctions := by
            intro s hs
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
            have hZipBound : index < selectedConjunctions.zipIdx.length := by
              simpa using hBound
            have hZipEntry : (entry, index) ∈ selectedConjunctions.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            exact ⟨(entry, index), hZipEntry, hs⟩
          have hSubset : childStates (index + 1) entry.2 ⊆ fragment.states := by
            intro s hs
            have hIndexed := hIndexedSubset hs
            simp [fragment, buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, hIndexed]
          calc
            entry.2.states.card = (childStates (index + 1) entry.2).card := by
              simp only [childStates]
              symm
              apply Finset.card_image_of_injective
              intro first second hEqual
              injection hEqual
            _ ≤ fragment.states.card := Finset.card_le_card hSubset
        have hEmbedding : computeFuture pending (childState (index + 1) entry.2.initial) =
            computeFuture { states := entry.2.states, edges := entry.2.edges }
              entry.2.initial :=
          taggedChild_computeFuture_of_outgoing
            ({ states := fragment.states, edges := fragment.edges } :
              PendingAutomaton)
            ({ states := entry.2.states, edges := entry.2.edges } :
              PendingAutomaton) (index + 1)
            (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
              signature branches elseFragment selectedConjunctions index entry
                hEntry)
            (PendingAutomaton.referencesClosed_of_futureTargetsInStates
              entry.2 (hConjunctionTargets entry hEntryMem))
            entry.2.initial (hConjunctionInitial entry hEntryMem) hCard
        have hIndexBound : index < branches.length := by
          have := List.getElem?_eq_some_iff.mp hEntry
          simpa [selectedConjunctions] using this.1
        let branch := branches[index]
        have hBranchEntry : branches[index]? = some branch := by
          simp [branch, List.getElem?_eq_getElem hIndexBound]
        have hBranchEq : entry = (branch.1, compileTypeFuel signature fuel
            (parallelTypeBranchesSelecting branch branches)) := by
          have hEntry' : selectedConjunctions[index]? = some entry := hEntry
          simp only [selectedConjunctions, List.getElem?_map, hBranchEntry,
            Option.map_some, Option.some.injEq] at hEntry'
          exact hEntry'.symm
        have hBranchMem : branch ∈ branches := by
          rcases List.getElem?_eq_some_iff.mp hBranchEntry with ⟨hBound, hValue⟩
          have hMember := List.getElem_mem hBound
          simpa [hValue] using hMember
        have hStable : entry.2 = compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting branch branches))
            (parallelTypeBranchesSelecting branch branches) := by
          rw [hBranchEq]
          exact compileTypeFuel_eq_of_sufficient signature
            (parallelTypeBranchesSelecting branch branches)
            (hEntryFuel branch hBranchMem) (typeCompilationFuel_sufficient _)
        have hBranchesNonempty : branches ≠ [] := fun h => by
          simp [h] at hBranchMem
        have hSelectedCanonical :
            (parallelTypeBranchesSelecting branch branches).EntryCanonical :=
          (parallelTypeBranchesSelecting_entryCanonical_and_ne_skip branch
            branches hBranchesNonempty hBranchesCanonical).1
        have hSelectedRelation : TypeCompilationRelation
            (parallelTypeBranchesSelecting branch branches)
            entry.2.initial (parallelTypeBranchesSelecting branch branches) := by
          simpa [hStable] using
            compileType_initial_relation_of_canonical signature
              (parallelTypeBranchesSelecting branch branches)
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hSelectedCanonical)
        have hSemantic := hConjunctionFuture branch index hBranchEntry
          hSelectedCanonical entry.2.initial
          (parallelTypeBranchesSelecting branch branches) hSelectedRelation
        have hSemanticShared : computeFuture
            { states := entry.2.states, edges := entry.2.edges } entry.2.initial =
              typeFutureOffers (parallelTypeBranchesSelecting branch branches) := by
          simpa [hStable] using hSemantic
        rw [hEmbedding, hSemanticShared,
          typeFutureOffers_parallelTypeBranchesSelecting_eq_fold]
      have hEntryMenus : (selectedConjunctiveOfferEntryStates elseFragment
          selectedConjunctions).biUnion (computeFuture pending) =
            typeFutureOffers elseType ∪
              if branches = [] then ∅ else
                branches.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
        ext action
        simp only [selectedConjunctiveOfferEntryStates, Finset.mem_biUnion,
          Finset.mem_union]
        constructor
        · rintro ⟨s, (hs | hs), hAction⟩
          · simp only [Finset.mem_singleton] at hs
            subst hs
            left
            simpa [hElseMenu] using hAction
          · rw [mem_foldl_union_iff] at hs
            rcases hs with hEmpty | ⟨indexed, hIndexed, hs⟩
            · simp at hEmpty
            simp only [Finset.mem_singleton] at hs
            subst hs
            right
            have hNonempty : branches ≠ [] := by
              rintro rfl
              simp [selectedConjunctions] at hIndexed
            rw [if_neg hNonempty]
            have hIndexedFields := List.mem_zipIdx hIndexed
            simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
              at hIndexedFields
            rcases hIndexedFields with ⟨hBound, hValue⟩
            have hEntry : selectedConjunctions[indexed.2]? = some indexed.1 := by
              rw [List.getElem?_eq_getElem hBound, hValue]
            rw [← hConjunctionMenu indexed.2 indexed.1 hEntry]
            exact hAction
        · rintro (hAction | hAction)
          · exact ⟨childState 0 elseFragment.initial, Or.inl (by simp),
              by simpa [hElseMenu] using hAction⟩
          · by_cases hEmpty : branches = []
            · subst hEmpty
              simp at hAction
            · rw [if_neg hEmpty] at hAction
              cases hBranches : branches with
              | nil => exact absurd hBranches hEmpty
              | cons head tail =>
                  have hEntry0 : selectedConjunctions[0]? = some
                      (head.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting head branches)) := by
                    simp [selectedConjunctions, hBranches]
                  refine ⟨childState 1 (compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting head branches)).initial,
                    Or.inr ?_, ?_⟩
                  · rw [mem_foldl_union_iff]
                    right
                    refine ⟨((head.1, compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting head branches)), 0), ?_, by simp⟩
                    rcases List.getElem?_eq_some_iff.mp hEntry0 with
                      ⟨hBound, hValue⟩
                    have hZipBound : (0 : Nat) <
                        selectedConjunctions.zipIdx.length := by simpa using hBound
                    have hMember := List.getElem_mem hZipBound
                    have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                      (i := 0) (j := 0) hZipBound
                    simp only [zero_add] at hAt
                    rw [hAt, hValue] at hMember
                    exact hMember
                  · rw [hConjunctionMenu 0 _ hEntry0]
                    exact hAction
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.offer elseType branches) := by
        rw [hRootGraph, hEntryMenus, typeFutureOffers_offer]
        by_cases hEmpty : branches = []
        · subst branches
          simp [typeBranchActions, typeFutureOffers, typeFutureOffersFuel]
        · rw [if_neg hEmpty]
          ext action
          rw [Finset.mem_union, Finset.mem_union,
            mem_futureOfferBranchFold_iff action branches ∅,
            mem_futureOfferBranchFold_iff action branches
              (typeFutureOffers elseType)]
          have hHeadIff : action ∈ typeBranchActions branches ↔
              ∃ branch ∈ branches, action = branch.1 := by
            constructor
            · intro hHead
              have hMapped : action ∈ branches.map Prod.fst := by
                simpa [typeBranchActions] using hHead
              rcases List.mem_map.mp hMapped with ⟨branch, hBranch, hAction⟩
              exact ⟨branch, hBranch, hAction.symm⟩
            · rintro ⟨branch, hBranch, hAction⟩
              simpa [typeBranchActions, hAction] using
                (List.mem_map_of_mem (f := Prod.fst) hBranch)
          rw [hHeadIff]
          constructor
          · rintro (⟨branch, hBranch, hAction⟩ | hElse | hEmptyMem | hExists)
            · exact Or.inr ⟨branch, hBranch, Or.inl hAction⟩
            · exact Or.inl hElse
            · simp at hEmptyMem
            · exact Or.inr hExists
          · rintro (hElse | ⟨branch, hBranch, hHead | hAction⟩)
            · exact Or.inr (Or.inl hElse)
            · exact Or.inl ⟨branch, hBranch, hHead⟩
            · exact Or.inr (Or.inr (Or.inr ⟨branch, hBranch, Or.inr hAction⟩))
      simpa only [pending, fragment] using hMenuEquality
  | offer_branches _ _ _ selected index state' hEntry hChildRelated =>
      have hEntryMem : selected ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hSelectedFuel := hEntryFuel selected hEntryMem
      let selectedFragment := compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)
      have hSelectedStable : selectedFragment = compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature
          (parallelTypeBranchesSelecting selected branches) hSelectedFuel
          (typeCompilationFuel_sufficient _)
      have hAutomatonEntry : selectedConjunctions[index]? =
          some (selected.1, selectedFragment) := by
        simp [selectedConjunctions, selectedFragment, hEntry]
      have hChildState : state' ∈ selectedFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          (parallelTypeBranchesSelecting selected branches) state' residual
          hChildRelated
        simpa [selectedFragment, hSelectedStable] using hCanonical
      have hCard : selectedFragment.states.card ≤ fragment.states.card := by
        have hIndexedSubset : childStates (index + 1) selectedFragment ⊆
            indexedFragmentStates selectedConjunctions := by
          intro s hs
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
            ⟨hBound, hValue⟩
          have hZipBound : index < selectedConjunctions.zipIdx.length := by
            simpa using hBound
          have hZipEntry : ((selected.1, selectedFragment), index) ∈
              selectedConjunctions.zipIdx := by
            have hMember := List.getElem_mem hZipBound
            have hAt := List.getElem_zipIdx (l := selectedConjunctions)
              (i := index) (j := 0) hZipBound
            simp only [zero_add] at hAt
            rw [hAt, hValue] at hMember
            exact hMember
          exact ⟨((selected.1, selectedFragment), index), hZipEntry, hs⟩
        have hSubset : childStates (index + 1) selectedFragment ⊆
            fragment.states := by
          intro s hs
          have hIndexed := hIndexedSubset hs
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hIndexed]
        calc
          selectedFragment.states.card =
              (childStates (index + 1) selectedFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding : computeFuture pending
          (childState (index + 1) state') = computeFuture
          { states := selectedFragment.states, edges := selectedFragment.edges }
          state' :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } :
            PendingAutomaton)
          ({ states := selectedFragment.states, edges := selectedFragment.edges } :
            PendingAutomaton) (index + 1)
          (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            selectedFragment
              (compileTypeFuel_futureTargetsInStates signature fuel
                (parallelTypeBranchesSelecting selected branches)
                hSelectedFuel))
          state' hChildState hCard
      have hSelectedCanonical :
          (parallelTypeBranchesSelecting selected branches).EntryCanonical :=
        (parallelTypeBranchesSelecting_entryCanonical_and_ne_skip selected
          branches (fun h => by simp [h] at hEntry) hBranchesCanonical).1
      have hSemantic := hConjunctionFuture selected index hEntry
        hSelectedCanonical state' residual hChildRelated
      have hSemanticShared : computeFuture
          { states := selectedFragment.states, edges := selectedFragment.edges }
          state' = typeFutureOffers residual := by
        simpa [selectedFragment, hSelectedStable] using hSemantic
      simpa only [pending, fragment] using hEmbedding.trans hSemanticShared
  | offer_else _ _ _ state' hChildRelated =>
      have hChildState : state' ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType state' residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding : computeFuture pending (childState 0 state') =
          computeFuture { states := elseFragment.states, edges := elseFragment.edges }
            state' :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
          ({ states := elseFragment.states, edges := elseFragment.edges } :
            PendingAutomaton) 0
          (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
            elseFragment selectedConjunctions)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            elseFragment hElseTargets)
          state' hChildState hCard
      have hSemantic := hElseFuture hElseCanonical state' residual hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          state' = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [pending, fragment] using hEmbedding.trans hSemanticShared
/-
  classical
  intro state residual hRelated
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel, conjunctionType]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hConjunctionStable : conjunction = compileTypeFuel signature
      (typeCompilationFuel conjunctionType) conjunctionType :=
    compileTypeFuel_eq_of_sufficient signature conjunctionType
      hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hConjunctionTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hConjunctionInitial : conjunction.initial ∈ conjunction.states :=
    compileTypeFuel_initial_mem signature fuel conjunctionType
      hConjunctionFuel
  have hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupports
  cases hRelated with
  | offer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (conjunctiveOfferEntryStates branches elseFragment
              conjunction).biUnion (computeFuture pending) := by
        simpa [pending, fragment] using
          buildConjunctiveOfferAutomaton_computeFuture_root signature branches
            elseFragment conjunction hAvailable hElseTargets
              hConjunctionTargets hElseInitial hConjunctionInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 1 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hConjunctionCard : conjunction.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 conjunction ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          conjunction.states.card = (childStates 0 conjunction).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 1 elseFragment
          (Or.inr ⟨rfl, rfl⟩) elseFragment.initial hElseTargets hElseInitial
            hElseCard
      have hConjunctionEmbedding :=
        buildConjunctiveOfferAutomaton_computeFuture_child signature branches
          elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
            conjunction.initial hConjunctionTargets hConjunctionInitial
              hConjunctionCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation signature elseType
      have hConjunctionRelation : TypeCompilationRelation conjunctionType
          conjunction.initial conjunctionType := by
        simpa [conjunction, hConjunctionStable] using
          compileType_initial_relation signature conjunctionType
      have hElseSemantic := hElseFuture elseFragment.initial elseType
        hElseRelation
      have hConjunctionSemantic := hConjunctionFuture conjunction.initial
        conjunctionType hConjunctionRelation
      have hElseMenu : computeFuture pending
          (childState 1 elseFragment.initial) =
          typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        simpa [pending, fragment] using hElseEmbedding.trans hStandalone
      have hConjunctionMenu : computeFuture pending
          (childState 0 conjunction.initial) =
          typeFutureOffers conjunctionType := by
        have hStandalone : computeFuture
            { states := conjunction.states, edges := conjunction.edges }
            conjunction.initial = typeFutureOffers conjunctionType := by
          simpa [conjunction, hConjunctionStable] using hConjunctionSemantic
        simpa [pending, fragment] using
          hConjunctionEmbedding.trans hStandalone
      have hEntryMenus :
          (conjunctiveOfferEntryStates branches elseFragment
              conjunction).biUnion (computeFuture pending) =
            typeFutureOffers elseType ∪
              if branches = [] then ∅ else typeFutureOffers conjunctionType := by
        ext action
        by_cases hEmpty : branches = []
        · subst branches
          simp [conjunctiveOfferEntryStates, hElseMenu]
        · simp [conjunctiveOfferEntryStates, hEmpty, hElseMenu,
            hConjunctionMenu, or_comm]
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.offer elseType branches) := by
        rw [hRootGraph, hEntryMenus, typeFutureOffers_offer]
        by_cases hEmpty : branches = []
        · subst branches
          simp [typeBranchActions, typeFutureOffers, typeFutureOffersFuel]
        · rw [if_neg hEmpty,
            typeFutureOffers_parallelTypeBranches_eq_fold]
          ext action
          rw [Finset.mem_union, Finset.mem_union,
            mem_futureOfferBranchFold_iff action branches ∅,
            mem_futureOfferBranchFold_iff action branches
              (typeFutureOffers elseType)]
          simp
          intro hHead
          right
          have hMapped : action ∈ branches.map Prod.fst := by
            simpa [typeBranchActions] using hHead
          rcases List.mem_map.mp hMapped with
            ⟨branch, hBranch, hAction⟩
          rcases branch with ⟨⟨message, direction⟩, branchType⟩
          exact ⟨message, direction, branchType, hBranch,
            Or.inl hAction.symm⟩
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hMenuEquality
  | offer_branches _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ conjunction.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          conjunctionType childState residual hChildRelated
        simpa [conjunction, hConjunctionStable] using hCanonical
      have hCard : conjunction.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 conjunction ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          conjunction.states.card = (childStates 0 conjunction).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 0 conjunction
          (Or.inl ⟨rfl, rfl⟩) childState hConjunctionTargets hChildState hCard
      have hSemantic := hConjunctionFuture childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := conjunction.states, edges := conjunction.edges }
          childState = typeFutureOffers residual := by
        simpa [conjunction, hConjunctionStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hEmbedding.trans hSemanticShared
  | offer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 1 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 1 elseFragment
          (Or.inr ⟨rfl, rfl⟩) childState hElseTargets hChildState hCard
      have hSemantic := hElseFuture childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hEmbedding.trans hSemanticShared
-/

private theorem TypeOffers.offer_some_fields_of_enabled
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hEnabled : ∃ enabled ∈ branches, TypeBranchEnabled env enabled)
    (enabled : BareMessage × PactType)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      (parallelTypeBranchesSelecting enabled branches) current future) :
    current = ∅ ∧
      future = typeFutureOffers
        (parallelTypeBranchesSelecting enabled branches) := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : parallelTypeBranchesSelecting enabled branches =
    actualTarget at hOffers
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

/- The former unrestricted `compilationFragmentStepCorrect_offer` theorem was
removed here.  It described the obsolete all-else conjunction child and had no
callers.  The compiler and semantics now agree through the proved scoped
theorem below, indexed by `parallelTypeBranchesSelecting selected branches`. -/
/-
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
-/

theorem compilationScopedFragmentStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationScopedFragmentStepCorrect signature
          (parallelTypeBranchesSelecting selected branches))
    (hElseStep : CompilationScopedFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationScopedFragmentStepCorrect signature
      (.offer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro hCanonical residual residual' state env label offers hRelated
    hLocalEnvironment hAvoids
  have hElseCanonical : elseType.EntryCanonical := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.1
  have hBranchesCanonical : PactType.EntryCanonicalBranches branches := by
    have h := hCanonical
    simp only [PactType.EntryCanonical] at h
    exact h.2
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
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
              hEnabledWitness enabled hOffers with ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting enabled branches) fuel := by
              simp only [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
              exact le_max_right _ _
            let selectedFragment := compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting enabled branches)
            have hEnabledCanonical : PactType.EntryCanonical
                (parallelTypeBranchesSelecting enabled branches) :=
              (parallelTypeBranchesSelecting_entryCanonical_and_ne_skip
                enabled branches (fun h => by simp [h] at hBranchMember)
                hBranchesCanonical).1
            have hInitial : TypeCompilationRelation
                (parallelTypeBranchesSelecting enabled branches)
                selectedFragment.initial
                (parallelTypeBranchesSelecting enabled branches) :=
              compileTypeFuel_initial_relation_of_canonical signature fuel
                (parallelTypeBranchesSelecting enabled branches) hBranchFuel
                (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                  hEnabledCanonical)
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState (index + 1) selectedFragment.initial)
                (parallelTypeBranchesSelecting enabled branches) :=
              TypeCompilationRelation.offer_branches elseType
                (parallelTypeBranchesSelecting enabled branches) branches
                enabled index selectedFragment.initial hEntry hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState (index + 1) selectedFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩
              (childState (index + 1) selectedFragment.initial)).mpr
            left
            have hAutomatonEntry : selectedConjunctions[index]? =
                some (enabled.1, selectedFragment) := by
              simp [selectedConjunctions, selectedFragment, hEntry]
            have hZipEntry : ((enabled.1, selectedFragment), index) ∈
                selectedConjunctions.zipIdx := by
              rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
                ⟨hBound, hValue⟩
              have hZipBound : index < selectedConjunctions.zipIdx.length := by
                simpa using hBound
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            exact ⟨((enabled.1, selectedFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation_of_canonical signature fuel
              elseType hElseFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hElseCanonical)
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture hCanonical _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
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
            have hComputed := hFuture hCanonical _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment selectedConjunctions env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨indexed, hIndexed, hLocal, hImmediate,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [selectedConjunctions] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)) := by
            rw [hValue]
            simp [selectedConjunctions, branch]
          have hBranchMember : branch ∈ branches := List.getElem_mem hBranchBound
          have hBranchEnabled : TypeBranchEnabled env branch := by
            have hNeed : typeNeed branch.1 ∈ env.immediate := by
              rw [← congrArg Prod.fst hIndexedValue]
              exact hImmediate
            exact hNeed
          rw [hIndexedValue] at hTargetState hEdgeFuture
          subst target
          have hBranchFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting branch branches) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
            exact le_max_right _ _
          have hBranchCanonical : PactType.EntryCanonical
              (parallelTypeBranchesSelecting branch branches) :=
            (parallelTypeBranchesSelecting_entryCanonical_and_ne_skip branch
              branches (fun h => by simp [h] at hBranchMember)
              hBranchesCanonical).1
          have hInitial : TypeCompilationRelation
              (parallelTypeBranchesSelecting branch branches)
              (compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)).initial
              (parallelTypeBranchesSelecting branch branches) :=
            compileTypeFuel_initial_relation_of_canonical signature fuel
              (parallelTypeBranchesSelecting branch branches) hBranchFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hBranchCanonical)
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting branch branches)).initial)
              (parallelTypeBranchesSelecting branch branches) :=
            TypeCompilationRelation.offer_branches elseType
              (parallelTypeBranchesSelecting branch branches) branches branch
              indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers (parallelTypeBranchesSelecting branch branches) :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches branch
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches branch
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
          have hComputed := hFuture hCanonical _ _ hSourceRelation
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
            compileTypeFuel_initial_relation_of_canonical signature fuel
              elseType hElseFuel
              (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
                hElseCanonical)
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture hCanonical _ _ hExpectedTarget
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
  | offer_branches _ childResidual _ selected index childQ hEntry
      hChildRelated =>
      have hAvoidsSelected : env.AvoidsInterface
          (parallelTypeBranchesSelecting selected branches).ParallelInterfaces :=
        hAvoids.mono (by
          intro message hMessage
          simp only [PactType.ParallelInterfaces, Finset.mem_union]
          right
          exact parallelTypeBranchesSelecting_parallelInterfaces_subset
            selected branches hMessage)
      have hSelectedCanonical :
          (parallelTypeBranchesSelecting selected branches).EntryCanonical :=
        (parallelTypeBranchesSelecting_entryCanonical_and_ne_skip selected
          branches (fun h => by simp [h] at hEntry) hBranchesCanonical).1
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep selected index hEntry hSelectedCanonical
          hChildRelated hLocalEnvironment hAvoidsSelected).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches selected index hEntry childQ childTarget env
            label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches selected index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches selected index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ selected' _ _ hEntry' hChildTarget =>
            have hSelectedEq : selected = selected' := by
              rw [hEntry] at hEntry'
              exact Option.some.inj hEntry'
            exact (hConjunctionStep selected index hEntry hSelectedCanonical
              hChildRelated hLocalEnvironment hAvoidsSelected).mpr
              ⟨childTarget, hChildEdge, hSelectedEq ▸ hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hElseCanonical hChildRelated hLocalEnvironment
          hAvoidsElse).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
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
            exact (hElseStep hElseCanonical hChildRelated hLocalEnvironment
              hAvoidsElse).mpr ⟨childTarget, hChildEdge, hChildTarget⟩
/-
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
-/

/-! ### Visible-edge target relatedness -/

theorem compilationResolvedEdgeTargetsRelated_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType)
    (hBranchTargets : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationResolvedEdgeTargetsRelated signature branchType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.xoffer elseType branches) := by
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
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | xoffer_source =>
      rw [hFragment] at hEdge
      rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment branchAutomata environment label
        offers target).mp hEdge with hBranch | hWait | hElse
      · rcases hBranch with ⟨indexed, hIndexed, _, _, _, _, _, _, hTarget⟩
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
        rw [hIndexedValue] at hTarget
        subst target
        have hBranchMember : branch ∈ branches :=
          List.getElem_mem hBranchBound
        have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
          exact le_trans
            (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
              hBranchMember)
            (by simp [fuel])
        have hInitial : TypeCompilationRelation branch.2
            (compileTypeFuel signature fuel branch.2).initial
            (PactType.canonicalEntryResidual branch.2) :=
          compileTypeFuel_initial_relation signature fuel branch.2 hBranchFuel
        exact ⟨PactType.canonicalEntryResidual branch.2,
          TypeCompilationRelation.xoffer_branch elseType branch.2 _
            branches branch.1 indexed.2 _ hEntry hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.xoffer elseType branches,
          TypeCompilationRelation.xoffer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial (PactType.canonicalEntryResidual elseType) :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨PactType.canonicalEntryResidual elseType,
          TypeCompilationRelation.xoffer_else elseType _ branches
            elseFragment.initial hInitial⟩
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_xoffer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
        elseType branches action branchType index hEntry hEdge with
        ⟨childTarget, rfl, hChildEdge⟩
      have hTargets : CompilationResolvedEdgeTargetsRelated signature
          branchType := hBranchTargets action branchType index hEntry
      rcases hTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_branch elseType branchType
          targetResidual branches action index childTarget hEntry
          hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionTargets : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationResolvedEdgeTargetsRelated signature
          (parallelTypeBranchesSelecting selected branches))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.offer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | offer_source =>
      rw [hFragment] at hEdge
      rcases hEdge with ⟨edge, hEdgeMem, hSource, _, _, _, _, hTarget⟩
      simp only [fragment, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union] at hEdgeMem
      rcases hEdgeMem with ((((hElse | hIndexed) | hEnabled) | hWait) |
        hResolved)
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
        rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          rcases hNewEdge with ⟨edgeEnvironment, _, rfl⟩
          simp only [childPendingEdge] at hTarget
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [selectedConjunctions] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)) := by
            rw [hValue]
            simp [selectedConjunctions, branch]
          rw [hIndexedValue] at hTarget
          subst target
          have hBranchFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting branch branches) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
            exact le_max_right _ _
          have hInitial : TypeCompilationRelation
              (parallelTypeBranchesSelecting branch branches)
              (compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)).initial
              (PactType.canonicalEntryResidual
                (parallelTypeBranchesSelecting branch branches)) :=
            compileTypeFuel_initial_relation signature fuel
              (parallelTypeBranchesSelecting branch branches) hBranchFuel
          exact ⟨PactType.canonicalEntryResidual
              (parallelTypeBranchesSelecting branch branches),
            TypeCompilationRelation.offer_branches elseType _ branches branch
              indexed.2 _ hEntry hInitial⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨edgeEnvironment, _, rfl⟩
        simp only [childPendingEdge] at hTarget
        subst target
        exact ⟨.offer elseType branches,
          TypeCompilationRelation.offer_source elseType branches⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
        rcases hResolved with ⟨edgeEnvironment, _, rfl⟩
        simp only [childPendingEdge] at hTarget
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial (PactType.canonicalEntryResidual elseType) :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨PactType.canonicalEntryResidual elseType,
          TypeCompilationRelation.offer_else elseType _ branches
            elseFragment.initial hInitial⟩
  | offer_branches _ childResidual _ selected index childQ hEntry
      hChildRelated =>
      rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
        elseType branches selected index hEntry hEdge with
        ⟨childTarget, rfl, hChildEdge⟩
      rcases hConjunctionTargets selected index hEntry hChildRelated
        hChildEdge with ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_branches elseType targetResidual
          branches selected index childTarget hEntry hTargetRelated⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
/-
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
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | offer_source =>
      rw [hFragment] at hEdge
      rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment conjunction environment label offers
        target).mp hEdge with hEnabled | hWait | hElse
      · rcases hEnabled with ⟨_, _, _, _, _, hTarget⟩
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
        exact ⟨conjunctionType,
          TypeCompilationRelation.offer_branches elseType conjunctionType
            branches conjunction.initial hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.offer elseType branches,
          TypeCompilationRelation.offer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.offer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
        elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hConjunctionTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_branches elseType targetResidual
          branches childTarget hTargetRelated⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
-/


end

end Pact
