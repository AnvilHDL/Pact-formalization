import Anvilpp.PactTypes.Correspondence.Offers.ParallelInterfaceTransport

/-!
# buildExclusiveOfferAutomaton graph structure: outgoing edges, entries, offersAt/computeFuture at the root
-/

namespace Pact

noncomputable section

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

end

end Pact
