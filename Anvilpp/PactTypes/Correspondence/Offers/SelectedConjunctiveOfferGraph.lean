import Anvilpp.PactTypes.Correspondence.Offers.ConjunctiveOfferResolvedEdge

/-!
# buildSelectedConjunctiveOfferAutomaton graph structure and its resolved-edge classifier
-/

namespace Pact

noncomputable section

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

end

end Pact
