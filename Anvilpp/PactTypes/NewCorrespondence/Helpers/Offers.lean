import Anvilpp.PactTypes.NewCorrespondence.Helpers.Parallel


namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def xofferRelationShape
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.xoffer alphabet elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType elseType))
        entry.1 q) ∨
    (∃ i action branchType q,
      branches[i]? = some (action, branchType) ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet branchType (compileType branchType))
        entry.1 q)

lemma relationMembership_xoffer_root
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) :
    relationMembership
      (buildRelationSet (.xoffer alphabet elseType branches)
        (compileType (.xoffer alphabet elseType branches)))
      (.xoffer alphabet elseType branches) .root := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.xoffer alphabet elseType branches : PactType), .root) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.xoffer alphabet elseType branches)) (.xoffer alphabet elseType branches)
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

lemma relationMembership_xoffer_else
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) {residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet elseType (compileType elseType))
      residual state) :
    relationMembership
      (buildRelationSet (.xoffer alphabet elseType branches)
        (compileType (.xoffer alphabet elseType branches)))
      residual (.child 0 state) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show (residual, .child 0 state) ∈ buildRelationSetCoreFuel
    (typeCompilationFuel (.xoffer alphabet elseType branches)) (.xoffer alphabet elseType branches)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(residual, state), ?_, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient elseType
    (le_max_left _ _) le_rfl]
  exact hRelated

lemma relationMembership_xoffer_branch
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {index : Nat} {action : BareMessage} {branchType residual : PactType}
    {state : TypeAutomatonState}
    (hGet : branches[index]? = some (action, branchType))
    (hRelated : relationMembership
      (buildRelationSet branchType (compileType branchType))
      residual state) :
    relationMembership
      (buildRelationSet (.xoffer alphabet elseType branches)
        (compileType (.xoffer alphabet elseType branches)))
      residual (.child (index + 1) state) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  have hMem : (action, branchType) ∈ branches :=
    List.mem_iff_getElem?.mpr ⟨index, hGet⟩
  have hBranchFuel : typeCompilationFuel branchType ≤
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) :=
    (typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) hMem).trans (le_max_right _ _)
  show (residual, .child (index + 1) state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.xoffer alphabet elseType branches)) (.xoffer alphabet elseType branches)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [mem_foldl_union_iff]
  apply Or.inr
  refine ⟨((action, branchType), index),
    List.mk_mem_zipIdx_iff_getElem?.mpr hGet, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(residual, state), ?_, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient branchType
    hBranchFuel le_rfl]
  exact hRelated

set_option maxHeartbeats 4000000 in
/-- Proves every related exclusive-offer pair has the exclusive-offer shape. -/
lemma relationMembership_xoffer_cases
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.xoffer alphabet elseType branches)
          (compileType (.xoffer alphabet elseType branches)))
        residual state) :
    xofferRelationShape alphabet elseType branches
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩ |
      ⟨item, hItem, entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · subst hResidual
    subst hState
    have hElseRelated : relationMembership
        (buildRelationSet elseType (compileType elseType))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel (typeCompilationFuel elseType)
          elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient elseType
        (le_max_left _ _) le_rfl]
      exact hEntry
    exact Or.inr (Or.inl ⟨entry.2, rfl, hElseRelated⟩)
  · subst hResidual
    subst hState
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hBranchMem : item.1 ∈ branches := List.mem_of_getElem? hGet
    have hBranchFuel : typeCompilationFuel item.1.2 ≤
        max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches) :=
      le_trans
        (typeCompilationFuel_le_typeBranchCompilationFuel
          branches item.1 hBranchMem)
        (le_max_right _ _)
    have hBranchRelated : relationMembership
        (buildRelationSet item.1.2 (compileType item.1.2))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel (typeCompilationFuel item.1.2)
          item.1.2
      rw [← buildRelationSetCoreFuel_eq_of_sufficient item.1.2
        hBranchFuel le_rfl]
      exact hEntry
    exact Or.inr (Or.inr ⟨item.2, item.1.1, item.1.2, entry.2,
      hGet, rfl, hBranchRelated⟩)

/-- Characterizes a public conjunctive-offer edge leaving a tagged else-child state as a copy of the else automaton's own outgoing edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_else
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton alphabet
      branches elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

/-- Characterizes a public conjunctive-offer edge leaving a tagged branch-`i`-child state as a copy of that branch's generated commit type's own outgoing edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_branch
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton alphabet
      branches elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = .child (i + 1) state ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet :
              selectedConjunctions[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton :=
          congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Proves a `.child 0`-tagged state's future menu, in a compiled conjunctive offer, agrees with the else child's own. -/
theorem computeFutureOf_selectedConjunctiveOffer_else
     {alphabet : PactTypeAlphabet}
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildSelectedConjunctiveOfferAutomaton alphabet branches
          (compileTypeFuel (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel
            (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))))
    (hElseAlphabet : elseType.alphabet = whole.alphabet)
    (hFuel : typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole)
    (hDisjoint : elseType.OfferBranchesDisjoint)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child 0 visited) =
        stateProductInfo elseType visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel (typeCompilationFuel elseType)
      elseType).states) :
    computeFutureOf whole (.child 0 state) =
      computeFutureOf elseType state := by
  classical
  let elseFragment :=
    compileTypeFuel (typeCompilationFuel elseType) elseType
  let selectedConjunctions := branches.map fun selected =>
    (selected.1, compileTypeFuel
      (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
      (parallelTypeBranchesSelecting alphabet selected branches))
  let parentFragment :=
    buildSelectedConjunctiveOfferAutomaton alphabet branches
      elseFragment selectedConjunctions
  have hCard : elseFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates 0 elseFragment).card = elseFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change elseFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    simp only [parentFragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union]
    exact Or.inl (Or.inr hTagged)
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole elseType
    (typeCompilationFuel whole) (typeCompilationFuel elseType)
    parentFragment elseFragment 0 hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient elseType) hDisjoint hElseAlphabet hFuel
    hProductInfo
    (fun q edge => buildSelectedConjunctiveOfferAutomaton_outgoing_else
      alphabet branches elseFragment selectedConjunctions q edge)
    hCard state (by simpa [elseFragment] using hState)

/-- Proves a `.child (i+1)`-tagged state's future menu, in a compiled conjunctive offer, agrees with branch `i`'s generated commit type's own. -/
theorem computeFutureOf_selectedConjunctiveOffer_branch
     {alphabet : PactTypeAlphabet}
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel (typeCompilationFuel whole) whole =
        buildSelectedConjunctiveOfferAutomaton alphabet branches
          (compileTypeFuel (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel
            (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))))
    (i : Nat) (selected : BareMessage × PactType)
    (hSelected : branches[i]? = some selected)
    (hFuel : typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches) +
      1 ≤ typeCompilationFuel whole)
    (hBranchAlphabet :
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        whole.alphabet)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hProductInfo : ∀ visited,
      stateProductInfo whole (.child (i + 1) visited) =
        stateProductInfo (parallelTypeBranchesSelecting alphabet selected branches)
          visited)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel
      (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
      (parallelTypeBranchesSelecting alphabet selected branches)).states) :
    computeFutureOf whole (.child (i + 1) state) =
      computeFutureOf (parallelTypeBranchesSelecting alphabet selected branches)
        state := by
  classical
  let elseFragment :=
    compileTypeFuel (typeCompilationFuel elseType) elseType
  let selectedConjunctions := branches.map fun branch =>
    (branch.1, compileTypeFuel
      (typeCompilationFuel (parallelTypeBranchesSelecting alphabet branch branches))
      (parallelTypeBranchesSelecting alphabet branch branches))
  let branchType := parallelTypeBranchesSelecting alphabet selected branches
  let branchFragment :=
    compileTypeFuel (typeCompilationFuel branchType) branchType
  let parentFragment :=
    buildSelectedConjunctiveOfferAutomaton alphabet branches
      elseFragment selectedConjunctions
  have hBranchFragment :
      selectedConjunctions[i]? = some (selected.1, branchFragment) := by
    simp [selectedConjunctions, branchFragment, branchType, List.getElem?_map,
      hSelected]
  have hCard : branchFragment.states.card ≤ parentFragment.states.card := by
    have hTaggedCard :
        (childStates (i + 1) branchFragment).card =
          branchFragment.states.card := by
      unfold childStates
      apply Finset.card_image_of_injective
      intro first second hEq
      simpa [childState] using hEq
    change branchFragment.states.card ≤ parentFragment.states.card
    rw [← hTaggedCard]
    apply Finset.card_le_card
    intro tagged hTagged
    have hIndexed : tagged ∈ indexedFragmentStates selectedConjunctions := by
      rw [indexedFragmentStates, mem_foldl_union_iff]
      exact Or.inr ⟨((selected.1, branchFragment), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranchFragment, hTagged⟩
    simp only [parentFragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, Finset.mem_union]
    exact Or.inr hIndexed
  unfold computeFutureOf
  exact computeFutureOfFuel_child_embedding whole branchType
    (typeCompilationFuel whole) (typeCompilationFuel branchType)
    parentFragment branchFragment (i + 1) hWhole rfl
    (typeCompilationFuel_sufficient whole)
    (typeCompilationFuel_sufficient branchType)
    (parallelTypeBranchesSelecting_offerBranchesDisjoint selected branches
      hDisjoint) hBranchAlphabet hFuel hProductInfo
    (fun q edge => buildSelectedConjunctiveOfferAutomaton_outgoing_branch
      alphabet branches elseFragment selectedConjunctions i selected.1
      branchFragment hBranchFragment q edge)
    hCard state (by simpa [branchFragment] using hState)

/-- Relates a branch's generated commit type found by index after mapping compiled fragments in to the same branch found by index in the original list. -/
theorem branches_map_selecting_getElem?_eq_some_iff
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment) :
    (branches.map fun selected => (selected.1, compileTypeFuel
        (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)))[i]? =
        some (action, automaton) ↔
      ∃ branchType, branches[i]? = some (action, branchType) ∧
        compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet (action, branchType) branches))
          (parallelTypeBranchesSelecting alphabet (action, branchType) branches) =
          automaton := by
  rw [List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨branchAction, branchType⟩, hGet, hEq⟩
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hAction, hAut⟩ := hEq
    subst hAction
    exact ⟨branchType, hGet, hAut⟩
  · rintro ⟨branchType, hGet, hAut⟩
    exact ⟨(action, branchType), hGet, by simp [hAut]⟩

/-- Defines the related-state shape for a compiled conjunctive offer: the root represents the whole offer, a tagged child represents a residual of `τ0` or a generated branch commit. -/
def offerRelationShape
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.offer alphabet elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType elseType))
        entry.1 q) ∨
    (∃ i selected q,
      branches[i]? = some selected ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting alphabet selected branches)
          (compileType
            (parallelTypeBranchesSelecting alphabet selected branches)))
        entry.1 q)

lemma relationMembership_offer_root
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) :
    relationMembership
      (buildRelationSet (.offer alphabet elseType branches)
        (compileType (.offer alphabet elseType branches)))
      (.offer alphabet elseType branches) .root := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.offer alphabet elseType branches : PactType), .root) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.offer alphabet elseType branches)) (.offer alphabet elseType branches)
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

lemma relationMembership_offer_else
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType)) {residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet elseType (compileType elseType))
      residual state) :
    relationMembership
      (buildRelationSet (.offer alphabet elseType branches)
        (compileType (.offer alphabet elseType branches)))
      residual (.child 0 state) := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show (residual, .child 0 state) ∈ buildRelationSetCoreFuel
    (typeCompilationFuel (.offer alphabet elseType branches)) (.offer alphabet elseType branches)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(residual, state), ?_, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient elseType
    (le_max_left _ _) le_rfl]
  exact hRelated

lemma relationMembership_offer_selected
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {index : Nat} {selected : BareMessage × PactType} {residual : PactType}
    {state : TypeAutomatonState}
    (hGet : branches[index]? = some selected)
    (hRelated : relationMembership
      (buildRelationSet (parallelTypeBranchesSelecting alphabet selected branches)
        (compileType (parallelTypeBranchesSelecting alphabet selected branches)))
      residual state) :
    relationMembership
      (buildRelationSet (.offer alphabet elseType branches)
        (compileType (.offer alphabet elseType branches)))
      residual (.child (index + 1) state) := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]
    omega
  have hSelectedFuel :
      typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches) ≤
        max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact le_max_right _ _
  show (residual, .child (index + 1) state) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.offer alphabet elseType branches)) (.offer alphabet elseType branches)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  rw [mem_foldl_union_iff]
  apply Or.inr
  refine ⟨(selected, index), List.mk_mem_zipIdx_iff_getElem?.mpr hGet, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(residual, state), ?_, rfl⟩
  rw [buildRelationSetCoreFuel_eq_of_sufficient
    (parallelTypeBranchesSelecting alphabet selected branches) hSelectedFuel le_rfl]
  exact hRelated

set_option maxHeartbeats 4000000 in
/-- Proves every related conjunctive-offer pair has the conjunctive-offer shape. -/
lemma relationMembership_offer_cases
     (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.offer alphabet elseType branches)
          (compileType (.offer alphabet elseType branches)))
        residual state) :
    offerRelationShape alphabet elseType branches
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩ |
      ⟨item, hItem, entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · subst hResidual
    subst hState
    have hElseRelated : relationMembership
        (buildRelationSet elseType (compileType elseType))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel (typeCompilationFuel elseType)
          elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient elseType
        (le_max_left _ _) le_rfl]
      exact hEntry
    exact Or.inr (Or.inl ⟨entry.2, rfl, hElseRelated⟩)
  · subst hResidual
    subst hState
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hSelectedFuel :
        typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet item.1 branches) ≤
          max (typeCompilationFuel elseType)
            (conjunctiveCompilationFuel branches) := by
      rw [typeCompilationFuel_parallelTypeBranchesSelecting]
      exact le_max_right _ _
    have hSelectedRelated : relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting alphabet item.1 branches)
          (compileType
            (parallelTypeBranchesSelecting alphabet item.1 branches)))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet item.1 branches))
          (parallelTypeBranchesSelecting alphabet item.1 branches)
      rw [← buildRelationSetCoreFuel_eq_of_sufficient
        (parallelTypeBranchesSelecting alphabet item.1 branches)
        hSelectedFuel le_rfl]
      exact hEntry
    exact Or.inr (Or.inr ⟨item.2, item.1, entry.2,
      hGet, rfl, hSelectedRelated⟩)


end


/-- A copied right component of a sequence keeps its own marker reach. -/
theorem buildSequenceAutomaton_markerReachable_right
    (left right : AutomatonFragment) (name : String)
    (hClosed : (⟨right.states, right.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hCard : right.states.card ≤ (buildSequenceAutomaton left right).states.card)
    (state : TypeAutomatonState) (hState : state ∈ right.states) :
    MarkerReachable (buildSequenceAutomaton left right) name
        (childState 1 state) ↔
      MarkerReachable right name state :=
  markerReachable_of_outgoing_childPendingEdge _ right 1 name
    (fun q edge => buildSequenceAutomaton_outgoing_right left right q edge)
    hClosed hCard state hState

/-- The copied default arm of an exclusive offer keeps its own marker reach. -/
theorem buildExclusiveOfferAutomaton_markerReachable_else
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (name : String)
    (hClosed : (⟨elseAutomaton.states, elseAutomaton.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hCard : elseAutomaton.states.card ≤
      (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata).states.card)
    (state : TypeAutomatonState) (hState : state ∈ elseAutomaton.states) :
    MarkerReachable (buildExclusiveOfferAutomaton alphabet branches
        elseAutomaton branchAutomata) name (childState 0 state) ↔
      MarkerReachable elseAutomaton name state :=
  markerReachable_of_outgoing_childPendingEdge _ elseAutomaton 0 name
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_else alphabet branches
      elseAutomaton branchAutomata q edge)
    hClosed hCard state hState

/-- A copied branch of an exclusive offer keeps its own marker reach. -/
theorem buildExclusiveOfferAutomaton_markerReachable_branch
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (name : String)
    (hBranch : branchAutomata[i]? = some (action, automaton))
    (hClosed : (⟨automaton.states, automaton.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hCard : automaton.states.card ≤
      (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
        branchAutomata).states.card)
    (state : TypeAutomatonState) (hState : state ∈ automaton.states) :
    MarkerReachable (buildExclusiveOfferAutomaton alphabet branches
        elseAutomaton branchAutomata) name (childState (i + 1) state) ↔
      MarkerReachable automaton name state :=
  markerReachable_of_outgoing_childPendingEdge _ automaton (i + 1) name
    (fun q edge => buildExclusiveOfferAutomaton_outgoing_branch alphabet
      branches elseAutomaton branchAutomata i action automaton hBranch q edge)
    hClosed hCard state hState

/-- The copied default arm of a conjunctive offer keeps its own marker reach. -/
theorem buildSelectedConjunctiveOfferAutomaton_markerReachable_else
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (name : String)
    (hClosed : (⟨elseAutomaton.states, elseAutomaton.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hCard : elseAutomaton.states.card ≤
      (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
        selectedConjunctions).states.card)
    (state : TypeAutomatonState) (hState : state ∈ elseAutomaton.states) :
    MarkerReachable (buildSelectedConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions) name (childState 0 state) ↔
      MarkerReachable elseAutomaton name state :=
  markerReachable_of_outgoing_childPendingEdge _ elseAutomaton 0 name
    (fun q edge => buildSelectedConjunctiveOfferAutomaton_outgoing_else alphabet
      branches elseAutomaton selectedConjunctions q edge)
    hClosed hCard state hState

/-- A copied branch of a conjunctive offer keeps its own marker reach. -/
theorem buildSelectedConjunctiveOfferAutomaton_markerReachable_branch
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (name : String)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (hClosed : (⟨automaton.states, automaton.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hCard : automaton.states.card ≤
      (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAutomaton
        selectedConjunctions).states.card)
    (state : TypeAutomatonState) (hState : state ∈ automaton.states) :
    MarkerReachable (buildSelectedConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions) name (childState (i + 1) state) ↔
      MarkerReachable automaton name state :=
  markerReachable_of_outgoing_childPendingEdge _ automaton (i + 1) name
    (fun q edge => buildSelectedConjunctiveOfferAutomaton_outgoing_branch
      alphabet branches elseAutomaton selectedConjunctions i action automaton
      hBranch q edge)
    hClosed hCard state hState

end Pact
