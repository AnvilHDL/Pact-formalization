import Anvilpp.PactTypes.Correspondence.Offers.SelectedConjunctiveOfferGraph

/-!
# Child-edge case classifiers shared by the xoffer/offer step-correctness proofs
-/

namespace Pact

noncomputable section

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

end

end Pact
