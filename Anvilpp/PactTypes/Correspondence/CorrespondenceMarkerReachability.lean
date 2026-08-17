import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosure

/-!
# Marker reachability vs. the syntactic marker analysis; compilationMarkerReachable_iff
-/

namespace Pact

noncomputable section

/-! ### Marker reachability against the syntactic marker analysis -/

/-- A branch list reaches a marker exactly when one of its continuations
does. -/
private theorem branchMarkerReachableSubst_iff_exists (name : String) :
    ∀ branches : List (BareMessage × PactType),
      (PactType.branchMarkerReachableSubst name branches = true ↔
        ∃ entry ∈ branches,
          PactType.markerReachableSubst name entry.2 = true) := by
  intro branches
  induction branches with
  | nil => simp [PactType.branchMarkerReachableSubst]
  | cons entry rest ih =>
      obtain ⟨action, branchType⟩ := entry
      simp only [PactType.branchMarkerReachableSubst, Bool.or_eq_true, ih,
        List.mem_cons]
      constructor
      · rintro (hHead | ⟨other, hOther, hValue⟩)
        · exact ⟨(action, branchType), Or.inl rfl, hHead⟩
        · exact ⟨other, Or.inr hOther, hValue⟩
      · rintro ⟨other, hOther | hOther, hValue⟩
        · exact Or.inl (by simpa [hOther] using hValue)
        · exact Or.inr ⟨other, hOther, hValue⟩

/-- An exclusive-offer root carries no marker: all five families of root edges
are visible. -/
private theorem not_buildExclusiveOfferAutomaton_markerSource_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (name : String) :
    ¬ MarkerSource (buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata) name .root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
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
      exact absurd hLabel (by simp)
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact absurd hLabel (by simp)
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact absurd hLabel (by simp)

/-- The same fact for the selected conjunctive-offer construction. -/
private theorem not_buildSelectedConjunctiveOfferAutomaton_markerSource_root
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (name : String) :
    ¬ MarkerSource (buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions) name .root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
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
      exact absurd hLabel (by simp)
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact absurd hLabel (by simp)
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact absurd hLabel (by simp)

/-- A lifted left sequence edge keeps its label, so a left component without
markers contributes no marker source at any tagged left state. -/
private theorem not_buildSequenceAutomaton_markerSource_left
    (signature : TypeAlphabet) (left right : AutomatonFragment) (name : String)
    (hLeftNoMarkers : ∀ edge ∈ left.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (state : TypeAutomatonState) :
    ¬ MarkerSource (buildSequenceAutomaton signature left right) name
      (.child 0 state) := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  rcases (buildSequenceAutomaton_outgoing_left signature left right state
    edge).mp ⟨hEdge, hSource⟩ with
    ⟨childEdge, hChildEdge, _, rfl⟩ | ⟨_, environment, _, rfl⟩ |
      ⟨_, environment, _, rfl⟩
  · exact hLeftNoMarkers childEdge hChildEdge (by simpa using hLabel)
  · exact absurd hLabel (by simp)
  · exact absurd hLabel (by simp)

/-- Marker reachability from a tagged left sequence state.  Markers can only be
found after the administrative bridge, so the condition is exactly "the left
residual may finish this cycle, and the right entry reaches a marker". -/
private theorem buildSequenceAutomaton_markerReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment) (name : String)
    (hLeftNoMarkers : ∀ edge ∈ left.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (MarkerReachable (buildSequenceAutomaton signature left right) name
        (.child 0 state) ↔
      ((∃ completed ∈ (sequenceExecutionAutomaton left).futureReachable state,
          completed ∈ left.accepting ∨ completed ∈ left.completing) ∧
        MarkerReachable right name right.initial)) := by
  classical
  have hReach := buildSequenceAutomaton_futureReachable_left signature left
    right state hLeftState hLeftTargets hRightTargets hRightInitial
  have hRightMarker : ∀ q, MarkerSource
      (buildSequenceAutomaton signature left right) name (childState 1 q) ↔
      MarkerSource right name q := by
    intro q
    exact markerSource_of_outgoing_childPendingEdge _ right 1 name q
      (fun edge => buildSequenceAutomaton_outgoing_right signature left right
        q edge)
  simp only [MarkerReachable]
  rw [show (⟨(buildSequenceAutomaton signature left right).states,
        (buildSequenceAutomaton signature left right).edges⟩ :
      PendingAutomaton).futureReachable (TypeAutomatonState.child 0 state) =
      ((sequenceExecutionAutomaton left).futureReachable state).image
          (childState 0) ∪
        (if ∃ completed ∈
              (sequenceExecutionAutomaton left).futureReachable state,
            completed ∈ left.accepting ∨ completed ∈ left.completing then
          ((⟨right.states, right.edges⟩ :
            PendingAutomaton).futureReachable right.initial).image
              (childState 1)
        else ∅) from hReach]
  by_cases hBridge : ∃ completed ∈
      (sequenceExecutionAutomaton left).futureReachable state,
      completed ∈ left.accepting ∨ completed ∈ left.completing
  · rw [if_pos hBridge]
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨reached, (⟨q, _, rfl⟩ | ⟨q, hq, rfl⟩), hMarker⟩
      · exact absurd hMarker (not_buildSequenceAutomaton_markerSource_left
          signature left right name hLeftNoMarkers q)
      · exact ⟨hBridge, ⟨q, hq, (hRightMarker q).mp hMarker⟩⟩
    · rintro ⟨_, q, hq, hMarker⟩
      exact ⟨childState 1 q, Or.inr ⟨q, hq, rfl⟩, (hRightMarker q).mpr hMarker⟩
  · rw [if_neg hBridge]
    simp only [Finset.union_empty, Finset.mem_image]
    constructor
    · rintro ⟨reached, ⟨q, _, rfl⟩, hMarker⟩
      exact absurd hMarker (not_buildSequenceAutomaton_markerSource_left
        signature left right name hLeftNoMarkers q)
    · rintro ⟨hAbsurd, _⟩
      exact absurd hAbsurd hBridge

/-- Tagging is injective, so a tagged carrier never shrinks. -/
private theorem card_le_of_childStates_subset
    (child parent : AutomatonFragment) (index : Nat)
    (hSubset : childStates index child ⊆ parent.states) :
    child.states.card ≤ parent.states.card := by
  calc child.states.card = (childStates index child).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
    _ ≤ parent.states.card := Finset.card_le_card hSubset

/-- Marker reachability at every represented state of a choice-like
constructor, given the two child correspondences.  Ordinary and fair choice
share `buildChoiceAutomaton`, so both use this one lemma. -/
private theorem buildChoiceAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftIH : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel left)
        left) name q ↔ PactType.markerReachableSubst name r = true))
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel right)
        right) name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildChoiceAutomaton signature
      (compileTypeFuel signature fuel left) (compileTypeFuel signature fuel right)
      selectionLeft selectionRight
    (MarkerReachable fragment name .root ↔
        (PactType.markerReachableSubst name left = true ∨
          PactType.markerReachableSubst name right = true)) ∧
      (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable fragment name (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hFuelDef
  set leftFragment := compileTypeFuel signature fuel left with hLeftDef
  set rightFragment := compileTypeFuel signature fuel right with hRightDef
  set fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight with hFragmentDef
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftClosed : (⟨leftFragment.states,
      leftFragment.edges⟩ : PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates leftFragment
      hLeftTargets
  have hRightClosed : (⟨rightFragment.states,
      rightFragment.edges⟩ : PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates rightFragment
      hRightTargets
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftCard : leftFragment.states.card ≤ fragment.states.card :=
    card_le_of_childStates_subset leftFragment fragment 0 (by
      intro child hChild
      simp [hFragmentDef, buildChoiceAutomaton, finishAutomatonFragment,
        hChild])
  have hRightCard : rightFragment.states.card ≤ fragment.states.card :=
    card_le_of_childStates_subset rightFragment fragment 1 (by
      intro child hChild
      simp [hFragmentDef, buildChoiceAutomaton, finishAutomatonFragment,
        hChild])
  have hLeftTagged : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable fragment name (.child 0 q) ↔
        PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ leftFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature left
        q r hr
      simpa [hLeftStable] using hCanonical
    rw [buildChoiceAutomaton_markerReachable_left signature leftFragment
      rightFragment selectionLeft selectionRight name q hLeftClosed hState
        hLeftCard, hLeftStable]
    exact hLeftIH q r hr
  have hRightTagged : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable fragment name (.child 1 q) ↔
        PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ rightFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature right
        q r hr
      simpa [hRightStable] using hCanonical
    rw [buildChoiceAutomaton_markerReachable_right signature leftFragment
      rightFragment selectionLeft selectionRight name q hRightClosed hState
        hRightCard, hRightStable]
    exact hRightIH q r hr
  refine ⟨?_, hLeftTagged, hRightTagged⟩
  have hRootIff : MarkerReachable fragment name .root ↔
      (MarkerReachable fragment name (.child 0 leftFragment.initial) ∨
        MarkerReachable fragment name (.child 1 rightFragment.initial)) :=
    buildChoiceAutomaton_markerReachable_root signature leftFragment
      rightFragment selectionLeft selectionRight name hSelectionLeft
        hSelectionRight hLeftTargets hRightTargets hLeftInitial hRightInitial
  rw [hRootIff,
    hLeftTagged leftFragment.initial left (by
      rw [hLeftStable]
      exact compileTypeFuel_initial_relation signature
        (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)),
    hRightTagged rightFragment.initial right (by
      rw [hRightStable]
      exact compileTypeFuel_initial_relation signature
        (typeCompilationFuel right) right
          (typeCompilationFuel_sufficient right))]

/-- Marker reachability at every represented state of a sequence.  The left
component cannot hold a marker (tail occurrence forbids it), so a marker is
found exactly after the administrative bridge. -/
private theorem buildSequenceAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (left right : PactType) (name : String)
    (hLeftAbsent : left.TailOccurrences name False)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (compileTypeFuel signature (typeCompilationFuel right)
        right) name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildSequenceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
    (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name (.seq r right) = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable fragment name (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hFuelDef
  set leftFragment := compileTypeFuel signature fuel left with hLeftDef
  set rightFragment := compileTypeFuel signature fuel right with hRightDef
  set fragment := buildSequenceAutomaton signature leftFragment rightFragment
    with hFragmentDef
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hRightClosed : (⟨rightFragment.states,
      rightFragment.edges⟩ : PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates rightFragment
      hRightTargets
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRightCard : rightFragment.states.card ≤ fragment.states.card :=
    card_le_of_childStates_subset rightFragment fragment 1 (by
      intro child hChild
      simp [hFragmentDef, buildSequenceAutomaton, finishAutomatonFragment,
        hChild])
  have hLeftNoMarkers : ∀ edge ∈ leftFragment.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name := by
    intro edge hEdge hLabel
    exact (compileTypeFuel_variableEdge_source_var signature name fuel left
      False hLeftFuel hLeftAbsent edge hEdge hLabel).1
  have hRightTagged : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable fragment name (.child 1 q) ↔
        PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ rightFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature right
        q r hr
      simpa [hRightStable] using hCanonical
    have hTransport : MarkerReachable fragment name (childState 1 q) ↔
        MarkerReachable rightFragment name q :=
      markerReachable_of_outgoing_childPendingEdge fragment rightFragment 1
        name
        (fun current edge => buildSequenceAutomaton_outgoing_right signature
          leftFragment rightFragment current edge)
        hRightClosed hRightCard q hState
    rw [show (TypeAutomatonState.child 1 q) = childState 1 q from rfl,
      hTransport, hRightStable]
    exact hRightIH q r hr
  have hRightEntry : MarkerReachable rightFragment name rightFragment.initial ↔
      PactType.markerReachableSubst name right = true := by
    rw [hRightStable]
    exact hRightIH _ right (compileTypeFuel_initial_relation signature
      (typeCompilationFuel right) right
        (typeCompilationFuel_sufficient right))
  refine ⟨?_, hRightTagged⟩
  intro q r hr
  have hState : q ∈ leftFragment.states := by
    have hCanonical := compilationStateCorrect_of_compilation signature left
      q r hr
    simpa [hLeftStable] using hCanonical
  have hBridge : (∃ completed ∈
        (sequenceExecutionAutomaton leftFragment).futureReachable q,
      completed ∈ leftFragment.accepting ∨
        completed ∈ leftFragment.completing) ↔
      r.CanCompleteBeforeTock = true := by
    have hCanonical := hLeftExecution q r hr
    simpa [CompilationSequenceExecutionCorrect, hLeftStable] using hCanonical.2
  show MarkerReachable fragment name (childState 0 q) ↔
    PactType.markerReachableSubst name (.seq r right) = true
  have hLeftIffRaw : MarkerReachable fragment name (childState 0 q) ↔
      ((∃ completed ∈
          (sequenceExecutionAutomaton leftFragment).futureReachable q,
          completed ∈ leftFragment.accepting ∨
            completed ∈ leftFragment.completing) ∧
        MarkerReachable rightFragment name rightFragment.initial) :=
    buildSequenceAutomaton_markerReachable_left signature leftFragment
      rightFragment name hLeftNoMarkers q hState hLeftTargets hRightTargets
        hRightInitial
  rw [hLeftIffRaw, hBridge, hRightEntry, PactType.markerReachableSubst]
  simp [Bool.and_eq_true]

private theorem exists_getElem?_of_mem
    {Element : Type} {element : Element} {items : List Element}
    (hMember : element ∈ items) :
    ∃ index : Nat, items[index]? = some element := by
  rcases List.mem_iff_getElem.mp hMember with ⟨index, hBound, hValue⟩
  exact ⟨index, by rw [List.getElem?_eq_getElem hBound, hValue]⟩

private theorem mem_zipIdx_of_getElem?
    {Element : Type} {items : List Element} {index : Nat} {element : Element}
    (hEntry : items[index]? = some element) :
    (element, index) ∈ items.zipIdx := by
  rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
  have hZipBound : index < items.zipIdx.length := by simpa using hBound
  have hMember := List.getElem_mem hZipBound
  have hAt := List.getElem_zipIdx (l := items) (i := index) (j := 0) hZipBound
  simp only [zero_add] at hAt
  rw [hAt, hValue] at hMember
  exact hMember

/-- Marker reachability at every represented state of an exclusive offer. -/
private theorem buildExclusiveOfferAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (compileTypeFuel signature
        (typeCompilationFuel elseType) elseType) name q ↔
          PactType.markerReachableSubst name r = true))
    (hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable (compileTypeFuel signature
          (typeCompilationFuel branchType) branchType) name q ↔
            PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (typeBranchCompilationFuel branches)
    let fragment := buildExclusiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))
    (MarkerReachable fragment name .root ↔
        PactType.markerReachableSubst name (.xoffer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
        branches[index]? = some (action, branchType) →
        ∀ q r, TypeCompilationRelation branchType q r →
          (MarkerReachable fragment name (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches) with hFuelDef
  set elseFragment := compileTypeFuel signature fuel elseType with hElseDef
  set branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2) with hAutomataDef
  set fragment := buildExclusiveOfferAutomaton signature branches elseFragment
    branchAutomata with hFragmentDef
  set entries := exclusiveOfferEntryStates elseFragment branchAutomata
    with hEntriesDef
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hElseStable : elseFragment =
      compileTypeFuel signature (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hBranchFuel : ∀ branch ∈ branches,
      TypeCompilationFuelSufficient branch.2 fuel := by
    intro branch hBranch
    exact (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
      hBranch).trans (by simp [hFuelDef])
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      (hBranchFuel branch hBranch)
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel branch.2
      (hBranchFuel branch hBranch)
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildExclusiveOfferAutomaton_futureTargetsInStates signature branches
      elseFragment branchAutomata hElseTargets hBranchTargets hElseInitial
        hBranchInitial
  have hClosed : (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
      hFragmentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [hFragmentDef, buildExclusiveOfferAutomaton, finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2 branch hBranch
  have hUpper : (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).referencedStates .root ⊆ insert .root entries :=
    buildExclusiveOfferAutomaton_root_references_upper signature branches
      elseFragment branchAutomata
  have hEntriesSubset : entries ⊆ (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).referencedStates .root :=
    buildExclusiveOfferAutomaton_entries_referenced signature branches
      elseFragment branchAutomata hAvailable
  have hElseCard : elseFragment.states.card ≤ fragment.states.card :=
    card_le_of_childStates_subset elseFragment fragment 0 (by
      intro child hChild
      simp only [hFragmentDef, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      exact Or.inl (Or.inr hChild))
  have hElseClosed : (⟨elseFragment.states, elseFragment.edges⟩ :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates elseFragment
      hElseTargets
  have hElseTagged : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable fragment name (.child 0 q) ↔
        PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ elseFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        elseType q r hr
      simpa [hElseStable] using hCanonical
    have hTransport : MarkerReachable fragment name (childState 0 q) ↔
        MarkerReachable elseFragment name q :=
      markerReachable_of_outgoing_childPendingEdge fragment elseFragment 0 name
        (fun current edge => buildExclusiveOfferAutomaton_outgoing_else
          signature branches elseFragment branchAutomata current edge)
        hElseClosed hElseCard q hState
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      hTransport, hElseStable]
    exact hElseIH q r hr
  have hBranchTagged : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable fragment name (.child (index + 1) q) ↔
          PactType.markerReachableSubst name r = true) := by
    intro action branchType index hSyntaxEntry q r hr
    have hMember : (action, branchType) ∈ branches := by
      rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with ⟨hBound, hValue⟩
      have hAt := List.getElem_mem hBound
      simpa [hValue] using hAt
    have hAutomatonEntry : branchAutomata[index]? =
        some (action, compileTypeFuel signature fuel branchType) := by
      simp [hAutomataDef, List.getElem?_map, hSyntaxEntry]
    have hBranchStable : compileTypeFuel signature fuel branchType =
        compileTypeFuel signature (typeCompilationFuel branchType) branchType :=
      compileTypeFuel_eq_of_sufficient signature branchType
        (hBranchFuel (action, branchType) hMember)
          (typeCompilationFuel_sufficient branchType)
    have hState : q ∈ (compileTypeFuel signature fuel branchType).states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        branchType q r hr
      simpa [hBranchStable] using hCanonical
    have hBranchClosed : (⟨(compileTypeFuel signature fuel branchType).states,
        (compileTypeFuel signature fuel branchType).edges⟩ :
          PendingAutomaton).ReferencesClosed :=
      PendingAutomaton.referencesClosed_of_futureTargetsInStates _
        (compileTypeFuel_futureTargetsInStates signature fuel branchType
          (hBranchFuel (action, branchType) hMember))
    have hCard : (compileTypeFuel signature fuel branchType).states.card ≤
        fragment.states.card :=
      card_le_of_childStates_subset _ fragment (index + 1) (by
        intro child hChild
        simp only [childStates, Finset.mem_image] at hChild
        rcases hChild with ⟨inner, hInner, rfl⟩
        have hIndexedState : childState (index + 1) inner ∈
            indexedFragmentStates branchAutomata := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, compileTypeFuel signature fuel branchType), index),
            mem_zipIdx_of_getElem? hAutomatonEntry,
            by simp [childStates, childState, hInner]⟩
        simp [hFragmentDef, buildExclusiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState])
    have hTransport : MarkerReachable fragment name
        (childState (index + 1) q) ↔
        MarkerReachable (compileTypeFuel signature fuel branchType) name q :=
      markerReachable_of_outgoing_childPendingEdge fragment
        (compileTypeFuel signature fuel branchType) (index + 1) name
        (fun current edge => buildExclusiveOfferAutomaton_outgoing_branch
          signature branches elseFragment branchAutomata index
            (action, compileTypeFuel signature fuel branchType)
              hAutomatonEntry current edge)
        hBranchClosed hCard q hState
    rw [show (TypeAutomatonState.child (index + 1) q) =
      childState (index + 1) q from rfl, hTransport, hBranchStable]
    exact hBranchIH action branchType index hSyntaxEntry q r hr
  have hElseEntryRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    rw [hElseStable]
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel elseType) elseType
        (typeCompilationFuel_sufficient elseType)
  refine ⟨?_, hElseTagged, hBranchTagged⟩
  have hRootIff : MarkerReachable fragment name .root ↔
      (MarkerSource fragment name .root ∨
        ∃ entry ∈ entries, MarkerReachable fragment name entry) :=
    markerReachable_root_of_entries fragment name .root entries hClosed hRoot
      hUpper hEntriesSubset
  rw [hRootIff, PactType.markerReachableSubst]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd hMarker
        (not_buildExclusiveOfferAutomaton_markerSource_root signature branches
          elseFragment branchAutomata name)
    · rw [hEntriesDef, exclusiveOfferEntryStates, Finset.mem_union,
        Finset.mem_singleton] at hEntry
      rcases hEntry with rfl | hBranchEntry
      · have hValue := (hElseTagged elseFragment.initial elseType
          hElseEntryRelation).mp hInner
        simp [hValue]
      · rw [mem_foldl_union_iff] at hBranchEntry
        rcases hBranchEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
        · simp at hEmpty
        · rw [Finset.mem_singleton] at hEntryState
          subst entry
          rcases compiledBranch_zipIdx_cases signature fuel branches indexed
              (by simpa [hAutomataDef] using hIndexed) with
            ⟨action, branchType, hSyntaxEntry, hCompiledEntry⟩
          rcases indexed with ⟨compiledEntry, index⟩
          simp only at hCompiledEntry
          subst compiledEntry
          have hMember : (action, branchType) ∈ branches := by
            rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
              ⟨hBound, hValue⟩
            have hAt := List.getElem_mem hBound
            simpa [hValue] using hAt
          have hBranchStable : compileTypeFuel signature fuel branchType =
              compileTypeFuel signature (typeCompilationFuel branchType)
                branchType :=
            compileTypeFuel_eq_of_sufficient signature branchType
              (hBranchFuel (action, branchType) hMember)
                (typeCompilationFuel_sufficient branchType)
          have hBranchEntryRelation : TypeCompilationRelation branchType
              (compileTypeFuel signature fuel branchType).initial branchType := by
            rw [hBranchStable]
            exact compileTypeFuel_initial_relation signature
              (typeCompilationFuel branchType) branchType
                (typeCompilationFuel_sufficient branchType)
          have hValue := (hBranchTagged action branchType index hSyntaxEntry
            (compileTypeFuel signature fuel branchType).initial branchType
              hBranchEntryRelation).mp hInner
          have hFold := (branchMarkerReachableSubst_iff_exists name
            branches).mpr ⟨(action, branchType), hMember, hValue⟩
          simp [hFold]
  · intro hValue
    simp only [Bool.or_eq_true] at hValue
    right
    rcases hValue with hElseValue | hBranchValue
    · refine ⟨childState 0 elseFragment.initial, ?_, ?_⟩
      · rw [hEntriesDef, exclusiveOfferEntryStates]
        simp
      · exact (hElseTagged elseFragment.initial elseType
          hElseEntryRelation).mpr hElseValue
    · rcases (branchMarkerReachableSubst_iff_exists name branches).mp
        hBranchValue with ⟨entry, hMember, hEntryValue⟩
      rcases exists_getElem?_of_mem hMember with ⟨index, hIndex⟩
      obtain ⟨action, branchType⟩ := entry
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, compileTypeFuel signature fuel branchType) := by
        simp [hAutomataDef, List.getElem?_map, hIndex]
      have hBranchStable : compileTypeFuel signature fuel branchType =
          compileTypeFuel signature (typeCompilationFuel branchType)
            branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType
          (hBranchFuel (action, branchType) hMember)
            (typeCompilationFuel_sufficient branchType)
      have hBranchEntryRelation : TypeCompilationRelation branchType
          (compileTypeFuel signature fuel branchType).initial branchType := by
        rw [hBranchStable]
        exact compileTypeFuel_initial_relation signature
          (typeCompilationFuel branchType) branchType
            (typeCompilationFuel_sufficient branchType)
      refine ⟨childState (index + 1)
        (compileTypeFuel signature fuel branchType).initial, ?_, ?_⟩
      · rw [hEntriesDef, exclusiveOfferEntryStates, Finset.mem_union,
          mem_foldl_union_iff]
        right
        right
        exact ⟨((action, compileTypeFuel signature fuel branchType), index),
          mem_zipIdx_of_getElem? hAutomatonEntry, by simp⟩
      · exact (hBranchTagged action branchType index hIndex
          (compileTypeFuel signature fuel branchType).initial branchType
            hBranchEntryRelation).mpr hEntryValue

theorem selectedConjunction_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches))).zipIdx) :
    ∃ selected : BareMessage × PactType,
      branches[indexed.2]? = some selected ∧
        indexed.1 = (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) := by
  have hFields := List.mem_zipIdx hIndexed
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
  rcases hFields with ⟨hBound, hValue⟩
  have hAt :
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)))[indexed.2]? =
          some indexed.1 := by
    rw [List.getElem?_eq_getElem hBound, hValue]
  rw [List.getElem?_map] at hAt
  cases hOriginal : branches[indexed.2]? with
  | none => simp [hOriginal] at hAt
  | some selected =>
      simp only [hOriginal, Option.map_some, Option.some.injEq] at hAt
      exact ⟨selected, rfl, hAt.symm⟩

private theorem tailOccurrences_false_of_branch_mem (name : String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
      ∀ entry ∈ branches, PactType.TailOccurrences name False entry.2 := by
  intro branches
  induction branches with
  | nil => intro _ entry hEntry; simp at hEntry
  | cons branch rest ih =>
      obtain ⟨action, branchType⟩ := branch
      intro hTail entry hEntry
      simp only [PactType.TailBranchOccurrences] at hTail
      rcases List.mem_cons.mp hEntry with rfl | hRest
      · exact hTail.1
      · exact ih hTail.2 entry hRest

/-- Marker reachability at every represented state of a conjunctive offer.  A
generated conjunction lies below a product, where tail occurrence forbids the
marker outright, so only the else continuation contributes. -/
private theorem buildSelectedConjunctiveOfferAutomaton_markerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesAbsent : PactType.TailBranchOccurrences name False branches)
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (compileTypeFuel signature
        (typeCompilationFuel elseType) elseType) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (conjunctiveCompilationFuel branches)
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)))
    (MarkerReachable fragment name .root ↔
        PactType.markerReachableSubst name (.offer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable fragment name (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (selected : BareMessage × PactType) (index : Nat),
        branches[index]? = some selected →
        ∀ q r, TypeCompilationRelation
            (parallelTypeBranchesSelecting selected branches) q r →
          (MarkerReachable fragment name (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches) with hFuelDef
  set elseFragment := compileTypeFuel signature fuel elseType with hElseDef
  set selectedConjunctions := branches.map fun selected =>
    (selected.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting selected branches)) with hConjDef
  set fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions with hFragmentDef
  set entries := selectedConjunctiveOfferEntryStates elseFragment
    selectedConjunctions with hEntriesDef
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hElseStable : elseFragment =
      compileTypeFuel signature (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hSelectedFuel : ∀ selected : BareMessage × PactType,
      TypeCompilationFuelSufficient
        (parallelTypeBranchesSelecting selected branches) fuel := by
    intro selected
    simp [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, hFuelDef]
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hConjTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel _
      (hSelectedFuel selected)
  have hConjInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel _ (hSelectedFuel selected)
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates signature
      branches elseFragment selectedConjunctions hElseTargets hConjTargets
        hElseInitial hConjInitial
  have hClosed : (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
      hFragmentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, hSelected, rfl⟩
    exact supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2 selected hSelected
  have hUpper : (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).referencedStates .root ⊆ insert .root entries :=
    buildSelectedConjunctiveOfferAutomaton_root_references_upper signature
      branches elseFragment selectedConjunctions
  have hEntriesSubset : entries ⊆ (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).referencedStates .root :=
    buildSelectedConjunctiveOfferAutomaton_entries_referenced signature
      branches elseFragment selectedConjunctions hAvailable
  have hElseCard : elseFragment.states.card ≤ fragment.states.card :=
    card_le_of_childStates_subset elseFragment fragment 0 (by
      intro child hChild
      simp only [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      exact Or.inl (Or.inr hChild))
  have hElseClosed : (⟨elseFragment.states, elseFragment.edges⟩ :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates elseFragment
      hElseTargets
  have hElseTagged : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable fragment name (.child 0 q) ↔
        PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ elseFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        elseType q r hr
      simpa [hElseStable] using hCanonical
    have hTransport : MarkerReachable fragment name (childState 0 q) ↔
        MarkerReachable elseFragment name q :=
      markerReachable_of_outgoing_childPendingEdge fragment elseFragment 0 name
        (fun current edge =>
          buildSelectedConjunctiveOfferAutomaton_outgoing_else signature
            branches elseFragment selectedConjunctions current edge)
        hElseClosed hElseCard q hState
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      hTransport, hElseStable]
    exact hElseIH q r hr
  have hConjTagged : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
      ∀ q r, TypeCompilationRelation
          (parallelTypeBranchesSelecting selected branches) q r →
        (MarkerReachable fragment name (.child (index + 1) q) ↔
          PactType.markerReachableSubst name r = true) := by
    intro selected index hSyntaxEntry q r hr
    have hAbsent : PactType.TailOccurrences name False
        (parallelTypeBranchesSelecting selected branches) :=
      tailOccurrences_parallelTypeBranchesSelecting name selected branches
        hBranchesAbsent
    have hConjEntry : selectedConjunctions[index]? =
        some (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) := by
      simp [hConjDef, List.getElem?_map, hSyntaxEntry]
    have hState : q ∈ (compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)).states := by
      have hStable : compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches) =
          compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected
              branches)) (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
          (typeCompilationFuel_sufficient _)
      have hCanonical := compilationStateCorrect_of_compilation signature
        (parallelTypeBranchesSelecting selected branches) q r hr
      simpa [hStable] using hCanonical
    have hConjClosed : (⟨(compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)).states,
        (compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)).edges⟩ :
            PendingAutomaton).ReferencesClosed :=
      PendingAutomaton.referencesClosed_of_futureTargetsInStates _
        (compileTypeFuel_futureTargetsInStates signature fuel _
          (hSelectedFuel selected))
    have hCard : (compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)).states.card ≤
        fragment.states.card :=
      card_le_of_childStates_subset _ fragment (index + 1) (by
        intro child hChild
        simp only [childStates, Finset.mem_image] at hChild
        rcases hChild with ⟨inner, hInner, rfl⟩
        have hIndexedState : childState (index + 1) inner ∈
            indexedFragmentStates selectedConjunctions := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches)), index),
            mem_zipIdx_of_getElem? hConjEntry,
            by simp [childStates, childState, hInner]⟩
        simp [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState])
    have hTransport : MarkerReachable fragment name
        (childState (index + 1) q) ↔
        MarkerReachable (compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) name q :=
      markerReachable_of_outgoing_childPendingEdge fragment _ (index + 1) name
        (fun current edge =>
          buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction signature
            branches elseFragment selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) hConjEntry
                  current edge)
        hConjClosed hCard q hState
    have hNoGraph : ¬ MarkerReachable (compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)) name q :=
      not_markerReachable_of_tailOccurrences_false signature name fuel _
        (hSelectedFuel selected) hAbsent q
    have hNoSyntax : PactType.markerReachableSubst name r = false :=
      PactType.markerReachableSubst_eq_false_of_tailOccurrences_false name r
        (compilationRelation_tailOccurrences_false name hr hAbsent)
    rw [show (TypeAutomatonState.child (index + 1) q) =
      childState (index + 1) q from rfl, hTransport, hNoSyntax]
    simp [hNoGraph]
  have hElseEntryRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    rw [hElseStable]
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel elseType) elseType
        (typeCompilationFuel_sufficient elseType)
  have hBranchNone : PactType.branchMarkerReachableSubst name branches =
      false := by
    by_contra hContra
    rcases (branchMarkerReachableSubst_iff_exists name branches).mp
      (by simpa using hContra) with ⟨entry, hMember, hValue⟩
    rw [PactType.markerReachableSubst_eq_false_of_tailOccurrences_false name
      entry.2 (tailOccurrences_false_of_branch_mem name branches
        hBranchesAbsent entry hMember)] at hValue
    exact absurd hValue (by simp)
  refine ⟨?_, hElseTagged, hConjTagged⟩
  have hRootIff : MarkerReachable fragment name .root ↔
      (MarkerSource fragment name .root ∨
        ∃ entry ∈ entries, MarkerReachable fragment name entry) :=
    markerReachable_root_of_entries fragment name .root entries hClosed hRoot
      hUpper hEntriesSubset
  rw [hRootIff, PactType.markerReachableSubst, hBranchNone]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd hMarker
        (not_buildSelectedConjunctiveOfferAutomaton_markerSource_root signature
          branches elseFragment selectedConjunctions name)
    · rw [hEntriesDef, selectedConjunctiveOfferEntryStates, Finset.mem_union,
        Finset.mem_singleton] at hEntry
      rcases hEntry with rfl | hConjEntry
      · have hValue := (hElseTagged elseFragment.initial elseType
          hElseEntryRelation).mp hInner
        simp [hValue]
      · rw [mem_foldl_union_iff] at hConjEntry
        rcases hConjEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
        · simp at hEmpty
        · rw [Finset.mem_singleton] at hEntryState
          subst entry
          rcases selectedConjunction_zipIdx_cases signature fuel branches
              indexed (by simpa [hConjDef] using hIndexed) with
            ⟨selected, hSyntaxEntry, hCompiledEntry⟩
          rcases indexed with ⟨compiledEntry, index⟩
          simp only at hCompiledEntry
          subst compiledEntry
          exfalso
          have hStable : compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches) =
              compileTypeFuel signature
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) :=
            compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
              (typeCompilationFuel_sufficient _)
          have hInitRelation : TypeCompilationRelation
              (parallelTypeBranchesSelecting selected branches)
              (compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)).initial
              (parallelTypeBranchesSelecting selected branches) := by
            rw [hStable]
            exact compileTypeFuel_initial_relation signature _ _
              (typeCompilationFuel_sufficient _)
          have hValue := (hConjTagged selected index hSyntaxEntry _ _
            hInitRelation).mp hInner
          rw [PactType.markerReachableSubst_eq_false_of_tailOccurrences_false
            name _ (tailOccurrences_parallelTypeBranchesSelecting name selected
              branches hBranchesAbsent)] at hValue
          exact absurd hValue (by simp)
  · intro hValue
    simp only [Bool.or_false] at hValue
    exact Or.inr ⟨childState 0 elseFragment.initial, by
      rw [hEntriesDef, selectedConjunctiveOfferEntryStates]
      simp, (hElseTagged elseFragment.initial elseType
        hElseEntryRelation).mpr hValue⟩

theorem tailOccurrences_branch_of_mem (name : String) (tail : Prop) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name tail branches →
      ∀ entry ∈ branches, PactType.TailOccurrences name tail entry.2 := by
  intro branches
  induction branches with
  | nil => intro _ entry hEntry; simp at hEntry
  | cons branch rest ih =>
      obtain ⟨action, branchType⟩ := branch
      intro hTail entry hEntry
      simp only [PactType.TailBranchOccurrences] at hTail
      rcases List.mem_cons.mp hEntry with rfl | hRest
      · exact hTail.1
      · exact ih hTail.2 entry hRest

private theorem branch_sizeOf_lt (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hMember : entry ∈ branches) :
    sizeOf entry.2 < sizeOf (PactType.xoffer elseType branches) ∧
      sizeOf entry.2 < sizeOf (PactType.offer elseType branches) := by
  have hPair := List.sizeOf_lt_of_mem hMember
  have hComponent : sizeOf entry.2 < sizeOf entry := by
    rcases entry
    simp_wf
    omega
  constructor <;> (simp_wf; omega)

/-- Tail absence excludes a marker from the execution view as well: execution
changes only future decoration, never edge labels or sources. -/
private theorem not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
    (signature : TypeAlphabet) (name : String) (fuel : Nat)
    (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences name False)
    (state : TypeAutomatonState) :
    ¬ MarkerReachable
      (sequenceExecutionFragment
        (compileTypeFuel signature fuel processType)) name state := by
  apply not_markerReachable_of_no_marker_edges
  intro executionEdge hExecutionEdge hLabel
  simp only [sequenceExecutionFragment, sequenceExecutionAutomaton,
    Finset.mem_image] at hExecutionEdge
  rcases hExecutionEdge with ⟨rawEdge, hRawEdge, rfl⟩
  have hRawLabel : rawEdge.label =
      AutomatonConstructionLabel.variable name := by
    simpa using hLabel
  exact (compileTypeFuel_variableEdge_source_var signature name fuel
    processType False hFuel hTail rawEdge hRawEdge hRawLabel).1

/-- Under the tail-occurrence discipline, the bookkeeping target of every
still-symbolic variable edge is a sink.  Constructor tagging preserves that
fact; sequence-left, parallel, and conjunctive-offer product positions cannot
contain such an edge at all. -/
private theorem compileTypeFuel_variableEdge_target_sink
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      processType.TailOccurrences name True →
      ∀ marker ∈ (compileTypeFuel signature fuel processType).edges,
        marker.label = AutomatonConstructionLabel.variable name →
        ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
          edge.source ≠ marker.target := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hTail marker hMarker hMarkerLabel edge hEdge
      cases processType with
      | skip =>
          exact (compileTypeFuel_variableEdge_source_var signature name
            (fuel + 1) .skip False hFuel (by simp [PactType.TailOccurrences])
              marker hMarker hMarkerLabel).1.elim
      | message msg dir =>
          exact (compileTypeFuel_variableEdge_source_var signature name
            (fuel + 1) (.message msg dir) False hFuel
              (by simp [PactType.TailOccurrences]) marker hMarker
                hMarkerLabel).1.elim
      | progress pid =>
          exact (compileTypeFuel_variableEdge_source_var signature name
            (fuel + 1) (.progress pid) False hFuel
              (by simp [PactType.TailOccurrences]) marker hMarker
                hMarkerLabel).1.elim
      | tock =>
          exact (compileTypeFuel_variableEdge_source_var signature name
            (fuel + 1) .tock False hFuel (by simp [PactType.TailOccurrences])
              marker hMarker hMarkerLabel).1.elim
      | var other =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image] at hMarker hEdge
          rcases hMarker with ⟨markerEnvironment, _, rfl⟩
          rcases hEdge with ⟨edgeEnvironment, _, rfl⟩
          simp
      | recur binder body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
              at hMarker hEdge
          rcases hMarker with hHeader | ⟨bodyMarker, hBodyMarker, rfl⟩
          · rcases hHeader with ⟨environment, _, rfl⟩
            exact absurd hMarkerLabel (by simp)
          · by_cases hBinderMarker : bodyMarker.label =
                AutomatonConstructionLabel.variable binder
            · simp [hBinderMarker] at hMarkerLabel
            · have hBodyMarkerLabel : bodyMarker.label =
                  AutomatonConstructionLabel.variable name := by
                simpa [hBinderMarker] using hMarkerLabel
              have hDistinct : binder ≠ name := by
                intro hEq
                subst binder
                exact hBinderMarker hBodyMarkerLabel
              have hBodyTail : body.TailOccurrences name True := by
                simpa [PactType.TailOccurrences, hDistinct] using hTail
              intro hSource
              rcases hEdge with hHeader | ⟨bodyEdge, hBodyEdge, rfl⟩
              · rcases hHeader with ⟨environment, _, rfl⟩
                simp [hBinderMarker, childState] at hSource
              · by_cases hBodyEdgeBinder : bodyEdge.label =
                    AutomatonConstructionLabel.variable binder
                · simp [hBinderMarker, hBodyEdgeBinder, childState] at hSource
                  exact ih body hBodyFuel hBodyTail bodyMarker hBodyMarker
                    hBodyMarkerLabel bodyEdge hBodyEdge (by simpa using hSource)
                · simp [hBinderMarker, hBodyEdgeBinder, childPendingEdge,
                    childState] at hSource
                  exact ih body hBodyFuel hBodyTail bodyMarker hBodyMarker
                    hBodyMarkerLabel bodyEdge hBodyEdge hSource
      | choice left right | fairChoice _ left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailOccurrences name True ∧
              right.TailOccurrences name True := by
            simpa [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton] at hMarker
          rcases hMarker with (hLeft | hRight) | hSelection
          · rcases hLeft with ⟨childMarker, hChildMarker, rfl⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              simpa [childPendingEdge] using hMarkerLabel
            intro hSource
            have hOutgoing := (buildChoiceAutomaton_outgoing_left signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right) _ _ childMarker.target
                edge).mp ⟨hEdge, by
                  simpa [childPendingEdge, childState] using hSource⟩
            rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
            exact ih left hLeftFuel hTailFields.1 childMarker hChildMarker
              hChildLabel childEdge hChildEdge hChildSource
          · rcases hRight with ⟨childMarker, hChildMarker, rfl⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              simpa [childPendingEdge] using hMarkerLabel
            intro hSource
            have hOutgoing := (buildChoiceAutomaton_outgoing_right signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right) _ _ childMarker.target
                edge).mp ⟨hEdge, by
                  simpa [childPendingEdge, childState] using hSource⟩
            rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
            exact ih right hRightFuel hTailFields.2 childMarker hChildMarker
              hChildLabel childEdge hChildEdge hChildSource
          · rcases hSelection with ⟨environment, _, hEq | hEq⟩ <;>
              (rw [hEq] at hMarkerLabel; exact absurd hMarkerLabel (by simp))
      | seq left right =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hTailFields : left.TailOccurrences name False ∧
              right.TailOccurrences name True := by
            simpa [PactType.TailOccurrences] using hTail
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion] at hMarker
          rcases hMarker with ((hLeft | hRight) | hBridge) | hFutureBridge
          · rcases hLeft with ⟨childMarker, hChildMarker, hEq⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              rw [← hEq] at hMarkerLabel
              simpa using hMarkerLabel
            have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
              simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                at hFuel ⊢
              omega
            exact (compileTypeFuel_variableEdge_source_var signature name fuel
              left False hLeftFuel hTailFields.1 childMarker hChildMarker
                hChildLabel).1.elim
          · rcases hRight with ⟨childMarker, hChildMarker, rfl⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              simpa [childPendingEdge] using hMarkerLabel
            intro hSource
            have hOutgoing := (buildSequenceAutomaton_outgoing_right signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right) childMarker.target
                edge).mp ⟨hEdge, by
                  simpa [childPendingEdge, childState] using hSource⟩
            rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
            exact ih right hRightFuel hTailFields.2 childMarker hChildMarker
              hChildLabel childEdge hChildEdge hChildSource
          · rcases hBridge with ⟨state, _, environment, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)
          · rcases hFutureBridge with ⟨state, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)
      | par left right interface =>
          have hFalse : PactType.TailOccurrences name False
              (.par left right interface) := by
            simpa [PactType.TailOccurrences] using hTail
          exact (compileTypeFuel_variableEdge_source_var signature name
            (fuel + 1) (.par left right interface) False hFuel hFalse marker
              hMarker hMarkerLabel).1.elim
      | xoffer elseType branches =>
          have hTailFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name True branches := by
            simpa [PactType.TailOccurrences] using hTail
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hMarker
          rcases hMarker with
            ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElse
            rcases hElse with ⟨childMarker, hChildMarker, rfl⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              simpa [childPendingEdge] using hMarkerLabel
            intro hSource
            have hOutgoing :=
              (buildExclusiveOfferAutomaton_outgoing_else signature branches
                (compileTypeFuel signature fuel elseType) branchAutomata
                  childMarker.target edge).mp ⟨by simpa [branchAutomata] using hEdge,
                    by simpa [childPendingEdge, childState] using hSource⟩
            rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
            exact ih elseType hElseFuel hTailFields.1 childMarker hChildMarker
              hChildLabel childEdge hChildEdge hChildSource
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childMarker, hChildMarker, rfl⟩
              obtain ⟨action, branchType, hSyntaxEntry, hCompiled⟩ :=
                compiledBranch_zipIdx_cases signature fuel branches indexed
                  hIndexedMem
              have hMember : (action, branchType) ∈ branches := by
                rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
                  ⟨hBound, hValue⟩
                simpa [hValue] using List.getElem_mem hBound
              have hBranchFuel : TypeCompilationFuelSufficient branchType
                  fuel := (typeCompilationFuel_le_typeBranchCompilationFuel
                    branches (action, branchType) hMember).trans (by
                      simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                        at hFuel ⊢
                      omega)
              have hBranchTail : branchType.TailOccurrences name True :=
                tailOccurrences_branch_of_mem name True branches hTailFields.2
                  (action, branchType) hMember
              rw [hCompiled] at hChildMarker
              have hChildLabel : childMarker.label =
                  AutomatonConstructionLabel.variable name := by
                simpa [childPendingEdge] using hMarkerLabel
              have hAutomatonEntry : branchAutomata[indexed.2]? =
                  some (action, compileTypeFuel signature fuel branchType) := by
                simp [branchAutomata, List.getElem?_map, hSyntaxEntry]
              intro hSource
              have hOutgoing :=
                (buildExclusiveOfferAutomaton_outgoing_branch signature
                  branches (compileTypeFuel signature fuel elseType)
                    branchAutomata indexed.2
                      (action, compileTypeFuel signature fuel branchType)
                        hAutomatonEntry childMarker.target edge).mp
                  ⟨by simpa [branchAutomata] using hEdge,
                    by simpa [hCompiled, childPendingEdge, childState]
                      using hSource⟩
              rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
              exact ih branchType hBranchFuel hBranchTail childMarker
                hChildMarker hChildLabel childEdge hChildEdge hChildSource
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hMarkerLabel
              exact absurd hMarkerLabel (by simp)

          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)
      | offer elseType branches =>
          have hTailFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa [PactType.TailOccurrences] using hTail
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          let conjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          simp only [compileTypeFuel,
            buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hMarker
          rcases hMarker with
            ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElse
            rcases hElse with ⟨childMarker, hChildMarker, rfl⟩
            have hChildLabel : childMarker.label =
                AutomatonConstructionLabel.variable name := by
              simpa [childPendingEdge] using hMarkerLabel
            intro hSource
            have hOutgoing :=
              (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature
                branches (compileTypeFuel signature fuel elseType)
                  conjunctions childMarker.target edge).mp
                ⟨by simpa [conjunctions] using hEdge,
                  by simpa [childPendingEdge, childState] using hSource⟩
            rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, _⟩
            exact ih elseType hElseFuel hTailFields.1 childMarker hChildMarker
              hChildLabel childEdge hChildEdge hChildSource
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨childMarker, hChildMarker, hEq⟩
              obtain ⟨selected, hSyntaxEntry, hCompiled⟩ :=
                selectedConjunction_zipIdx_cases signature fuel branches
                  indexed hIndexedMem
              have hSelectedTail : (parallelTypeBranchesSelecting selected
                  branches).TailOccurrences name False :=
                tailOccurrences_parallelTypeBranchesSelecting name selected
                  branches hTailFields.2
              have hSelectedFuel : TypeCompilationFuelSufficient
                  (parallelTypeBranchesSelecting selected branches) fuel := by
                simp [TypeCompilationFuelSufficient,
                  typeCompilationFuel_parallelTypeBranchesSelecting]
                simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                  at hFuel
                omega
              rw [hCompiled] at hChildMarker
              have hChildLabel : childMarker.label =
                  AutomatonConstructionLabel.variable name := by
                rw [← hEq] at hMarkerLabel
                simpa [childPendingEdge] using hMarkerLabel
              exact (compileTypeFuel_variableEdge_source_var signature name
                fuel (parallelTypeBranchesSelecting selected branches) False
                  hSelectedFuel hSelectedTail childMarker hChildMarker
                    hChildLabel).1.elim
          · rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨environment, _, hEq⟩
              rw [← hEq] at hMarkerLabel
              exact absurd hMarkerLabel (by simp)
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨environment, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨environment, _, hEq⟩
            rw [← hEq] at hMarkerLabel
            exact absurd hMarkerLabel (by simp)

private theorem markerStopped_sequenceExecution_markerReachable_iff
    (signature : TypeAlphabet) (stoppedName query : String)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences stoppedName True)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature fuel processType).states) :
    MarkerReachable
        (markerStoppedFragment
          (sequenceExecutionFragment
            (compileTypeFuel signature fuel processType)) stoppedName)
        query state ↔
      MarkerReachable
        (sequenceExecutionFragment
          (compileTypeFuel signature fuel processType)) query state := by
  let raw := compileTypeFuel signature fuel processType
  let executionFragment := sequenceExecutionFragment raw
  have hTargets : raw.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel processType hFuel
  have hClosed : executionFragment.toPending.ReferencesClosed := by
    exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
      executionFragment
        (sequenceExecutionFragment_futureTargetsInStates raw hTargets)
  have hExecutionState : state ∈ executionFragment.states := by
    exact Finset.mem_union_left _ hState
  apply markerStoppedFragment_markerReachable_of_target_sinks
    executionFragment stoppedName query hClosed
  · intro marker hMarker hMarkerLabel target removed hFuture
    simp only [executionFragment, sequenceExecutionFragment,
      sequenceExecutionAutomaton, Finset.mem_image] at hMarker
    rcases hMarker with ⟨rawMarker, hRawMarker, rfl⟩
    have hRawLabel : rawMarker.label =
        AutomatonConstructionLabel.variable stoppedName := by
      simpa using hMarkerLabel
    have hFields : rawMarker.target = target ∧
        rawMarker.current = removed := by
      simpa [hRawLabel] using hFuture
    exact hFields.1.symm
  · intro marker hMarker hMarkerLabel edge hEdge hSource
    simp only [executionFragment, sequenceExecutionFragment,
      sequenceExecutionAutomaton, Finset.mem_image] at hMarker hEdge
    rcases hMarker with ⟨rawMarker, hRawMarker, rfl⟩
    rcases hEdge with ⟨rawEdge, hRawEdge, rfl⟩
    have hRawLabel : rawMarker.label =
        AutomatonConstructionLabel.variable stoppedName := by
      simpa using hMarkerLabel
    exact compileTypeFuel_variableEdge_target_sink signature stoppedName fuel
      processType hFuel hTail rawMarker hRawMarker hRawLabel rawEdge hRawEdge
        (by simpa using hSource)
  · exact hExecutionState

/-- Stopping the temporary execution reference of a compiled free-variable
marker preserves the execution menu: that reference points to a sink target
and the marker itself carries no current offers. -/
theorem markerStopped_sequenceExecution_computeFuture
    (signature : TypeAlphabet) (stoppedName : String)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences stoppedName True)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature fuel processType).states) :
    computeFuture
        (markerStoppedFragment
          (sequenceExecutionFragment
            (compileTypeFuel signature fuel processType)) stoppedName).toPending
        state =
      computeFuture
        (sequenceExecutionAutomaton
          (compileTypeFuel signature fuel processType)) state := by
  let raw := compileTypeFuel signature fuel processType
  let executionFragment := sequenceExecutionFragment raw
  have hTargets : raw.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel processType hFuel
  have hClosed : executionFragment.toPending.ReferencesClosed := by
    exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
      executionFragment
        (sequenceExecutionFragment_futureTargetsInStates raw hTargets)
  have hExecutionState : state ∈ executionFragment.states :=
    Finset.mem_union_left _ hState
  apply markerStoppedFragment_computeFuture_of_target_sinks executionFragment
    stoppedName hClosed
  · intro marker hMarker hMarkerLabel
    simp only [executionFragment, sequenceExecutionFragment,
      sequenceExecutionAutomaton, Finset.mem_image] at hMarker
    rcases hMarker with ⟨rawMarker, hRawMarker, rfl⟩
    have hRawLabel : rawMarker.label =
        AutomatonConstructionLabel.variable stoppedName := by
      simpa using hMarkerLabel
    have hRawFields := compileTypeFuel_markerEdgesInert signature stoppedName
      fuel processType True hFuel hTail rawMarker hRawMarker hRawLabel
    simp [hRawLabel, hRawFields.1]
  · intro marker hMarker hMarkerLabel edge hEdge hSource
    simp only [executionFragment, sequenceExecutionFragment,
      sequenceExecutionAutomaton, Finset.mem_image] at hMarker hEdge
    rcases hMarker with ⟨rawMarker, hRawMarker, rfl⟩
    rcases hEdge with ⟨rawEdge, hRawEdge, rfl⟩
    have hRawLabel : rawMarker.label =
        AutomatonConstructionLabel.variable stoppedName := by
      simpa using hMarkerLabel
    exact compileTypeFuel_variableEdge_target_sink signature stoppedName fuel
      processType hFuel hTail rawMarker hRawMarker hRawLabel rawEdge hRawEdge
        (by simpa using hSource)
  · exact hExecutionState

/-- **Marker reachability is computed by the syntax.**

Under tail occurrence the compiled graph still reaches a `.variable name`
marker in the same cycle exactly when `PactType.markerReachableSubst` says so.
This is the graph half of the recursion future bridge; the syntax half is
`PactType.futureOffersSubst_eq_union_marker`.

The ambient `bound` list carries every enclosing binder whose variable may
still be free, exactly as `AllVariablesBound` does.  It is needed by the
sequence case, which must hand its *left* component a closed proof bundle;
closedness is recovered there from the fact that no ambient name occurs in a
sequence's left component. -/
theorem compilationMarkerReachable_iff (signature : TypeAlphabet) :
    ∀ (bound : List String) (name : String) (processType : PactType),
      name ∈ bound →
      PactType.AllTailOccurrences bound True processType →
      signature.WellFormed →
      signature.Supports processType →
      PactType.AllVariablesBound bound processType →
      PactType.BinderHygienic bound processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.SameCycleMessageLinear processType →
      PactType.InterfaceScoped processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → PactType.AllVariablesBound [] child →
        PactType.BinderHygienic [] child → PactType.ClockGuarded child →
        PactType.TailRecursive child →
        PactType.SameCycleMessageLinear child →
        PactType.InterfaceScoped child →
          CompilationProofBundle signature child) →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          (MarkerReachable (compileTypeFuel signature
              (typeCompilationFuel processType) processType) name state ↔
            PactType.markerReachableSubst name residual = true) := by
  classical
  intro bound name processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing bound name processType with
  | _ n ih =>
      intro hName hAllTail hSignature hSupports hBound hHygienic hGuarded
        hTail hLinear hScoped hClosedBundle state residual hRelated
      have hTailName : processType.TailOccurrences name True := hAllTail name hName
      cases processType with
      | message msg dir =>
          have hNo := not_markerReachable_of_tailOccurrences_false signature
            name (typeCompilationFuel (PactType.message msg dir))
            (.message msg dir) (typeCompilationFuel_sufficient _)
            (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | progress pid =>
          have hNo := not_markerReachable_of_tailOccurrences_false signature
            name (typeCompilationFuel (PactType.progress pid)) (.progress pid)
            (typeCompilationFuel_sufficient _)
            (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | tock =>
          have hNo := not_markerReachable_of_tailOccurrences_false signature
            name (typeCompilationFuel PactType.tock) .tock
            (typeCompilationFuel_sufficient _)
            (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | skip =>
          have hNo := not_markerReachable_of_tailOccurrences_false signature
            name (typeCompilationFuel PactType.skip) .skip
            (typeCompilationFuel_sufficient _)
            (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | par left right interface =>
          have hFalse : PactType.TailOccurrences name False
              (.par left right interface) := by
            simp only [PactType.TailOccurrences] at hTailName ⊢
            exact hTailName
          have hNo := not_markerReachable_of_tailOccurrences_false signature
            name (typeCompilationFuel (PactType.par left right interface))
            (.par left right interface) (typeCompilationFuel_sufficient _)
            hFalse state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated
            simp [PactType.markerReachableSubst] at hValue
      | var current =>
          cases hRelated with
          | «variable» _ =>
              constructor
              · rintro ⟨reached, _, edge, hEdge, _, hLabel⟩
                have hShape : edge.label =
                    AutomatonConstructionLabel.variable current := by
                  simp only [typeCompilationFuel, compileTypeFuel,
                    finishAutomatonFragment, Finset.mem_image] at hEdge
                  rcases hEdge with ⟨environment, _, rfl⟩
                  rfl
                rw [hShape] at hLabel
                have hEq : current = name := by simpa using hLabel
                simp [PactType.markerReachableSubst, hEq]
              · intro hValue
                have hEq : name = current := by
                  by_cases hCase : name = current
                  · exact hCase
                  · simp [PactType.markerReachableSubst, hCase] at hValue
                refine ⟨.root,
                  PendingAutomaton.mem_futureReachable_self _ _, ?_⟩
                refine ⟨{ source := .root
                          environment := TypeEnvironment.tock
                          label := .variable current
                          current := ∅
                          future := .explicit ∅
                          target := .final }, ?_, rfl, by simp [hEq]⟩
                simp only [typeCompilationFuel, compileTypeFuel,
                  finishAutomatonFragment, Finset.mem_image]
                exact ⟨TypeEnvironment.tock,
                  by simp [TypeAlphabet.localEnvironments], rfl⟩
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hBodyLt : sizeOf body < sizeOf (PactType.recur other body) := by
            simp_wf
            omega
          have hSupportBody : signature.Supports body := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundBody : PactType.AllVariablesBound (other :: bound) body := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : other ∉ bound ∧
              PactType.BinderHygienic (other :: bound) body := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : body.GuardedOccurrences other False ∧
              body.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : body.TailOccurrences other True ∧
              body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : body.SameCycleMessageLinear ∧
              Disjoint (PactType.SuffixMessageIds body)
                (PactType.PrefixMessageIds body) := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedBody : body.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hDistinct : name ≠ other := by
            intro hEq
            subst other
            exact hHygienicFields.1 hName
          have hOtherName : ¬ other = name := fun h => hDistinct h.symm
          have hTailOuter : body.TailOccurrences name True := by
            simpa only [PactType.TailOccurrences, if_neg hOtherName]
              using hTailName
          have hAllTailBody : PactType.AllTailOccurrences (other :: bound) True
              body := by
            intro m hm
            rcases List.mem_cons.mp hm with rfl | hRest
            · exact hTailFields.1
            · have hNe : ¬ other = m := by
                intro hEq
                exact hHygienicFields.1 (hEq ▸ hRest)
              have hEntry := hAllTail m hRest
              simpa only [PactType.TailOccurrences, if_neg hNe] using hEntry
          have hBodyCallback : ∀ child : PactType, sizeOf child < sizeOf body →
              signature.Supports child → PactType.AllVariablesBound [] child →
              PactType.BinderHygienic [] child → PactType.ClockGuarded child →
              PactType.TailRecursive child →
              PactType.SameCycleMessageLinear child →
              PactType.InterfaceScoped child →
                CompilationProofBundle signature child :=
            fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hBodySize)
          have hBodyIH : ∀ m, m ∈ (other :: bound) → ∀ q r,
              TypeCompilationRelation body q r →
                (MarkerReachable (compileTypeFuel signature
                    (typeCompilationFuel body) body) m q ↔
                  PactType.markerReachableSubst m r = true) := by
            intro m hm q r hr
            exact ih (sizeOf body) hBodySize (other :: bound) m body rfl hm
              hAllTailBody hSignature hSupportBody hBoundBody
              hHygienicFields.2 hGuardedFields.2 hTailFields.2
              hLinearFields.1 hScopedBody hBodyCallback q r hr
          set bodyFragment := compileTypeFuel signature
            (typeCompilationFuel body) body with hBodyFragment
          have hBodyFuel : TypeCompilationFuelSufficient body
              (typeCompilationFuel body) := typeCompilationFuel_sufficient body
          have hBodyTargets : bodyFragment.FutureTargetsInStates :=
            compileTypeFuel_futureTargetsInStates signature
              (typeCompilationFuel body) body hBodyFuel
          have hBodyInitial : bodyFragment.initial ∈ bodyFragment.states :=
            compileTypeFuel_initial_mem signature (typeCompilationFuel body)
              body hBodyFuel
          have hBodyClosed : (⟨bodyFragment.states,
              bodyFragment.edges⟩ : PendingAutomaton).ReferencesClosed :=
            PendingAutomaton.referencesClosed_of_futureTargetsInStates
              bodyFragment hBodyTargets
          have hMarkers : MarkerEdgesInert bodyFragment other :=
            compileTypeFuel_markerEdgesInert signature other
              (typeCompilationFuel body) body True hBodyFuel hTailFields.1
          have hParentClosed : (⟨(buildRecursionAutomaton signature other
                bodyFragment).states,
              (buildRecursionAutomaton signature other bodyFragment).edges⟩ :
                  PendingAutomaton).ReferencesClosed := by
            apply PendingAutomaton.referencesClosed_of_futureTargetsInStates
            exact buildRecursionAutomaton_futureTargetsInStates signature other
              bodyFragment hBodyTargets hBodyInitial
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.recur other body))
                (.recur other body) =
              buildRecursionAutomaton signature other bodyFragment := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              hBodyFragment]
          have hEntryIff : MarkerReachable
              (buildRecursionAutomaton signature other bodyFragment) name
                (childState 0 bodyFragment.initial) ↔
              PactType.markerReachableSubst name body = true := by
            rw [buildRecursionAutomaton_markerReachable_child_at_initial
              signature other name bodyFragment hDistinct hMarkers hBodyClosed
                hParentClosed hBodyInitial]
            exact hBodyIH name (List.mem_cons_of_mem other hName)
              bodyFragment.initial body
              (compileTypeFuel_initial_relation signature
                (typeCompilationFuel body) body hBodyFuel)
          rw [hFragment]
          cases hRelated with
          | recur_source =>
              rw [buildRecursionAutomaton_markerReachable_root signature other
                name bodyFragment hParentClosed, hEntryIff]
              simp [PactType.markerReachableSubst, hDistinct]
          | recur_body _ _ childResidual childQ hChild =>
              have hChildState : childQ ∈ bodyFragment.states := by
                have hCanonical := compilationStateCorrect_of_compilation
                  signature body childQ childResidual hChild
                simpa [hBodyFragment] using hCanonical
              have hChildTailOther : childResidual.TailOccurrences other True :=
                compilationRelation_tailOccurrences_true other hChild
                  hTailFields.2 hTailFields.1
              have hChildFresh : childResidual.BinderFreshFor [name] := by
                apply PactType.binderFreshFor_mono
                  (smaller := [name]) (larger := other :: bound)
                · intro m hm
                  rcases List.mem_singleton.mp hm with rfl
                  exact List.mem_cons_of_mem other hName
                · exact compilationRelation_binderFreshFor hChild
                    hHygienicFields.2
              show MarkerReachable
                  (buildRecursionAutomaton signature other bodyFragment) name
                    (childState 0 childQ) ↔ _
              rw [buildRecursionAutomaton_markerReachable_child signature other
                name bodyFragment hDistinct hMarkers hBodyClosed hParentClosed
                  hBodyInitial childQ hChildState, hEntryIff,
                hBodyIH name (List.mem_cons_of_mem other hName) childQ
                  childResidual hChild,
                hBodyIH other List.mem_cons_self childQ childResidual hChild,
                PactType.markerReachableSubst_replaceVar name other
                  (.recur other body) hDistinct childResidual hChildTailOther
                    hChildFresh]
              rw [show PactType.markerReachableSubst name
                  (PactType.recur other body) =
                  PactType.markerReachableSubst name body by
                simp [PactType.markerReachableSubst, hDistinct]]
              cases PactType.markerReachableSubst name childResidual <;>
                cases PactType.markerReachableSubst other childResidual <;>
                cases PactType.markerReachableSubst name body <;> simp
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftLt : sizeOf left < sizeOf (PactType.choice left right) := by
            simp_wf; omega
          have hRightLt : sizeOf right <
              sizeOf (PactType.choice left right) := by simp_wf; omega
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : left.SameCycleMessageLinear ∧
              right.SameCycleMessageLinear := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hLeftIH := ih (sizeOf left) hLeftSize bound name left rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hLeftSize))
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified := buildChoiceAutomaton_markerReachable_classified
            signature left right TypeLabel.silent TypeLabel.silent name
            (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent])
            hLeftIH hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.choice left right))
                (.choice left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right)
                TypeLabel.silent TypeLabel.silent := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | choice_source =>
              rw [hClassified.1, PactType.markerReachableSubst]
              simp [Bool.or_eq_true]
          | choice_left _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | choice_right _ _ _ _ hChild => exact hClassified.2.2 _ _ hChild
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftLt : sizeOf left <
              sizeOf (PactType.fairChoice bid left right) := by simp_wf; omega
          have hRightLt : sizeOf right <
              sizeOf (PactType.fairChoice bid left right) := by simp_wf; omega
          have hSupportFields := hSupports
          simp only [TypeAlphabet.Supports] at hSupportFields
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : left.SameCycleMessageLinear ∧
              right.SameCycleMessageLinear := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hLeftIH := ih (sizeOf left) hLeftSize bound name left rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.2.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hLeftSize))
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified := buildChoiceAutomaton_markerReachable_classified
            signature left right (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) name
            (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
            hLeftIH hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.fairChoice bid left right))
                (.fairChoice bid left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | fair_source =>
              rw [hClassified.1, PactType.markerReachableSubst]
              simp [Bool.or_eq_true]
          | fair_left _ _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | fair_right _ _ _ _ _ hChild => exact hClassified.2.2 _ _ hChild
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftLt : sizeOf left < sizeOf (PactType.seq left right) := by
            simp_wf; omega
          have hRightLt : sizeOf right < sizeOf (PactType.seq left right) := by
            simp_wf; omega
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields := hLinear
          simp only [PactType.SameCycleMessageLinear] at hLinearFields
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hAllTailLeftFalse : PactType.AllTailOccurrences bound False
              left := by
            intro m hm
            have hEntry := hAllTail m hm
            simp only [PactType.TailOccurrences] at hEntry
            exact hEntry.1
          have hLeftClosedType : PactType.AllVariablesBound [] left := by
            apply PactType.allVariablesBound_drop_of_allTailOccurrences_false
              bound [] left hAllTailLeftFalse
            simpa using hBoundFields.1
          have hLeftHygienicEmpty : PactType.BinderHygienic [] left :=
            PactType.binderHygienic_mono (by intro m hm; simp at hm) left
              hHygienicFields.1
          have hLeftBundle := hClosedBundle left hLeftSize hSupportFields.1
            hLeftClosedType hLeftHygienicEmpty hGuardedFields.1 hTailFields.1
            hLinearFields.1 hScopedFields.1
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2.1 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified := buildSequenceAutomaton_markerReachable_classified
            signature left right name (hAllTailLeftFalse name hName)
            hLeftBundle.execution hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.seq left right))
                (.seq left right) =
              buildSequenceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | sequence_left _ _ _ _ hChild => exact hClassified.1 _ _ hChild
          | sequence_right _ _ _ _ hChild => exact hClassified.2 _ _ hChild
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hElseLt : sizeOf elseType <
              sizeOf (PactType.xoffer elseType branches) := by simp_wf; omega
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound elseType ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : elseType.SameCycleMessageLinear ∧
              PactType.SameCycleMessageLinearBranches branches := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : elseType.InterfaceScoped ∧
              PactType.InterfaceScopedBranches branches := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hElseIH := ih (sizeOf elseType) hElseSize bound name elseType
            rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hElseSize))
          have hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
              (index : Nat), branches[index]? = some (action, branchType) →
              ∀ q r, TypeCompilationRelation branchType q r →
                (MarkerReachable (compileTypeFuel signature
                  (typeCompilationFuel branchType) branchType) name q ↔
                    PactType.markerReachableSubst name r = true) := by
            intro action branchType index hEntry q r hr
            have hMember : (action, branchType) ∈ branches := by
              rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBoundIndex,
                hValue⟩
              have hAt := List.getElem_mem hBoundIndex
              simpa [hValue] using hAt
            have hBranchLt : sizeOf branchType <
                sizeOf (PactType.xoffer elseType branches) :=
              (branch_sizeOf_lt elseType branches (action, branchType)
                hMember).1
            have hBranchSize : sizeOf branchType < n := by
              rw [← hSize]
              exact hBranchLt
            exact ih (sizeOf branchType) hBranchSize bound name branchType rfl
              hName
              (by
                intro m hm
                have hEntryTail := hAllTail m hm
                simp only [PactType.TailOccurrences] at hEntryTail
                exact tailOccurrences_branch_of_mem m True branches
                  hEntryTail.2 (action, branchType) hMember)
              hSignature
              (supports_branch_of_mem signature branches (action, branchType)
                hSupportFields.2 hMember)
              (allVariablesBound_branch_of_mem bound branches
                (action, branchType) hBoundFields.2 hMember)
              (binderHygienic_branch_of_mem bound branches
                (action, branchType) hHygienicFields.2 hMember)
              (clockGuarded_branch_of_mem branches (action, branchType)
                hGuardedFields.2 hMember)
              (tailRecursive_branch_of_mem branches (action, branchType)
                hTailFields.2 hMember)
              (sameCycleMessageLinear_branch_of_mem branches
                (action, branchType) hLinearFields.2 hMember)
              (interfaceScoped_branch_of_mem branches (action, branchType)
                hScopedFields.2 hMember)
              (fun child hChildSize => hClosedBundle child
                (lt_trans hChildSize hBranchSize)) q r hr
          have hClassified :=
            buildExclusiveOfferAutomaton_markerReachable_classified signature
              elseType branches name hSupports hElseIH hBranchIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.xoffer elseType branches))
                (.xoffer elseType branches) =
              buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature
                  (max (typeCompilationFuel elseType)
                    (typeBranchCompilationFuel branches)) elseType)
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature
                    (max (typeCompilationFuel elseType)
                      (typeBranchCompilationFuel branches)) branch.2)) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | xoffer_source => exact hClassified.1
          | xoffer_else _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | xoffer_branch _ branchType _ _ action index _ hEntry hChild =>
              exact hClassified.2.2 action branchType index hEntry _ _ hChild
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hElseLt : sizeOf elseType <
              sizeOf (PactType.offer elseType branches) := by simp_wf; omega
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound elseType ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : elseType.SameCycleMessageLinear ∧
              PactType.SameCycleMessageLinearBranches branches := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : elseType.InterfaceScoped ∧
              PactType.InterfaceScopedBranches branches := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hTailNameFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTailName
          have hElseIH := ih (sizeOf elseType) hElseSize bound name elseType
            rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hElseSize))
          have hClassified :=
            buildSelectedConjunctiveOfferAutomaton_markerReachable_classified
              signature elseType branches name hSupports hTailNameFields.2
                hElseIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (PactType.offer elseType branches))
                (.offer elseType branches) =
              buildSelectedConjunctiveOfferAutomaton signature branches
                (compileTypeFuel signature
                  (max (typeCompilationFuel elseType)
                    (conjunctiveCompilationFuel branches)) elseType)
                (branches.map fun selected =>
                  (selected.1, compileTypeFuel signature
                    (max (typeCompilationFuel elseType)
                      (conjunctiveCompilationFuel branches))
                      (parallelTypeBranchesSelecting selected branches))) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | offer_source => exact hClassified.1
          | offer_else _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | offer_branches _ _ _ selected index _ hEntry hChild =>
              exact hClassified.2.2 selected index hEntry _ _ hChild

end

noncomputable section

/-! ### Marker reachability in the sequence-execution view -/

/-- If a constructor root reaches exactly a finite collection of entries in
both graph views, marker reachability agrees at the root as soon as it agrees
at every entry. -/
private theorem sequenceExecution_markerReachable_iff_raw_of_entries
    (fragment : AutomatonFragment) (name : String)
    (entries : Finset TypeAutomatonState)
    (hTargets : fragment.FutureTargetsInStates)
    (hRoot : (.root : TypeAutomatonState) ∈ fragment.states)
    (hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed)
    (hRawClosed : fragment.toPending.ReferencesClosed)
    (hUpper : fragment.toPending.referencedStates .root ⊆
      insert .root entries)
    (hEntries : entries ⊆ fragment.toPending.referencedStates .root)
    (hEntry : ∀ entry ∈ entries,
      MarkerReachable (sequenceExecutionFragment fragment) name entry ↔
        MarkerReachable fragment name entry) :
    MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
      MarkerReachable fragment name .root := by
  classical
  rw [sequenceExecution_markerReachable_root_of_entries fragment name entries
      hTargets hRoot hShape hUpper hEntries,
    markerReachable_root_of_entries fragment name .root entries hRawClosed
      hRoot hUpper hEntries,
    sequenceExecutionFragment_markerSource]
  constructor
  · rintro (hSource | ⟨entry, hMem, hReach⟩)
    · exact Or.inl hSource
    · exact Or.inr ⟨entry, hMem, (hEntry entry hMem).mp hReach⟩
  · rintro (hSource | ⟨entry, hMem, hReach⟩)
    · exact Or.inl hSource
    · exact Or.inr ⟨entry, hMem, (hEntry entry hMem).mpr hReach⟩

/-- Execution-view marker correspondence for the binary choice constructor.
The proof uses the same child embeddings as the execution-menu proof. -/
private theorem buildChoiceAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftIH : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel left) left)) name q ↔
          PactType.markerReachableSubst name r = true))
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel right) right)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildChoiceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
      selectionLeft selectionRight
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        (PactType.markerReachableSubst name left = true ∨
          PactType.markerReachableSubst name right = true)) ∧
      (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hFuelDef
  set leftFragment := compileTypeFuel signature fuel left with hLeftDef
  set rightFragment := compileTypeFuel signature fuel right with hRightDef
  set fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight with hFragmentDef
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftStates : childStates 0 leftFragment ⊆ fragment.states := by
    intro child hChild
    simp [hFragmentDef, buildChoiceAutomaton, finishAutomatonFragment,
      hChild]
  have hRightStates : childStates 1 rightFragment ⊆ fragment.states := by
    intro child hChild
    simp [hFragmentDef, buildChoiceAutomaton, finishAutomatonFragment,
      hChild]
  have hLeftTagged : ∀ q r, TypeCompilationRelation left q r →
      (MarkerReachable (sequenceExecutionFragment fragment) name
          (.child 0 q) ↔ PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ leftFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature left
        q r hr
      simpa [hLeftStable] using hCanonical
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      sequenceExecution_taggedChild_markerReachable fragment leftFragment 0
        name (fun state edge => buildChoiceAutomaton_outgoing_left signature
          leftFragment rightFragment selectionLeft selectionRight state edge)
        hLeftStates hLeftTargets q hState,
      hLeftStable]
    exact hLeftIH q r hr
  have hRightTagged : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (sequenceExecutionFragment fragment) name
          (.child 1 q) ↔ PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ rightFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature right
        q r hr
      simpa [hRightStable] using hCanonical
    rw [show (TypeAutomatonState.child 1 q) = childState 1 q from rfl,
      sequenceExecution_taggedChild_markerReachable fragment rightFragment 1
        name (fun state edge => buildChoiceAutomaton_outgoing_right signature
          leftFragment rightFragment selectionLeft selectionRight state edge)
        hRightStates hRightTargets q hState,
      hRightStable]
    exact hRightIH q r hr
  refine ⟨?_, hLeftTagged, hRightTagged⟩
  rw [sequenceExecution_buildChoice_markerReachable_root signature
      leftFragment rightFragment selectionLeft selectionRight name
      hSelectionLeft hSelectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial,
    hLeftStable,
    hLeftIH (compileTypeFuel signature (typeCompilationFuel left) left).initial
      left (by
      exact compileTypeFuel_initial_relation signature
        (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)),
    hRightStable,
    hRightIH (compileTypeFuel signature (typeCompilationFuel right) right).initial
      right (by
      exact compileTypeFuel_initial_relation signature
        (typeCompilationFuel right) right
          (typeCompilationFuel_sufficient right))]

/-- Execution-view marker correspondence for sequence.  The execution edge
set of the parent is exactly a sequence constructor whose right child is
already in execution view; this leaves the existing bridge classifier
applicable without approximating its completion condition. -/
private theorem buildSequenceAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (left right : PactType) (name : String)
    (hLeftAbsent : left.TailOccurrences name False)
    (hLeftExecution : CompilationSequenceExecutionCorrect signature left)
    (hRightIH : ∀ q r, TypeCompilationRelation right q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel right) right)) name q ↔
          PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let fragment := buildSequenceAutomaton signature
      (compileTypeFuel signature fuel left)
      (compileTypeFuel signature fuel right)
    (∀ q r, TypeCompilationRelation left q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name (.seq r right) = true)) ∧
      (∀ q r, TypeCompilationRelation right q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 1 q) ↔
          PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hFuelDef
  set leftFragment := compileTypeFuel signature fuel left with hLeftDef
  set rightFragment := compileTypeFuel signature fuel right with hRightDef
  set fragment := buildSequenceAutomaton signature leftFragment rightFragment
    with hFragmentDef
  set rightExecution := sequenceExecutionFragment rightFragment
    with hRightExecutionDef
  set shadow := buildSequenceAutomaton signature leftFragment rightExecution
    with hShadowDef
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRightExecutionTargets : rightExecution.FutureTargetsInStates := by
    simpa [rightExecution] using
      sequenceExecutionFragment_futureTargetsInStates rightFragment
        hRightTargets
  have hRightExecutionInitial : rightExecution.initial ∈
      rightExecution.states := by
    exact Finset.mem_union_left _ hRightInitial
  have hFragmentTargets : fragment.FutureTargetsInStates := by
    simpa [fragment] using buildSequenceAutomaton_futureTargetsInStates
      signature leftFragment rightFragment hLeftTargets hRightTargets
        hRightInitial
  have hShadowTargets : shadow.FutureTargetsInStates := by
    simpa [shadow] using buildSequenceAutomaton_futureTargetsInStates signature
      leftFragment rightExecution hLeftTargets hRightExecutionTargets
        hRightExecutionInitial
  have hExecutionClosed :
      (sequenceExecutionFragment fragment).toPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates _
      (sequenceExecutionFragment_futureTargetsInStates fragment
        hFragmentTargets)
  have hShadowClosed : shadow.toPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates shadow
      hShadowTargets
  have hEdges : (sequenceExecutionFragment fragment).edges = shadow.edges := by
    simpa [fragment, shadow, sequenceExecutionFragment] using
      sequenceExecution_buildSequence_edges signature leftFragment
        rightFragment
  have hLeftNoMarkers : ∀ edge ∈ leftFragment.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name := by
    intro edge hEdge hLabel
    exact (compileTypeFuel_variableEdge_source_var signature name fuel left
      False hLeftFuel hLeftAbsent edge hEdge hLabel).1
  have hRightClosed : rightExecution.toPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates rightExecution
      hRightExecutionTargets
  have hRightCard : rightExecution.states.card ≤ shadow.states.card :=
    card_le_of_childStates_subset rightExecution shadow 1 (by
      intro child hChild
      simp [shadow, buildSequenceAutomaton, finishAutomatonFragment, hChild])
  have hRightTaggedShadow : ∀ q r,
      TypeCompilationRelation right q r →
        (MarkerReachable shadow name (.child 1 q) ↔
          PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ rightFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature right
        q r hr
      simpa [hRightStable] using hCanonical
    have hExecutionState : q ∈ rightExecution.states :=
      Finset.mem_union_left _ hState
    rw [show (TypeAutomatonState.child 1 q) = childState 1 q from rfl,
      markerReachable_of_outgoing_childPendingEdge shadow rightExecution 1 name
        (fun current edge => buildSequenceAutomaton_outgoing_right signature
          leftFragment rightExecution current edge)
        hRightClosed hRightCard q hExecutionState,
      hRightExecutionDef, hRightStable]
    exact hRightIH q r hr
  have hRightEntry : MarkerReachable rightExecution name
      rightExecution.initial ↔
        PactType.markerReachableSubst name right = true := by
    rw [hRightExecutionDef, hRightStable]
    exact hRightIH _ right (compileTypeFuel_initial_relation signature
      (typeCompilationFuel right) right (typeCompilationFuel_sufficient right))
  constructor
  · intro q r hr
    have hState : q ∈ leftFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature left
        q r hr
      simpa [hLeftStable] using hCanonical
    have hExecutionState : childState 0 q ∈
        (sequenceExecutionFragment fragment).states := by
      apply Finset.mem_union_left
      simp only [fragment, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childStates, Finset.mem_image]
      exact Or.inl (Or.inl ⟨q, hState, rfl⟩)
    have hShadowState : childState 0 q ∈ shadow.states := by
      simp only [shadow, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childStates, Finset.mem_image]
      exact Or.inl (Or.inl ⟨q, hState, rfl⟩)
    have hBridge : (∃ completed ∈
          (sequenceExecutionAutomaton leftFragment).futureReachable q,
        completed ∈ leftFragment.accepting ∨
          completed ∈ leftFragment.completing) ↔
        r.CanCompleteBeforeTock = true := by
      have hCanonical := hLeftExecution q r hr
      simpa [CompilationSequenceExecutionCorrect, hLeftStable] using
        hCanonical.2
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      markerReachable_iff_of_same_edges
        (sequenceExecutionFragment fragment) shadow name hEdges
          hExecutionClosed hShadowClosed (childState 0 q) hExecutionState
            hShadowState]
    rw [hShadowDef]
    change MarkerReachable
        (buildSequenceAutomaton signature leftFragment rightExecution) name
          (.child 0 q) ↔ _
    rw [buildSequenceAutomaton_markerReachable_left signature leftFragment
        rightExecution name hLeftNoMarkers q hState hLeftTargets
          hRightExecutionTargets hRightExecutionInitial,
      hBridge, hRightEntry, PactType.markerReachableSubst]
    simp [Bool.and_eq_true]
  · intro q r hr
    have hState : q ∈ rightFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature right
        q r hr
      simpa [hRightStable] using hCanonical
    have hExecutionState : childState 1 q ∈
        (sequenceExecutionFragment fragment).states := by
      apply Finset.mem_union_left
      simp only [fragment, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childStates, Finset.mem_image]
      exact Or.inr ⟨q, hState, rfl⟩
    have hShadowState : childState 1 q ∈ shadow.states := by
      have hRightExecutionState : q ∈ rightExecution.states :=
        Finset.mem_union_left _ hState
      simp only [shadow, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, childStates, Finset.mem_image]
      exact Or.inr ⟨q, hRightExecutionState, rfl⟩
    rw [show (TypeAutomatonState.child 1 q) = childState 1 q from rfl,
      markerReachable_iff_of_same_edges
        (sequenceExecutionFragment fragment) shadow name hEdges
          hExecutionClosed hShadowClosed (childState 1 q) hExecutionState
            hShadowState]
    exact hRightTaggedShadow q r hr

/-- Execution-view marker correspondence for an exclusive offer. -/
private theorem buildExclusiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType))
          name q ↔ PactType.markerReachableSubst name r = true))
    (hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable (sequenceExecutionFragment
          (compileTypeFuel signature (typeCompilationFuel branchType)
            branchType)) name q ↔
              PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (typeBranchCompilationFuel branches)
    let fragment := buildExclusiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun branch =>
        (branch.1, compileTypeFuel signature fuel branch.2))
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        PactType.markerReachableSubst name (.xoffer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
        branches[index]? = some (action, branchType) →
        ∀ q r, TypeCompilationRelation branchType q r →
          (MarkerReachable (sequenceExecutionFragment fragment) name
              (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches) with hFuelDef
  set elseFragment := compileTypeFuel signature fuel elseType with hElseDef
  set branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2) with hAutomataDef
  set fragment := buildExclusiveOfferAutomaton signature branches elseFragment
    branchAutomata with hFragmentDef
  set entries := exclusiveOfferEntryStates elseFragment branchAutomata
    with hEntriesDef
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hElseStable : elseFragment =
      compileTypeFuel signature (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hBranchFuel : ∀ branch ∈ branches,
      TypeCompilationFuelSufficient branch.2 fuel := by
    intro branch hBranch
    exact (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
      hBranch).trans (by simp [hFuelDef])
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      (hBranchFuel branch hBranch)
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel branch.2
      (hBranchFuel branch hBranch)
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildExclusiveOfferAutomaton_futureTargetsInStates signature branches
      elseFragment branchAutomata hElseTargets hBranchTargets hElseInitial
        hBranchInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [hFragmentDef, buildExclusiveOfferAutomaton,
      finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2 branch hBranch
  have hUpper : fragment.toPending.referencedStates .root ⊆
      insert .root entries :=
    buildExclusiveOfferAutomaton_root_references_upper signature branches
      elseFragment branchAutomata
  have hEntriesSubset : entries ⊆ fragment.toPending.referencedStates .root :=
    buildExclusiveOfferAutomaton_entries_referenced signature branches
      elseFragment branchAutomata hAvailable
  have hElseStates : childStates 0 elseFragment ⊆ fragment.states := by
    intro child hChild
    simp [hFragmentDef, buildExclusiveOfferAutomaton,
      finishAutomatonFragment, hChild]
  have hElseTagged : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment fragment) name
          (.child 0 q) ↔ PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ elseFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        elseType q r hr
      simpa [hElseStable] using hCanonical
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      sequenceExecution_taggedChild_markerReachable fragment elseFragment 0
        name (fun current edge => buildExclusiveOfferAutomaton_outgoing_else
          signature branches elseFragment branchAutomata current edge)
        hElseStates hElseTargets q hState,
      hElseStable]
    exact hElseIH q r hr
  have hBranchTagged : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
      ∀ q r, TypeCompilationRelation branchType q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child (index + 1) q) ↔
          PactType.markerReachableSubst name r = true) := by
    intro action branchType index hSyntaxEntry q r hr
    have hMember : (action, branchType) ∈ branches := by
      rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with ⟨hBound, hValue⟩
      have hAt := List.getElem_mem hBound
      simpa [hValue] using hAt
    have hAutomatonEntry : branchAutomata[index]? =
        some (action, compileTypeFuel signature fuel branchType) := by
      simp [hAutomataDef, List.getElem?_map, hSyntaxEntry]
    have hBranchStable : compileTypeFuel signature fuel branchType =
        compileTypeFuel signature (typeCompilationFuel branchType) branchType :=
      compileTypeFuel_eq_of_sufficient signature branchType
        (hBranchFuel (action, branchType) hMember)
          (typeCompilationFuel_sufficient branchType)
    have hState : q ∈ (compileTypeFuel signature fuel branchType).states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        branchType q r hr
      simpa [hBranchStable] using hCanonical
    have hStates : childStates (index + 1)
        (compileTypeFuel signature fuel branchType) ⊆ fragment.states := by
      intro child hChild
      simp only [childStates, Finset.mem_image] at hChild
      rcases hChild with ⟨inner, hInner, rfl⟩
      have hIndexedState : childState (index + 1) inner ∈
          indexedFragmentStates branchAutomata := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        exact ⟨((action, compileTypeFuel signature fuel branchType), index),
          mem_zipIdx_of_getElem? hAutomatonEntry,
          by simp [childStates, childState, hInner]⟩
      simp [hFragmentDef, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, hIndexedState]
    rw [show (TypeAutomatonState.child (index + 1) q) =
        childState (index + 1) q from rfl,
      sequenceExecution_taggedChild_markerReachable fragment
        (compileTypeFuel signature fuel branchType) (index + 1) name
        (fun current edge => buildExclusiveOfferAutomaton_outgoing_branch
          signature branches elseFragment branchAutomata index
            (action, compileTypeFuel signature fuel branchType)
              hAutomatonEntry current edge)
        hStates
        (compileTypeFuel_futureTargetsInStates signature fuel branchType
          (hBranchFuel (action, branchType) hMember)) q hState,
      hBranchStable]
    exact hBranchIH action branchType index hSyntaxEntry q r hr
  refine ⟨?_, hElseTagged, hBranchTagged⟩
  have hRootIff := sequenceExecution_markerReachable_root_of_entries fragment
    name entries hFragmentTargets hRoot
      (sequenceExecution_buildExclusiveOffer_root_shape signature branches
        elseFragment branchAutomata) hUpper hEntriesSubset
  rw [hRootIff, PactType.markerReachableSubst]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd
        ((sequenceExecutionFragment_markerSource fragment name .root).mp
          hMarker)
        (not_buildExclusiveOfferAutomaton_markerSource_root signature branches
          elseFragment branchAutomata name)
    · rw [hEntriesDef, exclusiveOfferEntryStates, Finset.mem_union,
        Finset.mem_singleton] at hEntry
      rcases hEntry with rfl | hBranchEntry
      · have hElseRelation : TypeCompilationRelation elseType
            elseFragment.initial elseType := by
          rw [hElseStable]
          exact compileTypeFuel_initial_relation signature
            (typeCompilationFuel elseType) elseType
              (typeCompilationFuel_sufficient elseType)
        have hValue := (hElseTagged elseFragment.initial elseType
          hElseRelation).mp hInner
        simp [hValue]
      · rw [mem_foldl_union_iff] at hBranchEntry
        rcases hBranchEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
        · simp at hEmpty
        · rw [Finset.mem_singleton] at hEntryState
          subst entry
          rcases compiledBranch_zipIdx_cases signature fuel branches indexed
              (by simpa [hAutomataDef] using hIndexed) with
            ⟨action, branchType, hSyntaxEntry, hCompiledEntry⟩
          rcases indexed with ⟨compiledEntry, index⟩
          simp only at hCompiledEntry
          subst compiledEntry
          have hMember : (action, branchType) ∈ branches := by
            rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
              ⟨hBound, hValue⟩
            have hAt := List.getElem_mem hBound
            simpa [hValue] using hAt
          have hBranchStable : compileTypeFuel signature fuel branchType =
              compileTypeFuel signature (typeCompilationFuel branchType)
                branchType :=
            compileTypeFuel_eq_of_sufficient signature branchType
              (hBranchFuel (action, branchType) hMember)
                (typeCompilationFuel_sufficient branchType)
          have hBranchEntryRelation : TypeCompilationRelation branchType
              (compileTypeFuel signature fuel branchType).initial branchType := by
            rw [hBranchStable]
            exact compileTypeFuel_initial_relation signature
              (typeCompilationFuel branchType) branchType
                (typeCompilationFuel_sufficient branchType)
          have hValue := (hBranchTagged action branchType index hSyntaxEntry
            (compileTypeFuel signature fuel branchType).initial branchType
              hBranchEntryRelation).mp hInner
          have hFold := (branchMarkerReachableSubst_iff_exists name
            branches).mpr ⟨(action, branchType), hMember, hValue⟩
          simp [hFold]
  · intro hValue
    simp only [Bool.or_eq_true] at hValue
    right
    rcases hValue with hElseValue | hBranchValue
    · refine ⟨childState 0 elseFragment.initial, ?_, ?_⟩
      · rw [hEntriesDef, exclusiveOfferEntryStates]
        simp
      · apply (hElseTagged elseFragment.initial elseType ?_).mpr hElseValue
        rw [hElseStable]
        exact compileTypeFuel_initial_relation signature
          (typeCompilationFuel elseType) elseType
            (typeCompilationFuel_sufficient elseType)
    · rcases (branchMarkerReachableSubst_iff_exists name branches).mp
        hBranchValue with ⟨entry, hMember, hEntryValue⟩
      rcases exists_getElem?_of_mem hMember with ⟨index, hIndex⟩
      obtain ⟨action, branchType⟩ := entry
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, compileTypeFuel signature fuel branchType) := by
        simp [hAutomataDef, List.getElem?_map, hIndex]
      have hBranchStable : compileTypeFuel signature fuel branchType =
          compileTypeFuel signature (typeCompilationFuel branchType)
            branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType
          (hBranchFuel (action, branchType) hMember)
            (typeCompilationFuel_sufficient branchType)
      have hBranchEntryRelation : TypeCompilationRelation branchType
          (compileTypeFuel signature fuel branchType).initial branchType := by
        rw [hBranchStable]
        exact compileTypeFuel_initial_relation signature
          (typeCompilationFuel branchType) branchType
            (typeCompilationFuel_sufficient branchType)
      refine ⟨childState (index + 1)
        (compileTypeFuel signature fuel branchType).initial, ?_, ?_⟩
      · rw [hEntriesDef, exclusiveOfferEntryStates, Finset.mem_union,
          mem_foldl_union_iff]
        right
        right
        exact ⟨((action, compileTypeFuel signature fuel branchType), index),
          mem_zipIdx_of_getElem? hAutomatonEntry, by simp⟩
      · exact (hBranchTagged action branchType index hIndex
          (compileTypeFuel signature fuel branchType).initial branchType
            hBranchEntryRelation).mpr hEntryValue

/-- Execution-view marker correspondence for a conjunctive offer.  Generated
conjunction children are non-tail positions, so only the else continuation can
contribute a marker. -/
private theorem buildSelectedConjunctiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (name : String)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesAbsent : PactType.TailBranchOccurrences name False branches)
    (hElseIH : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType))
          name q ↔ PactType.markerReachableSubst name r = true)) :
    let fuel := max (typeCompilationFuel elseType)
      (conjunctiveCompilationFuel branches)
    let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
      (compileTypeFuel signature fuel elseType)
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)))
    (MarkerReachable (sequenceExecutionFragment fragment) name .root ↔
        PactType.markerReachableSubst name (.offer elseType branches) = true) ∧
      (∀ q r, TypeCompilationRelation elseType q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child 0 q) ↔
          PactType.markerReachableSubst name r = true)) ∧
      (∀ (selected : BareMessage × PactType) (index : Nat),
        branches[index]? = some selected →
        ∀ q r, TypeCompilationRelation
            (parallelTypeBranchesSelecting selected branches) q r →
          (MarkerReachable (sequenceExecutionFragment fragment) name
              (.child (index + 1) q) ↔
            PactType.markerReachableSubst name r = true)) := by
  classical
  set fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches) with hFuelDef
  set elseFragment := compileTypeFuel signature fuel elseType with hElseDef
  set selectedConjunctions := branches.map fun selected =>
    (selected.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting selected branches)) with hConjDef
  set fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions with hFragmentDef
  set entries := selectedConjunctiveOfferEntryStates elseFragment
    selectedConjunctions with hEntriesDef
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, hFuelDef]
  have hElseStable : elseFragment =
      compileTypeFuel signature (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hSelectedFuel : ∀ selected : BareMessage × PactType,
      TypeCompilationFuelSufficient
        (parallelTypeBranchesSelecting selected branches) fuel := by
    intro selected
    simp [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, hFuelDef]
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hConjTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel _
      (hSelectedFuel selected)
  have hConjInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel _ (hSelectedFuel selected)
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates signature
      branches elseFragment selectedConjunctions hElseTargets hConjTargets
        hElseInitial hConjInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, hSelected, rfl⟩
    exact supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2 selected hSelected
  have hUpper : fragment.toPending.referencedStates .root ⊆
      insert .root entries :=
    buildSelectedConjunctiveOfferAutomaton_root_references_upper signature
      branches elseFragment selectedConjunctions
  have hEntriesSubset : entries ⊆ fragment.toPending.referencedStates .root :=
    buildSelectedConjunctiveOfferAutomaton_entries_referenced signature
      branches elseFragment selectedConjunctions hAvailable
  have hElseStates : childStates 0 elseFragment ⊆ fragment.states := by
    intro child hChild
    simp [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, hChild]
  have hElseTagged : ∀ q r, TypeCompilationRelation elseType q r →
      (MarkerReachable (sequenceExecutionFragment fragment) name
          (.child 0 q) ↔ PactType.markerReachableSubst name r = true) := by
    intro q r hr
    have hState : q ∈ elseFragment.states := by
      have hCanonical := compilationStateCorrect_of_compilation signature
        elseType q r hr
      simpa [hElseStable] using hCanonical
    rw [show (TypeAutomatonState.child 0 q) = childState 0 q from rfl,
      sequenceExecution_taggedChild_markerReachable fragment elseFragment 0
        name (fun current edge =>
          buildSelectedConjunctiveOfferAutomaton_outgoing_else signature
            branches elseFragment selectedConjunctions current edge)
        hElseStates hElseTargets q hState,
      hElseStable]
    exact hElseIH q r hr
  have hConjTagged : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
      ∀ q r, TypeCompilationRelation
          (parallelTypeBranchesSelecting selected branches) q r →
        (MarkerReachable (sequenceExecutionFragment fragment) name
            (.child (index + 1) q) ↔
          PactType.markerReachableSubst name r = true) := by
    intro selected index hSyntaxEntry q r hr
    have hAbsent : PactType.TailOccurrences name False
        (parallelTypeBranchesSelecting selected branches) :=
      tailOccurrences_parallelTypeBranchesSelecting name selected branches
        hBranchesAbsent
    have hConjEntry : selectedConjunctions[index]? =
        some (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) := by
      simp [hConjDef, List.getElem?_map, hSyntaxEntry]
    have hState : q ∈ (compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)).states := by
      have hStable : compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches) =
          compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected
              branches)) (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
          (typeCompilationFuel_sufficient _)
      have hCanonical := compilationStateCorrect_of_compilation signature
        (parallelTypeBranchesSelecting selected branches) q r hr
      simpa [hStable] using hCanonical
    have hStates : childStates (index + 1)
        (compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches)) ⊆
          fragment.states := by
      intro child hChild
      simp only [childStates, Finset.mem_image] at hChild
      rcases hChild with ⟨inner, hInner, rfl⟩
      have hIndexedState : childState (index + 1) inner ∈
          indexedFragmentStates selectedConjunctions := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        exact ⟨((selected.1, compileTypeFuel signature fuel
            (parallelTypeBranchesSelecting selected branches)), index),
          mem_zipIdx_of_getElem? hConjEntry,
          by simp [childStates, childState, hInner]⟩
      simp [hFragmentDef, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, hIndexedState]
    have hTransport : MarkerReachable (sequenceExecutionFragment fragment)
        name (childState (index + 1) q) ↔
        MarkerReachable (sequenceExecutionFragment (compileTypeFuel signature
          fuel (parallelTypeBranchesSelecting selected branches))) name q :=
      sequenceExecution_taggedChild_markerReachable fragment _ (index + 1)
        name (fun current edge =>
          buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction signature
            branches elseFragment selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) hConjEntry
                  current edge)
        hStates
        (compileTypeFuel_futureTargetsInStates signature fuel _
          (hSelectedFuel selected)) q hState
    have hNoGraph : ¬ MarkerReachable
        (sequenceExecutionFragment (compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches))) name q :=
      not_sequenceExecutionMarkerReachable_of_tailOccurrences_false signature
        name fuel _ (hSelectedFuel selected) hAbsent q
    have hNoSyntax : PactType.markerReachableSubst name r = false :=
      PactType.markerReachableSubst_eq_false_of_tailOccurrences_false name r
        (compilationRelation_tailOccurrences_false name hr hAbsent)
    rw [show (TypeAutomatonState.child (index + 1) q) =
      childState (index + 1) q from rfl, hTransport, hNoSyntax]
    simp [hNoGraph]
  have hElseEntryRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    rw [hElseStable]
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel elseType) elseType
        (typeCompilationFuel_sufficient elseType)
  have hBranchNone : PactType.branchMarkerReachableSubst name branches =
      false := by
    by_contra hContra
    rcases (branchMarkerReachableSubst_iff_exists name branches).mp
      (by simpa using hContra) with ⟨entry, hMember, hValue⟩
    rw [PactType.markerReachableSubst_eq_false_of_tailOccurrences_false name
      entry.2 (tailOccurrences_false_of_branch_mem name branches
        hBranchesAbsent entry hMember)] at hValue
    exact absurd hValue (by simp)
  refine ⟨?_, hElseTagged, hConjTagged⟩
  have hRootIff := sequenceExecution_markerReachable_root_of_entries fragment
    name entries hFragmentTargets hRoot
      (sequenceExecution_buildSelectedConjunctiveOffer_root_shape signature
        branches elseFragment selectedConjunctions) hUpper hEntriesSubset
  rw [hRootIff, PactType.markerReachableSubst, hBranchNone]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd
        ((sequenceExecutionFragment_markerSource fragment name .root).mp
          hMarker)
        (not_buildSelectedConjunctiveOfferAutomaton_markerSource_root signature
          branches elseFragment selectedConjunctions name)
    · rw [hEntriesDef, selectedConjunctiveOfferEntryStates,
        Finset.mem_union, Finset.mem_singleton] at hEntry
      rcases hEntry with rfl | hConjEntry
      · have hValue := (hElseTagged elseFragment.initial elseType
          hElseEntryRelation).mp hInner
        simp [hValue]
      · rw [mem_foldl_union_iff] at hConjEntry
        rcases hConjEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
        · simp at hEmpty
        · rw [Finset.mem_singleton] at hEntryState
          subst entry
          rcases selectedConjunction_zipIdx_cases signature fuel branches
              indexed (by simpa [hConjDef] using hIndexed) with
            ⟨selected, hSyntaxEntry, hCompiledEntry⟩
          rcases indexed with ⟨compiledEntry, index⟩
          simp only at hCompiledEntry
          subst compiledEntry
          exfalso
          have hStable : compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches) =
              compileTypeFuel signature
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) :=
            compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
              (typeCompilationFuel_sufficient _)
          have hInitRelation : TypeCompilationRelation
              (parallelTypeBranchesSelecting selected branches)
              (compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)).initial
              (parallelTypeBranchesSelecting selected branches) := by
            rw [hStable]
            exact compileTypeFuel_initial_relation signature _ _
              (typeCompilationFuel_sufficient _)
          have hValue := (hConjTagged selected index hSyntaxEntry _ _
            hInitRelation).mp hInner
          rw [PactType.markerReachableSubst_eq_false_of_tailOccurrences_false
            name _ (tailOccurrences_parallelTypeBranchesSelecting name selected
              branches hBranchesAbsent)] at hValue
          exact absurd hValue (by simp)
  · intro hValue
    simp only [Bool.or_false] at hValue
    exact Or.inr ⟨childState 0 elseFragment.initial, by
      rw [hEntriesDef, selectedConjunctiveOfferEntryStates]
      simp, (hElseTagged elseFragment.initial elseType
        hElseEntryRelation).mpr hValue⟩


/-- Marker reachability in the execution view is computed by the same syntax
analysis as marker reachability in the constructor fragment.  This is the
bridge needed when an enclosing recursion is itself placed to the left of a
sequence: its installed backedges are built from the body's execution view,
not from the body's original symbolic-future view. -/
theorem compilationSequenceExecutionMarkerReachable_iff
    (signature : TypeAlphabet) :
    ∀ (bound : List String) (name : String) (processType : PactType),
      name ∈ bound →
      PactType.AllTailOccurrences bound True processType →
      signature.WellFormed →
      signature.Supports processType →
      PactType.AllVariablesBound bound processType →
      PactType.BinderHygienic bound processType →
      PactType.ClockGuarded processType →
      PactType.TailRecursive processType →
      PactType.SameCycleMessageLinear processType →
      PactType.InterfaceScoped processType →
      (∀ child : PactType, sizeOf child < sizeOf processType →
        signature.Supports child → PactType.AllVariablesBound [] child →
        PactType.BinderHygienic [] child → PactType.ClockGuarded child →
        PactType.TailRecursive child →
        PactType.SameCycleMessageLinear child →
        PactType.InterfaceScoped child →
          CompilationProofBundle signature child) →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          (MarkerReachable (sequenceExecutionFragment
              (compileTypeFuel signature (typeCompilationFuel processType)
                processType)) name state ↔
            PactType.markerReachableSubst name residual = true) := by
  classical
  intro bound name processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing bound name processType with
  | _ n ih =>
      intro hName hAllTail hSignature hSupports hBound hHygienic hGuarded
        hTail hLinear hScoped hClosedBundle state residual hRelated
      have hTailName : processType.TailOccurrences name True :=
        hAllTail name hName
      cases processType with
      | message msg dir =>
          have hNo :=
            not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
              signature name (typeCompilationFuel (.message msg dir))
                (.message msg dir) (typeCompilationFuel_sufficient _)
                  (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | progress pid =>
          have hNo :=
            not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
              signature name (typeCompilationFuel (.progress pid))
                (.progress pid) (typeCompilationFuel_sufficient _)
                  (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | tock =>
          have hNo :=
            not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
              signature name (typeCompilationFuel .tock) .tock
                (typeCompilationFuel_sufficient _)
                  (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | skip =>
          have hNo :=
            not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
              signature name (typeCompilationFuel .skip) .skip
                (typeCompilationFuel_sufficient _)
                  (by simp [PactType.TailOccurrences]) state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated <;>
              simp [PactType.markerReachableSubst] at hValue
      | par left right interface =>
          have hFalse : PactType.TailOccurrences name False
              (.par left right interface) := by
            simpa only [PactType.TailOccurrences] using hTailName
          have hNo :=
            not_sequenceExecutionMarkerReachable_of_tailOccurrences_false
              signature name
                (typeCompilationFuel (.par left right interface))
                  (.par left right interface) (typeCompilationFuel_sufficient _)
                    hFalse state
          constructor
          · intro hMarker
            exact absurd hMarker hNo
          · intro hValue
            cases hRelated
            simp [PactType.markerReachableSubst] at hValue
      | var current =>
          cases hRelated with
          | «variable» _ =>
              constructor
              · rintro ⟨reached, _, hSource⟩
                have hRawSource :=
                  (sequenceExecutionFragment_markerSource
                    (compileTypeFuel signature
                      (typeCompilationFuel (.var current)) (.var current))
                    name reached).mp hSource
                rcases hRawSource with ⟨rawEdge, hRawEdge, _, hRawLabel⟩
                have hShape : rawEdge.label =
                    AutomatonConstructionLabel.variable current := by
                  simp only [typeCompilationFuel, compileTypeFuel,
                    finishAutomatonFragment, Finset.mem_image] at hRawEdge
                  rcases hRawEdge with ⟨environment, _, rfl⟩
                  rfl
                rw [hShape] at hRawLabel
                have hEq : current = name := by simpa using hRawLabel
                simp [PactType.markerReachableSubst, hEq]
              · intro hValue
                have hEq : name = current := by
                  by_cases hCase : name = current
                  · exact hCase
                  · simp [PactType.markerReachableSubst, hCase] at hValue
                let rawEdge : PendingAutomatonEdge :=
                  { source := .root
                    environment := TypeEnvironment.tock
                    label := .variable current
                    current := ∅
                    future := .explicit ∅
                    target := .final }
                have hRawEdge : rawEdge ∈
                    (compileTypeFuel signature (typeCompilationFuel (.var current))
                      (.var current)).edges := by
                  simp only [rawEdge, typeCompilationFuel, compileTypeFuel,
                    finishAutomatonFragment, Finset.mem_image]
                  exact ⟨TypeEnvironment.tock,
                    by simp [TypeAlphabet.localEnvironments], rfl⟩
                have hRawSource : MarkerSource
                    (compileTypeFuel signature
                      (typeCompilationFuel (.var current)) (.var current))
                    name .root :=
                  ⟨rawEdge, hRawEdge, rfl, by simp [rawEdge, hEq]⟩
                have hExecutionSource : MarkerSource
                    (sequenceExecutionFragment
                      (compileTypeFuel signature
                        (typeCompilationFuel (.var current)) (.var current)))
                    name .root :=
                  (sequenceExecutionFragment_markerSource _ name .root).mpr
                    hRawSource
                refine ⟨.root,
                  PendingAutomaton.mem_futureReachable_self _ _, ?_⟩
                exact hExecutionSource
      | recur other body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportBody : signature.Supports body := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundBody : PactType.AllVariablesBound (other :: bound) body := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : other ∉ bound ∧
              PactType.BinderHygienic (other :: bound) body := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : body.GuardedOccurrences other False ∧
              body.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : body.TailOccurrences other True ∧
              body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : body.SameCycleMessageLinear ∧
              Disjoint (PactType.SuffixMessageIds body)
                (PactType.PrefixMessageIds body) := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedBody : body.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hDistinct : name ≠ other := by
            intro hEq
            subst other
            exact hHygienicFields.1 hName
          have hOtherName : ¬ other = name := fun h => hDistinct h.symm
          have hAllTailBody : PactType.AllTailOccurrences (other :: bound) True
              body := by
            intro m hm
            rcases List.mem_cons.mp hm with rfl | hRest
            · exact hTailFields.1
            · have hNe : ¬ other = m := by
                intro hEq
                exact hHygienicFields.1 (hEq ▸ hRest)
              have hEntry := hAllTail m hRest
              simpa only [PactType.TailOccurrences, if_neg hNe] using hEntry
          have hBodyCallback : ∀ child : PactType, sizeOf child < sizeOf body →
              signature.Supports child → PactType.AllVariablesBound [] child →
              PactType.BinderHygienic [] child → PactType.ClockGuarded child →
              PactType.TailRecursive child →
              PactType.SameCycleMessageLinear child →
              PactType.InterfaceScoped child →
                CompilationProofBundle signature child :=
            fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hBodySize)
          have hBodyIH : ∀ m, m ∈ (other :: bound) → ∀ q r,
              TypeCompilationRelation body q r →
                (MarkerReachable (sequenceExecutionFragment
                    (compileTypeFuel signature (typeCompilationFuel body) body))
                    m q ↔ PactType.markerReachableSubst m r = true) := by
            intro m hm q r hr
            exact ih (sizeOf body) hBodySize (other :: bound) m body rfl hm
              hAllTailBody hSignature hSupportBody hBoundBody
              hHygienicFields.2 hGuardedFields.2 hTailFields.2
              hLinearFields.1 hScopedBody hBodyCallback q r hr
          set bodyFragment := compileTypeFuel signature
            (typeCompilationFuel body) body with hBodyFragment
          set bodyExecution := sequenceExecutionFragment bodyFragment
            with hBodyExecution
          set stopped := markerStoppedFragment bodyExecution other
            with hStopped
          set parent := buildRecursionAutomaton signature other bodyFragment
            with hParent
          set shadow := buildRecursionAutomaton signature other stopped
            with hShadow
          have hBodyFuel : TypeCompilationFuelSufficient body
              (typeCompilationFuel body) := typeCompilationFuel_sufficient body
          have hBodyTargets : bodyFragment.FutureTargetsInStates :=
            compileTypeFuel_futureTargetsInStates signature
              (typeCompilationFuel body) body hBodyFuel
          have hBodyInitial : bodyFragment.initial ∈ bodyFragment.states :=
            compileTypeFuel_initial_mem signature (typeCompilationFuel body)
              body hBodyFuel
          have hBodyExecutionTargets : bodyExecution.FutureTargetsInStates := by
            simpa [bodyExecution] using
              sequenceExecutionFragment_futureTargetsInStates bodyFragment
                hBodyTargets
          have hBodyExecutionClosed : bodyExecution.toPending.ReferencesClosed :=
            PendingAutomaton.referencesClosed_of_futureTargetsInStates
              bodyExecution hBodyExecutionTargets
          have hStoppedTargets : stopped.FutureTargetsInStates := by
            simpa [stopped] using markerStoppedFragment_futureTargetsInStates
              bodyExecution other hBodyExecutionTargets
          have hStoppedClosed : stopped.toPending.ReferencesClosed :=
            PendingAutomaton.referencesClosed_of_futureTargetsInStates stopped
              hStoppedTargets
          have hStoppedInitial : stopped.initial ∈ stopped.states := by
            exact Finset.mem_union_left _ hBodyInitial
          have hStoppedMarkers : MarkerEdgesInert stopped other := by
            simpa [stopped] using
              markerStoppedFragment_markerEdgesInert bodyExecution other
          have hShadowTargets : shadow.FutureTargetsInStates := by
            simpa [shadow] using
              buildRecursionAutomaton_futureTargetsInStates signature other
                stopped hStoppedTargets hStoppedInitial
          have hShadowClosed : shadow.toPending.ReferencesClosed :=
            PendingAutomaton.referencesClosed_of_futureTargetsInStates shadow
              hShadowTargets
          have hParentTargets : parent.FutureTargetsInStates := by
            simpa [parent] using
              buildRecursionAutomaton_futureTargetsInStates signature other
                bodyFragment hBodyTargets hBodyInitial
          have hParentExecutionClosed :
              (sequenceExecutionFragment parent).toPending.ReferencesClosed :=
            PendingAutomaton.referencesClosed_of_futureTargetsInStates _
              (sequenceExecutionFragment_futureTargetsInStates parent
                hParentTargets)
          have hEdges : (sequenceExecutionFragment parent).edges =
              shadow.edges := by
            simpa [parent, shadow, sequenceExecutionFragment] using
              sequenceExecution_buildRecursion_edges signature other
                bodyFragment
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.recur other body)) (.recur other body) =
                parent := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
              parent, hBodyFragment]
          have hStoppedIff : ∀ query q, q ∈ bodyFragment.states →
              (MarkerReachable stopped query q ↔
                MarkerReachable bodyExecution query q) := by
            intro query q hq
            simpa [stopped, bodyExecution, bodyFragment] using
              markerStopped_sequenceExecution_markerReachable_iff signature
                other query (typeCompilationFuel body) body hBodyFuel
                  hTailFields.1 q hq
          have hEntryIff : MarkerReachable shadow name
              (childState 0 stopped.initial) ↔
                PactType.markerReachableSubst name body = true := by
            rw [show shadow = buildRecursionAutomaton signature other stopped
                from hShadow,
              buildRecursionAutomaton_markerReachable_child_at_initial
                signature other name stopped hDistinct hStoppedMarkers
                  hStoppedClosed hShadowClosed hStoppedInitial,
              show stopped.initial = bodyFragment.initial by
                simp [stopped, bodyExecution, markerStoppedFragment,
                  sequenceExecutionFragment]]
            have hInitialRelation : TypeCompilationRelation body
                bodyFragment.initial body := by
              rw [hBodyFragment]
              exact compileTypeFuel_initial_relation signature
                (typeCompilationFuel body) body hBodyFuel
            exact (hStoppedIff name bodyFragment.initial hBodyInitial).trans
              (by
                simpa [hBodyExecution, hBodyFragment] using
                  hBodyIH name (List.mem_cons_of_mem other hName)
                    bodyFragment.initial body hInitialRelation)
          rw [hFragment]
          cases hRelated with
          | recur_source =>
              have hExecutionRoot : (.root : TypeAutomatonState) ∈
                  (sequenceExecutionFragment parent).states := by
                apply Finset.mem_union_left
                simp [parent, buildRecursionAutomaton,
                  finishAutomatonFragment]
              have hShadowRoot : (.root : TypeAutomatonState) ∈
                  shadow.states := by
                simp [shadow, buildRecursionAutomaton,
                  finishAutomatonFragment]
              rw [markerReachable_iff_of_same_edges
                  (sequenceExecutionFragment parent) shadow name hEdges
                    hParentExecutionClosed hShadowClosed .root hExecutionRoot
                      hShadowRoot,
                show shadow = buildRecursionAutomaton signature other stopped
                  from hShadow,
                buildRecursionAutomaton_markerReachable_root signature other
                  name stopped hShadowClosed,
                hEntryIff]
              simp [PactType.markerReachableSubst, hDistinct]
          | recur_body _ _ childResidual childQ hChild =>
              have hChildState : childQ ∈ bodyFragment.states := by
                have hCanonical := compilationStateCorrect_of_compilation
                  signature body childQ childResidual hChild
                simpa [hBodyFragment] using hCanonical
              have hChildTailOther :
                  childResidual.TailOccurrences other True :=
                compilationRelation_tailOccurrences_true other hChild
                  hTailFields.2 hTailFields.1
              have hChildFresh : childResidual.BinderFreshFor [name] := by
                apply PactType.binderFreshFor_mono
                  (smaller := [name]) (larger := other :: bound)
                · intro m hm
                  rcases List.mem_singleton.mp hm with rfl
                  exact List.mem_cons_of_mem other hName
                · exact compilationRelation_binderFreshFor hChild
                    hHygienicFields.2
              have hExecutionState : childState 0 childQ ∈
                  (sequenceExecutionFragment parent).states := by
                apply Finset.mem_union_left
                simp only [parent, buildRecursionAutomaton,
                  finishAutomatonFragment, Finset.mem_union, childStates,
                  Finset.mem_image]
                exact Or.inr ⟨childQ, hChildState, rfl⟩
              have hShadowState : childState 0 childQ ∈ shadow.states := by
                have hStoppedState : childQ ∈ stopped.states := by
                  have hExecutionState : childQ ∈ bodyExecution.states := by
                    change childQ ∈ bodyFragment.states ∪
                      bodyFragment.edges.image PendingAutomatonEdge.target
                    exact Finset.mem_union_left _ hChildState
                  simpa [stopped, markerStoppedFragment] using hExecutionState
                simp only [shadow, buildRecursionAutomaton,
                  finishAutomatonFragment, Finset.mem_union, childStates,
                  Finset.mem_image]
                exact Or.inr ⟨childQ, hStoppedState, rfl⟩
              rw [show (TypeAutomatonState.child 0 childQ) =
                    childState 0 childQ from rfl,
                markerReachable_iff_of_same_edges
                  (sequenceExecutionFragment parent) shadow name hEdges
                    hParentExecutionClosed hShadowClosed
                      (childState 0 childQ) hExecutionState hShadowState,
                show shadow = buildRecursionAutomaton signature other stopped
                  from hShadow,
                buildRecursionAutomaton_markerReachable_child signature other
                  name stopped hDistinct hStoppedMarkers hStoppedClosed
                    hShadowClosed hStoppedInitial childQ (by
                      have hExecutionState : childQ ∈ bodyExecution.states := by
                        change childQ ∈ bodyFragment.states ∪
                          bodyFragment.edges.image PendingAutomatonEdge.target
                        exact Finset.mem_union_left _ hChildState
                      simpa [stopped, markerStoppedFragment] using
                        hExecutionState),
                hEntryIff,
                hStoppedIff name childQ hChildState,
                hStoppedIff other childQ hChildState]
              have hOuterIH := hBodyIH name
                (List.mem_cons_of_mem other hName) childQ childResidual hChild
              have hBinderIH := hBodyIH other List.mem_cons_self childQ
                childResidual hChild
              rw [show bodyExecution = sequenceExecutionFragment
                    (compileTypeFuel signature (typeCompilationFuel body) body)
                  by simp [bodyExecution, bodyFragment],
                hOuterIH, hBinderIH,
                PactType.markerReachableSubst_replaceVar name other
                  (.recur other body) hDistinct childResidual hChildTailOther
                    hChildFresh]
              rw [show PactType.markerReachableSubst name
                  (.recur other body) =
                  PactType.markerReachableSubst name body by
                simp [PactType.markerReachableSubst, hDistinct]]
              cases PactType.markerReachableSubst name childResidual <;>
                cases PactType.markerReachableSubst other childResidual <;>
                cases PactType.markerReachableSubst name body <;> simp
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : left.SameCycleMessageLinear ∧
              right.SameCycleMessageLinear := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hLeftIH := ih (sizeOf left) hLeftSize bound name left rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hLeftSize))
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified :=
            buildChoiceAutomaton_sequenceExecutionMarkerReachable_classified
              signature left right TypeLabel.silent TypeLabel.silent name
                (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent])
                  hLeftIH hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.choice left right)) (.choice left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right)
                TypeLabel.silent TypeLabel.silent := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | choice_source =>
              rw [hClassified.1, PactType.markerReachableSubst]
              simp [Bool.or_eq_true]
          | choice_left _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | choice_right _ _ _ _ hChild => exact hClassified.2.2 _ _ hChild
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportFields := hSupports
          simp only [TypeAlphabet.Supports] at hSupportFields
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : left.SameCycleMessageLinear ∧
              right.SameCycleMessageLinear := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hLeftIH := ih (sizeOf left) hLeftSize bound name left rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.2.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hLeftSize))
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified :=
            buildChoiceAutomaton_sequenceExecutionMarkerReachable_classified
              signature left right (TypeLabel.fair bid true)
                (TypeLabel.fair bid false) name
                (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
                  hLeftIH hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.fairChoice bid left right))
                (.fairChoice bid left right) =
              buildChoiceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | fair_source =>
              rw [hClassified.1, PactType.markerReachableSubst]
              simp [Bool.or_eq_true]
          | fair_left _ _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | fair_right _ _ _ _ _ hChild => exact hClassified.2.2 _ _ hChild
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportFields : signature.Supports left ∧
              signature.Supports right := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound left ∧
              PactType.BinderHygienic bound right := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : left.ClockGuarded ∧ right.ClockGuarded := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields := hLinear
          simp only [PactType.SameCycleMessageLinear] at hLinearFields
          have hScopedFields : left.InterfaceScoped ∧
              right.InterfaceScoped := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hAllTailLeftFalse : PactType.AllTailOccurrences bound False
              left := by
            intro m hm
            have hEntry := hAllTail m hm
            simp only [PactType.TailOccurrences] at hEntry
            exact hEntry.1
          have hLeftClosedType : PactType.AllVariablesBound [] left := by
            apply PactType.allVariablesBound_drop_of_allTailOccurrences_false
              bound [] left hAllTailLeftFalse
            simpa using hBoundFields.1
          have hLeftHygienicEmpty : PactType.BinderHygienic [] left :=
            PactType.binderHygienic_mono (by intro m hm; simp at hm) left
              hHygienicFields.1
          have hLeftBundle := hClosedBundle left hLeftSize hSupportFields.1
            hLeftClosedType hLeftHygienicEmpty hGuardedFields.1 hTailFields.1
            hLinearFields.1 hScopedFields.1
          have hRightIH := ih (sizeOf right) hRightSize bound name right rfl
            hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.2)
            hSignature hSupportFields.2 hBoundFields.2 hHygienicFields.2
            hGuardedFields.2 hTailFields.2 hLinearFields.2.1 hScopedFields.2
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hRightSize))
          have hClassified :=
            buildSequenceAutomaton_sequenceExecutionMarkerReachable_classified
              signature left right name (hAllTailLeftFalse name hName)
                hLeftBundle.execution hRightIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.seq left right)) (.seq left right) =
              buildSequenceAutomaton signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right))
                    right) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | sequence_left _ _ _ _ hChild => exact hClassified.1 _ _ hChild
          | sequence_right _ _ _ _ hChild => exact hClassified.2 _ _ hChild
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound elseType ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : elseType.SameCycleMessageLinear ∧
              PactType.SameCycleMessageLinearBranches branches := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : elseType.InterfaceScoped ∧
              PactType.InterfaceScopedBranches branches := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hElseIH := ih (sizeOf elseType) hElseSize bound name elseType
            rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hElseSize))
          have hBranchIH : ∀ (action : BareMessage) (branchType : PactType)
              (index : Nat), branches[index]? = some (action, branchType) →
              ∀ q r, TypeCompilationRelation branchType q r →
                (MarkerReachable (sequenceExecutionFragment
                  (compileTypeFuel signature (typeCompilationFuel branchType)
                    branchType)) name q ↔
                    PactType.markerReachableSubst name r = true) := by
            intro action branchType index hEntry q r hr
            have hMember : (action, branchType) ∈ branches := by
              rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBoundIndex,
                hValue⟩
              have hAt := List.getElem_mem hBoundIndex
              simpa [hValue] using hAt
            have hBranchSize : sizeOf branchType < n := by
              rw [← hSize]
              exact (branch_sizeOf_lt elseType branches
                (action, branchType) hMember).1
            exact ih (sizeOf branchType) hBranchSize bound name branchType rfl
              hName
              (by
                intro m hm
                have hEntryTail := hAllTail m hm
                simp only [PactType.TailOccurrences] at hEntryTail
                exact tailOccurrences_branch_of_mem m True branches
                  hEntryTail.2 (action, branchType) hMember)
              hSignature
              (supports_branch_of_mem signature branches (action, branchType)
                hSupportFields.2 hMember)
              (allVariablesBound_branch_of_mem bound branches
                (action, branchType) hBoundFields.2 hMember)
              (binderHygienic_branch_of_mem bound branches
                (action, branchType) hHygienicFields.2 hMember)
              (clockGuarded_branch_of_mem branches (action, branchType)
                hGuardedFields.2 hMember)
              (tailRecursive_branch_of_mem branches (action, branchType)
                hTailFields.2 hMember)
              (sameCycleMessageLinear_branch_of_mem branches
                (action, branchType) hLinearFields.2 hMember)
              (interfaceScoped_branch_of_mem branches (action, branchType)
                hScopedFields.2 hMember)
              (fun child hChildSize => hClosedBundle child
                (lt_trans hChildSize hBranchSize)) q r hr
          have hClassified :=
            buildExclusiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
              signature elseType branches name hSupports hElseIH hBranchIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.xoffer elseType branches))
                (.xoffer elseType branches) =
              buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature
                  (max (typeCompilationFuel elseType)
                    (typeBranchCompilationFuel branches)) elseType)
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature
                    (max (typeCompilationFuel elseType)
                      (typeBranchCompilationFuel branches)) branch.2)) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | xoffer_source => exact hClassified.1
          | xoffer_else _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | xoffer_branch _ branchType _ _ action index _ hEntry hChild =>
              exact hClassified.2.2 action branchType index hEntry _ _ hChild
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hSupportFields : signature.Supports elseType ∧
              signature.SupportsBranches branches := by
            simpa only [TypeAlphabet.Supports] using hSupports
          have hBoundFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hHygienicFields : PactType.BinderHygienic bound elseType ∧
              PactType.BinderHygienicBranches bound branches := by
            simpa only [PactType.BinderHygienic] using hHygienic
          have hGuardedFields : elseType.ClockGuarded ∧
              PactType.ClockGuardedBranches branches := by
            simpa only [PactType.ClockGuarded] using hGuarded
          have hTailFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hTail
          have hLinearFields : elseType.SameCycleMessageLinear ∧
              PactType.SameCycleMessageLinearBranches branches := by
            simpa only [PactType.SameCycleMessageLinear] using hLinear
          have hScopedFields : elseType.InterfaceScoped ∧
              PactType.InterfaceScopedBranches branches := by
            simpa only [PactType.InterfaceScoped] using hScoped
          have hTailNameFields : elseType.TailOccurrences name True ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTailName
          have hElseIH := ih (sizeOf elseType) hElseSize bound name elseType
            rfl hName
            (by
              intro m hm
              have hEntry := hAllTail m hm
              simp only [PactType.TailOccurrences] at hEntry
              exact hEntry.1)
            hSignature hSupportFields.1 hBoundFields.1 hHygienicFields.1
            hGuardedFields.1 hTailFields.1 hLinearFields.1 hScopedFields.1
            (fun child hChildSize => hClosedBundle child
              (lt_trans hChildSize hElseSize))
          have hClassified :=
            buildSelectedConjunctiveOfferAutomaton_sequenceExecutionMarkerReachable_classified
              signature elseType branches name hSupports hTailNameFields.2
                hElseIH
          simp only at hClassified
          have hFragment : compileTypeFuel signature
              (typeCompilationFuel (.offer elseType branches))
                (.offer elseType branches) =
              buildSelectedConjunctiveOfferAutomaton signature branches
                (compileTypeFuel signature
                  (max (typeCompilationFuel elseType)
                    (conjunctiveCompilationFuel branches)) elseType)
                (branches.map fun selected =>
                  (selected.1, compileTypeFuel signature
                    (max (typeCompilationFuel elseType)
                      (conjunctiveCompilationFuel branches))
                      (parallelTypeBranchesSelecting selected branches))) := by
            simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          rw [hFragment]
          cases hRelated with
          | offer_source => exact hClassified.1
          | offer_else _ _ _ _ hChild => exact hClassified.2.1 _ _ hChild
          | offer_branches _ _ _ selected index _ hEntry hChild =>
              exact hClassified.2.2 selected index hEntry _ _ hChild
end

end Pact
