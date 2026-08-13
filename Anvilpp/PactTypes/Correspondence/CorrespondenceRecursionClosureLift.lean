import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionClosureCore

/-!
# Completing-back-closure lifting lemmas
-/

namespace Pact

noncomputable section


theorem completingBackClosure_lift_taggedChild
    (parent child : AutomatonFragment) (index : Nat)
    (name : String) (value : Bool)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges, childEdge.source = state ∧
          edge = childPendingEdge index childEdge)
    (hCompleting : ∀ state,
      childState index state ∈ parent.completing ↔
        state ∈ child.completing)
    {state : TypeAutomatonState}
    (hMember : state ∈ completingBackClosure child
      ((if value then
          (child.edges.filter fun edge => edge.label = .variable name).image
            fun edge => edge.source
        else ∅) ∪ child.completing)) :
    childState index state ∈ completingBackClosure parent
      ((if value then
          (parent.edges.filter fun edge => edge.label = .variable name).image
            fun edge => edge.source
        else ∅) ∪ parent.completing) := by
  classical
  let childSeed :=
    (if value then
        (child.edges.filter fun edge => edge.label = .variable name).image
          fun edge => edge.source
      else ∅) ∪ child.completing
  let parentSeed :=
    (if value then
        (parent.edges.filter fun edge => edge.label = .variable name).image
          fun edge => edge.source
      else ∅) ∪ parent.completing
  have hTagged : childState index state ∈ completingBackClosure
      (taggedFragment index child) (childSeed.image (childState index)) := by
    rw [completingBackClosure_taggedFragment_image]
    exact Finset.mem_image.mpr ⟨state, hMember, rfl⟩
  have hEdges : ∀ source label target,
      (∃ edge ∈ (taggedFragment index child).edges,
        edge.source = source ∧ edge.label = label ∧ edge.target = target) →
      ∃ edge ∈ parent.edges,
        edge.source = source ∧ edge.label = label ∧ edge.target = target := by
    rintro source label target ⟨edge, hEdge, hSource, hLabel, hTarget⟩
    simp only [taggedFragment, Finset.mem_image] at hEdge
    obtain ⟨childEdge, hChildEdge, rfl⟩ := hEdge
    have hParentEdge := (hOutgoing childEdge.source
      (childPendingEdge index childEdge)).mpr
        ⟨childEdge, hChildEdge, rfl, rfl⟩
    exact ⟨childPendingEdge index childEdge, hParentEdge.1,
      hSource, hLabel, hTarget⟩
  have hLifted := completingBackClosure_mono_edges
    (taggedFragment index child) parent hEdges _ hTagged
  apply completingBackClosure_mono parent (seed1 := childSeed.image
    (childState index)) (seed2 := parentSeed) _ hLifted
  intro tagged hTaggedSeed
  rcases Finset.mem_image.mp hTaggedSeed with ⟨source, hSourceSeed, rfl⟩
  rcases Finset.mem_union.mp hSourceSeed with hVariable | hChildCompleting
  · apply Finset.mem_union_left
    by_cases hValue : value
    · simp only [childSeed, parentSeed, hValue, if_true] at hVariable ⊢
      simp only [Finset.mem_image, Finset.mem_filter] at hVariable ⊢
      obtain ⟨childEdge, ⟨hChildEdge, hLabel⟩, hSource⟩ := hVariable
      let parentEdge := childPendingEdge index childEdge
      have hParentEdge := (hOutgoing childEdge.source parentEdge).mpr
        ⟨childEdge, hChildEdge, rfl, rfl⟩
      refine ⟨parentEdge, ⟨hParentEdge.1, ?_⟩, ?_⟩
      · simpa [parentEdge, childPendingEdge] using hLabel
      · simp [parentEdge, childPendingEdge, ← hSource]
    · simp [childSeed, hValue] at hVariable
  · exact Finset.mem_union_right _
      ((hCompleting source).mpr hChildCompleting)

/- Soundness of the scalar completion seed, with no recursion fixed-point
gate: a state reached backwards from a live variable marker or an ordinary
completing state represents a residual that completes under that scalar
interpretation.  This is used only to show that an unrelated inner-binder
marker cannot occur on an outer-binder closure path. -/
theorem parametricCompletingBackClosure_sound
    (signature : TypeAlphabet) (name : String) (value : Bool)
    (processType : PactType)
    (hTailOccurrences : processType.TailOccurrences name True)
    (hTailRecursive : processType.TailRecursive)
    (hHygienic : processType.BinderHygienic [name])
    (state : TypeAutomatonState)
    (hMember : state ∈ completingBackClosure
      (compileTypeFuel signature (typeCompilationFuel processType) processType)
      ((if value then
          ((compileTypeFuel signature (typeCompilationFuel processType)
              processType).edges.filter
            fun edge => edge.label = .variable name).image
              fun edge => edge.source
        else ∅) ∪
        (compileTypeFuel signature (typeCompilationFuel processType)
          processType).completing)) :
    ∃ residual, TypeCompilationRelation processType state residual ∧
      PactType.canCompleteBeforeTockSubst name value residual = true := by
  classical
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let seed :=
    (if value then
        (fragment.edges.filter fun edge => edge.label = .variable name).image
          fun edge => edge.source
      else ∅) ∪ fragment.completing
  let allowed := ((fragment.edges.image fun edge => edge.source) ∪
      fragment.completing).filter fun q =>
        ∃ residual, TypeCompilationRelation processType q residual ∧
          PactType.canCompleteBeforeTockSubst name value residual = true
  have hAllowed := completingBackClosure_subset_of_predecessor_closed fragment
    seed allowed ?_ ?_ (by simpa [fragment, seed] using hMember)
  · exact (Finset.mem_filter.mp hAllowed).2
  · intro q hSeed
    rcases Finset.mem_union.mp hSeed with hVariable | hCompleting
    · by_cases hValue : value
      · simp only [seed, hValue, if_true, Finset.mem_image,
          Finset.mem_filter] at hVariable
        obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVariable
        have hRelated := (compileTypeFuel_variableEdge_source_var signature name
          (typeCompilationFuel processType) processType True
          (typeCompilationFuel_sufficient processType) hTailOccurrences edge
            (by simpa [fragment] using hEdge) hLabel).2
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨edge, by simpa [fragment] using hEdge, hSource⟩),
            .var name, ?_, ?_⟩
        · rw [← hSource]
          exact hRelated
        · simp [PactType.canCompleteBeforeTockSubst, hValue]
      · simp [seed, hValue] at hVariable
    · obtain ⟨residual, hRelated, hPlain⟩ :=
        compiledFragmentCompleting_represented signature [name]
          (typeCompilationFuel processType) processType
          (typeCompilationFuel_sufficient processType) hTailRecursive
            hHygienic q (by simpa [fragment] using hCompleting)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ (by simpa [fragment] using hCompleting),
          residual, hRelated,
          PactType.canCompleteBeforeTock_le_subst name value residual hPlain⟩
  · intro edge hEdge hNonClock hTarget
    obtain ⟨targetResidual, hTargetRelated, hTargetComplete⟩ :=
      (Finset.mem_filter.mp hTarget).2
    obtain ⟨sourceResidual, hSourceRelated, hSourceComplete⟩ :=
      compiledFragmentNonClockPredecessor_subst signature name value
        (typeCompilationFuel processType) processType
        (typeCompilationFuel_sufficient processType) hTailRecursive hHygienic
          edge (by simpa [fragment] using hEdge) hNonClock targetResidual
            hTargetRelated hTargetComplete
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨edge, by simpa [fragment] using hEdge, rfl⟩),
        sourceResidual, hSourceRelated, hSourceComplete⟩

/- Lift an outer-variable closure through a distinct recursion binder.  A raw
marker for the inner binder is not copied unchanged by the builder, so the
caller supplies the semantic fact that no such source belongs to this outer
closure. -/
theorem completingBackClosure_lift_recursion_nonmatching
    (signature : TypeAlphabet) (outer binder : String) (value : Bool)
    (child : AutomatonFragment) (hDistinct : outer ≠ binder)
    (hNoInnerSource : ∀ edge ∈ child.edges,
      edge.label = .variable binder →
      edge.source ∉ completingBackClosure child
        ((if value then
            (child.edges.filter fun e => e.label = .variable outer).image
              fun e => e.source
          else ∅) ∪ child.completing))
    {state : TypeAutomatonState}
    (hMember : state ∈ completingBackClosure child
      ((if value then
          (child.edges.filter fun edge => edge.label = .variable outer).image
            fun edge => edge.source
        else ∅) ∪ child.completing)) :
    childState 0 state ∈ completingBackClosure
      (buildRecursionAutomaton signature binder child)
      ((if value then
          ((buildRecursionAutomaton signature binder child).edges.filter
            fun edge => edge.label = .variable outer).image
              fun edge => edge.source
        else ∅) ∪
        (buildRecursionAutomaton signature binder child).completing) := by
  classical
  let parent := buildRecursionAutomaton signature binder child
  let childSeed :=
    (if value then
        (child.edges.filter fun edge => edge.label = .variable outer).image
          fun edge => edge.source
      else ∅) ∪ child.completing
  let parentSeed :=
    (if value then
        (parent.edges.filter fun edge => edge.label = .variable outer).image
          fun edge => edge.source
      else ∅) ∪ parent.completing
  let childClosure := completingBackClosure child childSeed
  let parentClosure := completingBackClosure parent parentSeed
  let allowed := childClosure.filter fun q => childState 0 q ∈ parentClosure
  have hCompleting : ∀ q ∈ child.completing,
      childState 0 q ∈ parent.completing := by
    intro q hQ
    simp only [parent]
    rw [buildRecursionAutomaton_completing_eq signature binder child]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨q, completingBackClosure_superset_seed child _ ?_, rfl⟩
    exact Finset.mem_union_right _ hQ
  have hAllowed : childClosure ⊆ allowed := by
    apply completingBackClosure_subset_of_predecessor_closed child childSeed
      allowed
    · intro q hSeed
      refine Finset.mem_filter.mpr
        ⟨completingBackClosure_superset_seed child childSeed hSeed, ?_⟩
      rcases Finset.mem_union.mp hSeed with hVariable | hChildCompleting
      · by_cases hValue : value
        · simp only [childSeed, hValue, if_true, Finset.mem_image,
            Finset.mem_filter] at hVariable
          obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVariable
          have hNotInner : edge.label ≠ .variable binder := by
            rw [hLabel]
            intro hEq
            injection hEq with hNames
            exact hDistinct hNames
          let parentEdge := childPendingEdge 0 edge
          have hParentEdge : parentEdge ∈ parent.edges := by
            simp only [parent, buildRecursionAutomaton,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            right
            exact ⟨edge, hEdge, by
              simp [parentEdge, childPendingEdge, hNotInner]⟩
          apply completingBackClosure_superset_seed parent parentSeed
          apply Finset.mem_union_left
          simp only [parentSeed, hValue, if_true, Finset.mem_image,
            Finset.mem_filter]
          refine ⟨parentEdge, ⟨hParentEdge, ?_⟩, ?_⟩
          · simpa [parentEdge, childPendingEdge] using hLabel
          · simp [parentEdge, childPendingEdge, ← hSource]
        · simp [childSeed, hValue] at hVariable
      · apply completingBackClosure_superset_seed parent parentSeed
        exact Finset.mem_union_right _
          (hCompleting q hChildCompleting)
    · intro edge hEdge hNonClock hTargetAllowed
      have hTargetFields := Finset.mem_filter.mp hTargetAllowed
      have hSourceChild : edge.source ∈ childClosure :=
        completingBackClosure_mem_of_nonClockEdge child childSeed edge hEdge
          hNonClock hTargetFields.1
      by_cases hInner : edge.label = .variable binder
      · exact absurd hSourceChild (hNoInnerSource edge hEdge hInner)
      · let parentEdge := childPendingEdge 0 edge
        have hParentEdge : parentEdge ∈ parent.edges := by
          simp only [parent, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          right
          exact ⟨edge, hEdge, by
            simp [parentEdge, childPendingEdge, hInner]⟩
        have hSourceParent : childState 0 edge.source ∈ parentClosure :=
          completingBackClosure_mem_of_nonClockEdge parent parentSeed
            parentEdge hParentEdge (by
              simpa [parentEdge, childPendingEdge] using hNonClock) (by
                simpa [parentEdge, childPendingEdge] using hTargetFields.2)
        exact Finset.mem_filter.mpr ⟨hSourceChild, hSourceParent⟩
  exact (Finset.mem_filter.mp (hAllowed (by
    simpa [childClosure, childSeed] using hMember))).2

/- Lift a closure seeded by the inner binder's own live markers.  The caller
has already established that the tagged body entry is in the enclosing
closure; every matching marker is therefore an installed non-clock backedge
into that entry. -/
theorem completingBackClosure_lift_recursion_matching
    (signature : TypeAlphabet) (outer binder : String) (value : Bool)
    (child : AutomatonFragment)
    (hInitial : childState 0 child.initial ∈ completingBackClosure
      (buildRecursionAutomaton signature binder child)
      ((if value then
          ((buildRecursionAutomaton signature binder child).edges.filter
            fun edge => edge.label = .variable outer).image
              (fun edge => edge.source)
        else ∅) ∪
        (buildRecursionAutomaton signature binder child).completing))
    {state : TypeAutomatonState}
    (hMember : state ∈ completingBackClosure child
      ((child.edges.filter fun edge => edge.label = .variable binder).image
          (fun edge => edge.source) ∪ child.completing)) :
    childState 0 state ∈ completingBackClosure
      (buildRecursionAutomaton signature binder child)
      ((if value then
          ((buildRecursionAutomaton signature binder child).edges.filter
            fun edge => edge.label = .variable outer).image
              (fun edge => edge.source)
        else ∅) ∪
        (buildRecursionAutomaton signature binder child).completing) := by
  classical
  let parent := buildRecursionAutomaton signature binder child
  let childSeed :=
    (child.edges.filter fun edge => edge.label = .variable binder).image
      (fun edge => edge.source) ∪ child.completing
  let parentSeed :=
    (if value then
        (parent.edges.filter fun edge => edge.label = .variable outer).image
          (fun edge => edge.source)
      else ∅) ∪ parent.completing
  let childClosure := completingBackClosure child childSeed
  let parentClosure := completingBackClosure parent parentSeed
  let allowed := childClosure.filter fun q => childState 0 q ∈ parentClosure
  have hEntry : childState 0 child.initial ∈ parentClosure := by
    simpa [parentClosure, parent, parentSeed] using hInitial
  have hCompleting : ∀ q ∈ child.completing,
      childState 0 q ∈ parent.completing := by
    intro q hQ
    simp only [parent]
    rw [buildRecursionAutomaton_completing_eq signature binder child]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨q, completingBackClosure_superset_seed child _ ?_, rfl⟩
    exact Finset.mem_union_right _ hQ
  have installedPredecessor : ∀ edge ∈ child.edges,
      edge.label = .variable binder →
      childState 0 edge.source ∈ parentClosure := by
    intro edge hEdge hLabel
    let backedge : PendingAutomatonEdge :=
      { source := childState 0 edge.source
        environment := edge.environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 child.initial) ∅
        target := childState 0 child.initial }
    have hBackedge : backedge ∈ parent.edges := by
      simp only [parent, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image]
      right
      exact ⟨edge, hEdge, by simp [backedge, hLabel]⟩
    exact completingBackClosure_mem_of_nonClockEdge parent parentSeed backedge
      hBackedge (by
        intro hEq
        cases hEq)
      (by simpa [backedge] using hEntry)
  have hAllowed : childClosure ⊆ allowed := by
    apply completingBackClosure_subset_of_predecessor_closed child childSeed
      allowed
    · intro q hSeed
      refine Finset.mem_filter.mpr
        ⟨completingBackClosure_superset_seed child childSeed hSeed, ?_⟩
      rcases Finset.mem_union.mp hSeed with hVariable | hChildCompleting
      · simp only [childSeed, Finset.mem_image, Finset.mem_filter] at hVariable
        obtain ⟨edge, ⟨hEdge, hLabel⟩, hSource⟩ := hVariable
        rw [← hSource]
        exact installedPredecessor edge hEdge hLabel
      · apply completingBackClosure_superset_seed parent parentSeed
        exact Finset.mem_union_right _
          (hCompleting q hChildCompleting)
    · intro edge hEdge hNonClock hTargetAllowed
      have hTargetFields := Finset.mem_filter.mp hTargetAllowed
      have hSourceChild : edge.source ∈ childClosure :=
        completingBackClosure_mem_of_nonClockEdge child childSeed edge hEdge
          hNonClock hTargetFields.1
      by_cases hInner : edge.label = .variable binder
      · exact Finset.mem_filter.mpr
          ⟨hSourceChild, installedPredecessor edge hEdge hInner⟩
      · let parentEdge := childPendingEdge 0 edge
        have hParentEdge : parentEdge ∈ parent.edges := by
          simp only [parent, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          right
          exact ⟨edge, hEdge, by
            simp [parentEdge, childPendingEdge, hInner]⟩
        have hSourceParent : childState 0 edge.source ∈ parentClosure :=
          completingBackClosure_mem_of_nonClockEdge parent parentSeed
            parentEdge hParentEdge (by
              simpa [parentEdge, childPendingEdge] using hNonClock) (by
                simpa [parentEdge, childPendingEdge] using hTargetFields.2)
        exact Finset.mem_filter.mpr ⟨hSourceChild, hSourceParent⟩
  exact (Finset.mem_filter.mp (hAllowed (by
    simpa [childClosure, childSeed] using hMember))).2

theorem branchCanCompleteBeforeTockSubst_eq_of_tailOccurrences_false
    (name : String) (value : Bool) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailBranchOccurrences name False branches →
        PactType.branchCanCompleteBeforeTockSubst name value branches =
          PactType.BranchCanCompleteBeforeTock branches := by
  intro branches hTail
  induction branches with
  | nil =>
      simp [PactType.branchCanCompleteBeforeTockSubst,
        PactType.BranchCanCompleteBeforeTock]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.TailBranchOccurrences] at hTail
      simp only [PactType.branchCanCompleteBeforeTockSubst,
        PactType.BranchCanCompleteBeforeTock,
        PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
          name value branchType hTail.1,
        ih hTail.2]

theorem branchCanCompleteBeforeTockSubst_eq_true_iff
    (name : String) (value : Bool) :
    ∀ branches : List (BareMessage × PactType),
      PactType.branchCanCompleteBeforeTockSubst name value branches = true ↔
        ∃ branch ∈ branches,
          PactType.canCompleteBeforeTockSubst name value branch.2 = true := by
  intro branches
  induction branches with
  | nil =>
      simp [PactType.branchCanCompleteBeforeTockSubst]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      unfold PactType.branchCanCompleteBeforeTockSubst
      rw [Bool.or_eq_true, ih]
      constructor
      · rintro (hHead | ⟨entry, hEntry, hComplete⟩)
        · exact ⟨(action, branchType), List.mem_cons_self, hHead⟩
        · exact ⟨entry,
            List.mem_cons_of_mem (action, branchType) hEntry, hComplete⟩
      · rintro ⟨entry, hEntry, hComplete⟩
        rcases List.mem_cons.mp hEntry with rfl | hRest
        · exact Or.inl hComplete
        · exact Or.inr ⟨entry, hRest, hComplete⟩

theorem exists_getElem?_eq_some_of_mem
    {Element : Type} {element : Element} {items : List Element}
    (hMember : element ∈ items) :
    ∃ index : Nat, items[index]? = some element := by
  rcases List.mem_iff_getElem.mp hMember with ⟨index, hBound, hValue⟩
  refine ⟨index, ?_⟩
  rw [List.getElem?_eq_getElem hBound, hValue]

end

end Pact
