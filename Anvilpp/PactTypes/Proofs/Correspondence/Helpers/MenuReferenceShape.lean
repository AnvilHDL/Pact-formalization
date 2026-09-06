import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.FutureFieldShape

namespace Pact

noncomputable section

open Classical

private def EndpointMenuReferences (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ reference removed,
    edge.future = .at reference removed →
      edge.label.semantic ≠ .tock ∧ (reference = edge.source ∨ reference = edge.target)

private theorem endpointMenuReferences_child (index : Nat) (fragment : AutomatonFragment)
    (hFragment : EndpointMenuReferences fragment) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ childPendingEdges index fragment)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) :
    edge.label.semantic ≠ .tock ∧ (reference = edge.source ∨ reference = edge.target) := by
  obtain ⟨child, hChild, rfl⟩ := Finset.mem_image.mp hEdge
  cases hSpec : child.future with
  | explicit offers | atUnion offers target mask =>
    simp [childPendingEdge, hSpec, childFutureSpec] at hField
  | «at» target mask =>
    simp only [childPendingEdge, hSpec, childFutureSpec, FutureSpec.at.injEq] at hField
    obtain ⟨rfl, rfl⟩ := hField
    obtain ⟨hClock, hSource | hTarget⟩ := hFragment child hChild target mask hSpec
    · exact ⟨hClock, Or.inl (congrArg (childState index) hSource)⟩
    · exact ⟨hClock, Or.inr (congrArg (childState index) hTarget)⟩

private theorem endpointMenuReferences_indexed
    (fragments : List (BareMessage × AutomatonFragment))
    (hFragments : ∀ entry ∈ fragments, EndpointMenuReferences entry.2)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ indexedFragmentEdges fragments)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) :
    edge.label.semantic ≠ .tock ∧ (reference = edge.source ∨ reference = edge.target) := by
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨entry, hEntry, hChild⟩
  · simp at hEmpty
  · have hMember : entry.1 ∈ fragments := by
      obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hEntry
      simp [hValue, List.getElem_mem hBound]
    exact endpointMenuReferences_child (entry.2 + 1) entry.1.2
      (hFragments entry.1 hMember) edge hChild reference removed hField

private theorem compileTypeFuel_endpointMenuReferences :
    ∀ fuel ty, EndpointMenuReferences (compileTypeFuel fuel ty) := by
  intro fuel
  induction fuel with
  | zero => intro ty edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty edge hEdge reference removed hField
    cases ty with
    | skip a | var a name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
    | message a msg dir =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, _, rfl⟩ | ⟨env, _, rfl⟩) | ⟨env, _, rfl⟩ <;>
        simp_all [AutomatonConstructionLabel.semantic, TypeLabel.message, TypeLabel.silent]
    | progress a pid =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩ <;>
        simp_all [AutomatonConstructionLabel.semantic, TypeLabel.progress, TypeLabel.silent]
    | tock a =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩
      · split at hField <;> simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
    | choice a left right | fairChoice a bid left right =>
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeft | hRight) | hRoot
      · exact endpointMenuReferences_child 0 _ (ih left) edge hLeft reference removed hField
      · exact endpointMenuReferences_child 1 _ (ih right) edge hRight reference removed hField
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;>
          simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent, TypeLabel.fair]
    | recur a name body =>
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨child, hChild, rfl⟩
      · simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · by_cases hMarker : child.label = .variable name
        · simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        · simp only [if_neg hMarker] at hField ⊢
          exact endpointMenuReferences_child 0 _ (ih body) (childPendingEdge 0 child)
            (Finset.mem_image.mpr ⟨child, hChild, rfl⟩) reference removed hField
    | seq a left right =>
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with (hLeft | hRight) | hRedirect
      · simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeft
        obtain ⟨child, _, rfl⟩ := hLeft
        simp only [sequenceKeptLeftEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
      · exact endpointMenuReferences_child 1 _ (ih right) edge hRight reference removed hField
      · simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, _, rfl⟩ := hRedirect
        simp only [sequenceRedirectEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
    | par a left right interface =>
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
      · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRaw
        obtain ⟨le, _, re, _, rfl⟩ := hRaw
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hLC
        obtain ⟨q, _, re, _, env, _, rfl⟩ := hLC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRC
        obtain ⟨q, _, le, _, env, _, rfl⟩ := hRC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hLS
        obtain ⟨e, _, rfl⟩ := hLS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hRS
        obtain ⟨e, _, rfl⟩ := hRS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hLD
        obtain ⟨e, _, rfl⟩ := hLD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hRD
        obtain ⟨e, _, rfl⟩ := hRD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
        obtain ⟨env, _, rfl⟩ := hDone
        simp at hField
    | xoffer a other branches | offer a other branches =>
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union] at hEdge
      rcases hEdge with (((hElse | hIndexed) | hBranch) | hWait) | hDefault
      · exact endpointMenuReferences_child 0 _ (ih other) edge hElse reference removed hField
      · apply endpointMenuReferences_indexed _ ?_ edge hIndexed reference removed hField
        intro entry hEntry
        obtain ⟨branch, _, rfl⟩ := List.mem_map.mp hEntry
        exact ih _
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hNew
          simp_all [AutomatonConstructionLabel.semantic, TypeLabel.message, TypeLabel.silent]
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
        simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        simp_all [AutomatonConstructionLabel.semantic, TypeLabel.silent]

/-- Plain menu fields read their source or target; sequence entry reads use `.atUnion`. -/
theorem compileTypeFuel_at_endpoint
    (fuel : Nat) (ty : PactType) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel fuel ty).edges)
    (reference : TypeAutomatonState) (removed : Finset BareMessage)
    (hField : edge.future = .at reference removed) :
    edge.label.semantic ≠ .tock ∧ (reference = edge.source ∨ reference = edge.target) :=
  compileTypeFuel_endpointMenuReferences fuel ty edge hEdge reference removed hField

private def TargetMenuRemoval (accepting : Finset TypeAutomatonState)
    (edge : PendingAutomatonEdge) : Prop :=
  ∀ removed, edge.future = .at edge.target removed →
    removed = edge.current ∨ edge.target ∈ accepting

private theorem targetMenuRemoval_child (index : Nat) (edge : PendingAutomatonEdge)
    {accepting parent : Finset TypeAutomatonState}
    (hSubset : accepting.image (childState index) ⊆ parent)
    (h : TargetMenuRemoval accepting edge) :
    TargetMenuRemoval parent (childPendingEdge index edge) := by
  intro removed hField
  obtain ⟨inner, hInner, hTarget⟩ :=
    childFutureSpec_at index edge.future (childState index edge.target) removed hField
  have hEq : edge.target = inner := by
    simpa only [childState, TypeAutomatonState.child.injEq, true_and] using hTarget
  subst inner
  rcases h removed hInner with hRemoved | hAccept
  · exact Or.inl hRemoved
  · exact Or.inr (hSubset (Finset.mem_image_of_mem _ hAccept))

private theorem targetMenuRemoval_childEdges (index : Nat) (fragment : AutomatonFragment)
    {parent : Finset TypeAutomatonState}
    (hSubset : childAccepting index fragment ⊆ parent)
    (h : ∀ edge ∈ fragment.edges, TargetMenuRemoval fragment.accepting edge)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ childPendingEdges index fragment) :
    TargetMenuRemoval parent edge := by
  obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hEdge
  exact targetMenuRemoval_child index inner hSubset (h inner hInner)

private theorem targetMenuRemoval_indexed (fragments : List (BareMessage × AutomatonFragment))
    {parent : Finset TypeAutomatonState}
    (hSubset : indexedFragmentAccepting fragments ⊆ parent)
    (h : ∀ entry ∈ fragments, ∀ edge ∈ entry.2.edges, TargetMenuRemoval entry.2.accepting edge)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ indexedFragmentEdges fragments) :
    TargetMenuRemoval parent edge := by
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨entry, hEntry, hChild⟩
  · simp at hEmpty
  · have hMem : entry.1 ∈ fragments := by
      have := List.mem_map_of_mem (f := Prod.fst) hEntry
      simpa using this
    apply targetMenuRemoval_childEdges _ entry.1.2 ?_ (h entry.1 hMem) edge hChild
    intro q hq
    apply hSubset
    rw [indexedFragmentAccepting, mem_foldl_union_iff]
    exact Or.inr ⟨entry, hEntry, hq⟩

private theorem compileTypeFuel_targetMenuRemoval :
    ∀ fuel ty edge, edge ∈ (compileTypeFuel fuel ty).edges →
      TargetMenuRemoval (compileTypeFuel fuel ty).accepting edge := by
  intro fuel
  induction fuel with
  | zero => intro ty edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty edge hEdge
    cases ty with
    | skip a | var a name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, _, rfl⟩ := hEdge
      simp [TargetMenuRemoval, compileTypeFuel, finishAutomatonFragment]
    | message a msg dir =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, _, rfl⟩ | ⟨env, _, rfl⟩) | ⟨env, _, rfl⟩ <;>
        simp [TargetMenuRemoval, compileTypeFuel, finishAutomatonFragment]
    | tock a =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩
      · cases hClock : env.clock <;> simp [TargetMenuRemoval]
      · simp [TargetMenuRemoval]
    | progress a pid =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, _, rfl⟩ | ⟨env, _, rfl⟩ <;>
        simp [TargetMenuRemoval]
    | choice a left right | fairChoice a bid left right =>
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment]
      rcases hEdge with (hLeft | hRight) | hRoot
      · exact targetMenuRemoval_childEdges 0 _ Finset.subset_union_left (ih left) edge hLeft
      · exact targetMenuRemoval_childEdges 1 _ Finset.subset_union_right (ih right) edge hRight
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, _, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;> simp [TargetMenuRemoval, childState]
    | recur a name body =>
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment]
      rcases hEdge with hRoot | hBody
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hRoot
        simp [TargetMenuRemoval]
      · obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hBody
        by_cases hMarker : inner.label = .variable name
        · simp [TargetMenuRemoval, hMarker]
        · simp only [hMarker, if_false]
          exact targetMenuRemoval_child 0 inner (by intro q hq; exact hq) (ih body inner hInner)
    | seq a left right =>
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment]
      rcases hEdge with (hLeft | hRight) | hRedirect
      · simp only [sequenceLeftEdges, Finset.mem_image, Finset.mem_filter] at hLeft
        obtain ⟨child, _, rfl⟩ := hLeft
        intro removed hField
        simp only [sequenceKeptLeftEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
      · exact targetMenuRemoval_childEdges 1 _ (by intro q hq; exact hq) (ih right) edge hRight
      · simp only [sequenceRedirectEdges, Finset.mem_image, Finset.mem_filter] at hRedirect
        obtain ⟨child, _, rfl⟩ := hRedirect
        intro removed hField
        simp only [sequenceRedirectEdge, sequenceLeftFutureSpec] at hField
        split_ifs at hField
    | par a left right interface =>
      intro removed hField
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
      · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRaw
        obtain ⟨le, _, re, _, rfl⟩ := hRaw
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hLC
        obtain ⟨q, _, re, _, env, _, rfl⟩ := hLC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_image] at hRC
        obtain ⟨q, _, le, _, env, _, rfl⟩ := hRC
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hLS
        obtain ⟨e, _, rfl⟩ := hLS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter, Finset.mem_image] at hRS
        obtain ⟨e, _, rfl⟩ := hRS
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hLD
        obtain ⟨e, _, rfl⟩ := hLD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter, Finset.mem_image] at hRD
        obtain ⟨e, _, rfl⟩ := hRD
        simp only [parallelFutureSpec] at hField
        split_ifs at hField
      · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
        obtain ⟨env, _, rfl⟩ := hDone
        simp at hField
    | xoffer a other branches | offer a other branches =>
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
        buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
        buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
      rcases hEdge with (((hElse | hIndexed) | hBranch) | hWait) | hDefault
      · exact targetMenuRemoval_childEdges 0 _ Finset.subset_union_left (ih other) edge hElse
      · refine targetMenuRemoval_indexed _ Finset.subset_union_right ?_ edge hIndexed
        intro entry hEntry
        obtain ⟨branch, _, rfl⟩ := List.mem_map.mp hEntry
        exact ih _
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, _, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hNew
          simp [TargetMenuRemoval, childState]
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
        simp [TargetMenuRemoval]
      · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hDefault
        simp [TargetMenuRemoval, childState]

/-- Target reads remove the current offer, except when the target is accepting. -/
theorem compileTypeFuel_at_target_removal
    (fuel : Nat) (ty : PactType) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (compileTypeFuel fuel ty).edges) (removed : Finset BareMessage)
    (hField : edge.future = .at edge.target removed) :
    removed = edge.current ∨ edge.target ∈ (compileTypeFuel fuel ty).accepting :=
  compileTypeFuel_targetMenuRemoval fuel ty edge hEdge removed hField

end

end Pact
