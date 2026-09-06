import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Base

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

private def FutureRemoval (accepting : Finset TypeAutomatonState)
    (edge : PendingAutomatonEdge) : Prop :=
  ∀ q removed, edge.future = .at q removed →
    (removed = edge.current ∨ q ∈ accepting) ∧ edge.label.semantic ≠ TypeLabel.tock

private theorem child_futureRemoval (index : Nat) (edge : PendingAutomatonEdge)
    {accepting parent : Finset TypeAutomatonState}
    (hSubset : accepting.image (childState index) ⊆ parent)
    (h : FutureRemoval accepting edge) : FutureRemoval parent (childPendingEdge index edge) := by
  intro q removed hFuture
  obtain ⟨inner, hInner, rfl⟩ := childFutureSpec_at index edge.future q removed hFuture
  obtain ⟨hRemoved | hAccept, hClock⟩ := h inner removed hInner
  · exact ⟨Or.inl hRemoved, hClock⟩
  · exact ⟨Or.inr (hSubset (Finset.mem_image_of_mem _ hAccept)), hClock⟩

private theorem childEdges_futureRemoval (index : Nat) (fragment : AutomatonFragment)
    {parent : Finset TypeAutomatonState}
    (hSubset : childAccepting index fragment ⊆ parent)
    (h : ∀ edge ∈ fragment.edges, FutureRemoval fragment.accepting edge)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ childPendingEdges index fragment) :
    FutureRemoval parent edge := by
  obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hEdge
  exact child_futureRemoval index inner hSubset (h inner hInner)

private theorem indexedEdges_futureRemoval (fragments : List (BareMessage × AutomatonFragment))
    {parent : Finset TypeAutomatonState}
    (hSubset : indexedFragmentAccepting fragments ⊆ parent)
    (h : ∀ entry ∈ fragments, ∀ edge ∈ entry.2.edges, FutureRemoval entry.2.accepting edge)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ indexedFragmentEdges fragments) :
    FutureRemoval parent edge := by
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨entry, hEntry, hChild⟩
  · simp at hEmpty
  · have hMem : entry.1 ∈ fragments := by
      have := List.mem_map_of_mem (f := Prod.fst) hEntry
      simpa using this
    apply childEdges_futureRemoval _ entry.1.2 ?_ (h entry.1 hMem) edge hChild
    intro q hq
    apply hSubset
    rw [indexedFragmentAccepting, mem_foldl_union_iff]
    exact Or.inr ⟨entry, hEntry, hq⟩

private theorem parallelFutureSpec_removal (label : AutomatonConstructionLabel)
    (target q : TypeAutomatonState) (current removed : Finset BareMessage)
    (h : parallelFutureSpec label target current = .at q removed) :
    removed = current ∧ label.semantic ≠ TypeLabel.tock := by
  by_cases hClock : label.semantic = TypeLabel.tock
  · simp [parallelFutureSpec, hClock] at h
  · have hEq : target = q ∧ current = removed := by
      simpa [parallelFutureSpec, hClock] using h
    exact ⟨hEq.2.symm, hClock⟩

private theorem sequenceFutureSpec_removal (label : AutomatonConstructionLabel)
    (target q : TypeAutomatonState) (current removed : Finset BareMessage)
    (h : sequenceRedirectFutureSpec label target current = .at q removed) :
    removed = current ∧ label.semantic ≠ TypeLabel.tock := by
  exact parallelFutureSpec_removal label target q current removed h

private theorem compileTypeFuel_futureRemoval :
    ∀ fuel ty edge, edge ∈ (compileTypeFuel fuel ty).edges →
      FutureRemoval (compileTypeFuel fuel ty).accepting edge := by
  intro fuel
  induction fuel with
  | zero => intro ty edge hEdge; simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
    intro ty edge hEdge
    cases ty with
    | skip alphabet | var alphabet name =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image,
        Finset.mem_filter] at hEdge
      obtain ⟨env, -, rfl⟩ := hEdge
      simp [FutureRemoval, compileTypeFuel, finishAutomatonFragment,
        AutomatonConstructionLabel.semantic, TypeLabel.silent]
    | message alphabet msg dir =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with (⟨env, -, rfl⟩ | ⟨env, -, rfl⟩) | ⟨env, -, rfl⟩ <;>
        simp [FutureRemoval, compileTypeFuel, finishAutomatonFragment,
          AutomatonConstructionLabel.semantic, TypeLabel.silent, TypeLabel.message]
    | tock alphabet =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, -, rfl⟩ | ⟨env, -, rfl⟩
      · cases hClock : env.clock <;>
          simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent]
    | progress alphabet pid =>
      simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image, Finset.mem_filter] at hEdge
      rcases hEdge with ⟨env, -, rfl⟩ | ⟨env, -, rfl⟩ <;>
        simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent,
          TypeLabel.progress]
    | choice alphabet left right | fairChoice alphabet bid left right =>
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildChoiceAutomaton, finishAutomatonFragment]
      rcases hEdge with (hLeft | hRight) | hRoot
      · exact childEdges_futureRemoval 0 _ Finset.subset_union_left (ih left) edge hLeft
      · exact childEdges_futureRemoval 1 _ Finset.subset_union_right (ih right) edge hRight
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
          Finset.mem_singleton] at hRoot
        obtain ⟨env, -, hCase⟩ := hRoot
        rcases hCase with rfl | rfl <;>
          simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent,
            TypeLabel.fair]
    | recur alphabet name body =>
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildRecursionAutomaton, finishAutomatonFragment]
      rcases hEdge with hRoot | hBody
      · obtain ⟨env, -, rfl⟩ := Finset.mem_image.mp hRoot
        simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hBody
        by_cases hMarker : inner.label = .variable name
        · simp [FutureRemoval, hMarker, AutomatonConstructionLabel.semantic, TypeLabel.silent]
        · simp only [hMarker, if_false]
          exact child_futureRemoval 0 inner (by intro q hq; exact hq) (ih body inner hInner)
    | seq alphabet left right =>
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildSequenceAutomaton, finishAutomatonFragment]
      rcases hEdge with (hLeft | hRight) | hRedirect
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hLeft
        intro q removed hFuture
        obtain ⟨hRemoved, hClock⟩ := sequenceFutureSpec_removal _ _ _ _ _ hFuture
        exact ⟨Or.inl hRemoved, hClock⟩
      · exact childEdges_futureRemoval 1 _ (by intro q hq; exact hq) (ih right) edge hRight
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hRedirect
        intro q removed hFuture
        obtain ⟨hRemoved, hClock⟩ := sequenceFutureSpec_removal _ _ _ _ _ hFuture
        exact ⟨Or.inl hRemoved, hClock⟩
    | par alphabet left right interface =>
      simp only [compileTypeFuel, buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
      · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_image] at hRaw
        obtain ⟨eL, -, eR, -, rfl⟩ := hRaw
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_image] at hLC
        obtain ⟨qL, -, eR, -, env, -, rfl⟩ := hLC
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_image] at hRC
        obtain ⟨qR, -, eL, -, env, -, rfl⟩ := hRC
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hLS
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hRS
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hLD
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · obtain ⟨inner, -, rfl⟩ := Finset.mem_image.mp hRD
        exact fun q removed hFuture => (parallelFutureSpec_removal _ _ _ _ _ hFuture).imp Or.inl id
      · obtain ⟨env, -, rfl⟩ := Finset.mem_image.mp hDone
        simp [FutureRemoval]
    | xoffer alphabet elseType branches | offer alphabet elseType branches =>
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
        buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
        buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
      rcases hEdge with (((hElse | hIndexed) | hBranch) | hWait) | hElseRoot
      · exact childEdges_futureRemoval 0 _ Finset.subset_union_left (ih elseType) edge hElse
      · refine indexedEdges_futureRemoval _ Finset.subset_union_right ?_ edge hIndexed
        intro fragment hFragment
        obtain ⟨entry, -, rfl⟩ := List.mem_map.mp hFragment
        exact ih _
      · rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨entry, -, hNew⟩
        · simp at hEmpty
        · obtain ⟨env, -, rfl⟩ := Finset.mem_image.mp hNew
          simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent,
            TypeLabel.message]
      · obtain ⟨env, -, rfl⟩ := Finset.mem_image.mp hWait
        simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent]
      · obtain ⟨env, -, rfl⟩ := Finset.mem_image.mp hElseRoot
        simp [FutureRemoval, AutomatonConstructionLabel.semantic, TypeLabel.silent]

/-- The child menu hypothesis and the compiler's future field recover the
whole offer summary, not just its current component. -/
theorem edge_future_eq_of_menuAgree {ty residual : PactType}
    (hMenus : FutureOffersAgree ty) {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hTarget : relationMembership (buildRelationSet ty (compileType ty)) residual target)
    (hEdge : (compileType ty).HasEdge source env label ⟨current, future⟩ target) :
    future = if label = TypeLabel.tock then ∅ else typeFutureOffers residual \ current := by
  obtain ⟨edge, hMem, -, -, hLabel, hCurrent, hFuture, hTargetEq⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge ty source target env label
      ⟨current, future⟩).mp hEdge
  cases hSpec : edge.future with
  | explicit offers =>
    have hEmpty := compileTypeFuel_storedMenusEmpty (typeCompilationFuel ty) ty
      edge hMem offers hSpec
    simp only [hSpec] at hFuture
    subst offers
    rw [← hFuture]
    split
    · rfl
    · next hClock =>
        have hAccept := compileTypeFuel_explicitOnlyAtAccepting
          (typeCompilationFuel ty) ty edge hMem
          (by simpa only [hLabel, AutomatonConstructionLabel.semantic] using hClock)
          ∅ hSpec
        have hTargetAccept := (compileTypeFuel_acceptingInert
          (typeCompilationFuel ty) ty edge hMem hAccept).2.1
        obtain ⟨skipAlphabet, hSkip⟩ := final_state_represents_skip ty hTarget
          (by simpa only [compileType, hTargetEq] using hTargetAccept)
        rw [hSkip]
        simp [typeFutureOffers, typeFutureOffersFuel]
  | «at» state removed =>
    have hState := compileTypeFuel_futureTargetsAreEdgeTargets
      (typeCompilationFuel ty) ty edge hMem state removed hSpec
    obtain ⟨hRemoved | hAccept, hClock⟩ := compileTypeFuel_futureRemoval
      (typeCompilationFuel ty) ty edge hMem state removed hSpec
    · simp only [hLabel, AutomatonConstructionLabel.semantic] at hClock
      simp only [hSpec, hState, hTargetEq, hRemoved, hCurrent, hMenus hTarget] at hFuture
      rw [if_neg hClock]
      exact hFuture.symm
    · obtain ⟨skipAlphabet, hSkip⟩ := final_state_represents_skip ty hTarget
        (by simpa only [compileType, hState, hTargetEq] using hAccept)
      simp only [hSpec, hState, hTargetEq, hMenus hTarget, hSkip] at hFuture
      have hEmpty : future = ∅ := by
        simpa [typeFutureOffers, typeFutureOffersFuel] using hFuture.symm
      simp [hEmpty, hSkip, typeFutureOffers, typeFutureOffersFuel]

/-- Both lower-rank hypotheses give a child edge with the same complete offer
summary. The current-offer hypothesis also identifies its target residual. -/
theorem CurrentOfferCorrespondence.forward_with_future {ty : PactType}
    (hCurrent : CurrentOfferCorrespondence ty) (hMenus : FutureOffersAgree ty)
    {rho rho' : PactType} {q : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q)
    (hStep : DecoratedTypeTransition env rho label ⟨current, future⟩ rho') :
    ∃ q', (compileType ty).HasEdge q env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet ty (compileType ty)) rho' q' := by
  obtain ⟨q', future', hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
  have hEq := edge_future_eq_of_menuAgree hMenus hTarget hEdge
  have hSemantic : future = if label = TypeLabel.tock then ∅
      else typeFutureOffers rho' \ current := by
    by_cases hClock : label = TypeLabel.tock
    · simpa only [if_pos hClock] using hStep.2.future_eq_empty_of_label_tock hClock
    · simpa only [if_neg hClock] using hStep.2.future_eq_sdiff_of_label_ne_tock hClock
  exact ⟨q', hEq.trans hSemantic.symm ▸ hEdge, hTarget⟩

theorem CurrentOfferCorrespondence.backward_with_future {ty : PactType}
    (hCurrent : CurrentOfferCorrespondence ty) (hMenus : FutureOffersAgree ty)
    {rho : PactType} {q q' : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q)
    (hEdge : (compileType ty).HasEdge q env label ⟨current, future⟩ q') :
    ∃ rho', DecoratedTypeTransition env rho label ⟨current, future⟩ rho' ∧
      relationMembership (buildRelationSet ty (compileType ty)) rho' q' := by
  obtain ⟨rho', future', hStep, hTarget⟩ := hCurrent.2 hRelated hEdge
  have hEq := edge_future_eq_of_menuAgree hMenus hTarget hEdge
  have hSemantic : future' = if label = TypeLabel.tock then ∅
      else typeFutureOffers rho' \ current := by
    by_cases hClock : label = TypeLabel.tock
    · simpa only [if_pos hClock] using hStep.2.future_eq_empty_of_label_tock hClock
    · simpa only [if_neg hClock] using hStep.2.future_eq_sdiff_of_label_ne_tock hClock
  exact ⟨rho', hSemantic.trans hEq.symm ▸ hStep, hTarget⟩

theorem edge_offers_empty_of_clock {ty residual : PactType}
    (hMenus : FutureOffersAgree ty) {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hTarget : relationMembership (buildRelationSet ty (compileType ty)) residual target)
    (hEdge : (compileType ty).HasEdge source env label ⟨current, future⟩ target)
    (hClock : env.clock = true) : current = ∅ ∧ future = ∅ := by
  obtain ⟨edge, hMem, -, hEnv, hLabel, hCurrent, -, -⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  obtain ⟨hTock, hEmpty⟩ := compileTypeFuel_clockEdgesAreTock
    (typeCompilationFuel ty) ty le_rfl edge hMem (by rw [hEnv]; exact hClock)
  simp only [hLabel, AutomatonConstructionLabel.semantic] at hTock
  exact ⟨hCurrent.symm.trans hEmpty,
    by simpa only [if_pos hTock] using edge_future_eq_of_menuAgree hMenus hTarget hEdge⟩

end
end Pact
