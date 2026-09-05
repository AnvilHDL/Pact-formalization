import Anvilpp.PactTypes.NewCorrespondence.Helpers.TypeWellFormedIn
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers
import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.CompletionNormalization

namespace Pact

noncomputable section

open Classical

private theorem branchCanCompleteBeforeTock_of_mem
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) (hComplete : branch.2.CanCompleteBeforeTock = true) :
    PactType.BranchCanCompleteBeforeTock branches = true := by
  induction branches with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.BranchCanCompleteBeforeTock, Bool.or_eq_true]
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact Or.inl hComplete
      · exact Or.inr (ih hRest)

/-- A committed conjunction must complete its selected branch. -/
theorem parallelTypeBranchesSelecting_canComplete_before
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) (hSelected : selected ∈ branches)
    (hComplete : (parallelTypeBranchesSelecting alphabet selected branches).CanCompleteBeforeTock = true) :
    selected.2.CanCompleteBeforeTock = true := by
  have hWithin : ∀ branches : List (BareMessage × PactType),
      selected ∈ branches →
      (parallelTypeBranchesSelectingWithin alphabet selected branches).CanCompleteBeforeTock = true →
      selected.2.CanCompleteBeforeTock = true := by
    intro branches
    induction branches with
    | nil => simp
    | cons head rest ih =>
        intro hMem hComplete
        cases rest with
        | nil =>
            have hEq : head = selected := (List.mem_singleton.mp hMem).symm
            simpa [parallelTypeBranchesSelectingWithin, hEq, selectedTypeBranchAt,
              PactType.CanCompleteBeforeTock, PactType.reannotate_canCompleteBeforeTock]
              using hComplete
        | cons next tail =>
            by_cases hEq : head = selected
            · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq] at hComplete
              simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true] at hComplete
              simpa [selectedTypeBranchAt, PactType.CanCompleteBeforeTock,
                PactType.reannotate_canCompleteBeforeTock, hEq] using hComplete.1
            · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq] at hComplete
              simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true] at hComplete
              exact ih ((List.mem_cons.mp hMem).resolve_left (Ne.symm hEq)) hComplete.2
  cases branches with
  | nil => simp at hSelected
  | cons head rest => exact hWithin (head :: rest) hSelected hComplete

/-- A non-clock type step cannot turn the optimistic completion test from false to true. -/
theorem TypeTransition.canCompleteBeforeTock_backward
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hStep : TypeTransition env source label target)
    (hNonClock : label ≠ .tock)
    (hComplete : target.CanCompleteBeforeTock = true) :
    source.CanCompleteBeforeTock = true := by
  have hIsTock (label : TypeLabel) : label.isTock ↔ label = .tock := by
    cases label <;> simp [TypeLabel.isTock]
  induction hStep with
  | action | action_wait | skip | progress => simp [PactType.CanCompleteBeforeTock]
  | cycle => exact (hNonClock rfl).elim
  | cycle_wait => exact hComplete
  | choice_left | choice_right | fair_left | fair_right =>
      simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
      first | exact Or.inl hComplete | exact Or.inr hComplete
  | recur env alphabet name body =>
      simpa only [PactType.replaceVar_canCompleteBeforeTock, PactType.CanCompleteBeforeTock,
        PactType.canCompleteBeforeTockSubst_self] using hComplete
  | seq env alphabet left left' right label _ _ ih =>
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true] at hComplete ⊢
      exact ⟨ih hNonClock hComplete.1, hComplete.2⟩
  | seq_fuse env alphabet skipAlphabet left right label _ ih =>
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
      exact ⟨ih hNonClock (by simp [PactType.CanCompleteBeforeTock]), hComplete⟩
  | xoffer_branch env alphabet other branches action body hEnv =>
      simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
      exact Or.inr (branchCanCompleteBeforeTock_of_mem hEnv.2.1 hComplete)
  | xoffer_else | offer_else =>
      simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
      exact Or.inl hComplete
  | xoffer_wait | offer_wait => exact hComplete
  | offer_some env alphabet other branches selected hEnv =>
      simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
      exact Or.inr (branchCanCompleteBeforeTock_of_mem hEnv.2.1
        (parallelTypeBranchesSelecting_canComplete_before alphabet selected branches
          hEnv.2.1 hComplete))
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _ hEnv ihLeft ihRight =>
      have hClocks := typeLabel_sync_not_isTock interface leftLabel rightLabel hEnv.2.2.2
        (by simpa only [hIsTock] using hNonClock)
      have hLeftClock : leftLabel ≠ .tock := by simpa only [hIsTock] using hClocks.1
      have hRightClock : rightLabel ≠ .tock := by simpa only [hIsTock] using hClocks.2
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true] at hComplete ⊢
      exact ⟨ihLeft hLeftClock hComplete.1, ihRight hRightClock hComplete.2⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ hEnv ihLeft ihRight =>
      have hClocks := typeLabel_sync_not_isTock interface leftLabel rightLabel hEnv.2.2.2
        (by simpa only [hIsTock] using hNonClock)
      have hLeftClock : leftLabel ≠ .tock := by simpa only [hIsTock] using hClocks.1
      have hRightClock : rightLabel ≠ .tock := by simpa only [hIsTock] using hClocks.2
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
      exact ⟨ihLeft hLeftClock (by simp [PactType.CanCompleteBeforeTock]),
        ihRight hRightClock (by simp [PactType.CanCompleteBeforeTock])⟩
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hSkip _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.reannotate_canCompleteBeforeTock] at hComplete
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
      exact ⟨by rw [hSkip]; simp [PactType.CanCompleteBeforeTock], ih hNonClock hComplete⟩
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hSkip _ _ _ _ _ _ _ _ ih =>
      simp only [PactType.reannotate_canCompleteBeforeTock] at hComplete
      simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
      exact ⟨ih hNonClock hComplete, by rw [hSkip]; simp [PactType.CanCompleteBeforeTock]⟩

private theorem branchCanCompleteDeclared_of_mem
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) (hComplete : branch.2.CanCompleteDeclared = true) :
    PactType.BranchCanCompleteDeclared branches = true := by
  induction branches with
  | nil => simp at hMem
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      rw [PactType.branchCanCompleteDeclared_cons]
      rcases List.mem_cons.mp hMem with rfl | hRest
      · simp only [hComplete, Bool.true_or]
      · simp only [ih hRest, Bool.or_true]

private theorem selected_canCompleteDeclared_before
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) (hSelected : selected ∈ branches)
    (hNormal : selected.2.reannotate alphabet = selected.2)
    (hComplete : (parallelTypeBranchesSelecting alphabet selected branches).CanCompleteDeclared = true) :
    selected.2.CanCompleteDeclared = true := by
  have hWithin : ∀ branches : List (BareMessage × PactType), selected ∈ branches →
      (parallelTypeBranchesSelectingWithin alphabet selected branches).CanCompleteDeclared = true →
        selected.2.CanCompleteDeclared = true := by
    intro branches
    induction branches with
    | nil => simp
    | cons head rest ih =>
      intro hMem hComplete
      cases rest with
      | nil =>
          have hEq : head = selected := (List.mem_singleton.mp hMem).symm
          simp only [parallelTypeBranchesSelectingWithin, hEq, if_pos rfl, selectedTypeBranchAt] at hComplete
          rw [PactType.canCompleteDeclared_eq] at hComplete
          exact hNormal ▸ (Bool.and_eq_true_iff.mp hComplete).2
      | cons next tail =>
          by_cases hEq : head = selected
          · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq] at hComplete
            rw [PactType.canCompleteDeclared_eq] at hComplete
            have hHead := (Bool.and_eq_true_iff.mp hComplete).1
            simp only [selectedTypeBranchAt, hEq] at hHead
            rw [PactType.canCompleteDeclared_eq] at hHead
            exact hNormal ▸ (Bool.and_eq_true_iff.mp hHead).2
          · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq] at hComplete
            rw [PactType.canCompleteDeclared_eq] at hComplete
            exact ih ((List.mem_cons.mp hMem).resolve_left (Ne.symm hEq)) (Bool.and_eq_true_iff.mp hComplete).2
  cases branches with
  | nil => simp at hSelected
  | cons head rest => exact hWithin (head :: rest) hSelected hComplete

/-- Non-clock steps propagate declared-action completion backwards. -/
theorem TypeTransition.canCompleteDeclared_backward
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hStep : TypeTransition env source label target)
    (hNormal : source.reannotate source.alphabet = source)
    (hTail : source.TailRecursive)
    (hNonClock : label ≠ .tock) (hComplete : target.CanCompleteDeclared = true) :
    source.CanCompleteDeclared = true := by
  have hIsTock (label : TypeLabel) : label.isTock ↔ label = .tock := by
    cases label <;> simp [TypeLabel.isTock]
  induction hStep with
  | action | action_wait | skip | progress =>
      simp_all [PactType.CanCompleteDeclared, PactType.completionView, PactType.CanCompleteBeforeTock]
  | cycle => exact (hNonClock rfl).elim
  | cycle_wait => exact hComplete
  | choice_left | choice_right | fair_left | fair_right =>
      rw [PactType.canCompleteDeclared_eq]
      simp only [Bool.or_eq_true]
      first | exact Or.inl hComplete | exact Or.inr hComplete
  | recur env alphabet name body =>
      rw [PactType.canCompleteDeclared_recur_unfold] at hComplete
      rw [PactType.canCompleteDeclared_eq]
      exact hComplete
  | seq env alphabet left left' right label _ _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.seq.injEq, true_and] at hNormal
      simp only [PactType.TailRecursive] at hTail
      rw [PactType.canCompleteDeclared_eq] at hComplete ⊢
      simp only [Bool.and_eq_true] at hComplete ⊢
      exact ⟨ih (PactType.reannotate_eq_self_data hNormal.1).2 hTail.1 hNonClock hComplete.1, hComplete.2⟩
  | seq_fuse env alphabet skipAlphabet left right label _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.seq.injEq, true_and] at hNormal
      simp only [PactType.TailRecursive] at hTail
      rw [PactType.canCompleteDeclared_eq]
      exact Bool.and_eq_true_iff.mpr ⟨ih (PactType.reannotate_eq_self_data hNormal.1).2 hTail.1
        hNonClock (PactType.canCompleteDeclared_eq (.skip skipAlphabet)), hComplete⟩
  | xoffer_branch env alphabet other branches action body hEnv hGate =>
      rw [PactType.canCompleteDeclared_eq]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      exact ⟨hGate, Or.inr (branchCanCompleteDeclared_of_mem hEnv.2.1 hComplete)⟩
  | xoffer_else env alphabet other branches hEnv hGate
  | offer_else env alphabet other branches hEnv hGate =>
      rw [PactType.canCompleteDeclared_eq]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      exact ⟨hGate, Or.inl hComplete⟩
  | xoffer_wait | offer_wait => exact hComplete
  | offer_some env alphabet other branches selected hEnv hGate =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.offer.injEq, true_and] at hNormal
      rw [PactType.reannotateOfferBranches_map] at hNormal
      rw [PactType.canCompleteDeclared_eq]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      exact ⟨hGate, Or.inr (branchCanCompleteDeclared_of_mem hEnv.2.1
        (selected_canCompleteDeclared_before alphabet selected branches hEnv.2.1
          (reannotate_branches_fixed_of_mem alphabet branches hNormal.2 selected hEnv.2.1) hComplete))⟩
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _ hEnv ihLeft ihRight =>
      have hClocks := typeLabel_sync_not_isTock interface leftLabel rightLabel hEnv.2.2.2
        (by simpa only [hIsTock] using hNonClock)
      simp only [hIsTock] at hClocks
      simp only [PactType.alphabet, PactType.reannotate, PactType.par.injEq, true_and, and_true] at hNormal
      simp only [PactType.TailRecursive] at hTail
      rw [PactType.canCompleteDeclared_eq] at hComplete ⊢
      simp only [Bool.and_eq_true] at hComplete ⊢
      exact ⟨ihLeft (PactType.reannotate_eq_self_data hNormal.1).2 hTail.1 hClocks.1 hComplete.1,
        ihRight (PactType.reannotate_eq_self_data hNormal.2).2 hTail.2 hClocks.2 hComplete.2⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ hEnv ihLeft ihRight =>
      have hClocks := typeLabel_sync_not_isTock interface leftLabel rightLabel hEnv.2.2.2
        (by simpa only [hIsTock] using hNonClock)
      simp only [hIsTock] at hClocks
      simp only [PactType.alphabet, PactType.reannotate, PactType.par.injEq, true_and, and_true] at hNormal
      simp only [PactType.TailRecursive] at hTail
      rw [PactType.canCompleteDeclared_eq]
      exact Bool.and_eq_true_iff.mpr
        ⟨ihLeft (PactType.reannotate_eq_self_data hNormal.1).2 hTail.1 hClocks.1
          (PactType.canCompleteDeclared_eq (.skip _)),
         ihRight (PactType.reannotate_eq_self_data hNormal.2).2 hTail.2 hClocks.2
          (PactType.canCompleteDeclared_eq (.skip _))⟩
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hSkip _ hStep _ _ _ _ _ _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.par.injEq, true_and, and_true] at hNormal
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hA, hN⟩ := PactType.reannotate_eq_self_data hNormal.2
      have hSub : alphabet.actions ⊆ right.alphabet.actions := by
        rw [hA]; exact Finset.subset_union_right
      have hTarget := hStep.preserves_reannotate_self hN hTail.2
      have hRaw := PactType.canCompleteDeclared_reannotate_mono right' alphabet right.alphabet hSub hComplete
      rw [hTarget] at hRaw
      rw [PactType.canCompleteDeclared_eq]
      exact Bool.and_eq_true_iff.mpr ⟨by rw [hSkip]; exact PactType.canCompleteDeclared_eq (.skip _),
        ih hN hTail.2 hNonClock hRaw⟩
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hSkip _ hStep _ _ _ _ _ _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.par.injEq, true_and, and_true] at hNormal
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hA, hN⟩ := PactType.reannotate_eq_self_data hNormal.1
      have hSub : alphabet.actions ⊆ left.alphabet.actions := by
        rw [hA]; exact Finset.subset_union_right
      have hTarget := hStep.preserves_reannotate_self hN hTail.1
      have hRaw := PactType.canCompleteDeclared_reannotate_mono left' alphabet left.alphabet hSub hComplete
      rw [hTarget] at hRaw
      rw [PactType.canCompleteDeclared_eq]
      exact Bool.and_eq_true_iff.mpr ⟨ih hN hTail.1 hNonClock hRaw,
        by rw [hSkip]; exact PactType.canCompleteDeclared_eq (.skip _)⟩

/-- The same implication for the completion test used by the compiler. -/
theorem TypeTransition.completionFlag_backward
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hStep : TypeTransition env source label target)
    (hNormal : source.reannotate source.alphabet = source) (hTail : source.TailRecursive)
    (hNonClock : label ≠ .tock)
    (hComplete : typeCanCompleteThisCycleFuel (sizeOf target + 1) target = true) :
    typeCanCompleteThisCycleFuel (sizeOf source + 1) source = true := by
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ target (by omega)] at hComplete
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ source (by omega)]
  exact hStep.canCompleteDeclared_backward hNormal hTail hNonClock hComplete

end

end Pact
