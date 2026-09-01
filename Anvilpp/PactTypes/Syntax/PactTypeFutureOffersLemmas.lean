import Anvilpp.PactTypes.Syntax.PactTypeFutureOffersDefs

namespace Pact

noncomputable section

/-- Syntax-derived futures of a sequence include the right menu exactly when
the left syntax may optimistically complete before the next clock. -/
theorem typeFutureOffers_sequence
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers (.seq alphabet left right) =
      if left.CanCompleteBeforeTock then
        typeFutureOffers left ∪ typeFutureOffers right
      else typeFutureOffers left := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  have hCompleteFuel : sizeOf left <
      sizeOf (PactType.seq alphabet left right) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.seq alphabet left right) + 1)
      (PactType.seq alphabet left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
      _ left hCompleteFuel,
    typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over ordinary choice. -/
theorem typeFutureOffers_choice
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers (.choice alphabet left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.choice alphabet left right) := by
    change sizeOf left + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.choice alphabet left right) := by
    change sizeOf right + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.choice alphabet left right) + 1)
      (PactType.choice alphabet left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over fair choice. -/
theorem typeFutureOffers_fairChoice
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType) :
    typeFutureOffers (.fairChoice alphabet bid left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.fairChoice alphabet bid left right) := by
    change sizeOf left + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.fairChoice alphabet bid left right) := by
    change sizeOf right + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.fairChoice alphabet bid left right) + 1)
      (PactType.fairChoice alphabet bid left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures of an exclusive offer contain the else menu, every
branch head, and every branch continuation menu. -/
theorem typeFutureOffers_xoffer
    (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hGate : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeFutureOffers (.xoffer alphabet elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  let fuel := sizeOf (PactType.xoffer alphabet elseType branches)
  have hElseFuel : sizeOf elseType + 1 ≤ fuel := by
    simp [fuel]
    omega
  have hBranchFuel : ∀ branch ∈ branches,
      sizeOf branch.2 + 1 ≤ fuel := by
    intro branch hBranch
    have hPairSize := List.sizeOf_lt_of_mem hBranch
    have hComponentSize : sizeOf branch.2 < sizeOf branch := by
      rcases branch
      simp_wf
      omega
    simp [fuel]
    omega
  have hFold : ∀ rest : List (BareMessage × PactType),
      (∀ branch ∈ rest, sizeOf branch.2 + 1 ≤ fuel) →
      ∀ initial,
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) initial =
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial := by
    intro rest hRest
    induction rest with
    | nil => simp
    | cons branch tail ih =>
        intro initial
        simp only [List.foldl_cons]
        rw [typeFutureOffersFuel_eq_typeFutureOffers branch.2 fuel
          (hRest branch (by simp))]
        apply ih
        intro entry hEntry
        exact hRest entry (by simp [hEntry])
  change (if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
        (typeFutureOffersFuel fuel elseType)
    else ∅) = _
  rw [if_pos hGate]
  rw [typeFutureOffersFuel_eq_typeFutureOffers elseType fuel hElseFuel]
  exact hFold branches hBranchFuel (typeFutureOffers elseType)

/-- Conjunctive offers have the same optimistic syntax menu as exclusive
offers: the else continuation, every branch head, and every branch menu. -/
theorem typeFutureOffers_offer
    (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hGate : ∀ b ∈ branches, b.1 ∈ alphabet.actions) :
    typeFutureOffers (.offer alphabet elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  simpa only [typeFutureOffers, typeFutureOffersFuel] using
    typeFutureOffers_xoffer alphabet elseType branches hGate

/-- Parallel future offers are the optimistic union of both syntax-derived
component menus, with the synchronization interface hidden. -/
theorem typeFutureOffers_parallel
    (alphabet : PactTypeAlphabet) (left right : PactType) (interface : Interface) :
    typeFutureOffers (.par alphabet left right interface) =
      hideTypeOffers interface
        (typeFutureOffers left ∪ typeFutureOffers right) := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.par alphabet left right interface) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.par alphabet left right interface) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.par alphabet left right interface) + 1)
      (PactType.par alphabet left right interface) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- A recursion binder exposes the same syntactic same-cycle future menu as
its body; guardedness is used separately when replacing recursive calls. -/
theorem typeFutureOffers_recur
    (alphabet : PactTypeAlphabet) (name : String) (body : PactType) :
    typeFutureOffers (.recur alphabet name body) = typeFutureOffers body := by
  have hBodyFuel : sizeOf body + 1 ≤
      sizeOf (PactType.recur alphabet name body) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.recur alphabet name body) + 1)
      (PactType.recur alphabet name body) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers body _ hBodyFuel]

/-- A decorated offer step that reaches `skip` has no future offer.

This is the semantic counterpart of the `seq_fuse_tock`/`par_fuse_tock`
split: once the residual is `skip`, there is no later message menu to
advertise. -/
theorem TypeOffers.future_eq_empty_of_target_skip
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hTarget : target = .skip target.alphabet) :
    future = ∅ := by
  induction hOffers using TypeOffers.rec with
  | action =>
      simp [typeFutureOffers, typeFutureOffersFuel]
  | action_wait =>
      cases hTarget
  | choice_left env alphabet left right hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | choice_right env alphabet left right hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | fair_left env alphabet bid left right hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | fair_right env alphabet bid left right hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | cycle =>
      simp
  | cycle_wait =>
      simp [typeFutureOffers, typeFutureOffersFuel]
  | skip =>
      simp [typeFutureOffers, typeFutureOffersFuel]
  | progress =>
      simp [typeFutureOffers, typeFutureOffersFuel]
  | recur env alphabet name body hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | seq env alphabet left left' right label current childFuture hChild
      hNotSkip hNotTock ihChild =>
      cases hTarget
  | seq_tock env alphabet left left' right current childFuture hChild
      hNotSkip ihChild =>
      simp
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ihChild =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | seq_fuse_tock =>
      simp
  | xoffer_branch env alphabet elseType branches action branchType hSelect =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | xoffer_else env alphabet elseType branches hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | xoffer_wait =>
      cases hTarget
  | offer_some env alphabet elseType branches enabled hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | offer_else env alphabet elseType branches hConditions =>
      rw [hTarget]
      simp [typeFutureOffers, typeFutureOffersFuel]
  | offer_wait =>
      cases hTarget
  | par =>
      cases hTarget
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocal1
      hLocal2 hConditions hNotTock ihLeft ihRight =>
      have hLeftFuture : leftFuture = ∅ := ihLeft rfl
      have hRightFuture : rightFuture = ∅ := ihRight rfl
      rw [hLeftFuture, hRightFuture]
      simp [hideTypeOffers]
  | par_fuse_tock =>
      simp
  | left_complete outer rightEnv interface left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hRight hNotSkip _ _
      hLocal hWF hNotTock ihRight =>
      refine absurd ?_ hNotSkip
      cases hForm : right' <;> rw [hForm] at hTarget <;>
        simp [PactType.reannotate, PactType.alphabet] at hTarget ⊢
  | left_complete_tock =>
      simp
  | right_complete outer leftEnv interface left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hLeft hNotSkip _ _
      hLocal hWF hNotTock ihLeft =>
      refine absurd ?_ hNotSkip
      cases hForm : left' <;> rw [hForm] at hTarget <;>
        simp [PactType.reannotate, PactType.alphabet] at hTarget ⊢
  | right_complete_tock =>
      simp

/-- Combining to a clock forces both component labels to be clocks. -/
theorem TypeLabel.combine_eq_tock_iff (interface : Interface)
    (left right : TypeLabel) :
    TypeLabel.combine interface left right = TypeLabel.tock ↔
      left = TypeLabel.tock ∧ right = TypeLabel.tock := by
  cases left <;> cases right <;>
    simp [TypeLabel.combine, TypeLabel.silent]

/-- A clock offer step exposes no future menu.

The clock ends the current cycle, so nothing later in it can still be
advertised.  This is the semantic counterpart of the `seq_tock` /
`seq_fuse_tock` / `par_fuse_tock` split. -/
theorem TypeOffers.future_eq_empty_of_label_tock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label = TypeLabel.tock) :
    future = ∅ := by
  induction hOffers using TypeOffers.rec with
  | action => cases hLabel
  | action_wait => cases hLabel
  | choice_left => cases hLabel
  | choice_right => cases hLabel
  | fair_left => cases hLabel
  | fair_right => cases hLabel
  | cycle => simp
  | cycle_wait => cases hLabel
  | skip => cases hLabel
  | progress => cases hLabel
  | recur => cases hLabel
  | seq _ _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_tock => simp
  | seq_fuse _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_fuse_tock => simp
  | xoffer_branch => cases hLabel
  | xoffer_else => cases hLabel
  | xoffer_wait => cases hLabel
  | offer_some => cases hLabel
  | offer_else => cases hLabel
  | offer_wait => cases hLabel
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip
      hRightNotSkip hLeft hRight hNotBothSkip hLocal1 hLocal2 hConditions
      ihLeft ihRight =>
      simp [hLabel]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ =>
      exact absurd hLabel hNotTock
  | par_fuse_tock => simp
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ =>
      exact absurd hLabel hNotTock
  | left_complete_tock => simp
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ =>
      exact absurd hLabel hNotTock
  | right_complete_tock => simp

end

end Pact
