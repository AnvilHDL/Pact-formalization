import Anvilpp.PactTypes.Spec.Syntax.PactTypeFutureOffersDefs

namespace Pact

noncomputable section

/-- Syntax-derived futures of a sequence include the right menu exactly when
the left syntax may optimistically complete before the next clock. -/
theorem typeFutureOffers_sequence
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers (.seq alphabet left right) =
      if left.CanCompleteDeclared then
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
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared
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

/-- Combining to a clock forces both component labels to be clocks. -/
theorem TypeLabel.combine_eq_tock_iff (interface : Interface)
    (left right : TypeLabel) :
    TypeLabel.combine interface left right = TypeLabel.tock ↔
      left = TypeLabel.tock ∧ right = TypeLabel.tock := by
  cases left <;> cases right <;>
    simp [TypeLabel.combine, TypeLabel.silent]

/-- A label synchronized with `ε` on `I` meets no interface id, so no message
is resolved and the combination is that label itself: `ε ∪_I α = α`. -/
theorem TypeLabel.combine_silent_left (interface : Interface) (label : TypeLabel)
    (hSync : TypeLabel.Sync interface TypeLabel.silent label) :
    TypeLabel.combine interface TypeLabel.silent label = label := by
  classical
  obtain ⟨hSends, hRecvs, hTock⟩ := hSync
  cases label with
  | tock => exact absurd (hTock.mpr trivial) (by simp [TypeLabel.silent, TypeLabel.isTock])
  | actions observations =>
    have hNoSends : interface ∩ (TypeLabel.actions observations).sends = ∅ := by
      rw [← hRecvs]
      simp [TypeLabel.silent, TypeLabel.recvs, TypeLabel.messageIdsWith]
    have hEmptySends : (TypeLabel.actions ∅).sends = (∅ : Finset MessageId) := by
      simp [TypeLabel.sends, TypeLabel.messageIdsWith]
    have hSynced :
        TypeLabel.synced interface (.actions ∅) (.actions observations) = ∅ := by
      show (interface ∩ (TypeLabel.actions ∅).sends) ∪
        (interface ∩ (TypeLabel.actions observations).sends) = ∅
      rw [hEmptySends, Finset.inter_empty, Finset.empty_union, hNoSends]
    have hFilter : (∅ ∪ observations).filter
        (fun observation => !(TypeLabel.isRawSyncedMessage ∅ observation)) =
        observations := by
      rw [Finset.empty_union]
      refine Finset.filter_true_of_mem ?_
      intro observation _
      cases observation <;> simp [TypeLabel.isRawSyncedMessage]
    simp only [TypeLabel.silent, TypeLabel.combine, hSynced, hFilter,
      Finset.image_empty, Finset.union_empty]

/-- Mirror of `TypeLabel.combine_silent_left`: `α ∪_I ε = α`. -/
theorem TypeLabel.combine_silent_right (interface : Interface) (label : TypeLabel)
    (hSync : TypeLabel.Sync interface label TypeLabel.silent) :
    TypeLabel.combine interface label TypeLabel.silent = label := by
  classical
  obtain ⟨hSends, hRecvs, hTock⟩ := hSync
  cases label with
  | tock => exact absurd (hTock.mp trivial) (by simp [TypeLabel.silent, TypeLabel.isTock])
  | actions observations =>
    have hNoSends : interface ∩ (TypeLabel.actions observations).sends = ∅ := by
      rw [hSends]
      simp [TypeLabel.silent, TypeLabel.recvs, TypeLabel.messageIdsWith]
    have hEmptySends : (TypeLabel.actions ∅).sends = (∅ : Finset MessageId) := by
      simp [TypeLabel.sends, TypeLabel.messageIdsWith]
    have hSynced :
        TypeLabel.synced interface (.actions observations) (.actions ∅) = ∅ := by
      show (interface ∩ (TypeLabel.actions observations).sends) ∪
        (interface ∩ (TypeLabel.actions ∅).sends) = ∅
      rw [hEmptySends, Finset.inter_empty, Finset.union_empty, hNoSends]
    have hFilter : observations.filter
        (fun observation => !(TypeLabel.isRawSyncedMessage ∅ observation)) =
        observations := by
      refine Finset.filter_true_of_mem ?_
      intro observation _
      cases observation <;> simp [TypeLabel.isRawSyncedMessage]
    simp only [TypeLabel.silent, TypeLabel.combine, hSynced, hFilter,
      Finset.image_empty, Finset.union_empty]

/-- Clock half of the uniform offer law: a clock step advertises nothing now. -/
theorem TypeOffers.current_eq_empty_of_label_tock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future)
    (hLabel : label = TypeLabel.tock) :
    current = ∅ := by
  induction hOffers using TypeOffers.rec with
  | action => cases hLabel
  | action_wait => cases hLabel
  | choice_left => cases hLabel
  | choice_right => cases hLabel
  | fair_left => cases hLabel
  | fair_right => cases hLabel
  | cycle => rfl
  | cycle_wait => cases hLabel
  | skip => cases hLabel
  | progress => cases hLabel
  | recur => cases hLabel
  | seq _ _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_tock => rfl
  | seq_fuse _ _ _ _ _ _ _ _ _ hNotTock _ => exact absurd hLabel hNotTock
  | seq_fuse_tock => rfl
  | xoffer_branch => cases hLabel
  | xoffer_else => cases hLabel
  | xoffer_wait => cases hLabel
  | offer_some => cases hLabel
  | offer_else => cases hLabel
  | offer_wait => cases hLabel
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _
      _ ihLeft ihRight =>
      obtain ⟨hLeftTock, hRightTock⟩ :=
        (TypeLabel.combine_eq_tock_iff interface leftLabel rightLabel).mp hLabel
      rw [ihLeft hLeftTock, ihRight hRightTock]
      simp [hideTypeOffers]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ =>
      exact absurd hLabel hNotTock
  | par_fuse_tock => rfl
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSync _ _ =>
      exact absurd (hSync.2.2.mpr (by rw [hLabel]; trivial))
        (by simp [TypeLabel.silent, TypeLabel.isTock])
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSync _ _ =>
      exact absurd (hSync.2.2.mp (by rw [hLabel]; trivial))
        (by simp [TypeLabel.silent, TypeLabel.isTock])

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
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftNotSkip
      hRightNotSkip hLeft hRight hNotBothSkip hLocal1 hLocal2 hConditions
      ihLeft ihRight =>
      simp [hLabel]
  | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock _ _ =>
      exact absurd hLabel hNotTock
  | par_fuse_tock => simp
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSync _ _ =>
      exact absurd (hSync.2.2.mpr (by rw [hLabel]; trivial))
        (by simp [TypeLabel.silent, TypeLabel.isTock])
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hSync _ _ =>
      exact absurd (hSync.2.2.mp (by rw [hLabel]; trivial))
        (by simp [TypeLabel.silent, TypeLabel.isTock])

/-- Membership in an offer's folded menu: the default's menu, or some branch's
head or menu. -/
theorem mem_foldl_offer_menu {action : BareMessage} :
    ∀ (branches : List (BareMessage × PactType))
      (initial : Finset BareMessage),
      action ∈ branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial ↔
        action ∈ initial ∨
          ∃ branch ∈ branches,
            action = branch.1 ∨ action ∈ typeFutureOffers branch.2
  | [], initial => by simp
  | branch :: rest, initial => by
      rw [List.foldl_cons, mem_foldl_offer_menu rest]
      simp only [Finset.mem_union, Finset.mem_singleton, List.mem_cons]
      aesop

/-- The uncommitted singleton product offers every branch head together with
every branch continuation menu. -/
theorem typeFutureOffers_parallelTypeBranchesWithin
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ b ∈ branches, b.1 ∈ alphabet.actions) →
      (∀ b ∈ branches, b.2.alphabet = alphabet) →
      (∀ b ∈ branches, b.2.AlphabetWellFormed) →
      typeFutureOffers (parallelTypeBranchesWithin alphabet branches) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
  have hSkip : typeFutureOffers (PactType.skip alphabet) = ∅ := by
    simp [typeFutureOffers, typeFutureOffersFuel]
  have hHideEmpty : ∀ offers : Finset BareMessage,
      hideTypeOffers (∅ : Interface) offers = offers := by
    intro offers
    ext action
    simp [hideTypeOffers]
  have hSingle : ∀ b : BareMessage × PactType,
      b.1 ∈ alphabet.actions → b.2.alphabet = alphabet →
      b.2.AlphabetWellFormed →
      typeFutureOffers (singletonTypeXOfferAt alphabet b) =
        {b.1} ∪ typeFutureOffers b.2 := by
    intro b hDecl hAlpha hWFb
    have hOwn : b.2.reannotate alphabet = b.2 := by
      rw [← hAlpha]
      exact PactType.reannotate_own_alphabet b.2 hWFb
    have hGate : ∀ x ∈ [(b.1, b.2.reannotate alphabet)],
        x.1 ∈ alphabet.actions := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hDecl
    have hUnfold : singletonTypeXOfferAt alphabet b =
        PactType.xoffer alphabet (PactType.skip alphabet)
          [(b.1, b.2.reannotate alphabet)] := rfl
    rw [hUnfold, typeFutureOffers_xoffer alphabet (PactType.skip alphabet)
      [(b.1, b.2.reannotate alphabet)] hGate, hOwn, hSkip]
    simp
  intro branches
  induction branches with
  | nil =>
      intro _ _ _
      simp [parallelTypeBranchesWithin, hSkip]
  | cons head rest ih =>
      intro hDeclared hAlphabet hWF
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          rw [hSingle head (hDeclared head (by simp)) (hAlphabet head (by simp))
            (hWF head (by simp))]
          simp
      | cons next tail =>
          simp only [parallelTypeBranchesWithin]
          rw [typeFutureOffers_parallel,
            hSingle head (hDeclared head (by simp)) (hAlphabet head (by simp))
              (hWF head (by simp)),
            ih (fun b hb => hDeclared b (by simp [hb]))
              (fun b hb => hAlphabet b (by simp [hb]))
              (fun b hb => hWF b (by simp [hb]))]
          rw [hHideEmpty]
          ext action
          simp only [List.foldl_cons, mem_foldl_offer_menu, Finset.mem_union,
            Finset.mem_singleton, Finset.notMem_empty, false_or, or_assoc]

/-- The committed product has the same menu as the uncommitted one: dropping a
singleton offer's synthetic `skip` arm in favour of a mandatory head keeps both
that head and its continuation menu on offer. -/
theorem typeFutureOffers_parallelTypeBranchesSelecting
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hDeclared : ∀ b ∈ branches, b.1 ∈ alphabet.actions)
    (hAlphabet : ∀ b ∈ branches, b.2.alphabet = alphabet)
    (hWF : ∀ b ∈ branches, b.2.AlphabetWellFormed) :
    typeFutureOffers (parallelTypeBranchesSelecting alphabet selected branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
  have hSkip : ∀ signature : PactTypeAlphabet,
      typeFutureOffers (PactType.skip signature) = ∅ := by
    intro signature
    simp [typeFutureOffers, typeFutureOffersFuel]
  have hHideEmpty : ∀ offers : Finset BareMessage,
      hideTypeOffers (∅ : Interface) offers = offers := by
    intro offers
    ext action
    simp [hideTypeOffers]
  have hSingle : ∀ b : BareMessage × PactType,
      b.1 ∈ alphabet.actions → b.2.alphabet = alphabet →
      b.2.AlphabetWellFormed →
      typeFutureOffers (singletonTypeXOfferAt alphabet b) =
        {b.1} ∪ typeFutureOffers b.2 := by
    intro b hDecl hAlpha hWFb
    have hOwn : b.2.reannotate alphabet = b.2 := by
      rw [← hAlpha]
      exact PactType.reannotate_own_alphabet b.2 hWFb
    have hGate : ∀ x ∈ [(b.1, b.2.reannotate alphabet)],
        x.1 ∈ alphabet.actions := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hDecl
    have hUnfold : singletonTypeXOfferAt alphabet b =
        PactType.xoffer alphabet (PactType.skip alphabet)
          [(b.1, b.2.reannotate alphabet)] := rfl
    rw [hUnfold, typeFutureOffers_xoffer alphabet (PactType.skip alphabet)
      [(b.1, b.2.reannotate alphabet)] hGate, hOwn, hSkip]
    simp
  have hSelected : ∀ b : BareMessage × PactType,
      b.1 ∈ alphabet.actions → b.2.alphabet = alphabet →
      b.2.AlphabetWellFormed →
      typeFutureOffers (selectedTypeBranchAt alphabet b) =
        {b.1} ∪ typeFutureOffers b.2 := by
    intro b hDecl hAlpha hWFb
    have hOwn : b.2.reannotate alphabet = b.2 := by
      rw [← hAlpha]
      exact PactType.reannotate_own_alphabet b.2 hWFb
    have hEta : ((b.1.1, b.1.2) : BareMessage) = b.1 := rfl
    have hHead : typeFutureOffers
        (PactType.message alphabet b.1.1 b.1.2) = {b.1} := by
      simp only [typeFutureOffers, typeFutureOffersFuel, hEta]
      rw [if_pos hDecl]
    have hCan : (PactType.message alphabet b.1.1 b.1.2).CanCompleteDeclared =
        true := by
      rw [PactType.canCompleteDeclared_eq]
      exact decide_eq_true hDecl
    have hUnfold : selectedTypeBranchAt alphabet b =
        PactType.seq alphabet (PactType.message alphabet b.1.1 b.1.2)
          (b.2.reannotate alphabet) := rfl
    rw [hUnfold, typeFutureOffers_sequence, if_pos hCan, hHead, hOwn]
  have hWithin : ∀ rest : List (BareMessage × PactType),
      (∀ b ∈ rest, b.1 ∈ alphabet.actions) →
      (∀ b ∈ rest, b.2.alphabet = alphabet) →
      (∀ b ∈ rest, b.2.AlphabetWellFormed) →
      typeFutureOffers
          (parallelTypeBranchesSelectingWithin alphabet selected rest) =
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
    intro rest
    induction rest with
    | nil =>
        intro _ _ _
        simp [parallelTypeBranchesSelectingWithin, hSkip]
    | cons head tail ih =>
        intro hD hA hW
        cases tail with
        | nil =>
            by_cases hEq : head = selected
            · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq]
              rw [hSelected head (hD head (by simp)) (hA head (by simp))
                (hW head (by simp))]
              simp
            · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq]
              rw [hSingle head (hD head (by simp)) (hA head (by simp))
                (hW head (by simp))]
              simp
        | cons next tail' =>
            by_cases hEq : head = selected
            · simp only [parallelTypeBranchesSelectingWithin, if_pos hEq]
              rw [typeFutureOffers_parallel,
                hSelected head (hD head (by simp)) (hA head (by simp))
                  (hW head (by simp)),
                typeFutureOffers_parallelTypeBranchesWithin alphabet
                  (next :: tail')
                  (fun b hb => hD b (by simp [hb]))
                  (fun b hb => hA b (by simp [hb]))
                  (fun b hb => hW b (by simp [hb]))]
              rw [hHideEmpty]
              ext action
              simp only [List.foldl_cons, mem_foldl_offer_menu,
                Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
                false_or, or_assoc]
            · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq]
              rw [typeFutureOffers_parallel,
                hSingle head (hD head (by simp)) (hA head (by simp))
                  (hW head (by simp)),
                ih (fun b hb => hD b (by simp [hb]))
                  (fun b hb => hA b (by simp [hb]))
                  (fun b hb => hW b (by simp [hb]))]
              rw [hHideEmpty]
              ext action
              simp only [List.foldl_cons, mem_foldl_offer_menu,
                Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
                false_or, or_assoc]
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, hSkip]
  | cons head rest =>
      simp only [parallelTypeBranchesSelecting]
      exact hWithin (head :: rest) hDeclared hAlphabet hWF

end

end Pact
