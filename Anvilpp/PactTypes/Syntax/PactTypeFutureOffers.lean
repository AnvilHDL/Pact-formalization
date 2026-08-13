import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionLemmas

/-!
# Per-constructor typeFutureOffers equations, substitution, and marker-reachability transport
-/

namespace Pact

noncomputable section

/-- Syntax-derived futures of a sequence include the right menu exactly when
the left syntax may optimistically complete before the next clock. -/
theorem typeFutureOffers_sequence (left right : PactType) :
    typeFutureOffers (.seq left right) =
      if left.CanCompleteBeforeTock then
        typeFutureOffers left ∪ typeFutureOffers right
      else typeFutureOffers left := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  have hCompleteFuel : sizeOf left <
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.seq left right) + 1)
      (PactType.seq left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
      _ left hCompleteFuel,
    typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over ordinary choice. -/
theorem typeFutureOffers_choice (left right : PactType) :
    typeFutureOffers (.choice left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.choice left right) := by
    change sizeOf left + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.choice left right) := by
    change sizeOf right + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.choice left right) + 1)
      (PactType.choice left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over fair choice. -/
theorem typeFutureOffers_fairChoice
    (bid : BranchId) (left right : PactType) :
    typeFutureOffers (.fairChoice bid left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.fairChoice bid left right) := by
    change sizeOf left + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.fairChoice bid left right) := by
    change sizeOf right + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.fairChoice bid left right) + 1)
      (PactType.fairChoice bid left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures of an exclusive offer contain the else menu, every
branch head, and every branch continuation menu. -/
theorem typeFutureOffers_xoffer
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.xoffer elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  let fuel := sizeOf (PactType.xoffer elseType branches)
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
  change branches.foldl (fun offers branch =>
      offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
      (typeFutureOffersFuel fuel elseType) = _
  rw [typeFutureOffersFuel_eq_typeFutureOffers elseType fuel hElseFuel]
  exact hFold branches hBranchFuel (typeFutureOffers elseType)

/-- Conjunctive offers have the same optimistic syntax menu as exclusive
offers: the else continuation, every branch head, and every branch menu. -/
theorem typeFutureOffers_offer
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.offer elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  simpa only [typeFutureOffers, typeFutureOffersFuel] using
    typeFutureOffers_xoffer elseType branches

/-- Parallel future offers are the optimistic union of both syntax-derived
component menus, with the synchronization interface hidden. -/
theorem typeFutureOffers_parallel
    (left right : PactType) (interface : Interface) :
    typeFutureOffers (.par left right interface) =
      hideTypeOffers interface
        (typeFutureOffers left ∪ typeFutureOffers right) := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.par left right interface) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.par left right interface) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.par left right interface) + 1)
      (PactType.par left right interface) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- A recursion binder exposes the same syntactic same-cycle future menu as
its body; guardedness is used separately when replacing recursive calls. -/
theorem typeFutureOffers_recur (name : String) (body : PactType) :
    typeFutureOffers (.recur name body) = typeFutureOffers body := by
  have hBodyFuel : sizeOf body + 1 ≤ sizeOf (PactType.recur name body) := by
    simp_wf
    omega
  change typeFutureOffersFuel (sizeOf (PactType.recur name body) + 1)
      (PactType.recur name body) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers body _ hBodyFuel]

/-- Substituting syntax and then computing its optimistic future menu is
equivalent to interpreting the substituted variable directly in the
parameterized syntax fold.  This is capture-avoiding: a nested binder with the
same name stops the interpretation exactly where `replaceVar` stops. -/
theorem PactType.replaceVar_typeFutureOffers
    (name : String) (replacement processType : PactType) :
    typeFutureOffers (processType.replaceVar name replacement) =
      futureOffersSubst name replacement.CanCompleteBeforeTock
        (typeFutureOffers replacement) processType := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | h n ih =>
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | progress pid =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | tock =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | skip =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | var other =>
          by_cases hName : name = other
          · subst other
            simp [PactType.replaceVar, futureOffersSubst]
          · simp [PactType.replaceVar, futureOffersSubst, hName,
              typeFutureOffers, typeFutureOffersFuel]
      | recur other body =>
          by_cases hName : name = other
          · subst other
            simp [PactType.replaceVar, futureOffersSubst,
              typeFutureOffers_recur]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [PactType.replaceVar, hName, if_false,
              futureOffersSubst, typeFutureOffers_recur]
            exact ih (sizeOf body) hBodySize body rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_choice,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_fairChoice,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_sequence,
            futureOffersSubst]
          rw [PactType.replaceVar_canCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_parallel,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, entry ∈ branches) →
              ∀ initial,
                (PactType.replaceBranches rest name replacement).foldl
                    (fun offers branch =>
                      offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
                    initial =
                  initial ∪ branchFutureOffersSubst name
                    replacement.CanCompleteBeforeTock
                    (typeFutureOffers replacement) rest := by
            intro rest hRest
            induction rest with
            | nil =>
                intro initial
                simp [PactType.replaceBranches, branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                have hMember : (action, branchType) ∈ branches :=
                  hRest _ (by simp)
                have hBranchSize : sizeOf branchType < n := by
                  have hPair := List.sizeOf_lt_of_mem hMember
                  have hComponent : sizeOf branchType <
                      sizeOf (action, branchType) := by
                    simp_wf
                    omega
                  rw [← hSize]
                  simp_wf
                  omega
                simp only [PactType.replaceBranches, List.foldl_cons,
                  branchFutureOffersSubst]
                rw [ih (sizeOf branchType) hBranchSize branchType rfl,
                  hTail (fun other hOther => hRest other (by simp [hOther]))]
                simp only [Finset.union_assoc]
          simp only [PactType.replaceVar, typeFutureOffers_xoffer,
            futureOffersSubst]
          rw [ih (sizeOf elseType) hElseSize elseType rfl,
            hFold branches (by simp)]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, entry ∈ branches) →
              ∀ initial,
                (PactType.replaceBranches rest name replacement).foldl
                    (fun offers branch =>
                      offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
                    initial =
                  initial ∪ branchFutureOffersSubst name
                    replacement.CanCompleteBeforeTock
                    (typeFutureOffers replacement) rest := by
            intro rest hRest
            induction rest with
            | nil =>
                intro initial
                simp [PactType.replaceBranches, branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                have hMember : (action, branchType) ∈ branches :=
                  hRest _ (by simp)
                have hBranchSize : sizeOf branchType < n := by
                  have hPair := List.sizeOf_lt_of_mem hMember
                  have hComponent : sizeOf branchType <
                      sizeOf (action, branchType) := by
                    simp_wf
                    omega
                  rw [← hSize]
                  simp_wf
                  omega
                simp only [PactType.replaceBranches, List.foldl_cons,
                  branchFutureOffersSubst]
                rw [ih (sizeOf branchType) hBranchSize branchType rfl,
                  hTail (fun other hOther => hRest other (by simp [hOther]))]
                simp only [Finset.union_assoc]
          simp only [PactType.replaceVar, typeFutureOffers_offer,
            futureOffersSubst]
          rw [ih (sizeOf elseType) hElseSize elseType rfl,
            hFold branches (by simp)]

/-- Unfolding a clock-guarded recursive variable preserves the public
same-cycle future-offer menu. -/
theorem guardedOccurrences_replace_typeFutureOffers_recur
    (name : String) (body processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) :
    typeFutureOffers (processType.replaceVar name (.recur name body)) =
      typeFutureOffers processType := by
  unfold typeFutureOffers
  let unfolded := processType.replaceVar name (.recur name body)
  have hSize : sizeOf processType ≤ sizeOf unfolded := by
    exact PactType.sizeOf_le_replaceVar_recur processType name body
  have hFuel : sizeOf processType + 1 ≤ sizeOf unfolded + 1 := by omega
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hFuel
  rw [guardedOccurrences_replace_typeFutureOffersFuel
    name (.recur name body) processType hGuarded (sizeOf unfolded + 1)]
  rw [hExtra]
  exact typeFutureOffersFuel_add_stable processType
    (sizeOf processType + 1) extra (by omega)

/-- `GuardedOccurrences` is covariant in its guard proposition: weakening what
the guard must establish weakens the whole predicate.  The `.seq` clause passes
`guarded ∨ MustTockBeforeCompletion left` to its right component, so the
implication must be transported under that disjunction as well. -/
theorem PactType.guardedOccurrences_mono (name : String) {P Q : Prop}
    (hPQ : P → Q) :
    ∀ processType, GuardedOccurrences name P processType →
      GuardedOccurrences name Q processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType P Q with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          GuardedBranchOccurrences name P branches →
            GuardedBranchOccurrences name Q branches := by
        intro branches hBranchesSize h
        induction branches with
        | nil => simp [GuardedBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [GuardedBranchOccurrences] at h ⊢
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf
                omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hHead : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize hPQ branchType rfl h.1,
              restIH hRestSize h.2⟩
      cases processType with
      | message _ _ | progress _ | tock | skip =>
          simp [GuardedOccurrences]
      | var other =>
          intro h
          simp only [GuardedOccurrences] at h ⊢
          exact fun hEq => hPQ (h hEq)
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [GuardedOccurrences] at h ⊢
          by_cases hEq : other = name
          · rw [if_pos hEq]
            trivial
          · rw [if_neg hEq] at h ⊢
            exact ih (sizeOf body) hBodySize hPQ body rfl h
      | choice left right | fairChoice _ left right | par left right _ =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [GuardedOccurrences] at h ⊢
          exact ⟨ih (sizeOf left) hLeftSize hPQ left rfl h.1,
            ih (sizeOf right) hRightSize hPQ right rfl h.2⟩
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [GuardedOccurrences] at h ⊢
          refine ⟨ih (sizeOf left) hLeftSize hPQ left rfl h.1, ?_⟩
          exact ih (sizeOf right) hRightSize
            (fun hOr => hOr.elim (fun hp => Or.inl (hPQ hp)) Or.inr)
            right rfl h.2
      | xoffer elseType branches | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro h
          simp only [GuardedOccurrences] at h ⊢
          exact ⟨ih (sizeOf elseType) hElseSize hPQ elseType rfl h.1,
            hBranches branches hBranchesSize h.2⟩

/-- A structurally mandatory clock also blocks *parametric* same-cycle
completion, for every interpretation of the substituted variable.  A bare
`.var` is never `MustTockBeforeCompletion`, so no interpretation can revive
completion across a mandatory clock. -/
theorem PactType.mustTock_canCompleteBeforeTockSubst_false (name : String) :
    ∀ (value : Bool) (processType : PactType),
      MustTockBeforeCompletion processType →
        canCompleteBeforeTockSubst name value processType = false := by
  intro value processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType value with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          BranchesMustTockBeforeCompletion branches →
            branchCanCompleteBeforeTockSubst name value branches = false := by
        intro branches hBranchesSize h
        induction branches with
        | nil => simp [branchCanCompleteBeforeTockSubst]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [BranchesMustTockBeforeCompletion] at h
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf
                omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hHead : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            simp only [branchCanCompleteBeforeTockSubst,
              ih (sizeOf branchType) hBranchSize value branchType rfl h.1,
              restIH hRestSize h.2, Bool.or_self]
      cases processType with
      | message _ _ | progress _ | skip | var _ =>
          intro h
          simp [MustTockBeforeCompletion] at h
      | tock =>
          intro _
          simp [canCompleteBeforeTockSubst]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [MustTockBeforeCompletion] at h
          simp only [canCompleteBeforeTockSubst]
          by_cases hEq : name = other
          · rw [if_pos hEq, ← canCompleteBeforeTockSubst_false name body]
            exact ih (sizeOf body) hBodySize false body rfl h
          · rw [if_neg hEq]
            exact ih (sizeOf body) hBodySize value body rfl h
      | choice left right | fairChoice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [MustTockBeforeCompletion] at h
          simp only [canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize value left rfl h.1,
            ih (sizeOf right) hRightSize value right rfl h.2, Bool.or_self]
      | par left right _ =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [MustTockBeforeCompletion] at h
          simp only [canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize value left rfl h.1, Bool.false_and]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [MustTockBeforeCompletion] at h
          simp only [canCompleteBeforeTockSubst]
          rcases h with hLeft | hRight
          · simp [ih (sizeOf left) hLeftSize value left rfl hLeft]
          · simp [ih (sizeOf right) hRightSize value right rfl hRight]
      | xoffer elseType branches | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro h
          simp only [MustTockBeforeCompletion] at h
          simp only [canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize value elseType rfl h.1,
            hBranches branches hBranchesSize h.2, Bool.or_self]

/-- Completion companion of the menu collapse below: a clock-guarded variable
cannot influence same-cycle completion under any interpretation. -/
theorem PactType.canCompleteBeforeTockSubst_eq_of_guardedOccurrences_false
    (name : String) :
    ∀ (value : Bool) (processType : PactType),
      processType.GuardedOccurrences name False →
        canCompleteBeforeTockSubst name value processType =
          processType.CanCompleteBeforeTock := by
  intro value processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          GuardedBranchOccurrences name False branches →
            branchCanCompleteBeforeTockSubst name value branches =
              BranchCanCompleteBeforeTock branches := by
        intro branches hSizes hGuardedBranches
        induction branches with
        | nil =>
            simp [branchCanCompleteBeforeTockSubst,
              BranchCanCompleteBeforeTock]
        | cons entry rest restIH =>
            obtain ⟨action, branchType⟩ := entry
            simp only [GuardedBranchOccurrences] at hGuardedBranches
            simp only [branchCanCompleteBeforeTockSubst,
              BranchCanCompleteBeforeTock]
            rw [ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                branchType rfl hGuardedBranches.1,
              restIH (fun entry hEntry => hSizes entry (by simp [hEntry]))
                hGuardedBranches.2]
      cases processType with
      | message _ _ | progress _ | tock | skip =>
          intro _
          simp [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
      | var other =>
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hNe : name ≠ other := fun hEq => hGuarded hEq.symm
          simp [canCompleteBeforeTockSubst, hNe, CanCompleteBeforeTock]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          simp only [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
          by_cases hEq : name = other
          · rw [if_pos hEq]
          · rw [if_neg hEq, if_neg (fun h => hEq h.symm)] at *
            exact ih (sizeOf body) hBodySize body rfl hGuarded
      | choice left right | fairChoice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          simp only [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
          rw [ih (sizeOf left) hLeftSize left rfl hGuarded.1,
            ih (sizeOf right) hRightSize right rfl hGuarded.2]
      | par left right _ =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          simp only [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
          rw [ih (sizeOf left) hLeftSize left rfl hGuarded.1,
            ih (sizeOf right) hRightSize right rfl hGuarded.2]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          simp only [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
          by_cases hTock : left.MustTockBeforeCompletion
          · have hSubstFalse : canCompleteBeforeTockSubst name value left =
                false :=
              mustTock_canCompleteBeforeTockSubst_false name value left hTock
            have hPlainFalse : left.CanCompleteBeforeTock = false := by
              rw [← canCompleteBeforeTockSubst_false name left]
              exact mustTock_canCompleteBeforeTockSubst_false name false left
                hTock
            rw [hSubstFalse, hPlainFalse, Bool.false_and, Bool.false_and]
          · have hRightGuarded : right.GuardedOccurrences name False :=
              guardedOccurrences_mono name
                (fun hOr => hOr.elim id (fun hMust => absurd hMust hTock))
                right hGuarded.2
            rw [ih (sizeOf left) hLeftSize left rfl hGuarded.1,
              ih (sizeOf right) hRightSize right rfl hRightGuarded]
      | xoffer elseType branches | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hBranchSizes : ∀ entry ∈ branches, sizeOf entry.2 < n := by
            intro entry hEntry
            have hPair := List.sizeOf_lt_of_mem hEntry
            have hComponent : sizeOf entry.2 < sizeOf entry := by
              rcases entry
              simp_wf
              omega
            rw [← hSize]
            simp_wf
            omega
          simp only [canCompleteBeforeTockSubst, CanCompleteBeforeTock]
          rw [ih (sizeOf elseType) hElseSize elseType rfl hGuarded.1,
            hBranches branches hBranchSizes hGuarded.2]

/-- When every free occurrence of `name` is clock-guarded, the parametric
future menu does not depend on the interpretation at all: it collapses to the
ordinary syntax menu, for **every** `value`/`menu` pair.

This is the fixed-point fact that makes the recursion future leaf well-founded.
`guardedOccurrences_replace_typeFutureOffers_recur` only supplies the instance
where the interpretation comes from an actual replacement type; the recursion
graph instead supplies an interpretation read off the compiled automaton, which
is not a priori of that form.  The `.seq` case is the only one with content:
if the left component must tock, the substituted completion test is `false`
by `mustTock_canCompleteBeforeTockSubst_false`, so the right menu — the only
place an unguarded occurrence could hide — is never unioned in. -/
theorem PactType.futureOffersSubst_eq_of_guardedOccurrences_false
    (name : String) :
    ∀ (value : Bool) (menu : Finset BareMessage) (processType : PactType),
      processType.GuardedOccurrences name False →
        futureOffersSubst name value menu processType =
          typeFutureOffers processType := by
  intro value menu processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir =>
          intro _
          simp [futureOffersSubst, typeFutureOffers, typeFutureOffersFuel]
      | progress _ | tock | skip =>
          intro _
          simp [futureOffersSubst, typeFutureOffers, typeFutureOffersFuel]
      | var other =>
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hNe : name ≠ other := by
            intro hEq
            exact hGuarded hEq.symm
          simp [futureOffersSubst, hNe, typeFutureOffers, typeFutureOffersFuel]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          simp only [futureOffersSubst]
          by_cases hEq : name = other
          · rw [if_pos hEq, typeFutureOffers_recur]
          · rw [if_neg hEq, if_neg (fun h => hEq h.symm)] at *
            rw [ih (sizeOf body) hBodySize body rfl hGuarded,
              typeFutureOffers_recur]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          rw [futureOffersSubst, typeFutureOffers_choice,
            ih (sizeOf left) hLeftSize left rfl hGuarded.1,
            ih (sizeOf right) hRightSize right rfl hGuarded.2]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          rw [futureOffersSubst, typeFutureOffers_fairChoice,
            ih (sizeOf left) hLeftSize left rfl hGuarded.1,
            ih (sizeOf right) hRightSize right rfl hGuarded.2]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          rw [futureOffersSubst, typeFutureOffers_parallel,
            ih (sizeOf left) hLeftSize left rfl hGuarded.1,
            ih (sizeOf right) hRightSize right rfl hGuarded.2]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hLeftMenu := ih (sizeOf left) hLeftSize left rfl hGuarded.1
          by_cases hTock : left.MustTockBeforeCompletion
          · -- A mandatory clock in `left` blocks both completion tests, so the
            -- right menu (the only place an unguarded occurrence can hide) is
            -- never consulted on either side.
            have hSubstFalse : canCompleteBeforeTockSubst name value left =
                false :=
              mustTock_canCompleteBeforeTockSubst_false name value left hTock
            have hPlainFalse : left.CanCompleteBeforeTock = false := by
              rw [← canCompleteBeforeTockSubst_false name left]
              exact mustTock_canCompleteBeforeTockSubst_false name false left
                hTock
            rw [futureOffersSubst, typeFutureOffers_sequence, hSubstFalse,
              hPlainFalse, if_neg (by simp), if_neg (by simp), hLeftMenu]
          · -- Without a mandatory clock the guard passed to `right` collapses
            -- to `False`, so the induction hypothesis applies there too.
            have hRightGuarded : right.GuardedOccurrences name False :=
              guardedOccurrences_mono name
                (fun hOr => hOr.elim id (fun hMust => absurd hMust hTock))
                right hGuarded.2
            have hRightMenu := ih (sizeOf right) hRightSize right rfl
              hRightGuarded
            have hCompleteEq : canCompleteBeforeTockSubst name value left =
                left.CanCompleteBeforeTock :=
              canCompleteBeforeTockSubst_eq_of_guardedOccurrences_false name
                value left hGuarded.1
            rw [futureOffersSubst, typeFutureOffers_sequence, hLeftMenu,
              hRightMenu, hCompleteEq]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, sizeOf entry.2 < n) →
              GuardedBranchOccurrences name False rest →
              ∀ initial,
                rest.foldl (fun offers branch =>
                    offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial =
                  initial ∪
                    branchFutureOffersSubst name value menu rest := by
            intro rest hSizes hRestGuarded
            induction rest with
            | nil =>
                intro initial
                simp [branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                simp only [GuardedBranchOccurrences] at hRestGuarded
                simp only [List.foldl_cons, branchFutureOffersSubst]
                rw [← ih (sizeOf branchType)
                    (hSizes (action, branchType) (by simp)) branchType
                    rfl hRestGuarded.1,
                  hTail (fun entry hEntry => hSizes entry (by simp [hEntry]))
                    hRestGuarded.2]
                simp only [Finset.union_assoc]
          have hBranchSizes : ∀ entry ∈ branches, sizeOf entry.2 < n := by
            intro entry hEntry
            have hPair := List.sizeOf_lt_of_mem hEntry
            have hComponent : sizeOf entry.2 < sizeOf entry := by
              rcases entry
              simp_wf
              omega
            rw [← hSize]
            simp_wf
            omega
          rw [futureOffersSubst, typeFutureOffers_xoffer,
            ih (sizeOf elseType) hElseSize elseType rfl hGuarded.1,
            hFold branches hBranchSizes hGuarded.2]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          intro hGuarded
          simp only [GuardedOccurrences] at hGuarded
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, sizeOf entry.2 < n) →
              GuardedBranchOccurrences name False rest →
              ∀ initial,
                rest.foldl (fun offers branch =>
                    offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial =
                  initial ∪
                    branchFutureOffersSubst name value menu rest := by
            intro rest hSizes hRestGuarded
            induction rest with
            | nil =>
                intro initial
                simp [branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                simp only [GuardedBranchOccurrences] at hRestGuarded
                simp only [List.foldl_cons, branchFutureOffersSubst]
                rw [← ih (sizeOf branchType)
                    (hSizes (action, branchType) (by simp)) branchType
                    rfl hRestGuarded.1,
                  hTail (fun entry hEntry => hSizes entry (by simp [hEntry]))
                    hRestGuarded.2]
                simp only [Finset.union_assoc]
          have hBranchSizes : ∀ entry ∈ branches, sizeOf entry.2 < n := by
            intro entry hEntry
            have hPair := List.sizeOf_lt_of_mem hEntry
            have hComponent : sizeOf entry.2 < sizeOf entry := by
              rcases entry
              simp_wf
              omega
            rw [← hSize]
            simp_wf
            omega
          rw [futureOffersSubst, typeFutureOffers_offer,
            ih (sizeOf elseType) hElseSize elseType rfl hGuarded.1,
            hFold branches hBranchSizes hGuarded.2]

mutual
  /-- Whether a recursive-call marker for `name` can still be met while the
  optimistic same-cycle future menu is being collected.  This is the syntactic
  counterpart of "some `MarkerSource` is future-reachable" in the compiled
  graph.

  It is deliberately *not* `canCompleteBeforeTockSubst name true`: the two
  agree everywhere except at a shadowing `.recur name _`, where completion
  still reads the body but a marker for the outer `name` is captured and can
  no longer be reached.  The `.seq` clause consults the right component only
  when the left can finish in this cycle, and `.par` is `false` because tail
  occurrence forbids a marker below a product in the first place. -/
  def PactType.markerReachableSubst (name : String) : PactType → Bool
    | .message _ _ | .progress _ | .tock | .skip => false
    | .var other => if name = other then true else false
    | .recur other body =>
        if name = other then false else markerReachableSubst name body
    | .choice left right | .fairChoice _ left right =>
        markerReachableSubst name left || markerReachableSubst name right
    | .seq left right =>
        left.CanCompleteBeforeTock && markerReachableSubst name right
    | .par _ _ _ => false
    | .xoffer elseType branches | .offer elseType branches =>
        markerReachableSubst name elseType ||
          branchMarkerReachableSubst name branches
  termination_by processType => sizeOf processType

  /-- Branch-list component of `markerReachableSubst`. -/
  def PactType.branchMarkerReachableSubst (name : String) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        markerReachableSubst name processType ||
          branchMarkerReachableSubst name rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- If `name` does not occur at all, the parametric future menu is the
ordinary one.  Unlike the clock-guarded collapse proved above, this needs no
`MustTockBeforeCompletion` reasoning: the interpretation is simply never
consulted. -/
theorem PactType.futureOffersSubst_eq_of_tailOccurrences_false
    (name : String) (value : Bool) (menu : Finset BareMessage) :
    ∀ processType, processType.TailOccurrences name False →
      futureOffersSubst name value menu processType =
        typeFutureOffers processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          TailBranchOccurrences name False branches →
          ∀ initial,
            branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial =
              initial ∪ branchFutureOffersSubst name value menu branches := by
        intro branches hSizes hTail
        induction branches with
        | nil => intro initial; simp [branchFutureOffersSubst]
        | cons entry tail hTail' =>
            obtain ⟨action, branchType⟩ := entry
            intro initial
            simp only [TailBranchOccurrences] at hTail
            simp only [List.foldl_cons, branchFutureOffersSubst]
            rw [← ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                branchType rfl hTail.1,
              hTail' (fun entry hEntry => hSizes entry (by simp [hEntry]))
                hTail.2]
            simp only [Finset.union_assoc]
      have hBranchSizes : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ entry ∈ branches, sizeOf entry.2 < n := by
        intro branches hBranchesSize entry hEntry
        have hPair := List.sizeOf_lt_of_mem hEntry
        have hComponent : sizeOf entry.2 < sizeOf entry := by
          rcases entry
          simp_wf
          omega
        omega
      cases processType with
      | message msg dir =>
          intro _
          simp [futureOffersSubst, typeFutureOffers, typeFutureOffersFuel]
      | progress _ | tock | skip =>
          intro _
          simp [futureOffersSubst, typeFutureOffers, typeFutureOffersFuel]
      | var other =>
          intro hTail
          simp only [TailOccurrences] at hTail
          have hNe : name ≠ other := fun hEq => hTail hEq.symm
          simp [futureOffersSubst, hNe, typeFutureOffers, typeFutureOffersFuel]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [futureOffersSubst]
          by_cases hEq : name = other
          · rw [if_pos hEq, typeFutureOffers_recur]
          · rw [if_neg hEq, if_neg (fun h => hEq h.symm)] at *
            rw [ih (sizeOf body) hBodySize body rfl hTail, typeFutureOffers_recur]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_choice,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_fairChoice,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_parallel,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_sequence,
            canCompleteBeforeTockSubst_eq_of_tailOccurrences_false name value
              left hTail.1,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_xoffer,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1,
            hBranches branches (hBranchSizes branches hBranchesSize) hTail.2]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, typeFutureOffers_offer,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1,
            hBranches branches (hBranchSizes branches hBranchesSize) hTail.2]

/-- A name that does not occur has no reachable marker. -/
theorem PactType.markerReachableSubst_eq_false_of_tailOccurrences_false
    (name : String) :
    ∀ processType, processType.TailOccurrences name False →
      markerReachableSubst name processType = false := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          TailBranchOccurrences name False branches →
            branchMarkerReachableSubst name branches = false := by
        intro branches hSizes hTail
        induction branches with
        | nil => simp [branchMarkerReachableSubst]
        | cons entry tail hTail' =>
            obtain ⟨action, branchType⟩ := entry
            simp only [TailBranchOccurrences] at hTail
            simp only [branchMarkerReachableSubst,
              ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                branchType rfl hTail.1,
              hTail' (fun entry hEntry => hSizes entry (by simp [hEntry]))
                hTail.2, Bool.or_self]
      have hBranchSizes : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ entry ∈ branches, sizeOf entry.2 < n := by
        intro branches hBranchesSize entry hEntry
        have hPair := List.sizeOf_lt_of_mem hEntry
        have hComponent : sizeOf entry.2 < sizeOf entry := by
          rcases entry
          simp_wf
          omega
        omega
      cases processType with
      | message _ _ | progress _ | tock | skip =>
          intro _; simp [markerReachableSubst]
      | var other =>
          intro hTail
          simp only [TailOccurrences] at hTail
          have hNe : name ≠ other := fun hEq => hTail hEq.symm
          simp [markerReachableSubst, hNe]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [markerReachableSubst]
          by_cases hEq : name = other
          · rw [if_pos hEq]
          · rw [if_neg hEq, if_neg (fun h => hEq h.symm)] at *
            exact ih (sizeOf body) hBodySize body rfl hTail
      | choice left right | fairChoice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [markerReachableSubst,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2, Bool.or_self]
      | seq left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [markerReachableSubst,
            ih (sizeOf right) hRightSize right rfl hTail.2, Bool.and_false]
      | par left right _ =>
          intro _; simp [markerReachableSubst]
      | xoffer elseType branches | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [markerReachableSubst,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1,
            hBranches branches (hBranchSizes branches hBranchesSize) hTail.2,
            Bool.or_self]

/-- `TailOccurrences` is covariant in its tail proposition.  The `.seq` left
component, `.par`, and `.offer` branches are pinned to `False` in both
instances, so only the genuinely tail-carrying positions move. -/
theorem PactType.tailOccurrences_mono (name : String) {P Q : Prop}
    (hPQ : P → Q) :
    ∀ processType, TailOccurrences name P processType →
      TailOccurrences name Q processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType P Q with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          TailBranchOccurrences name P branches →
            TailBranchOccurrences name Q branches := by
        intro branches hSizes h
        induction branches with
        | nil => simp [TailBranchOccurrences]
        | cons entry rest restIH =>
            obtain ⟨action, branchType⟩ := entry
            simp only [TailBranchOccurrences] at h ⊢
            exact ⟨ih (sizeOf branchType)
                (hSizes (action, branchType) (by simp)) hPQ branchType rfl h.1,
              restIH (fun e hE => hSizes e (by simp [hE])) h.2⟩
      have hBranchSizes : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ entry ∈ branches, sizeOf entry.2 < n := by
        intro branches hBranchesSize entry hEntry
        have hPair := List.sizeOf_lt_of_mem hEntry
        have hComponent : sizeOf entry.2 < sizeOf entry := by
          rcases entry
          simp_wf
          omega
        omega
      cases processType with
      | message _ _ | progress _ | tock | skip => simp [TailOccurrences]
      | var other =>
          intro h
          simp only [TailOccurrences] at h ⊢
          exact fun hEq => hPQ (h hEq)
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [TailOccurrences] at h ⊢
          by_cases hEq : other = name
          · rw [if_pos hEq]; trivial
          · rw [if_neg hEq] at h ⊢
            exact ih (sizeOf body) hBodySize hPQ body rfl h
      | choice left right | fairChoice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [TailOccurrences] at h ⊢
          exact ⟨ih (sizeOf left) hLeftSize hPQ left rfl h.1,
            ih (sizeOf right) hRightSize hPQ right rfl h.2⟩
      | seq left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro h
          simp only [TailOccurrences] at h ⊢
          exact ⟨h.1, ih (sizeOf right) hRightSize hPQ right rfl h.2⟩
      | par left right _ =>
          intro h
          simpa only [TailOccurrences] using h
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro h
          simp only [TailOccurrences] at h ⊢
          exact ⟨ih (sizeOf elseType) hElseSize hPQ elseType rfl h.1,
            hBranches branches (hBranchSizes branches hBranchesSize) h.2⟩
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          intro h
          simp only [TailOccurrences] at h ⊢
          exact ⟨ih (sizeOf elseType) hElseSize hPQ elseType rfl h.1, h.2⟩

private theorem foldl_branchFuture_shift :
    ∀ (branches : List (BareMessage × PactType))
      (base extra : Finset BareMessage),
      branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) (base ∪ extra) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) base ∪ extra := by
  intro branches
  induction branches with
  | nil => intro base extra; simp
  | cons branch rest ih =>
      intro base extra
      simp only [List.foldl_cons]
      rw [show base ∪ extra ∪ {branch.1} ∪ typeFutureOffers branch.2 =
          base ∪ {branch.1} ∪ typeFutureOffers branch.2 ∪ extra from by ac_rfl]
      exact ih _ extra

private theorem foldl_branchFuture_base
    (branches : List (BareMessage × PactType)) (base : Finset BareMessage) :
    branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2) base =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ ∪ base := by
  simpa using foldl_branchFuture_shift branches ∅ base

private theorem ite_or_union_menu (a b : Bool) (menu : Finset BareMessage) :
    (if a || b then menu else ∅) =
      (if a then menu else ∅) ∪ (if b then menu else ∅) := by
  cases a <;> cases b <;> simp

/-- **The parametric future menu splits.**  Under tail occurrence, the
interpretation `menu` contributes exactly when a recursive-call marker is
still reachable; otherwise the parametric menu is the ordinary one.

This is the syntax half of the recursion future bridge, matching the graph
half `mem_computeFuture_markerAugmented`: there the activation menu is added
exactly when a `MarkerSource` is future-reachable. -/
theorem PactType.futureOffersSubst_eq_union_marker
    (name : String) (value : Bool) (menu : Finset BareMessage) :
    ∀ processType, processType.TailOccurrences name True →
      futureOffersSubst name value menu processType =
        typeFutureOffers processType ∪
          (if markerReachableSubst name processType then menu else ∅) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranchSizes : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ entry ∈ branches, sizeOf entry.2 < n := by
        intro branches hBranchesSize entry hEntry
        have hPair := List.sizeOf_lt_of_mem hEntry
        have hComponent : sizeOf entry.2 < sizeOf entry := by
          rcases entry
          simp_wf
          omega
        omega
      have hFold : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          TailBranchOccurrences name True branches →
            branchFutureOffersSubst name value menu branches =
              branches.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ ∪
                (if branchMarkerReachableSubst name branches then menu
                  else ∅) := by
        intro branches hSizes hTail
        induction branches with
        | nil => simp [branchFutureOffersSubst, branchMarkerReachableSubst]
        | cons entry tail hTail' =>
            obtain ⟨action, branchType⟩ := entry
            simp only [TailBranchOccurrences] at hTail
            simp only [branchFutureOffersSubst, branchMarkerReachableSubst,
              List.foldl_cons, ite_or_union_menu]
            rw [ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                branchType rfl hTail.1,
              hTail' (fun e hE => hSizes e (by simp [hE])) hTail.2,
              foldl_branchFuture_base tail (∅ ∪ {action} ∪
                typeFutureOffers branchType)]
            simp only [Finset.empty_union]
            ac_rfl
      cases processType with
      | message msg dir =>
          intro _
          simp [futureOffersSubst, markerReachableSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | progress _ | tock | skip =>
          intro _
          simp [futureOffersSubst, markerReachableSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | var other =>
          intro _
          by_cases hEq : name = other
          · simp [futureOffersSubst, markerReachableSubst, hEq,
              typeFutureOffers, typeFutureOffersFuel]
          · simp [futureOffersSubst, markerReachableSubst, hEq,
              typeFutureOffers, typeFutureOffersFuel]
      | recur other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          simp only [futureOffersSubst, markerReachableSubst]
          by_cases hEq : name = other
          · rw [if_pos hEq, if_pos hEq, typeFutureOffers_recur]
            simp
          · have hOther : ¬ (other = name) := fun h => hEq h.symm
            rw [if_neg hOther] at hTail
            rw [if_neg hEq, if_neg hEq, typeFutureOffers_recur,
              ih (sizeOf body) hBodySize body rfl hTail]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, markerReachableSubst, typeFutureOffers_choice,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2,
            ite_or_union_menu]
          ac_rfl
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, markerReachableSubst,
            typeFutureOffers_fairChoice,
            ih (sizeOf left) hLeftSize left rfl hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2,
            ite_or_union_menu]
          ac_rfl
      | par left right interface =>
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, markerReachableSubst,
            typeFutureOffers_parallel,
            futureOffersSubst_eq_of_tailOccurrences_false name value menu left
              hTail.1,
            futureOffersSubst_eq_of_tailOccurrences_false name value menu right
              hTail.2]
          simp
      | seq left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, markerReachableSubst,
            typeFutureOffers_sequence,
            canCompleteBeforeTockSubst_eq_of_tailOccurrences_false name value
              left hTail.1,
            futureOffersSubst_eq_of_tailOccurrences_false name value menu left
              hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2]
          by_cases hComplete : left.CanCompleteBeforeTock
          · rw [if_pos hComplete, if_pos hComplete]
            simp only [hComplete, Bool.true_and]
            ac_rfl
          · rw [if_neg hComplete, if_neg hComplete]
            simp only [Bool.eq_false_iff.mpr hComplete, Bool.false_and]
            simp
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          rw [futureOffersSubst, markerReachableSubst, typeFutureOffers_xoffer,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1,
            ite_or_union_menu,
            hFold branches (hBranchSizes branches hBranchesSize) hTail.2,
            foldl_branchFuture_base branches (typeFutureOffers elseType)]
          ac_rfl
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail
          simp only [TailOccurrences] at hTail
          have hBranchesTrue : TailBranchOccurrences name True branches := by
            have hMono : ∀ branches : List (BareMessage × PactType),
                TailBranchOccurrences name False branches →
                  TailBranchOccurrences name True branches := by
              intro bs h
              induction bs with
              | nil => simp [TailBranchOccurrences]
              | cons e rest restIH =>
                  obtain ⟨action, branchType⟩ := e
                  simp only [TailBranchOccurrences] at h ⊢
                  exact ⟨tailOccurrences_mono name (fun hFalse => hFalse.elim)
                      branchType h.1,
                    restIH h.2⟩
            exact hMono branches hTail.2
          rw [futureOffersSubst, markerReachableSubst, typeFutureOffers_offer,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1,
            ite_or_union_menu,
            hFold branches (hBranchSizes branches hBranchesSize) hBranchesTrue,
            foldl_branchFuture_base branches (typeFutureOffers elseType)]
          ac_rfl

/-- **Marker reachability under substitution.**  Replacing a *different*
binder's variable by its own recursion either leaves the outer marker where it
was, or exposes it through the replacement — the latter exactly when the inner
marker was itself same-cycle reachable.

`BinderFreshFor [name]` rules out a shadowing `.recur name _`, where the left
side is captured while the right side is not.  `TailOccurrences other True`
is needed only in the sequence clause, where it forces `other` to be absent
from the left component and therefore fixes its completion analysis. -/
theorem PactType.markerReachableSubst_replaceVar
    (name other : String) (replacement : PactType) (hDistinct : name ≠ other) :
    ∀ processType : PactType,
      processType.TailOccurrences other True →
      processType.BinderFreshFor [name] →
        markerReachableSubst name (processType.replaceVar other replacement) =
          (markerReachableSubst name processType ||
            (markerReachableSubst other processType &&
              markerReachableSubst name replacement)) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranchSizes : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ entry ∈ branches, sizeOf entry.2 < n := by
        intro branches hBranchesSize entry hEntry
        have hPair := List.sizeOf_lt_of_mem hEntry
        have hComponent : sizeOf entry.2 < sizeOf entry := by
          rcases entry
          simp_wf
          omega
        omega
      have hBranches : ∀ branches : List (BareMessage × PactType),
          (∀ entry ∈ branches, sizeOf entry.2 < n) →
          TailBranchOccurrences other True branches →
          BinderFreshForBranches [name] branches →
            branchMarkerReachableSubst name
                (replaceBranches branches other replacement) =
              (branchMarkerReachableSubst name branches ||
                (branchMarkerReachableSubst other branches &&
                  markerReachableSubst name replacement)) := by
        intro branches hSizes hTail hFresh
        induction branches with
        | nil => simp [replaceBranches, branchMarkerReachableSubst]
        | cons entry tail restIH =>
            obtain ⟨action, branchType⟩ := entry
            simp only [TailBranchOccurrences] at hTail
            simp only [BinderFreshForBranches] at hFresh
            rw [replaceBranches, branchMarkerReachableSubst,
              branchMarkerReachableSubst, branchMarkerReachableSubst,
              ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                branchType rfl hTail.1 hFresh.1,
              restIH (fun entry hEntry => hSizes entry (by simp [hEntry]))
                hTail.2 hFresh.2]
            cases markerReachableSubst name branchType <;>
              cases markerReachableSubst other branchType <;>
              cases branchMarkerReachableSubst name tail <;>
              cases branchMarkerReachableSubst other tail <;>
              cases markerReachableSubst name replacement <;> rfl
      cases processType with
      | message msg dir =>
          intro _ _
          simp [replaceVar, markerReachableSubst]
      | progress _ | tock | skip =>
          intro _ _
          simp [replaceVar, markerReachableSubst]
      | var current =>
          intro _ _
          by_cases hEq : other = current
          · subst current
            simp [replaceVar, markerReachableSubst, hDistinct]
          · simp [replaceVar, markerReachableSubst, hEq]
      | recur current body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [BinderFreshFor] at hFresh
          have hNotName : ¬ current = name := by
            intro hEq
            exact hFresh.1 (by simp [hEq])
          by_cases hEq : other = current
          · subst current
            simp [replaceVar, markerReachableSubst]
          · have hCurrentOther : ¬ current = other := fun h => hEq h.symm
            have hNameCurrent : ¬ name = current := fun h => hNotName h.symm
            simp only [TailOccurrences, if_neg hCurrentOther] at hTail
            rw [replaceVar, if_neg hEq, markerReachableSubst,
              markerReachableSubst, markerReachableSubst,
              if_neg hNameCurrent, if_neg hNameCurrent, if_neg hEq,
              ih (sizeOf body) hBodySize body rfl hTail hFresh.2]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [TailOccurrences] at hTail
          simp only [BinderFreshFor] at hFresh
          rw [replaceVar, markerReachableSubst, markerReachableSubst,
            markerReachableSubst,
            ih (sizeOf left) hLeftSize left rfl hTail.1 hFresh.1,
            ih (sizeOf right) hRightSize right rfl hTail.2 hFresh.2]
          cases markerReachableSubst name left <;>
            cases markerReachableSubst other left <;>
            cases markerReachableSubst name right <;>
            cases markerReachableSubst other right <;>
            cases markerReachableSubst name replacement <;> rfl
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [TailOccurrences] at hTail
          simp only [BinderFreshFor] at hFresh
          rw [replaceVar, markerReachableSubst, markerReachableSubst,
            markerReachableSubst,
            ih (sizeOf left) hLeftSize left rfl hTail.1 hFresh.1,
            ih (sizeOf right) hRightSize right rfl hTail.2 hFresh.2]
          cases markerReachableSubst name left <;>
            cases markerReachableSubst other left <;>
            cases markerReachableSubst name right <;>
            cases markerReachableSubst other right <;>
            cases markerReachableSubst name replacement <;> rfl
      | par left right interface =>
          intro _ _
          simp [replaceVar, markerReachableSubst]
      | seq left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [TailOccurrences] at hTail
          simp only [BinderFreshFor] at hFresh
          rw [replaceVar, markerReachableSubst, markerReachableSubst,
            markerReachableSubst,
            replaceVar_eq_self_of_tailOccurrences_false other replacement left
              hTail.1,
            ih (sizeOf right) hRightSize right rfl hTail.2 hFresh.2]
          cases left.CanCompleteBeforeTock <;>
            cases markerReachableSubst name right <;>
            cases markerReachableSubst other right <;>
            cases markerReachableSubst name replacement <;> rfl
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [TailOccurrences] at hTail
          simp only [BinderFreshFor] at hFresh
          rw [replaceVar, markerReachableSubst, markerReachableSubst,
            markerReachableSubst,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1 hFresh.1,
            hBranches branches (hBranchSizes branches hBranchesSize) hTail.2
              hFresh.2]
          cases markerReachableSubst name elseType <;>
            cases markerReachableSubst other elseType <;>
            cases branchMarkerReachableSubst name branches <;>
            cases branchMarkerReachableSubst other branches <;>
            cases markerReachableSubst name replacement <;> rfl
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          intro hTail hFresh
          simp only [TailOccurrences] at hTail
          simp only [BinderFreshFor] at hFresh
          have hBranchesTrue : TailBranchOccurrences other True branches := by
            have hMono : ∀ list : List (BareMessage × PactType),
                TailBranchOccurrences other False list →
                  TailBranchOccurrences other True list := by
              intro list
              induction list with
              | nil => intro _; simp [TailBranchOccurrences]
              | cons entry rest restIH =>
                  obtain ⟨action, branchType⟩ := entry
                  intro h
                  simp only [TailBranchOccurrences] at h ⊢
                  exact ⟨tailOccurrences_mono other
                      (fun hFalse => hFalse.elim) branchType h.1, restIH h.2⟩
            exact hMono branches hTail.2
          rw [replaceVar, markerReachableSubst, markerReachableSubst,
            markerReachableSubst,
            ih (sizeOf elseType) hElseSize elseType rfl hTail.1 hFresh.1,
            hBranches branches (hBranchSizes branches hBranchesSize)
              hBranchesTrue hFresh.2]
          cases markerReachableSubst name elseType <;>
            cases markerReachableSubst other elseType <;>
            cases branchMarkerReachableSubst name branches <;>
            cases branchMarkerReachableSubst other branches <;>
            cases markerReachableSubst name replacement <;> rfl

/-- Specialization of `replaceVar_typeFutureOffers` to a recursion binder
substituting itself.  This is the exact right-hand side of
`RecursionBodyFutureCorrect`, rewritten into the parametric form whose
interpretation constants (`body.CanCompleteBeforeTock`, `typeFutureOffers
body`) are fixed throughout a structural descent into `body` — mirroring the
way `canCompleteBeforeTockSubst name body.CanCompleteBeforeTock` is the fixed
right-hand side of the already-proved recursion *completion* leaf. -/
theorem PactType.replaceVar_typeFutureOffers_recur
    (name : String) (body residual : PactType) :
    typeFutureOffers (residual.replaceVar name (.recur name body)) =
      futureOffersSubst name body.CanCompleteBeforeTock
        (typeFutureOffers body) residual := by
  have hComplete : (PactType.recur name body).CanCompleteBeforeTock =
      body.CanCompleteBeforeTock := by
    simp [CanCompleteBeforeTock]
  have hFuture : typeFutureOffers (PactType.recur name body) =
      typeFutureOffers body := typeFutureOffers_recur name body
  rw [replaceVar_typeFutureOffers, hComplete, hFuture]

/-- Regression for optimistic, syntax-derived futures: after selecting the
left choice, both distinct sends can still occur before the next clock. -/
theorem syntactic_optimistic_sequence_future_regression :
    typeFutureOffers
        (.seq (.choice (.message "a" .send) .skip) (.message "b" .send)) =
      {("a", .send), ("b", .send)} := by
  decide

/-- Branch offers selected by the future part of this environment. -/
def typeWaitingOffers (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (env.future.image typeNeed) ∩ typeBranchActions branches

/-
Environment-indexed current/future offers and the sibling-local environment
relation are mutually defined: parallel offers depend on the two local steps,
while each local environment depends on the sibling step's offers.
-/
mutual
  @[aesop unsafe]
  inductive TypeOffers :
      TypeEnvironment → PactType → TypeLabel → PactType →
        Finset BareMessage → Finset BareMessage → Prop where
    | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ env.hasNeed (msg, dir) →
        TypeOffers env (.message msg dir) (TypeLabel.message msg dir) .skip
          {(msg, dir)} (typeFutureOffers .skip)
    | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
        TypeOffers env (.message msg dir) TypeLabel.silent (.message msg dir)
          {(msg, dir)} (typeFutureOffers (.message msg dir) \ {(msg, dir)})
    | choice_left (env : TypeEnvironment) (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.choice left right) TypeLabel.silent left
          ∅ (typeFutureOffers left)
    | choice_right (env : TypeEnvironment) (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.choice left right) TypeLabel.silent right
          ∅ (typeFutureOffers right)
    | fair_left (env : TypeEnvironment) (bid : BranchId)
        (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.fairChoice bid left right) (TypeLabel.fair bid true) left
          ∅ (typeFutureOffers left)
    | fair_right (env : TypeEnvironment) (bid : BranchId)
        (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.fairChoice bid left right) (TypeLabel.fair bid false) right
          ∅ (typeFutureOffers right)
    | cycle (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = true →
        TypeOffers env .tock .tock .skip ∅ ∅
    | cycle_wait (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env .tock TypeLabel.silent .tock ∅ ∅
    | skip (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = false ∧ env.immediate = ∅ →
        TypeOffers env .skip TypeLabel.silent .skip ∅ ∅
    | skip_seq (env : TypeEnvironment) (processType : PactType) :
        env.WellFormed →
        TypeOffers env (.seq .skip processType) TypeLabel.silent processType
          ∅ (typeFutureOffers processType)
    | progress (env : TypeEnvironment) (pid : ProcId) :
        env.WellFormed →
        TypeOffers env (.progress pid) (TypeLabel.progress pid) .skip ∅ ∅
    | recur (env : TypeEnvironment) (name : String) (body : PactType) :
        env.WellFormed →
        TypeOffers env (.recur name body) TypeLabel.silent
          (body.replaceVar name (.recur name body)) ∅
          (typeFutureOffers (body.replaceVar name (.recur name body)))
    | seq (env : TypeEnvironment) (left left' right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label left' current childFuture →
        TypeOffers env (.seq left right) label (.seq left' right) current
          (typeFutureOffers (.seq left' right) \ current)
    | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (action : BareMessage) (processType : PactType) :
        env.WellFormed ∧
          (action, processType) ∈ branches ∧
          TypeBranchEnabled env (action, processType) ∧
          TypeResolved env branches →
        TypeOffers env (.xoffer elseType branches)
          (TypeLabel.message action.1 action.2) processType
          {action} (typeFutureOffers processType)
    | xoffer_else (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.xoffer elseType branches) TypeLabel.silent elseType
          ∅ (typeFutureOffers elseType)
    | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.xoffer elseType branches) TypeLabel.silent
          (.xoffer elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.xoffer elseType branches) \
            typeWaitingOffers env branches)
    | offer_some (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (enabled : BareMessage × PactType) :
        env.WellFormed ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
        TypeOffers env (.offer elseType branches) TypeLabel.silent
          (parallelTypeBranchesSelecting enabled branches) ∅
          (typeFutureOffers (parallelTypeBranchesSelecting enabled branches))
    | offer_else (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.offer elseType branches) TypeLabel.silent elseType
          (typeBranchActions branches) (typeFutureOffers elseType)
    | offer_wait (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
          ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.offer elseType branches) TypeLabel.silent
          (.offer elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.offer elseType branches) \
            typeWaitingOffers env branches)
    | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
        LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv →
        LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv →
        outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
        TypeOffers outer (.par left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.par left' right' interface)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))

  /-- The erased sibling-aware local-environment relation. -/
  @[aesop unsafe]
  inductive LocalTypeEnvironment :
      TypeEnvironment → Interface → TypeEnvironment → PactType →
        TypeLabel → TypeEnvironment → Prop where
    | clock (outer : TypeEnvironment) (interface : Interface)
        (sibling : PactType) (label : TypeLabel) :
        outer.clock = true →
        LocalTypeEnvironment outer interface TypeEnvironment.tock
          sibling label TypeEnvironment.tock
    | ordinary (outer siblingEnv localEnv : TypeEnvironment)
        (interface : Interface) (sibling siblingTarget : PactType)
        (label : TypeLabel) (current future : Finset BareMessage) :
        outer.clock = false →
        siblingEnv.clock = false →
        TypeOffers siblingEnv sibling label siblingTarget current future →
        localEnv.clock = false →
        localEnv.immediate =
          outer.immediate ∪ restrictTypeOffers interface current →
        localEnv.future =
          (outer.future ∪ restrictTypeOffers interface future) \ localEnv.immediate →
        LocalTypeEnvironment outer interface siblingEnv sibling label localEnv
end

/-- The operational sequence offer rule reads the future from the residual
syntax.  Selecting `a!` therefore exposes both `a!` and the subsequent `b!`
in the same cycle. -/
theorem syntactic_optimistic_sequence_offer_regression :
    TypeOffers TypeEnvironment.empty
      (.seq (.choice (.message "a" .send) .skip) (.message "b" .send))
      TypeLabel.silent
      (.seq (.message "a" .send) (.message "b" .send)) ∅
      {("a", .send), ("b", .send)} := by
  have hWellFormed : TypeEnvironment.empty.WellFormed := by
    simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
  have hChoice : TypeOffers TypeEnvironment.empty
      (.choice (.message "a" .send) .skip) TypeLabel.silent
      (.message "a" .send) ∅
      (typeFutureOffers (.message "a" .send)) :=
    TypeOffers.choice_left TypeEnvironment.empty (.message "a" .send) .skip
      hWellFormed
  have hSequence := TypeOffers.seq TypeEnvironment.empty
    (.choice (.message "a" .send) .skip) (.message "a" .send)
    (.message "b" .send) TypeLabel.silent ∅
    (typeFutureOffers (.message "a" .send)) hChoice
  simpa [syntactic_optimistic_sequence_future_regression] using hSequence

end

end Pact
