import Anvilpp.PactTypes.Spec.Syntax.TypeFutureOffersFuelDefs

namespace Pact

noncomputable section

/-- Once fuel covers the finite syntax tree, one more unit cannot expose a new
same-cycle future offer. -/
private theorem typeFutureOffersFuel_succ_stable :
    ∀ fuel processType, sizeOf processType ≤ fuel →
      typeFutureOffersFuel (fuel + 1) processType =
        typeFutureOffersFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hSize
      cases processType <;> simp at hSize
  | succ fuel ih =>
      intro processType hSize
      cases processType with
      | message alphabet msg dir => rfl
      | progress alphabet pid => rfl
      | tock alphabet => rfl
      | skip alphabet => rfl
      | var alphabet name => rfl
      | recur alphabet name body =>
          change typeFutureOffersFuel (fuel + 1) body =
            typeFutureOffersFuel fuel body
          apply ih
          have : sizeOf body <
              sizeOf (PactType.recur alphabet name body) := by
            simp_wf
            omega
          omega
      | choice alphabet left right =>
          change (typeFutureOffersFuel (fuel + 1) left ∪
              typeFutureOffersFuel (fuel + 1) right) =
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.choice alphabet left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.choice alphabet left right) := by
                simp_wf
                omega
              omega)]
      | fairChoice alphabet bid left right =>
          change (typeFutureOffersFuel (fuel + 1) left ∪
              typeFutureOffersFuel (fuel + 1) right) =
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.fairChoice alphabet bid left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.fairChoice alphabet bid left right) := by
                simp_wf
                omega
              omega)]
      | seq alphabet left right =>
          have hLeft : sizeOf left ≤ fuel := by
            have : sizeOf left <
                sizeOf (PactType.seq alphabet left right) := by
              simp_wf
              omega
            omega
          have hRight : sizeOf right ≤ fuel := by
            have : sizeOf right <
                sizeOf (PactType.seq alphabet left right) := by
              simp_wf
              omega
            omega
          change (if typeCanCompleteThisCycleFuel (fuel + 1) left then
              typeFutureOffersFuel (fuel + 1) left ∪
                typeFutureOffersFuel (fuel + 1) right
            else typeFutureOffersFuel (fuel + 1) left) =
            (if typeCanCompleteThisCycleFuel fuel left then
              typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right
            else typeFutureOffersFuel fuel left)
          rw [typeCanCompleteThisCycleFuel_succ_stable fuel left hLeft,
            ih left hLeft, ih right hRight]
      | par alphabet left right interface =>
          change hideTypeOffers interface
              (typeFutureOffersFuel (fuel + 1) left ∪
                typeFutureOffersFuel (fuel + 1) right) =
            hideTypeOffers interface
              (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.par alphabet left right interface) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.par alphabet left right interface) := by
                simp_wf
                omega
              omega)]
      | xoffer alphabet elseType branches =>
          change (branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2)
                (typeFutureOffersFuel (fuel + 1) elseType)) ∩ alphabet.actions =
            (branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                (typeFutureOffersFuel fuel elseType)) ∩ alphabet.actions
          apply congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer alphabet elseType branches) := by
              simp_wf
              omega
            omega)]
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.xoffer alphabet elseType branches) := by
              simp_wf
              omega
            omega
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2) initial =
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel fuel branch.2) initial := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro initial hSubset
                simp only [List.foldl_cons]
                rw [ih branch.2 (hEvery branch (hSubset branch (by simp)))]
                apply tailIH
                intro other hOther
                exact hSubset other (by simp [hOther])
          exact hFold branches _ (by simp)
      | offer alphabet elseType branches =>
          change (branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2)
                (typeFutureOffersFuel (fuel + 1) elseType)) ∩ alphabet.actions =
            (branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                (typeFutureOffersFuel fuel elseType)) ∩ alphabet.actions
          apply congrArg (fun offers : Finset BareMessage => offers ∩ alphabet.actions)
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer alphabet elseType branches) := by
              simp_wf
              omega
            omega)]
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.offer alphabet elseType branches) := by
              simp_wf
              omega
            omega
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2) initial =
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel fuel branch.2) initial := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro initial hSubset
                simp only [List.foldl_cons]
                rw [ih branch.2 (hEvery branch (hSubset branch (by simp)))]
                apply tailIH
                intro other hOther
                exact hSubset other (by simp [hOther])
          exact hFold branches _ (by simp)

theorem typeFutureOffersFuel_add_stable
    (processType : PactType) (fuel extra : Nat)
    (hFuel : sizeOf processType ≤ fuel) :
    typeFutureOffersFuel (fuel + extra) processType =
      typeFutureOffersFuel fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        typeFutureOffersFuel_succ_stable (fuel + extra) processType (by omega),
        ih]

/-- Any fuel budget covering the syntax computes the same public future menu. -/
theorem typeFutureOffersFuel_eq_typeFutureOffers
    (processType : PactType) (fuel : Nat)
    (hFuel : sizeOf processType + 1 ≤ fuel) :
    typeFutureOffersFuel fuel processType = typeFutureOffers processType := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  unfold typeFutureOffers
  exact typeFutureOffersFuel_add_stable processType
    (sizeOf processType + 1) extra (by omega)

/-- Folding branch menus introduces only heads and messages used by their bodies. -/
theorem foldl_typeMenu_subset_messageActions (menu : PactType → Finset BareMessage)
    (hMenu : ∀ ty, menu ty ⊆ ty.MessageActions) :
    ∀ (branches : List (BareMessage × PactType)) (initial : Finset BareMessage),
      branches.foldl (fun offers branch => offers ∪ {branch.1} ∪ menu branch.2) initial ⊆
        initial ∪ PactType.BranchMessageActions branches := by
  intro branches
  induction branches with
  | nil => intro initial; simp [PactType.BranchMessageActions]
  | cons branch rest ih =>
      rcases branch with ⟨head, body⟩
      intro initial action hAction
      have h := ih (initial ∪ {head} ∪ menu body) hAction
      simp only [PactType.BranchMessageActions, Finset.mem_union] at h ⊢
      rcases h with ((hInitial | hHead) | hBody) | hRest
      · exact Or.inl hInitial
      · exact Or.inr (Or.inl (Or.inl hHead))
      · exact Or.inr (Or.inl (Or.inr (hMenu body hBody)))
      · exact Or.inr (Or.inr hRest)

/-- Future menus contain only syntactic message actions, regardless of well-formedness. -/
theorem typeFutureOffersFuel_subset_messageActions (fuel : Nat) (ty : PactType) :
    typeFutureOffersFuel fuel ty ⊆ ty.MessageActions := by
  induction fuel generalizing ty with
  | zero => simp [typeFutureOffersFuel]
  | succ fuel ih =>
      cases ty with
      | message alphabet msg dir =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          split_ifs <;> simp
      | progress | tock | skip | var => simp [typeFutureOffersFuel]
      | recur alphabet name body =>
          simpa only [typeFutureOffersFuel, PactType.MessageActions] using ih body
      | choice alphabet left right | fairChoice alphabet bid left right =>
          simpa only [typeFutureOffersFuel, PactType.MessageActions] using
            Finset.union_subset_union (ih left) (ih right)
      | seq alphabet left right =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          split_ifs
          · exact Finset.union_subset_union (ih left) (ih right)
          · exact Finset.Subset.trans (ih left) Finset.subset_union_left
      | par alphabet left right interface =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          exact Finset.Subset.trans (Finset.filter_subset _ _)
            (Finset.union_subset_union (ih left) (ih right))
      | xoffer alphabet other branches | offer alphabet other branches =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          exact Finset.Subset.trans Finset.inter_subset_left
            (Finset.Subset.trans
              (foldl_typeMenu_subset_messageActions (typeFutureOffersFuel fuel) ih branches _)
              (Finset.union_subset_union (ih other) (Finset.Subset.refl _)))

/-- Every optimistic menu respects the written alphabet of a well-formed type. -/
theorem typeFutureOffersFuel_subset_alphabet (fuel : Nat) (ty : PactType)
    (hWF : ty.AlphabetWellFormed) :
    typeFutureOffersFuel fuel ty ⊆ ty.alphabet.actions := by
  induction fuel generalizing ty with
  | zero => simp [typeFutureOffersFuel]
  | succ fuel ih =>
      cases ty with
      | message alphabet msg dir =>
          simp only [typeFutureOffersFuel, PactType.alphabet]
          split_ifs with h <;> simp_all
      | progress | tock | skip | var => simp [typeFutureOffersFuel]
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          exact hWF.2.1 ▸ ih body hWF.2.2
      | choice alphabet left right | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          exact Finset.union_subset (hWF.2.1 ▸ ih left hWF.2.2.2.1)
            (hWF.2.2.1 ▸ ih right hWF.2.2.2.2)
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          split_ifs
          · exact Finset.union_subset (hWF.2.1 ▸ ih left hWF.2.2.2.1)
              (hWF.2.2.1 ▸ ih right hWF.2.2.2.2)
          · exact hWF.2.1 ▸ ih left hWF.2.2.2.1
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          intro action hAction
          obtain ⟨hChild, hOutside⟩ := Finset.mem_filter.mp hAction
          rcases Finset.mem_union.mp hChild with hLeft | hRight
          · rw [← hWF.2.1.parent_eq_left]
            exact Finset.mem_filter.mpr ⟨ih left hWF.2.2.1 hLeft, hOutside⟩
          · rw [← hWF.2.1.parent_eq_right]
            exact Finset.mem_filter.mpr ⟨ih right hWF.2.2.2 hRight, hOutside⟩
      | xoffer | offer => exact Finset.inter_subset_right

theorem typeFutureOffers_subset_alphabet (ty : PactType)
    (hWF : ty.AlphabetWellFormed) :
    typeFutureOffers ty ⊆ ty.alphabet.actions :=
  typeFutureOffersFuel_subset_alphabet _ ty hWF

end

end Pact
