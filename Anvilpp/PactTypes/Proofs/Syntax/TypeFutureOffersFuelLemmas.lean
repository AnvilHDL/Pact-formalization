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
          change (if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
              branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2)
                (typeFutureOffersFuel (fuel + 1) elseType)
            else ∅) =
            (if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
              branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                (typeFutureOffersFuel fuel elseType)
            else ∅)
          split_ifs with hGate
          case neg => rfl
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
          change (if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
              branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2)
                (typeFutureOffersFuel (fuel + 1) elseType)
            else ∅) =
            (if ∀ b ∈ branches, b.1 ∈ alphabet.actions then
              branches.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                (typeFutureOffersFuel fuel elseType)
            else ∅)
          split_ifs with hGate
          case neg => rfl
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

end

end Pact
