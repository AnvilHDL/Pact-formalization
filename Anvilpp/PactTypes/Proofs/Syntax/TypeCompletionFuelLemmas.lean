import Anvilpp.PactTypes.Spec.Syntax.TypeCompletionFuelDefs

namespace Pact

noncomputable section

/-- Substitution changes branch bodies, not their head declarations. -/
theorem replaceBranches_head_gate_iff
    (branches : List (BareMessage × PactType)) (name : String)
    (replacement : PactType) (alphabet : PactTypeAlphabet) :
    (∀ b ∈ PactType.replaceBranches branches name replacement,
        b.1 ∈ alphabet.actions) ↔
      ∀ b ∈ branches, b.1 ∈ alphabet.actions := by
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp only [PactType.replaceBranches, List.forall_mem_cons, ih]

/-- Once the fuel covers the finite syntax tree, one more unit cannot change
same-cycle completion. -/
theorem typeCanCompleteThisCycleFuel_succ_stable :
    ∀ fuel processType, sizeOf processType ≤ fuel →
      typeCanCompleteThisCycleFuel (fuel + 1) processType =
        typeCanCompleteThisCycleFuel fuel processType := by
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
          change typeCanCompleteThisCycleFuel (fuel + 1) body =
            typeCanCompleteThisCycleFuel fuel body
          apply ih
          have hBody : sizeOf body <
              sizeOf (PactType.recur alphabet name body) := by
            simp_wf
            omega
          omega
      | choice alphabet left right =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left ||
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right)
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
          change (typeCanCompleteThisCycleFuel (fuel + 1) left ||
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right)
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
          change (typeCanCompleteThisCycleFuel (fuel + 1) left &&
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left &&
              typeCanCompleteThisCycleFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.seq alphabet left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.seq alphabet left right) := by
                simp_wf
                omega
              omega)]
      | par alphabet left right interface =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left &&
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left &&
              typeCanCompleteThisCycleFuel fuel right)
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
          change (typeCanCompleteThisCycleFuel (fuel + 1) elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel (fuel + 1) branch.2)) =
            (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2))
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer alphabet elseType branches) := by
              simp_wf
              omega
            omega)]
          congr 1
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
          induction branches with
          | nil => rfl
          | cons branch rest restIH =>
              simp only [List.any_cons]
              rw [ih branch.2 (hEvery branch (by simp))]
              rw [restIH (by
                have : sizeOf (PactType.xoffer alphabet elseType rest) <
                    sizeOf (PactType.xoffer alphabet elseType
                      (branch :: rest)) := by
                  simp_wf
                  omega
                omega) (by
                intro other hOther
                exact hEvery other (by simp [hOther]))]
      | offer alphabet elseType branches =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel (fuel + 1) branch.2)) =
            (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2))
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer alphabet elseType branches) := by
              simp_wf
              omega
            omega)]
          congr 1
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
          induction branches with
          | nil => rfl
          | cons branch rest restIH =>
              simp only [List.any_cons]
              rw [ih branch.2 (hEvery branch (by simp))]
              rw [restIH (by
                have : sizeOf (PactType.offer alphabet elseType rest) <
                    sizeOf (PactType.offer alphabet elseType
                      (branch :: rest)) := by
                  simp_wf
                  omega
                omega) (by
                intro other hOther
                exact hEvery other (by simp [hOther]))]

/-- Once fuel covers the finite syntax tree, the bounded completion analysis
agrees with the structural completion predicate. -/
theorem typeCanCompleteThisCycleFuel_eq_canCompleteDeclared :
    ∀ fuel processType, sizeOf processType < fuel →
      typeCanCompleteThisCycleFuel fuel processType =
        processType.CanCompleteDeclared := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hSize
      omega
  | succ fuel ih =>
      intro processType hSize
      cases processType with
      | message alphabet msg dir =>
          simp [typeCanCompleteThisCycleFuel, PactType.canCompleteDeclared_eq]
      | progress alphabet pid =>
          simp [typeCanCompleteThisCycleFuel, PactType.canCompleteDeclared_eq]
      | tock alphabet =>
          simp [typeCanCompleteThisCycleFuel, PactType.canCompleteDeclared_eq]
      | skip alphabet =>
          simp [typeCanCompleteThisCycleFuel, PactType.canCompleteDeclared_eq]
      | var alphabet name =>
          simp [typeCanCompleteThisCycleFuel, PactType.canCompleteDeclared_eq]
      | recur alphabet name body =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          apply ih
          have hProper : sizeOf body <
              sizeOf (PactType.recur alphabet name body) := by
            simp_wf
            omega
          omega
      | choice alphabet left right =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.choice alphabet left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.choice alphabet left right) := by
                simp_wf; omega
              omega)]
      | fairChoice alphabet bid left right =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.fairChoice alphabet bid left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.fairChoice alphabet bid left right) := by
                simp_wf; omega
              omega)]
      | seq alphabet left right =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.seq alphabet left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.seq alphabet left right) := by
                simp_wf; omega
              omega)]
      | par alphabet left right interface =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.par alphabet left right interface) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.par alphabet left right interface) := by
                simp_wf; omega
              omega)]
      | xoffer alphabet elseType branches =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer alphabet elseType branches) := by
              simp_wf; omega
            omega)]
          congr 1
          induction branches with
          | nil => simp [PactType.branchCanCompleteDeclared_nil]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [List.any_cons, PactType.branchCanCompleteDeclared_cons]
              rw [ih branchType (by
                have : sizeOf branchType < sizeOf
                    (PactType.xoffer alphabet elseType
                      ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
              rw [restIH (by
                have : sizeOf (PactType.xoffer alphabet elseType rest) < sizeOf
                    (PactType.xoffer alphabet elseType
                      ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
      | offer alphabet elseType branches =>
          rw [PactType.canCompleteDeclared_eq]
          simp only [typeCanCompleteThisCycleFuel]
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer alphabet elseType branches) := by
              simp_wf; omega
            omega)]
          congr 1
          induction branches with
          | nil => simp [PactType.branchCanCompleteDeclared_nil]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [List.any_cons, PactType.branchCanCompleteDeclared_cons]
              rw [ih branchType (by
                have : sizeOf branchType < sizeOf
                    (PactType.offer alphabet elseType
                      ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
              rw [restIH (by
                have : sizeOf (PactType.offer alphabet elseType rest) < sizeOf
                    (PactType.offer alphabet elseType
                      ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]

/- A structurally mandatory clock prevents same-cycle completion. -/
end

end Pact
