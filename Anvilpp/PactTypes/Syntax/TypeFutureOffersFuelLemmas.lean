import Anvilpp.PactTypes.Syntax.TypeFutureOffersFuelDefs

namespace Pact

noncomputable section

/-- Substitution rewrites branch bodies only, so a branch-head condition is
unaffected by it. -/
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

/-- A clock-guarded substitution cannot expose a new offer before the next
clock. -/
theorem guardedOccurrences_replace_typeFutureOffersFuel
    (name : String) (replacement processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) (fuel : Nat) :
    typeFutureOffersFuel fuel (processType.replaceVar name replacement) =
      typeFutureOffersFuel fuel processType := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases processType with
      | message alphabet msg dir => simp [PactType.replaceVar, typeFutureOffersFuel]
      | progress alphabet pid => simp [PactType.replaceVar, typeFutureOffersFuel]
      | tock alphabet => simp [PactType.replaceVar, typeFutureOffersFuel]
      | skip alphabet => simp [PactType.replaceVar, typeFutureOffersFuel]
      | var alphabet other =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          have hNe : name ≠ other := by
            intro h
            exact hGuarded h.symm
          simp [PactType.replaceVar, typeFutureOffersFuel, hNe]
      | recur alphabet other body =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          by_cases hName : other = name
          · have hTarget : name = other := hName.symm
            simp [PactType.replaceVar, typeFutureOffersFuel, hTarget]
          · simp only [hName, ↓reduceIte] at hGuarded
            have hTarget : name ≠ other := by
              intro h
              exact hName h.symm
            simp only [PactType.replaceVar, typeFutureOffersFuel, hTarget]
            exact guardedOccurrences_replace_typeFutureOffersFuel
              name replacement body hGuarded fuel
      | choice alphabet left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | fairChoice alphabet bid left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | par alphabet left right interface =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | seq alphabet left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement left hLeft fuel]
          by_cases hTock : left.MustTockBeforeCompletion
          · rw [mustTock_cannotCompleteThisCycleFuel left hTock fuel]
            simp
          · simp only [hTock, or_false] at hRight
            rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | xoffer alphabet elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hFold : ∀ initial,
              (PactType.replaceBranches branches name replacement).foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial =
                branches.foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial := by
            intro initial
            induction branches generalizing initial with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.foldl_cons]
                rw [guardedOccurrences_replace_typeFutureOffersFuel
                  name replacement branchType hBranch fuel]
                exact ih hRest _
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            replaceBranches_head_gate_iff]
          split_ifs with hGate
          case neg => rfl
          rw [guardedOccurrences_replace_typeFutureOffersFuel
            name replacement elseType hElse fuel]
          exact hFold _
      | offer alphabet elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hFold : ∀ initial,
              (PactType.replaceBranches branches name replacement).foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial =
                branches.foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial := by
            intro initial
            induction branches generalizing initial with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.foldl_cons]
                rw [guardedOccurrences_replace_typeFutureOffersFuel
                  name replacement branchType hBranch fuel]
                exact ih hRest _
          simp only [PactType.replaceVar, typeFutureOffersFuel,
            replaceBranches_head_gate_iff]
          split_ifs with hGate
          case neg => rfl
          rw [guardedOccurrences_replace_typeFutureOffersFuel
            name replacement elseType hElse fuel]
          exact hFold _
termination_by fuel
decreasing_by
  all_goals
    omega

/-- Any fuel budget covering the syntax computes the same public future menu. -/
theorem typeFutureOffersFuel_eq_typeFutureOffers
    (processType : PactType) (fuel : Nat)
    (hFuel : sizeOf processType + 1 ≤ fuel) :
    typeFutureOffersFuel fuel processType = typeFutureOffers processType := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  unfold typeFutureOffers
  exact typeFutureOffersFuel_add_stable processType
    (sizeOf processType + 1) extra (by omega)

/-- Same-cycle completion ignores alphabet annotations. -/
theorem typeCanCompleteThisCycleFuel_reannotate :
    ∀ (fuel : Nat) (processType : PactType) (alphabet : PactTypeAlphabet),
      typeCanCompleteThisCycleFuel fuel (processType.reannotate alphabet) =
        typeCanCompleteThisCycleFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero => intro processType alphabet; rfl
  | succ fuel ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (alphabet : PactTypeAlphabet),
          (PactType.reannotateBranches alphabet branches).any
              (fun branch => typeCanCompleteThisCycleFuel fuel branch.2) =
            branches.any fun branch =>
              typeCanCompleteThisCycleFuel fuel branch.2 := by
        intro branches alphabet
        induction branches with
        | nil => simp
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.reannotateBranches_cons, List.any_cons, restIH,
              ih branchType alphabet]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (alphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          (PactType.reannotateOfferBranches alphabet seen branches).any
              (fun branch => typeCanCompleteThisCycleFuel fuel branch.2) =
            branches.any fun branch =>
              typeCanCompleteThisCycleFuel fuel branch.2 := by
        intro branches alphabet
        induction branches with
        | nil =>
            intro seen
            simp [PactType.reannotateOfferBranches_nil]
        | cons branch rest restIH =>
            intro seen
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.reannotateOfferBranches_cons, List.any_cons,
              restIH, ih branchType]
      intro processType alphabet
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, typeCanCompleteThisCycleFuel]
      | recur a binder body =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            ih body alphabet
      | choice a l r =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· || ·) (ih l alphabet) (ih r alphabet)
      | fairChoice a b l r =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· || ·) (ih l alphabet) (ih r alphabet)
      | seq a l r =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· && ·) (ih l alphabet) (ih r alphabet)
      | par a l r bdry =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· && ·) (ih l _) (ih r _)
      | xoffer a e bs =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· || ·) (ih e alphabet) (hBranches bs alphabet)
      | offer a e bs =>
          simpa [PactType.reannotate, typeCanCompleteThisCycleFuel] using
            congrArg₂ (· || ·) (ih e alphabet) (hOfferBranches bs alphabet ∅)

end

end Pact
