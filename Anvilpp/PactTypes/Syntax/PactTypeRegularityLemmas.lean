import Anvilpp.PactTypes.Syntax.PactTypeRegularityDefs

namespace Pact

noncomputable section

namespace PactType

  /-- `GuardedOccurrences` is monotone in its guard parameter: a weaker guard
  hypothesis yields a weaker conclusion at every clause. -/
  theorem guardedOccurrences_mono (name : String) {guarded₁ guarded₂ : Prop}
      (hImp : guarded₁ → guarded₂) :
      ∀ processType : PactType,
        GuardedOccurrences name guarded₁ processType →
          GuardedOccurrences name guarded₂ processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType guarded₁ guarded₂ with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            GuardedBranchOccurrences name guarded₁ branches →
            GuardedBranchOccurrences name guarded₂ branches := by
          intro branches hBranchesSize hGuarded
          induction branches with
          | nil => simp [GuardedBranchOccurrences]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              have hFields : GuardedOccurrences name guarded₁ branchType ∧
                  GuardedBranchOccurrences name guarded₁ rest := by
                simpa only [GuardedBranchOccurrences] using hGuarded
              have hBranchSize : sizeOf branchType < n := by
                have hPair : sizeOf branchType <
                    sizeOf (action, branchType) := by simp_wf; omega
                have hHead : sizeOf (action, branchType) <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              have hRestSize : sizeOf rest < n := by
                have hRest : sizeOf rest <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              simpa only [GuardedBranchOccurrences] using
                And.intro (ih (sizeOf branchType) hBranchSize hImp branchType rfl
                    hFields.1)
                  (restIH hRestSize hFields.2)
        intro hGuarded
        cases processType with
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [GuardedOccurrences]
        | var _ other =>
            simp only [GuardedOccurrences] at hGuarded ⊢
            exact fun hEq => hImp (hGuarded hEq)
        | recur _ binder body =>
            by_cases hBinder : binder = name
            · simp [GuardedOccurrences, hBinder]
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              simpa only [GuardedOccurrences, if_neg hBinder] using
                ih (sizeOf body) hBodySize hImp body rfl
                  (by simpa only [GuardedOccurrences, if_neg hBinder]
                    using hGuarded)
        | choice _ left right | fairChoice _ _ left right | par _ left right _ =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hGuarded
            simp only [GuardedOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf left) hLeftSize hImp left rfl hFields.1,
              ih (sizeOf right) hRightSize hImp right rfl hFields.2⟩
        | seq _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hGuarded
            simp only [GuardedOccurrences] at hFields ⊢
            refine ⟨ih (sizeOf left) hLeftSize hImp left rfl hFields.1, ?_⟩
            refine ih (sizeOf right) hRightSize ?_ right rfl hFields.2
            rintro (hLeft | hTock)
            · exact Or.inl (hImp hLeft)
            · exact Or.inr hTock
        | xoffer _ elseType branches | offer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields := hGuarded
            simp only [GuardedOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf elseType) hElseSize hImp elseType rfl hFields.1,
              hBranches branches hBranchesSize hFields.2⟩

  /-- `TailOccurrences` is monotone in its tail parameter: every clause either
  passes `tail` through unchanged or replaces it by a constant. -/
  theorem tailOccurrences_mono (name : String) {tail₁ tail₂ : Prop}
      (hImp : tail₁ → tail₂) :
      ∀ processType : PactType,
        TailOccurrences name tail₁ processType →
          TailOccurrences name tail₂ processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            TailBranchOccurrences name tail₁ branches →
            TailBranchOccurrences name tail₂ branches := by
          intro branches hBranchesSize hTail
          induction branches with
          | nil => simp [TailBranchOccurrences]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              have hFields : TailOccurrences name tail₁ branchType ∧
                  TailBranchOccurrences name tail₁ rest := by
                simpa only [TailBranchOccurrences] using hTail
              have hBranchSize : sizeOf branchType < n := by
                have hPair : sizeOf branchType <
                    sizeOf (action, branchType) := by simp_wf; omega
                have hHead : sizeOf (action, branchType) <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              have hRestSize : sizeOf rest < n := by
                have hRest : sizeOf rest <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              simpa only [TailBranchOccurrences] using
                And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                    hFields.1)
                  (restIH hRestSize hFields.2)
        intro hTail
        cases processType with
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [TailOccurrences]
        | var _ other =>
            simp only [TailOccurrences] at hTail ⊢
            exact fun hEq => hImp (hTail hEq)
        | recur _ binder body =>
            by_cases hBinder : binder = name
            · simp [TailOccurrences, hBinder]
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              simpa only [TailOccurrences, if_neg hBinder] using
                ih (sizeOf body) hBodySize body rfl
                  (by simpa only [TailOccurrences, if_neg hBinder] using hTail)
        | choice _ left right | fairChoice _ _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf left) hLeftSize left rfl hFields.1,
              ih (sizeOf right) hRightSize right rfl hFields.2⟩
        | seq _ left right =>
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨hFields.1, ih (sizeOf right) hRightSize right rfl hFields.2⟩
        | par _ left right _ =>
            simpa only [TailOccurrences] using hTail
        | xoffer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
              hBranches branches hBranchesSize hFields.2⟩
        | offer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
              hFields.2⟩

  /-- Branch-list form of `tailOccurrences_mono`. -/
  theorem tailBranchOccurrences_mono (name : String) {tail₁ tail₂ : Prop}
      (hImp : tail₁ → tail₂) :
      ∀ branches : List (BareMessage × PactType),
        TailBranchOccurrences name tail₁ branches →
          TailBranchOccurrences name tail₂ branches := by
    intro branches
    induction branches with
    | nil => simp [TailBranchOccurrences]
    | cons branch rest ih =>
        rcases branch with ⟨action, branchType⟩
        intro hTail
        have hFields : TailOccurrences name tail₁ branchType ∧
            TailBranchOccurrences name tail₁ rest := by
          simpa only [TailBranchOccurrences] using hTail
        simpa only [TailBranchOccurrences] using
          And.intro (tailOccurrences_mono name hImp branchType hFields.1)
            (ih hFields.2)

  /-- A variable outside the ambient bound-name list has no free occurrence
  in a type whose variables are all bound by that list. -/
  theorem tailOccurrences_false_of_allVariablesBound_not_mem
      (name : String) (bound : List String) :
      ∀ processType,
        AllVariablesBound bound processType →
        name ∉ bound →
        TailOccurrences name False processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType bound with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            AllBranchVariablesBound bound branches →
            name ∉ bound →
            TailBranchOccurrences name False branches := by
          intro branches hBranchesSize hBound hNotMem
          induction branches with
          | nil => simp [TailBranchOccurrences]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              have hFields : AllVariablesBound bound branchType ∧
                  AllBranchVariablesBound bound rest := by
                simpa only [AllBranchVariablesBound] using hBound
              have hBranchSize : sizeOf branchType < n := by
                have hPair : sizeOf branchType <
                    sizeOf (action, branchType) := by simp_wf; omega
                have hHead : sizeOf (action, branchType) <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              have hRestSize : sizeOf rest < n := by
                have hRest : sizeOf rest <
                    sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                omega
              simp only [TailBranchOccurrences]
              exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                  hFields.1 hNotMem,
                restIH hRestSize hFields.2⟩
        intro hBound hNotMem
        cases processType with
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [TailOccurrences]
        | var _ other =>
            simp only [AllVariablesBound] at hBound
            simp only [TailOccurrences]
            intro hEq
            subst other
            exact hNotMem hBound
        | recur _ binder body =>
            by_cases hBinder : binder = name
            · simp [TailOccurrences, hBinder]
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              have hBodyBound : AllVariablesBound (binder :: bound) body := by
                simpa only [AllVariablesBound] using hBound
              have hNameNotMem : name ∉ binder :: bound := by
                simp [Ne.symm hBinder, hNotMem]
              simpa only [TailOccurrences, if_neg hBinder] using
                ih (sizeOf body) hBodySize (binder :: bound) body rfl
                  hBodyBound hNameNotMem
        | choice _ left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | fairChoice _ _ left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | seq _ left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | par _ left right _ =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | xoffer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound elseType ∧
                AllBranchVariablesBound bound branches := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl
                hFields.1 hNotMem,
              hBranches branches hBranchesSize hFields.2 hNotMem⟩
        | offer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound elseType ∧
                AllBranchVariablesBound bound branches := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl
                hFields.1 hNotMem,
              hBranches branches hBranchesSize hFields.2 hNotMem⟩

  /- If `name` occurs nowhere in `processType` (in the unconditional,
  non-tail-restricted sense `TailOccurrences name False`), then `name` can be
  dropped from the bound-name list without affecting `AllVariablesBound`: every
  `.var` leaf that was relying on `name` being in the list must, since it
  cannot itself be `name`, already be covered by the rest of the list. -/
  theorem allVariablesBound_drop_of_tailOccurrences_false
      (name : String) (bound : List String) :
      ∀ processType,
        TailOccurrences name False processType →
        AllVariablesBound (name :: bound) processType →
          AllVariablesBound bound processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType bound with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            TailBranchOccurrences name False branches →
            AllBranchVariablesBound (name :: bound) branches →
              AllBranchVariablesBound bound branches := by
          intro branches hBranchesSize hTail h
          induction branches with
          | nil => simp [AllBranchVariablesBound]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [TailBranchOccurrences] at hTail
              simp only [AllBranchVariablesBound] at h ⊢
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
                have hHead : sizeOf rest < sizeOf ((action, branchType) :: rest) := by
                  simp_wf
                  omega
                omega
              exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                  hTail.1 h.1,
                restIH hRestSize hTail.2 h.2⟩
        cases processType with
        | var _ other =>
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound, List.mem_cons] at h ⊢
            rcases h with hEq | h
            · exact absurd hEq hTail
            · exact h
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [AllVariablesBound]
        | recur _ other body =>
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            by_cases hEq : other = name
            · rw [hEq] at h ⊢
              exact allVariablesBound_mono
                (smaller := name :: name :: bound) (larger := name :: bound)
                (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact List.mem_cons_self
                  · exact hx)
                body h
            · rw [if_neg hEq] at hTail
              have hReorder : AllVariablesBound (name :: other :: bound) body :=
                allVariablesBound_mono
                  (smaller := other :: name :: bound)
                  (larger := name :: other :: bound)
                  (fun x hx => by
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact List.mem_cons_of_mem name List.mem_cons_self
                    · rcases List.mem_cons.mp hx with rfl | hx
                      · exact List.mem_cons_self
                      · exact List.mem_cons_of_mem name
                          (List.mem_cons_of_mem other hx))
                  body h
              exact ih (sizeOf body) hBodySize (other :: bound) body rfl
                hTail hReorder
        | choice _ left right | fairChoice _ _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | seq _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | par _ left right _ =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | xoffer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl hTail.1
                h.1,
              hBranches branches hBranchesSize hTail.2 h.2⟩
        | offer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl hTail.1
                h.1,
              hBranches branches hBranchesSize hTail.2 h.2⟩

  /- Bulk form of `allVariablesBound_drop_of_tailOccurrences_false`: every
  name in `names` can be dropped from the bound-name list at once, provided
  none of them occur in `processType`. -/
  theorem allVariablesBound_drop_of_allTailOccurrences_false
      (names bound : List String) (processType : PactType)
      (hTail : AllTailOccurrences names False processType)
      (hBound : AllVariablesBound (names ++ bound) processType) :
      AllVariablesBound bound processType := by
    induction names with
    | nil => simpa using hBound
    | cons n rest ih =>
        simp only [List.cons_append] at hBound
        have hRest : AllVariablesBound (rest ++ bound) processType :=
          allVariablesBound_drop_of_tailOccurrences_false n (rest ++ bound)
            processType (hTail n List.mem_cons_self) hBound
        exact ih (fun m hm => hTail m (List.mem_cons_of_mem n hm)) hRest

end PactType

/-- Everything one branch declares is declared by the branch list. -/
theorem branch_subset_branchMessageActions
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    {branch.1} ∪ PactType.MessageActions branch.2 ⊆
      PactType.BranchMessageActions branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchMessageActions]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

theorem branch_subset_branchProgressIds
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    PactType.ProgressIds branch.2 ⊆ PactType.BranchProgressIds branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchProgressIds]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

theorem branch_subset_branchFairChoiceIds
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    PactType.FairChoiceIds branch.2 ⊆ PactType.BranchFairChoiceIds branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchFairChoiceIds]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

/-- Branch ownership makes the branch list pairwise declaration-disjoint. -/
theorem branchDeclarationsDisjoint_pairwise :
    ∀ branches : List (BareMessage × PactType),
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      List.Pairwise BranchDeclarationsDisjoint branches := by
  intro branches
  induction branches with
  | nil => intro _ _ _; exact List.Pairwise.nil
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      intro hMsg hProgress hFair
      simp only [PactType.ParallelMessageOwnershipBranches] at hMsg
      simp only [PactType.ParallelProgressOwnershipBranches] at hProgress
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFair
      refine List.Pairwise.cons ?_ (ih hMsg.2.2.2 hProgress.2.2 hFair.2.2)
      intro other hOther
      refine ⟨?_, ?_, ?_⟩
      · exact hMsg.2.2.1.mono_right (branch_subset_branchMessageActions hOther)
      · exact hProgress.2.1.mono_right (branch_subset_branchProgressIds hOther)
      · exact hFair.2.1.mono_right (branch_subset_branchFairChoiceIds hOther)

/-- The ownership invariants give offer-branch disjointness at every offer. -/
theorem offerBranchesDisjoint_of_ownership :
    ∀ processType : PactType,
      processType.ParallelMessageOwnership →
      processType.ParallelProgressOwnership →
      processType.ParallelFairChoiceOwnership →
      processType.OfferBranchesDisjoint := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ParallelMessageOwnershipBranches branches →
          PactType.ParallelProgressOwnershipBranches branches →
          PactType.ParallelFairChoiceOwnershipBranches branches →
          PactType.OfferBranchesDisjointBranches branches := by
        intro branches hBranchesSize hMsg hProgress hFair
        induction branches with
        | nil => simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.ParallelMessageOwnershipBranches] at hMsg
            simp only [PactType.ParallelProgressOwnershipBranches] at hProgress
            simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFair
            simp only [PactType.OfferBranchesDisjointBranches]
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, branchType) :: tail) := by
                simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl hMsg.1
                hProgress.1 hFair.1,
              restIH hTailSize hMsg.2.2.2 hProgress.2.2 hFair.2.2⟩
      have hBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ParallelMessageOwnershipBodies branches →
          PactType.ParallelProgressOwnershipBranches branches →
          PactType.ParallelFairChoiceOwnershipBranches branches →
          PactType.OfferBranchesDisjointBranches branches := by
        intro branches hBranchesSize hMsg hProgress hFair
        induction branches with
        | nil => simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.ParallelMessageOwnershipBodies] at hMsg
            simp only [PactType.ParallelProgressOwnershipBranches] at hProgress
            simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFair
            simp only [PactType.OfferBranchesDisjointBranches]
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have : sizeOf tail < sizeOf ((action, branchType) :: tail) := by
                simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl hMsg.1
                hProgress.1 hFair.1,
              restIH hTailSize hMsg.2 hProgress.2.2 hFair.2.2⟩
      intro hMsg hProgress hFair
      cases processType with
      | message a m d | progress a p | tock a | skip a | var a _ =>
          simp [PactType.OfferBranchesDisjoint]
      | choice a l r | seq a l r | fairChoice a b l r =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl hMsg.1 hProgress.1 hFair.1,
            ih (sizeOf r) hR r rfl hMsg.2 hProgress.2 hFair.2⟩
      | par a l r i =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl hMsg.2.2.1 hProgress.2.1 hFair.2.1,
            ih (sizeOf r) hR r rfl hMsg.2.2.2 hProgress.2.2 hFair.2.2⟩
      | recur a name body =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.OfferBranchesDisjoint]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ih (sizeOf body) hB body rfl hMsg hProgress hFair
      | xoffer a elseType branches =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl hMsg.1 hProgress.1 hFair.1,
            hBodies branches hBr hMsg.2 hProgress.2 hFair.2⟩
      | offer a elseType branches =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl hMsg.1 hProgress.1 hFair.1,
            branchDeclarationsDisjoint_pairwise branches hMsg.2 hProgress.2 hFair.2,
            hBranches branches hBr hMsg.2 hProgress.2 hFair.2⟩

end

end Pact
