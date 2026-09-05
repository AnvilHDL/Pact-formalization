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
  /- Bulk form of `allVariablesBound_drop_of_tailOccurrences_false`: every
  name in `names` can be dropped from the bound-name list at once, provided
  none of them occur in `processType`. -/
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

/-- Erasing polarity sends a declared action to a declared message
identifier. -/
theorem PactType.messageId_mem_of_action_mem :
    ∀ (processType : PactType) (action : BareMessage),
      action ∈ PactType.MessageActions processType →
      action.1 ∈ PactType.MessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ action : BareMessage,
          action ∈ PactType.BranchMessageActions branches →
          action.1 ∈ PactType.BranchMessageIds branches := by
        intro branches
        induction branches with
        | nil => intro _ action hAction; simp [PactType.BranchMessageActions] at hAction
        | cons head tail restIH =>
            intro hSizeCons action hAction
            rcases head with ⟨headAction, headType⟩
            have hBodySize : sizeOf headType < n := by
              have hPair : sizeOf headType < sizeOf (headAction, headType) := by
                simp_wf; omega
              have hHead : sizeOf (headAction, headType) <
                  sizeOf ((headAction, headType) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((headAction, headType) :: tail) := by simp_wf; omega
              omega
            simp only [PactType.BranchMessageActions, Finset.mem_union,
              Finset.mem_singleton] at hAction
            simp only [PactType.BranchMessageIds, Finset.mem_union,
              Finset.mem_singleton]
            rcases hAction with (hEq | hBody) | hTail
            · exact Or.inl (Or.inl (by rw [hEq]))
            · exact Or.inl (Or.inr
                (ih (sizeOf headType) hBodySize headType rfl action hBody))
            · exact Or.inr (restIH hTailSize action hTail)
      intro action hAction
      subst hSize
      cases processType with
      | message _ msg dir =>
          simp only [PactType.MessageActions, Finset.mem_singleton] at hAction
          simp only [PactType.MessageIds, Finset.mem_singleton]
          rw [hAction]
      | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.MessageActions] at hAction
      | recur alphabet name body =>
          have hBodySize : sizeOf body < sizeOf
              (PactType.recur alphabet name body) := by simp_wf; omega
          simp only [PactType.MessageActions] at hAction
          simp only [PactType.MessageIds]
          exact ih (sizeOf body) hBodySize body rfl action hAction
      | choice alphabet left right =>
          have hL : sizeOf left < sizeOf (PactType.choice alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf (PactType.choice alphabet left right) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf left) hL left rfl action)
            (ih (sizeOf right) hR right rfl action)
      | seq alphabet left right =>
          have hL : sizeOf left < sizeOf (PactType.seq alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf (PactType.seq alphabet left right) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf left) hL left rfl action)
            (ih (sizeOf right) hR right rfl action)
      | par alphabet left right interface =>
          have hL : sizeOf left < sizeOf (PactType.par alphabet left right interface) := by simp_wf; omega
          have hR : sizeOf right < sizeOf (PactType.par alphabet left right interface) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf left) hL left rfl action)
            (ih (sizeOf right) hR right rfl action)
      | fairChoice alphabet bid left right =>
          have hL : sizeOf left < sizeOf (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf left) hL left rfl action)
            (ih (sizeOf right) hR right rfl action)
      | xoffer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf elseType) hE elseType rfl action)
            (hBranches branches hB action)
      | offer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf (PactType.offer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf (PactType.offer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.MessageActions, Finset.mem_union] at hAction
          simp only [PactType.MessageIds, Finset.mem_union]
          exact hAction.imp (ih (sizeOf elseType) hE elseType rfl action)
            (hBranches branches hB action)

/-- Erasing polarity sends a declared branch action to a declared branch
message identifier. -/
theorem PactType.branchMessageId_mem_of_action_mem :
    ∀ (branches : List (BareMessage × PactType)) (action : BareMessage),
      action ∈ PactType.BranchMessageActions branches →
      action.1 ∈ PactType.BranchMessageIds branches := by
  intro branches
  induction branches with
  | nil => intro action hAction; simp [PactType.BranchMessageActions] at hAction
  | cons head tail ih =>
      intro action hAction
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchMessageActions, Finset.mem_union,
        Finset.mem_singleton] at hAction
      simp only [PactType.BranchMessageIds, Finset.mem_union,
        Finset.mem_singleton]
      rcases hAction with (hEq | hBody) | hTail
      · exact Or.inl (Or.inl (by rw [hEq]))
      · exact Or.inl (Or.inr
          (PactType.messageId_mem_of_action_mem headType action hBody))
      · exact Or.inr (ih action hTail)

/-- A conjunctive offer's branch condition contains the pointwise one. -/
theorem conjunctiveMessageOwnershipBodies_of_branches :
    ∀ branches : List (BareMessage × PactType),
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ConjunctiveMessageOwnershipBodies branches := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simp [PactType.ConjunctiveMessageOwnershipBodies]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      intro hConj
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      simp only [PactType.ConjunctiveMessageOwnershipBodies]
      exact ⟨hConj.1, ih hConj.2.2⟩

/-- The paper's two ownership conditions on a conjunctive offer rebuild the
branch bundle the proofs consume. -/
theorem PactType.parallelMessageOwnershipBranches_of_conjuncts :
    ∀ branches : List (BareMessage × PactType),
      PactType.ParallelMessageOwnershipBodies branches →
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ParallelMessageOwnershipBranches branches := by
  intro branches
  induction branches with
  | nil =>
      intro _ _
      simp [PactType.ParallelMessageOwnershipBranches]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      intro hBodies hConj
      simp only [PactType.ParallelMessageOwnershipBodies] at hBodies
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      simp only [PactType.ParallelMessageOwnershipBranches]
      refine ⟨hBodies.1, hConj.2.1, ?_, ih hBodies.2 hConj.2.2⟩
      refine Finset.disjoint_left.mpr ?_
      intro other hOther hRest
      have hId : other.1 ∈ {action.1} ∪ PactType.MessageIds body := by
        rcases Finset.mem_union.mp hOther with hHead | hBody
        · exact Finset.mem_union_left _
            (Finset.mem_singleton.mpr
              (congrArg Prod.fst (Finset.mem_singleton.mp hHead)))
        · exact Finset.mem_union_right _
            (PactType.messageId_mem_of_action_mem body other hBody)
      exact Finset.disjoint_left.mp hConj.2.1 hId
        (PactType.branchMessageId_mem_of_action_mem tail other hRest)

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
      processType.ConjunctiveMessageOwnership →
      processType.OfferBranchesDisjoint := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ParallelMessageOwnershipBodies branches →
          PactType.ParallelProgressOwnershipBranches branches →
          PactType.ParallelFairChoiceOwnershipBranches branches →
          PactType.ConjunctiveMessageOwnershipBodies branches →
          PactType.OfferBranchesDisjointBranches branches := by
        intro branches hBranchesSize hMsg hProgress hFair hBodyConj
        induction branches with
        | nil => simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.ParallelMessageOwnershipBodies] at hMsg
            simp only [PactType.ParallelProgressOwnershipBranches] at hProgress
            simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFair
            simp only [PactType.ConjunctiveMessageOwnershipBodies] at hBodyConj
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
                hProgress.1 hFair.1 hBodyConj.1,
              restIH hTailSize hMsg.2 hProgress.2.2 hFair.2.2 hBodyConj.2⟩
      intro hMsg hProgress hFair hConj
      cases processType with
      | message a m d | progress a p | tock a | skip a | var a _ =>
          simp [PactType.OfferBranchesDisjoint]
      | choice a l r | seq a l r | fairChoice a b l r =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.ConjunctiveMessageOwnership] at hConj
          simp only [PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl hMsg.1 hProgress.1 hFair.1 hConj.1,
            ih (sizeOf r) hR r rfl hMsg.2 hProgress.2 hFair.2 hConj.2⟩
      | par a l r i =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.ConjunctiveMessageOwnership] at hConj
          simp only [PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl hMsg.2.1 hProgress.2.1 hFair.2.1
              hConj.1,
            ih (sizeOf r) hR r rfl hMsg.2.2 hProgress.2.2 hFair.2.2 hConj.2⟩
      | recur a name body =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.ConjunctiveMessageOwnership] at hConj
          simp only [PactType.OfferBranchesDisjoint]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ih (sizeOf body) hB body rfl hMsg hProgress hFair hConj
      | xoffer a elseType branches =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.ConjunctiveMessageOwnership] at hConj
          simp only [PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl hMsg.1 hProgress.1 hFair.1
              hConj.1,
            hBodies branches hBr hMsg.2 hProgress.2 hFair.2 hConj.2⟩
      | offer a elseType branches =>
          simp only [PactType.ParallelMessageOwnership] at hMsg
          simp only [PactType.ParallelProgressOwnership] at hProgress
          simp only [PactType.ParallelFairChoiceOwnership] at hFair
          simp only [PactType.ConjunctiveMessageOwnership] at hConj
          simp only [PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          have hBundle := PactType.parallelMessageOwnershipBranches_of_conjuncts
            branches hMsg.2 hConj.2
          exact ⟨ih (sizeOf elseType) hE elseType rfl hMsg.1 hProgress.1 hFair.1
              hConj.1,
            branchDeclarationsDisjoint_pairwise branches hBundle hProgress.2
              hFair.2,
            hBodies branches hBr hMsg.2 hProgress.2 hFair.2
              (conjunctiveMessageOwnershipBodies_of_branches branches
                hConj.2)⟩

end

end Pact
