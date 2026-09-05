import Anvilpp.PactTypes.Syntax.PactTypeSubstitutionDefs

namespace Pact

noncomputable section

/-- Substituting any value at `.var name` can only make same-cycle completion
easier, since `CanCompleteBeforeTock` scores a bare variable as `false` and
both `||` and `&&` are monotone.  This is the direction needed to place a
fragment's own `completing` states into the substituted completion set. -/
theorem PactType.canCompleteBeforeTock_le_subst
    (name : String) (value : Bool) (processType : PactType)
    (hComplete : processType.CanCompleteBeforeTock = true) :
    canCompleteBeforeTockSubst name value processType = true := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message _ msg dir => simp [canCompleteBeforeTockSubst]
      | progress _ pid => simp [canCompleteBeforeTockSubst]
      | skip _ => simp [canCompleteBeforeTockSubst]
      | tock _ => simp [PactType.CanCompleteBeforeTock] at hComplete
      | var _ other => simp [PactType.CanCompleteBeforeTock] at hComplete
      | recur _ other body =>
          by_cases hName : name = other
          · subst hName
            simp only [canCompleteBeforeTockSubst, if_pos rfl]
            simpa [PactType.CanCompleteBeforeTock] using hComplete
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp only [canCompleteBeforeTockSubst, hName, if_false]
            exact ih (sizeOf body) hBodySize body
              (by simpa [PactType.CanCompleteBeforeTock] using hComplete) rfl
      | choice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | fairChoice _ bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.BranchCanCompleteBeforeTock rest = true →
              branchCanCompleteBeforeTockSubst name value rest = true := by
            intro rest
            induction rest with
            | nil => intro _ hNil
                     simp [PactType.BranchCanCompleteBeforeTock] at hNil
            | cons branch tail ihTail =>
                intro hRestSize hCons
                have hBranchSize : sizeOf branch.2 < n := by
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                have hTailSize : sizeOf tail < n := by
                  have hHead : sizeOf tail < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.BranchCanCompleteBeforeTock at hCons
                unfold branchCanCompleteBeforeTockSubst
                simp only [Bool.or_eq_true] at hCons ⊢
                rcases hCons with hHead | hTail
                · exact Or.inl (ih (sizeOf branch.2) hBranchSize branch.2
                    hHead rfl)
                · exact Or.inr (ihTail hTailSize hTail)
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hElse | hBranch
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType hElse rfl)
          · exact Or.inr (hBranches branches hBranchesSize hBranch)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.BranchCanCompleteBeforeTock rest = true →
              branchCanCompleteBeforeTockSubst name value rest = true := by
            intro rest
            induction rest with
            | nil => intro _ hNil
                     simp [PactType.BranchCanCompleteBeforeTock] at hNil
            | cons branch tail ihTail =>
                intro hRestSize hCons
                have hBranchSize : sizeOf branch.2 < n := by
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                have hTailSize : sizeOf tail < n := by
                  have hHead : sizeOf tail < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.BranchCanCompleteBeforeTock at hCons
                unfold branchCanCompleteBeforeTockSubst
                simp only [Bool.or_eq_true] at hCons ⊢
                rcases hCons with hHead | hTail
                · exact Or.inl (ih (sizeOf branch.2) hBranchSize branch.2
                    hHead rfl)
                · exact Or.inr (ihTail hTailSize hTail)
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hElse | hBranch
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType hElse rfl)
          · exact Or.inr (hBranches branches hBranchesSize hBranch)

/- Interpreting the distinguished variable as non-completing is exactly the
ordinary completion analysis, which already assigns `false` to every bare
variable.  The branch-list statement is carried locally because exclusive and
conjunctive offers fold the same Boolean disjunction over their branches. -/
theorem PactType.canCompleteBeforeTockSubst_false (name : String) :
    ∀ processType,
      canCompleteBeforeTockSubst name false processType =
        processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCanCompleteBeforeTockSubst name false branches =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            simp [branchCanCompleteBeforeTockSubst,
              PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            have hBranchSize : sizeOf branch.2 < n := by
              have hPair : sizeOf branch.2 < sizeOf branch := by
                obtain ⟨action, branchType⟩ := branch
                simp_wf
                omega
              have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest < sizeOf (branch :: rest) := by
                simp_wf
                omega
              omega
            unfold branchCanCompleteBeforeTockSubst
              PactType.BranchCanCompleteBeforeTock
            rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
              restIH hRestSize]
      cases processType with
      | message _ msg dir =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | progress _ pid =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | tock _ =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | skip _ =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | var _ other => simp [canCompleteBeforeTockSubst,
          PactType.CanCompleteBeforeTock]
      | recur _ other body =>
          by_cases hName : name = other
          · simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName, ih (sizeOf body) hBodySize body rfl]
      | choice _ left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice _ bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]

/-- Same-cycle completion commutes with capture-avoiding substitution. -/
theorem PactType.replaceVar_canCompleteBeforeTock
    (name : String) (replacement : PactType) : ∀ processType : PactType,
    (processType.replaceVar name replacement).CanCompleteBeforeTock =
      canCompleteBeforeTockSubst name replacement.CanCompleteBeforeTock
        processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BranchCanCompleteBeforeTock
              (PactType.replaceBranches branches name replacement) =
            branchCanCompleteBeforeTockSubst name
              replacement.CanCompleteBeforeTock branches := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            simp [PactType.replaceBranches,
              PactType.BranchCanCompleteBeforeTock,
              branchCanCompleteBeforeTockSubst]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            simp only [PactType.replaceBranches,
              PactType.BranchCanCompleteBeforeTock,
              branchCanCompleteBeforeTockSubst]
            rw [ih (sizeOf branchType) hBranchSize branchType rfl,
              restIH hRestSize]
      cases processType with
      | message _ msg dir =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | progress _ pid =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | tock _ =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | skip _ =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | var _ other =>
          by_cases hName : name = other
          · simp [PactType.replaceVar,
              canCompleteBeforeTockSubst, hName]
          · simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, hName]
      | recur _ other body =>
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hName : name = other
          · simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, hName]
          · simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, hName,
              ih (sizeOf body) hBodySize body rfl]
      | choice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice _ bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]

/-- Interpreting a recursive-call variable by the completion value of its
own body is a Boolean fixed point.  This is the syntax equation matched by a
recursion backedge in the constructor graph. -/
theorem PactType.canCompleteBeforeTockSubst_self
    (name : String) (processType : PactType) :
    canCompleteBeforeTockSubst name processType.CanCompleteBeforeTock
        processType = processType.CanCompleteBeforeTock := by
  cases hComplete : processType.CanCompleteBeforeTock with
  | false =>
      simpa [hComplete] using
        PactType.canCompleteBeforeTockSubst_false name processType
  | true =>
      simpa [hComplete] using
        PactType.canCompleteBeforeTock_le_subst name true processType hComplete

/- Substitution preserves the absence of a free tail occurrence when both
the substituted syntax and the replacement have that property. -/
/- A name forbidden from every free tail position does not occur freely at
all, so capture-avoiding substitution for that name is inert.  This is the
syntax bridge used by the recursion correspondence in every non-tail context
(sequence-left, parallel children, and conjunctive-offer branches). -/
theorem PactType.replaceVar_eq_self_of_tailOccurrences_false
    (name : String) (replacement : PactType) :
    ∀ processType : PactType,
      processType.TailOccurrences name False →
        processType.replaceVar name replacement = processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hTail
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name False branches →
          PactType.replaceBranches branches name replacement = branches := by
        intro branches hBranchesSize hBranchTail
        induction branches with
        | nil => simp [PactType.replaceBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailOccurrences name False ∧
                PactType.TailBranchOccurrences name False rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchTail
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
            simp only [PactType.replaceBranches]
            rw [ih (sizeOf branchType) hBranchSize branchType rfl hFields.1,
              restIH hRestSize hFields.2]
      cases processType with
      | message _ msg dir => simp [PactType.replaceVar]
      | progress _ pid => simp [PactType.replaceVar]
      | tock _ => simp [PactType.replaceVar]
      | skip _ => simp [PactType.replaceVar]
      | var _ other =>
          have hAbsent : name ≠ other := by
            intro hEq
            simp only [PactType.TailOccurrences] at hTail
            exact hTail hEq.symm
          simp [PactType.replaceVar, hAbsent]
      | recur _ binder body =>
          by_cases hShadow : name = binder
          · simp [PactType.replaceVar, hShadow]
          · have hBodyTail : body.TailOccurrences name False := by
              have hBinder : binder ≠ name := by exact Ne.symm hShadow
              simpa only [PactType.TailOccurrences, if_neg hBinder] using hTail
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp [PactType.replaceVar, hShadow,
              ih (sizeOf body) hBodySize body rfl hBodyTail]
      | choice _ left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | fairChoice _ bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | seq _ left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | par _ left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | xoffer _ elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]
      | offer _ elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]

/-- Branch-list form of `replaceVar_eq_self_of_tailOccurrences_false`. -/
theorem PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
    (name : String) (replacement : PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailBranchOccurrences name False branches →
        PactType.replaceBranches branches name replacement = branches := by
  intro branches hTail
  induction branches with
  | nil => simp [PactType.replaceBranches]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      have hFields : processType.TailOccurrences name False ∧
          PactType.TailBranchOccurrences name False rest := by
        simpa only [PactType.TailBranchOccurrences] using hTail
      simp only [PactType.replaceBranches]
      rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name replacement
          processType hFields.1,
        ih hFields.2]

/-- Substituting for a name confined to tail positions transports a tail-
occurrence fact: the replacement lands only where the ambient tail parameter
is the one it was checked against.  The disjunction covers substituting for
the very name being tracked, where the ambient fact is the confinement
itself. -/
theorem PactType.tailOccurrences_replaceVar
    (name other : String) {replacement : PactType} :
    ∀ (processType : PactType) (tail : Prop),
      replacement.TailOccurrences name tail →
      processType.TailOccurrences other True →
      (other = name ∨ processType.TailOccurrences name tail) →
        (processType.replaceVar other replacement).TailOccurrences name tail := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro tail hReplacement hOther hName
      -- Given this, now we need to prove the two constant-`False` contexts
      -- (sequence-left, parallel children, conjunctive branches) are inert.
      have hInertOccurrences : ∀ child : PactType,
          child.TailOccurrences other False →
          (other = name ∨ child.TailOccurrences name False) →
          (child.replaceVar other replacement).TailOccurrences name False := by
        intro child hChildOther hChildName
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false other
          replacement child hChildOther]
        rcases hChildName with hEq | hChild
        · exact hEq ▸ hChildOther
        · exact hChild
      have hInertBranches : ∀ branches : List (BareMessage × PactType),
          PactType.TailBranchOccurrences other False branches →
          (other = name ∨ PactType.TailBranchOccurrences name False branches) →
          PactType.TailBranchOccurrences name False
            (PactType.replaceBranches branches other replacement) := by
        intro branches hBranchesOther hBranchesName
        rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
          other replacement branches hBranchesOther]
        rcases hBranchesName with hEq | hBranches
        · exact hEq ▸ hBranchesOther
        · exact hBranches
      have hBranchesRec : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailBranchOccurrences other True branches →
          (other = name ∨ PactType.TailBranchOccurrences name tail branches) →
          PactType.TailBranchOccurrences name tail
            (PactType.replaceBranches branches other replacement) := by
        intro branches hBranchesSize hBranchesOther hBranchesName
        induction branches with
        | nil => simp [PactType.replaceBranches, PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hOtherFields : branchType.TailOccurrences other True ∧
                PactType.TailBranchOccurrences other True rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchesOther
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
            have hNameFields : (other = name ∨
                  branchType.TailOccurrences name tail) ∧
                (other = name ∨
                  PactType.TailBranchOccurrences name tail rest) := by
              rcases hBranchesName with hEq | hBranches
              · exact ⟨Or.inl hEq, Or.inl hEq⟩
              · have hSplit : branchType.TailOccurrences name tail ∧
                    PactType.TailBranchOccurrences name tail rest := by
                  simpa only [PactType.TailBranchOccurrences] using hBranches
                exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
            simpa only [PactType.replaceBranches,
              PactType.TailBranchOccurrences] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl tail
                  hReplacement hOtherFields.1 hNameFields.1)
                (restIH hRestSize hOtherFields.2 hNameFields.2)
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.TailOccurrences]
      | var _ current =>
          by_cases hCurrent : other = current
          · simpa [PactType.replaceVar, hCurrent] using hReplacement
          · rcases hName with hEq | hProcess
            · simp only [PactType.replaceVar, if_neg hCurrent,
                PactType.TailOccurrences]
              intro hVar
              exact absurd (hEq.trans hVar.symm) hCurrent
            · simpa only [PactType.replaceVar, if_neg hCurrent] using hProcess
      | recur _ binder body =>
          by_cases hBinderName : binder = name
          · by_cases hShadow : other = binder
            · simp only [PactType.replaceVar, if_pos hShadow,
                PactType.TailOccurrences, if_pos hBinderName]
            · simp only [PactType.replaceVar, if_neg hShadow,
                PactType.TailOccurrences, if_pos hBinderName]
          · by_cases hShadow : other = binder
            · simp only [PactType.replaceVar, if_pos hShadow,
                PactType.TailOccurrences, if_neg hBinderName]
              rcases hName with hEq | hProcess
              · exact absurd (hShadow.symm.trans hEq) hBinderName
              · simpa only [PactType.TailOccurrences, if_neg hBinderName]
                  using hProcess
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              have hBodyOther : body.TailOccurrences other True := by
                simpa only [PactType.TailOccurrences,
                  if_neg (fun h : binder = other => hShadow h.symm)] using hOther
              have hBodyName : other = name ∨
                  body.TailOccurrences name tail := by
                rcases hName with hEq | hProcess
                · exact Or.inl hEq
                · exact Or.inr (by
                    simpa only [PactType.TailOccurrences, if_neg hBinderName]
                      using hProcess)
              simpa only [PactType.replaceVar, if_neg hShadow,
                PactType.TailOccurrences, if_neg hBinderName] using
                ih (sizeOf body) hBodySize body rfl tail hReplacement hBodyOther
                  hBodyName
      | choice _ left right | fairChoice _ _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hOtherFields : left.TailOccurrences other True ∧
              right.TailOccurrences other True := by
            simpa only [PactType.TailOccurrences] using hOther
          have hNameFields : (other = name ∨ left.TailOccurrences name tail) ∧
              (other = name ∨ right.TailOccurrences name tail) := by
            rcases hName with hEq | hProcess
            · exact ⟨Or.inl hEq, Or.inl hEq⟩
            · have hSplit : left.TailOccurrences name tail ∧
                  right.TailOccurrences name tail := by
                simpa only [PactType.TailOccurrences] using hProcess
              exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl tail hReplacement
                hOtherFields.1 hNameFields.1)
              (ih (sizeOf right) hRightSize right rfl tail hReplacement
                hOtherFields.2 hNameFields.2)
      | seq _ left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hOtherFields : left.TailOccurrences other False ∧
              right.TailOccurrences other True := by
            simpa only [PactType.TailOccurrences] using hOther
          have hNameFields : (other = name ∨ left.TailOccurrences name False) ∧
              (other = name ∨ right.TailOccurrences name tail) := by
            rcases hName with hEq | hProcess
            · exact ⟨Or.inl hEq, Or.inl hEq⟩
            · have hSplit : left.TailOccurrences name False ∧
                  right.TailOccurrences name tail := by
                simpa only [PactType.TailOccurrences] using hProcess
              exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (hInertOccurrences left hOtherFields.1 hNameFields.1)
              (ih (sizeOf right) hRightSize right rfl tail hReplacement
                hOtherFields.2 hNameFields.2)
      | par _ left right _ =>
          have hOtherFields : left.TailOccurrences other False ∧
              right.TailOccurrences other False := by
            simpa only [PactType.TailOccurrences] using hOther
          have hNameFields : (other = name ∨ left.TailOccurrences name False) ∧
              (other = name ∨ right.TailOccurrences name False) := by
            rcases hName with hEq | hProcess
            · exact ⟨Or.inl hEq, Or.inl hEq⟩
            · have hSplit : left.TailOccurrences name False ∧
                  right.TailOccurrences name False := by
                simpa only [PactType.TailOccurrences] using hProcess
              exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (hInertOccurrences left hOtherFields.1 hNameFields.1)
              (hInertOccurrences right hOtherFields.2 hNameFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hOtherFields : elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other True branches := by
            simpa only [PactType.TailOccurrences] using hOther
          have hNameFields :
              (other = name ∨ elseType.TailOccurrences name tail) ∧
              (other = name ∨
                PactType.TailBranchOccurrences name tail branches) := by
            rcases hName with hEq | hProcess
            · exact ⟨Or.inl hEq, Or.inl hEq⟩
            · have hSplit : elseType.TailOccurrences name tail ∧
                  PactType.TailBranchOccurrences name tail branches := by
                simpa only [PactType.TailOccurrences] using hProcess
              exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl tail
                hReplacement hOtherFields.1 hNameFields.1)
              (hBranchesRec branches hBranchesSize hOtherFields.2
                hNameFields.2)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hOtherFields : elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other False branches := by
            simpa only [PactType.TailOccurrences] using hOther
          have hNameFields :
              (other = name ∨ elseType.TailOccurrences name tail) ∧
              (other = name ∨
                PactType.TailBranchOccurrences name False branches) := by
            rcases hName with hEq | hProcess
            · exact ⟨Or.inl hEq, Or.inl hEq⟩
            · have hSplit : elseType.TailOccurrences name tail ∧
                  PactType.TailBranchOccurrences name False branches := by
                simpa only [PactType.TailOccurrences] using hProcess
              exact ⟨Or.inr hSplit.1, Or.inr hSplit.2⟩
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl tail
                hReplacement hOtherFields.1 hNameFields.1)
              (hInertBranches branches hOtherFields.2 hNameFields.2)

/-- A branch body of a branch list satisfying `TailBranchOccurrences` inherits
that judgement. -/
theorem PactType.tailOccurrences_of_mem_branches (name : String) (tail : Prop)
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.TailBranchOccurrences name tail branches)
    {branch : BareMessage × PactType} (hMember : branch ∈ branches) :
    branch.2.TailOccurrences name tail := by
  induction branches with
  | nil => cases hMember
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      have hSplit : headType.TailOccurrences name tail ∧
          PactType.TailBranchOccurrences name tail rest := by
        simpa only [PactType.TailBranchOccurrences] using hBranches
      simp only [List.mem_cons] at hMember
      rcases hMember with hEq | hMem
      · exact hEq ▸ hSplit.1
      · exact ih hSplit.2 hMem

/-- A name bound nowhere in a type satisfies every tail-occurrence obligation
there: the only clause that can fail is a `.var` leaf naming it, and every
`.var` leaf is covered by a bound list the name is absent from. -/
theorem PactType.tailOccurrences_of_allVariablesBound_notMem (name : String) :
    ∀ (processType : PactType) (bound : List String) (tail : Prop),
      PactType.AllVariablesBound bound processType → name ∉ bound →
        processType.TailOccurrences name tail := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (bound : List String) (tail : Prop), sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches → name ∉ bound →
          PactType.TailBranchOccurrences name tail branches := by
        intro branches bound tail hBranchesSize hBound hNotMem
        induction branches with
        | nil => simp [PactType.TailBranchOccurrences]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : PactType.AllVariablesBound bound branchType ∧
                PactType.AllBranchVariablesBound bound rest := by
              simpa only [PactType.AllBranchVariablesBound] using hBound
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hTailSize : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simpa only [PactType.TailBranchOccurrences] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl bound
                  tail hFields.1 hNotMem)
                (restIH hRestSize hFields.2)
      intro bound tail hBound hNotMem
      cases processType with
      | message alphabet msg dir => simp [PactType.TailOccurrences]
      | progress alphabet pid => simp [PactType.TailOccurrences]
      | tock alphabet => simp [PactType.TailOccurrences]
      | skip alphabet => simp [PactType.TailOccurrences]
      | var alphabet other =>
          simp only [PactType.AllVariablesBound] at hBound
          simp only [PactType.TailOccurrences]
          intro hEq
          exact absurd (hEq ▸ hBound) hNotMem
      | choice alphabet left right =>
          have hFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl bound tail hFields.1
                hNotMem)
              (ih (sizeOf right) hRightSize right rfl bound tail hFields.2
                hNotMem)
      | seq alphabet left right =>
          have hFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl bound False hFields.1
                hNotMem)
              (ih (sizeOf right) hRightSize right rfl bound tail hFields.2
                hNotMem)
      | par alphabet left right interface =>
          have hFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl bound False hFields.1
                hNotMem)
              (ih (sizeOf right) hRightSize right rfl bound False hFields.2
                hNotMem)
      | fairChoice alphabet bid left right =>
          have hFields : PactType.AllVariablesBound bound left ∧
              PactType.AllVariablesBound bound right := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl bound tail hFields.1
                hNotMem)
              (ih (sizeOf right) hRightSize right rfl bound tail hFields.2
                hNotMem)
      | recur alphabet other body =>
          simp only [PactType.TailOccurrences]
          by_cases hEq : other = name
          · simp [hEq]
          · simp only [hEq, if_false]
            have hBodyBound : PactType.AllVariablesBound (other :: bound) body := by
              simpa only [PactType.AllVariablesBound] using hBound
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            refine ih (sizeOf body) hBodySize body rfl (other :: bound) tail
              hBodyBound ?_
            simp only [List.mem_cons, not_or]
            exact ⟨fun hContra => hEq hContra.symm, hNotMem⟩
      | xoffer alphabet elseType branches =>
          have hFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl bound tail
                hFields.1 hNotMem)
              (hBranches branches bound tail hBranchesSize hFields.2 hNotMem)
      | offer alphabet elseType branches =>
          have hFields : PactType.AllVariablesBound bound elseType ∧
              PactType.AllBranchVariablesBound bound branches := by
            simpa only [PactType.AllVariablesBound] using hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.TailOccurrences] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl bound tail
                hFields.1 hNotMem)
              (hBranches branches bound False hBranchesSize hFields.2 hNotMem)

/-- A closed type is tail-closed. -/
theorem PactType.tailClosed_of_allVariablesBound_nil {processType : PactType}
    (hBound : PactType.AllVariablesBound [] processType) :
    processType.TailClosed :=
  fun name => PactType.tailOccurrences_of_allVariablesBound_notMem name
    processType [] True hBound (by simp)

/-- Substituting a tail-closed tail-recursive replacement for a name confined
to tail positions preserves tail recursion: at every nested binder the
replacement lands where that binder's own tail discipline already holds. -/
theorem PactType.tailRecursive_replaceVar (other : String)
    {replacement : PactType} (hReplacementRec : replacement.TailRecursive)
    (hReplacementClosed : replacement.TailClosed) :
    ∀ processType : PactType,
      processType.TailRecursive →
      processType.TailOccurrences other True →
        (processType.replaceVar other replacement).TailRecursive := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hRec hOther
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailRecursiveBranches branches →
          (∀ branch ∈ branches, branch.2.TailOccurrences other True) →
          PactType.TailRecursiveBranches
            (PactType.replaceBranches branches other replacement) := by
        intro branches hBranchesSize hBranchesRec hBranchesOther
        induction branches with
        | nil => simp [PactType.replaceBranches, PactType.TailRecursiveBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailRecursive ∧
                PactType.TailRecursiveBranches rest := by
              simpa only [PactType.TailRecursiveBranches] using hBranchesRec
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
            simpa only [PactType.replaceBranches,
              PactType.TailRecursiveBranches] using
              And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                  hFields.1 (hBranchesOther (action, branchType) (by simp)))
                (restIH hRestSize hFields.2 (fun item hItem =>
                  hBranchesOther item (List.mem_cons_of_mem _ hItem)))
      have hInertBranches : ∀ branches : List (BareMessage × PactType),
          PactType.TailRecursiveBranches branches →
          PactType.TailBranchOccurrences other False branches →
          PactType.TailRecursiveBranches
            (PactType.replaceBranches branches other replacement) := by
        intro branches hBranchesRec hBranchesOther
        rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
          other replacement branches hBranchesOther]
        exact hBranchesRec
      have hInert : ∀ child : PactType, child.TailRecursive →
          child.TailOccurrences other False →
          (child.replaceVar other replacement).TailRecursive := by
        intro child hChildRec hChildOther
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false other
          replacement child hChildOther]
        exact hChildRec
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ =>
          simp [PactType.replaceVar, PactType.TailRecursive]
      | var _ current =>
          by_cases hCurrent : other = current
          · simpa [PactType.replaceVar, hCurrent] using hReplacementRec
          · simp [PactType.replaceVar, hCurrent, PactType.TailRecursive]
      | recur _ binder body =>
          have hFields : body.TailOccurrences binder True ∧ body.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          by_cases hShadow : other = binder
          · simpa only [PactType.replaceVar, if_pos hShadow,
              PactType.TailRecursive] using hFields
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            have hBodyOther : body.TailOccurrences other True := by
              simpa only [PactType.TailOccurrences,
                if_neg (fun h : binder = other => hShadow h.symm)] using hOther
            simpa only [PactType.replaceVar, if_neg hShadow,
              PactType.TailRecursive] using
              And.intro (PactType.tailOccurrences_replaceVar binder other body
                  True (hReplacementClosed binder) hBodyOther
                  (Or.inr hFields.1))
                (ih (sizeOf body) hBodySize body rfl hFields.2 hBodyOther)
      | choice _ left right | fairChoice _ _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          have hOtherFields : left.TailOccurrences other True ∧
              right.TailOccurrences other True := by
            simpa only [PactType.TailOccurrences] using hOther
          simpa only [PactType.replaceVar, PactType.TailRecursive] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1
                hOtherFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2 hOtherFields.2)
      | seq _ left right =>
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          have hOtherFields : left.TailOccurrences other False ∧
              right.TailOccurrences other True := by
            simpa only [PactType.TailOccurrences] using hOther
          simpa only [PactType.replaceVar, PactType.TailRecursive] using
            And.intro (hInert left hFields.1 hOtherFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2 hOtherFields.2)
      | par _ left right _ =>
          have hFields : left.TailRecursive ∧ right.TailRecursive := by
            simpa only [PactType.TailRecursive] using hRec
          have hOtherFields : left.TailOccurrences other False ∧
              right.TailOccurrences other False := by
            simpa only [PactType.TailOccurrences] using hOther
          simpa only [PactType.replaceVar, PactType.TailRecursive] using
            And.intro (hInert left hFields.1 hOtherFields.1)
              (hInert right hFields.2 hOtherFields.2)
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hRec
          have hOtherFields : elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other True branches := by
            simpa only [PactType.TailOccurrences] using hOther
          have hBranchOther : ∀ branch ∈ branches,
              branch.2.TailOccurrences other True := fun _ hBranch =>
            PactType.tailOccurrences_of_mem_branches other True hOtherFields.2
              hBranch
          simpa only [PactType.replaceVar, PactType.TailRecursive] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl hFields.1
                hOtherFields.1)
              (hBranches branches hBranchesSize hFields.2 hBranchOther)
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hFields : elseType.TailRecursive ∧
              PactType.TailRecursiveBranches branches := by
            simpa only [PactType.TailRecursive] using hRec
          have hOtherFields : elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other False branches := by
            simpa only [PactType.TailOccurrences] using hOther
          simpa only [PactType.replaceVar, PactType.TailRecursive] using
            And.intro (ih (sizeOf elseType) hElseSize elseType rfl hFields.1
                hOtherFields.1)
              (hInertBranches branches hFields.2 hOtherFields.2)
end

end Pact
