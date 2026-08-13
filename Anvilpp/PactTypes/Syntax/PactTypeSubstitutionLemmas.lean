import Anvilpp.PactTypes.Syntax.PactTypeCompletionEval

/-!
# Substitution lemmas for CanCompleteBeforeTock and tail-occurrence transport
-/

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
      | message msg dir => simp [canCompleteBeforeTockSubst]
      | progress pid => simp [canCompleteBeforeTockSubst]
      | skip => simp [canCompleteBeforeTockSubst]
      | tock => simp [PactType.CanCompleteBeforeTock] at hComplete
      | var other => simp [PactType.CanCompleteBeforeTock] at hComplete
      | recur other body =>
          by_cases hName : name = other
          · subst hName
            simp only [canCompleteBeforeTockSubst, if_pos rfl]
            simpa [PactType.CanCompleteBeforeTock] using hComplete
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp only [canCompleteBeforeTockSubst, hName, if_false]
            exact ih (sizeOf body) hBodySize body
              (by simpa [PactType.CanCompleteBeforeTock] using hComplete) rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | xoffer elseType branches =>
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
      | offer elseType branches =>
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
      | message msg dir =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | var other => simp [canCompleteBeforeTockSubst,
          PactType.CanCompleteBeforeTock]
      | recur other body =>
          by_cases hName : name = other
          · simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName, ih (sizeOf body) hBodySize body rfl]
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
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
      | par left right interface =>
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
      | xoffer elseType branches =>
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
      | offer elseType branches =>
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

/-- The ordinary syntax predicate is `completionEval` in the everywhere-false
variable environment. -/
theorem PactType.completionEval_eq_canCompleteBeforeTock_of_all_false
    (valuation : String → Bool) : ∀ processType,
    (∀ name, valuation name = false) →
      completionEval valuation processType = processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType valuation with
  | _ n ih =>
      intro hFalse
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval valuation branches =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval,
            PactType.BranchCanCompleteBeforeTock]
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
            simp only [branchCompletionEval,
              PactType.BranchCanCompleteBeforeTock]
            rw [ih (sizeOf branchType) hBranchSize valuation branchType rfl hFalse,
              restIH hRestSize]
      cases processType with
      | message msg dir =>
          simp [completionEval, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [completionEval, PactType.CanCompleteBeforeTock]
      | tock => simp [completionEval, PactType.CanCompleteBeforeTock]
      | skip => simp [completionEval, PactType.CanCompleteBeforeTock]
      | var name => simp [completionEval, PactType.CanCompleteBeforeTock, hFalse]
      | recur name body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          rw [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf body) hBodySize (Function.update valuation name false)
              body rfl]
          intro other
          by_cases hEq : other = name
          · subst other
            simp
          · simp [Function.update, hEq, hFalse]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFalse,
            hBranches branches hBranchesSize]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFalse,
            hBranches branches hBranchesSize]

/-- The one-variable completion fold is the singleton specialization of the
finite-control valuation semantics.  This is the bridge used when the old
scalar recursion lemmas are lifted to the binder-context induction. -/
theorem PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst
    (name : String) (value : Bool) : ∀ processType : PactType,
    completionEval (Function.update (fun _ => false) name value) processType =
      canCompleteBeforeTockSubst name value processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      let valuation : String → Bool :=
        Function.update (fun _ => false) name value
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval valuation branches =
            branchCanCompleteBeforeTockSubst name value branches := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval,
            branchCanCompleteBeforeTockSubst]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by
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
            simp only [branchCompletionEval,
              branchCanCompleteBeforeTockSubst]
            rw [show completionEval valuation branchType =
                canCompleteBeforeTockSubst name value branchType by
                  simpa [valuation] using
                    ih (sizeOf branchType) hBranchSize branchType rfl,
              restIH hRestSize]
      cases processType with
      | message msg dir =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | progress pid =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | tock =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | skip =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | var other =>
          by_cases hName : other = name
          · subst other
            simp [valuation, completionEval, canCompleteBeforeTockSubst]
          · simp [valuation, completionEval, canCompleteBeforeTockSubst,
              hName, Ne.symm hName]
      | recur other body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          by_cases hName : name = other
          · subst other
            rw [completionEval, canCompleteBeforeTockSubst]
            simp only [if_pos rfl]
            apply completionEval_eq_canCompleteBeforeTock_of_all_false
            intro variableName
            by_cases hEq : variableName = name
            · subst variableName
              simp [valuation]
            · simp [valuation, Function.update, hEq]
          · rw [completionEval, canCompleteBeforeTockSubst, if_neg hName]
            have hValuationEq : Function.update valuation other false =
                valuation := by
              funext variableName
              by_cases hOther : variableName = other
              · subst variableName
                simp [valuation, Function.update, hName, Ne.symm hName]
              · simp [Function.update, hOther]
            rw [hValuationEq]
            simpa [valuation] using
              ih (sizeOf body) hBodySize body rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]

/-- `completionEval` is monotone in the Boolean interpretation of free
variables.  Binders preserve monotonicity by assigning `false` to the bound
name in both environments. -/
theorem PactType.completionEval_mono
    (source target : String → Bool)
    (hLe : ∀ name, source name = true → target name = true) :
    ∀ processType,
      completionEval source processType = true →
        completionEval target processType = true := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType source target with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval source branches = true →
            branchCompletionEval target branches = true := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval]
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
            simp only [branchCompletionEval, Bool.or_eq_true]
            intro h
            rcases h with h | h
            · exact Or.inl (ih (sizeOf branchType) hBranchSize source target
                hLe branchType rfl h)
            · exact Or.inr (restIH hRestSize h)
      cases processType with
      | message msg dir => simp [completionEval]
      | progress pid => simp [completionEval]
      | tock => simp [completionEval]
      | skip => simp [completionEval]
      | var name =>
          simpa [completionEval] using hLe name
      | recur name body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [completionEval]
          apply ih (sizeOf body) hBodySize
              (Function.update source name false)
              (Function.update target name false)
          · intro other hTrue
            by_cases hEq : other = name
            · subst other
              simp at hTrue
            · have hSource : source other = true := by
                simpa [Function.update, hEq] using hTrue
              simpa [Function.update, hEq] using hLe other hSource
          · rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf left) hLeftSize source target hLe left
                rfl h)
          · exact Or.inr (ih (sizeOf right) hRightSize source target hLe right
                rfl h)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf left) hLeftSize source target hLe left
                rfl h)
          · exact Or.inr (ih (sizeOf right) hRightSize source target hLe right
                rfl h)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.and_eq_true]
          rintro ⟨hLeft, hRight⟩
          exact ⟨ih (sizeOf left) hLeftSize source target hLe left rfl hLeft,
            ih (sizeOf right) hRightSize source target hLe right rfl hRight⟩
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.and_eq_true]
          rintro ⟨hLeft, hRight⟩
          exact ⟨ih (sizeOf left) hLeftSize source target hLe left rfl hLeft,
            ih (sizeOf right) hRightSize source target hLe right rfl hRight⟩
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf elseType) hElseSize source target hLe
                elseType rfl h)
          · exact Or.inr (hBranches branches hBranchesSize h)
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf elseType) hElseSize source target hLe
                elseType rfl h)
          · exact Or.inr (hBranches branches hBranchesSize h)

/-- The completion value of a recursive body is a Boolean fixed point when
fed back to the corresponding variable. -/
theorem PactType.completionEval_update_self
    (valuation : String → Bool) (name : String) (processType : PactType) :
    completionEval
        (Function.update valuation name
          (completionEval (Function.update valuation name false) processType))
        processType =
      completionEval (Function.update valuation name false) processType := by
  let base := Function.update valuation name false
  cases hValue : completionEval base processType with
  | false => simp [base, hValue]
  | true =>
      have hMono := completionEval_mono base
        (Function.update valuation name true) (processType := processType)
          (by
            intro other hTrue
            by_cases hEq : other = name
            · subst other
              simp
            · simpa [base, Function.update, hEq] using hTrue)
      simpa [base, hValue] using hMono hValue

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

/-- A variable forbidden from tail position cannot affect optimistic
completion.  This is the exact elimination rule used in the recursion proof:
sequence-left, parallel, and conjunctive-offer branch contexts all impose
`TailOccurrences name False`, so their parametric completion reduces to the
ordinary syntax predicate. -/
theorem PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
    (name : String) (value : Bool) : ∀ processType,
    processType.TailOccurrences name False →
      canCompleteBeforeTockSubst name value processType =
        processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hTail
      cases processType with
      | message msg dir =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | var other =>
          have hNe : name ≠ other := by
            intro hEq
            have hImpossible : False := by
              simp only [PactType.TailOccurrences] at hTail
              apply hTail
              exact hEq.symm
            exact hImpossible.elim
          simp [canCompleteBeforeTockSubst, hNe,
            PactType.CanCompleteBeforeTock]
      | recur other body =>
          by_cases hName : name = other
          · subst other
            simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
          · have hBodyTail : body.TailOccurrences name False := by
              simp only [PactType.TailOccurrences] at hTail
              rw [if_neg (Ne.symm hName)] at hTail
              exact hTail
            have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [canCompleteBeforeTockSubst, hName, if_false,
              PactType.CanCompleteBeforeTock]
            exact ih (sizeOf body) hBodySize body rfl hBodyTail
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchEq : PactType.branchCanCompleteBeforeTockSubst name value
                branches = PactType.BranchCanCompleteBeforeTock branches := by
            have hList : ∀ rest : List (BareMessage × PactType),
                sizeOf rest < n →
                PactType.TailBranchOccurrences name False rest →
                PactType.branchCanCompleteBeforeTockSubst name value rest =
                  PactType.BranchCanCompleteBeforeTock rest := by
              intro rest
              induction rest with
              | nil =>
                  intro _ _
                  simp [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock]
              | cons branch tail tailIH =>
                  intro hRestSize hRestTail
                  rcases branch with ⟨action, branchType⟩
                  have hBranchFields :
                      branchType.TailOccurrences name False ∧
                        PactType.TailBranchOccurrences name False tail := by
                    simpa only [PactType.TailBranchOccurrences] using
                      hRestTail
                  have hBranchSize : sizeOf branchType < n := by
                    have hPair : sizeOf branchType <
                        sizeOf (action, branchType) := by
                      simp_wf
                      omega
                    have hHead : sizeOf (action, branchType) <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  have hTailSize : sizeOf tail < n := by
                    have hTail : sizeOf tail <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  simp only [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock,
                    ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1,
                    tailIH hTailSize hBranchFields.2]
            apply hList branches
            · rw [← hSize]; simp_wf; omega
            · exact hFields.2
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranchEq]
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchEq : PactType.branchCanCompleteBeforeTockSubst name value
                branches = PactType.BranchCanCompleteBeforeTock branches := by
            have hList : ∀ rest : List (BareMessage × PactType),
                sizeOf rest < n →
                PactType.TailBranchOccurrences name False rest →
                PactType.branchCanCompleteBeforeTockSubst name value rest =
                  PactType.BranchCanCompleteBeforeTock rest := by
              intro rest
              induction rest with
              | nil =>
                  intro _ _
                  simp [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock]
              | cons branch tail tailIH =>
                  intro hRestSize hRestTail
                  rcases branch with ⟨action, branchType⟩
                  have hBranchFields :
                      branchType.TailOccurrences name False ∧
                        PactType.TailBranchOccurrences name False tail := by
                    simpa only [PactType.TailBranchOccurrences] using
                      hRestTail
                  have hBranchSize : sizeOf branchType < n := by
                    have hPair : sizeOf branchType <
                        sizeOf (action, branchType) := by
                      simp_wf
                      omega
                    have hHead : sizeOf (action, branchType) <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  have hTailSize : sizeOf tail < n := by
                    have hTail : sizeOf tail <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  simp only [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock,
                    ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1,
                    tailIH hTailSize hBranchFields.2]
            apply hList branches
            · rw [← hSize]; simp_wf; omega
            · exact hFields.2
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranchEq]

/- Substitution preserves the absence of a free tail occurrence when both
the substituted syntax and the replacement have that property. -/
theorem PactType.tailOccurrences_false_replaceVar
    (name other : String) (replacement : PactType)
    (hReplacement : replacement.TailOccurrences name False) :
    ∀ processType : PactType,
      processType.TailOccurrences name False →
        (processType.replaceVar other replacement).TailOccurrences
          name False := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hProcess
      have hOfferChildren : ∀ (elseType : PactType)
          (branches : List (BareMessage × PactType)),
          sizeOf elseType < n → sizeOf branches < n →
          elseType.TailOccurrences name False ∧
            PactType.TailBranchOccurrences name False branches →
          (elseType.replaceVar other replacement).TailOccurrences name False ∧
            PactType.TailBranchOccurrences name False
              (PactType.replaceBranches branches other replacement) := by
        intro elseType branches hElseSize hBranchesSize hFields
        have hBranches : PactType.TailBranchOccurrences name False
            (PactType.replaceBranches branches other replacement) := by
          have hList : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.TailBranchOccurrences name False rest →
              PactType.TailBranchOccurrences name False
                (PactType.replaceBranches rest other replacement) := by
            intro rest
            induction rest with
            | nil =>
                intro _ _
                simp [PactType.replaceBranches,
                  PactType.TailBranchOccurrences]
            | cons branch rest ihRest =>
                intro hRestSize hRestTail
                rcases branch with ⟨action, branchType⟩
                have hBranchFields :
                    branchType.TailOccurrences name False ∧
                      PactType.TailBranchOccurrences name False rest := by
                  simpa only [PactType.TailBranchOccurrences] using hRestTail
                have hBranchSize : sizeOf branchType < n := by
                  have hPair : sizeOf branchType <
                      sizeOf (action, branchType) := by simp_wf; omega
                  have hHead : sizeOf (action, branchType) <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                have hTailSize : sizeOf rest < n := by
                  have hTail : sizeOf rest <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                simpa only [PactType.replaceBranches,
                  PactType.TailBranchOccurrences] using And.intro
                    (ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1)
                    (ihRest hTailSize hBranchFields.2)
          exact hList branches hBranchesSize hFields.2
        exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
          hBranches⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.TailOccurrences]
      | progress pid => simp [PactType.replaceVar, PactType.TailOccurrences]
      | tock => simp [PactType.replaceVar, PactType.TailOccurrences]
      | skip => simp [PactType.replaceVar, PactType.TailOccurrences]
      | var current =>
          by_cases hCurrent : other = current
          · simpa [PactType.replaceVar, hCurrent] using hReplacement
          · simpa [PactType.replaceVar, hCurrent,
              PactType.TailOccurrences] using hProcess
      | recur binder body =>
          by_cases hShadow : other = binder
          · simpa [PactType.replaceVar, hShadow] using hProcess
          · by_cases hBinder : binder = name
            · subst binder
              simp [PactType.replaceVar, hShadow, PactType.TailOccurrences]
            · have hBodyTail : body.TailOccurrences name False := by
                simpa [PactType.TailOccurrences, hBinder] using hProcess
              have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              simpa [PactType.replaceVar, hShadow,
                PactType.TailOccurrences, hBinder] using
                  ih (sizeOf body) hBodySize body rfl hBodyTail
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize hFields
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize hFields

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
      | message msg dir => simp [PactType.replaceVar]
      | progress pid => simp [PactType.replaceVar]
      | tock => simp [PactType.replaceVar]
      | skip => simp [PactType.replaceVar]
      | var other =>
          have hAbsent : name ≠ other := by
            intro hEq
            simp only [PactType.TailOccurrences] at hTail
            exact hTail hEq.symm
          simp [PactType.replaceVar, hAbsent]
      | recur binder body =>
          by_cases hShadow : name = binder
          · simp [PactType.replaceVar, hShadow]
          · have hBodyTail : body.TailOccurrences name False := by
              have hBinder : binder ≠ name := by exact Ne.symm hShadow
              simpa only [PactType.TailOccurrences, if_neg hBinder] using hTail
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp [PactType.replaceVar, hShadow,
              ih (sizeOf body) hBodySize body rfl hBodyTail]
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
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
      | par left right interface =>
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
      | xoffer elseType branches =>
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
      | offer elseType branches =>
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

/- Replacing every free occurrence of a name by its own binder removes that
name from all non-tail positions, independently of the original syntax. -/
theorem PactType.tailOccurrences_false_replaceVar_self_recur
    (name : String) (body : PactType) : ∀ processType : PactType,
    (processType.replaceVar name (.recur name body)).TailOccurrences
      name False := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hOfferChildren : ∀ (elseType : PactType)
          (branches : List (BareMessage × PactType)),
          sizeOf elseType < n → sizeOf branches < n →
          (elseType.replaceVar name (.recur name body)).TailOccurrences
              name False ∧
            PactType.TailBranchOccurrences name False
              (PactType.replaceBranches branches name (.recur name body)) := by
        intro elseType branches hElseSize hBranchesSize
        have hBranches : PactType.TailBranchOccurrences name False
            (PactType.replaceBranches branches name (.recur name body)) := by
          have hList : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.TailBranchOccurrences name False
                (PactType.replaceBranches rest name (.recur name body)) := by
            intro rest
            induction rest with
            | nil =>
                intro _
                simp [PactType.replaceBranches,
                  PactType.TailBranchOccurrences]
            | cons branch rest ihRest =>
                intro hRestSize
                rcases branch with ⟨action, branchType⟩
                have hBranchSize : sizeOf branchType < n := by
                  have hPair : sizeOf branchType <
                      sizeOf (action, branchType) := by simp_wf; omega
                  have hHead : sizeOf (action, branchType) <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                have hTailSize : sizeOf rest < n := by
                  have hTail : sizeOf rest <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                simpa only [PactType.replaceBranches,
                  PactType.TailBranchOccurrences] using And.intro
                    (ih (sizeOf branchType) hBranchSize branchType rfl)
                    (ihRest hTailSize)
          exact hList branches hBranchesSize
        exact ⟨ih (sizeOf elseType) hElseSize elseType rfl, hBranches⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.TailOccurrences]
      | progress pid => simp [PactType.replaceVar, PactType.TailOccurrences]
      | tock => simp [PactType.replaceVar, PactType.TailOccurrences]
      | skip => simp [PactType.replaceVar, PactType.TailOccurrences]
      | var current =>
          by_cases hCurrent : name = current
          · simp [PactType.replaceVar, hCurrent, PactType.TailOccurrences]
          · simp [PactType.replaceVar, hCurrent,
              PactType.TailOccurrences, Ne.symm hCurrent]
      | recur binder nestedBody =>
          by_cases hShadow : name = binder
          · simp [PactType.replaceVar, hShadow, PactType.TailOccurrences]
          · have hBinder : binder ≠ name := Ne.symm hShadow
            have hBodySize : sizeOf nestedBody < n := by
              rw [← hSize]; simp_wf; omega
            simpa [PactType.replaceVar, hShadow,
              PactType.TailOccurrences, hBinder] using
                ih (sizeOf nestedBody) hBodySize nestedBody rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize

/-- Replacing an occurrence protected by a clock does not change whether the
surrounding syntax can finish in the current cycle. -/
theorem PactType.guardedOccurrences_replace_canCompleteBeforeTock
    (name : String) (replacement processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) :
    (processType.replaceVar name replacement).CanCompleteBeforeTock =
      processType.CanCompleteBeforeTock := by
  let replaced := processType.replaceVar name replacement
  let fuel := max (sizeOf replaced + 1) (sizeOf processType + 1)
  have hReplacedFuel : sizeOf replaced < fuel := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_max_left (sizeOf replaced + 1) (sizeOf processType + 1))
  have hProcessFuel : sizeOf processType < fuel := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_max_right (sizeOf replaced + 1) (sizeOf processType + 1))
  calc
    replaced.CanCompleteBeforeTock =
        typeCanCompleteThisCycleFuel fuel replaced :=
      (typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
        fuel replaced hReplacedFuel).symm
    _ = typeCanCompleteThisCycleFuel fuel processType := by
      exact guardedOccurrences_replace_canCompleteThisCycleFuel
        name replacement processType hGuarded fuel
    _ = processType.CanCompleteBeforeTock :=
      typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
        fuel processType hProcessFuel

end

end Pact
