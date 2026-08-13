import Anvilpp.PactTypes.Syntax.TypeFutureOffersFuel

/-!
# Valuation-polymorphic completion evaluator and its substitution/hygiene transport
-/

namespace Pact

noncomputable section

mutual
  /-- `CanCompleteBeforeTock`, but every occurrence of `.var name` contributes
  `value` instead of the unconditional `false` used by `CanCompleteBeforeTock`
  itself.  Respects the same capture-avoiding shadowing as `replaceVar`: a
  nested `.recur name _` binder stops the substitution view of its own body,
  matching `replaceVar`'s `if var = other then .recur other body else ...`
  clause. -/
  def PactType.canCompleteBeforeTockSubst
      (name : String) (value : Bool) : PactType → Bool
    | .message _ _ | .progress _ | .skip => true
    | .tock => false
    | .var other => if name = other then value else false
    | .recur other body =>
        if name = other then PactType.CanCompleteBeforeTock body
        else canCompleteBeforeTockSubst name value body
    | .choice left right | .fairChoice _ left right =>
        canCompleteBeforeTockSubst name value left ||
          canCompleteBeforeTockSubst name value right
    | .seq left right | .par left right _ =>
        canCompleteBeforeTockSubst name value left &&
          canCompleteBeforeTockSubst name value right
    | .xoffer elseType branches | .offer elseType branches =>
        canCompleteBeforeTockSubst name value elseType ||
          branchCanCompleteBeforeTockSubst name value branches
  termination_by processType => sizeOf processType

  def PactType.branchCanCompleteBeforeTockSubst
      (name : String) (value : Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        canCompleteBeforeTockSubst name value processType ||
          branchCanCompleteBeforeTockSubst name value rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  /-- Optimistic completion under a finite-control interpretation of the free
  recursion variables.  Entering a binder shadows its own name with the
  ordinary (unfolded-call-free) value `false`; an installed backedge is
  represented separately by updating that name to the binder's completion
  value when its body is analysed. -/
  def PactType.completionEval (valuation : String → Bool) : PactType → Bool
    | .message _ _ | .progress _ | .skip => true
    | .tock => false
    | .var name => valuation name
    | .recur name body => completionEval (Function.update valuation name false) body
    | .choice left right | .fairChoice _ left right =>
        completionEval valuation left || completionEval valuation right
    | .seq left right | .par left right _ =>
        completionEval valuation left && completionEval valuation right
    | .xoffer elseType branches | .offer elseType branches =>
        completionEval valuation elseType ||
          branchCompletionEval valuation branches
  termination_by processType => sizeOf processType

  def PactType.branchCompletionEval (valuation : String → Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        completionEval valuation processType || branchCompletionEval valuation rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Completion evaluation depends only on the values of variables declared
free in the supplied binding context. -/
theorem PactType.completionEval_congr_of_allVariablesBound
    (bound : List String) (left right : String → Bool)
    (hAgree : ∀ name ∈ bound, left name = right name) :
    ∀ processType : PactType,
      PactType.AllVariablesBound bound processType →
        completionEval left processType = completionEval right processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound left right with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
            branchCompletionEval left branches =
              branchCompletionEval right branches := by
        intro branches hBranchesSize hBound
        induction branches with
        | nil => simp [branchCompletionEval]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hBound
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
            simp only [branchCompletionEval]
            rw [ih (sizeOf branchType) hBranchSize bound left right hAgree
                branchType rfl hBound.1,
              restIH hRestSize hBound.2]
      cases processType with
      | message msg dir => simp [completionEval]
      | progress pid => simp [completionEval]
      | tock => simp [completionEval]
      | skip => simp [completionEval]
      | var name =>
          intro hBound
          simpa [completionEval] using
            hAgree name (by simpa [PactType.AllVariablesBound] using hBound)
      | recur name body =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval]
          exact ih (sizeOf body) hBodySize (name :: bound)
            (Function.update left name false)
            (Function.update right name false)
            (by
              intro other hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with rfl | hMem
              · simp
              · by_cases hEq : other = name
                · subst other
                  simp
                · simpa [Function.update, hEq] using hAgree other hMem)
            body rfl hBound
      | choice leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | fairChoice bid leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | seq leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | par leftType rightType interface =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | xoffer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf elseType) hElseSize bound left right hAgree elseType rfl
              hBound.1,
            hBranches branches hBranchesSize hBound.2]
      | offer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf elseType) hElseSize bound left right hAgree elseType rfl
              hBound.1,
            hBranches branches hBranchesSize hBound.2]

/-- Hygienic substitution is interpreted by updating the completion
valuation.  Every name outside `active` is already interpreted as `false`, so
a nested binder fresh for `active` does not change the replacement's value;
the replacement itself need not be closed. -/
theorem PactType.completionEval_replaceVar_of_hygienic
    (active : List String) (valuation : String → Bool) (name : String)
    (replacement : PactType)
    (hSupported : ∀ other, other ∉ active → valuation other = false) :
    ∀ processType : PactType,
      processType.BinderFreshFor (name :: active) →
        completionEval valuation (processType.replaceVar name replacement) =
          completionEval
            (Function.update valuation name
              (completionEval valuation replacement)) processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active valuation with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: active) branches →
          branchCompletionEval valuation
              (PactType.replaceBranches branches name replacement) =
            branchCompletionEval
              (Function.update valuation name
                (completionEval valuation replacement)) branches := by
        intro branches hBranchesSize hHygienic
        induction branches with
        | nil => simp [PactType.replaceBranches, branchCompletionEval]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hHygienic
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
            simp only [PactType.replaceBranches, branchCompletionEval]
            rw [ih (sizeOf branchType) hBranchSize active valuation hSupported
                branchType rfl hHygienic.1,
              restIH hRestSize hHygienic.2]
      cases processType with
      | message msg dir => simp [PactType.replaceVar, completionEval]
      | progress pid => simp [PactType.replaceVar, completionEval]
      | tock => simp [PactType.replaceVar, completionEval]
      | skip => simp [PactType.replaceVar, completionEval]
      | var other =>
          intro _
          by_cases hEq : name = other
          · subst other
            simp [PactType.replaceVar, completionEval]
          · simp [PactType.replaceVar, completionEval, hEq, Ne.symm hEq]
      | recur other body =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hOtherName : other ≠ name := by
            intro hEq
            subst other
            exact hHygienic.1 (by simp)
          have hOtherActive : other ∉ active := by
            intro hMem
            exact hHygienic.1 (by simp [hMem])
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hSupported' : ∀ x, x ∉ active →
              Function.update valuation other false x = false := by
            intro x hx
            by_cases hEq : x = other
            · subst x
              simp
            · simpa [Function.update, hEq] using hSupported x hx
          have hReplacementEval :
              completionEval (Function.update valuation other false)
                  replacement = completionEval valuation replacement := by
            have hValuation : Function.update valuation other false =
                valuation := by
              funext x
              by_cases hEq : x = other
              · subst x
                simp [hSupported other hOtherActive]
              · simp [Function.update, hEq]
            rw [hValuation]
          simp only [PactType.replaceVar, if_neg hOtherName.symm,
            completionEval]
          rw [ih (sizeOf body) hBodySize active
              (Function.update valuation other false) hSupported' body rfl
                hHygienic.2,
            hReplacementEval]
          exact congrArg (fun f => completionEval f body)
            (Function.update_comm hOtherName.symm
              (completionEval valuation replacement) false valuation).symm
      | choice left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | fairChoice bid left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | seq left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | par left right interface =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | xoffer elseType branches =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf elseType) hElseSize active valuation hSupported
              elseType rfl hHygienic.1,
            hBranches branches hBranchesSize hHygienic.2]
      | offer elseType branches =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf elseType) hElseSize active valuation hSupported
              elseType rfl hHygienic.1,
            hBranches branches hBranchesSize hHygienic.2]

/-- Substituting an `active`-closed replacement for `name` closes that name in
the result. -/
theorem PactType.replaceVar_allVariablesBound
    (active : List String) (name : String) (replacement : PactType)
    (hReplacement : replacement.AllVariablesBound active) :
    ∀ processType : PactType,
      processType.AllVariablesBound (name :: active) →
        (processType.replaceVar name replacement).AllVariablesBound active := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound (name :: active) branches →
            PactType.AllBranchVariablesBound active
              (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hBound
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound,
              PactType.replaceBranches] at hBound ⊢
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
            exact ⟨ih (sizeOf branchType) hBranchSize active hReplacement
                branchType rfl hBound.1, restIH hRestSize hBound.2⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | progress pid => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | tock => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | skip => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | var other =>
          intro hBound
          by_cases hEq : name = other
          · subst other
            simpa [PactType.replaceVar] using hReplacement
          · have hMem : other ∈ active := by
              simp only [PactType.AllVariablesBound, List.mem_cons] at hBound
              exact hBound.resolve_left (Ne.symm hEq)
            simpa [PactType.replaceVar, PactType.AllVariablesBound, hEq,
              Ne.symm hEq] using hMem
      | recur other body =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound ⊢
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hEq : name = other
          · subst other
            simp [PactType.replaceVar, PactType.AllVariablesBound]
            exact PactType.allVariablesBound_mono
              (smaller := name :: name :: active)
              (larger := name :: active)
              (by
                intro x hx
                simp only [List.mem_cons] at hx ⊢
                rcases hx with rfl | rfl | hx
                · exact Or.inl rfl
                · exact Or.inl rfl
                · exact Or.inr hx)
              body hBound
          · simp only [PactType.replaceVar, if_neg hEq,
              PactType.AllVariablesBound]
            have hReordered :
                body.AllVariablesBound (name :: other :: active) := by
              exact PactType.allVariablesBound_mono
                (smaller := other :: name :: active)
                (larger := name :: other :: active)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | rfl | hx
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr hx))
                body hBound
            have hReplacement' :
                replacement.AllVariablesBound (other :: active) :=
              PactType.allVariablesBound_mono
                (by intro x hx; exact List.mem_cons_of_mem other hx)
                replacement hReplacement
            exact ih (sizeOf body) hBodySize (other :: active) hReplacement'
              body rfl hReordered
      | choice left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | fairChoice bid left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | seq left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | par left right interface =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | xoffer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar,
            PactType.replaceBranches] at hBound ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hBound.1, hBranches branches hBranchesSize hBound.2⟩
      | offer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar,
            PactType.replaceBranches] at hBound ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hBound.1, hBranches branches hBranchesSize hBound.2⟩

/-- Capture-freshness is preserved by substituting a replacement which is
fresh for the active names. -/
theorem PactType.replaceVar_binderFreshFor
    (active : List String) (name : String) (replacement : PactType)
    (hReplacement : replacement.BinderFreshFor active) :
    ∀ processType : PactType,
      processType.BinderFreshFor (name :: active) →
        (processType.replaceVar name replacement).BinderFreshFor active := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: active) branches →
            PactType.BinderFreshForBranches active
              (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hFresh
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches,
              PactType.replaceBranches] at hFresh ⊢
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
            exact ⟨ih (sizeOf branchType) hBranchSize active hReplacement
                branchType rfl hFresh.1, restIH hRestSize hFresh.2⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | progress pid => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | tock => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | skip => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | var other =>
          intro _
          by_cases hEq : name = other
          · subst other
            simpa [PactType.replaceVar] using hReplacement
          · simp [PactType.replaceVar, PactType.BinderFreshFor, hEq,
              Ne.symm hEq]
      | recur other body =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hOtherName : other ≠ name := by
            intro hEq
            subst other
            exact hFresh.1 (by simp)
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, if_neg hOtherName.symm,
            PactType.BinderFreshFor]
          exact ⟨fun hMem => hFresh.1 (by simp [hMem]),
            ih (sizeOf body) hBodySize active hReplacement body rfl hFresh.2⟩
      | choice left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | fairChoice bid left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | seq left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | par left right interface =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | xoffer elseType branches =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hFresh.1, hBranches branches hBranchesSize hFresh.2⟩
      | offer elseType branches =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar,
            PactType.replaceBranches] at hFresh ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hFresh.1, hBranches branches hBranchesSize hFresh.2⟩

mutual
  /-- `typeFutureOffers`, parameterized by the interpretation of one free
  variable. A matching `.var name` contributes `replacementFuture`, while a
  sequence consults the matching parametric completion analysis. This is the
  syntax-side invariant used after an enclosing recursion binder installs its
  backedges. -/
  def PactType.futureOffersSubst
      (name : String) (replacementCompleting : Bool)
      (replacementFuture : Finset BareMessage) : PactType →
        Finset BareMessage
    | .message msg dir => {(msg, dir)}
    | .progress _ | .tock | .skip => ∅
    | .var other => if name = other then replacementFuture else ∅
    | .recur other body =>
        if name = other then typeFutureOffers body
        else futureOffersSubst name replacementCompleting replacementFuture body
    | .choice left right | .fairChoice _ left right =>
        futureOffersSubst name replacementCompleting replacementFuture left ∪
          futureOffersSubst name replacementCompleting replacementFuture right
    | .seq left right =>
        let leftFuture :=
          futureOffersSubst name replacementCompleting replacementFuture left
        if canCompleteBeforeTockSubst name replacementCompleting left then
          leftFuture ∪
            futureOffersSubst name replacementCompleting replacementFuture right
        else leftFuture
    | .par left right interface =>
        hideTypeOffers interface
          (futureOffersSubst name replacementCompleting replacementFuture left ∪
            futureOffersSubst name replacementCompleting replacementFuture right)
    | .xoffer elseType branches | .offer elseType branches =>
        futureOffersSubst name replacementCompleting replacementFuture elseType ∪
          branchFutureOffersSubst name replacementCompleting replacementFuture
            branches
  termination_by processType => sizeOf processType

  /-- Branch-list component of `futureOffersSubst`: every branch contributes
  its head action and the parametric future of its continuation. -/
  def PactType.branchFutureOffersSubst
      (name : String) (replacementCompleting : Bool)
      (replacementFuture : Finset BareMessage) :
      List (BareMessage × PactType) → Finset BareMessage
    | [] => ∅
    | (action, processType) :: rest =>
        {action} ∪
          futureOffersSubst name replacementCompleting replacementFuture
            processType ∪
          branchFutureOffersSubst name replacementCompleting replacementFuture
            rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Unconditional substitution equation for `CanCompleteBeforeTock`: no
`GuardedOccurrences` hypothesis is needed, because `CanCompleteBeforeTock`
never unfolds a `.recur` node more than once (it reads `body`'s own
completion directly, per its `.recur _ body => CanCompleteBeforeTock body`
clause) and `replaceVar` only ever substitutes literal `.var name` leaves. -/
theorem PactType.replaceVar_canCompleteBeforeTock
    (name : String) (replacement processType : PactType) :
    (processType.replaceVar name replacement).CanCompleteBeforeTock =
      canCompleteBeforeTockSubst name replacement.CanCompleteBeforeTock
        processType := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | progress pid =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | tock =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | skip =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | var other =>
          by_cases hName : name = other
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst]
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, Ne.symm hName]
      | recur other body =>
          by_cases hName : name = other
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, ih (sizeOf body) hBodySize body rfl]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : PactType.BranchCanCompleteBeforeTock
              (PactType.replaceBranches branches name replacement) =
              branchCanCompleteBeforeTockSubst name
                replacement.CanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil => simp [PactType.replaceBranches,
                PactType.BranchCanCompleteBeforeTock,
                branchCanCompleteBeforeTockSubst]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hMem := List.sizeOf_lt_of_mem
                    (List.mem_cons_self (a := branch) (l := rest))
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.replaceBranches PactType.BranchCanCompleteBeforeTock
                  branchCanCompleteBeforeTockSubst
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf elseType) hElseSize
              elseType rfl, hBranches]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : PactType.BranchCanCompleteBeforeTock
              (PactType.replaceBranches branches name replacement) =
              branchCanCompleteBeforeTockSubst name
                replacement.CanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil => simp [PactType.replaceBranches,
                PactType.BranchCanCompleteBeforeTock,
                branchCanCompleteBeforeTockSubst]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hMem := List.sizeOf_lt_of_mem
                    (List.mem_cons_self (a := branch) (l := rest))
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.replaceBranches PactType.BranchCanCompleteBeforeTock
                  branchCanCompleteBeforeTockSubst
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf elseType) hElseSize
              elseType rfl, hBranches]

end

end Pact
