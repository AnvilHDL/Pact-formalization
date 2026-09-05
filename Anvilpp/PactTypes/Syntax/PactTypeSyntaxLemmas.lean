import Anvilpp.PactTypes.Syntax.PactTypeSyntaxDefs

namespace Pact

noncomputable section

namespace PactTypeAlphabet

  /-- Each child declares everything the parent does: away from the interface
  the two agree, and the parent declares no interface action. -/
  theorem parent_actions_subset_left
      {parent left right : PactTypeAlphabet} {interface : Interface}
      (h : ParallelCompatible parent left right interface) :
      parent.actions ⊆ left.actions := by
    intro action hAction
    have hMem : action ∈ (hideInterface left interface).actions := by
      rw [h.parent_eq_left]
      exact hAction
    simp only [hideInterface, Finset.mem_filter] at hMem
    exact hMem.1

  /-- Mirror for the right child. -/
  theorem parent_actions_subset_right
      {parent left right : PactTypeAlphabet} {interface : Interface}
      (h : ParallelCompatible parent left right interface) :
      parent.actions ⊆ right.actions := by
    intro action hAction
    have hMem : action ∈ (hideInterface right interface).actions := by
      rw [h.parent_eq_right]
      exact hAction
    simp only [hideInterface, Finset.mem_filter] at hMem
    exact hMem.1

end PactTypeAlphabet

namespace PactType

  theorem branch_alphabet_eq_of_mem
      {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType}
      (hBranches : BranchesAlphabetWellFormed alphabet branches)
      (hMem : branch ∈ branches) :
      branch.2.alphabet = alphabet := by
    induction branches with
    | nil =>
        cases hMem
    | cons head tail ih =>
        rcases head with ⟨action, processType⟩
        simp only [BranchesAlphabetWellFormed] at hBranches
        simp only [List.mem_cons] at hMem
        rcases hMem with hHead | hTail
        · cases hHead
          exact hBranches.1
        · exact ih hBranches.2.2 hTail

  theorem replaceVar_alphabet_eq_of_replacement
      (processType : PactType) (name : String) {replacement : PactType}
      (hReplacement : replacement.alphabet = processType.alphabet) :
      (processType.replaceVar name replacement).alphabet =
        processType.alphabet := by
    cases processType with
    | var alphabet other =>
        by_cases hName : name = other
        · subst other
          simpa [replaceVar, PactType.alphabet] using hReplacement
        · simp [replaceVar, PactType.alphabet, hName]
    | recur alphabet other body =>
        by_cases hName : name = other <;>
          simp [replaceVar, PactType.alphabet, hName]
    | message alphabet msg dir => simp [replaceVar, PactType.alphabet]
    | progress alphabet pid => simp [replaceVar, PactType.alphabet]
    | tock alphabet => simp [replaceVar, PactType.alphabet]
    | skip alphabet => simp [replaceVar, PactType.alphabet]
    | choice alphabet left right => simp [replaceVar, PactType.alphabet]
    | seq alphabet left right => simp [replaceVar, PactType.alphabet]
    | par alphabet left right interface =>
        simp [replaceVar, PactType.alphabet]
    | fairChoice alphabet bid left right =>
        simp [replaceVar, PactType.alphabet]
    | xoffer alphabet elseType branches =>
        simp [replaceVar, PactType.alphabet]
    | offer alphabet elseType branches =>
        simp [replaceVar, PactType.alphabet]


  /-- Enlarging the set of names regarded as bound preserves closedness. -/
  theorem allVariablesBound_mono
      {smaller larger : List String}
      (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
      ∀ processType,
        AllVariablesBound smaller processType →
          AllVariablesBound larger processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType smaller larger with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            AllBranchVariablesBound smaller branches →
              AllBranchVariablesBound larger branches := by
          intro branches hBranchesSize h
          induction branches with
          | nil => simp [AllBranchVariablesBound]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
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
                have hRest : sizeOf rest <
                    sizeOf ((action, branchType) :: rest) := by
                  simp_wf
                  omega
                omega
              exact ⟨ih (sizeOf branchType) hBranchSize hSubset branchType
                  rfl h.1, restIH hRestSize h.2⟩
        cases processType with
        | message alphabet msg dir => simp [AllVariablesBound]
        | progress alphabet pid => simp [AllVariablesBound]
        | tock alphabet => simp [AllVariablesBound]
        | skip alphabet => simp [AllVariablesBound]
        | var alphabet name => simpa [AllVariablesBound] using hSubset name
        | recur alphabet name body =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize
              (by
                intro other hMem
                simp only [List.mem_cons] at hMem ⊢
                exact hMem.elim Or.inl (fun h => Or.inr (hSubset other h)))
              body rfl h
        | choice alphabet left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | fairChoice alphabet bid left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | seq alphabet left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | par alphabet left right interface =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | xoffer alphabet elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer alphabet elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩

end PactType

/-- Freshness weakens along a smaller forbidden set. -/
theorem PactType.binderFreshFor_of_cons {name : String} :
    ∀ (processType : PactType) (bound : List String),
      PactType.BinderFreshFor (name :: bound) processType →
      PactType.BinderFreshFor bound processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (bound : List String), sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: bound) branches →
          PactType.BinderFreshForBranches bound branches := by
        intro branches bound hSizeBranches hFresh
        induction branches with
        | nil => simp [PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hFresh ⊢
            refine ⟨ih (sizeOf branchType) (by simp at hSizeBranches ⊢; omega)
              branchType rfl bound hFresh.1, ?_⟩
            exact restIH (by simp at hSizeBranches ⊢; omega) hFresh.2
      intro bound hFresh
      cases processType with
      | message _ _ _ => simp [PactType.BinderFreshFor]
      | progress _ _ => simp [PactType.BinderFreshFor]
      | tock _ => simp [PactType.BinderFreshFor]
      | skip _ => simp [PactType.BinderFreshFor]
      | var _ _ => simp [PactType.BinderFreshFor]
      | recur alphabet other body =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨fun hMem => hFresh.1 (List.mem_cons_of_mem _ hMem),
            ih (sizeOf body) (by subst hSize; simp; omega) body rfl bound
              hFresh.2⟩
      | choice alphabet left right =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2⟩
      | seq alphabet left right =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2⟩
      | fairChoice alphabet bid left right =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2⟩
      | par alphabet left right interface =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2⟩
      | xoffer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hFresh.1,
            hBranches branches bound (by subst hSize; simp; omega) hFresh.2⟩
      | offer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hFresh ⊢
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hFresh.1,
            hBranches branches bound (by subst hSize; simp; omega) hFresh.2⟩

/-- Substitution introduces no new binder: every binder of the result is one of
the target's or one of the replacement's. -/
theorem PactType.binderFreshFor_replaceVar (var : String)
    (replacement : PactType) :
    ∀ (processType : PactType) (bound : List String),
      PactType.BinderFreshFor bound processType →
      PactType.BinderFreshFor bound replacement →
      PactType.BinderFreshFor bound (processType.replaceVar var replacement) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (bound : List String), sizeOf branches < n →
          PactType.BinderFreshForBranches bound branches →
          PactType.BinderFreshFor bound replacement →
          PactType.BinderFreshForBranches bound
            (PactType.replaceBranches branches var replacement) := by
        intro branches bound hSizeBranches hFresh hReplacement
        induction branches with
        | nil => simp [PactType.replaceBranches, PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hFresh
            simp only [PactType.replaceBranches,
              PactType.BinderFreshForBranches]
            refine ⟨ih (sizeOf branchType) (by simp at hSizeBranches ⊢; omega)
              branchType rfl bound hFresh.1 hReplacement, ?_⟩
            exact restIH (by simp at hSizeBranches ⊢; omega) hFresh.2
      intro bound hFresh hReplacement
      cases processType with
      | message _ _ _ => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | progress _ _ => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | tock _ => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | skip _ => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | var alphabet other =>
          simp only [PactType.replaceVar]
          by_cases hEq : var = other
          · rw [if_pos hEq]; exact hReplacement
          · rw [if_neg hEq]; simp [PactType.BinderFreshFor]
      | recur alphabet other body =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar]
          by_cases hEq : var = other
          · rw [if_pos hEq]
            simp only [PactType.BinderFreshFor]
            exact hFresh
          · rw [if_neg hEq]
            simp only [PactType.BinderFreshFor]
            exact ⟨hFresh.1, ih (sizeOf body) (by subst hSize; simp; omega) body
              rfl bound hFresh.2 hReplacement⟩
      | choice alphabet left right =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1
              hReplacement,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2
              hReplacement⟩
      | seq alphabet left right =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1
              hReplacement,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2
              hReplacement⟩
      | fairChoice alphabet bid left right =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1
              hReplacement,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2
              hReplacement⟩
      | par alphabet left right interface =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hFresh.1
              hReplacement,
            ih _ (by subst hSize; simp; omega) right rfl bound hFresh.2
              hReplacement⟩
      | xoffer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hFresh.1
              hReplacement,
            hBranches branches bound (by subst hSize; simp; omega) hFresh.2
              hReplacement⟩
      | offer alphabet elseType branches =>
          simp only [PactType.BinderFreshFor] at hFresh
          simp only [PactType.replaceVar, PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hFresh.1
              hReplacement,
            hBranches branches bound (by subst hSize; simp; omega) hFresh.2
              hReplacement⟩

/-- Hygiene gives freshness.  `BinderHygienic` grows the context at every
binder, so each binder it meets is outside the context it inherited; that head
conjunct is what `BinderFreshFor` asks of the original context. -/
theorem PactType.binderHygienic_binderFreshFor :
    ∀ (processType : PactType) (bound : List String),
      PactType.BinderHygienic bound processType →
      PactType.BinderFreshFor bound processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (bound : List String), sizeOf branches < n →
          PactType.BinderHygienicBranches bound branches →
          PactType.BinderFreshForBranches bound branches := by
        intro branches bound hSizeBranches hHyg
        induction branches with
        | nil => simp [PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderHygienicBranches] at hHyg
            simp only [PactType.BinderFreshForBranches]
            refine ⟨ih (sizeOf branchType) (by simp at hSizeBranches ⊢; omega)
              branchType rfl bound hHyg.1, ?_⟩
            exact restIH (by simp at hSizeBranches ⊢; omega) hHyg.2
      intro bound hHyg
      cases processType with
      | message _ _ _ => simp [PactType.BinderFreshFor]
      | progress _ _ => simp [PactType.BinderFreshFor]
      | tock _ => simp [PactType.BinderFreshFor]
      | skip _ => simp [PactType.BinderFreshFor]
      | var _ _ => simp [PactType.BinderFreshFor]
      | recur alphabet other body =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          refine ⟨hHyg.1, ?_⟩
          exact PactType.binderFreshFor_of_cons body bound
            (ih _ (by subst hSize; simp; omega) body rfl (other :: bound)
              hHyg.2)
      | choice alphabet left right =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hHyg.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hHyg.2⟩
      | seq alphabet left right =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hHyg.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hHyg.2⟩
      | fairChoice alphabet bid left right =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hHyg.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hHyg.2⟩
      | par alphabet left right interface =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) left rfl bound hHyg.1,
            ih _ (by subst hSize; simp; omega) right rfl bound hHyg.2⟩
      | xoffer alphabet elseType branches =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hHyg.1,
            hBranches branches bound (by subst hSize; simp; omega) hHyg.2⟩
      | offer alphabet elseType branches =>
          simp only [PactType.BinderHygienic] at hHyg
          simp only [PactType.BinderFreshFor]
          exact ⟨ih _ (by subst hSize; simp; omega) elseType rfl bound hHyg.1,
            hBranches branches bound (by subst hSize; simp; omega) hHyg.2⟩

end

end Pact
