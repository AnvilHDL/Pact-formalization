import Anvilpp.PactTypes.Syntax.PactTypeSyntaxDefs

namespace Pact

noncomputable section

namespace PactTypeAlphabet

  @[simp] theorem mergeHidden_self_empty (alphabet : PactTypeAlphabet) :
      mergeHidden alphabet alphabet ∅ = alphabet := by
    cases alphabet
    simp [mergeHidden]

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

  mutual
    /-- Replacing a variable by its recursion binder never shrinks the type. -/
    theorem sizeOf_le_replaceVar_recur (processType : PactType)
        (name : String) (body : PactType) :
        sizeOf processType ≤
          sizeOf (processType.replaceVar name (recurSelf name body)) := by
      cases processType with
      | message alphabet msg dir => simp [replaceVar]
      | progress alphabet pid => simp [replaceVar]
      | tock alphabet => simp [replaceVar]
      | skip alphabet => simp [replaceVar]
      | var alphabet other =>
          by_cases hName : name = other
          · subst other
            simp [replaceVar, recurSelf]
          · simp [replaceVar, recurSelf, hName]
      | recur alphabet other nestedBody =>
          by_cases hName : name = other
          · simp [replaceVar, recurSelf, hName]
          · simp [replaceVar, hName]
            have hBody := sizeOf_le_replaceVar_recur nestedBody name body
            omega
      | choice alphabet left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | fairChoice alphabet bid left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | seq alphabet left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | par alphabet left right interface =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | xoffer alphabet elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          omega
      | offer alphabet elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          omega
    termination_by sizeOf processType

    theorem sizeOf_le_replaceBranches_recur
        (branches : List (BareMessage × PactType))
        (name : String) (body : PactType) :
        sizeOf branches ≤
          sizeOf (replaceBranches branches name (recurSelf name body)) := by
      cases branches with
      | nil => simp [replaceBranches]
      | cons branch rest =>
          rcases branch with ⟨action, branchType⟩
          have hBranch := sizeOf_le_replaceVar_recur branchType name body
          have hRest := sizeOf_le_replaceBranches_recur rest name body
          simp [replaceBranches]
          omega
    termination_by sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

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

end

end Pact
