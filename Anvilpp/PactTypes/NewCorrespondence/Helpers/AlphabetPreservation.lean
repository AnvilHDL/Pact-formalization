import Anvilpp.PactTypes.NewCorrespondence.Helpers.ChoiceRelations
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Sequence
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Parallel
import Anvilpp.PactTypes.NewCorrespondence.Helpers.RecursionFoundations
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Offers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Variables

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

mutual
  /-- The alphabet-propagation part of syntactic well-formedness.  Generated
  conjunctive-offer residuals satisfy this invariant even though they are not
  user-written admissible types. -/
  def PactType.AlphabetCoherent : PactType → Prop
    | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .choice alphabet left right | .seq alphabet left right =>
        left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
          left.AlphabetCoherent ∧ right.AlphabetCoherent
    | .fairChoice alphabet _ left right =>
        left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
          left.AlphabetCoherent ∧ right.AlphabetCoherent
    | .par alphabet left right interface =>
        alphabet = PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
          interface ∧
          left.AlphabetCoherent ∧ right.AlphabetCoherent
    | .recur alphabet _ body =>
        body.alphabet = alphabet ∧ body.AlphabetCoherent
    | .xoffer alphabet elseType branches
    | .offer alphabet elseType branches =>
        elseType.alphabet = alphabet ∧ elseType.AlphabetCoherent ∧
          PactType.BranchesAlphabetCoherent alphabet branches
  termination_by processType => sizeOf processType

  def PactType.BranchesAlphabetCoherent
      (alphabet : PactTypeAlphabet) :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        processType.alphabet = alphabet ∧ processType.AlphabetCoherent ∧
          PactType.BranchesAlphabetCoherent alphabet rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Full alphabet well-formedness implies alphabet coherence. -/
theorem PactType.alphabetCoherent_of_wellFormed :
    ∀ processType : PactType, processType.AlphabetWellFormed →
      processType.AlphabetCoherent := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ alphabet branches,
          sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.BranchesAlphabetCoherent alphabet branches := by
        intro alphabet branches hBranchesSize hWellFormed
        induction branches with
        | nil => simp [PactType.BranchesAlphabetCoherent]
        | cons entry rest restIH =>
            obtain ⟨action, branchType⟩ := entry
            simp only [PactType.BranchesAlphabetWellFormed] at hWellFormed
            simp only [PactType.BranchesAlphabetCoherent]
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
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf
                omega
              omega
            exact ⟨hWellFormed.2.1,
              ih (sizeOf branchType) hBranchSize branchType rfl
                hWellFormed.2.2.1,
              restIH hRestSize hWellFormed.2.2.2⟩
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          intro _
          simp [PactType.AlphabetCoherent]
      | choice alphabet left right | seq alphabet left right =>
          intro hWellFormed
          simp only [PactType.AlphabetWellFormed] at hWellFormed
          simp only [PactType.AlphabetCoherent]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hWellFormed.2.1, hWellFormed.2.2.1,
            ih (sizeOf left) hLeftSize left rfl hWellFormed.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl hWellFormed.2.2.2.2⟩
      | fairChoice alphabet bid left right =>
          intro hWellFormed
          simp only [PactType.AlphabetWellFormed] at hWellFormed
          simp only [PactType.AlphabetCoherent]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hWellFormed.2.2.1, hWellFormed.2.2.2.1,
            ih (sizeOf left) hLeftSize left rfl hWellFormed.2.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl hWellFormed.2.2.2.2.2⟩
      | par alphabet left right interface =>
          intro hWellFormed
          simp only [PactType.AlphabetWellFormed] at hWellFormed
          simp only [PactType.AlphabetCoherent]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hWellFormed.2.1.1,
            ih (sizeOf left) hLeftSize left rfl hWellFormed.2.2.1,
            ih (sizeOf right) hRightSize right rfl hWellFormed.2.2.2⟩
      | recur alphabet name body =>
          intro hWellFormed
          simp only [PactType.AlphabetWellFormed] at hWellFormed
          simp only [PactType.AlphabetCoherent]
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hWellFormed.2.1,
            ih (sizeOf body) hBodySize body rfl hWellFormed.2.2⟩
      | xoffer alphabet elseType branches
      | offer alphabet elseType branches =>
          intro hWellFormed
          simp only [PactType.AlphabetWellFormed] at hWellFormed
          simp only [PactType.AlphabetCoherent]
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          exact ⟨hWellFormed.2.1,
            ih (sizeOf elseType) hElseSize elseType rfl hWellFormed.2.2.1,
            hBranches alphabet branches hBranchesSize hWellFormed.2.2.2⟩

private theorem singletonTypeXOffer_alphabetCoherent
    {alphabet : PactTypeAlphabet} {branch : BareMessage × PactType}
    (hBranch : branch.2.alphabet = alphabet ∧
      branch.2.AlphabetCoherent) :
    (singletonTypeXOffer branch).AlphabetCoherent := by
  rcases branch with ⟨action, branchType⟩
  simp only [singletonTypeXOffer, PactType.AlphabetCoherent,
    PactType.BranchesAlphabetCoherent]
  exact ⟨rfl, trivial, trivial, hBranch.2, trivial⟩

private theorem selectedTypeBranch_alphabetCoherent
    {branch : BareMessage × PactType}
    (hBranch : branch.2.AlphabetCoherent) :
    (selectedTypeBranch branch).AlphabetCoherent := by
  rcases branch with ⟨action, branchType⟩
  simpa [selectedTypeBranch, PactType.AlphabetCoherent, PactType.alphabet]
    using hBranch

theorem parallelTypeBranches_alphabet_coherent
    {alphabet : PactTypeAlphabet} :
    ∀ {branches : List (BareMessage × PactType)},
      branches ≠ [] →
      PactType.BranchesAlphabetCoherent alphabet branches →
      (parallelTypeBranches branches).alphabet = alphabet ∧
        (parallelTypeBranches branches).AlphabetCoherent := by
  intro branches hNonempty hBranches
  induction branches with
  | nil => exact False.elim (hNonempty rfl)
  | cons branch rest ih =>
      cases rest with
      | nil =>
          rcases branch with ⟨action, branchType⟩
          simp only [PactType.BranchesAlphabetCoherent] at hBranches
          exact ⟨by simpa using hBranches.1,
            singletonTypeXOffer_alphabetCoherent ⟨hBranches.1,
              hBranches.2.1⟩⟩
      | cons next tail =>
          rcases branch with ⟨action, branchType⟩
          simp only [PactType.BranchesAlphabetCoherent] at hBranches
          obtain ⟨hTailAlphabet, hTailCoherent⟩ :=
            ih (by simp) hBranches.2.2
          have hHeadCoherent :=
            singletonTypeXOffer_alphabetCoherent
              (branch := (action, branchType)) ⟨hBranches.1,
              hBranches.2.1⟩
          constructor
          · change PactTypeAlphabet.mergeHidden branchType.alphabet
                (parallelTypeBranches (next :: tail)).alphabet ∅ = alphabet
            rw [hBranches.1, hTailAlphabet]
            simp
          · simp [parallelTypeBranches, parallelType,
              PactType.AlphabetCoherent, hHeadCoherent, hTailCoherent]

theorem parallelTypeBranchesSelecting_alphabet_coherent
    {alphabet : PactTypeAlphabet} {selected : BareMessage × PactType} :
    ∀ {branches : List (BareMessage × PactType)},
      selected ∈ branches →
      PactType.BranchesAlphabetCoherent alphabet branches →
      (parallelTypeBranchesSelecting selected branches).alphabet = alphabet ∧
        (parallelTypeBranchesSelecting selected branches).AlphabetCoherent := by
  intro branches hSelected hBranches
  induction branches with
  | nil => cases hSelected
  | cons branch rest ih =>
      cases rest with
      | nil =>
          have hEq : selected = branch := by simpa using hSelected
          subst selected
          rcases branch with ⟨action, branchType⟩
          simp only [PactType.BranchesAlphabetCoherent] at hBranches
          rw [parallelTypeBranchesSelecting_singleton_self]
          exact ⟨by simpa using hBranches.1,
            selectedTypeBranch_alphabetCoherent hBranches.2.1⟩
      | cons next tail =>
          rcases branch with ⟨action, branchType⟩
          simp only [PactType.BranchesAlphabetCoherent] at hBranches
          by_cases hHead : (action, branchType) = selected
          · subst selected
            obtain ⟨hTailAlphabet, hTailCoherent⟩ :=
              parallelTypeBranches_alphabet_coherent (by simp) hBranches.2.2
            have hHeadCoherent :=
              selectedTypeBranch_alphabetCoherent
                (branch := (action, branchType)) hBranches.2.1
            constructor
            · simp only [parallelTypeBranchesSelecting, if_true, parallelType,
                  PactType.alphabet]
              change PactTypeAlphabet.mergeHidden branchType.alphabet
                  (parallelTypeBranches (next :: tail)).alphabet ∅ = alphabet
              rw [hBranches.1, hTailAlphabet]
              simp
            · simp [parallelTypeBranchesSelecting, parallelType,
                PactType.AlphabetCoherent, hHeadCoherent, hTailCoherent]
          · have hSelectedTail : selected ∈ next :: tail := by
              simp only [List.mem_cons] at hSelected
              rcases hSelected with hSelectedHead | hSelectedTail
              · exact False.elim (hHead hSelectedHead.symm)
              · simpa [List.mem_cons] using hSelectedTail
            obtain ⟨hTailAlphabet, hTailCoherent⟩ :=
              ih hSelectedTail hBranches.2.2
            have hHeadCoherent :=
              singletonTypeXOffer_alphabetCoherent
                (branch := (action, branchType)) ⟨hBranches.1,
                hBranches.2.1⟩
            constructor
            · simp only [parallelTypeBranchesSelecting, if_neg hHead,
                  parallelType, PactType.alphabet]
              change PactTypeAlphabet.mergeHidden branchType.alphabet
                  (parallelTypeBranchesSelecting selected
                    (next :: tail)).alphabet ∅ = alphabet
              rw [hBranches.1, hTailAlphabet]
              simp
            · simp [parallelTypeBranchesSelecting, hHead, parallelType,
                PactType.AlphabetCoherent, hHeadCoherent, hTailCoherent]

private theorem branchesAlphabetCoherent_of_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    {branch : BareMessage × PactType}
    (hBranches : PactType.BranchesAlphabetCoherent alphabet branches)
    (hMember : branch ∈ branches) :
    branch.2.alphabet = alphabet ∧ branch.2.AlphabetCoherent := by
  induction branches with
  | nil => cases hMember
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchesAlphabetCoherent] at hBranches
      simp only [List.mem_cons] at hMember
      rcases hMember with hHead | hTail
      · cases hHead
        exact ⟨hBranches.1, hBranches.2.1⟩
      · exact ih hBranches.2.2 hTail

/-- Every residual represented by a compiled state retains the fixed alphabet
of the source type.  The proof follows the structural relation clauses; the
fuel measure is needed for generated conjunctive-offer children. -/
theorem relationMembership_alphabet_eq
    (signature : TypeAlphabet) :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.AlphabetCoherent →
      relationMembership (buildRelationSet source (compileType signature source))
        residual state →
      residual.alphabet = source.alphabet := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hCoherent hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases signature alphabet hRelated).1]
      | message alphabet msg dir =>
          rcases relationMembership_message_cases signature alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | tock alphabet =>
          rcases relationMembership_tock_cases signature alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases signature alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | var alphabet name =>
          rw [(relationMembership_var_cases signature alphabet name hRelated).1]
      | choice alphabet left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_choice_cases signature alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hCoherent.2.2.1 hLeftRelated).trans hCoherent.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_fairChoice_cases signature alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hCoherent.2.2.1 hLeftRelated).trans hCoherent.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | seq alphabet left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_seq_cases signature alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, _, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            simp [PactType.alphabet]
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | par alphabet left right interface =>
          rcases relationMembership_par_cases signature alphabet left right
              interface hRelated with hPair | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, _, _, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            simp [PactType.alphabet]
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.alphabet]
      | recur alphabet name body =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_recur_cases signature alphabet name body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            have hBodyAlphabet := ih (typeCompilationFuel body) hBodyFuel body
              rfl bodyResidual q hCoherent.2 hBodyRelated
            have hReplacement :
                (PactType.recur alphabet name body).alphabet =
                  bodyResidual.alphabet := by
              simpa [PactType.alphabet] using
                (hBodyAlphabet.trans hCoherent.1).symm
            exact (PactType.replaceVar_alphabet_eq_of_replacement bodyResidual
              name hReplacement).trans (hBodyAlphabet.trans hCoherent.1)
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_xoffer_cases signature alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hCoherent.2.1 hElseRelated).trans hCoherent.1
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchCoherent := branchesAlphabetCoherent_of_mem
              hCoherent.2.2 hMember
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel branchType) hBranchFuel branchType
              rfl residual q hBranchCoherent.2 hBranchRelated).trans
                hBranchCoherent.1
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_offer_cases signature alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hCoherent.2.1 hElseRelated).trans hCoherent.1
          · rcases hSelected with ⟨i, selected, q, hGet, _,
              hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            obtain ⟨hSelectedAlphabet, hSelectedCoherent⟩ :=
              parallelTypeBranchesSelecting_alphabet_coherent hMember
                hCoherent.2.2
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]
              omega
            exact (ih (typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting selected branches)
              rfl residual q hSelectedCoherent hSelectedRelated).trans
                hSelectedAlphabet

end

end Pact
