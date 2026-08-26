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
    | .par _ left right _ =>
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
          exact ⟨ih (sizeOf left) hLeftSize left rfl hWellFormed.2.2.1,
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

theorem PactType.reannotate_alphabetCoherent
    (alphabet : PactTypeAlphabet) :
    ∀ processType : PactType, processType.AlphabetCoherent →
      (processType.reannotate alphabet).AlphabetCoherent := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType alphabet with
  | _ n ih =>
      have hBranches : ∀ sourceAlphabet
          (branches : List (BareMessage × PactType)),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.BranchesAlphabetCoherent sourceAlphabet branches →
          PactType.BranchesAlphabetCoherent branchAlphabet
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro sourceAlphabet branches hBranchesSize branchAlphabet hCoherent
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.BranchesAlphabetCoherent]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.BranchesAlphabetCoherent] at hCoherent ⊢
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            exact ⟨PactType.reannotate_alphabet branchAlphabet branchType,
              ih (sizeOf branchType) hBranchSize branchAlphabet branchType rfl
                hCoherent.2.1,
              restIH hRestSize hCoherent.2.2⟩
      intro hCoherent
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.AlphabetCoherent]
      | choice _ left right | seq _ left right | fairChoice _ _ left right =>
          simp only [PactType.reannotate, PactType.AlphabetCoherent]
          simp only [PactType.AlphabetCoherent] at hCoherent
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨PactType.reannotate_alphabet alphabet left,
            PactType.reannotate_alphabet alphabet right,
            ih (sizeOf left) hLeftSize alphabet left rfl hCoherent.2.2.1,
            ih (sizeOf right) hRightSize alphabet right rfl hCoherent.2.2.2⟩
      | par _ left right interface =>
          simp only [PactType.reannotate, PactType.AlphabetCoherent]
          simp only [PactType.AlphabetCoherent] at hCoherent
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨
            ih (sizeOf left) hLeftSize
              (PactTypeAlphabet.projectParallelLeft alphabet left.alphabet
                right.alphabet interface) left rfl hCoherent.1,
            ih (sizeOf right) hRightSize
              (PactTypeAlphabet.projectParallelChild alphabet right.alphabet
                interface) right rfl hCoherent.2⟩
      | recur _ _ body =>
          simp only [PactType.reannotate, PactType.AlphabetCoherent]
          simp only [PactType.AlphabetCoherent] at hCoherent
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ⟨PactType.reannotate_alphabet alphabet body,
            ih (sizeOf body) hBodySize alphabet body rfl hCoherent.2⟩
      | xoffer _ elseType branches | offer _ elseType branches =>
          simp only [PactType.reannotate, PactType.AlphabetCoherent]
          simp only [PactType.AlphabetCoherent] at hCoherent
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨PactType.reannotate_alphabet alphabet elseType,
            ih (sizeOf elseType) hElseSize alphabet elseType rfl hCoherent.2.1,
            hBranches _ branches hBranchesSize alphabet hCoherent.2.2⟩

theorem singletonTypeXOfferAt_alphabetCoherent
    (alphabet : PactTypeAlphabet) {branch : BareMessage × PactType}
    (hBranch : branch.2.AlphabetCoherent) :
    (singletonTypeXOfferAt alphabet branch).AlphabetCoherent := by
  rcases branch with ⟨action, branchType⟩
  simp only [singletonTypeXOfferAt, PactType.AlphabetCoherent,
    PactType.BranchesAlphabetCoherent, PactType.alphabet]
  exact ⟨trivial, trivial, PactType.reannotate_alphabet alphabet branchType,
    PactType.reannotate_alphabetCoherent alphabet branchType hBranch, trivial⟩

theorem selectedTypeBranchAt_alphabetCoherent
    (alphabet : PactTypeAlphabet) {branch : BareMessage × PactType}
    (hBranch : branch.2.AlphabetCoherent) :
    (selectedTypeBranchAt alphabet branch).AlphabetCoherent := by
  rcases branch with ⟨action, branchType⟩
  simp only [selectedTypeBranchAt, PactType.AlphabetCoherent,
    PactType.alphabet]
  exact ⟨trivial, PactType.reannotate_alphabet alphabet branchType, trivial,
    PactType.reannotate_alphabetCoherent alphabet branchType hBranch⟩

theorem parallelTypeBranchesWithin_alphabet_coherent
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.AlphabetCoherent) →
      (parallelTypeBranchesWithin alphabet branches).AlphabetCoherent
  | [], _ => by simp [parallelTypeBranchesWithin, PactType.AlphabetCoherent]
  | [branch], hBranches => by
      exact singletonTypeXOfferAt_alphabetCoherent alphabet
        (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      simp only [parallelTypeBranchesWithin, PactType.AlphabetCoherent]
      exact ⟨
        singletonTypeXOfferAt_alphabetCoherent
          (PactTypeAlphabet.branchPart alphabet branch)
          (hBranches branch (by simp)),
        parallelTypeBranchesWithin_alphabet_coherent
          (PactTypeAlphabet.remove alphabet
            (PactTypeAlphabet.branchPart alphabet branch)) (next :: rest)
          (fun item hItem => hBranches item (by simp [hItem]))⟩

theorem parallelTypeBranchesSelectingWithin_alphabet_coherent
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.AlphabetCoherent) →
      PactType.AlphabetCoherent
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [], _ => by simp [parallelTypeBranchesSelectingWithin,
      PactType.AlphabetCoherent]
  | [branch], hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
        exact selectedTypeBranchAt_alphabetCoherent alphabet
          (hBranches branch (by simp))
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
        exact singletonTypeXOfferAt_alphabetCoherent alphabet
          (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected,
          PactType.AlphabetCoherent]
        exact ⟨
          selectedTypeBranchAt_alphabetCoherent
            (PactTypeAlphabet.branchPart alphabet branch)
            (hBranches branch (by simp)),
          parallelTypeBranchesWithin_alphabet_coherent
            (PactTypeAlphabet.remove alphabet
              (PactTypeAlphabet.branchPart alphabet branch)) (next :: rest)
            (fun item hItem => hBranches item (by simp [hItem]))⟩
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected,
          PactType.AlphabetCoherent]
        exact ⟨
          singletonTypeXOfferAt_alphabetCoherent
            (PactTypeAlphabet.branchPart alphabet branch)
            (hBranches branch (by simp)),
          parallelTypeBranchesSelectingWithin_alphabet_coherent
            (PactTypeAlphabet.remove alphabet
              (PactTypeAlphabet.branchPart alphabet branch)) selected
            (next :: rest)
            (fun item hItem => hBranches item (by simp [hItem]))⟩

theorem branchesAlphabetCoherent_of_mem
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

@[simp] theorem parallelTypeBranchesWithin_alphabet
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (parallelTypeBranchesWithin alphabet branches).alphabet = alphabet
  | [] => by simp [parallelTypeBranchesWithin, PactType.alphabet]
  | [branch] => by
      simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
        PactType.alphabet]
  | branch :: next :: rest => by
      simp [parallelTypeBranchesWithin, PactType.alphabet]

@[simp] theorem parallelTypeBranchesSelectingWithin_alphabet
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (parallelTypeBranchesSelectingWithin alphabet selected branches).alphabet =
        alphabet
  | [] => by simp [parallelTypeBranchesSelectingWithin, PactType.alphabet]
  | [branch] => by
      by_cases hSelected : branch = selected <;>
        simp [parallelTypeBranchesSelectingWithin, hSelected,
          selectedTypeBranchAt, singletonTypeXOfferAt, PactType.alphabet]
  | branch :: next :: rest => by
      by_cases hSelected : branch = selected <;>
        simp [parallelTypeBranchesSelectingWithin, hSelected,
          PactType.alphabet]

theorem parallelTypeBranches_alphabet_coherent
    {alphabet : PactTypeAlphabet} :
    ∀ {branches : List (BareMessage × PactType)},
      branches ≠ [] →
      PactType.BranchesAlphabetCoherent alphabet branches →
      (parallelTypeBranches branches).alphabet = alphabet ∧
        (parallelTypeBranches branches).AlphabetCoherent := by
  intro branches hNonempty hBranches
  cases branches with
  | nil => exact False.elim (hNonempty rfl)
  | cons branch rest =>
      have hFirstAlphabet : branch.2.alphabet = alphabet :=
        (branchesAlphabetCoherent_of_mem hBranches (by simp)).1
      constructor
      · simpa [parallelTypeBranches] using hFirstAlphabet
      · apply parallelTypeBranchesWithin_alphabet_coherent
        intro item hItem
        exact (branchesAlphabetCoherent_of_mem hBranches hItem).2

theorem parallelTypeBranchesSelecting_alphabet_coherent
    {alphabet : PactTypeAlphabet} {selected : BareMessage × PactType} :
    ∀ {branches : List (BareMessage × PactType)},
      selected ∈ branches →
      PactType.BranchesAlphabetCoherent alphabet branches →
      (parallelTypeBranchesSelecting selected branches).alphabet = alphabet ∧
        (parallelTypeBranchesSelecting selected branches).AlphabetCoherent := by
  intro branches hSelected hBranches
  cases branches with
  | nil => cases hSelected
  | cons branch rest =>
      have hFirstAlphabet : branch.2.alphabet = alphabet :=
        (branchesAlphabetCoherent_of_mem hBranches (by simp)).1
      constructor
      · simpa [parallelTypeBranchesSelecting] using
          hFirstAlphabet
      · apply parallelTypeBranchesSelectingWithin_alphabet_coherent
        intro item hItem
        exact (branchesAlphabetCoherent_of_mem hBranches hItem).2

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
