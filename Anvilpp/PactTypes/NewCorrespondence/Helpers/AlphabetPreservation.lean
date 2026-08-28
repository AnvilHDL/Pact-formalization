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

mutual
  /-- Whether reannotating `processType` to `alphabet` keeps enough information
  at every `.par` node to remain alphabet-well-formed: the target must stay
  `ParallelCompatible` with its own projections onto the two children. -/
  def PactType.ReannotationSafe (alphabet : PactTypeAlphabet) :
      PactType → Prop
    | .message _ msg dir => (msg, dir) ∈ alphabet.actions
    | .progress _ pid => pid ∈ alphabet.progress
    | .tock _ | .skip _ | .var _ _ => True
    | .choice _ left right | .seq _ left right =>
        ReannotationSafe alphabet left ∧ ReannotationSafe alphabet right
    | .fairChoice _ bid left right =>
        bid ∈ alphabet.fair ∧
          ReannotationSafe alphabet left ∧ ReannotationSafe alphabet right
    | .par _ left right interface =>
        PactTypeAlphabet.ParallelCompatible alphabet
          (PactTypeAlphabet.projectParallelLeft alphabet left.alphabet
            right.alphabet interface)
          (PactTypeAlphabet.projectParallelChild alphabet right.alphabet
            interface) interface ∧
        ReannotationSafe (PactTypeAlphabet.projectParallelLeft alphabet
          left.alphabet right.alphabet interface) left ∧
        ReannotationSafe (PactTypeAlphabet.projectParallelChild alphabet
          right.alphabet interface) right
    | .recur _ _ body => ReannotationSafe alphabet body
    | .xoffer _ elseType branches | .offer _ elseType branches =>
        ReannotationSafe alphabet elseType ∧
          ReannotationSafeBranches alphabet branches
  termination_by processType => sizeOf processType

  def PactType.ReannotationSafeBranches (alphabet : PactTypeAlphabet) :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (action, processType) :: rest =>
        action ∈ alphabet.actions ∧ ReannotationSafe alphabet processType ∧
          ReannotationSafeBranches alphabet rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- A `ParallelCompatible` left child inherits well-formedness from the
parent: interface actions are complementary, and non-interface actions of
`left` survive unhidden into the parent. -/
theorem PactTypeAlphabet.ParallelCompatible.wellFormed_left
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface)
    (hParentWF : parent.WellFormed) : left.WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  by_cases hI : msg ∈ interface
  · rcases hCompatible.complementary msg hI with ⟨_, hRecvR⟩ | ⟨_, hSendR⟩
    · exact hCompatible.actions_disjoint.forall_ne_finset hRecv hRecvR rfl
    · exact hCompatible.actions_disjoint.forall_ne_finset hSend hSendR rfl
  · have hSendP : (msg, MessageDir.send) ∈ parent.actions := by
      rw [hCompatible.parent_eq]
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inl hSend, hI⟩
    have hRecvP : (msg, MessageDir.recv) ∈ parent.actions := by
      rw [hCompatible.parent_eq]
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inl hRecv, hI⟩
    exact hParentWF msg ⟨hSendP, hRecvP⟩

/-- Right-child counterpart of `wellFormed_left`. -/
theorem PactTypeAlphabet.ParallelCompatible.wellFormed_right
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface)
    (hParentWF : parent.WellFormed) : right.WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  by_cases hI : msg ∈ interface
  · rcases hCompatible.complementary msg hI with ⟨hSendL, _⟩ | ⟨hRecvL, _⟩
    · exact hCompatible.actions_disjoint.forall_ne_finset hSendL hSend rfl
    · exact hCompatible.actions_disjoint.forall_ne_finset hRecvL hRecv rfl
  · have hSendP : (msg, MessageDir.send) ∈ parent.actions := by
      rw [hCompatible.parent_eq]
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inr hSend, hI⟩
    have hRecvP : (msg, MessageDir.recv) ∈ parent.actions := by
      rw [hCompatible.parent_eq]
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inr hRecv, hI⟩
    exact hParentWF msg ⟨hSendP, hRecvP⟩

/-- `AlphabetWellFormed` analog of `reannotate_alphabetCoherent`.  Unlike the
`Coherent` version this is NOT unconditional: the target `alphabet` must be
well-formed and `ReannotationSafe` for `processType`, which in particular
requires the projected alphabets at every `.par` node to stay
`ParallelCompatible`.  (This side-condition is genuinely necessary, not a
proof-engineering artifact: reannotating a `.par` node to a target whose
interface actions are not already explained by the original children can
break `AlphabetWellFormed`, independent of any `MessageActions`/`ProgressIds`/
`FairChoiceIds` containment.) -/
theorem PactType.reannotate_alphabetWellFormed
    (alphabet : PactTypeAlphabet) :
    ∀ processType : PactType, processType.AlphabetWellFormed →
      alphabet.WellFormed → PactType.ReannotationSafe alphabet processType →
      (processType.reannotate alphabet).AlphabetWellFormed := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType alphabet with
  | _ n ih =>
      have hBranches : ∀ sourceAlphabet (branches : List (BareMessage × PactType)),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.BranchesAlphabetWellFormed sourceAlphabet branches →
          branchAlphabet.WellFormed →
          PactType.ReannotationSafeBranches branchAlphabet branches →
          PactType.BranchesAlphabetWellFormed branchAlphabet
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro sourceAlphabet branches hBranchesSize branchAlphabet hWF hBAWF hSafe
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.BranchesAlphabetWellFormed]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.ReannotationSafeBranches] at hSafe
            simp only [PactType.BranchesAlphabetWellFormed]
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
            refine ⟨hSafe.1, PactType.reannotate_alphabet branchAlphabet branchType,
              ih (sizeOf branchType) hBranchSize branchAlphabet branchType rfl
                hWF.2.2.1 hBAWF hSafe.2.1,
              restIH hRestSize hWF.2.2.2 hSafe.2.2⟩
      intro hWF hAlphaWF hSafe
      cases processType with
      | message alphabet0 msg dir =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp [PactType.reannotate, PactType.AlphabetWellFormed, hAlphaWF, hSafe]
      | progress alphabet0 pid =>
          simp only [PactType.ReannotationSafe] at hSafe
          simp [PactType.reannotate, PactType.AlphabetWellFormed, hAlphaWF, hSafe]
      | tock alphabet0 | skip alphabet0 | var alphabet0 _ =>
          simp [PactType.reannotate, PactType.AlphabetWellFormed, hAlphaWF]
      | choice alphabet0 left right | seq alphabet0 left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hAlphaWF, PactType.reannotate_alphabet alphabet left,
            PactType.reannotate_alphabet alphabet right,
            ih (sizeOf left) hLeftSize alphabet left rfl hWF.2.2.2.1 hAlphaWF hSafe.1,
            ih (sizeOf right) hRightSize alphabet right rfl hWF.2.2.2.2 hAlphaWF hSafe.2⟩
      | fairChoice alphabet0 bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hAlphaWF, hSafe.1, PactType.reannotate_alphabet alphabet left,
            PactType.reannotate_alphabet alphabet right,
            ih (sizeOf left) hLeftSize alphabet left rfl hWF.2.2.2.2.1 hAlphaWF hSafe.2.1,
            ih (sizeOf right) hRightSize alphabet right rfl hWF.2.2.2.2.2 hAlphaWF hSafe.2.2⟩
      | par alphabet0 left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftAWF := hSafe.1.wellFormed_left hAlphaWF
          have hRightAWF := hSafe.1.wellFormed_right hAlphaWF
          refine ⟨hAlphaWF, ?_,
            ih (sizeOf left) hLeftSize _ left rfl hWF.2.2.1 hLeftAWF hSafe.2.1,
            ih (sizeOf right) hRightSize _ right rfl hWF.2.2.2 hRightAWF hSafe.2.2⟩
          simpa [PactType.reannotate_alphabet] using hSafe.1
      | recur alphabet0 name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hAlphaWF, PactType.reannotate_alphabet alphabet body,
            ih (sizeOf body) hBodySize alphabet body rfl hWF.2.2 hAlphaWF hSafe⟩
      | xoffer alphabet0 elseType branches | offer alphabet0 elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe] at hSafe
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hAlphaWF, PactType.reannotate_alphabet alphabet elseType,
            ih (sizeOf elseType) hElseSize alphabet elseType rfl hWF.2.2.1 hAlphaWF hSafe.1,
            hBranches alphabet0 branches hBranchesSize alphabet hWF.2.2.2 hAlphaWF hSafe.2⟩

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

theorem singletonTypeXOfferAt_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hAction : branch.1 ∈ alphabet.actions)
    (hBranch : branch.2.AlphabetWellFormed)
    (hSafe : PactType.ReannotationSafe alphabet branch.2) :
    (singletonTypeXOfferAt alphabet branch).AlphabetWellFormed := by
  rcases branch with ⟨action, branchType⟩
  simp only [singletonTypeXOfferAt, PactType.AlphabetWellFormed,
    PactType.BranchesAlphabetWellFormed, PactType.alphabet] at hAction ⊢
  exact ⟨hAlphaWF, trivial, hAlphaWF, hAction,
    PactType.reannotate_alphabet alphabet branchType,
    PactType.reannotate_alphabetWellFormed alphabet branchType hBranch hAlphaWF hSafe,
    trivial⟩

theorem selectedTypeBranchAt_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hAction : branch.1 ∈ alphabet.actions)
    (hBranch : branch.2.AlphabetWellFormed)
    (hSafe : PactType.ReannotationSafe alphabet branch.2) :
    (selectedTypeBranchAt alphabet branch).AlphabetWellFormed := by
  rcases branch with ⟨action, branchType⟩
  simp only [selectedTypeBranchAt, PactType.AlphabetWellFormed,
    PactType.alphabet] at hAction ⊢
  exact ⟨hAlphaWF, trivial, PactType.reannotate_alphabet alphabet branchType,
    ⟨hAlphaWF, hAction⟩,
    PactType.reannotate_alphabetWellFormed alphabet branchType hBranch hAlphaWF hSafe⟩

/-- `branchPart` only removes declarations, so it keeps `OnePolarity`. -/
theorem PactTypeAlphabet.branchPart_wellFormed
    {parent : PactTypeAlphabet} (hParentWF : parent.WellFormed)
    (branch : BareMessage × PactType) :
    (PactTypeAlphabet.branchPart parent branch).WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  simp only [PactTypeAlphabet.branchPart, Finset.mem_inter] at hSend hRecv
  exact hParentWF msg ⟨hSend.1, hRecv.1⟩

/-- `remove` only removes declarations, so it keeps `OnePolarity`. -/
theorem PactTypeAlphabet.remove_wellFormed
    {parent assigned : PactTypeAlphabet} (hParentWF : parent.WellFormed) :
    (PactTypeAlphabet.remove parent assigned).WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  simp only [PactTypeAlphabet.remove, Finset.mem_sdiff] at hSend hRecv
  exact hParentWF msg ⟨hSend.1, hRecv.1⟩

theorem branch_action_mem_fixedAlphabet_of_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    action ∈ alphabet.actions := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2.2 hMem

theorem branch_body_alphabetWellFormed_of_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    branchType.AlphabetWellFormed := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hBranches.2.2.1
      · exact ih hBranches.2.2.2 hMem

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

/-- Branch action labels distinct from a head branch's own label and disjoint
from its body's syntactic actions survive that head's `branchPart`/`remove`
split unchanged.  Needed because `parallelTypeBranchesWithin` re-partitions
the fixed alphabet branch by branch: without this, a later branch's action
could collide with the part already carved out for an earlier one. -/
theorem PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint
    {alphabet : PactTypeAlphabet} {branch other : BareMessage × PactType}
    (hMem : other.1 ∈ alphabet.actions)
    (hDisjoint : Disjoint ({branch.1} ∪ PactType.MessageActions branch.2)
      ({other.1} ∪ PactType.MessageActions other.2)) :
    other.1 ∈ (PactTypeAlphabet.remove alphabet
      (PactTypeAlphabet.branchPart alphabet branch)).actions := by
  simp only [PactTypeAlphabet.remove, PactTypeAlphabet.branchPart, Finset.mem_sdiff,
    Finset.mem_inter]
  refine ⟨hMem, fun ⟨_, hOtherInBranch⟩ => ?_⟩
  exact hDisjoint.forall_ne_finset hOtherInBranch (Finset.mem_union_left _
    (Finset.mem_singleton_self other.1)) rfl

theorem parallelTypeBranchesWithin_alphabet_wellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed) :
    ∀ branches : List (BareMessage × PactType),
      List.Pairwise (fun b1 b2 => Disjoint ({b1.1} ∪ PactType.MessageActions b1.2)
        ({b2.1} ∪ PactType.MessageActions b2.2)) branches →
      (∀ branch ∈ branches, branch.1 ∈ alphabet.actions ∧
        branch.2.AlphabetWellFormed ∧
        ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet branch.2) →
      (parallelTypeBranchesWithin alphabet branches).AlphabetWellFormed
  | [], _, _ => by simp [parallelTypeBranchesWithin, PactType.AlphabetWellFormed, hAlphaWF]
  | [branch], _, hBranches => by
      have hHead := hBranches branch (by simp)
      exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
        (hHead.2.2 alphabet)
  | branch :: next :: rest, hPairwise, hBranches => by
      have hLeftWF := PactTypeAlphabet.branchPart_wellFormed hAlphaWF branch
      have hRightWF := PactTypeAlphabet.remove_wellFormed
        (assigned := PactTypeAlphabet.branchPart alphabet branch) hAlphaWF
      have hHead := hBranches branch (by simp)
      have hHeadActionLeft :
          branch.1 ∈ (PactTypeAlphabet.branchPart alphabet branch).actions := by
        simp only [PactTypeAlphabet.branchPart, Finset.mem_inter]
        exact ⟨hHead.1, Finset.mem_union_left _ (Finset.mem_singleton_self branch.1)⟩
      rw [List.pairwise_cons] at hPairwise
      obtain ⟨hHeadDisjoint, hTailPairwise⟩ := hPairwise
      have hLeftAlphabet :
          (singletonTypeXOfferAt (PactTypeAlphabet.branchPart alphabet branch) branch).alphabet =
            PactTypeAlphabet.branchPart alphabet branch := by
        simp [singletonTypeXOfferAt, PactType.alphabet]
      have hRightAlphabet :
          (parallelTypeBranchesWithin
            (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
            (next :: rest)).alphabet =
            PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch) := by
        cases rest <;> simp [parallelTypeBranchesWithin, singletonTypeXOfferAt, PactType.alphabet]
      simp only [parallelTypeBranchesWithin, PactType.AlphabetWellFormed]
      rw [hLeftAlphabet, hRightAlphabet]
      exact ⟨hAlphaWF,
        PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet hAlphaWF branch,
        singletonTypeXOfferAt_alphabetWellFormed
          (PactTypeAlphabet.branchPart alphabet branch) hLeftWF hHeadActionLeft hHead.2.1
          (hHead.2.2 _),
        parallelTypeBranchesWithin_alphabet_wellFormed
          (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
          hRightWF (next :: rest) hTailPairwise
          (fun item hItem =>
            have hItemBranches := hBranches item (by simp [hItem])
            ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hItemBranches.1
              (hHeadDisjoint item hItem), hItemBranches.2.1, hItemBranches.2.2⟩)⟩

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

theorem parallelTypeBranchesSelectingWithin_alphabet_wellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed)
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      List.Pairwise (fun b1 b2 => Disjoint ({b1.1} ∪ PactType.MessageActions b1.2)
        ({b2.1} ∪ PactType.MessageActions b2.2)) branches →
      (∀ branch ∈ branches, branch.1 ∈ alphabet.actions ∧
        branch.2.AlphabetWellFormed ∧
        ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet branch.2) →
      PactType.AlphabetWellFormed
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [], _, _ => by
      simp [parallelTypeBranchesSelectingWithin, PactType.AlphabetWellFormed, hAlphaWF]
  | [branch], _, hBranches => by
      have hHead := hBranches branch (by simp)
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
        exact selectedTypeBranchAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
          (hHead.2.2 alphabet)
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
        exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
          (hHead.2.2 alphabet)
  | branch :: next :: rest, hPairwise, hBranches => by
      have hLeftWF := PactTypeAlphabet.branchPart_wellFormed hAlphaWF branch
      have hRightWF := PactTypeAlphabet.remove_wellFormed
        (assigned := PactTypeAlphabet.branchPart alphabet branch) hAlphaWF
      have hHead := hBranches branch (by simp)
      have hHeadActionLeft :
          branch.1 ∈ (PactTypeAlphabet.branchPart alphabet branch).actions := by
        simp only [PactTypeAlphabet.branchPart, Finset.mem_inter]
        exact ⟨hHead.1, Finset.mem_union_left _ (Finset.mem_singleton_self branch.1)⟩
      rw [List.pairwise_cons] at hPairwise
      obtain ⟨hHeadDisjoint, hTailPairwise⟩ := hPairwise
      have hRestSafe : ∀ item ∈ next :: rest,
          item.1 ∈ (PactTypeAlphabet.remove alphabet
            (PactTypeAlphabet.branchPart alphabet branch)).actions ∧
          item.2.AlphabetWellFormed ∧
          ∀ targetAlphabet, PactType.ReannotationSafe targetAlphabet item.2 :=
        fun item hItem =>
          have hItemBranches := hBranches item (by simp [hItem])
          ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hItemBranches.1
            (hHeadDisjoint item hItem), hItemBranches.2.1, hItemBranches.2.2⟩
      have hCompatible :=
        PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet hAlphaWF branch
      by_cases hSelected : branch = selected
      · have hLeftAlphabet :
            (selectedTypeBranchAt (PactTypeAlphabet.branchPart alphabet branch) branch).alphabet =
              PactTypeAlphabet.branchPart alphabet branch := by
          simp [selectedTypeBranchAt, PactType.alphabet]
        have hRightAlphabet :
            (parallelTypeBranchesWithin
              (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
              (next :: rest)).alphabet =
              PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch) := by
          cases rest <;>
            simp [parallelTypeBranchesWithin, singletonTypeXOfferAt, PactType.alphabet]
        simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected,
          PactType.AlphabetWellFormed]
        rw [hLeftAlphabet, hRightAlphabet]
        exact ⟨hAlphaWF, hCompatible,
          selectedTypeBranchAt_alphabetWellFormed
            (PactTypeAlphabet.branchPart alphabet branch) hLeftWF hHeadActionLeft hHead.2.1
            (hHead.2.2 _),
          parallelTypeBranchesWithin_alphabet_wellFormed
            (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
            hRightWF (next :: rest) hTailPairwise hRestSafe⟩
      · have hLeftAlphabet :
            (singletonTypeXOfferAt (PactTypeAlphabet.branchPart alphabet branch) branch).alphabet =
              PactTypeAlphabet.branchPart alphabet branch := by
          simp [singletonTypeXOfferAt, PactType.alphabet]
        have hRightAlphabet :
            (parallelTypeBranchesSelectingWithin
              (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
              selected (next :: rest)).alphabet =
              PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch) :=
          parallelTypeBranchesSelectingWithin_alphabet _ selected (next :: rest)
        simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected,
          PactType.AlphabetWellFormed]
        rw [hLeftAlphabet, hRightAlphabet]
        exact ⟨hAlphaWF, hCompatible,
          singletonTypeXOfferAt_alphabetWellFormed
            (PactTypeAlphabet.branchPart alphabet branch) hLeftWF hHeadActionLeft hHead.2.1
            (hHead.2.2 _),
          parallelTypeBranchesSelectingWithin_alphabet_wellFormed
            (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
            hRightWF selected (next :: rest) hTailPairwise hRestSafe⟩

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

theorem parallelTypeBranchesSelecting_alphabet_wellFormed
    {alphabet : PactTypeAlphabet} (hAlphaWF : alphabet.WellFormed)
    {selected : BareMessage × PactType} {branches : List (BareMessage × PactType)}
    (hSelected : selected ∈ branches)
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise (fun b1 b2 => Disjoint ({b1.1} ∪ PactType.MessageActions b1.2)
      ({b2.1} ∪ PactType.MessageActions b2.2)) branches)
    (hSafe : ∀ branch ∈ branches, ∀ targetAlphabet,
      PactType.ReannotationSafe targetAlphabet branch.2) :
    (parallelTypeBranchesSelecting selected branches).alphabet = alphabet ∧
      (parallelTypeBranchesSelecting selected branches).AlphabetWellFormed := by
  cases branches with
  | nil => cases hSelected
  | cons branch rest =>
      have hFirstAlphabet : branch.2.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem hBranches (by simp)
      simp only [parallelTypeBranchesSelecting, hFirstAlphabet]
      refine ⟨parallelTypeBranchesSelectingWithin_alphabet alphabet selected (branch :: rest), ?_⟩
      apply parallelTypeBranchesSelectingWithin_alphabet_wellFormed alphabet hAlphaWF selected
        (branch :: rest) hPairwise
      intro item hItem
      exact ⟨branch_action_mem_fixedAlphabet_of_mem hBranches
          (branchType := item.2) (by simpa using hItem),
        branch_body_alphabetWellFormed_of_mem hBranches (by simpa using hItem),
        hSafe item hItem⟩

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
