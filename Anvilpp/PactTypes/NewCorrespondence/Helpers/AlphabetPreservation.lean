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
    | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .choice _ left right | .seq _ left right
    | .fairChoice _ _ left right =>
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

/-- Every case of `AlphabetWellFormed` opens with the node alphabet's own
well-formedness. -/
theorem PactType.AlphabetWellFormed.alphabet_wellFormed
    {processType : PactType} (hWF : processType.AlphabetWellFormed) :
    processType.alphabet.WellFormed := by
  cases processType <;>
    simp only [PactType.AlphabetWellFormed] at hWF <;>
    first
      | exact hWF
      | exact hWF.1

/-- One alphabet declares no more than another. -/
def PactTypeAlphabet.Subalphabet (small large : PactTypeAlphabet) : Prop :=
  small.actions ⊆ large.actions

/-- Restricted to a target it already covers, the child projection keeps the
child's interface actions and its declarations shared with the target. -/
theorem PactTypeAlphabet.projectParallelChild_actions
    (target child : PactTypeAlphabet) (interface : Interface) :
    (projectParallelChild target child interface).actions =
      child.actions.filter fun action =>
        action.1 ∈ interface ∨ action ∈ target.actions := rfl

/-- The left projection keeps the left child's own projection and whatever the
target declares outside the right child. -/
theorem PactTypeAlphabet.projectParallelLeft_actions
    (target left right : PactTypeAlphabet) (interface : Interface) :
    (projectParallelLeft target left right interface).actions =
      (left.actions.filter fun action =>
          action.1 ∈ interface ∨ action ∈ target.actions) ∪
        (target.actions \ right.actions) := by
  simp only [projectParallelLeft, projectParallelChild]
  congr 1
  apply Finset.ext
  intro a
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun hr => hn ⟨hr, Or.inr ha⟩⟩
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun h => hn h.1⟩

/-- The child projection only filters, so it inherits the child's own
one-polarity property. -/
theorem PactTypeAlphabet.projectParallelChild_wellFormed
    {target child : PactTypeAlphabet} {interface : Interface}
    (hChildWF : child.WellFormed) :
    (projectParallelChild target child interface).WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  rw [projectParallelChild_actions] at hSend hRecv
  exact hChildWF msg
    ⟨(Finset.mem_filter.mp hSend).1, (Finset.mem_filter.mp hRecv).1⟩

/-- The left projection mixes the left child's declarations with the target's
own.  A target that hides the interface keeps the two halves from colliding. -/
theorem PactTypeAlphabet.projectParallelLeft_wellFormed
    {target left right : PactTypeAlphabet} {interface : Interface}
    (hLeftWF : left.WellFormed) (hTargetWF : target.WellFormed)
    (hTargetHidden : ∀ action ∈ target.actions, action.1 ∉ interface) :
    (projectParallelLeft target left right interface).WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  rw [projectParallelLeft_actions] at hSend hRecv
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    at hSend hRecv
  rcases hSend with ⟨hSendL, hSendI⟩ | ⟨hSendT, _⟩ <;>
    rcases hRecv with ⟨hRecvL, hRecvI⟩ | ⟨hRecvT, _⟩
  · exact hLeftWF msg ⟨hSendL, hRecvL⟩
  · rcases hSendI with hI | hSendT
    · exact hTargetHidden _ hRecvT hI
    · exact hTargetWF msg ⟨hSendT, hRecvT⟩
  · rcases hRecvI with hI | hRecvT
    · exact hTargetHidden _ hSendT hI
    · exact hTargetWF msg ⟨hSendT, hRecvT⟩
  · exact hTargetWF msg ⟨hSendT, hRecvT⟩

/-- Splitting a target that the parallel node's own alphabet already covers
gives two projected children compatible with it.  The interface actions are
taken from the original children, so no interface message is lost. -/
theorem PactTypeAlphabet.projectParallel_compatible
    {parent left right target : PactTypeAlphabet} {interface : Interface}
    (hCompatible : ParallelCompatible parent left right interface)
    (hSub : Subalphabet target parent) :
    ParallelCompatible target (projectParallelLeft target left right interface)
      (projectParallelChild target right interface) interface := by
  have hParentActions : parent.actions =
      (left.actions ∪ right.actions).filter fun action => action.1 ∉ interface := by
    rw [hCompatible.parent_eq]; rfl
  have hTargetNoInterface : ∀ a ∈ target.actions, a.1 ∉ interface := by
    intro a ha
    have := hSub ha
    rw [hParentActions] at this
    exact (Finset.mem_filter.mp this).2
  have hLeftActions : (projectParallelLeft target left right interface).actions =
      (left.actions.filter fun action =>
          action.1 ∈ interface ∨ action ∈ target.actions) ∪
        (target.actions \ right.actions) :=
    projectParallelLeft_actions target left right interface
  have hRightActions : (projectParallelChild target right interface).actions =
      right.actions.filter fun action =>
        action.1 ∈ interface ∨ action ∈ target.actions := rfl
  refine
    { parent_eq := ?parentEq
      complementary := ?complementary }
  case parentEq =>
    have hA : ((projectParallelLeft target left right interface).actions ∪
        (projectParallelChild target right interface).actions).filter
          (fun action => action.1 ∉ interface) = target.actions := by
      rw [hLeftActions, hRightActions]
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨(((haL | haT) | haR)), hI⟩
        · rcases haL.2 with h | h
          · exact absurd h hI
          · exact h
        · exact haT.1
        · rcases haR.2 with h | h
          · exact absurd h hI
          · exact h
      · intro ha
        refine ⟨?_, hTargetNoInterface a ha⟩
        by_cases hR : a ∈ right.actions
        · exact Or.inr ⟨hR, Or.inr ha⟩
        · exact Or.inl (Or.inr ⟨ha, hR⟩)
    show target = { actions := _ }
    rw [hA]
  case complementary =>
    intro msg hMsg
    rcases hCompatible.complementary msg hMsg with ⟨hL, hR⟩ | ⟨hL, hR⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hLeftActions]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hL, Or.inl hMsg⟩)
      · rw [hRightActions]
        exact Finset.mem_filter.mpr ⟨hR, Or.inl hMsg⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hLeftActions]
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hL, Or.inl hMsg⟩)
      · rw [hRightActions]
        exact Finset.mem_filter.mpr ⟨hR, Or.inl hMsg⟩

/-- Progress identifiers occurring in a well-formed type are declared by its
alphabet.  Unlike message actions, no parallel interface hides them. -/
theorem PactType.progressIds_subset_alphabet :
    ∀ processType : PactType, processType.AlphabetWellFormed →
      processType.ProgressIds ⊆ processType.alphabet.progress := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (alphabet : PactTypeAlphabet) branches,
          sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.BranchProgressIds branches ⊆ alphabet.progress := by
        intro alphabet branches hBranchesSize hWF
        induction branches with
        | nil => simp [PactType.BranchProgressIds]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.BranchProgressIds]
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
            have hHead := ih (sizeOf branchType) hBranchSize branchType rfl hWF.2.2.1
            rw [hWF.2.1] at hHead
            exact Finset.union_subset hHead (restIH hTailSize hWF.2.2.2)
      intro hWF
      cases processType with
      | progress alphabet pid =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp [PactType.ProgressIds, PactType.alphabet, hWF.2]
      | message alphabet msg dir => simp [PactType.ProgressIds]
      | tock alphabet | skip alphabet | var alphabet _ => simp [PactType.ProgressIds]
      | choice alphabet left right | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ProgressIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2.2
          rw [hWF.2.1] at hLeft
          rw [hWF.2.2.1] at hRight
          exact Finset.union_subset hLeft hRight
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ProgressIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2.2.2
          rw [hWF.2.2.1] at hLeft
          rw [hWF.2.2.2.1] at hRight
          exact Finset.union_subset hLeft hRight
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ProgressIds, PactType.alphabet]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hBody := ih (sizeOf body) hB body rfl hWF.2.2
          rw [hWF.2.1] at hBody
          exact hBody
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ProgressIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2
          have hProgress : alphabet.progress =
              left.alphabet.progress ∪ right.alphabet.progress := by
            rw [hWF.2.1.parent_eq]; rfl
          rw [hProgress]
          exact Finset.union_subset (hLeft.trans Finset.subset_union_left)
            (hRight.trans Finset.subset_union_right)
      | xoffer alphabet elseType branches | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ProgressIds, PactType.alphabet]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          have hElse := ih (sizeOf elseType) hE elseType rfl hWF.2.2.1
          rw [hWF.2.1] at hElse
          exact Finset.union_subset hElse (hBranches alphabet branches hBr hWF.2.2.2)

/-- Fair-choice identifiers occurring in a well-formed type are declared by its
alphabet.  Unlike message actions, no parallel interface hides them. -/
theorem PactType.fairChoiceIds_subset_alphabet :
    ∀ processType : PactType, processType.AlphabetWellFormed →
      processType.FairChoiceIds ⊆ processType.alphabet.fair := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (alphabet : PactTypeAlphabet) branches,
          sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.BranchFairChoiceIds branches ⊆ alphabet.fair := by
        intro alphabet branches hBranchesSize hWF
        induction branches with
        | nil => simp [PactType.BranchFairChoiceIds]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.BranchFairChoiceIds]
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
            have hHead := ih (sizeOf branchType) hBranchSize branchType rfl hWF.2.2.1
            rw [hWF.2.1] at hHead
            exact Finset.union_subset hHead (restIH hTailSize hWF.2.2.2)
      intro hWF
      cases processType with
      | progress alphabet pid | message alphabet _ _ =>
          simp [PactType.FairChoiceIds]
      | tock alphabet | skip alphabet | var alphabet _ => simp [PactType.FairChoiceIds]
      | choice alphabet left right | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.FairChoiceIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2.2
          rw [hWF.2.1] at hLeft
          rw [hWF.2.2.1] at hRight
          exact Finset.union_subset hLeft hRight
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.FairChoiceIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2.2.2
          rw [hWF.2.2.1] at hLeft
          rw [hWF.2.2.2.1] at hRight
          exact Finset.union_subset
            (Finset.union_subset (Finset.singleton_subset_iff.mpr hWF.2.1) hLeft) hRight
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.FairChoiceIds, PactType.alphabet]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hBody := ih (sizeOf body) hB body rfl hWF.2.2
          rw [hWF.2.1] at hBody
          exact hBody
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.FairChoiceIds, PactType.alphabet]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hL left rfl hWF.2.2.1
          have hRight := ih (sizeOf right) hR right rfl hWF.2.2.2
          have hFair : alphabet.fair =
              left.alphabet.fair ∪ right.alphabet.fair := by
            rw [hWF.2.1.parent_eq]; rfl
          rw [hFair]
          exact Finset.union_subset (hLeft.trans Finset.subset_union_left)
            (hRight.trans Finset.subset_union_right)
      | xoffer alphabet elseType branches | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.FairChoiceIds, PactType.alphabet]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          have hElse := ih (sizeOf elseType) hE elseType rfl hWF.2.2.1
          rw [hWF.2.1] at hElse
          exact Finset.union_subset hElse (hBranches alphabet branches hBr hWF.2.2.2)

/-- Reannotating to a smaller target is safe once the target keeps every
visible action, progress identifier and fair-choice identifier of the type.
Actions hidden by an inner parallel interface need not be declared: they are
recovered from the original child alphabets by the projections. -/
theorem PactType.reannotationSafe_of_subalphabet :
    ∀ (processType : PactType) (target : PactTypeAlphabet),
      processType.AlphabetWellFormed → target.WellFormed →
      PactTypeAlphabet.Subalphabet target processType.alphabet →
      processType.MessageActions ∩ processType.alphabet.actions ⊆ target.actions →
      processType.ProgressIds ⊆ target.progress →
      processType.FairChoiceIds ⊆ target.fair →
      PactType.ReannotationSafe target processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (alphabet target : PactTypeAlphabet) branches,
          sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          target.WellFormed → PactTypeAlphabet.Subalphabet target alphabet →
          PactType.BranchMessageActions branches ∩ alphabet.actions ⊆ target.actions →
          PactType.BranchProgressIds branches ⊆ target.progress →
          PactType.BranchFairChoiceIds branches ⊆ target.fair →
          PactType.ReannotationSafeBranches target branches := by
        intro alphabet target branches hBranchesSize hWF hTargetWF hSub
          hActions hProgress hFair
        induction branches with
        | nil => simp [PactType.ReannotationSafeBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.BranchMessageActions] at hActions
            simp only [PactType.BranchProgressIds] at hProgress
            simp only [PactType.BranchFairChoiceIds] at hFair
            simp only [PactType.ReannotationSafeBranches]
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
            refine ⟨hActions (Finset.mem_inter.mpr ⟨by simp, hWF.1⟩), ?_, ?_⟩
            · refine ih (sizeOf branchType) hBranchSize branchType rfl target
                hWF.2.2.1 hTargetWF (by rw [hWF.2.1]; exact hSub) ?_
                (fun x hx => hProgress (Finset.mem_union_left _ hx))
                (fun x hx => hFair (Finset.mem_union_left _ hx))
              rw [hWF.2.1]
              exact fun a ha => hActions (Finset.mem_inter.mpr
                ⟨Finset.mem_union_left _ (Finset.mem_union_right _
                  (Finset.mem_inter.mp ha).1), (Finset.mem_inter.mp ha).2⟩)
            · exact restIH hTailSize hWF.2.2.2
                (fun a ha => hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
                (fun x hx => hProgress (Finset.mem_union_right _ hx))
                (fun x hx => hFair (Finset.mem_union_right _ hx))
      intro target hWF hTargetWF hSub hActions hProgress hFair
      cases processType with
      | message alphabet msg dir =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.ReannotationSafe]
          apply hActions
          simp [PactType.MessageActions, PactType.alphabet, hWF.2]
      | progress alphabet pid =>
          simp only [PactType.ReannotationSafe]
          exact hProgress (by simp [PactType.ProgressIds])
      | tock alphabet | skip alphabet | var alphabet _ =>
          simp [PactType.ReannotationSafe]
      | choice alphabet left right | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.alphabet] at hActions hProgress hFair
          simp only [PactType.alphabet] at hSub
          simp only [PactType.ReannotationSafe]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          constructor
          · exact ih (sizeOf left) hL left rfl target hWF.2.2.2.1 hTargetWF
              (by rw [hWF.2.1]; exact hSub)
              (by rw [hWF.2.1]; exact fun a ha =>
                hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_left _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_left _ hx))
              (fun x hx => hFair (Finset.mem_union_left _ hx))
          · exact ih (sizeOf right) hR right rfl target hWF.2.2.2.2 hTargetWF
              (by rw [hWF.2.2.1]; exact hSub)
              (by rw [hWF.2.2.1]; exact fun a ha =>
                hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_right _ hx))
              (fun x hx => hFair (Finset.mem_union_right _ hx))
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.alphabet] at hActions hProgress hFair
          simp only [PactType.alphabet] at hSub
          simp only [PactType.ReannotationSafe]
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          refine ⟨hFair (by simp), ?_, ?_⟩
          · exact ih (sizeOf left) hL left rfl target hWF.2.2.2.2.1 hTargetWF
              (by rw [hWF.2.2.1]; exact hSub)
              (by rw [hWF.2.2.1]; exact fun a ha =>
                hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_left _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_left _ hx))
              (fun x hx => hFair (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
          · exact ih (sizeOf right) hR right rfl target hWF.2.2.2.2.2 hTargetWF
              (by rw [hWF.2.2.2.1]; exact hSub)
              (by rw [hWF.2.2.2.1]; exact fun a ha =>
                hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_right _ hx))
              (fun x hx => hFair (Finset.mem_union_right _ hx))
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.alphabet] at hActions hProgress hFair
          simp only [PactType.alphabet] at hSub
          simp only [PactType.ReannotationSafe]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ih (sizeOf body) hB body rfl target hWF.2.2 hTargetWF
            (by rw [hWF.2.1]; exact hSub) (by rw [hWF.2.1]; exact hActions)
            hProgress hFair
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.alphabet] at hActions hProgress hFair
          simp only [PactType.alphabet] at hSub
          simp only [PactType.ReannotationSafe]
          have hCompatible := hWF.2.1
          have hLeftWF := hWF.2.2.1
          have hRightWF := hWF.2.2.2
          have hLeftAlphaWF := hLeftWF.alphabet_wellFormed
          have hRightAlphaWF := hRightWF.alphabet_wellFormed
          have hParentActions : alphabet.actions =
              (left.alphabet.actions ∪ right.alphabet.actions).filter
                fun action => action.1 ∉ interface := by
            rw [hCompatible.parent_eq]; rfl
          have hParentProgress : alphabet.progress =
              left.alphabet.progress ∪ right.alphabet.progress := by
            rw [hCompatible.parent_eq]; rfl
          have hParentFair : alphabet.fair =
              left.alphabet.fair ∪ right.alphabet.fair := by
            rw [hCompatible.parent_eq]; rfl
          set targetLeft := PactTypeAlphabet.projectParallelLeft target
            left.alphabet right.alphabet interface with hTargetLeft
          set targetRight := PactTypeAlphabet.projectParallelChild target
            right.alphabet interface with hTargetRight
          have hLeftActions : targetLeft.actions =
              (left.alphabet.actions.filter fun action =>
                  action.1 ∈ interface ∨ action ∈ target.actions) ∪
                (target.actions \ right.alphabet.actions) :=
            PactTypeAlphabet.projectParallelLeft_actions _ _ _ _
          have hRightActions : targetRight.actions =
              right.alphabet.actions.filter fun action =>
                action.1 ∈ interface ∨ action ∈ target.actions := rfl
          have hTargetHidden : ∀ action ∈ target.actions, action.1 ∉ interface := by
            intro a ha
            have := hSub.1 ha
            rw [hParentActions] at this
            exact (Finset.mem_filter.mp this).2
          have hProjCompatible :=
            PactTypeAlphabet.projectParallel_compatible hCompatible hSub
          have hL : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftVisible := PactType.progressIds_subset_alphabet left hLeftWF
          have hRightVisible := PactType.progressIds_subset_alphabet right hRightWF
          have hLeftFairVisible := PactType.fairChoiceIds_subset_alphabet left hLeftWF
          have hRightFairVisible := PactType.fairChoiceIds_subset_alphabet right hRightWF
          refine ⟨hProjCompatible, ?_, ?_⟩
          · refine ih (sizeOf left) hL left rfl targetLeft hLeftWF
              (PactTypeAlphabet.projectParallelLeft_wellFormed hLeftAlphaWF
                hTargetWF hTargetHidden) ?_ ?_ ?_ ?_
            · refine ⟨?_, ?_, ?_⟩
              · rw [hLeftActions]
                refine Finset.union_subset (Finset.filter_subset _ _) ?_
                intro a ha
                simp only [Finset.mem_sdiff] at ha
                have := hSub.1 ha.1
                rw [hParentActions, Finset.mem_filter, Finset.mem_union] at this
                rcases this.1 with h | h
                · exact h
                · exact absurd h ha.2
              · rw [PactTypeAlphabet.projectParallelLeft_progress]
                intro x hx
                simp only [Finset.mem_sdiff] at hx
                have := hSub.2.1 hx.1
                rw [hParentProgress, Finset.mem_union] at this
                rcases this with h | h
                · exact h
                · exact absurd h hx.2
              · rw [PactTypeAlphabet.projectParallelLeft_fair]
                intro x hx
                simp only [Finset.mem_sdiff] at hx
                have := hSub.2.2 hx.1
                rw [hParentFair, Finset.mem_union] at this
                rcases this with h | h
                · exact h
                · exact absurd h hx.2
            · intro a ha
              simp only [Finset.mem_inter] at ha
              rw [hLeftActions]
              refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha.2, ?_⟩)
              by_cases hI : a.1 ∈ interface
              · exact Or.inl hI
              · refine Or.inr (hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_left _ ha.1, ?_⟩))
                rw [hParentActions, Finset.mem_filter, Finset.mem_union]
                exact ⟨Or.inl ha.2, hI⟩
            · rw [PactTypeAlphabet.projectParallelLeft_progress]
              intro x hx
              refine Finset.mem_sdiff.mpr
                ⟨hProgress (Finset.mem_union_left _ hx), fun hRight =>
                  hCompatible.progress_disjoint.forall_ne_finset
                    (hLeftVisible hx) hRight rfl⟩
            · rw [PactTypeAlphabet.projectParallelLeft_fair]
              intro x hx
              refine Finset.mem_sdiff.mpr
                ⟨hFair (Finset.mem_union_left _ hx), fun hRight =>
                  hCompatible.fair_disjoint.forall_ne_finset
                    (hLeftFairVisible hx) hRight rfl⟩
          · refine ih (sizeOf right) hR right rfl targetRight hRightWF
              (PactTypeAlphabet.projectParallelChild_wellFormed hRightAlphaWF)
              ?_ ?_ ?_ ?_
            · exact ⟨Finset.filter_subset _ _, Finset.inter_subset_left,
                Finset.inter_subset_left⟩
            · intro a ha
              simp only [Finset.mem_inter] at ha
              rw [hRightActions]
              refine Finset.mem_filter.mpr ⟨ha.2, ?_⟩
              by_cases hI : a.1 ∈ interface
              · exact Or.inl hI
              · refine Or.inr (hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_right _ ha.1, ?_⟩))
                rw [hParentActions, Finset.mem_filter, Finset.mem_union]
                exact ⟨Or.inr ha.2, hI⟩
            · intro x hx
              exact Finset.mem_inter.mpr
                ⟨hRightVisible hx, hProgress (Finset.mem_union_right _ hx)⟩
            · intro x hx
              exact Finset.mem_inter.mpr
                ⟨hRightFairVisible hx, hFair (Finset.mem_union_right _ hx)⟩
      | xoffer alphabet elseType branches | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds, PactType.alphabet] at hActions hProgress hFair
          simp only [PactType.alphabet] at hSub
          simp only [PactType.ReannotationSafe]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          constructor
          · exact ih (sizeOf elseType) hE elseType rfl target hWF.2.2.1 hTargetWF
              (by rw [hWF.2.1]; exact hSub)
              (by rw [hWF.2.1]; exact fun a ha =>
                hActions (Finset.mem_inter.mpr
                  ⟨Finset.mem_union_left _ (Finset.mem_inter.mp ha).1,
                    (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_left _ hx))
              (fun x hx => hFair (Finset.mem_union_left _ hx))
          · exact hBranches alphabet target branches hBr hWF.2.2.2 hTargetWF hSub
              (fun a ha => hActions (Finset.mem_inter.mpr
                ⟨Finset.mem_union_right _ (Finset.mem_inter.mp ha).1,
                  (Finset.mem_inter.mp ha).2⟩))
              (fun x hx => hProgress (Finset.mem_union_right _ hx))
              (fun x hx => hFair (Finset.mem_union_right _ hx))

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
          -- `parent_eq` hides the interface, so the reannotation target itself
          -- declares no interface action.
          have hTargetHidden : ∀ action ∈ alphabet.actions,
              action.1 ∉ interface := by
            intro a ha
            rw [hSafe.1.parent_eq] at ha
            simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter] at ha
            exact ha.2
          have hLeftAWF := PactTypeAlphabet.projectParallelLeft_wellFormed
            (right := right.alphabet)
            hWF.2.2.1.alphabet_wellFormed hAlphaWF hTargetHidden
          have hRightAWF := PactTypeAlphabet.projectParallelChild_wellFormed
            (target := alphabet) (interface := interface)
            hWF.2.2.2.alphabet_wellFormed
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

/-- What one conjunctive-offer branch still needs from the alphabet it is
handed once the earlier branches have taken their parts: its head action, and
everything its continuation can still observe. -/
def BranchAlphabetCarried (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) : Prop :=
  branch.1 ∈ alphabet.actions ∧ branch.2.AlphabetWellFormed ∧
    PactTypeAlphabet.Subalphabet alphabet branch.2.alphabet ∧
    PactType.MessageActions branch.2 ∩ branch.2.alphabet.actions ⊆
      alphabet.actions ∧
    PactType.ProgressIds branch.2 ⊆ alphabet.progress ∧
    PactType.FairChoiceIds branch.2 ⊆ alphabet.fair

/-- A carried branch may be reannotated to its own part of the alphabet: that
part is exactly the head action together with the continuation's actions. -/
theorem BranchAlphabetCarried.reannotationSafe_branchPart
    {alphabet : PactTypeAlphabet} (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hCarried : BranchAlphabetCarried alphabet branch) :
    PactType.ReannotationSafe (PactTypeAlphabet.branchPart alphabet branch) branch.2 := by
  obtain ⟨_, hBranchWF, hSub, hActions, hProgress, hFair⟩ := hCarried
  refine PactType.reannotationSafe_of_subalphabet branch.2 _ hBranchWF
    (PactTypeAlphabet.branchPart_wellFormed hAlphaWF branch)
    ⟨?_, ?_, ?_⟩ ?_ ?_ ?_
  · exact Finset.inter_subset_left.trans hSub.1
  · exact Finset.inter_subset_left.trans hSub.2.1
  · exact Finset.inter_subset_left.trans hSub.2.2
  · intro a ha
    simp only [PactTypeAlphabet.branchPart, Finset.mem_inter] at ha ⊢
    exact ⟨hActions (Finset.mem_inter.mpr ha),
      Finset.mem_union_right _ ha.1⟩
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hProgress hx, hx⟩
  · intro x hx
    exact Finset.mem_inter.mpr ⟨hFair hx, hx⟩

/-- A carried branch may equally be reannotated to the whole alphabet it was
handed, which is the case of a single remaining branch. -/
theorem BranchAlphabetCarried.reannotationSafe
    {alphabet : PactTypeAlphabet} (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hCarried : BranchAlphabetCarried alphabet branch) :
    PactType.ReannotationSafe alphabet branch.2 := by
  obtain ⟨_, hBranchWF, hSub, hActions, hProgress, hFair⟩ := hCarried
  exact PactType.reannotationSafe_of_subalphabet branch.2 _ hBranchWF hAlphaWF hSub
    hActions hProgress hFair

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

/-- A branch keeps everything it needs after an earlier branch has taken its
own part of the alphabet, because the two branches use disjoint declarations. -/
theorem BranchAlphabetCarried.remove_branchPart
    {alphabet : PactTypeAlphabet} {branch other : BareMessage × PactType}
    (hCarried : BranchAlphabetCarried alphabet other)
    (hDisjoint : BranchDeclarationsDisjoint branch other) :
    BranchAlphabetCarried
      (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
      other := by
  obtain ⟨hAction, hBranchWF, hSub, hActions, hProgress, hFair⟩ := hCarried
  obtain ⟨hActionsDisjoint, hProgressDisjoint, hFairDisjoint⟩ := hDisjoint
  refine ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hAction
      hActionsDisjoint, hBranchWF, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (Finset.sdiff_subset).trans hSub.1
  · exact (Finset.sdiff_subset).trans hSub.2.1
  · exact (Finset.sdiff_subset).trans hSub.2.2
  · intro a ha
    simp only [PactTypeAlphabet.remove, PactTypeAlphabet.branchPart, Finset.mem_sdiff,
      Finset.mem_inter]
    refine ⟨hActions ha, fun hIn => ?_⟩
    exact hActionsDisjoint.forall_ne_finset hIn.2
      (Finset.mem_union_right _ (Finset.mem_inter.mp ha).1) rfl
  · intro x hx
    simp only [PactTypeAlphabet.remove, PactTypeAlphabet.branchPart, Finset.mem_sdiff,
      Finset.mem_inter]
    exact ⟨hProgress hx, fun hIn => hProgressDisjoint.forall_ne_finset hIn.2 hx rfl⟩
  · intro x hx
    simp only [PactTypeAlphabet.remove, PactTypeAlphabet.branchPart, Finset.mem_sdiff,
      Finset.mem_inter]
    exact ⟨hFair hx, fun hIn => hFairDisjoint.forall_ne_finset hIn.2 hx rfl⟩

theorem parallelTypeBranchesWithin_alphabet_wellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed) :
    ∀ branches : List (BareMessage × PactType),
      List.Pairwise BranchDeclarationsDisjoint branches →
      (∀ branch ∈ branches, BranchAlphabetCarried alphabet branch) →
      (parallelTypeBranchesWithin alphabet branches).AlphabetWellFormed
  | [], _, _ => by simp [parallelTypeBranchesWithin, PactType.AlphabetWellFormed, hAlphaWF]
  | [branch], _, hBranches => by
      have hHead := hBranches branch (by simp)
      exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
        (hHead.reannotationSafe hAlphaWF)
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
        PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet branch,
        singletonTypeXOfferAt_alphabetWellFormed
          (PactTypeAlphabet.branchPart alphabet branch) hLeftWF hHeadActionLeft hHead.2.1
          (hHead.reannotationSafe_branchPart hAlphaWF),
        parallelTypeBranchesWithin_alphabet_wellFormed
          (PactTypeAlphabet.remove alphabet (PactTypeAlphabet.branchPart alphabet branch))
          hRightWF (next :: rest) hTailPairwise
          (fun item hItem =>
            (hBranches item (by simp [hItem])).remove_branchPart
              (hHeadDisjoint item hItem))⟩

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
      List.Pairwise BranchDeclarationsDisjoint branches →
      (∀ branch ∈ branches, BranchAlphabetCarried alphabet branch) →
      PactType.AlphabetWellFormed
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [], _, _ => by
      simp [parallelTypeBranchesSelectingWithin, PactType.AlphabetWellFormed, hAlphaWF]
  | [branch], _, hBranches => by
      have hHead := hBranches branch (by simp)
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
        exact selectedTypeBranchAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
          (hHead.reannotationSafe hAlphaWF)
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
        exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hHead.1 hHead.2.1
          (hHead.reannotationSafe hAlphaWF)
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
          BranchAlphabetCarried (PactTypeAlphabet.remove alphabet
            (PactTypeAlphabet.branchPart alphabet branch)) item :=
        fun item hItem =>
          (hBranches item (by simp [hItem])).remove_branchPart
            (hHeadDisjoint item hItem)
      have hCompatible :=
        PactTypeAlphabet.branchPart_remove_parallelCompatible alphabet branch
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
            (hHead.reannotationSafe_branchPart hAlphaWF),
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
            (hHead.reannotationSafe_branchPart hAlphaWF),
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

/-- A branch of a well-formed offer is carried by the offer's own alphabet:
the branch body is annotated with that alphabet, so every declaration it can
still observe is already there. -/
theorem branchAlphabetCarried_of_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    {branch : BareMessage × PactType} (hMem : branch ∈ branches) :
    BranchAlphabetCarried alphabet branch := by
  have hAlphaEq : branch.2.alphabet = alphabet :=
    PactType.branch_alphabet_eq_of_mem hBranches hMem
  have hBranchWF : branch.2.AlphabetWellFormed :=
    branch_body_alphabetWellFormed_of_mem hBranches (branchType := branch.2) (by simpa using hMem)
  refine ⟨branch_action_mem_fixedAlphabet_of_mem hBranches
      (branchType := branch.2) (by simpa using hMem), hBranchWF,
    ⟨by rw [hAlphaEq], by rw [hAlphaEq], by rw [hAlphaEq]⟩,
    by rw [hAlphaEq]; exact Finset.inter_subset_right, ?_, ?_⟩
  · rw [← hAlphaEq]
    exact PactType.progressIds_subset_alphabet branch.2 hBranchWF
  · rw [← hAlphaEq]
    exact PactType.fairChoiceIds_subset_alphabet branch.2 hBranchWF

theorem parallelTypeBranchesSelecting_alphabet_wellFormed
    {alphabet : PactTypeAlphabet} (hAlphaWF : alphabet.WellFormed)
    {selected : BareMessage × PactType} {branches : List (BareMessage × PactType)}
    (hSelected : selected ∈ branches)
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hPairwise : List.Pairwise BranchDeclarationsDisjoint branches) :
    (parallelTypeBranchesSelecting selected branches).alphabet = alphabet ∧
      (parallelTypeBranchesSelecting selected branches).AlphabetWellFormed := by
  cases branches with
  | nil => cases hSelected
  | cons branch rest =>
      have hFirstAlphabet : branch.2.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem hBranches (by simp)
      simp only [parallelTypeBranchesSelecting, hFirstAlphabet]
      refine ⟨parallelTypeBranchesSelectingWithin_alphabet alphabet selected (branch :: rest), ?_⟩
      exact parallelTypeBranchesSelectingWithin_alphabet_wellFormed alphabet hAlphaWF selected
        (branch :: rest) hPairwise
        (fun item hItem => branchAlphabetCarried_of_mem hBranches hItem)

/-- Every residual represented by a compiled state retains the fixed alphabet
of the source type.  The proof follows the structural relation clauses; the
fuel measure is needed for generated conjunctive-offer children. -/
theorem relationMembership_alphabet_eq
     :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.AlphabetCoherent →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.alphabet = source.alphabet := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hCoherent hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp [PactType.alphabet]
      | var alphabet name =>
          rw [(relationMembership_var_cases alphabet name hRelated).1]
      | choice alphabet left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_choice_cases alphabet left right
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
          rcases relationMembership_fairChoice_cases alphabet bid left
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
          rcases relationMembership_seq_cases alphabet left right
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
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, _, _, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            simp [PactType.alphabet]
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, _, _⟩
            injection hEntry with hResidual _
            rw [hResidual, PactType.reannotate_alphabet]
            simp [PactType.alphabet]
          · rcases hSurvR with ⟨q2, residualRight, hEntry, _, _⟩
            injection hEntry with hResidual _
            rw [hResidual, PactType.reannotate_alphabet]
            simp [PactType.alphabet]
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.alphabet]
      | recur alphabet name body =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_recur_cases alphabet name body
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
          rcases relationMembership_xoffer_cases alphabet elseType
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
          rcases relationMembership_offer_cases alphabet elseType
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

/-- Substituting an alphabet-matching replacement for a variable occurring only
in tail position preserves alphabet well-formedness: below a `.par`, where the
children's alphabets differ from the parent's, the variable cannot occur. -/
theorem PactType.replaceVar_alphabetWellFormed (name : String)
    {replacement : PactType} (hReplacementWF : replacement.AlphabetWellFormed) :
    ∀ processType : PactType, processType.AlphabetWellFormed →
      replacement.alphabet = processType.alphabet →
      processType.TailOccurrences name True →
      (processType.replaceVar name replacement).AlphabetWellFormed := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (alphabet : PactTypeAlphabet)
          (branches : List (BareMessage × PactType)), sizeOf branches < n →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          replacement.alphabet = alphabet →
          PactType.TailBranchOccurrences name True branches →
          PactType.BranchesAlphabetWellFormed alphabet
            (PactType.replaceBranches branches name replacement) := by
        intro alphabet branches hBranchesSize hWF hAlphabet hTail
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.BranchesAlphabetWellFormed]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BranchesAlphabetWellFormed] at hWF
            simp only [PactType.TailBranchOccurrences] at hTail
            simp only [PactType.replaceBranches,
              PactType.BranchesAlphabetWellFormed]
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
            have hBranchAlphabet : replacement.alphabet = branchType.alphabet :=
              hAlphabet.trans hWF.2.1.symm
            exact ⟨hWF.1,
              (PactType.replaceVar_alphabet_eq_of_replacement branchType name
                hBranchAlphabet).trans hWF.2.1,
              ih (sizeOf branchType) hBranchSize branchType rfl hWF.2.2.1
                hBranchAlphabet hTail.1,
              restIH hRestSize hWF.2.2.2 hTail.2⟩
      intro hWF hAlphabet hTail
      cases processType with
      | message alphabet msg dir | progress alphabet pid | tock alphabet
      | skip alphabet =>
          simpa [PactType.replaceVar] using hWF
      | var alphabet other =>
          by_cases hName : name = other
          · subst other
            simpa [PactType.replaceVar, PactType.alphabet] using hReplacementWF
          · simpa [PactType.replaceVar, hName] using hWF
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          refine ⟨hWF.1, ?_, ?_,
            ih (sizeOf left) hLeftSize left rfl hWF.2.2.2.1
              (hAlphabet.trans hWF.2.1.symm) hTail.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2
              (hAlphabet.trans hWF.2.2.1.symm) hTail.2⟩
          · rw [PactType.replaceVar_alphabet_eq_of_replacement left name
              (hAlphabet.trans hWF.2.1.symm)]
            exact hWF.2.1
          · rw [PactType.replaceVar_alphabet_eq_of_replacement right name
              (hAlphabet.trans hWF.2.2.1.symm)]
            exact hWF.2.2.1
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          refine ⟨hWF.1, hWF.2.1, ?_, hWF.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2
              (hAlphabet.trans hWF.2.2.1.symm) hTail.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement right name
            (hAlphabet.trans hWF.2.2.1.symm)]
          exact hWF.2.2.1
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          refine ⟨hWF.1, hWF.2.1, ?_, ?_,
            ih (sizeOf left) hLeftSize left rfl hWF.2.2.2.2.1
              (hAlphabet.trans hWF.2.2.1.symm) hTail.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2.2
              (hAlphabet.trans hWF.2.2.2.1.symm)
                hTail.2⟩
          · rw [PactType.replaceVar_alphabet_eq_of_replacement left name
              (hAlphabet.trans hWF.2.2.1.symm)]
            exact hWF.2.2.1
          · rw [PactType.replaceVar_alphabet_eq_of_replacement right name
              (hAlphabet.trans hWF.2.2.2.1.symm)]
            exact hWF.2.2.2.1
      | par alphabet left right interface =>
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hWF
      | recur alphabet other body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          by_cases hName : name = other
          · simpa [PactType.replaceVar, hName, PactType.AlphabetWellFormed]
              using hWF
          · simp only [PactType.TailOccurrences, if_neg (Ne.symm hName)] at hTail
            simp only [PactType.replaceVar, if_neg hName,
              PactType.AlphabetWellFormed]
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            have hBodyAlphabet : replacement.alphabet = body.alphabet :=
              hAlphabet.trans hWF.2.1.symm
            refine ⟨hWF.1, ?_,
              ih (sizeOf body) hBodySize body rfl hWF.2.2 hBodyAlphabet hTail⟩
            rw [PactType.replaceVar_alphabet_eq_of_replacement body name
              hBodyAlphabet]
            exact hWF.2.1
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hElseAlphabet : replacement.alphabet = elseType.alphabet :=
            hAlphabet.trans hWF.2.1.symm
          refine ⟨hWF.1, ?_,
            ih (sizeOf elseType) hElseSize elseType rfl hWF.2.2.1 hElseAlphabet
              hTail.1,
            hBranches alphabet branches hBranchesSize hWF.2.2.2 hAlphabet
              hTail.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement elseType name
            hElseAlphabet]
          exact hWF.2.1
      | offer alphabet elseType branches =>
          -- Given this, now the branch bodies are non-tail, so inert.
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hElseAlphabet : replacement.alphabet = elseType.alphabet :=
            hAlphabet.trans hWF.2.1.symm
          refine ⟨hWF.1, ?_,
            ih (sizeOf elseType) hElseSize elseType rfl hWF.2.2.1 hElseAlphabet
              hTail.1, hWF.2.2.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement elseType name
            hElseAlphabet]
          exact hWF.2.1

/-- Branch bodies of a tail-recursive offer are themselves tail-recursive. -/
theorem tailRecursive_of_mem_branches
    {branches : List (BareMessage × PactType)}
    {branch : BareMessage × PactType}
    (hBranches : PactType.TailRecursiveBranches branches)
    (hMember : branch ∈ branches) : branch.2.TailRecursive := by
  induction branches with
  | nil => cases hMember
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.TailRecursiveBranches] at hBranches
      simp only [List.mem_cons] at hMember
      rcases hMember with hEq | hMem
      · cases hEq; exact hBranches.1
      · exact ih hBranches.2 hMem

/-- The residual of a compiled state keeps every tail-occurrence judgement of
its source.  The statement is parametric in the tail parameter because a
sequence's left child and a parallel's children carry the constant `False`. -/
theorem relationMembership_tailOccurrences  :
    ∀ (source residual : PactType) (state : TypeAutomatonState)
      (name : String) (tail : Prop),
      source.TailRecursive →
      source.TailOccurrences name tail →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.TailOccurrences name tail := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state name tail hTailRec hTail hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
          exact hTail
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hTail
          · rw [hFinal.1]; simp [PactType.TailOccurrences]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]; exact hTail
          · rw [hFinal.1]; simp [PactType.TailOccurrences]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hTail
          · rw [hFinal.1]; simp [PactType.TailOccurrences]
      | var alphabet other =>
          rw [(relationMembership_var_cases alphabet other hRelated).1]
          exact hTail
      | choice alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : left.TailOccurrences name tail ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTail
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              name tail hTailRec.1 hFields.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              name tail hTailRec.2 hFields.2 hRightRelated
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : left.TailOccurrences name tail ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTail
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              name tail hTailRec.1 hFields.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              name tail hTailRec.2 hFields.2 hRightRelated
      | seq alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name tail := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailOccurrences] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q name False hTailRec.1 hFields.1 hLeftRelated)
                hFields.2
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              name tail hTailRec.2 hFields.2 hRightRelated
      | par alphabet left right interface =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailOccurrences] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q1 name False hTailRec.1 hFields.1 hLeftRelated)
                (ih (typeCompilationFuel right) hRightFuel right rfl
                  rightResidual q2 name False hTailRec.2 hFields.2 hRightRelated)
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact PactType.tailOccurrences_mono name False.elim _
              (PactType.reannotate_tailOccurrences name residualLeft alphabet
                False (ih (typeCompilationFuel left) hLeftFuel left rfl
                  residualLeft q1 name False hTailRec.1 hFields.1 hLeftRelated))
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact PactType.tailOccurrences_mono name False.elim _
              (PactType.reannotate_tailOccurrences name residualRight alphabet
                False (ih (typeCompilationFuel right) hRightFuel right rfl
                  residualRight q2 name False hTailRec.2 hFields.2 hRightRelated))
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.TailOccurrences]
      | recur alphabet binder body =>
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_recur_cases alphabet binder body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTail
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            -- Given this, now we need to prove the copied body residual keeps
            -- the binder in tail position, so the backedge substitution is
            -- transported by `tailOccurrences_replaceVar`.
            have hBodyResidualBinder :
                bodyResidual.TailOccurrences binder True :=
              ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
                binder True hTailRec.2 hTailRec.1 hBodyRelated
            refine PactType.tailOccurrences_replaceVar name binder bodyResidual
              tail hTail hBodyResidualBinder ?_
            by_cases hBinder : binder = name
            · exact Or.inl hBinder
            · exact Or.inr (ih (typeCompilationFuel body) hBodyFuel body rfl
                bodyResidual q name tail hTailRec.2
                (by simpa only [PactType.TailOccurrences, if_neg hBinder]
                  using hTail) hBodyRelated)
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name tail branches := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTail
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q name tail hTailRec.1 hFields.1 hElseRelated
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
              residual q name tail
              (tailRecursive_of_mem_branches (branch := (action, branchType))
                hTailRec.2 hMember)
              (PactType.tailOccurrences_of_mem_branches name tail hFields.2
                hMember)
              hBranchRelated
      | offer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFields : elseType.TailOccurrences name tail ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTail
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q name tail hTailRec.1 hFields.1 hElseRelated
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hBranchFalse : ∀ branch ∈ branches,
                branch.2.TailOccurrences name False := fun _ hBranch =>
              PactType.tailOccurrences_of_mem_branches name False hFields.2
                hBranch
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting selected branches)
              rfl residual q name tail
              (parallelTypeBranchesSelecting_tailRecursive selected branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (parallelTypeBranchesSelecting_tailOccurrences name selected
                branches tail hBranchFalse (hBranchFalse selected hMember))
              hSelectedRelated

/-- Every residual represented by a compiled state is itself tail-recursive.
Tail-closedness supplies the side condition that the recursion backedge
substituted at a `recur` node has all its own variables in tail position. -/
theorem relationMembership_tailRecursive  :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.TailRecursive →
      source.TailClosed →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.TailRecursive ∧ residual.TailClosed := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hTailRec hClosed hRelated
      -- Given this, now we need to prove tail-closedness of the residual,
      -- which `relationMembership_tailOccurrences` supplies name by name.
      have hResidualClosed : ∀ (r : PactType) (s : TypeAutomatonState),
          relationMembership
            (buildRelationSet source (compileType source)) r s →
          r.TailClosed := by
        intro r s hr other
        exact relationMembership_tailOccurrences source r s other True
          hTailRec (hClosed other) hr
      refine ⟨?_, hResidualClosed residual state hRelated⟩
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
          exact hTailRec
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hTailRec
          · rw [hFinal.1]; simp [PactType.TailRecursive]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]; exact hTailRec
          · rw [hFinal.1]; simp [PactType.TailRecursive]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hTailRec
          · rw [hFinal.1]; simp [PactType.TailRecursive]
      | var alphabet other =>
          rw [(relationMembership_var_cases alphabet other hRelated).1]
          exact hTailRec
      | choice alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, left.TailOccurrences other True ∧
              right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => (hSplit other).1, fun other => (hSplit other).2⟩
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 hClosedFields.1 hLeftRelated).1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hClosedFields.2 hRightRelated).1
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, left.TailOccurrences other True ∧
              right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => (hSplit other).1, fun other => (hSplit other).2⟩
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 hClosedFields.1 hLeftRelated).1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hClosedFields.2 hRightRelated).1
      | seq alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, left.TailOccurrences other False ∧
              right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedLeft : left.TailClosed := fun other =>
            PactType.tailOccurrences_mono other False.elim left
              (hSplit other).1
          have hClosedRight : right.TailClosed := fun other =>
            (hSplit other).2
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailRecursive] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q hTailRec.1 hClosedLeft hLeftRelated).1
                hTailRec.2
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hClosedRight hRightRelated).1
      | par alphabet left right interface =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, left.TailOccurrences other False ∧
              right.TailOccurrences other False := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedFields : left.TailClosed ∧ right.TailClosed :=
            ⟨fun other => PactType.tailOccurrences_mono other False.elim left
              (hSplit other).1,
              fun other => PactType.tailOccurrences_mono other False.elim right
                (hSplit other).2⟩
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailRecursive] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q1 hTailRec.1 hClosedFields.1 hLeftRelated).1
                (ih (typeCompilationFuel right) hRightFuel right rfl
                  rightResidual q2 hTailRec.2 hClosedFields.2 hRightRelated).1
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact PactType.reannotate_tailRecursive residualLeft alphabet
              (ih (typeCompilationFuel left) hLeftFuel left rfl residualLeft q1
                hTailRec.1 hClosedFields.1 hLeftRelated).1
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact PactType.reannotate_tailRecursive residualRight alphabet
              (ih (typeCompilationFuel right) hRightFuel right rfl residualRight
                q2 hTailRec.2 hClosedFields.2 hRightRelated).1
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.TailRecursive]
      | recur alphabet binder body =>
          simp only [PactType.TailRecursive] at hTailRec
          rcases relationMembership_recur_cases alphabet binder body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyClosed : body.TailClosed := by
              intro other
              by_cases hBinder : binder = other
              · exact hBinder ▸ hTailRec.1
              · simpa only [PactType.TailOccurrences, if_neg hBinder] using
                  hClosed other
            have hBodyResidualRec : bodyResidual.TailRecursive :=
              (ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
                hTailRec.2 hBodyClosed hBodyRelated).1
            have hBodyResidualBinder :
                bodyResidual.TailOccurrences binder True :=
              relationMembership_tailOccurrences body
                bodyResidual q binder True hTailRec.2 hTailRec.1 hBodyRelated
            exact PactType.tailRecursive_replaceVar binder
              (by simpa only [PactType.TailRecursive] using hTailRec) hClosed
              bodyResidual hBodyResidualRec hBodyResidualBinder
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other True branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedElse : elseType.TailClosed := fun other =>
            (hSplit other).1
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 hClosedElse hElseRelated).1
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchClosed : branchType.TailClosed := fun other =>
              PactType.tailOccurrences_of_mem_branches other True
                (hSplit other).2 hMember
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
              residual q
              (tailRecursive_of_mem_branches (branch := (action, branchType))
                hTailRec.2 hMember)
              hBranchClosed hBranchRelated).1
      | offer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hSplit : ∀ other : String, elseType.TailOccurrences other True ∧
              PactType.TailBranchOccurrences other False branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedElse : elseType.TailClosed := fun other =>
            (hSplit other).1
          have hBranchFalse : ∀ (other : String), ∀ branch ∈ branches,
              branch.2.TailOccurrences other False := fun other _ hBranch =>
            PactType.tailOccurrences_of_mem_branches other False
              (hSplit other).2 hBranch
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 hClosedElse hElseRelated).1
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting selected branches)
              rfl residual q
              (parallelTypeBranchesSelecting_tailRecursive selected branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (fun other =>
                parallelTypeBranchesSelecting_tailOccurrences other selected
                  branches True (hBranchFalse other)
                  (hBranchFalse other selected hMember))
              hSelectedRelated).1

/-- Committing a conjunctive offer keeps the alphabet well-formed.  Unlike the
`AlphabetCoherent` counterpart this is not free: the generated product
reannotates each branch body to its own part of the offer alphabet, so it
needs the branch declarations to survive that partition. -/
theorem committedOffer_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (selected : BareMessage × PactType)
    (hOfferWF : (PactType.offer alphabet elseType branches).AlphabetWellFormed)
    (hPairwise : List.Pairwise BranchDeclarationsDisjoint branches)
    (hSelected : selected ∈ branches) :
    (parallelTypeBranchesSelecting selected branches).AlphabetWellFormed := by
  simp only [PactType.AlphabetWellFormed] at hOfferWF
  exact (parallelTypeBranchesSelecting_alphabet_wellFormed hOfferWF.1 hSelected
    hOfferWF.2.2.2 hPairwise).2

/-- Every branch of a reannotated list comes from a source branch. -/
theorem reannotateBranches_mem
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    {item : BareMessage × PactType}
    (hMem : item ∈ PactType.reannotateBranches alphabet branches) :
    ∃ source ∈ branches, item = (source.1, source.2.reannotate alphabet) := by
  induction branches with
  | nil => rw [PactType.reannotateBranches_nil] at hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      rw [PactType.reannotateBranches_cons, List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · exact ⟨(action, branchType), by simp, hEq⟩
      · obtain ⟨source, hSource, hEq⟩ := ih hTail
        exact ⟨source, List.mem_cons_of_mem _ hSource, hEq⟩

/-- Reannotation keeps branch heads and structural footprints, so it keeps
declaration-disjointness of a branch list. -/
theorem reannotateBranches_pairwise_branchDeclarationsDisjoint
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      List.Pairwise BranchDeclarationsDisjoint branches →
      List.Pairwise BranchDeclarationsDisjoint
        (PactType.reannotateBranches alphabet branches) := by
  intro branches
  induction branches with
  | nil => intro _; rw [PactType.reannotateBranches_nil]; exact List.Pairwise.nil
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      intro hPairwise
      rw [PactType.reannotateBranches_cons, List.pairwise_cons]
      rw [List.pairwise_cons] at hPairwise
      refine ⟨?_, ih hPairwise.2⟩
      intro other hOther
      obtain ⟨source, hSource, hEq⟩ := reannotateBranches_mem hOther
      subst hEq
      have hHead := hPairwise.1 source hSource
      exact ⟨by simpa using hHead.1, by simpa using hHead.2.1,
        by simpa using hHead.2.2⟩

theorem reannotate_offerBranchesDisjoint :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      processType.OfferBranchesDisjoint →
      (processType.reannotate alphabet).OfferBranchesDisjoint := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType)),
          sizeOf branches < n → ∀ branchAlphabet,
          PactType.OfferBranchesDisjointBranches branches →
          PactType.OfferBranchesDisjointBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches hBranchesSize branchAlphabet hDisjoint
        induction branches with
        | nil =>
            rw [PactType.reannotateBranches_nil]
            simp [PactType.OfferBranchesDisjointBranches]
        | cons head tail restIH =>
            rcases head with ⟨action, branchType⟩
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint ⊢
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
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet
              hDisjoint.1, restIH hTailSize hDisjoint.2⟩
      intro alphabet hDisjoint
      cases processType with
      | message a m d | progress a p | tock a | skip a | var a _ =>
          simp [PactType.reannotate, PactType.OfferBranchesDisjoint]
      | choice a l r | seq a l r | fairChoice a b l r =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl alphabet hDisjoint.1,
            ih (sizeOf r) hR r rfl alphabet hDisjoint.2⟩
      | par a l r i =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf l) hL l rfl _ hDisjoint.1,
            ih (sizeOf r) hR r rfl _ hDisjoint.2⟩
      | recur a name body =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          exact ih (sizeOf body) hB body rfl alphabet hDisjoint
      | xoffer a elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl alphabet hDisjoint.1,
            hBranches branches hBr alphabet hDisjoint.2⟩
      | offer a elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.reannotate, PactType.OfferBranchesDisjoint]
          have hE : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBr : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hE elseType rfl alphabet hDisjoint.1,
            reannotateBranches_pairwise_branchDeclarationsDisjoint alphabet
              branches hDisjoint.2.1,
            hBranches branches hBr alphabet hDisjoint.2.2⟩

/-- A generated singleton offer has a one-element branch list. -/
theorem singletonTypeXOfferAt_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.OfferBranchesDisjoint) :
    (singletonTypeXOfferAt alphabet branch).OfferBranchesDisjoint := by
  rcases branch with ⟨action, branchType⟩
  simp only [singletonTypeXOfferAt, PactType.OfferBranchesDisjoint,
    PactType.OfferBranchesDisjointBranches]
  exact ⟨trivial,
    reannotate_offerBranchesDisjoint branchType alphabet hBranch, trivial⟩

/-- A committed branch is a mandatory action followed by the continuation. -/
theorem selectedTypeBranchAt_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hBranch : branch.2.OfferBranchesDisjoint) :
    (selectedTypeBranchAt alphabet branch).OfferBranchesDisjoint := by
  rcases branch with ⟨action, branchType⟩
  simp only [selectedTypeBranchAt, PactType.OfferBranchesDisjoint]
  exact ⟨trivial, reannotate_offerBranchesDisjoint branchType alphabet hBranch⟩

/-- The generated branch product only introduces singleton offers. -/
theorem parallelTypeBranchesWithin_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      (parallelTypeBranchesWithin alphabet branches).OfferBranchesDisjoint
  | [], _ => by simp [parallelTypeBranchesWithin, PactType.OfferBranchesDisjoint]
  | [branch], hBranches =>
      singletonTypeXOfferAt_offerBranchesDisjoint alphabet branch
        (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      simp only [parallelTypeBranchesWithin, PactType.OfferBranchesDisjoint]
      exact ⟨singletonTypeXOfferAt_offerBranchesDisjoint _ branch
          (hBranches branch (by simp)),
        parallelTypeBranchesWithin_offerBranchesDisjoint _ (next :: rest)
          (fun item hItem => hBranches item (by simp [hItem]))⟩

/-- Committing one branch of the generated product keeps the property. -/
theorem parallelTypeBranchesSelectingWithin_offerBranchesDisjoint
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      (∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) →
      PactType.OfferBranchesDisjoint
        (parallelTypeBranchesSelectingWithin alphabet selected branches)
  | [], _ => by
      simp [parallelTypeBranchesSelectingWithin, PactType.OfferBranchesDisjoint]
  | [branch], hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected]
        exact selectedTypeBranchAt_offerBranchesDisjoint alphabet branch
          (hBranches branch (by simp))
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected]
        exact singletonTypeXOfferAt_offerBranchesDisjoint alphabet branch
          (hBranches branch (by simp))
  | branch :: next :: rest, hBranches => by
      by_cases hSelected : branch = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSelected,
          PactType.OfferBranchesDisjoint]
        exact ⟨selectedTypeBranchAt_offerBranchesDisjoint _ branch
            (hBranches branch (by simp)),
          parallelTypeBranchesWithin_offerBranchesDisjoint _ (next :: rest)
            (fun item hItem => hBranches item (by simp [hItem]))⟩
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSelected,
          PactType.OfferBranchesDisjoint]
        exact ⟨singletonTypeXOfferAt_offerBranchesDisjoint _ branch
            (hBranches branch (by simp)),
          parallelTypeBranchesSelectingWithin_offerBranchesDisjoint _ selected
            (next :: rest) (fun item hItem => hBranches item (by simp [hItem]))⟩

/-- Committing a conjunctive offer keeps offer-branch disjointness. -/
theorem parallelTypeBranchesSelecting_offerBranchesDisjoint
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint) :
    (parallelTypeBranchesSelecting selected branches).OfferBranchesDisjoint := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.OfferBranchesDisjoint]
  | cons branch rest =>
      exact parallelTypeBranchesSelectingWithin_offerBranchesDisjoint _ selected
        (branch :: rest) hBranches

/-- Branch bodies of an offer whose branches are disjoint inherit the
property. -/
theorem offerBranchesDisjoint_of_mem
    {branches : List (BareMessage × PactType)}
    (hDisjoint : PactType.OfferBranchesDisjointBranches branches)
    {action : BareMessage} {branchType : PactType}
    (hMem : (action, branchType) ∈ branches) :
    branchType.OfferBranchesDisjoint := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact hDisjoint.1
      · exact ih hDisjoint.2 hTail

/-- Substituting for a variable confined to tail positions preserves offer-branch
disjointness.  A conjunctive offer's branches are non-tail, so substitution is
inert there and cannot grow the declarations the pairwise condition constrains;
an exclusive offer's branches are tail positions but carry no such condition. -/
theorem PactType.replaceVar_offerBranchesDisjoint (name : String)
    {replacement : PactType}
    (hReplacement : replacement.OfferBranchesDisjoint) :
    ∀ processType : PactType, processType.OfferBranchesDisjoint →
      processType.TailOccurrences name True →
      (processType.replaceVar name replacement).OfferBranchesDisjoint := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.OfferBranchesDisjointBranches branches →
          PactType.TailBranchOccurrences name True branches →
          PactType.OfferBranchesDisjointBranches
            (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hDisjoint hTail
        induction branches with
        | nil =>
            simp [PactType.replaceBranches,
              PactType.OfferBranchesDisjointBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.OfferBranchesDisjointBranches] at hDisjoint
            simp only [PactType.TailBranchOccurrences] at hTail
            simp only [PactType.replaceBranches,
              PactType.OfferBranchesDisjointBranches]
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl hDisjoint.1
                hTail.1, restIH hRestSize hDisjoint.2 hTail.2⟩
      intro hDisjoint hTail
      cases processType with
      | message alphabet msg dir | progress alphabet pid | tock alphabet
      | skip alphabet =>
          simp [PactType.replaceVar, PactType.OfferBranchesDisjoint]
      | var alphabet other =>
          by_cases hName : name = other
          · simpa [PactType.replaceVar, hName] using hReplacement
          · simp [PactType.replaceVar, hName, PactType.OfferBranchesDisjoint]
      | choice alphabet left right | fairChoice alphabet bid left right =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.OfferBranchesDisjoint]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize left rfl hDisjoint.1 hTail.1,
            ih (sizeOf right) hRightSize right rfl hDisjoint.2 hTail.2⟩
      | seq alphabet left right =>
          -- Given this, now the left operand is non-tail, so inert.
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.OfferBranchesDisjoint]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨hDisjoint.1,
            ih (sizeOf right) hRightSize right rfl hDisjoint.2 hTail.2⟩
      | par alphabet left right interface =>
          -- Given this, now both children are non-tail, so inert.
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hDisjoint
      | recur alphabet other body =>
          by_cases hName : name = other
          · simpa [PactType.replaceVar, hName] using hDisjoint
          · simp only [PactType.OfferBranchesDisjoint] at hDisjoint
            simp only [PactType.TailOccurrences, if_neg (Ne.symm hName)] at hTail
            simp only [PactType.replaceVar, if_neg hName,
              PactType.OfferBranchesDisjoint]
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize body rfl hDisjoint hTail
      | xoffer alphabet elseType branches =>
          -- Given this, now the branches carry no pairwise condition, so the
          -- substituted bodies only need the recursive hypothesis.
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.OfferBranchesDisjoint]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hDisjoint.1 hTail.1,
            hBranches branches hBranchesSize hDisjoint.2 hTail.2⟩
      | offer alphabet elseType branches =>
          -- Given this, now the branch bodies are non-tail, so inert, and the
          -- pairwise condition is carried over unchanged.
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar, PactType.OfferBranchesDisjoint]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hDisjoint.1 hTail.1,
            hDisjoint.2.1, hDisjoint.2.2⟩

/-- The offer-commit obligation of `relationMembership_alphabetWellFormed`,
carrying the branch-disjointness the generated product needs. -/
def CommittedOfferAlphabetWellFormed : Prop :=
  ∀ (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (selected : BareMessage × PactType),
    (PactType.offer alphabet elseType branches).AlphabetWellFormed →
    List.Pairwise BranchDeclarationsDisjoint branches →
    selected ∈ branches →
    (parallelTypeBranchesSelecting selected branches).AlphabetWellFormed

/-- The offer-commit obligation is discharged by the branch-product
well-formedness theorem. -/
theorem committedOfferAlphabetWellFormed_holds :
    CommittedOfferAlphabetWellFormed :=
  committedOffer_alphabetWellFormed

/-- Every residual represented by a compiled state is alphabet-well-formed
whenever the source type is.  Tail recursion is needed because a recursion
variable below a `.par` would be substituted with a type carrying the wrong
alphabet. -/
theorem relationMembership_alphabetWellFormed
     (hCommitted : CommittedOfferAlphabetWellFormed) :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.AlphabetWellFormed →
      source.TailRecursive →
      source.OfferBranchesDisjoint →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.AlphabetWellFormed := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hWF hTailRec hDisjoint hRelated
      have hCoherent := PactType.alphabetCoherent_of_wellFormed source hWF
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
          exact hWF
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hWF
          · rw [hFinal.1]
            simp only [PactType.AlphabetWellFormed] at hWF ⊢
            exact hWF.1
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]; exact hWF
          · rw [hFinal.1]
            simpa [PactType.AlphabetWellFormed] using hWF
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hWF
          · rw [hFinal.1]
            simp only [PactType.AlphabetWellFormed] at hWF ⊢
            exact hWF.1
      | var alphabet name =>
          rw [(relationMembership_var_cases alphabet name hRelated).1]
          exact hWF
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hWF.2.2.2.1 hTailRec.1 hDisjoint.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hWF.2.2.2.2 hTailRec.2 hDisjoint.2 hRightRelated
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hWF.2.2.2.2.1 hTailRec.1 hDisjoint.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hWF.2.2.2.2.2 hTailRec.2 hDisjoint.2 hRightRelated
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hLeftResidualWF := ih (typeCompilationFuel left) hLeftFuel left
              rfl leftResidual q hWF.2.2.2.1 hTailRec.1 hDisjoint.1 hLeftRelated
            have hLeftResidualAlphabet :=
              relationMembership_alphabet_eq left leftResidual q
                (PactType.alphabetCoherent_of_wellFormed left hWF.2.2.2.1)
                hLeftRelated
            simp only [PactType.AlphabetWellFormed]
            exact ⟨hWF.1, hLeftResidualAlphabet.trans hWF.2.1, hWF.2.2.1,
              hLeftResidualWF, hWF.2.2.2.2⟩
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hWF.2.2.2.2 hTailRec.2 hDisjoint.2 hRightRelated
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hLeftAlphabet := relationMembership_alphabet_eq left
              leftResidual q1
              (PactType.alphabetCoherent_of_wellFormed left hWF.2.2.1)
              hLeftRelated
            have hRightAlphabet := relationMembership_alphabet_eq right
              rightResidual q2
              (PactType.alphabetCoherent_of_wellFormed right hWF.2.2.2)
              hRightRelated
            simp only [PactType.AlphabetWellFormed]
            refine ⟨hWF.1, ?_,
              ih (typeCompilationFuel left) hLeftFuel left rfl leftResidual q1
                hWF.2.2.1 hTailRec.1 hDisjoint.1 hLeftRelated,
              ih (typeCompilationFuel right) hRightFuel right rfl rightResidual q2
                hWF.2.2.2 hTailRec.2 hDisjoint.2 hRightRelated⟩
            rw [hLeftAlphabet, hRightAlphabet]
            exact hWF.2.1
          -- Survivor residuals carry the parent alphabet, which `mergeHidden`
          -- strips of interface actions the residual may still mention.
          · sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
          · sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
          · injection hFinal with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF.1
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_recur_cases alphabet name body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyResidualWF := ih (typeCompilationFuel body) hBodyFuel body
              rfl bodyResidual q hWF.2.2 hTailRec.2 hDisjoint hBodyRelated
            have hBodyResidualAlphabet :=
              relationMembership_alphabet_eq body bodyResidual q
                (PactType.alphabetCoherent_of_wellFormed body hWF.2.2)
                hBodyRelated
            have hBodyResidualTail :
                bodyResidual.TailOccurrences name True :=
              relationMembership_tailOccurrences body bodyResidual q
                name True hTailRec.2 hTailRec.1 hBodyRelated
            refine PactType.replaceVar_alphabetWellFormed name ?_ bodyResidual
              hBodyResidualWF ?_ hBodyResidualTail
            · simpa only [PactType.AlphabetWellFormed] using
                ⟨hWF.1, hWF.2.1, hWF.2.2⟩
            · simpa [PactType.alphabet] using
                (hBodyResidualAlphabet.trans hWF.2.1).symm
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hWF.2.2.1 hTailRec.1 hDisjoint.1 hElseRelated
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩

            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchWF := branch_body_alphabetWellFormed_of_mem hWF.2.2.2
              hMember
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
              residual q hBranchWF
              (tailRecursive_of_mem_branches (branch := (action, branchType))
                hTailRec.2 hMember)
              (offerBranchesDisjoint_of_mem hDisjoint.2 hMember) hBranchRelated
      | offer alphabet elseType branches =>
          have hOfferWF : (PactType.offer alphabet elseType branches
            : PactType).AlphabetWellFormed := hWF
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.AlphabetWellFormed] using hWF
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hWF.2.2.1 hTailRec.1 hDisjoint.1 hElseRelated
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting selected branches)
              rfl residual q
              (hCommitted alphabet elseType branches selected hOfferWF
                hDisjoint.2.1 hMember)
              (parallelTypeBranchesSelecting_tailRecursive selected branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (parallelTypeBranchesSelecting_offerBranchesDisjoint selected branches
                (fun branch hBranch =>
                  offerBranchesDisjoint_of_mem (action := branch.1)
                    hDisjoint.2.2 (by simpa using hBranch)))
              hSelectedRelated

/-- Every residual represented by a compiled state keeps offer-branch
disjointness.  Tail recursion is what makes the unfolding case go through: the
recursion variable occurs only in tail positions, where substitution cannot
grow a conjunctive offer's branch declarations. -/
theorem relationMembership_offerBranchesDisjoint  :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.TailRecursive →
      source.OfferBranchesDisjoint →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.OfferBranchesDisjoint := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hTailRec hDisjoint hRelated
      cases source with
      | skip alphabet =>
          rw [(relationMembership_skip_cases alphabet hRelated).1]
          exact hDisjoint
      | message alphabet msg dir =>
          rcases relationMembership_message_cases alphabet msg dir
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hDisjoint
          · rw [hFinal.1]; simp [PactType.OfferBranchesDisjoint]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]; exact hDisjoint
          · rw [hFinal.1]; simp [PactType.OfferBranchesDisjoint]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]; exact hDisjoint
          · rw [hFinal.1]; simp [PactType.OfferBranchesDisjoint]
      | var alphabet name =>
          rw [(relationMembership_var_cases alphabet name hRelated).1]
          exact hDisjoint
      | choice alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.OfferBranchesDisjoint] using hDisjoint
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 hDisjoint.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hDisjoint.2 hRightRelated
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.OfferBranchesDisjoint] using hDisjoint
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 hDisjoint.1 hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hDisjoint.2 hRightRelated
      | seq alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simp only [PactType.OfferBranchesDisjoint]
            exact ⟨ih (typeCompilationFuel left) hLeftFuel left rfl leftResidual
              q hTailRec.1 hDisjoint.1 hLeftRelated, hDisjoint.2⟩
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 hDisjoint.2 hRightRelated
      | par alphabet left right interface =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simp only [PactType.OfferBranchesDisjoint]
            exact ⟨ih (typeCompilationFuel left) hLeftFuel left rfl leftResidual
                q1 hTailRec.1 hDisjoint.1 hLeftRelated,
              ih (typeCompilationFuel right) hRightFuel right rfl rightResidual
                q2 hTailRec.2 hDisjoint.2 hRightRelated⟩
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact reannotate_offerBranchesDisjoint residualLeft alphabet
              (ih (typeCompilationFuel left) hLeftFuel left rfl residualLeft q1
                hTailRec.1 hDisjoint.1 hLeftRelated)
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact reannotate_offerBranchesDisjoint residualRight alphabet
              (ih (typeCompilationFuel right) hRightFuel right rfl residualRight
                q2 hTailRec.2 hDisjoint.2 hRightRelated)
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.OfferBranchesDisjoint]
      | recur alphabet name body =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_recur_cases alphabet name body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.OfferBranchesDisjoint] using hDisjoint
          · -- Given this, now the unfolded residual substitutes the whole binder
            -- into the body residual, whose recursion variable stays in tail
            -- position.
            rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyResidualDisjoint := ih (typeCompilationFuel body) hBodyFuel
              body rfl bodyResidual q hTailRec.2 hDisjoint hBodyRelated
            have hBodyResidualTail :
                bodyResidual.TailOccurrences name True :=
              relationMembership_tailOccurrences body bodyResidual q
                name True hTailRec.2 hTailRec.1 hBodyRelated
            exact PactType.replaceVar_offerBranchesDisjoint name
              (by simpa only [PactType.OfferBranchesDisjoint] using hDisjoint)
              bodyResidual hBodyResidualDisjoint hBodyResidualTail
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.OfferBranchesDisjoint] using hDisjoint
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 hDisjoint.1 hElseRelated
          · rcases hBranch with ⟨i, action, branchType, q, hGet, _,
              hBranchRelated⟩
            have hMember : (action, branchType) ∈ branches :=
              List.mem_of_getElem? hGet
            have hBranchFuel : typeCompilationFuel branchType < n := by
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches := by
                simpa using typeCompilationFuel_le_typeBranchCompilationFuel
                  branches (action, branchType) hMember
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel branchType) hBranchFuel branchType rfl
              residual q
              (tailRecursive_of_mem_branches (branch := (action, branchType))
                hTailRec.2 hMember)
              (offerBranchesDisjoint_of_mem hDisjoint.2 hMember) hBranchRelated
      | offer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa [PactType.OfferBranchesDisjoint] using hDisjoint
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 hDisjoint.1 hElseRelated
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting selected branches)
              rfl residual q
              (parallelTypeBranchesSelecting_tailRecursive selected branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (parallelTypeBranchesSelecting_offerBranchesDisjoint selected
                branches
                (fun branch hBranch =>
                  offerBranchesDisjoint_of_mem (action := branch.1)
                    hDisjoint.2.2 (by simpa using hBranch)))
              hSelectedRelated

/-- The part of admissibility that survives taking a step: what a residual
needs to carry so that the parallel case can still bound its offers and the
recursion case can still unfold its binder. -/
def PactType.ResidualInvariant (processType : PactType) : Prop :=
  processType.AlphabetWellFormed ∧ processType.TailRecursive ∧
    processType.TailClosed ∧ processType.OfferBranchesDisjoint

/-- Every residual represented by a compiled state satisfies the residual
invariant whenever the source does. -/
theorem relationMembership_residualInvariant
    (source residual : PactType) (state : TypeAutomatonState)
    (hSource : source.ResidualInvariant)
    (hRelated :
      relationMembership (buildRelationSet source (compileType source))
        residual state) :
    residual.ResidualInvariant :=
  have hTail := relationMembership_tailRecursive source residual state
    hSource.2.1 hSource.2.2.1 hRelated
  ⟨relationMembership_alphabetWellFormed
      committedOfferAlphabetWellFormed_holds source residual state hSource.1
      hSource.2.1 hSource.2.2.2 hRelated,
    hTail.1, hTail.2,
    relationMembership_offerBranchesDisjoint source residual state
      hSource.2.1 hSource.2.2.2 hRelated⟩

/-- A semantic type step keeps its target alphabet-well-formed.  Tail
recursion is needed for the unfolding rule, whose target substitutes a
recursion variable, and offer-branch disjointness for the committed branch
product. -/
theorem TypeTransition.preserves_alphabetWellFormed
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    source.AlphabetWellFormed → source.TailRecursive →
      source.OfferBranchesDisjoint → target.AlphabetWellFormed := by
  induction transition with
  | action env alphabet msg dir conditions =>
      intro hWF _ _
      simpa [PactType.AlphabetWellFormed] using
        (by simpa [PactType.AlphabetWellFormed] using hWF : alphabet.WellFormed ∧ _).1
  | action_wait env alphabet msg dir conditions => intro hWF _ _; exact hWF
  | choice_left env alphabet left right hEnv hClock =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.2.1
  | choice_right env alphabet left right hEnv hClock =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.2.2
  | fair_left env alphabet bid left right hEnv hClock =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.2.2.1
  | fair_right env alphabet bid left right hEnv hClock =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.2.2.2
  | cycle env alphabet conditions =>
      intro hWF _ _; simpa [PactType.AlphabetWellFormed] using hWF
  | cycle_wait env alphabet conditions => intro hWF _ _; exact hWF
  | skip env alphabet conditions => intro hWF _ _; exact hWF
  | seq_fuse env alphabet skipAlphabet left right label childTransition ihLeft =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.2.2
  | progress env alphabet pid hEnv hClock =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      simpa [PactType.AlphabetWellFormed] using hWF.1
  | recur env alphabet name body hEnv hClock =>
      intro hWF hTailRec _
      have hWF' := hWF
      simp only [PactType.AlphabetWellFormed] at hWF'
      simp only [PactType.TailRecursive] at hTailRec
      exact PactType.replaceVar_alphabetWellFormed name hWF body hWF'.2.2
        (by simpa [PactType.alphabet] using hWF'.2.1.symm) hTailRec.1
  | seq env alphabet left left' right label childTransition hNotSkip ihLeft =>
      intro hWF hTailRec hDisjoint
      simp only [PactType.AlphabetWellFormed] at hWF ⊢
      simp only [PactType.TailRecursive] at hTailRec
      simp only [PactType.OfferBranchesDisjoint] at hDisjoint
      exact ⟨hWF.1, by
        rw [TypeTransition.preserves_alphabet hWF.2.2.2.1 childTransition]
        exact hWF.2.1, hWF.2.2.1,
        ihLeft hWF.2.2.2.1 hTailRec.1 hDisjoint.1, hWF.2.2.2.2⟩
  | xoffer_branch env alphabet elseType branches action processType conditions =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact branch_body_alphabetWellFormed_of_mem hWF.2.2.2 conditions.2.1

  | xoffer_else env alphabet elseType branches conditions =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.1
  | xoffer_wait env alphabet elseType branches conditions =>
      intro hWF _ _; exact hWF
  | offer_some env alphabet elseType branches enabled conditions =>
      intro hWF _ hDisjoint
      simp only [PactType.OfferBranchesDisjoint] at hDisjoint
      exact committedOffer_alphabetWellFormed alphabet elseType branches enabled
        hWF hDisjoint.2.1 conditions.2.1
  | offer_else env alphabet elseType branches conditions =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF
      exact hWF.2.2.1
  | offer_wait env alphabet elseType branches conditions =>
      intro hWF _ _; exact hWF
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ _
      leftTransition
      hLeftOffers rightTransition hRightOffers hNotBothSkip conditions ihLeft
      ihRight =>
      intro hWF hTailRec hDisjoint
      simp only [PactType.AlphabetWellFormed] at hWF ⊢
      simp only [PactType.TailRecursive] at hTailRec
      simp only [PactType.OfferBranchesDisjoint] at hDisjoint
      have hLeftAlphabet :=
        TypeTransition.preserves_alphabet hWF.2.2.1 leftTransition
      have hRightAlphabet :=
        TypeTransition.preserves_alphabet hWF.2.2.2 rightTransition
      exact ⟨hWF.1, by rw [hLeftAlphabet, hRightAlphabet]; exact hWF.2.1,
        ihLeft hWF.2.2.1 hTailRec.1 hDisjoint.1,
        ihRight hWF.2.2.2 hTailRec.2 hDisjoint.2⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture leftTransition
      hLeftOffers rightTransition hRightOffers conditions ihLeft ihRight =>
      intro hWF _ _
      simp only [PactType.AlphabetWellFormed] at hWF ⊢
      exact hWF.1
  -- Unlike `par_fuse`, whose target is `.skip`, the survivor targets keep the
  -- residual and re-stamp it with the parent alphabet.
  | left_complete outer rightEnv interface left right right' rightLabel
      rightCurrent rightFuture hLeftSkip _ rightTransition hRightOffers hNotSkip
      hRightCurrent
      hRightFuture hLocal hOuterWF ihRight =>
      intro hWF hTailRec hDisjoint
      sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
  | right_complete outer leftEnv interface left left' right leftLabel
      leftCurrent leftFuture hRightSkip _ leftTransition hLeftOffers hNotSkip
      hLeftCurrent hLeftFuture hLocal hOuterWF ihLeft =>
      intro hWF hTailRec hDisjoint
      sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`

/-- Offer-level form of `TypeTransition.preserves_alphabetWellFormed`. -/
theorem DecoratedTypeTransition.preserves_alphabetWellFormed
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hSource : source.AlphabetWellFormed) (hTailRec : source.TailRecursive)
    (hDisjoint : source.OfferBranchesDisjoint)
    (transition : DecoratedTypeTransition env source label offers target) :
    target.AlphabetWellFormed :=
  TypeTransition.preserves_alphabetWellFormed transition.1 hSource hTailRec
    hDisjoint

end

end Pact
