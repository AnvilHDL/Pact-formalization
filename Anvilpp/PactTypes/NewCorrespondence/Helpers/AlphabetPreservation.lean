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


/-- One alphabet declares no more than another. -/
def PactTypeAlphabet.Subalphabet (small large : PactTypeAlphabet) : Prop :=
  small.actions ⊆ large.actions

/-- The projection keeps the child's interface actions and adds the whole new
parent alphabet. -/
theorem PactTypeAlphabet.projectParallel_actions
    (target child : PactTypeAlphabet) (interface : Interface) :
    (projectParallel target child interface).actions =
      (child.actions.filter fun action => action.1 ∈ interface) ∪
        target.actions := rfl

/-- An empty interface hides nothing. -/
theorem PactTypeAlphabet.hideInterface_empty_actions
    (alphabet : PactTypeAlphabet) :
    (PactTypeAlphabet.hideInterface alphabet ∅).actions = alphabet.actions := by
  simp [PactTypeAlphabet.hideInterface]

/-- One polarity per message is inherited by every smaller alphabet. -/
theorem PactTypeAlphabet.wellFormed_of_subset {small large : PactTypeAlphabet}
    (hSub : small.actions ⊆ large.actions) (hLarge : large.WellFormed) :
    small.WellFormed :=
  fun msg h => hLarge msg ⟨hSub h.1, hSub h.2⟩

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

/-- The projection mixes the child's interface actions with the target's own.
A target that declares no interface action keeps the two halves apart. -/
theorem PactTypeAlphabet.projectParallel_wellFormed
    {target child : PactTypeAlphabet} {interface : Interface}
    (hChildWF : child.WellFormed) (hTargetWF : target.WellFormed)
    (hTargetHidden : ∀ action ∈ target.actions, action.1 ∉ interface) :
    (projectParallel target child interface).WellFormed := by
  intro msg ⟨hSend, hRecv⟩
  rw [projectParallel_actions] at hSend hRecv
  simp only [Finset.mem_union, Finset.mem_filter] at hSend hRecv
  rcases hSend with ⟨hSendC, hSendI⟩ | hSendT <;>
    rcases hRecv with ⟨hRecvC, hRecvI⟩ | hRecvT
  · exact hChildWF msg ⟨hSendC, hRecvC⟩
  · exact hTargetHidden _ hRecvT hSendI
  · exact hTargetHidden _ hSendT hRecvI
  · exact hTargetWF msg ⟨hSendT, hRecvT⟩

/-- Splitting a target that declares no interface action gives two projected
children compatible with it: each keeps its own interface polarity, and hiding
the interface returns exactly the target. -/
theorem PactTypeAlphabet.projectParallel_compatible
    {parent left right target : PactTypeAlphabet} {interface : Interface}
    (hCompatible : ParallelCompatible parent left right interface)
    (hTargetHidden : ∀ action ∈ target.actions, action.1 ∉ interface) :
    ParallelCompatible target (projectParallel target left interface)
      (projectParallel target right interface) interface := by
  classical
  refine ⟨hTargetHidden, ?_, ?_, ?_⟩
  · intro msg hmsg
    rcases hCompatible.complementary msg hmsg with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hl, hmsg⟩),
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hmsg⟩)⟩
    · exact Or.inr ⟨Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hl, hmsg⟩),
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hmsg⟩)⟩
  · cases target with
    | mk targetActions =>
        simp only [hideInterface, projectParallel_actions]
        congr 1
        apply Finset.ext
        intro action
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hIn | hIn, hHidden⟩
          · exact absurd hIn.2 hHidden
          · exact hIn
        · intro hIn
          exact ⟨Or.inr hIn, hTargetHidden action hIn⟩
  · cases target with
    | mk targetActions =>
        simp only [hideInterface, projectParallel_actions]
        congr 1
        apply Finset.ext
        intro action
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hIn | hIn, hHidden⟩
          · exact absurd hIn.2 hHidden
          · exact hIn
        · intro hIn
          exact ⟨Or.inr hIn, hTargetHidden action hIn⟩


/-- Re-signing by a target that need not sit inside the type's own alphabet.
The target must declare none of the interfaces occurring in the type; that
invariant descends into both children of every `.par`. -/
theorem PactType.reannotate_alphabetWellFormed_avoiding :
    ∀ (processType : PactType) (target : PactTypeAlphabet),
      processType.AlphabetWellFormed → target.WellFormed →
      processType.InterfaceScoped →
      (∀ action ∈ target.actions,
        action.1 ∉ PactType.ParallelInterfaces processType) →
      (processType.reannotate target).AlphabetWellFormed := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hXBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ source target : PactTypeAlphabet,
          target.WellFormed →
          PactType.BranchesAlphabetWellFormed source branches →
          PactType.InterfaceScopedBranches branches →
          (∀ action ∈ target.actions,
            action.1 ∉ PactType.ParallelBranchInterfaces branches) →
          PactType.BranchesAlphabetWellFormed target
            (PactType.reannotateBranches target branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _ _ _
            rw [PactType.reannotateBranches_nil]
            simp [PactType.BranchesAlphabetWellFormed]
        | cons head tail restIH =>
            intro hSizeCons source target hTargetWF hWF hScoped hAvoid
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            simp only [PactType.InterfaceScopedBranches] at hScoped
            simp only [PactType.ParallelBranchInterfaces,
              Finset.mem_union] at hAvoid
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.BranchesAlphabetWellFormed] at hWF ⊢
            refine ⟨PactType.reannotate_alphabet target body, ?_, ?_⟩
            · exact ih (sizeOf body) hBodySize body rfl target hWF.2.1
                hTargetWF hScoped.1
                (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
            · exact restIH hTailSize source target hTargetWF hWF.2.2 hScoped.2
                (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      have hOBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (source target : PactTypeAlphabet)
            (seen : Finset BareMessage),
          target.WellFormed →
          PactType.OfferBranchesWellFormed source seen branches →
          PactType.InterfaceScopedBranches branches →
          (∀ action ∈ target.actions,
            action.1 ∉ PactType.ParallelBranchInterfaces branches) →
          PactType.OfferBranchesWellFormed target seen
            (PactType.reannotateOfferBranches target seen branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _ _ _ _
            rw [PactType.reannotateOfferBranches_nil]
            simp [PactType.OfferBranchesWellFormed]
        | cons head tail restIH =>
            intro hSizeCons source target seen hTargetWF hWF hScoped hAvoid
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            simp only [PactType.InterfaceScopedBranches] at hScoped
            simp only [PactType.ParallelBranchInterfaces,
              Finset.mem_union] at hAvoid
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.OfferBranchesWellFormed] at hWF ⊢
            refine ⟨PactType.reannotate_alphabet target body, ?_, ?_⟩
            · exact ih (sizeOf body) hBodySize body rfl target hWF.2.1
                hTargetWF hScoped.1
                (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
            · exact restIH hTailSize source target seen hTargetWF hWF.2.2
                hScoped.2 (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      intro target hWF hTargetWF hScoped hAvoid
      cases processType with
      | message a msg dir | progress a pid | tock a | skip a | var a name =>
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          exact hTargetWF
      | choice a left right | seq a left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hAvoid
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, PactType.reannotate_alphabet target left,
            PactType.reannotate_alphabet target right, ?_, ?_⟩
          · exact ih (sizeOf left) hLeftSize left rfl target hWF.2.2.2.1
              hTargetWF hScoped.1
              (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
          · exact ih (sizeOf right) hRightSize right rfl target hWF.2.2.2.2
              hTargetWF hScoped.2
              (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      | fairChoice a bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hAvoid
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, PactType.reannotate_alphabet target left,
            PactType.reannotate_alphabet target right, ?_, ?_⟩
          · exact ih (sizeOf left) hLeftSize left rfl target hWF.2.2.2.1
              hTargetWF hScoped.1
              (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
          · exact ih (sizeOf right) hRightSize right rfl target hWF.2.2.2.2
              hTargetWF hScoped.2
              (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      | recur a name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces] at hAvoid
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, PactType.reannotate_alphabet target body, ?_⟩
          exact ih (sizeOf body) hBodySize body rfl target hWF.2.2 hTargetWF
            hScoped hAvoid
      | xoffer a elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hAvoid
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, PactType.reannotate_alphabet target elseType, ?_, ?_⟩
          · exact ih (sizeOf elseType) hElseSize elseType rfl target hWF.2.2.1
              hTargetWF hScoped.1
              (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
          · exact hXBranches branches hBranchesSize a target hTargetWF
              hWF.2.2.2 hScoped.2
              (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      | offer a elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hAvoid
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, PactType.reannotate_alphabet target elseType, ?_, ?_⟩
          · exact ih (sizeOf elseType) hElseSize elseType rfl target hWF.2.2.1
              hTargetWF hScoped.1
              (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
          · exact hOBranches branches hBranchesSize a target ∅ hTargetWF
              hWF.2.2.2 hScoped.2
              (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      | par a left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.ParallelInterfaces, Finset.mem_union] at hAvoid
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLAlphaWF : left.alphabet.WellFormed :=
            PactType.AlphabetWellFormed.alphabet_wellFormed hWF.2.2.1
          have hRAlphaWF : right.alphabet.WellFormed :=
            PactType.AlphabetWellFormed.alphabet_wellFormed hWF.2.2.2
          have hTargetHidden : ∀ action ∈ target.actions,
              action.1 ∉ interface := fun act hAct hIn =>
            hAvoid act hAct (Or.inl (Or.inl hIn))
          -- The declaring interface is disjoint from every interface below it,
          -- so an interface action of a child avoids that child's own nested
          -- interfaces.
          have hInterfaceAvoid : ∀ msg ∈ interface,
              msg ∉ PactType.ParallelInterfaces left ∧
                msg ∉ PactType.ParallelInterfaces right := by
            intro msg hMsg
            have hNot := Finset.disjoint_left.mp hScoped.1 hMsg
            exact ⟨fun h => hNot (Finset.mem_union_left _ h),
              fun h => hNot (Finset.mem_union_right _ h)⟩
          have hCompat : PactTypeAlphabet.ParallelCompatible target
              (PactTypeAlphabet.projectParallel target left.alphabet interface)
              (PactTypeAlphabet.projectParallel target right.alphabet interface)
              interface :=
            PactTypeAlphabet.projectParallel_compatible hWF.2.1 hTargetHidden
          have hLTWF : (PactTypeAlphabet.projectParallel target left.alphabet
              interface).WellFormed :=
            PactTypeAlphabet.projectParallel_wellFormed hLAlphaWF hTargetWF
              hTargetHidden
          have hRTWF : (PactTypeAlphabet.projectParallel target right.alphabet
              interface).WellFormed :=
            PactTypeAlphabet.projectParallel_wellFormed hRAlphaWF hTargetWF
              hTargetHidden
          have hLeftAvoid : ∀ action ∈ (PactTypeAlphabet.projectParallel
              target left.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces left := by
            intro act hAct
            rw [PactTypeAlphabet.projectParallel_actions,
              Finset.mem_union] at hAct
            rcases hAct with hAct | hAct
            · exact (hInterfaceAvoid act.1 (Finset.mem_filter.mp hAct).2).1
            · exact fun h => hAvoid act hAct (Or.inl (Or.inr h))
          have hRightAvoid : ∀ action ∈ (PactTypeAlphabet.projectParallel
              target right.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces right := by
            intro act hAct
            rw [PactTypeAlphabet.projectParallel_actions,
              Finset.mem_union] at hAct
            rcases hAct with hAct | hAct
            · exact (hInterfaceAvoid act.1 (Finset.mem_filter.mp hAct).2).2
            · exact fun h => hAvoid act hAct (Or.inr h)
          simp only [PactType.reannotate, PactType.AlphabetWellFormed]
          refine ⟨hTargetWF, ?_, ?_, ?_⟩
          · rw [PactType.reannotate_alphabet, PactType.reannotate_alphabet]
            exact hCompat
          · exact ih (sizeOf left) hLeftSize left rfl _ hWF.2.2.1 hLTWF
              hScoped.2.1 hLeftAvoid
          · exact ih (sizeOf right) hRightSize right rfl _ hWF.2.2.2 hRTWF
              hScoped.2.2 hRightAvoid

/-- Re-signing renames no interface. -/
theorem PactType.reannotate_parallelInterfaces :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.ParallelInterfaces (processType.reannotate alphabet) =
        PactType.ParallelInterfaces processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.ParallelBranchInterfaces
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.ParallelBranchInterfaces branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.ParallelBranchInterfaces]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.ParallelBranchInterfaces,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.ParallelBranchInterfaces
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.ParallelBranchInterfaces branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.ParallelBranchInterfaces]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.ParallelBranchInterfaces,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.ParallelInterfaces]
      | progress a p => simp [PactType.reannotate, PactType.ParallelInterfaces]
      | tock a => simp [PactType.reannotate, PactType.ParallelInterfaces]
      | skip a => simp [PactType.reannotate, PactType.ParallelInterfaces]
      | var a name => simp [PactType.reannotate, PactType.ParallelInterfaces]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.ParallelInterfaces,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

theorem parallelTypeBranchesWithin_parallelInterfaces :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      PactType.ParallelInterfaces (parallelTypeBranchesWithin alphabet branches) =
        PactType.ParallelBranchInterfaces branches := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet
      simp [parallelTypeBranchesWithin, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet
      cases rest with
      | nil =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
            PactType.reannotate_parallelInterfaces]
      | cons next tail =>
          simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
            PactType.reannotate_parallelInterfaces,
            ih alphabet, Finset.union_assoc]

theorem parallelTypeBranchesSelectingWithin_parallelInterfaces
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      PactType.ParallelInterfaces
          (parallelTypeBranchesSelectingWithin alphabet selected branches) =
        PactType.ParallelBranchInterfaces branches := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet
      simp [parallelTypeBranchesSelectingWithin, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet
      cases rest with
      | nil =>
          by_cases hSel : (action, body) = selected
          · subst hSel
            simp [parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
              PactType.reannotate_parallelInterfaces]
          · simp [parallelTypeBranchesSelectingWithin, if_neg hSel,
              singletonTypeXOfferAt, PactType.ParallelInterfaces,
              PactType.ParallelBranchInterfaces,
              PactType.reannotate_parallelInterfaces]
      | cons next tail =>
          by_cases hSel : (action, body) = selected
          · subst hSel
            simp [parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
              PactType.reannotate_parallelInterfaces,
              parallelTypeBranchesWithin_parallelInterfaces (next :: tail)
                alphabet,
              Finset.union_assoc]
          · simp [parallelTypeBranchesSelectingWithin, if_neg hSel,
              singletonTypeXOfferAt, PactType.ParallelInterfaces,
              PactType.ParallelBranchInterfaces,
              PactType.reannotate_parallelInterfaces,
              ih alphabet, Finset.union_assoc]

/-- Branch-list form of `reannotate_parallelInterfaces`. -/
theorem PactType.parallelBranchInterfaces_reannotateBranches
    (target : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.ParallelBranchInterfaces
          (PactType.reannotateBranches target branches) =
        PactType.ParallelBranchInterfaces branches
  | [] => by rw [PactType.reannotateBranches_nil]
  | (action, body) :: rest => by
      rw [PactType.reannotateBranches_cons]
      simp only [PactType.ParallelBranchInterfaces,
        PactType.reannotate_parallelInterfaces,
        PactType.parallelBranchInterfaces_reannotateBranches target rest]

/-- Conjunctive-branch form of `reannotate_parallelInterfaces`. -/
theorem PactType.parallelBranchInterfaces_reannotateOfferBranches
    (target : PactTypeAlphabet) :
    ∀ (seen : Finset BareMessage) (branches : List (BareMessage × PactType)),
      PactType.ParallelBranchInterfaces
          (PactType.reannotateOfferBranches target seen branches) =
        PactType.ParallelBranchInterfaces branches
  | _, [] => by rw [PactType.reannotateOfferBranches_nil]
  | seen, (action, body) :: rest => by
      rw [PactType.reannotateOfferBranches_cons]
      simp only [PactType.ParallelBranchInterfaces,
        PactType.reannotate_parallelInterfaces,
        PactType.parallelBranchInterfaces_reannotateOfferBranches target seen
          rest]

/-- A target avoiding the interfaces below a type re-signs it into a type whose
alphabets still avoid the interfaces below them. -/
theorem PactType.reannotate_interfaceAlphabetScoped :
    ∀ (processType : PactType) (target : PactTypeAlphabet),
      processType.InterfaceAlphabetScoped →
      (∀ action ∈ target.actions,
        action.1 ∉ PactType.ParallelInterfaces processType) →
      (processType.reannotate target).InterfaceAlphabetScoped := by
  have hDisj : ∀ (target : PactTypeAlphabet) (blocked : Finset MessageId),
      (∀ action ∈ target.actions, action.1 ∉ blocked) →
      Disjoint (PactTypeAlphabet.messageIds target) blocked := by
    intro target blocked hBlocked
    refine Finset.disjoint_left.mpr ?_
    intro msg hMsg
    obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp hMsg
    exact hBlocked action hAction
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hXBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ target : PactTypeAlphabet,
          PactType.InterfaceAlphabetScopedBranches branches →
          (∀ action ∈ target.actions,
            action.1 ∉ PactType.ParallelBranchInterfaces branches) →
          PactType.InterfaceAlphabetScopedBranches
            (PactType.reannotateBranches target branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _
            rw [PactType.reannotateBranches_nil]
            simp [PactType.InterfaceAlphabetScopedBranches]
        | cons head tail restIH =>
            intro hSizeCons target hScoped hAvoid
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            simp only [PactType.InterfaceAlphabetScopedBranches] at hScoped
            simp only [PactType.ParallelBranchInterfaces,
              Finset.mem_union] at hAvoid
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.InterfaceAlphabetScopedBranches]
            exact ⟨ih (sizeOf body) hBodySize body rfl target hScoped.1
                (fun act hAct hIn => hAvoid act hAct (Or.inl hIn)),
              restIH hTailSize target hScoped.2
                (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))⟩
      have hOBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (target : PactTypeAlphabet)
            (seen : Finset BareMessage),
          PactType.InterfaceAlphabetScopedBranches branches →
          (∀ action ∈ target.actions,
            action.1 ∉ PactType.ParallelBranchInterfaces branches) →
          PactType.InterfaceAlphabetScopedBranches
            (PactType.reannotateOfferBranches target seen branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _ _ _
            rw [PactType.reannotateOfferBranches_nil]
            simp [PactType.InterfaceAlphabetScopedBranches]
        | cons head tail restIH =>
            intro hSizeCons target seen hScoped hAvoid
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            simp only [PactType.InterfaceAlphabetScopedBranches] at hScoped
            simp only [PactType.ParallelBranchInterfaces,
              Finset.mem_union] at hAvoid
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.InterfaceAlphabetScopedBranches]
            refine ⟨ih (sizeOf body) hBodySize body rfl target hScoped.1 ?_,
              restIH hTailSize target seen hScoped.2
                (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))⟩
            intro act hAct hIn
            exact hAvoid act hAct (Or.inl hIn)
      intro target hScoped hAvoid
      cases processType with
      | message a msg dir | progress a pid | tock a | skip a | var a name =>
          simp only [PactType.reannotate]
          simp only [PactType.InterfaceAlphabetScoped]
      | choice a left right | seq a left right | fairChoice a bid left right =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hUnion : ∀ action ∈ target.actions,
              action.1 ∉ PactType.ParallelInterfaces left ∪
                PactType.ParallelInterfaces right := by
            intro act hAct hIn
            exact hAvoid act hAct (by
              simp only [PactType.ParallelInterfaces]
              exact hIn)
          simp only [PactType.reannotate, PactType.InterfaceAlphabetScoped,
            PactType.reannotate_parallelInterfaces]
          refine ⟨hDisj target _ hUnion, ?_, ?_⟩
          · exact ih (sizeOf left) hLeftSize left rfl target hScoped.2.1
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_left _ hIn))
          · exact ih (sizeOf right) hRightSize right rfl target hScoped.2.2
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_right _ hIn))
      | recur a name body =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hBodyAvoid : ∀ action ∈ target.actions,
              action.1 ∉ PactType.ParallelInterfaces body := by
            intro act hAct hIn
            exact hAvoid act hAct (by
              simp only [PactType.ParallelInterfaces]
              exact hIn)
          simp only [PactType.reannotate, PactType.InterfaceAlphabetScoped,
            PactType.reannotate_parallelInterfaces]
          exact ⟨hDisj target _ hBodyAvoid,
            ih (sizeOf body) hBodySize body rfl target hScoped.2 hBodyAvoid⟩
      | xoffer a elseType branches =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hUnion : ∀ action ∈ target.actions,
              action.1 ∉ PactType.ParallelInterfaces elseType ∪
                PactType.ParallelBranchInterfaces branches := by
            intro act hAct hIn
            exact hAvoid act hAct (by
              simp only [PactType.ParallelInterfaces]
              exact hIn)
          simp only [PactType.reannotate, PactType.InterfaceAlphabetScoped,
            PactType.reannotate_parallelInterfaces,
            PactType.parallelBranchInterfaces_reannotateBranches]
          refine ⟨hDisj target _ hUnion, ?_, ?_⟩
          · exact ih (sizeOf elseType) hElseSize elseType rfl target hScoped.2.1
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_left _ hIn))
          · exact hXBranches branches hBranchesSize target hScoped.2.2
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_right _ hIn))
      | offer a elseType branches =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hUnion : ∀ action ∈ target.actions,
              action.1 ∉ PactType.ParallelInterfaces elseType ∪
                PactType.ParallelBranchInterfaces branches := by
            intro act hAct hIn
            exact hAvoid act hAct (by
              simp only [PactType.ParallelInterfaces]
              exact hIn)
          simp only [PactType.reannotate, PactType.InterfaceAlphabetScoped,
            PactType.reannotate_parallelInterfaces,
            PactType.parallelBranchInterfaces_reannotateOfferBranches]
          refine ⟨hDisj target _ hUnion, ?_, ?_⟩
          · exact ih (sizeOf elseType) hElseSize elseType rfl target hScoped.2.1
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_left _ hIn))
          · exact hOBranches branches hBranchesSize target ∅ hScoped.2.2
              (fun act hAct hIn =>
                hUnion act hAct (Finset.mem_union_right _ hIn))
      | par a left right interface =>
          simp only [PactType.InterfaceAlphabetScoped] at hScoped
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hUnion : ∀ action ∈ target.actions,
              action.1 ∉ interface ∪ PactType.ParallelInterfaces left ∪
                PactType.ParallelInterfaces right := by
            intro act hAct hIn
            exact hAvoid act hAct (by
              simp only [PactType.ParallelInterfaces]
              exact hIn)
          -- A projected child alphabet lies in the child's own alphabet or in
          -- the target, and both avoid that child's interfaces.
          have hLeftAvoid : ∀ action ∈ (PactTypeAlphabet.projectParallel
              target left.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces left := by
            intro act hAct
            rw [PactTypeAlphabet.projectParallel_actions,
              Finset.mem_union] at hAct
            rcases hAct with hAct | hAct
            · exact PactType.InterfaceAlphabetScoped.avoids hScoped.2.1 act
                (Finset.mem_filter.mp hAct).1
            · intro hIn
              exact hUnion act hAct
                (Finset.mem_union_left _ (Finset.mem_union_right _ hIn))
          have hRightAvoid : ∀ action ∈ (PactTypeAlphabet.projectParallel
              target right.alphabet interface).actions,
              action.1 ∉ PactType.ParallelInterfaces right := by
            intro act hAct
            rw [PactTypeAlphabet.projectParallel_actions,
              Finset.mem_union] at hAct
            rcases hAct with hAct | hAct
            · exact PactType.InterfaceAlphabetScoped.avoids hScoped.2.2 act
                (Finset.mem_filter.mp hAct).1
            · intro hIn
              exact hUnion act hAct (Finset.mem_union_right _ hIn)
          simp only [PactType.reannotate, PactType.InterfaceAlphabetScoped,
            PactType.reannotate_parallelInterfaces]
          refine ⟨hDisj target _ hUnion, ?_, ?_⟩
          · exact ih (sizeOf left) hLeftSize left rfl _ hScoped.2.1 hLeftAvoid
          · exact ih (sizeOf right) hRightSize right rfl _ hScoped.2.2
              hRightAvoid

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
      alphabet.actions

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
      rcases hMem with hEq | hTail
      · cases hEq
        exact hBranches.2.1
      · exact ih hBranches.2.2 hTail

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
  obtain ⟨hAction, hOtherWF, hSub, hActions⟩ := hCarried
  refine ⟨PactTypeAlphabet.mem_remove_branchPart_actions_of_disjoint hAction
      hDisjoint.1, hOtherWF, ?_, ?_⟩
  · intro action hMem
    simp only [PactTypeAlphabet.remove, Finset.mem_sdiff] at hMem
    exact hSub hMem.1
  · intro action hMem
    have hAlpha : action ∈ alphabet.actions := hActions hMem
    have hOwn : action ∈ PactType.MessageActions other.2 :=
      (Finset.mem_inter.mp hMem).1
    simp only [PactTypeAlphabet.remove, PactTypeAlphabet.branchPart,
      Finset.mem_sdiff, Finset.mem_inter]
    refine ⟨hAlpha, fun hTaken => ?_⟩
    exact hDisjoint.1.forall_ne_finset hTaken.2
      (Finset.mem_union_right _ hOwn) rfl

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

/-- Every residual represented by a state of a re-signed type carries the
signature it was re-signed with, and so does every residual of the conjunctive
children such a re-signed offer generates.  Unlike
`relationMembership_alphabet_eq` this needs no coherence hypothesis: re-signing
stamps the signature on the node the relation rebuilds. -/
theorem reannotate_relation_alphabet :
    ∀ fuel : Nat,
      (∀ (target : PactTypeAlphabet) (source residual : PactType)
          (state : TypeAutomatonState),
          (residual, state) ∈
            buildRelationSetCoreFuel fuel (source.reannotate target) →
          residual.alphabet = target) ∧
      (∀ (target : PactTypeAlphabet) (selected branch : BareMessage × PactType)
          (rest : List (BareMessage × PactType)) (residual : PactType)
          (state : TypeAutomatonState),
          (residual, state) ∈
            buildRelationSetCoreFuel fuel
              (parallelTypeBranchesSelecting target selected (branch :: rest)) →
          residual.alphabet = target) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro target source residual state hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_singleton] at hMem
        injection hMem with hResidual _
        rw [hResidual, PactType.reannotate_alphabet]
      · intro target selected branch rest residual state hMem
        simp only [buildRelationSetCoreFuel, Finset.mem_singleton] at hMem
        injection hMem with hResidual _
        rw [hResidual]
        simp only [parallelTypeBranchesSelecting]
        exact parallelTypeBranchesSelectingWithin_alphabet target selected
          (branch :: rest)
  | succ fuel ih =>
      -- A rebuilt parallel node carries the signature outright, and both
      -- survivor families are relations of children re-signed to it.
      have hPar : ∀ (target : PactTypeAlphabet)
          (leftChild rightChild : PactType) (interface : Interface)
          (residual : PactType) (state : TypeAutomatonState),
          (residual, state) ∈ buildRelationSetCoreFuel (fuel + 1)
            (.par target leftChild rightChild interface) →
          residual.alphabet = target := by
        intro target leftChild rightChild interface residual state hMem
        simp only [buildRelationSetCoreFuel] at hMem
        rcases Finset.mem_insert.mp hMem with hFinal | hRest
        · injection hFinal with hResidual _
          rw [hResidual]
          simp only [PactType.alphabet]
        rcases Finset.mem_union.mp hRest with hProductLeft | hSurvivorRight
        · rcases Finset.mem_union.mp hProductLeft with hProduct | hSurvivorLeft
          · rcases Finset.mem_image.mp hProduct with ⟨entry, _, hEq⟩
            injection hEq with hResidual _
            rw [← hResidual]
            simp only [PactType.alphabet]
          · rcases Finset.mem_image.mp hSurvivorLeft with ⟨entry, hEntry, hEq⟩
            injection hEq with hResidual _
            rw [← hResidual]
            exact ih.1 target leftChild entry.1 entry.2
              (Finset.mem_filter.mp hEntry).1
        · rcases Finset.mem_image.mp hSurvivorRight with ⟨entry, hEntry, hEq⟩
          injection hEq with hResidual _
          rw [← hResidual]
          exact ih.1 target rightChild entry.1 entry.2
            (Finset.mem_filter.mp hEntry).1
      -- Every exclusive-offer branch of a re-signed node is itself re-signed.
      have hBranchType : ∀ (t : PactTypeAlphabet)
          (branches : List (BareMessage × PactType))
          (indexed : (BareMessage × PactType) × Nat),
          indexed ∈ (PactType.reannotateBranches t branches).zipIdx →
          ∃ body : PactType, indexed.1.2 = body.reannotate t := by
        have hMap : ∀ (t : PactTypeAlphabet)
            (branches : List (BareMessage × PactType)),
            PactType.reannotateBranches t branches =
              branches.map (fun item => (item.1, item.2.reannotate t)) := by
          intro t branches
          induction branches with
          | nil => simp
          | cons head tail ihBranches =>
              obtain ⟨action, body⟩ := head
              simp only [PactType.reannotateBranches, List.map_cons,
                ihBranches]
        intro t branches indexed hIndexed
        have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
        rw [hMap, List.getElem?_map, Option.map_eq_some_iff] at hGet
        obtain ⟨item, _, hEq⟩ := hGet
        exact ⟨item.2, by rw [← hEq]⟩
      refine ⟨?_, ?_⟩
      · intro target source residual state hMem
        cases source with
        | skip a =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel,
              Finset.mem_singleton] at hMem
            injection hMem with hResidual _
            rw [hResidual]
            simp only [PactType.alphabet]
        | var a name =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel,
              Finset.mem_singleton] at hMem
            injection hMem with hResidual _
            rw [hResidual]
            simp only [PactType.alphabet]
        | message a msg dir =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hFinal
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            · rw [Finset.mem_singleton] at hFinal
              injection hFinal with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
        | tock a =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hFinal
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            · rw [Finset.mem_singleton] at hFinal
              injection hFinal with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
        | progress a pid =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hFinal
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            · rw [Finset.mem_singleton] at hFinal
              injection hFinal with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
        | choice a leftChild rightChild =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hRest
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            rcases Finset.mem_union.mp hRest with hLeft | hRight
            · rcases Finset.mem_image.mp hLeft with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target leftChild entry.1 entry.2 hEntry
            · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target rightChild entry.1 entry.2 hEntry
        | fairChoice a bid leftChild rightChild =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hRest
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            rcases Finset.mem_union.mp hRest with hLeft | hRight
            · rcases Finset.mem_image.mp hLeft with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target leftChild entry.1 entry.2 hEntry
            · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target rightChild entry.1 entry.2 hEntry
        | seq a leftChild rightChild =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_union.mp hMem with hLeft | hRight
            · rcases Finset.mem_image.mp hLeft with ⟨entry, _, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              simp only [PactType.alphabet]
            · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target rightChild entry.1 entry.2 hEntry
        | par a leftChild rightChild interface =>
            simp only [PactType.reannotate] at hMem
            exact hPar target _ _ _ residual state hMem
        | recur a name body =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hBody
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            · rcases Finset.mem_image.mp hBody with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              have hEntryAlphabet := ih.1 target body entry.1 entry.2 hEntry
              rw [PactType.replaceVar_alphabet_eq_of_replacement entry.1 name
                (by rw [hEntryAlphabet]; simp only [PactType.alphabet]),
                hEntryAlphabet]
        | xoffer a elseType branches =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hRest
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            rcases Finset.mem_union.mp hRest with hElse | hBranch
            · rcases Finset.mem_image.mp hElse with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target elseType entry.1 entry.2 hEntry
            · rw [mem_foldl_union_iff] at hBranch
              rcases hBranch with hEmpty | ⟨indexed, hIndexed, hImage⟩
              · simp at hEmpty
              · rcases Finset.mem_image.mp hImage with ⟨entry, hEntry, hEq⟩
                injection hEq with hResidual _
                rw [← hResidual]
                obtain ⟨body, hBody⟩ := hBranchType target branches indexed
                  hIndexed
                rw [hBody] at hEntry
                exact ih.1 target body entry.1 entry.2 hEntry
        | offer a elseType branches =>
            simp only [PactType.reannotate, buildRelationSetCoreFuel] at hMem
            rcases Finset.mem_insert.mp hMem with hRoot | hRest
            · injection hRoot with hResidual _
              rw [hResidual]
              simp only [PactType.alphabet]
            rcases Finset.mem_union.mp hRest with hElse | hBranch
            · rcases Finset.mem_image.mp hElse with ⟨entry, hEntry, hEq⟩
              injection hEq with hResidual _
              rw [← hResidual]
              exact ih.1 target elseType entry.1 entry.2 hEntry
            · rw [mem_foldl_union_iff] at hBranch
              rcases hBranch with hEmpty | ⟨indexed, hIndexed, hImage⟩
              · simp at hEmpty
              · rcases Finset.mem_image.mp hImage with ⟨entry, hEntry, hEq⟩
                injection hEq with hResidual _
                rw [← hResidual]
                cases hOffer : PactType.reannotateOfferBranches target ∅
                    branches with
                | nil =>
                    rw [hOffer] at hIndexed
                    simp at hIndexed
                | cons head tail =>
                    rw [hOffer] at hEntry
                    exact ih.2 target indexed.1 head tail entry.1 entry.2 hEntry
      · intro target selected branch rest residual state hMem
        simp only [parallelTypeBranchesSelecting] at hMem
        cases rest with
        | cons next tail =>
            simp only [parallelTypeBranchesSelectingWithin] at hMem
            by_cases hSelected : branch = selected
            · rw [if_pos hSelected] at hMem
              exact hPar target _ _ _ residual state hMem
            · rw [if_neg hSelected] at hMem
              exact hPar target _ _ _ residual state hMem
        | nil =>
            simp only [parallelTypeBranchesSelectingWithin] at hMem
            by_cases hSelected : branch = selected
            · rw [if_pos hSelected] at hMem
              simp only [selectedTypeBranchAt, buildRelationSetCoreFuel] at hMem
              rcases Finset.mem_union.mp hMem with hLeft | hRight
              · rcases Finset.mem_image.mp hLeft with ⟨entry, _, hEq⟩
                injection hEq with hResidual _
                rw [← hResidual]
                simp only [PactType.alphabet]
              · rcases Finset.mem_image.mp hRight with ⟨entry, hEntry, hEq⟩
                injection hEq with hResidual _
                rw [← hResidual]
                exact ih.1 target branch.2 entry.1 entry.2 hEntry
            · rw [if_neg hSelected] at hMem
              simp only [singletonTypeXOfferAt,
                buildRelationSetCoreFuel] at hMem
              rcases Finset.mem_insert.mp hMem with hRoot | hRest
              · injection hRoot with hResidual _
                rw [hResidual]
                simp only [PactType.alphabet]
              rcases Finset.mem_union.mp hRest with hElse | hBranch
              · rcases Finset.mem_image.mp hElse with ⟨entry, hEntry, hEq⟩
                injection hEq with hResidual _
                rw [← hResidual]
                exact ih.1 target (.skip target) entry.1 entry.2
                  (by simpa only [PactType.reannotate] using hEntry)
              · rw [mem_foldl_union_iff] at hBranch
                rcases hBranch with hEmpty | ⟨indexed, hIndexed, hImage⟩
                · simp at hEmpty
                · rcases Finset.mem_image.mp hImage with ⟨entry, hEntry, hEq⟩
                  injection hEq with hResidual _
                  rw [← hResidual]
                  have hIndexedEq : indexed =
                      ((branch.1, branch.2.reannotate target), 0) := by
                    simpa using hIndexed
                  rw [hIndexedEq] at hEntry
                  exact ih.1 target branch.2 entry.1 entry.2 hEntry

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
            simp only [PactType.alphabet]
      | tock alphabet =>
          rcases relationMembership_tock_cases alphabet hRelated with
            hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp only [PactType.alphabet]
      | progress alphabet pid =>
          rcases relationMembership_progress_cases alphabet pid
              hRelated with hRoot | hFinal
          · rw [hRoot.1]
          · rw [hFinal.1]
            simp only [PactType.alphabet]
      | var alphabet other =>
          rw [(relationMembership_var_cases alphabet other hRelated).1]
      | choice alphabet left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hCoherent.2.2.1 hLeftRelated).trans hCoherent.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hCoherent.2.2.1 hLeftRelated).trans hCoherent.1
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | seq alphabet left right =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            simp only [PactType.alphabet]
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel right) hRightFuel right rfl residual
              q hCoherent.2.2.2 hRightRelated).trans hCoherent.2.1
      | par alphabet left right interface =>
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            simp only [PactType.alphabet]
          -- A survivor residual belongs to the re-signed child's relation, so
          -- it carries the node alphabet outright; coherence is not needed.
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual,
              (reannotate_relation_alphabet
                  (typeCompilationFuel (left.reannotate alphabet))).1
                alphabet left residualLeft q1 hLeftRelated]
            simp only [PactType.alphabet]
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual,
              (reannotate_relation_alphabet
                  (typeCompilationFuel (right.reannotate alphabet))).1
                alphabet right residualRight q2 hRightRelated]
            simp only [PactType.alphabet]
          · injection hFinal with hResidual _
            rw [hResidual]
            simp only [PactType.alphabet]
      | recur alphabet binder body =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_recur_cases alphabet binder body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyAlpha : bodyResidual.alphabet = body.alphabet :=
              ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
                hCoherent.2 hBodyRelated
            have hRepl : (PactType.recur alphabet binder body).alphabet =
                bodyResidual.alphabet := by
              rw [hBodyAlpha]
              exact hCoherent.1.symm
            rw [PactType.replaceVar_alphabet_eq_of_replacement bodyResidual
              binder hRepl]
            exact hBodyAlpha.trans hCoherent.1
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetCoherent] at hCoherent
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hCoherent.2.1 hElseRelated).trans hCoherent.1
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
            have hBranchCoherent := branchesAlphabetCoherent_of_mem
              hCoherent.2.2 hMember
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
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact (ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hCoherent.2.1 hElseRelated).trans hCoherent.1
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            cases branches with
            | nil => cases hMember
            | cons branch rest =>
                exact (reannotate_relation_alphabet
                    (typeCompilationFuel
                      (parallelTypeBranchesSelecting alphabet selected
                        (branch :: rest)))).2
                  alphabet selected branch rest residual q hSelectedRelated

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
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ alphabet : PactTypeAlphabet,
          replacement.alphabet = alphabet →
          PactType.BranchesAlphabetWellFormed alphabet branches →
          PactType.TailBranchOccurrences name True branches →
          PactType.BranchesAlphabetWellFormed alphabet
            (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize alphabet hAlpha hWF hTail
        induction branches with
        | nil =>
            simp [PactType.replaceBranches,
              PactType.BranchesAlphabetWellFormed]
        | cons head rest restIH =>
            rcases head with ⟨action, branchType⟩
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
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hBranchAlpha : replacement.alphabet = branchType.alphabet := by
              rw [hWF.1]; exact hAlpha
            refine ⟨?_, ih (sizeOf branchType) hBranchSize branchType rfl
                hWF.2.1 hBranchAlpha hTail.1,
              restIH hRestSize hWF.2.2 hTail.2⟩
            rw [PactType.replaceVar_alphabet_eq_of_replacement branchType name
              hBranchAlpha]
            exact hWF.1
      intro hWF hAlpha hTail
      cases processType with
      | message alphabet msg dir | progress alphabet pid | tock alphabet
      | skip alphabet =>
          simpa only [PactType.replaceVar] using hWF
      | var alphabet other =>
          by_cases hName : name = other
          · simpa [PactType.replaceVar, hName] using hReplacementWF
          · simpa only [PactType.replaceVar, if_neg hName] using hWF
      | choice alphabet left right | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAlpha
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeftAlpha : replacement.alphabet = left.alphabet := by
            rw [hWF.2.1]; exact hAlpha
          have hRightAlpha : replacement.alphabet = right.alphabet := by
            rw [hWF.2.2.1]; exact hAlpha
          refine ⟨hWF.1, ?_, ?_,
            ih (sizeOf left) hLeftSize left rfl hWF.2.2.2.1 hLeftAlpha hTail.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2 hRightAlpha
              hTail.2⟩
          · rw [PactType.replaceVar_alphabet_eq_of_replacement left name
              hLeftAlpha]
            exact hWF.2.1
          · rw [PactType.replaceVar_alphabet_eq_of_replacement right name
              hRightAlpha]
            exact hWF.2.2.1
      | seq alphabet left right =>
          -- Given this, now the left operand is non-tail, so inert.
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAlpha
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1]
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hRightAlpha : replacement.alphabet = right.alphabet := by
            rw [hWF.2.2.1]; exact hAlpha
          refine ⟨hWF.1, hWF.2.1, ?_, hWF.2.2.2.1,
            ih (sizeOf right) hRightSize right rfl hWF.2.2.2.2 hRightAlpha
              hTail.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement right name
            hRightAlpha]
          exact hWF.2.2.1
      | par alphabet left right interface =>
          -- Given this, now both children are non-tail, so inert.
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.replaceVar]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false name
            replacement left hTail.1,
            PactType.replaceVar_eq_self_of_tailOccurrences_false name
              replacement right hTail.2]
          exact hWF
      | recur alphabet other body =>
          by_cases hName : name = other
          · simpa only [PactType.replaceVar, if_pos hName] using hWF
          · simp only [PactType.AlphabetWellFormed] at hWF
            simp only [PactType.TailOccurrences, if_neg (Ne.symm hName)] at hTail
            simp only [PactType.alphabet] at hAlpha
            simp only [PactType.replaceVar, if_neg hName,
              PactType.AlphabetWellFormed]
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            have hBodyAlpha : replacement.alphabet = body.alphabet := by
              rw [hWF.2.1]; exact hAlpha
            refine ⟨hWF.1, ?_, ih (sizeOf body) hBodySize body rfl hWF.2.2
              hBodyAlpha hTail⟩
            rw [PactType.replaceVar_alphabet_eq_of_replacement body name
              hBodyAlpha]
            exact hWF.2.1
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAlpha
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hElseAlpha : replacement.alphabet = elseType.alphabet := by
            rw [hWF.2.1]; exact hAlpha
          refine ⟨hWF.1, ?_, ih (sizeOf elseType) hElseSize elseType rfl
              hWF.2.2.1 hElseAlpha hTail.1,
            hBranches branches hBranchesSize alphabet hAlpha hWF.2.2.2 hTail.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement elseType name
            hElseAlpha]
          exact hWF.2.1
      | offer alphabet elseType branches =>
          -- Given this, now the branch bodies are non-tail, so inert, and the
          -- alphabet partition they carry is unchanged.
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.TailOccurrences] at hTail
          simp only [PactType.alphabet] at hAlpha
          simp only [PactType.replaceVar, PactType.AlphabetWellFormed]
          rw [PactType.replaceBranches_eq_self_of_tailBranchOccurrences_false
            name replacement branches hTail.2]
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hElseAlpha : replacement.alphabet = elseType.alphabet := by
            rw [hWF.2.1]; exact hAlpha
          refine ⟨hWF.1, ?_, ih (sizeOf elseType) hElseSize elseType rfl
              hWF.2.2.1 hElseAlpha hTail.1, hWF.2.2.2⟩
          rw [PactType.replaceVar_alphabet_eq_of_replacement elseType name
            hElseAlpha]
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
              hEntry, hLeftRelated, hRightRelated⟩
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
            have hLeftFuel :
                typeCompilationFuel (left.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact PactType.tailOccurrences_mono name False.elim _
              (ih (typeCompilationFuel (left.reannotate alphabet)) hLeftFuel
                (left.reannotate alphabet) rfl residualLeft q1 name False
                (PactType.reannotate_tailRecursive left alphabet hTailRec.1)
                (PactType.reannotate_tailOccurrences name left alphabet False
                  hFields.1)
                hLeftRelated)
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel :
                typeCompilationFuel (right.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact PactType.tailOccurrences_mono name False.elim _
              (ih (typeCompilationFuel (right.reannotate alphabet)) hRightFuel
                (right.reannotate alphabet) rfl residualRight q2 name False
                (PactType.reannotate_tailRecursive right alphabet hTailRec.2)
                (PactType.reannotate_tailOccurrences name right alphabet False
                  hFields.2)
                hRightRelated)
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
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting alphabet selected branches)
              rfl residual q name tail
              (parallelTypeBranchesSelecting_tailRecursive alphabet selected branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (parallelTypeBranchesSelecting_tailOccurrences name alphabet selected
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
  suffices hMain : ∀ (source residual : PactType) (state : TypeAutomatonState),
      source.TailRecursive → source.TailClosed →
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      residual.TailRecursive by
    intro source residual state hTailRec hClosed hRelated
    exact ⟨hMain source residual state hTailRec hClosed hRelated,
      fun name => relationMembership_tailOccurrences source residual state name
        True hTailRec (hClosed name) hRelated⟩
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hTailRec hClosed hRelated
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
          have hFieldsClosed : ∀ other : String,
              left.TailOccurrences other True ∧
                right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          rcases relationMembership_choice_cases alphabet left right
              hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 (fun other => (hFieldsClosed other).1) hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 (fun other => (hFieldsClosed other).2) hRightRelated
      | fairChoice alphabet bid left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFieldsClosed : ∀ other : String,
              left.TailOccurrences other True ∧
                right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          rcases relationMembership_fairChoice_cases alphabet bid left
              right hRelated with hRoot | hLeft | hRight
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hLeft with ⟨q, _, hLeftRelated⟩
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel left) hLeftFuel left rfl residual q
              hTailRec.1 (fun other => (hFieldsClosed other).1) hLeftRelated
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 (fun other => (hFieldsClosed other).2) hRightRelated
      | seq alphabet left right =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFieldsClosed : ∀ other : String,
              left.TailOccurrences other False ∧
                right.TailOccurrences other True := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedLeft : left.TailClosed := fun other =>
            PactType.tailOccurrences_mono other False.elim left
              (hFieldsClosed other).1
          rcases relationMembership_seq_cases alphabet left right
              hRelated with hLeft | hRight
          · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailRecursive] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q hTailRec.1 hClosedLeft hLeftRelated)
                hTailRec.2
          · rcases hRight with ⟨q, _, hRightRelated⟩
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel right) hRightFuel right rfl residual q
              hTailRec.2 (fun other => (hFieldsClosed other).2) hRightRelated
      | par alphabet left right interface =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFieldsClosed : ∀ other : String,
              left.TailOccurrences other False ∧
                right.TailOccurrences other False := fun other => by
            simpa only [PactType.TailOccurrences] using hClosed other
          have hClosedLeft : left.TailClosed := fun other =>
            PactType.tailOccurrences_mono other False.elim left
              (hFieldsClosed other).1
          have hClosedRight : right.TailClosed := fun other =>
            PactType.tailOccurrences_mono other False.elim right
              (hFieldsClosed other).2
          rcases relationMembership_par_cases alphabet left right
              interface hRelated with hPair | hSurvL | hSurvR | hFinal
          · rcases hPair with ⟨q1, q2, leftResidual, rightResidual,
              hEntry, hLeftRelated, hRightRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel : typeCompilationFuel left < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hRightFuel : typeCompilationFuel right < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            simpa only [PactType.TailRecursive] using
              And.intro (ih (typeCompilationFuel left) hLeftFuel left rfl
                  leftResidual q1 hTailRec.1 hClosedLeft hLeftRelated)
                (ih (typeCompilationFuel right) hRightFuel right rfl
                  rightResidual q2 hTailRec.2 hClosedRight hRightRelated)
          · rcases hSurvL with ⟨q1, residualLeft, hEntry, hLeftRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hLeftFuel :
                typeCompilationFuel (left.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel (left.reannotate alphabet)) hLeftFuel
              (left.reannotate alphabet) rfl residualLeft q1
              (PactType.reannotate_tailRecursive left alphabet hTailRec.1)
              (fun other => PactType.reannotate_tailOccurrences other left
                alphabet True (hClosedLeft other))
              hLeftRelated
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel :
                typeCompilationFuel (right.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel (right.reannotate alphabet))
              hRightFuel (right.reannotate alphabet) rfl residualRight q2
              (PactType.reannotate_tailRecursive right alphabet hTailRec.2)
              (fun other => PactType.reannotate_tailOccurrences other right
                alphabet True (hClosedRight other))
              hRightRelated
          · injection hFinal with hResidual _
            rw [hResidual]
            simp [PactType.TailRecursive]
      | recur alphabet binder body =>
          have hTailRecFull := hTailRec
          simp only [PactType.TailRecursive] at hTailRec
          have hClosedBody : body.TailClosed := by
            intro other
            by_cases hBinder : binder = other
            · subst hBinder
              exact hTailRec.1
            · simpa only [PactType.TailOccurrences, if_neg hBinder] using
                hClosed other
          rcases relationMembership_recur_cases alphabet binder body
              hRelated with hRoot | hBody
          · injection hRoot with hResidual _
            rw [hResidual]
            exact hTailRecFull
          · rcases hBody with ⟨q, bodyResidual, hEntry, hBodyRelated⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hBodyFuel : typeCompilationFuel body < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            have hBodyResidualRec : bodyResidual.TailRecursive :=
              ih (typeCompilationFuel body) hBodyFuel body rfl bodyResidual q
                hTailRec.2 hClosedBody hBodyRelated
            have hBodyResidualTail :
                bodyResidual.TailOccurrences binder True :=
              relationMembership_tailOccurrences body bodyResidual q binder True
                hTailRec.2 hTailRec.1 hBodyRelated
            exact PactType.tailRecursive_replaceVar binder hTailRecFull hClosed
              bodyResidual hBodyResidualRec hBodyResidualTail
      | xoffer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFieldsClosed : ∀ other : String,
              elseType.TailOccurrences other True ∧
                PactType.TailBranchOccurrences other True branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hClosed other
          rcases relationMembership_xoffer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hBranch
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 (fun other => (hFieldsClosed other).1)
              hElseRelated
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
              (fun other => PactType.tailOccurrences_of_mem_branches other True
                (hFieldsClosed other).2 hMember)
              hBranchRelated
      | offer alphabet elseType branches =>
          simp only [PactType.TailRecursive] at hTailRec
          have hFieldsClosed : ∀ other : String,
              elseType.TailOccurrences other True ∧
                PactType.TailBranchOccurrences other False branches :=
            fun other => by
              simpa only [PactType.TailOccurrences] using hClosed other
          rcases relationMembership_offer_cases alphabet elseType
              branches hRelated with hRoot | hElse | hSelected
          · injection hRoot with hResidual _
            rw [hResidual]
            simpa only [PactType.TailRecursive] using hTailRec
          · rcases hElse with ⟨q, _, hElseRelated⟩
            have hElseFuel : typeCompilationFuel elseType < n := by
              rw [← hFuel]; simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel elseType) hElseFuel elseType rfl
              residual q hTailRec.1 (fun other => (hFieldsClosed other).1)
              hElseRelated
          · rcases hSelected with ⟨i, selected, q, hGet, _, hSelectedRelated⟩
            have hMember : selected ∈ branches := List.mem_of_getElem? hGet
            have hSelectedFuel : typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              hSelectedFuel
              (parallelTypeBranchesSelecting alphabet selected branches) rfl
              residual q
              (parallelTypeBranchesSelecting_tailRecursive alphabet selected
                branches
                (fun branch hBranch =>
                  tailRecursive_of_mem_branches hTailRec.2 hBranch)
                (tailRecursive_of_mem_branches hTailRec.2 hMember))
              (fun other =>
                parallelTypeBranchesSelecting_tailOccurrences other alphabet
                  selected branches True
                  (fun branch hBranch =>
                    PactType.tailOccurrences_of_mem_branches other False
                      (hFieldsClosed other).2 hBranch)
                  (PactType.tailOccurrences_of_mem_branches other False
                    (hFieldsClosed other).2 hMember))
              hSelectedRelated

/-- A branch's own declarations meet none of the actions its later siblings
mention, once the branch list is pairwise disjoint. -/
theorem branchMessageActions_disjoint_of_head
    {branch : BareMessage × PactType} :
    ∀ rest : List (BareMessage × PactType),
      (∀ other ∈ rest, BranchDeclarationsDisjoint branch other) →
      Disjoint ({branch.1} ∪ PactType.MessageActions branch.2)
        (PactType.BranchMessageActions rest)
  | [], _ => by simp [PactType.BranchMessageActions]
  | (action, body) :: rest, hDisjoint => by
      simp only [PactType.BranchMessageActions]
      exact Finset.disjoint_union_right.mpr
        ⟨(hDisjoint (action, body) (by simp)).1,
          branchMessageActions_disjoint_of_head rest
            (fun other hOther => hDisjoint other (by simp [hOther]))⟩

/-- Two successive removals are one removal of the union. -/
theorem sdiff_sdiff_eq_sdiff_union {A s t : Finset BareMessage} :
    (A \ s) \ t = A \ (s ∪ t) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- Two complements taken against disjoint remainders cover the whole. -/
theorem sdiff_union_sdiff_of_disjoint {A seen X Y : Finset BareMessage}
    (hDisjoint : Disjoint X Y) :
    (A \ (seen ∪ Y)) ∪ (A \ (seen ∪ X)) = A \ seen := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hx, hn⟩ | ⟨hx, hn⟩) <;> exact ⟨hx, fun h => hn (Or.inl h)⟩
  · rintro ⟨hx, hn⟩
    by_cases hIn : x ∈ Y
    · exact Or.inr ⟨hx, fun hmem => hmem.elim hn
        (fun h => (Finset.disjoint_left.mp hDisjoint h) hIn)⟩
    · exact Or.inl ⟨hx, fun hmem => hmem.elim hn (fun h => hIn h)⟩

/-- A node whose two components carry the enclosing alphabet and synchronise on
nothing is compatible with it. -/
theorem PactTypeAlphabet.parallelCompatible_self_empty
    (alphabet : PactTypeAlphabet) :
    PactTypeAlphabet.ParallelCompatible alphabet alphabet alphabet ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro action _ hInterface
    simp at hInterface
  · intro msg hMsg
    simp at hMsg
  · cases alphabet with
    | mk actions => simp [PactTypeAlphabet.hideInterface]
  · cases alphabet with
    | mk actions => simp [PactTypeAlphabet.hideInterface]

/-- The singleton expansion is well formed at the alphabet its branch carries. -/
theorem singletonTypeXOfferAt_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hBody : branch.2.AlphabetWellFormed)
    (hScoped : branch.2.InterfaceScoped)
    (hAvoid : ∀ action ∈ alphabet.actions,
      action.1 ∉ PactType.ParallelInterfaces branch.2) :
    (singletonTypeXOfferAt alphabet branch).AlphabetWellFormed := by
  rcases branch with ⟨action, body⟩
  simp only [singletonTypeXOfferAt, PactType.AlphabetWellFormed,
    PactType.BranchesAlphabetWellFormed, PactType.alphabet]
  exact ⟨hAlphaWF, trivial, hAlphaWF, PactType.reannotate_alphabet _ _,
    PactType.reannotate_alphabetWellFormed_avoiding body alphabet hBody
      hAlphaWF hScoped hAvoid, trivial⟩

/-- Same for the committed branch, whose head action becomes mandatory. -/
theorem selectedTypeBranchAt_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (hAlphaWF : alphabet.WellFormed)
    {branch : BareMessage × PactType} (hBody : branch.2.AlphabetWellFormed)
    (hScoped : branch.2.InterfaceScoped)
    (hAvoid : ∀ action ∈ alphabet.actions,
      action.1 ∉ PactType.ParallelInterfaces branch.2) :
    (selectedTypeBranchAt alphabet branch).AlphabetWellFormed := by
  rcases branch with ⟨action, body⟩
  simp only [selectedTypeBranchAt, PactType.AlphabetWellFormed,
    PactType.alphabet]
  exact ⟨hAlphaWF, trivial, PactType.reannotate_alphabet _ _, hAlphaWF,
    PactType.reannotate_alphabetWellFormed_avoiding body alphabet hBody
      hAlphaWF hScoped hAvoid⟩

/-- The generated branch product of a conjunctive offer is well formed.  Every
component carries the enclosing alphabet and the products synchronise on
nothing, so compatibility is immediate. -/
theorem parallelTypeBranchesWithin_alphabetWellFormed :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      alphabet.WellFormed →
      PactType.OfferBranchesWellFormed alphabet ∅ branches →
      PactType.InterfaceScopedBranches branches →
      (∀ action ∈ alphabet.actions,
        action.1 ∉ PactType.ParallelBranchInterfaces branches) →
      (parallelTypeBranchesWithin alphabet branches).AlphabetWellFormed
  | [], alphabet, hAlphaWF, _, _, _ => by
      simp only [parallelTypeBranchesWithin, PactType.AlphabetWellFormed]
      exact hAlphaWF
  | [(a1, b1)], alphabet, hAlphaWF, hOB, hScoped, hAvoid => by
      simp only [PactType.OfferBranchesWellFormed] at hOB
      simp only [PactType.InterfaceScopedBranches] at hScoped
      simp only [PactType.ParallelBranchInterfaces, Finset.union_empty]
        at hAvoid
      exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hOB.2.1
        hScoped.1 hAvoid
  | (a1, b1) :: next :: tl, alphabet, hAlphaWF, hOB, hScoped, hAvoid => by
      simp only [PactType.OfferBranchesWellFormed] at hOB
      simp only [PactType.InterfaceScopedBranches] at hScoped
      simp only [PactType.ParallelBranchInterfaces, Finset.mem_union] at hAvoid
      simp only [parallelTypeBranchesWithin, PactType.AlphabetWellFormed,
        parallelTypeBranchesWithin_alphabet]
      refine ⟨hAlphaWF, PactTypeAlphabet.parallelCompatible_self_empty _, ?_, ?_⟩
      · exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hOB.2.1
          hScoped.1 (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
      · exact parallelTypeBranchesWithin_alphabetWellFormed (next :: tl) alphabet
          hAlphaWF hOB.2.2 hScoped.2
          (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))

/-- Same after one branch has been committed. -/
theorem parallelTypeBranchesSelectingWithin_alphabetWellFormed
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      alphabet.WellFormed →
      PactType.OfferBranchesWellFormed alphabet ∅ branches →
      PactType.InterfaceScopedBranches branches →
      (∀ action ∈ alphabet.actions,
        action.1 ∉ PactType.ParallelBranchInterfaces branches) →
      (parallelTypeBranchesSelectingWithin alphabet selected
        branches).AlphabetWellFormed
  | [], alphabet, hAlphaWF, _, _, _ => by
      simp only [parallelTypeBranchesSelectingWithin,
        PactType.AlphabetWellFormed]
      exact hAlphaWF
  | [(a1, b1)], alphabet, hAlphaWF, hOB, hScoped, hAvoid => by
      simp only [PactType.OfferBranchesWellFormed] at hOB
      simp only [PactType.InterfaceScopedBranches] at hScoped
      simp only [PactType.ParallelBranchInterfaces, Finset.union_empty]
        at hAvoid
      by_cases hSel : ((a1, b1) : BareMessage × PactType) = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSel]
        exact selectedTypeBranchAt_alphabetWellFormed alphabet hAlphaWF hOB.2.1
          hScoped.1 hAvoid
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSel]
        exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF hOB.2.1
          hScoped.1 hAvoid
  | (a1, b1) :: next :: tl, alphabet, hAlphaWF, hOB, hScoped, hAvoid => by
      simp only [PactType.OfferBranchesWellFormed] at hOB
      simp only [PactType.InterfaceScopedBranches] at hScoped
      simp only [PactType.ParallelBranchInterfaces, Finset.mem_union] at hAvoid
      by_cases hSel : ((a1, b1) : BareMessage × PactType) = selected
      · simp only [parallelTypeBranchesSelectingWithin, if_pos hSel,
          PactType.AlphabetWellFormed, parallelTypeBranchesWithin_alphabet]
        refine ⟨hAlphaWF, PactTypeAlphabet.parallelCompatible_self_empty _, ?_, ?_⟩
        · exact selectedTypeBranchAt_alphabetWellFormed alphabet hAlphaWF
            hOB.2.1 hScoped.1
            (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
        · exact parallelTypeBranchesWithin_alphabetWellFormed (next :: tl)
            alphabet hAlphaWF hOB.2.2 hScoped.2
            (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))
      · simp only [parallelTypeBranchesSelectingWithin, if_neg hSel,
          PactType.AlphabetWellFormed, parallelTypeBranchesSelectingWithin_alphabet]
        refine ⟨hAlphaWF, PactTypeAlphabet.parallelCompatible_self_empty _, ?_, ?_⟩
        · exact singletonTypeXOfferAt_alphabetWellFormed alphabet hAlphaWF
            hOB.2.1 hScoped.1
            (fun act hAct hIn => hAvoid act hAct (Or.inl hIn))
        · exact parallelTypeBranchesSelectingWithin_alphabetWellFormed selected
            (next :: tl) alphabet hAlphaWF hOB.2.2 hScoped.2
            (fun act hAct hIn => hAvoid act hAct (Or.inr hIn))

/-- Committing a conjunctive offer keeps the alphabet well-formed: every
generated component carries the offer's own alphabet. -/
theorem committedOffer_alphabetWellFormed
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (selected : BareMessage × PactType)
    (hOfferWF : (PactType.offer alphabet elseType branches).AlphabetWellFormed)
    (hScoped : (PactType.offer alphabet elseType branches).InterfaceScoped)
    (hAlphaScoped :
      (PactType.offer alphabet elseType branches).InterfaceAlphabetScoped)
    (hSelected : selected ∈ branches) :
    (parallelTypeBranchesSelecting alphabet selected branches).AlphabetWellFormed := by
  classical
  simp only [PactType.AlphabetWellFormed] at hOfferWF
  simp only [PactType.InterfaceScoped] at hScoped
  simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
  have hAvoid : ∀ action ∈ alphabet.actions,
      action.1 ∉ PactType.ParallelBranchInterfaces branches := by
    intro action hAction hIn
    exact Finset.disjoint_left.mp hAlphaScoped.1
      (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
      (Finset.mem_union_right _ hIn)
  cases branches with
  | nil => cases hSelected
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact
        parallelTypeBranchesSelectingWithin_alphabetWellFormed
          selected (branch :: rest) alphabet hOfferWF.1 hOfferWF.2.2.2
          hScoped.2 hAvoid

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
carrying the interface scoping the generated product needs. -/
def CommittedOfferAlphabetWellFormed : Prop :=
  ∀ (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (selected : BareMessage × PactType),
    (PactType.offer alphabet elseType branches).AlphabetWellFormed →
    (PactType.offer alphabet elseType branches).InterfaceScoped →
    (PactType.offer alphabet elseType branches).InterfaceAlphabetScoped →
    selected ∈ branches →
    (parallelTypeBranchesSelecting alphabet selected branches).AlphabetWellFormed

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
  -- Open: `hCommitted` and `reannotate_alphabetWellFormed` both hold now; only
  -- the induction over the relation is missing.
  sorry

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
              hEntry, hLeftRelated, hRightRelated⟩
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
            have hLeftFuel :
                typeCompilationFuel (left.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel (left.reannotate alphabet)) hLeftFuel
              (left.reannotate alphabet) rfl residualLeft q1
              (PactType.reannotate_tailRecursive left alphabet hTailRec.1)
              (reannotate_offerBranchesDisjoint left alphabet hDisjoint.1)
              hLeftRelated
          · rcases hSurvR with ⟨q2, residualRight, hEntry, hRightRelated, _⟩
            injection hEntry with hResidual _
            rw [hResidual]
            have hRightFuel :
                typeCompilationFuel (right.reannotate alphabet) < n := by
              rw [← hFuel, typeCompilationFuel_reannotate]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel (right.reannotate alphabet))
              hRightFuel (right.reannotate alphabet) rfl residualRight q2
              (PactType.reannotate_tailRecursive right alphabet hTailRec.2)
              (reannotate_offerBranchesDisjoint right alphabet hDisjoint.2)
              hRightRelated
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
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hFuel]
              simp only [typeCompilationFuel]; omega
            exact ih (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              hSelectedFuel (parallelTypeBranchesSelecting alphabet selected branches)
              rfl residual q
              (parallelTypeBranchesSelecting_tailRecursive alphabet selected branches
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
  -- Open: the offer-commit case reduces to `committedOffer_alphabetWellFormed`,
  -- which now holds; only the induction over the transition is missing.
  sorry

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

/-- Every component of the branch product carries the enclosing alphabet, and
the interfaces below it are exactly the branches' own, so the offer's scoping
condition transfers to the product. -/
theorem parallelTypeBranchesWithin_interfaceAlphabetScoped
    (alphabet : PactTypeAlphabet)
    (hAvoid : ∀ action ∈ alphabet.actions,
      action.1 ∉ PactType.ParallelBranchInterfaces branchesAll) :
    ∀ branches : List (BareMessage × PactType),
      PactType.ParallelBranchInterfaces branches ⊆
        PactType.ParallelBranchInterfaces branchesAll →
      PactType.InterfaceAlphabetScopedBranches branches →
      PactType.InterfaceAlphabetScoped
        (parallelTypeBranchesWithin alphabet branches) := by
  have hDisj : ∀ blocked : Finset MessageId,
      blocked ⊆ PactType.ParallelBranchInterfaces branchesAll →
      Disjoint (PactTypeAlphabet.messageIds alphabet) blocked := by
    intro blocked hSub
    refine Finset.disjoint_left.mpr ?_
    intro msg hMsg hBlocked
    obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp hMsg
    exact hAvoid action hAction (hSub hBlocked)
  intro branches
  induction branches with
  | nil =>
      intro _ _
      simp [parallelTypeBranchesWithin, PactType.InterfaceAlphabetScoped]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hSub hScoped
      simp only [PactType.InterfaceAlphabetScopedBranches] at hScoped
      have hBodySub : PactType.ParallelInterfaces body ⊆
          PactType.ParallelBranchInterfaces branchesAll := by
        refine Finset.Subset.trans ?_ hSub
        simp only [PactType.ParallelBranchInterfaces]
        exact Finset.subset_union_left
      have hRestSub : PactType.ParallelBranchInterfaces rest ⊆
          PactType.ParallelBranchInterfaces branchesAll := by
        refine Finset.Subset.trans ?_ hSub
        simp only [PactType.ParallelBranchInterfaces]
        exact Finset.subset_union_right
      have hLeaf : PactType.InterfaceAlphabetScoped
          (singletonTypeXOfferAt alphabet (action, body)) := by
        simp only [singletonTypeXOfferAt, PactType.InterfaceAlphabetScoped,
          PactType.InterfaceAlphabetScopedBranches,
          PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
          PactType.reannotate_parallelInterfaces]
        refine ⟨?_, trivial, ?_, trivial⟩
        · simpa using hDisj (PactType.ParallelInterfaces body) hBodySub
        · exact PactType.reannotate_interfaceAlphabetScoped body alphabet
            hScoped.1 (fun act hAct hIn => hAvoid act hAct (hBodySub hIn))
      cases rest with
      | nil =>
          simpa only [parallelTypeBranchesWithin] using hLeaf
      | cons next tail =>
          simp only [parallelTypeBranchesWithin,
            PactType.InterfaceAlphabetScoped]
          refine ⟨?_, hLeaf, ih hRestSub hScoped.2⟩
          rw [singletonTypeXOfferAt, PactType.ParallelInterfaces]
          rw [parallelTypeBranchesWithin_parallelInterfaces (next :: tail)
            alphabet]
          refine hDisj _ ?_
          intro msg hMsg
          rcases Finset.mem_union.mp hMsg with hMsg | hMsg
          · rcases Finset.mem_union.mp hMsg with hMsg | hMsg
            · exact absurd hMsg (Finset.notMem_empty msg)
            · simp only [PactType.ParallelInterfaces,
                PactType.ParallelBranchInterfaces,
                PactType.reannotate_parallelInterfaces,
                Finset.union_empty, Finset.empty_union] at hMsg
              exact hBodySub hMsg
          · exact hRestSub hMsg

/-- The committed branch product of a conjunctive offer inherits the offer's
interface-alphabet scoping. -/
theorem parallelTypeBranchesSelecting_interfaceAlphabetScoped
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hScoped : PactType.InterfaceAlphabetScopedBranches branches)
    (hAvoid : ∀ action ∈ alphabet.actions,
      action.1 ∉ PactType.ParallelBranchInterfaces branches) :
    PactType.InterfaceAlphabetScoped
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  have hDisj : ∀ blocked : Finset MessageId,
      blocked ⊆ PactType.ParallelBranchInterfaces branches →
      Disjoint (PactTypeAlphabet.messageIds alphabet) blocked := by
    intro blocked hSub
    refine Finset.disjoint_left.mpr ?_
    intro msg hMsg hBlocked
    obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp hMsg
    exact hAvoid action hAction (hSub hBlocked)
  have hWithin : ∀ list : List (BareMessage × PactType),
      PactType.ParallelBranchInterfaces list ⊆
        PactType.ParallelBranchInterfaces branches →
      PactType.InterfaceAlphabetScopedBranches list →
      PactType.InterfaceAlphabetScoped
        (parallelTypeBranchesSelectingWithin alphabet selected list) := by
    intro list
    induction list with
    | nil =>
        intro _ _
        simp [parallelTypeBranchesSelectingWithin,
          PactType.InterfaceAlphabetScoped]
    | cons head rest ih =>
        rcases head with ⟨action, body⟩
        intro hSub hList
        simp only [PactType.InterfaceAlphabetScopedBranches] at hList
        have hBodySub : PactType.ParallelInterfaces body ⊆
            PactType.ParallelBranchInterfaces branches := by
          refine Finset.Subset.trans ?_ hSub
          simp only [PactType.ParallelBranchInterfaces]
          exact Finset.subset_union_left
        have hRestSub : PactType.ParallelBranchInterfaces rest ⊆
            PactType.ParallelBranchInterfaces branches := by
          refine Finset.Subset.trans ?_ hSub
          simp only [PactType.ParallelBranchInterfaces]
          exact Finset.subset_union_right
        have hBodyScoped : PactType.InterfaceAlphabetScoped
            (body.reannotate alphabet) :=
          PactType.reannotate_interfaceAlphabetScoped body alphabet hList.1
            (fun act hAct hIn => hAvoid act hAct (hBodySub hIn))
        have hSelectedLeaf : PactType.InterfaceAlphabetScoped
            (selectedTypeBranchAt alphabet (action, body)) := by
          simp only [selectedTypeBranchAt, PactType.InterfaceAlphabetScoped,
            PactType.ParallelInterfaces, PactType.reannotate_parallelInterfaces]
          refine ⟨?_, trivial, hBodyScoped⟩
          simpa using hDisj (PactType.ParallelInterfaces body) hBodySub
        have hSingleLeaf : PactType.InterfaceAlphabetScoped
            (singletonTypeXOfferAt alphabet (action, body)) := by
          simp only [singletonTypeXOfferAt, PactType.InterfaceAlphabetScoped,
            PactType.InterfaceAlphabetScopedBranches,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces,
            PactType.reannotate_parallelInterfaces]
          refine ⟨?_, trivial, hBodyScoped, trivial⟩
          simpa using hDisj (PactType.ParallelInterfaces body) hBodySub
        have hHeadInterfaces : ∀ leafInterfaces : Finset MessageId,
            leafInterfaces ⊆ PactType.ParallelInterfaces body →
            ∀ tailInterfaces : Finset MessageId,
            tailInterfaces ⊆ PactType.ParallelBranchInterfaces rest →
            Disjoint (PactTypeAlphabet.messageIds alphabet)
              (∅ ∪ leafInterfaces ∪ tailInterfaces) := by
          intro leafInterfaces hLeafSub tailInterfaces hTailSub
          refine hDisj _ ?_
          intro msg hMsg
          rcases Finset.mem_union.mp hMsg with hMsg | hMsg
          · rcases Finset.mem_union.mp hMsg with hMsg | hMsg
            · exact absurd hMsg (Finset.notMem_empty msg)
            · exact hBodySub (hLeafSub hMsg)
          · exact hRestSub (hTailSub hMsg)
        cases rest with
        | nil =>
            by_cases hSel : (action, body) = selected
            · simpa only [parallelTypeBranchesSelectingWithin, if_pos hSel]
                using hSel ▸ hSelectedLeaf
            · simpa only [parallelTypeBranchesSelectingWithin, if_neg hSel]
                using hSingleLeaf
        | cons next tail =>
            have hRestScoped : PactType.InterfaceAlphabetScoped
                (parallelTypeBranchesWithin alphabet (next :: tail)) :=
              parallelTypeBranchesWithin_interfaceAlphabetScoped
                (branchesAll := branches) alphabet hAvoid (next :: tail)
                hRestSub hList.2
            by_cases hSel : (action, body) = selected
            · rw [parallelTypeBranchesSelectingWithin, if_pos hSel]
              simp only [PactType.InterfaceAlphabetScoped]
              refine ⟨?_, hSel ▸ hSelectedLeaf, hRestScoped⟩
              rw [selectedTypeBranchAt, PactType.ParallelInterfaces,
                parallelTypeBranchesWithin_parallelInterfaces (next :: tail)
                  alphabet]
              refine hHeadInterfaces _ ?_ _ (Finset.Subset.refl _)
              simp only [PactType.ParallelInterfaces,
                PactType.reannotate_parallelInterfaces, Finset.empty_union]
              · exact Finset.Subset.refl _
              · exact List.cons_ne_nil _ _
            · rw [parallelTypeBranchesSelectingWithin, if_neg hSel]
              simp only [PactType.InterfaceAlphabetScoped]
              refine ⟨?_, hSingleLeaf, ih hRestSub hList.2⟩
              rw [singletonTypeXOfferAt, PactType.ParallelInterfaces,
                parallelTypeBranchesSelectingWithin_parallelInterfaces selected
                  (next :: tail) alphabet]
              refine hHeadInterfaces _ ?_ _ (Finset.Subset.refl _)
              simp only [PactType.ParallelInterfaces,
                PactType.ParallelBranchInterfaces,
                PactType.reannotate_parallelInterfaces, Finset.union_empty,
                Finset.empty_union]
              · exact Finset.Subset.refl _
              · exact List.cons_ne_nil _ _
  cases branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.InterfaceAlphabetScoped]
  | cons head rest =>
      exact hWithin (head :: rest) (Finset.Subset.refl _) hScoped

end

end Pact
