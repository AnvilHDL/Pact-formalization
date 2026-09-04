import Anvilpp.PactTypes.NewCorrespondence.Helpers.NewMainHelpers

/-!
Hop 1 of the guard transport: a residual's declared identifiers are among its
source's.  Split out of `Simultaneous` so that the re-signing transport can use
it without depending on the simultaneous induction.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

theorem branch_subset_parallelBranchInterfaces
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    PactType.ParallelInterfaces branch.2 ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.ParallelBranchInterfaces]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq; exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

/-- Top-level form of the generated child's identifier computation. -/
theorem parallelTypeBranchesSelecting_ownership (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.MessageIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchMessageIds branches ∧
      PactType.MessageActions
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchMessageActions branches ∧
      PactType.ProgressIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchProgressIds branches ∧
      PactType.FairChoiceIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchFairChoiceIds branches := by
  cases branches with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelecting, PactType.MessageActions,
          PactType.ProgressIds, PactType.FairChoiceIds, PactType.MessageIds,
          PactType.BranchMessageActions, PactType.BranchProgressIds,
          PactType.BranchFairChoiceIds, PactType.BranchMessageIds]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_ownershipData alphabet selected
        (branch :: rest)

theorem PactType.reannotate_progressIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.ProgressIds (processType.reannotate alphabet) =
      PactType.ProgressIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.1

theorem PactType.reannotate_fairChoiceIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.FairChoiceIds (processType.reannotate alphabet) =
      PactType.FairChoiceIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.1

theorem PactType.reannotate_messageIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
      PactType.MessageIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).1

theorem PactType.reannotate_messageActions (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.MessageActions (processType.reannotate alphabet) =
      PactType.MessageActions processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.1

theorem parallelTypeBranchesSelecting_parallelInterfaces
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.ParallelInterfaces
        (parallelTypeBranchesSelecting alphabet selected branches) =
      PactType.ParallelBranchInterfaces branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.ParallelInterfaces,
      PactType.ParallelBranchInterfaces]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_parallelInterfaces selected
        (branch :: rest) alphabet

lemma union_subset_union_union {α : Type} [DecidableEq α]
    {XL XR A B R : Finset α} (hL : XL ⊆ A ∪ R) (hR : XR ⊆ B ∪ R) :
    XL ∪ XR ⊆ (A ∪ B) ∪ R := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp (hL h) with h2 | h2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h2)
    · exact Finset.mem_union_right _ h2
  · rcases Finset.mem_union.mp (hR h) with h2 | h2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
    · exact Finset.mem_union_right _ h2

theorem replaceVar_ownership_subset (name : String) (replacement : PactType) :
    ∀ processType : PactType,
      PactType.MessageActions (processType.replaceVar name replacement) ⊆
          PactType.MessageActions processType ∪
            PactType.MessageActions replacement ∧
        PactType.ProgressIds (processType.replaceVar name replacement) ⊆
          PactType.ProgressIds processType ∪ PactType.ProgressIds replacement ∧
        PactType.FairChoiceIds (processType.replaceVar name replacement) ⊆
          PactType.FairChoiceIds processType ∪
            PactType.FairChoiceIds replacement ∧
        PactType.MessageIds (processType.replaceVar name replacement) ⊆
          PactType.MessageIds processType ∪ PactType.MessageIds replacement ∧
        PactType.ParallelInterfaces (processType.replaceVar name replacement) ⊆
          PactType.ParallelInterfaces processType ∪
            PactType.ParallelInterfaces replacement := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BranchMessageActions
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchMessageActions branches ∪
              PactType.MessageActions replacement ∧
          PactType.BranchProgressIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchProgressIds branches ∪
              PactType.ProgressIds replacement ∧
          PactType.BranchFairChoiceIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchFairChoiceIds branches ∪
              PactType.FairChoiceIds replacement ∧
          PactType.BranchMessageIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchMessageIds branches ∪
              PactType.MessageIds replacement ∧
          PactType.ParallelBranchInterfaces
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.ParallelBranchInterfaces branches ∪
              PactType.ParallelInterfaces replacement := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceBranches, PactType.BranchMessageActions,
                PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
                PactType.BranchMessageIds, PactType.ParallelBranchInterfaces]
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
            obtain ⟨hM, hP, hF, hI, hPI⟩ :=
              ih (sizeOf branchType) hBranchSize branchType rfl
            obtain ⟨rM, rP, rF, rI, rPI⟩ := restIH hRestSize
            simp only [PactType.replaceBranches, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.BranchMessageIds, PactType.ParallelBranchInterfaces]
            refine ⟨union_subset_union_union ?_ rM,
              union_subset_union_union hP rP,
              union_subset_union_union hF rF,
              union_subset_union_union ?_ rI,
              union_subset_union_union hPI rPI⟩
            · exact union_subset_union_union Finset.subset_union_left hM
            · exact union_subset_union_union Finset.subset_union_left hI
      cases processType with
      | message a m d =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | progress a p =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | tock a =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | skip a =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | var a other =>
          by_cases hEq : name = other <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceVar, hEq, PactType.MessageActions,
                PactType.ProgressIds, PactType.FairChoiceIds,
                PactType.MessageIds, PactType.ParallelInterfaces]
      | recur a other body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hEq : name = other
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceVar, hEq, PactType.MessageActions,
                PactType.ProgressIds, PactType.FairChoiceIds,
                PactType.MessageIds, PactType.ParallelInterfaces]
          · obtain ⟨hM, hP, hF, hI, hPI⟩ := ih (sizeOf body) hB body rfl
            simp only [PactType.replaceVar, if_neg hEq,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨hM, hP, hF, hI, hPI⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union
              (union_subset_union_union Finset.subset_union_left lF) rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union
              (union_subset_union_union Finset.subset_union_left lPI) rPI⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨eM, eP, eF, eI, ePI⟩ := ih (sizeOf e) hE e rfl
          obtain ⟨bM, bP, bF, bI, bPI⟩ := hBranches bs hBs
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union eM bM,
            union_subset_union_union eP bP,
            union_subset_union_union eF bF,
            union_subset_union_union eI bI,
            union_subset_union_union ePI bPI⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨eM, eP, eF, eI, ePI⟩ := ih (sizeOf e) hE e rfl
          obtain ⟨bM, bP, bF, bI, bPI⟩ := hBranches bs hBs
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union eM bM,
            union_subset_union_union eP bP,
            union_subset_union_union eF bF,
            union_subset_union_union eI bI,
            union_subset_union_union ePI bPI⟩

/-- Hop 1 of the guard transport: a residual's declared identifiers are among
its source's.  The five sets `LabelOwned` reads are bundled into one induction,
since they behave alike at every clause. -/
theorem relationMembership_ownership_subset :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      PactType.MessageActions residual ⊆ PactType.MessageActions source ∧
        PactType.ProgressIds residual ⊆ PactType.ProgressIds source ∧
        PactType.FairChoiceIds residual ⊆ PactType.FairChoiceIds source ∧
        PactType.MessageIds residual ⊆ PactType.MessageIds source ∧
        PactType.ParallelInterfaces residual ⊆
          PactType.ParallelInterfaces source := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hRelated
      cases source with
      | skip a =>
          obtain ⟨hR, -⟩ := relationMembership_skip_cases a hRelated
          subst hR
          exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
            Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
      | var a name =>
          obtain ⟨hR, -⟩ := relationMembership_var_cases a name hRelated
          subst hR
          exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
            Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
      | message a m d =>
          rcases relationMembership_message_cases a m d hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | tock a =>
          rcases relationMembership_tock_cases a hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | progress a p =>
          rcases relationMembership_progress_cases a p hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | choice a l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_choice_cases a l r hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨q, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | fairChoice a bid l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_fairChoice_cases a bid l r hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨q, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans (Finset.subset_union_right.trans Finset.subset_union_left),
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | seq a l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_seq_cases a l r hRelated with
            ⟨q1, ρ, hEntry, hChild, -⟩ | ⟨q2, -, hChild⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl ρ q1 hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨Finset.union_subset_union m (Finset.Subset.refl _),
              Finset.union_subset_union p (Finset.Subset.refl _),
              Finset.union_subset_union f (Finset.Subset.refl _),
              Finset.union_subset_union mi (Finset.Subset.refl _),
              Finset.union_subset_union pi (Finset.Subset.refl _)⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q2 hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | recur a name body =>
          have hB : typeCompilationFuel body < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_recur_cases a name body hRelated with
            hRoot | ⟨q, ρ, hEntry, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hB body rfl ρ q hChild
            obtain ⟨sm, sp, sf, smi, spi⟩ :=
              replaceVar_ownership_subset name (.recur a name body) ρ
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces] at m p f mi pi ⊢
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro x hx
              rcases Finset.mem_union.mp (sm hx) with h | h
              · exact m h
              · simpa [PactType.MessageActions] using h
            · intro x hx
              rcases Finset.mem_union.mp (sp hx) with h | h
              · exact p h
              · simpa [PactType.ProgressIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (sf hx) with h | h
              · exact f h
              · simpa [PactType.FairChoiceIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (smi hx) with h | h
              · exact mi h
              · simpa [PactType.MessageIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (spi hx) with h | h
              · exact pi h
              · simpa [PactType.ParallelInterfaces] using h
      | par a l r i =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hLre : typeCompilationFuel (l.reannotate a) < n := by
            rw [typeCompilationFuel_reannotate]; exact hL
          have hRre : typeCompilationFuel (r.reannotate a) < n := by
            rw [typeCompilationFuel_reannotate]; exact hR
          rcases relationMembership_par_cases a l r i hRelated with
            ⟨q1, q2, ρl, ρr, hEntry, hLeft, hRight⟩ |
            ⟨q1, ρl, hEntry, hLeft, -⟩ | ⟨q2, ρr, hEntry, hRight, -⟩ | hFinal
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨lm, lp, lf, lmi, lpi⟩ := ih _ hL l rfl ρl q1 hLeft
            obtain ⟨rm, rp, rf, rmi, rpi⟩ := ih _ hR r rfl ρr q2 hRight
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨Finset.union_subset (lm.trans Finset.subset_union_left)
                (rm.trans Finset.subset_union_right),
              Finset.union_subset (lp.trans Finset.subset_union_left)
                (rp.trans Finset.subset_union_right),
              Finset.union_subset (lf.trans Finset.subset_union_left)
                (rf.trans Finset.subset_union_right),
              Finset.union_subset (lmi.trans Finset.subset_union_left)
                (rmi.trans Finset.subset_union_right),
              Finset.union_subset_union
                (Finset.union_subset_union (Finset.Subset.refl _) lpi) rpi⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hLre (l.reannotate a) rfl _ q1 hLeft
            rw [PactType.reannotate_messageActions] at m
            rw [PactType.reannotate_progressIds] at p
            rw [PactType.reannotate_fairChoiceIds] at f
            rw [PactType.reannotate_messageIds] at mi
            rw [PactType.reannotate_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans (Finset.subset_union_right.trans
                Finset.subset_union_left)⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hRre (r.reannotate a) rfl _ q2 hRight
            rw [PactType.reannotate_messageActions] at m
            rw [PactType.reannotate_progressIds] at p
            rw [PactType.reannotate_fairChoiceIds] at f
            rw [PactType.reannotate_messageIds] at mi
            rw [PactType.reannotate_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
          · injection hFinal with hRes hStateEq
            subst hRes
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | xoffer a e bs =>
          have hE : typeCompilationFuel e < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_xoffer_cases a e bs hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨idx, action, branchType, q, hGet, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hE e rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · have hMem : (action, branchType) ∈ bs := List.mem_of_getElem? hGet
            have hBF : typeCompilationFuel branchType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel bs :=
                typeCompilationFuel_le_typeBranchCompilationFuel bs
                  (action, branchType) hMem
              have hMax : typeBranchCompilationFuel bs ≤
                  max (typeCompilationFuel e) (typeBranchCompilationFuel bs) :=
                le_max_right _ _
              omega
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hBF branchType rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            refine ⟨(m.trans ?_).trans Finset.subset_union_right,
              (p.trans ?_).trans Finset.subset_union_right,
              (f.trans ?_).trans Finset.subset_union_right,
              (mi.trans ?_).trans Finset.subset_union_right,
              (pi.trans ?_).trans Finset.subset_union_right⟩
            · exact Finset.subset_union_right.trans
                (branch_subset_branchMessageActions hMem)
            · exact branch_subset_branchProgressIds hMem
            · exact branch_subset_branchFairChoiceIds hMem
            · exact Finset.subset_union_right.trans
                (branch_subset_branchMessageIds hMem)
            · exact branch_subset_parallelBranchInterfaces hMem
      | offer a e bs =>
          have hE : typeCompilationFuel e < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_offer_cases a e bs hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨idx, selected, q, hGet, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hE e rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · have hGF : typeCompilationFuel
                (parallelTypeBranchesSelecting a selected bs) < n := by
              rw [← hFuel, typeCompilationFuel_parallelTypeBranchesSelecting]
              simp only [typeCompilationFuel]; omega
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hGF
              (parallelTypeBranchesSelecting a selected bs) rfl residual q hChild
            obtain ⟨gI, gm, gp, gf⟩ :=
              parallelTypeBranchesSelecting_ownership a selected bs
            rw [gm] at m; rw [gp] at p; rw [gf] at f; rw [gI] at mi
            rw [parallelTypeBranchesSelecting_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩

end

end Pact
