import Anvilpp.PactTypes.Correspondence.CorrespondenceCore

/-!
# Interface-subset and interface-scoping transport for parallelTypeBranches(Selecting)
-/

namespace Pact

noncomputable section

private theorem mem_parallelBranchInterfaces_iff_exists
    (message : MessageId) : ∀ branches,
    message ∈ PactType.ParallelBranchInterfaces branches ↔
      ∃ entry ∈ branches, message ∈ entry.2.ParallelInterfaces := by
  intro branches
  induction branches with
  | nil => simp [PactType.ParallelBranchInterfaces]
  | cons entry rest ih =>
      rcases entry with ⟨action, processType⟩
      simp [PactType.ParallelBranchInterfaces, ih]

private theorem parallelInterfaces_subset_parallelBranchInterfaces_of_mem
    {branches : List (BareMessage × PactType)}
    {entry : BareMessage × PactType} (hEntry : entry ∈ branches) :
    entry.2.ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  intro message hMessage
  exact (mem_parallelBranchInterfaces_iff_exists message branches).mpr
    ⟨entry, hEntry, hMessage⟩

theorem parallelTypeBranches_parallelInterfaces_subset
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranches branches).ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
            using Finset.union_subset_union (fun _ h => h) ih

theorem parallelTypeBranches_interfaceScoped
    (branches : List (BareMessage × PactType))
    (hScoped : PactType.InterfaceScopedBranches branches) :
    PactType.InterfaceScoped (parallelTypeBranches branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.InterfaceScoped]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.InterfaceScopedBranches] at hScoped
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.InterfaceScoped, PactType.InterfaceScopedBranches]
            using hScoped.1
      | cons next tail =>
          have hRest := ih hScoped.2
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
            hScoped.1, hRest]

theorem parallelTypeBranchesSelecting_parallelInterfaces_subset
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranchesSelecting selected branches).ParallelInterfaces ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.ParallelInterfaces,
        PactType.ParallelBranchInterfaces]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · rw [show parallelTypeBranchesSelecting selected
                [(action, processType)] = selectedTypeBranch (action, processType)
              by simp [parallelTypeBranchesSelecting, hEq]]
            simp [selectedTypeBranch, PactType.ParallelInterfaces,
              PactType.ParallelBranchInterfaces]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            rw [show parallelTypeBranchesSelecting (action, processType)
                ((action, processType) :: next :: tail) =
                .par (selectedTypeBranch (action, processType))
                  (parallelTypeBranches (next :: tail)) ∅
              by simp [parallelTypeBranchesSelecting]]
            simp only [PactType.ParallelInterfaces, selectedTypeBranch,
              PactType.ParallelBranchInterfaces, Finset.empty_union]
            exact Finset.union_subset_union (fun _ h => h)
              (parallelTypeBranches_parallelInterfaces_subset (next :: tail))
          · simpa [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.ParallelInterfaces, PactType.ParallelBranchInterfaces]
              using Finset.union_subset_union (fun _ h => h) ih

theorem parallelTypeBranchesSelecting_interfaceScoped
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hScoped : PactType.InterfaceScopedBranches branches) :
    PactType.InterfaceScoped (parallelTypeBranchesSelecting selected branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, PactType.InterfaceScoped]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.InterfaceScopedBranches] at hScoped
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hEq, selectedTypeBranch,
              PactType.InterfaceScoped, hScoped.1]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
              hScoped.1]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.InterfaceScoped, hScoped.1,
              parallelTypeBranches_interfaceScoped (next :: tail) hScoped.2]
          · have hRest := ih hScoped.2
            simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.InterfaceScoped, PactType.InterfaceScopedBranches,
              hScoped.1, hRest]

end

end Pact
