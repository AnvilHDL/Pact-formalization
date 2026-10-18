import Anvilpp.PactTypes.Proofs.Syntax.TypeDynamicsCoreLemmas

namespace Pact

noncomputable section

open Classical

/-- A selected index identifies a branch satisfying the selection predicate. -/
theorem mem_branchIndices {α : Type} (predicate : α → Prop) (branches : List α)
    (index : Nat) :
    index ∈ branchIndices predicate branches ↔
      ∃ branch, (branch, index) ∈ branches.zipIdx ∧ predicate branch := by
  simp only [branchIndices, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨branch, index⟩, ⟨hMem, hPredicate⟩, rfl⟩
    exact ⟨branch, hMem, hPredicate⟩
  · rintro ⟨branch, hMem, hPredicate⟩
    exact ⟨(branch, index), ⟨hMem, hPredicate⟩, rfl⟩

/-- Mapping branches preserves their indices. -/
theorem branchIndices_map {α β : Type} (predicate : β → Prop) (f : α → β)
    (branches : List α) :
    branchIndices predicate (branches.map f) =
      branchIndices (fun branch => predicate (f branch)) branches := by
  simp [branchIndices, List.zipIdx_map, List.filter_map, List.map_map, Function.comp_def]

/-- A branch index is within the source list. -/
theorem branchIndices_subset_range {α : Type} (predicate : α → Prop)
    (branches : List α) : branchIndices predicate branches ⊆ Finset.range branches.length := by
  intro index hIndex
  obtain ⟨branch, hMem, _⟩ := (mem_branchIndices predicate branches index).mp hIndex
  exact Finset.mem_range.mpr (List.mem_zipIdx' hMem).1

/-- Selection is nonempty exactly when some branch satisfies its predicate. -/
theorem branchIndices_nonempty {α : Type} (predicate : α → Prop) (branches : List α) :
    (branchIndices predicate branches).Nonempty ↔ ∃ branch ∈ branches, predicate branch := by
  constructor
  · rintro ⟨index, hIndex⟩
    obtain ⟨branch, hMem, hPredicate⟩ := (mem_branchIndices predicate branches index).mp hIndex
    exact ⟨branch, List.fst_mem_of_mem_zipIdx hMem, hPredicate⟩
  · rintro ⟨branch, hMem, hPredicate⟩
    have hIndexed : branch ∈ branches.zipIdx.map Prod.fst := by simpa using hMem
    obtain ⟨⟨branch', index⟩, hIndex, hEq⟩ := List.mem_map.mp hIndexed
    cases hEq
    exact ⟨index, (mem_branchIndices predicate branches index).mpr ⟨branch', hIndex, hPredicate⟩⟩

/-- The compiler's selections are precisely the nonempty subsets of branch indices. -/
@[simp] theorem mem_conjunctiveSelections (count : Nat) (selected : Finset Nat) :
    selected ∈ conjunctiveSelections count ↔
      selected.Nonempty ∧ selected ⊆ Finset.range count := by
  simp [conjunctiveSelections, Finset.nonempty_iff_ne_empty]

/-- Every nonempty enabled set has a compiled residual copy. -/
theorem typeEnabledBranches_mem_selections (env : TypeEnvironment)
    (branches : List (BareMessage × PactType))
    (hEnabled : (typeEnabledBranches env branches).Nonempty) :
    typeEnabledBranches env branches ∈ conjunctiveSelections branches.length :=
  (mem_conjunctiveSelections _ _).mpr
    ⟨hEnabled, branchIndices_subset_range _ _⟩

/-- The absence of enabled indices is the usual no-immediate-head condition. -/
theorem typeEnabledBranches_eq_empty_iff (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) :
    typeEnabledBranches env branches = ∅ ↔ TypeNoImmediateBranch env branches := by
  rw [typeEnabledBranches, ← Finset.not_nonempty_iff_eq_empty, branchIndices_nonempty]
  simp only [TypeBranchEnabled, TypeNoImmediateBranch,
    Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, typeBranchNeeds,
    List.mem_toFinset, List.mem_map]
  aesop

/-- Clock environments enable no conjunctive communication head. -/
@[simp] theorem typeEnabledBranches_tock (branches : List (BareMessage × PactType)) :
    typeEnabledBranches TypeEnvironment.tock branches = ∅ := by
  rw [typeEnabledBranches_eq_empty_iff]
  simp [TypeNoImmediateBranch, TypeEnvironment.tock]

/-- Every residual retains the enclosing alphabet, including the empty product. -/
@[simp] theorem parallelTypeBranchesFiringFrom_alphabet (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branches : List (BareMessage × PactType)) :
    (parallelTypeBranchesFiringFrom alphabet selected index branches).alphabet = alphabet := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesFiringFrom]
          split
          · exact PactType.reannotate_alphabet _ _
          · rfl
      | cons next rest => rfl

@[simp] theorem parallelTypeBranchesFiring_alphabet (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (branches : List (BareMessage × PactType)) :
    (parallelTypeBranchesFiring alphabet selected branches).alphabet = alphabet :=
  parallelTypeBranchesFiringFrom_alphabet alphabet selected 0 branches

@[simp] theorem parallelProcessBranchesFiringFrom_alphabet (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (values : Nat → Bool) (index : Nat) (branches : List ChoiceBranch) :
    (parallelProcessBranchesFiringFrom alphabet selected values index branches).alphabet =
      alphabet := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      cases rest with
      | nil =>
          simp only [parallelProcessBranchesFiringFrom]
          split
          · exact Proc.alphabet_reannotate _ _
          · rfl
      | cons next rest => rfl

@[simp] theorem parallelProcessBranchesFiring_alphabet (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (values : Nat → Bool) (branches : List ChoiceBranch) :
    (parallelProcessBranchesFiring alphabet selected values branches).alphabet = alphabet :=
  parallelProcessBranchesFiringFrom_alphabet alphabet selected values 0 branches

end

end Pact
