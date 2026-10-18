import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResiduals
import Anvilpp.PactTypes.Proofs.Syntax.PactTypeFutureOffersLemmas

namespace Pact

noncomputable section

open Classical

/-- A consumed head contributes only its continuation; an optional head remains in the menu. -/
theorem mem_typeFutureOffers_conjunctiveFactor (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branch : BareMessage × PactType)
    (hAlphabet : branch.2.alphabet = alphabet) (hWF : branch.2.AlphabetWellFormed)
    (action : BareMessage) :
    action ∈ typeFutureOffers
        (if index ∈ selected then branch.2.reannotate alphabet
         else singletonTypeXOfferAt alphabet branch) ↔
      action ∈ alphabet.actions ∧
        (action ∈ typeFutureOffers branch.2 ∨ (index ∉ selected ∧ action = branch.1)) := by
  by_cases hSelected : index ∈ selected
  · rw [if_pos hSelected, ← hAlphabet, PactType.reannotate_own_alphabet _ hWF]
    have hBound := typeFutureOffers_subset_alphabet branch.2 hWF
    simp only [hSelected, not_true_eq_false, false_and, or_false]
    exact ⟨fun h => ⟨hBound h, h⟩, And.right⟩
  · rw [if_neg hSelected, typeFutureOffers_singletonTypeXOfferAt alphabet branch hAlphabet hWF]
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
      hSelected, not_false_eq_true, true_and]
    tauto

/-- A subset residual retains every continuation menu and exactly the unconsumed heads. -/
theorem mem_typeFutureOffers_parallelTypeBranchesFiringFrom (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) (action : BareMessage) :
    action ∈ typeFutureOffers (parallelTypeBranchesFiringFrom alphabet selected index branches) ↔
      action ∈ alphabet.actions ∧ ∃ entry ∈ branches.zipIdx index,
        action ∈ typeFutureOffers entry.1.2 ∨
          (entry.2 ∉ selected ∧ action = entry.1.1) := by
  induction branches generalizing index with
  | nil => simp [parallelTypeBranchesFiringFrom, typeFutureOffers, typeFutureOffersFuel]
  | cons branch rest ih =>
      have hHead := mem_typeFutureOffers_conjunctiveFactor alphabet selected index branch
        (hAlphabet branch (by simp)) (hWF branch (by simp)) action
      cases rest with
      | nil => simpa [parallelTypeBranchesFiringFrom] using hHead
      | cons next rest =>
          rw [parallelTypeBranchesFiringFrom, typeFutureOffers_parallel]
          simp only [hideTypeOffers, Finset.mem_filter, Finset.notMem_empty,
            not_false_eq_true, and_true, Finset.mem_union]
          rw [hHead, ih (index + 1) (fun b hb => hAlphabet b (by simp [hb]))
            (fun b hb => hWF b (by simp [hb]))]
          conv_rhs => rw [List.zipIdx_cons]
          simp only [List.mem_cons, exists_eq_or_imp]
          constructor
          · rintro (⟨hDeclared, hHead⟩ | ⟨hDeclared, hRest⟩)
            · exact ⟨hDeclared, Or.inl hHead⟩
            · exact ⟨hDeclared, Or.inr hRest⟩
          · rintro ⟨hDeclared, hHead | hRest⟩
            · exact Or.inl ⟨hDeclared, hHead⟩
            · exact Or.inr ⟨hDeclared, hRest⟩

theorem mem_typeFutureOffers_parallelTypeBranchesFiring (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) (action : BareMessage) :
    action ∈ typeFutureOffers (parallelTypeBranchesFiring alphabet selected branches) ↔
      action ∈ alphabet.actions ∧ ∃ entry ∈ branches.zipIdx,
        action ∈ typeFutureOffers entry.1.2 ∨
          (entry.2 ∉ selected ∧ action = entry.1.1) :=
  mem_typeFutureOffers_parallelTypeBranchesFiringFrom alphabet selected 0 branches
    hAlphabet hWF action

/-- Consuming every head leaves exactly the union of the continuation menus. -/
theorem mem_typeFutureOffers_parallelTypeBranchesFiring_all (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) (action : BareMessage) :
    action ∈ typeFutureOffers
        (parallelTypeBranchesFiring alphabet (Finset.range branches.length) branches) ↔
      ∃ branch ∈ branches, action ∈ typeFutureOffers branch.2 := by
  rw [mem_typeFutureOffers_parallelTypeBranchesFiring alphabet _ branches hAlphabet hWF]
  constructor
  · rintro ⟨_, entry, hMem, hFuture | ⟨hNotSelected, _⟩⟩
    · exact ⟨entry.1, List.fst_mem_of_mem_zipIdx hMem, hFuture⟩
    · exact False.elim (hNotSelected (Finset.mem_range.mpr (List.mem_zipIdx' hMem).1))
  · rintro ⟨branch, hMem, hFuture⟩
    have hIndexed : branch ∈ branches.zipIdx.map Prod.fst := by simpa using hMem
    obtain ⟨entry, hEntry, hEq⟩ := List.mem_map.mp hIndexed
    refine ⟨?_, entry, hEntry, Or.inl (hEq.symm ▸ hFuture)⟩
    rw [← hAlphabet branch hMem]
    exact typeFutureOffers_subset_alphabet branch.2 (hWF branch hMem) hFuture

/-- A consumed factor completes when its continuation does; an optional factor may default. -/
theorem conjunctiveFactor_canComplete (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branch : BareMessage × PactType)
    (hAlphabet : branch.2.alphabet = alphabet) (hWF : branch.2.AlphabetWellFormed) :
    (if index ∈ selected then branch.2.reannotate alphabet
     else singletonTypeXOfferAt alphabet branch).CanCompleteDeclared = true ↔
      (index ∈ selected → branch.2.CanCompleteDeclared = true) := by
  by_cases hSelected : index ∈ selected
  · rw [if_pos hSelected, ← hAlphabet, PactType.reannotate_own_alphabet _ hWF]
    simp [hSelected]
  · rw [if_neg hSelected, singletonTypeXOfferAt, PactType.canCompleteDeclared_eq]
    dsimp only
    simp [PactType.canCompleteDeclared_eq (.skip alphabet), hSelected]

/-- Completion of a residual requires completion of every consumed continuation. -/
theorem parallelTypeBranchesFiringFrom_canComplete (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (index : Nat) (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) :
    (parallelTypeBranchesFiringFrom alphabet selected index branches).CanCompleteDeclared = true ↔
      ∀ entry ∈ branches.zipIdx index, entry.2 ∈ selected →
        entry.1.2.CanCompleteDeclared = true := by
  induction branches generalizing index with
  | nil =>
      rw [parallelTypeBranchesFiringFrom, PactType.canCompleteDeclared_eq]
      simp
  | cons branch rest ih =>
      have hHead := conjunctiveFactor_canComplete alphabet selected index branch
        (hAlphabet branch (by simp)) (hWF branch (by simp))
      cases rest with
      | nil => simpa [parallelTypeBranchesFiringFrom] using hHead
      | cons next rest =>
          rw [parallelTypeBranchesFiringFrom, PactType.canCompleteDeclared_eq, Bool.and_eq_true]
          rw [hHead, ih (index + 1) (fun b hb => hAlphabet b (by simp [hb]))
            (fun b hb => hWF b (by simp [hb]))]
          conv_rhs => rw [List.zipIdx_cons]
          simp only [List.forall_mem_cons]

/-- A nonempty completing residual supplies a completing branch of the source offer. -/
theorem parallelTypeBranchesFiring_canComplete_branch (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (branches : List (BareMessage × PactType))
    (hSelection : selected ∈ conjunctiveSelections branches.length)
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed)
    (hComplete : (parallelTypeBranchesFiring alphabet selected branches).CanCompleteDeclared = true) :
    ∃ branch ∈ branches, branch.2.CanCompleteDeclared = true := by
  obtain ⟨hNonempty, hBound⟩ := (mem_conjunctiveSelections _ _).mp hSelection
  obtain ⟨index, hIndex⟩ := hNonempty
  have hLt := Finset.mem_range.mp (hBound hIndex)
  have hEntry : (branches[index], index) ∈ branches.zipIdx := by
    simp [List.mk_mem_zipIdx_iff_getElem?]
  exact ⟨branches[index], List.getElem_mem hLt,
    (parallelTypeBranchesFiringFrom_canComplete alphabet selected 0 branches hAlphabet hWF).mp
      hComplete (branches[index], index) hEntry hIndex⟩

/-- The subset family preserves the source offer's optimistic branch-completion test. -/
theorem exists_firing_canComplete_iff (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) :
    (∃ selected ∈ conjunctiveSelections branches.length,
      (parallelTypeBranchesFiring alphabet selected branches).CanCompleteDeclared = true) ↔
      ∃ branch ∈ branches, branch.2.CanCompleteDeclared = true := by
  constructor
  · rintro ⟨selected, hSelection, hComplete⟩
    exact parallelTypeBranchesFiring_canComplete_branch alphabet selected branches hSelection
      hAlphabet hWF hComplete
  · rintro ⟨branch, hMem, hComplete⟩
    have hIndexed : branch ∈ branches.zipIdx.map Prod.fst := by simpa using hMem
    obtain ⟨⟨branch', index⟩, hEntry, hEq⟩ := List.mem_map.mp hIndexed
    cases hEq
    refine ⟨{index}, ?_, ?_⟩
    · rw [mem_conjunctiveSelections]
      exact ⟨Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr
        (Finset.mem_range.mpr (List.mem_zipIdx' hEntry).1)⟩
    · apply (parallelTypeBranchesFiringFrom_canComplete alphabet {index} 0 branches hAlphabet hWF).mpr
      rintro ⟨other, position⟩ hOther hSelected
      have hPosition : position = index := Finset.mem_singleton.mp hSelected
      subst position
      have hSame : other = branch' := Option.some.inj
        ((List.mk_mem_zipIdx_iff_getElem?.mp hOther).symm.trans
          (List.mk_mem_zipIdx_iff_getElem?.mp hEntry))
      exact hSame ▸ hComplete

end

end Pact
