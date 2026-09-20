import Anvilpp.ProofHelpers.CompatibilitySoundness

namespace Pact

noncomputable section

open Classical

/-! ## Completion and menus under re-signing -/

/-- Re-signing rewrites branch bodies only, so a branch list keeps its shape. -/
lemma reannotateBranches_map (target : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) :
    PactType.reannotateBranches target branches =
      branches.map fun branch => (branch.1, branch.2.reannotate target) := by
  induction branches with
  | nil => rw [PactType.reannotateBranches]; rfl
  | cons branch rest ih =>
      rcases branch with ⟨action, body⟩
      rw [PactType.reannotateBranches, ih]
      rfl

lemma reannotateOfferBranches_map (target : PactTypeAlphabet)
    (seen : Finset BareMessage) (branches : List (BareMessage × PactType)) :
    PactType.reannotateOfferBranches target seen branches =
      branches.map fun branch => (branch.1, branch.2.reannotate target) := by
  induction branches with
  | nil => rw [PactType.reannotateOfferBranches]; rfl
  | cons branch rest ih =>
      rcases branch with ⟨action, body⟩
      rw [PactType.reannotateOfferBranches, ih]
      rfl

/-- The optimistic completion test is invariant under re-signing. -/
theorem typeCanCompleteThisCycleFuel_reannotate :
    ∀ (fuel : Nat) (processType : PactType) (target : PactTypeAlphabet),
      typeCanCompleteThisCycleFuel fuel (processType.reannotate target) =
        typeCanCompleteThisCycleFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel ih =>
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (target : PactTypeAlphabet),
          (branches.map fun branch => (branch.1, branch.2.reannotate target)).any
              (fun branch => typeCanCompleteThisCycleFuel fuel branch.2) =
            branches.any fun branch => typeCanCompleteThisCycleFuel fuel branch.2 := by
        intro branches target
        induction branches with
        | nil => rfl
        | cons branch rest ihRest =>
            simp only [List.map_cons, List.any_cons, ihRest, ih]
      intro processType target
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel]
      | recur alphabet name body =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, ih]
      | choice alphabet left right | fairChoice alphabet bid left right
      | seq alphabet left right =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, ih]
      | par alphabet left right interface =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, ih]
      | xoffer alphabet elseType branches =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, ih,
            reannotateBranches_map, hBranches]
      | offer alphabet elseType branches =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, ih,
            reannotateOfferBranches_map, hBranches]

/-- `ParallelCompatible` makes the parent alphabet a subset of either child's. -/
lemma parent_actions_subset_left {parent left right : PactTypeAlphabet}
    {interface : Interface}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface) :
    parent.actions ⊆ left.actions := by
  rw [← hCompat.parent_eq_left]
  intro action hMem
  exact (Finset.mem_filter.mp hMem).1

lemma parent_actions_subset_right {parent left right : PactTypeAlphabet}
    {interface : Interface}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface) :
    parent.actions ⊆ right.actions := by
  rw [← hCompat.parent_eq_right]
  intro action hMem
  exact (Finset.mem_filter.mp hMem).1

/-- Outside the interface, the projected child alphabet agrees with the new
boundary alphabet. -/
lemma mem_projectParallel_of_not_interface {parent child : PactTypeAlphabet}
    {interface : Interface} {action : BareMessage} (hAction : action.1 ∉ interface) :
    action ∈ (PactTypeAlphabet.projectParallel parent child interface).actions ↔
      action ∈ parent.actions := by
  simp only [PactTypeAlphabet.projectParallel, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨-, hIn⟩ | hParent)
    · exact absurd hIn hAction
    · exact hParent
  · exact fun hParent => Or.inr hParent

lemma branchesAlphabetWellFormed_mem {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches) :
    ∀ branch ∈ branches, branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed := by
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      intro branch hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact ⟨hBranches.1, hBranches.2.1⟩
      · exact ih hBranches.2.2 branch hTail

lemma offerBranchesWellFormed_mem {alphabet : PactTypeAlphabet}
    {seen : Finset BareMessage} {branches : List (BareMessage × PactType)}
    (hBranches : PactType.OfferBranchesWellFormed alphabet seen branches) :
    ∀ branch ∈ branches, branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed := by
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.OfferBranchesWellFormed] at hBranches
      intro branch hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact ⟨hBranches.1, hBranches.2.1⟩
      · exact ih hBranches.2.2 branch hTail

/-- Intersection distributes over the offer menu fold. -/
lemma foldl_menu_reannotate (fuel : Nat) (target : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seedResigned seed : Finset BareMessage),
      (∀ branch ∈ branches,
        typeFutureOffersFuel fuel (branch.2.reannotate target) =
          typeFutureOffersFuel fuel branch.2 ∩ target.actions) →
      seedResigned ∩ target.actions = seed ∩ target.actions →
      ((branches.map fun branch => (branch.1, branch.2.reannotate target)).foldl
          (fun offers branch => offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
          seedResigned) ∩ target.actions =
        (branches.foldl
          (fun offers branch => offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
          seed) ∩ target.actions := by
  intro branches
  induction branches with
  | nil => intro seedResigned seed _ hSeed; simpa using hSeed
  | cons branch rest ih =>
      intro seedResigned seed hAll hSeed
      simp only [List.map_cons, List.foldl_cons]
      refine ih _ _ (fun b hb => hAll b (List.mem_cons_of_mem _ hb)) ?_
      have hBranch := hAll branch (List.mem_cons_self ..)
      have hSeedPt := Finset.ext_iff.mp hSeed
      simp only [Finset.mem_inter] at hSeedPt
      rw [hBranch]
      ext action
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
      have := hSeedPt action
      tauto

/-- Re-signing projects the future menu. -/
theorem typeFutureOffersFuel_reannotate :
    ∀ (fuel : Nat) (processType : PactType) (target : PactTypeAlphabet),
      processType.AlphabetWellFormed →
      target.actions ⊆ processType.alphabet.actions →
      typeFutureOffersFuel fuel (processType.reannotate target) =
        typeFutureOffersFuel fuel processType ∩ target.actions := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; simp [typeFutureOffersFuel]
  | succ fuel ih =>
      intro processType target hWF hSubset
      cases processType with
      | message alphabet msg dir =>
          simp only [PactType.alphabet] at hSubset
          simp only [PactType.reannotate, typeFutureOffersFuel]
          by_cases hTarget : (msg, dir) ∈ target.actions
          · rw [if_pos hTarget, if_pos (hSubset hTarget)]
            ext action; simp [hTarget]
          · rw [if_neg hTarget]
            by_cases hParent : (msg, dir) ∈ alphabet.actions
            · rw [if_pos hParent]; ext action; simp [hTarget]
            · rw [if_neg hParent]; simp
      | progress _ _ | tock _ | skip _ | var _ _ =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, typeFutureOffersFuel]
          exact ih body target hWF.2.2 (by rw [hWF.2.1]; exact hSubset)
      | choice alphabet left right | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, typeFutureOffersFuel,
            ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hSubset),
            ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hSubset)]
          exact (Finset.union_inter_distrib_right _ _ _).symm
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, typeFutureOffersFuel,
            typeCanCompleteThisCycleFuel_reannotate,
            ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hSubset),
            ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hSubset)]
          split
          · exact (Finset.union_inter_distrib_right _ _ _).symm
          · rfl
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          obtain ⟨hAlpha, hCompat, hLeft, hRight⟩ := hWF
          have hLeftSub : (PactTypeAlphabet.projectParallel target left.alphabet
              interface).actions ⊆ left.alphabet.actions := by
            intro action hMem
            simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
              Finset.mem_filter] at hMem
            rcases hMem with ⟨hIn, -⟩ | hParent
            · exact hIn
            · exact parent_actions_subset_left hCompat (hSubset hParent)
          have hRightSub : (PactTypeAlphabet.projectParallel target right.alphabet
              interface).actions ⊆ right.alphabet.actions := by
            intro action hMem
            simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
              Finset.mem_filter] at hMem
            rcases hMem with ⟨hIn, -⟩ | hParent
            · exact hIn
            · exact parent_actions_subset_right hCompat (hSubset hParent)
          simp only [PactType.reannotate, typeFutureOffersFuel,
            ih left _ hLeft hLeftSub, ih right _ hRight hRightSub]
          ext action
          simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_inter,
            Finset.mem_union]
          constructor
          · rintro ⟨hMem, hHide⟩
            refine ⟨⟨?_, hHide⟩, ?_⟩
            · rcases hMem with ⟨hIn, -⟩ | ⟨hIn, -⟩
              · exact Or.inl hIn
              · exact Or.inr hIn
            · rcases hMem with ⟨-, hIn⟩ | ⟨-, hIn⟩
              · exact (mem_projectParallel_of_not_interface hHide).mp hIn
              · exact (mem_projectParallel_of_not_interface hHide).mp hIn
          · rintro ⟨⟨hMem, hHide⟩, hTarget⟩
            refine ⟨?_, hHide⟩
            rcases hMem with hIn | hIn
            · exact Or.inl ⟨hIn, (mem_projectParallel_of_not_interface hHide).mpr hTarget⟩
            · exact Or.inr ⟨hIn, (mem_projectParallel_of_not_interface hHide).mpr hTarget⟩
      | xoffer alphabet elseType branches =>
          simp only [PactType.alphabet] at hSubset
          simp only [PactType.AlphabetWellFormed] at hWF
          obtain ⟨hAlpha, hElseAlpha, hElse, hBranches⟩ := hWF
          have hElseEq := ih elseType target hElse (by rw [hElseAlpha]; exact hSubset)
          have hAll : ∀ branch ∈ branches,
              typeFutureOffersFuel fuel (branch.2.reannotate target) =
                typeFutureOffersFuel fuel branch.2 ∩ target.actions := by
            intro branch hMem
            obtain ⟨hEq, hWFBranch⟩ := branchesAlphabetWellFormed_mem hBranches branch hMem
            exact ih branch.2 target hWFBranch (by rw [hEq]; exact hSubset)
          simp only [PactType.reannotate, typeFutureOffersFuel, reannotateBranches_map]
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hSubset]
          exact foldl_menu_reannotate fuel target branches _ _ hAll
            (by rw [hElseEq, Finset.inter_assoc, Finset.inter_self])
      | offer alphabet elseType branches =>
          simp only [PactType.alphabet] at hSubset
          simp only [PactType.AlphabetWellFormed] at hWF
          obtain ⟨hAlpha, hElseAlpha, hElse, hBranches⟩ := hWF
          have hElseEq := ih elseType target hElse (by rw [hElseAlpha]; exact hSubset)
          have hAll : ∀ branch ∈ branches,
              typeFutureOffersFuel fuel (branch.2.reannotate target) =
                typeFutureOffersFuel fuel branch.2 ∩ target.actions := by
            intro branch hMem
            obtain ⟨hEq, hWFBranch⟩ := offerBranchesWellFormed_mem hBranches branch hMem
            exact ih branch.2 target hWFBranch (by rw [hEq]; exact hSubset)
          simp only [PactType.reannotate, typeFutureOffersFuel,
            reannotateOfferBranches_map]
          rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hSubset]
          exact foldl_menu_reannotate fuel target branches _ _ hAll
            (by rw [hElseEq, Finset.inter_assoc, Finset.inter_self])

/-- `FutOff(ρ[A]) = FutOff(ρ) ∩ A`, the fuel-free form. -/
theorem typeFutureOffers_reannotate (processType : PactType)
    (target : PactTypeAlphabet) (hWF : processType.AlphabetWellFormed)
    (hSubset : target.actions ⊆ processType.alphabet.actions) :
    typeFutureOffers (processType.reannotate target) =
      typeFutureOffers processType ∩ target.actions := by
  classical
  set fuel := max (sizeOf processType + 1)
    (sizeOf (processType.reannotate target) + 1) with hFuelDef
  rw [← typeFutureOffersFuel_eq_typeFutureOffers (processType.reannotate target) fuel
      (by omega),
    ← typeFutureOffersFuel_eq_typeFutureOffers processType fuel (by omega)]
  exact typeFutureOffersFuel_reannotate fuel processType target hWF hSubset

end

end Pact
