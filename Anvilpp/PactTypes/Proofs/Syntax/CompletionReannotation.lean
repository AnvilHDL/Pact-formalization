import Anvilpp.PactTypes.Proofs.Syntax.DeclaredCompletionLemmas

namespace Pact
noncomputable section
open Classical

theorem PactTypeAlphabet.projectParallel_idem (parent child : PactTypeAlphabet) (i : Interface) :
    projectParallel parent (projectParallel parent child i) i = projectParallel parent child i := by
  unfold projectParallel
  congr 1
  ext action
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

mutual
  /-- Re-signing twice by the same alphabet has no further effect. -/
  theorem PactType.reannotate_idem (ty : PactType) (alphabet : PactTypeAlphabet) :
      (ty.reannotate alphabet).reannotate alphabet = ty.reannotate alphabet := by
    cases ty with
    | message a m d | progress a p | skip a | tock a | var a n => simp only [reannotate]
    | recur a n body =>
        simp only [reannotate]
        rw [reannotate_idem body alphabet]
    | choice a l r | fairChoice a b l r | seq a l r =>
        simp only [reannotate]
        rw [reannotate_idem l alphabet, reannotate_idem r alphabet]
    | par a l r i =>
        simp only [reannotate, reannotate_alphabet, PactTypeAlphabet.projectParallel_idem]
        rw [reannotate_idem l _, reannotate_idem r _]
    | xoffer a other branches =>
        simp only [reannotate]
        rw [reannotate_idem other alphabet, reannotateBranches_idem branches alphabet]
    | offer a other branches =>
        simp only [reannotate]
        rw [reannotate_idem other alphabet, reannotateOfferBranches_idem branches alphabet ∅]
  termination_by sizeOf ty

  theorem PactType.reannotateBranches_idem (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) :
      reannotateBranches alphabet (reannotateBranches alphabet branches) =
        reannotateBranches alphabet branches := by
    cases branches with
    | nil => simp
    | cons branch rest =>
        rcases branch with ⟨action, ty⟩
        simp only [reannotateBranches_cons]
        rw [reannotate_idem ty alphabet, reannotateBranches_idem rest alphabet]
  termination_by sizeOf branches

  theorem PactType.reannotateOfferBranches_idem (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet) (seen : Finset BareMessage) :
      reannotateOfferBranches alphabet seen (reannotateOfferBranches alphabet seen branches) =
        reannotateOfferBranches alphabet seen branches := by
    cases branches with
    | nil => simp only [reannotateOfferBranches_nil]
    | cons branch rest =>
        rcases branch with ⟨action, ty⟩
        simp only [reannotateOfferBranches_cons]
        rw [reannotate_idem ty alphabet, reannotateOfferBranches_idem rest alphabet seen]
  termination_by sizeOf branches
decreasing_by all_goals simp_wf; omega
end

theorem PactType.reannotate_eq_self_data {ty : PactType} {alphabet : PactTypeAlphabet}
    (h : ty.reannotate alphabet = ty) :
    ty.alphabet = alphabet ∧ ty.reannotate ty.alphabet = ty := by
  have hA : ty.alphabet = alphabet := by
    simpa only [reannotate_alphabet] using (congrArg PactType.alphabet h).symm
  exact ⟨hA, hA ▸ h⟩

mutual
  /-- Tail substitution commutes with re-signing when the replacement already carries that alphabet. -/
  theorem PactType.replaceVar_reannotate_tail (ty : PactType) (name : String)
      (replacement : PactType) (alphabet : PactTypeAlphabet)
      (hReplacement : replacement.reannotate alphabet = replacement)
      (hTail : ty.TailOccurrences name True) :
      (ty.replaceVar name replacement).reannotate alphabet =
        (ty.reannotate alphabet).replaceVar name replacement := by
    cases ty with
    | message a m d | progress a p | skip a | tock a => simp only [replaceVar, reannotate]
    | var a other =>
        by_cases h : name = other <;> simp only [replaceVar, reannotate, h, ↓reduceIte, hReplacement]
    | recur a other body =>
        by_cases h : name = other
        · simp only [replaceVar, reannotate, h, ↓reduceIte]
        · have hBody : body.TailOccurrences name True := by
            simpa only [TailOccurrences, Ne.symm h, ↓reduceIte] using hTail
          simp only [replaceVar, reannotate, h, ↓reduceIte]
          rw [replaceVar_reannotate_tail body name replacement alphabet hReplacement hBody]
    | par a l r i =>
        have hFalse : (par a l r i).TailOccurrences name False := by
          simpa only [TailOccurrences] using hTail
        rw [replaceVar_eq_self_of_tailOccurrences_false name replacement _ hFalse,
          replaceVar_eq_self_of_tailOccurrences_false name replacement _
            (reannotate_tailOccurrences name _ alphabet False hFalse)]
    | choice a l r | fairChoice a bid l r | seq a l r =>
        simp only [TailOccurrences] at hTail
        have hL : l.TailOccurrences name True := by
          first | exact hTail.1 | exact tailOccurrences_mono name False.elim l hTail.1
        simp only [replaceVar, reannotate]
        rw [replaceVar_reannotate_tail l name replacement alphabet hReplacement hL,
          replaceVar_reannotate_tail r name replacement alphabet hReplacement hTail.2]
    | xoffer a other branches =>
        simp only [TailOccurrences] at hTail
        simp only [replaceVar, reannotate]
        rw [replaceVar_reannotate_tail other name replacement alphabet hReplacement hTail.1,
          replaceBranches_reannotate_tail branches name replacement alphabet hReplacement hTail.2]
    | offer a other branches =>
        simp only [TailOccurrences] at hTail
        simp only [replaceVar, reannotate]
        rw [replaceVar_reannotate_tail other name replacement alphabet hReplacement hTail.1,
          replaceOfferBranches_reannotate_tail branches name replacement alphabet ∅ hReplacement
            (tailBranchOccurrences_mono name False.elim branches hTail.2)]
  termination_by sizeOf ty

  theorem PactType.replaceBranches_reannotate_tail (branches : List (BareMessage × PactType))
      (name : String) (replacement : PactType) (alphabet : PactTypeAlphabet)
      (hReplacement : replacement.reannotate alphabet = replacement)
      (hTail : TailBranchOccurrences name True branches) :
      reannotateBranches alphabet (replaceBranches branches name replacement) =
        replaceBranches (reannotateBranches alphabet branches) name replacement := by
    cases branches with
    | nil => simp only [replaceBranches, reannotateBranches_nil]
    | cons branch rest =>
        cases hBranch : branch with
        | mk action ty =>
          simp only [hBranch, TailBranchOccurrences] at hTail
          simp only [hBranch, replaceBranches, reannotateBranches_cons]
          rw [replaceVar_reannotate_tail ty name replacement alphabet hReplacement hTail.1,
            replaceBranches_reannotate_tail rest name replacement alphabet hReplacement hTail.2]
  termination_by sizeOf branches

  theorem PactType.replaceOfferBranches_reannotate_tail (branches : List (BareMessage × PactType))
      (name : String) (replacement : PactType) (alphabet : PactTypeAlphabet) (seen : Finset BareMessage)
      (hReplacement : replacement.reannotate alphabet = replacement)
      (hTail : TailBranchOccurrences name True branches) :
      reannotateOfferBranches alphabet seen (replaceBranches branches name replacement) =
        replaceBranches (reannotateOfferBranches alphabet seen branches) name replacement := by
    cases branches with
    | nil => simp only [replaceBranches, reannotateOfferBranches_nil]
    | cons branch rest =>
        cases hBranch : branch with
        | mk action ty =>
          simp only [hBranch, TailBranchOccurrences] at hTail
          simp only [hBranch, replaceBranches, reannotateOfferBranches_cons]
          rw [replaceVar_reannotate_tail ty name replacement alphabet hReplacement hTail.1,
            replaceOfferBranches_reannotate_tail rest name replacement alphabet seen hReplacement hTail.2]
  termination_by sizeOf branches
decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; simp_wf; omega
end

theorem PactType.reannotateBranches_map (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) :
    reannotateBranches alphabet branches = branches.map (fun b => (b.1, b.2.reannotate alphabet)) := by
  induction branches with
  | nil => simp
  | cons branch rest ih => cases branch; simp only [reannotateBranches_cons, List.map_cons, ih]

theorem PactType.reannotateOfferBranches_map (alphabet : PactTypeAlphabet)
    (seen : Finset BareMessage) (branches : List (BareMessage × PactType)) :
    reannotateOfferBranches alphabet seen branches = branches.map (fun b => (b.1, b.2.reannotate alphabet)) := by
  induction branches with
  | nil => simp only [reannotateOfferBranches_nil, List.map_nil]
  | cons branch rest ih => cases branch; simp only [reannotateOfferBranches_cons, List.map_cons, ih]

/-- Enlarging the alphabet supplied to re-signing cannot disable completion. -/
theorem typeCanCompleteThisCycleFuel_reannotate_mono (fuel : Nat) (ty : PactType)
    (small large : PactTypeAlphabet) (hSub : small.actions ⊆ large.actions) :
    typeCanCompleteThisCycleFuel fuel (ty.reannotate small) = true →
      typeCanCompleteThisCycleFuel fuel (ty.reannotate large) = true := by
  induction fuel generalizing ty small large with
  | zero => simp [typeCanCompleteThisCycleFuel]
  | succ fuel ih =>
      cases ty with
      | message a m d => simp [PactType.reannotate, typeCanCompleteThisCycleFuel]
      | progress a p | skip a | tock a | var a n => simp [PactType.reannotate, typeCanCompleteThisCycleFuel]
      | recur a n body =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel]
          exact ih body small large hSub
      | choice a l r | fairChoice a bid l r | seq a l r =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, Bool.or_eq_true, Bool.and_eq_true]
          first
          | exact Or.imp (ih l small large hSub) (ih r small large hSub)
          | exact fun h => ⟨ih l small large hSub h.1, ih r small large hSub h.2⟩
      | par a l r i =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, Bool.and_eq_true]
          exact fun h => ⟨ih l _ _ (Finset.union_subset_union (Finset.Subset.refl _) hSub) h.1,
            ih r _ _ (Finset.union_subset_union (Finset.Subset.refl _) hSub) h.2⟩
      | xoffer a other branches | offer a other branches =>
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, PactType.reannotateBranches_map,
            PactType.reannotateOfferBranches_map, List.forall_mem_map, List.any_map,
            Function.comp_def, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
          rintro (hElse | ⟨branch, hMem, hComplete⟩)
          · exact Or.inl (ih other small large hSub hElse)
          · exact Or.inr ⟨branch, hMem, ih branch.2 small large hSub hComplete⟩

theorem PactType.canCompleteDeclared_reannotate_mono (ty : PactType)
    (small large : PactTypeAlphabet) (hSub : small.actions ⊆ large.actions)
    (h : (ty.reannotate small).CanCompleteDeclared = true) :
    (ty.reannotate large).CanCompleteDeclared = true := by
  let fuel := max (sizeOf (ty.reannotate small)) (sizeOf (ty.reannotate large)) + 1
  rw [← typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel _ (by dsimp [fuel]; omega)] at h
  rw [← typeCanCompleteThisCycleFuel_eq_canCompleteDeclared fuel _ (by dsimp [fuel]; omega)]
  exact typeCanCompleteThisCycleFuel_reannotate_mono fuel ty small large hSub h

end
end Pact
