import Anvilpp.PactTypes.NewCorrespondence.Helpers.TypeWellFormedIn
import Anvilpp.PactTypes.Syntax.CompletionReannotation

namespace Pact
noncomputable section
open Classical

theorem reannotate_branches_fixed_of_mem
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (h : branches.map (fun b => (b.1, b.2.reannotate alphabet)) = branches)
    (branch : BareMessage × PactType) (hMem : branch ∈ branches) :
    branch.2.reannotate alphabet = branch.2 := by
  induction branches with
  | nil => simp at hMem
  | cons head rest ih =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact congrArg Prod.snd h.1
      · exact ih h.2 hRest

theorem parallelTypeBranchesSelecting_reannotate_self
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) (hMem : selected ∈ branches) :
    (parallelTypeBranchesSelecting alphabet selected branches).reannotate alphabet =
      parallelTypeBranchesSelecting alphabet selected branches := by
  have hProject : PactTypeAlphabet.projectParallel alphabet alphabet ∅ = alphabet := by
    simp [PactTypeAlphabet.projectParallel]
  have hSelected (branch : BareMessage × PactType) :
      (selectedTypeBranchAt alphabet branch).reannotate alphabet = selectedTypeBranchAt alphabet branch := by
    simp only [selectedTypeBranchAt, PactType.reannotate, PactType.reannotate_idem]
  have hSingleton (branch : BareMessage × PactType) :
      (singletonTypeXOfferAt alphabet branch).reannotate alphabet = singletonTypeXOfferAt alphabet branch := by
    simp only [singletonTypeXOfferAt, PactType.reannotate, PactType.reannotateBranches_cons,
      PactType.reannotateBranches_nil, PactType.reannotate_idem]
  have hAll : ∀ branches,
      (parallelTypeBranchesWithin alphabet branches).reannotate alphabet =
        parallelTypeBranchesWithin alphabet branches := by
    intro branches
    induction branches with
    | nil => simp [parallelTypeBranchesWithin, PactType.reannotate]
    | cons head rest ih =>
        cases rest with
        | nil => exact hSingleton head
        | cons next tail =>
            rw [parallelTypeBranchesWithin, PactType.reannotate]
            simp only [parallelTypeBranchesWithin_alphabet]
            change PactType.par alphabet
              ((singletonTypeXOfferAt alphabet head).reannotate (PactTypeAlphabet.projectParallel alphabet alphabet ∅))
              ((parallelTypeBranchesWithin alphabet (next :: tail)).reannotate (PactTypeAlphabet.projectParallel alphabet alphabet ∅)) ∅ = _
            rw [hProject, hSingleton, ih]
            all_goals simp
  have hWithin : ∀ branches,
      (parallelTypeBranchesSelectingWithin alphabet selected branches).reannotate alphabet =
        parallelTypeBranchesSelectingWithin alphabet selected branches := by
    intro branches
    induction branches with
    | nil => simp [parallelTypeBranchesSelectingWithin, PactType.reannotate]
    | cons head rest ih =>
        cases rest with
        | nil =>
            simp only [parallelTypeBranchesSelectingWithin]
            split_ifs <;> first | exact hSelected head | exact hSingleton head
        | cons next tail =>
            simp only [parallelTypeBranchesSelectingWithin]
            split_ifs <;> rw [PactType.reannotate]
            all_goals simp only [parallelTypeBranchesSelectingWithin_alphabet, parallelTypeBranchesWithin_alphabet]
            all_goals
              change (PactType.par alphabet
                (PactType.reannotate (PactTypeAlphabet.projectParallel alphabet alphabet ∅) _)
                (PactType.reannotate (PactTypeAlphabet.projectParallel alphabet alphabet ∅) _) ∅ = _)
            all_goals rw [hProject]
            · rw [hSelected, hAll]
            · rw [hSingleton, ih]
  cases branches with
  | nil => simp at hMem
  | cons head rest => exact hWithin (head :: rest)

/-- A step preserves the fixed-point property of re-signing by the node alphabet. -/
theorem TypeTransition.preserves_reannotate_self
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hStep : TypeTransition env source label target)
    (hNormal : source.reannotate source.alphabet = source)
    (hTail : source.TailRecursive) :
    target.reannotate source.alphabet = target := by
  induction hStep with
  | action | action_wait | skip | progress | cycle | cycle_wait =>
      simp only [PactType.alphabet, PactType.reannotate]
  | choice_left | fair_left =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.choice.injEq,
        PactType.fairChoice.injEq, true_and] at hNormal
      exact hNormal.1
  | choice_right | fair_right =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.choice.injEq,
        PactType.fairChoice.injEq, true_and] at hNormal
      exact hNormal.2
  | recur env alphabet name body =>
      have hSelf := hNormal
      simp only [PactType.alphabet, PactType.reannotate, PactType.recur.injEq, true_and] at hNormal
      simp only [PactType.TailRecursive] at hTail
      change (body.replaceVar name (.recur alphabet name body)).reannotate alphabet = _
      rw [PactType.replaceVar_reannotate_tail body name _ alphabet hSelf hTail.1, hNormal]
  | seq env alphabet left left' right label _ _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.seq.injEq, true_and] at hNormal
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hA, hL⟩ := PactType.reannotate_eq_self_data hNormal.1
      have hTarget := ih hL hTail.1
      rw [hA] at hTarget
      simpa only [PactType.alphabet, PactType.reannotate, hTarget, hNormal.2]
  | seq_fuse env alphabet skipAlphabet left right label _ ih =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.seq.injEq, true_and] at hNormal
      exact hNormal.2
  | xoffer_branch env alphabet other branches action body hEnv =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.xoffer.injEq, true_and] at hNormal
      rw [PactType.reannotateBranches_map] at hNormal
      exact reannotate_branches_fixed_of_mem alphabet branches hNormal.2 (action, body) hEnv.2.1
  | xoffer_else | offer_else =>
      simp only [PactType.alphabet, PactType.reannotate, PactType.xoffer.injEq,
        PactType.offer.injEq, true_and] at hNormal
      exact hNormal.1
  | xoffer_wait | offer_wait => exact hNormal
  | offer_some env alphabet other branches selected hEnv =>
      exact parallelTypeBranchesSelecting_reannotate_self alphabet selected branches hEnv.2.1
  | par outer leftEnv rightEnv interface alphabet left left' right right' leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ _ _ _ _ _ _ hEnv ihLeft ihRight =>
      change (PactType.par alphabet left right interface).reannotate alphabet = _ at hNormal
      simp only [PactType.reannotate, PactType.par.injEq, true_and, and_true] at hNormal
      simp only [PactType.TailRecursive] at hTail
      obtain ⟨hLA, hLN⟩ := PactType.reannotate_eq_self_data hNormal.1
      obtain ⟨hRA, hRN⟩ := PactType.reannotate_eq_self_data hNormal.2
      have hL := ihLeft hLN hTail.1
      have hR := ihRight hRN hTail.2
      have hLT := (PactType.reannotate_eq_self_data hL).1
      have hRT := (PactType.reannotate_eq_self_data hR).1
      change (PactType.par alphabet left' right' interface).reannotate alphabet = _
      rw [PactType.reannotate, hLT, hRT, ← hLA, ← hRA, hL, hR]
  | par_fuse => simp only [PactType.alphabet, PactType.reannotate]
  | left_complete | right_complete => exact PactType.reannotate_idem _ _

end
end Pact
