import Anvilpp.PactTypes.Proofs.Syntax.DeclaredCompletionLemmas
import Anvilpp.PactTypes.Proofs.Syntax.CompletionReannotation
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SequenceMenus

namespace Pact

noncomputable section

open Classical

-- Copied recursion states carry the substitutions of their enclosing binders.
private def completionAfter : List (String × PactType) → PactType → Bool
  | [], rho => rho.CanCompleteDeclared
  | (name, replacement) :: rest, rho => completionAfter rest (rho.replaceVar name replacement)

private theorem completionAfter_of_complete (substitutions : List (String × PactType))
    (rho : PactType) (hComplete : rho.CanCompleteDeclared = true) :
    completionAfter substitutions rho = true := by
  induction substitutions generalizing rho with
  | nil => exact hComplete
  | cons head rest ih =>
      apply ih
      exact PactType.canCompleteDeclared_replaceVar_of_complete _ _ rho hComplete

private theorem completionAfter_seq (substitutions : List (String × PactType))
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    completionAfter substitutions (.seq alphabet left right) =
      (completionAfter substitutions left && completionAfter substitutions right) := by
  induction substitutions generalizing left right with
  | nil => exact PactType.canCompleteDeclared_eq (.seq alphabet left right)
  | cons head rest ih =>
      rcases head with ⟨name, replacement⟩
      simp only [completionAfter, PactType.replaceVar, ih]

private theorem completionAfter_skip (substitutions : List (String × PactType))
    (alphabet : PactTypeAlphabet) : completionAfter substitutions (.skip alphabet) = true :=
  completionAfter_of_complete substitutions _ (PactType.canCompleteDeclared_eq (.skip alphabet))

private theorem branchCompletion_eq_any (branches : List (BareMessage × PactType)) :
    PactType.BranchCanCompleteDeclared branches = branches.any (fun b => b.2.CanCompleteDeclared) := by
  induction branches with
  | nil => exact PactType.branchCanCompleteDeclared_nil
  | cons b rest ih => cases b; simp only [PactType.branchCanCompleteDeclared_cons, List.any_cons, ih]

private theorem replaceBranches_map (name : String) (replacement : PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.replaceBranches branches name replacement =
      branches.map (fun b => (b.1, b.2.replaceVar name replacement)) := by
  induction branches with
  | nil => simp only [PactType.replaceBranches, List.map_nil]
  | cons b rest ih => cases b; simp only [PactType.replaceBranches, List.map_cons, ih]

private theorem completionAfter_eq (subs : List (String × PactType)) (ty : PactType) :
    completionAfter subs ty = match ty with
    | .message _ _ _ | .progress _ _ | .skip _ => true
    | .tock _ => false
    | .var _ _ => completionAfter subs ty
    | .recur _ name body => completionAfter (subs.filter (fun s => s.1 != name)) body
    | .choice _ left right | .fairChoice _ _ left right =>
        completionAfter subs left || completionAfter subs right
    | .seq _ left right | .par _ left right _ =>
        completionAfter subs left && completionAfter subs right
    | .xoffer _ other branches | .offer _ other branches =>
        completionAfter subs other || branches.any (fun b => completionAfter subs b.2) := by
  induction subs generalizing ty with
  | nil =>
    cases ty <;> simp only [completionAfter, List.filter_nil]
    all_goals rw [PactType.canCompleteDeclared_eq]
    all_goals simp only [branchCompletion_eq_any]
  | cons s rest ih =>
    rcases s with ⟨name, replacement⟩
    cases ty with
    | var => rfl
    | recur a other body =>
      by_cases hName : name = other
      · subst other
        simp only [completionAfter, PactType.replaceVar, List.filter_cons,
          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact ih (.recur a name body)
      · simpa only [completionAfter, PactType.replaceVar, if_neg hName, List.filter_cons,
          bne_iff_ne, if_pos hName] using ih (.recur a other (body.replaceVar name replacement))
    | message | progress | skip | tock | choice | fairChoice | seq | par =>
      simp only [completionAfter, PactType.replaceVar]
      apply ih
    | xoffer | offer =>
      simp only [completionAfter, PactType.replaceVar]
      rw [ih]
      simp only [replaceBranches_map, List.any_map, Function.comp_def]

private theorem completionAfter_reannotate (ty : PactType) :
    ∀ alphabet subs, completionAfter subs (ty.reannotate alphabet) = completionAfter subs ty := by
  induction hSize : sizeOf ty using Nat.strong_induction_on generalizing ty with
  | h n ih =>
    intro alphabet subs
    have hBranches : ∀ (bs : List (BareMessage × PactType)), sizeOf bs < n →
        (bs.any fun b => completionAfter subs (b.2.reannotate alphabet)) =
          bs.any (fun b => completionAfter subs b.2) := by
      intro bs
      induction bs with
      | nil => intro _; rfl
      | cons b rest hRest =>
        rcases b with ⟨action, body⟩
        intro hSizeB
        simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at hSizeB
        simp only [List.any_cons]
        rw [ih _ (by omega) body rfl alphabet subs, hRest (by omega)]
    cases ty with
    | var a name =>
      clear hBranches
      induction subs with
      | nil => simp only [PactType.reannotate, completionAfter, PactType.canCompleteDeclared_eq]
      | cons s rest hRest =>
        simp only [PactType.reannotate, completionAfter, PactType.replaceVar]
        split_ifs
        · rfl
        · simpa only [PactType.reannotate] using hRest
    | message | progress | skip | tock =>
      simp only [PactType.reannotate, completionAfter_eq]
    | recur a name body =>
      simp only [PactType.reannotate]
      conv_lhs => rw [completionAfter_eq]
      conv_rhs => rw [completionAfter_eq]
      simp only []
      exact ih _ (by rw [← hSize]; simp; omega) body rfl alphabet _
    | choice a left right | fairChoice a bid left right | seq a left right =>
      simp only [PactType.reannotate]
      conv_lhs => rw [completionAfter_eq]
      conv_rhs => rw [completionAfter_eq]
      simp only []
      rw [ih _ (by rw [← hSize]; simp; omega) left rfl alphabet subs,
        ih _ (by rw [← hSize]; simp; omega) right rfl alphabet subs]
    | par a left right interface =>
      simp only [PactType.reannotate]
      conv_lhs => rw [completionAfter_eq]
      conv_rhs => rw [completionAfter_eq]
      simp only []
      rw [ih _ (by rw [← hSize]; simp; omega) left rfl _ subs,
        ih _ (by rw [← hSize]; simp; omega) right rfl _ subs]
    | xoffer a other bs | offer a other bs =>
      simp only [PactType.reannotate]
      conv_lhs => rw [completionAfter_eq]
      conv_rhs => rw [completionAfter_eq]
      simp only [
        PactType.reannotateBranches_map, PactType.reannotateOfferBranches_map,
        List.any_map, Function.comp_def]
      rw [ih _ (by rw [← hSize]; simp; omega) other rfl alphabet subs,
        hBranches bs (by rw [← hSize]; simp; omega)]

private theorem completionAfter_selected (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType) (branches : List (BareMessage × PactType))
    (hSelected : selected ∈ branches) (subs : List (String × PactType))
    (hComplete : completionAfter subs
      (parallelTypeBranchesSelecting alphabet selected branches) = true) :
    completionAfter subs selected.2 = true := by
  have hWithin : ∀ bs : List (BareMessage × PactType), selected ∈ bs →
      completionAfter subs (parallelTypeBranchesSelectingWithin alphabet selected bs) = true →
      completionAfter subs selected.2 = true := by
    intro bs
    induction bs with
    | nil => simp
    | cons b rest ih =>
      intro hMem hComplete
      cases rest with
      | nil =>
        have hEq : b = selected := (List.mem_singleton.mp hMem).symm
        subst b
        simp only [parallelTypeBranchesSelectingWithin, ↓reduceIte, selectedTypeBranchAt,
          completionAfter_seq] at hComplete
        exact (completionAfter_reannotate selected.2 alphabet subs) ▸
          (Bool.and_eq_true_iff.mp hComplete).2
      | cons next tail =>
        by_cases hEq : b = selected
        · subst b
          simp only [parallelTypeBranchesSelectingWithin] at hComplete
          rw [completionAfter_eq] at hComplete
          have hHead := (Bool.and_eq_true_iff.mp hComplete).1
          simp only [selectedTypeBranchAt, completionAfter_seq] at hHead
          exact (completionAfter_reannotate selected.2 alphabet subs) ▸
            (Bool.and_eq_true_iff.mp hHead).2
        · simp only [parallelTypeBranchesSelectingWithin, if_neg hEq] at hComplete
          rw [completionAfter_eq] at hComplete
          exact ih (List.mem_of_ne_of_mem (Ne.symm hEq) hMem)
            (Bool.and_eq_true_iff.mp hComplete).2
  cases branches with
  | nil => simp at hSelected
  | cons b rest => exact hWithin _ hSelected hComplete

private theorem completionAfter_final (fuel : Nat) (ty rho : PactType)
    (hFuel : typeCompilationFuel ty ≤ fuel) (state : TypeAutomatonState)
    (hRelated : (rho, state) ∈ buildRelationSetCoreFuel fuel ty)
    (hFinal : state ∈ (compileTypeFuel fuel ty).accepting)
    (substitutions : List (String × PactType)) : completionAfter substitutions rho = true := by
  rw [compileTypeFuel_eq_of_sufficient ty hFuel le_rfl] at hFinal
  rw [buildRelationSetCoreFuel_eq_of_sufficient ty hFuel le_rfl] at hRelated
  obtain ⟨alphabet, hSkip⟩ := relationMembership_of_accepting ty hFinal
  have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel ty) ty hRelated hSkip
  rw [hEq]
  exact completionAfter_skip substitutions alphabet

private theorem menuLinks_completion_transport :
    ∀ fuel ty, typeCompilationFuel ty ≤ fuel →
      ∀ link ∈ compileTypeMenuLinksFuel fuel ty,
        ∃ source target,
          (source, link.1) ∈ buildRelationSetCoreFuel fuel ty ∧
          (target, link.2) ∈ buildRelationSetCoreFuel fuel ty ∧
          ∀ substitutions, completionAfter substitutions target = true →
            completionAfter substitutions source = true := by
  intro fuel
  induction fuel with
  | zero => intro ty _ link hLink; simp [compileTypeMenuLinksFuel] at hLink
  | succ fuel ih =>
      intro ty hFuel link hLink
      cases ty with
      | message a m d | progress a p | skip a | tock a | var a x =>
          simp [compileTypeMenuLinksFuel] at hLink
      | choice a left right | fairChoice a bid left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image] at hLink
          rcases hLink with ⟨entry, hEntry, rfl⟩ | ⟨entry, hEntry, rfl⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih left hLeft entry hEntry
            refine ⟨rho, theta, ?_, ?_, hComplete⟩
            · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inl ⟨(rho, entry.1), hRho, rfl⟩)
            · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inl ⟨(theta, entry.2), hTheta, rfl⟩)
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih right hRight entry hEntry
            refine ⟨rho, theta, ?_, ?_, hComplete⟩
            · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inr ⟨(rho, entry.1), hRho, rfl⟩)
            · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
              exact Or.inr (Or.inr ⟨(theta, entry.2), hTheta, rfl⟩)
      | recur a name body =>
          have hBody : typeCompilationFuel body ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          simp only [compileTypeMenuLinksFuel, Finset.mem_image] at hLink
          obtain ⟨entry, hEntry, rfl⟩ := hLink
          obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih body hBody entry hEntry
          refine ⟨rho.replaceVar name (.recur a name body), theta.replaceVar name (.recur a name body),
            ?_, ?_, ?_⟩
          · rw [buildRelationSetCoreFuel]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(rho, entry.1), hRho, rfl⟩)
          · rw [buildRelationSetCoreFuel]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(theta, entry.2), hTheta, rfl⟩)
          · intro substitutions h
            exact hComplete ((name, .recur a name body) :: substitutions) h
      | seq a left right =>
          have hLeft : typeCompilationFuel left ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel right ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          have hEntryRight := buildRelationSetCoreFuel_initial_mem fuel right hRight
          have hLiftLeft (rho : PactType) (q : TypeAutomatonState)
              (hRho : (rho, q) ∈ buildRelationSetCoreFuel fuel left)
              (hq : q ∉ sequenceDeleted (compileTypeFuel fuel left)) :
              (.seq a rho right, TypeAutomatonState.child 0 q) ∈
                buildRelationSetCoreFuel (fuel + 1) (.seq a left right) := by
            rw [buildRelationSetCoreFuel]
            exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨(rho, q), Finset.mem_filter.mpr ⟨hRho, hq⟩, rfl⟩)
          have hLiftRight (rho : PactType) (q : TypeAutomatonState)
              (hRho : (rho, q) ∈ buildRelationSetCoreFuel fuel right) :
              (rho, TypeAutomatonState.child 1 q) ∈
                buildRelationSetCoreFuel (fuel + 1) (.seq a left right) := by
            rw [buildRelationSetCoreFuel]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(rho, q), hRho, rfl⟩)
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter] at hLink
          rcases hLink with (⟨entry, ⟨hEntry, hKeep⟩, rfl⟩ | ⟨entry, hEntry, rfl⟩) |
            ⟨entry, ⟨hEntry, hKeep, hFlag⟩, rfl⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih left hLeft entry hEntry
            by_cases hFinal : entry.2 ∈ (compileTypeFuel fuel left).accepting
            · refine ⟨.seq a rho right, right, hLiftLeft rho entry.1 hRho hKeep, ?_, ?_⟩
              · simpa only [sequenceRedirect, if_pos hFinal, childState] using
                  hLiftRight right _ hEntryRight
              · intro substitutions h
                rw [completionAfter_seq, Bool.and_eq_true]
                exact ⟨hComplete substitutions
                  (completionAfter_final fuel left theta hLeft entry.2 hTheta hFinal substitutions), h⟩
            · refine ⟨.seq a rho right, .seq a theta right,
                hLiftLeft rho entry.1 hRho hKeep, ?_, ?_⟩
              · simpa only [sequenceRedirect, if_neg hFinal, childState] using
                  hLiftLeft theta entry.2 hTheta (not_mem_sequenceDeleted_of_not_accepting hFinal)
              · intro substitutions h
                rw [completionAfter_seq, Bool.and_eq_true] at h ⊢
                exact ⟨hComplete substitutions h.1, h.2⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih right hRight entry hEntry
            exact ⟨rho, theta, hLiftRight rho entry.1 hRho, hLiftRight theta entry.2 hTheta, hComplete⟩
          · refine ⟨.seq a entry.1 right, right,
              hLiftLeft entry.1 entry.2 hEntry hKeep, hLiftRight right _ hEntryRight, ?_⟩
            intro substitutions h
            rw [completionAfter_seq, Bool.and_eq_true]
            rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ entry.1 (by omega)] at hFlag
            exact ⟨completionAfter_of_complete substitutions entry.1 hFlag, h⟩
      | par a left right interface =>
          have hLeft : typeCompilationFuel (left.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]; simp [typeCompilationFuel] at hFuel; omega
          have hRight : typeCompilationFuel (right.reannotate a) ≤ fuel := by
            rw [typeCompilationFuel_reannotate]; simp [typeCompilationFuel] at hFuel; omega
          have hDone : (.skip a, TypeAutomatonState.final) ∈
              buildRelationSetCoreFuel (fuel + 1) (.par a left right interface) := by
            rw [buildRelationSetCoreFuel]; exact Finset.mem_insert_self _ _
          simp only [compileTypeMenuLinksFuel, Finset.mem_union, Finset.mem_image,
            Finset.mem_filter] at hLink
          rcases hLink with ⟨entry, ⟨hEntry, hKeep⟩, rfl⟩ | ⟨entry, ⟨hEntry, hKeep⟩, rfl⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih (left.reannotate a) hLeft entry hEntry
            have hLift (rho : PactType) (q : TypeAutomatonState)
                (hRho : (rho, q) ∈ buildRelationSetCoreFuel fuel (left.reannotate a))
                (hq : q ∉ (compileTypeFuel fuel (left.reannotate a)).accepting) :
                (rho, TypeAutomatonState.survivor 0 q) ∈
                  buildRelationSetCoreFuel (fuel + 1) (.par a left right interface) := by
              rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨(rho, q), Finset.mem_filter.mpr ⟨hRho, hq⟩, rfl⟩)))
            by_cases hFinal : entry.2 ∈ (compileTypeFuel fuel (left.reannotate a)).accepting
            · refine ⟨rho, .skip a, hLift rho entry.1 hRho hKeep, ?_, ?_⟩
              · simpa only [if_pos hFinal] using hDone
              · intro substitutions _
                exact hComplete substitutions (completionAfter_final fuel (left.reannotate a)
                  theta hLeft entry.2 hTheta hFinal substitutions)
            · exact ⟨rho, theta, hLift rho entry.1 hRho hKeep,
                by simpa only [if_neg hFinal] using hLift theta entry.2 hTheta hFinal, hComplete⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih (right.reannotate a) hRight entry hEntry
            have hLift (rho : PactType) (q : TypeAutomatonState)
                (hRho : (rho, q) ∈ buildRelationSetCoreFuel fuel (right.reannotate a))
                (hq : q ∉ (compileTypeFuel fuel (right.reannotate a)).accepting) :
                (rho, TypeAutomatonState.survivor 1 q) ∈
                  buildRelationSetCoreFuel (fuel + 1) (.par a left right interface) := by
              rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨(rho, q), Finset.mem_filter.mpr ⟨hRho, hq⟩, rfl⟩))
            by_cases hFinal : entry.2 ∈ (compileTypeFuel fuel (right.reannotate a)).accepting
            · refine ⟨rho, .skip a, hLift rho entry.1 hRho hKeep, ?_, ?_⟩
              · simpa only [if_pos hFinal] using hDone
              · intro substitutions _
                exact hComplete substitutions (completionAfter_final fuel (right.reannotate a)
                  theta hRight entry.2 hTheta hFinal substitutions)
            · exact ⟨rho, theta, hLift rho entry.1 hRho hKeep,
                by simpa only [if_neg hFinal] using hLift theta entry.2 hTheta hFinal, hComplete⟩
      | xoffer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          simp only [compileTypeMenuLinksFuel, Finset.union_assoc] at hLink
          simp only [mem_foldl_union_iff, Finset.mem_union, Finset.mem_image,
            Finset.mem_singleton] at hLink
          rcases hLink with (⟨entry, hEntry, rfl⟩ | rfl) | ⟨item, hItem, hItemLink⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih other hElse entry hEntry
            refine ⟨rho, theta, ?_, ?_, hComplete⟩
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(rho, entry.1), hRho, rfl⟩))
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(theta, entry.2), hTheta, rfl⟩))
          · refine ⟨.xoffer a other branches, other, ?_, ?_, ?_⟩
            · rw [buildRelationSetCoreFuel]; exact Finset.mem_insert_self _ _
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(other, (compileTypeFuel fuel other).initial),
                  buildRelationSetCoreFuel_initial_mem fuel other hElse, rfl⟩))
            · intro subs h
              rw [completionAfter_eq]
              simp only [h, Bool.true_or]
          · have hMember : item.1 ∈ branches := by
              obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hItem
              simp [hValue, List.getElem_mem hBound]
            rcases hItemLink with ⟨entry, hEntry, rfl⟩ | rfl
            · specialize ih item.1.2 (by
                  have := typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember
                  simp [typeCompilationFuel] at hFuel; omega) entry hEntry
              obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih
              refine ⟨rho, theta, ?_, ?_, hComplete⟩
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem, (rho, entry.1), hRho, rfl⟩))
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem, (theta, entry.2), hTheta, rfl⟩))
            · have hBranchFuel : typeCompilationFuel item.1.2 ≤ fuel := by
                have := typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember
                simp [typeCompilationFuel] at hFuel; omega
              refine ⟨.xoffer a other branches, item.1.2, ?_, ?_, ?_⟩
              · rw [buildRelationSetCoreFuel]; exact Finset.mem_insert_self _ _
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem,
                  (item.1.2, (compileTypeFuel fuel item.1.2).initial),
                  buildRelationSetCoreFuel_initial_mem fuel item.1.2 hBranchFuel, rfl⟩))
              · intro subs h
                have hSelected : completionAfter subs item.1.2 = true := h
                rw [completionAfter_eq]
                simp only [Bool.or_eq_true]
                exact Or.inr (List.any_eq_true.mpr ⟨item.1, hMember, hSelected⟩)

      | offer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          simp only [compileTypeMenuLinksFuel, Finset.union_assoc] at hLink
          simp only [mem_foldl_union_iff, Finset.mem_union, Finset.mem_image,
            Finset.mem_singleton] at hLink
          rcases hLink with (⟨entry, hEntry, rfl⟩ | rfl) | ⟨item, hItem, hItemLink⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih other hElse entry hEntry
            refine ⟨rho, theta, ?_, ?_, hComplete⟩
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(rho, entry.1), hRho, rfl⟩))
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(theta, entry.2), hTheta, rfl⟩))
          · refine ⟨.offer a other branches, other, ?_, ?_, ?_⟩
            · rw [buildRelationSetCoreFuel]; exact Finset.mem_insert_self _ _
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(other, (compileTypeFuel fuel other).initial),
                  buildRelationSetCoreFuel_initial_mem fuel other hElse, rfl⟩))
            · intro subs h
              rw [completionAfter_eq]
              simp only [h, Bool.true_or]
          · have hMember : item.1 ∈ branches := by
              obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hItem
              simp [hValue, List.getElem_mem hBound]
            rcases hItemLink with ⟨entry, hEntry, rfl⟩ | rfl
            · specialize ih (parallelTypeBranchesSelecting a item.1 branches) (by
                  rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                  simp [typeCompilationFuel] at hFuel; omega) entry hEntry
              obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih
              refine ⟨rho, theta, ?_, ?_, hComplete⟩
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem, (rho, entry.1), hRho, rfl⟩))
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem, (theta, entry.2), hTheta, rfl⟩))
            · have hSelectedFuel : typeCompilationFuel (parallelTypeBranchesSelecting a item.1 branches) ≤ fuel := by
                rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                simp [typeCompilationFuel] at hFuel; omega
              refine ⟨.offer a other branches, parallelTypeBranchesSelecting a item.1 branches, ?_, ?_, ?_⟩
              · rw [buildRelationSetCoreFuel]; exact Finset.mem_insert_self _ _
              · simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
                  mem_foldl_union_iff, Finset.mem_image]
                exact Or.inr (Or.inr (Or.inr ⟨item, hItem,
                  (parallelTypeBranchesSelecting a item.1 branches,
                    (compileTypeFuel fuel (parallelTypeBranchesSelecting a item.1 branches)).initial),
                  buildRelationSetCoreFuel_initial_mem fuel _ hSelectedFuel, rfl⟩))
              · intro subs h
                have hSelected : completionAfter subs item.1.2 = true := by
                  first | exact h | exact completionAfter_selected a item.1 branches hMember subs h
                rw [completionAfter_eq]
                simp only [Bool.or_eq_true]
                exact Or.inr (List.any_eq_true.mpr ⟨item.1, hMember, hSelected⟩)

/-- Every optimistic link has related endpoints and propagates completion backwards. -/
theorem compileTypeMenuLinksFuel_completion_transport
    (fuel : Nat) (ty : PactType) (hFuel : typeCompilationFuel ty ≤ fuel)
    (link : TypeAutomatonState × TypeAutomatonState)
    (hLink : link ∈ compileTypeMenuLinksFuel fuel ty) :
    ∃ source target,
      (source, link.1) ∈ buildRelationSetCoreFuel fuel ty ∧
      (target, link.2) ∈ buildRelationSetCoreFuel fuel ty ∧
      (typeCanCompleteThisCycleFuel (sizeOf target + 1) target = true →
        typeCanCompleteThisCycleFuel (sizeOf source + 1) source = true) := by
  obtain ⟨source, target, hSource, hTarget, hComplete⟩ :=
    menuLinks_completion_transport fuel ty hFuel link hLink
  refine ⟨source, target, hSource, hTarget, ?_⟩
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ source (by omega),
    typeCanCompleteThisCycleFuel_eq_canCompleteDeclared _ target (by omega)]
  exact hComplete []

end

end Pact
