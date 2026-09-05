import Anvilpp.PactTypes.Syntax.DeclaredCompletionLemmas
import Anvilpp.PactTypes.NewCorrespondence.Helpers.SequenceMenus

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
      | xoffer a other branches | offer a other branches =>
          have hElse : typeCompilationFuel other ≤ fuel := by simp [typeCompilationFuel] at hFuel; omega
          simp only [compileTypeMenuLinksFuel, mem_foldl_union_iff, Finset.mem_image] at hLink
          rcases hLink with ⟨entry, hEntry, rfl⟩ | ⟨item, hItem, entry, hEntry, rfl⟩
          · obtain ⟨rho, theta, hRho, hTheta, hComplete⟩ := ih other hElse entry hEntry
            refine ⟨rho, theta, ?_, ?_, hComplete⟩
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(rho, entry.1), hRho, rfl⟩))
            · rw [buildRelationSetCoreFuel]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨(theta, entry.2), hTheta, rfl⟩))
          · have hMember : item.1 ∈ branches := by
              obtain ⟨hBound, hValue⟩ := List.mem_zipIdx' hItem
              simp [hValue, List.getElem_mem hBound]
            first
            | specialize ih item.1.2 (by
                have := typeCompilationFuel_le_typeBranchCompilationFuel branches item.1 hMember
                simp [typeCompilationFuel] at hFuel; omega) entry hEntry
            | specialize ih (parallelTypeBranchesSelecting a item.1 branches) (by
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
