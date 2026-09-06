import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Base
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MenuLinkCompletion
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.CompletionFlag

namespace Pact

noncomputable section

open Classical

/-- A menu reference has a related target and propagates its completion flag backwards. -/
theorem menuReference_completion_backward
    (ty : PactType) {bound : List String} (hWF : TypeWellFormedIn bound ty)
    (hNoMarker : ∀ name edge, edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges →
      edge.label ≠ .variable name)
    (hCurrent : CurrentOfferCorrespondence ty)
    {rho : PactType} {source target : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho source)
    (hReference : target ∈
      (compiledMenuGraphFuel (typeCompilationFuel ty) ty).referencedStates source) :
    ∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta target ∧
      (typeCanCompleteThisCycleFuel (sizeOf theta + 1) theta = true →
        typeCanCompleteThisCycleFuel (sizeOf rho + 1) rho = true) := by
  simp only [compiledMenuGraphFuel, Nat.min_self, PendingAutomaton.withMenuDependencies,
    Finset.mem_union] at hReference
  rcases hReference with hExecution | hLink
  · -- Execution references use the current-offer hypothesis and the type-step implication.
    obtain ⟨edge, hEdge, hRef⟩ := Finset.mem_biUnion.mp hExecution
    obtain ⟨hEdge, hSource⟩ := Finset.mem_filter.mp hEdge
    by_cases hClock : edge.label.semantic = .tock
    · simp [hClock] at hRef
    have hTarget : target = edge.target := by
      simpa only [if_neg hClock, Finset.mem_singleton] using hRef
    subst target
    cases hLabel : edge.label with
    | «variable» name => exact (hNoMarker name edge hEdge hLabel).elim
    | visible label =>
        have hPublic : (compileType ty).HasEdge source edge.environment label
            ⟨edge.current, resolveFutureSpec (computeFutureOf ty) edge.future⟩ edge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge]
          exact ⟨edge, hEdge, hSource, rfl, hLabel, rfl, rfl, rfl⟩
        obtain ⟨theta, _, hStep, hTheta⟩ := hCurrent.2 hRelated hPublic
        have hRhoWF := relationMembership_alphabetWellFormed
          committedOfferAlphabetWellFormed_holds committedOfferScoping_holds ty rho source
          hWF.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.1
          hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.1
          (offerBranchesDisjoint_of_wellFormedIn hWF) hRelated
        have hRhoTail := (relationMembership_tailRecursive ty rho source
          hWF.2.2.2.2.2.1 hWF.2.2.2.1 hRelated).1
        exact ⟨theta, hTheta, hStep.1.completionFlag_backward
          (PactType.reannotate_own_alphabet rho hRhoWF) hRhoTail
          (by simpa [hLabel, AutomatonConstructionLabel.semantic] using hClock)⟩
  · -- Optimistic links include copied links and redirected final targets.
    obtain ⟨link, hLink, hTarget⟩ := Finset.mem_image.mp hLink
    obtain ⟨hLink, hSource⟩ := Finset.mem_filter.mp hLink
    obtain ⟨sourceType, targetType, hSourceType, hTargetType, hComplete⟩ :=
      compileTypeMenuLinksFuel_completion_transport (typeCompilationFuel ty) ty le_rfl link hLink
    have hEq : sourceType = rho := buildRelationSetCoreFuel_functional
      (typeCompilationFuel ty) ty (hSource ▸ hSourceType) hRelated
    subst sourceType
    exact ⟨targetType, hTarget ▸ hTargetType, hComplete⟩

/-- Starting from a related state, every state used in menu saturation remains related. -/
theorem menuReachable_related_of_currentOffer
    (ty : PactType) {bound : List String} (hWF : TypeWellFormedIn bound ty)
    (hDisjoint : ty.OfferBranchesDisjoint)
    (hNoMarker : ∀ name edge, edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges →
      edge.label ≠ .variable name)
    (hCurrent : CurrentOfferCorrespondence ty)
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho source)
    (q : TypeAutomatonState)
    (hReach : q ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable source) :
    ∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q := by
  let graph := compiledMenuGraphFuel (typeCompilationFuel ty) ty
  let allowed := graph.states.filter fun q =>
    ∃ theta, relationMembership (buildRelationSet ty (compileType ty)) theta q
  have hSeed : source ∈ allowed := Finset.mem_filter.mpr
    ⟨relationMembership_state_mem ty rho source hDisjoint hRelated, rho, hRelated⟩
  have hClosed : ∀ q ∈ allowed, graph.referencedStates q ⊆ allowed := by
    intro q hq r hr
    obtain ⟨_, theta, hTheta⟩ := Finset.mem_filter.mp hq
    obtain ⟨target, hTarget, _⟩ := menuReference_completion_backward ty hWF hNoMarker hCurrent hTheta hr
    exact Finset.mem_filter.mpr
      ⟨relationMembership_state_mem ty target r hDisjoint hTarget, target, hTarget⟩
  exact (Finset.mem_filter.mp
    (graph.futureReachable_subset_of_reference_closed source allowed hSeed hClosed hReach)).2

/-- The paper's completion invariant on the saturated menu of a related state. -/
theorem completionFlag_backward_of_menuReachable
    (ty : PactType) {bound : List String} (hWF : TypeWellFormedIn bound ty)
    (hDisjoint : ty.OfferBranchesDisjoint)
    (hNoMarker : ∀ name edge, edge ∈ (compileTypeFuel (typeCompilationFuel ty) ty).edges →
      edge.label ≠ .variable name)
    (hCurrent : CurrentOfferCorrespondence ty)
    {rho : PactType} {source : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho source)
    (q : TypeAutomatonState)
    (hReach : q ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).futureReachable source)
    (r : TypeAutomatonState)
    (hRef : r ∈ (compiledMenuGraphFuel (typeCompilationFuel ty) ty).referencedStates q)
    (hComplete : ∃ residual, (residual, r) ∈ buildRelationSetCoreFuel (typeCompilationFuel ty) ty ∧
      typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true) :
    ∃ residual, (residual, q) ∈ buildRelationSetCoreFuel (typeCompilationFuel ty) ty ∧
      typeCanCompleteThisCycleFuel (sizeOf residual + 1) residual = true := by
  obtain ⟨theta, hTheta⟩ := menuReachable_related_of_currentOffer ty hWF hDisjoint hNoMarker
    hCurrent hRelated q hReach
  obtain ⟨target, hTarget, hBack⟩ := menuReference_completion_backward ty hWF hNoMarker hCurrent hTheta hRef
  obtain ⟨candidate, hCandidate, hComplete⟩ := hComplete
  have hEq := buildRelationSetCoreFuel_functional (typeCompilationFuel ty) ty hCandidate hTarget
  exact ⟨theta, hTheta, hBack (by simpa only [hEq] using hComplete)⟩

end

end Pact
