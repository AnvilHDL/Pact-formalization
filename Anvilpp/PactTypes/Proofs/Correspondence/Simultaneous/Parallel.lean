import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.EdgeFuture
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.OfferLocality

namespace Pact

noncomputable section

open Classical Pact.NewCorrespondence

/-- Normalize each compiler call to the fuel of its own child. -/
theorem compileTypeFuel_par_eq_children (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    compileTypeFuel (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
      buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right)
        (compileTypeFuel (typeCompilationFuel (left.reannotate alphabet))
          (left.reannotate alphabet))
        (compileTypeFuel (typeCompilationFuel (right.reannotate alphabet))
          (right.reannotate alphabet))
        (computeFutureOf left) (computeFutureOf right)
        (computeFutureOf (left.reannotate alphabet))
        (computeFutureOf (right.reannotate alphabet)) := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuel]
  simp only [compileTypeFuel]
  have hL := compileTypeFuel_eq_of_sufficient left (le_max_left
    (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
  have hR := compileTypeFuel_eq_of_sufficient right (le_max_right
    (typeCompilationFuel left) (typeCompilationFuel right)) le_rfl
  have hSL := compileTypeFuel_eq_of_sufficient (left.reannotate alphabet)
    (by simpa only [TypeCompilationFuelSufficient, typeCompilationFuel_reannotate] using
      (le_max_left (typeCompilationFuel left) (typeCompilationFuel right))) le_rfl
  have hSR := compileTypeFuel_eq_of_sufficient (right.reannotate alphabet)
    (by simpa only [TypeCompilationFuelSufficient, typeCompilationFuel_reannotate] using
      (le_max_right (typeCompilationFuel left) (typeCompilationFuel right))) le_rfl
  simp only [hL, hR, hSL, hSR, Nat.min_eq_right (le_max_left _ _),
    Nat.min_eq_right (le_max_right _ _), typeCompilationFuel_reannotate]
  unfold computeFutureOf
  simp only [typeCompilationFuel_reannotate]

private theorem localEnvironment_iff (outer : TypeEnvironment) (interface : Interface)
    (ty : PactType) (sibling edge : AutomatonFragmentEdge) :
    AutomatonLocalEnvironment outer interface ty.alphabet sibling edge ↔
      LocalTypeOfferEnvironment outer interface ty sibling.environment
        sibling.current sibling.future edge.environment := by
  cases sibling
  cases edge
  constructor
  · intro h
    cases h with
    | clock hClock hSibling hEdge =>
      rw [hSibling, hEdge]
      exact .clock _ _ _ _ _ hClock
    | ordinary hClock hSibling hEdge hImmediate hFuture =>
      exact .ordinary _ _ _ _ _ _ _ hClock hSibling hEdge hImmediate hFuture
  · intro h
    cases h with
    | clock _ _ _ _ hClock => exact .clock hClock rfl rfl
    | ordinary _ _ _ _ _ _ hClock hSibling hEdge hImmediate hFuture =>
      exact .ordinary hClock hSibling hEdge hImmediate hFuture

private theorem offers_disjoint {env : TypeEnvironment} {ty rho rho' : PactType}
    {bound : List String} {q : TypeAutomatonState}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hWF : TypeWellFormedIn bound ty)
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q)
    (h : TypeOffers env rho label rho' current future) : Disjoint current future :=
  h.offers_disjoint (relationMembership_parallelMessageOwnership ty rho q hWF hRelated)

private theorem outer_avoids_interface {alphabet : PactTypeAlphabet}
    {interface : Interface} {outer : TypeEnvironment}
    (hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface)
    (hWF : outer.WellFormed alphabet) :
    (∀ action ∈ outer.immediate, action.1 ∉ interface) ∧
      (∀ action ∈ outer.future, action.1 ∉ interface) := by
  constructor
  · intro action hAction
    obtain ⟨base, hBase, rfl⟩ := Finset.mem_image.mp (hWF.2.2.1 hAction)
    exact hHidden base hBase
  · intro action hAction
    obtain ⟨base, hBase, rfl⟩ := Finset.mem_image.mp (hWF.2.2.2 hAction)
    exact hHidden base hBase

/-- The two local semantic environments publish exactly their shared outer
environment. Interface traffic disappears when the product combines them. -/
private theorem combineEnvironment_eq_outer {alphabet : PactTypeAlphabet}
    {interface : Interface} {outer : TypeEnvironment} {left right : PactType}
    {eL eR : AutomatonFragmentEdge}
    (hWF : outer.WellFormed alphabet)
    (hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface)
    (hL : LocalTypeOfferEnvironment outer interface left eR.environment
      eR.current eR.future eL.environment)
    (hR : LocalTypeOfferEnvironment outer interface right eL.environment
      eL.current eL.future eR.environment) :
    combineAutomatonEnvironment interface eL.environment eR.environment = outer := by
  obtain ⟨hImmHidden, hFutHidden⟩ := outer_avoids_interface hHidden hWF
  have hImm : hideOffers interface outer.immediate = outer.immediate :=
    Finset.filter_eq_self.mpr hImmHidden
  have hFut : hideOffers interface outer.future = outer.future :=
    Finset.filter_eq_self.mpr hFutHidden
  have hAL := (localEnvironment_iff outer interface left eR eL).mpr hL
  have hAR := (localEnvironment_iff outer interface right eL eR).mpr hR
  cases hAL with
  | clock hClock hRE hLE =>
    obtain ⟨hI, hF⟩ := hWF.1 hClock
    rw [hRE, hLE]
    cases outer
    simp_all [combineAutomatonEnvironment, TypeEnvironment.tock]
  | ordinary hClock hRC hLC hLI hLF =>
    cases hAR with
    | clock hClock' _ _ => simp_all
    | ordinary _ _ _ hRI hRF =>
      have hI := combineAutomatonEnvironment_ordinary_eq hLC hRC hLI hRI
      have hF := combineAutomatonEnvironment_ordinary_future_eq hLC hRC hLI hRI hLF hRF
      rw [hImm] at hI
      rw [hImm, hFut, Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_iff_inter_eq_empty.mpr (hWF.2.1 hClock)).symm] at hF
      have hC : (combineAutomatonEnvironment interface eL.environment eR.environment).clock =
          outer.clock := by simp [combineAutomatonEnvironment, hLC, hRC, hClock]
      cases hCombined : combineAutomatonEnvironment interface eL.environment eR.environment
      cases outer
      simp_all

/-- Restricting a local environment recovers the sibling's offers. -/
private theorem localEnvironment_interface {alphabet : PactTypeAlphabet}
    {interface : Interface} {outer : TypeEnvironment} {ty : PactType}
    {sibling edge : AutomatonFragmentEdge}
    (hWF : outer.WellFormed alphabet)
    (hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface)
    (hLocal : LocalTypeOfferEnvironment outer interface ty sibling.environment
      sibling.current sibling.future edge.environment)
    (hDisjoint : Disjoint sibling.current sibling.future)
    (hClockEmpty : outer.clock = true → sibling.current = ∅ ∧ sibling.future = ∅) :
    sameOnInterface interface sibling.current edge.environment.immediate ∧
      sameOnInterface interface sibling.future edge.environment.future := by
  obtain ⟨hImmHidden, hFutHidden⟩ := outer_avoids_interface hHidden hWF
  have hAL := (localEnvironment_iff outer interface ty sibling edge).mpr hLocal
  cases hAL with
  | clock hClock _ hEdge =>
    obtain ⟨hC, hF⟩ := hClockEmpty hClock
    simp [sameOnInterface, hC, hF, hEdge, TypeEnvironment.tock, restrictTypeOffers]
  | ordinary _ _ _ hI hF =>
    constructor
    · unfold sameOnInterface
      ext action
      simp only [restrictTypeOffers, hI, Finset.mem_filter,
        Finset.mem_union]
      constructor
      · rintro ⟨hC, hIn⟩; exact ⟨Or.inr ⟨hC, hIn⟩, hIn⟩
      · rintro ⟨hOuter | ⟨hC, _⟩, hIn⟩
        · exact False.elim (hImmHidden action hOuter hIn)
        · exact ⟨hC, hIn⟩
    · unfold sameOnInterface
      ext action
      simp only [restrictTypeOffers, hF, hI, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_union, not_or]
      constructor
      · rintro ⟨hFuture, hIn⟩
        exact ⟨⟨Or.inr ⟨hFuture, hIn⟩,
          (fun h => hImmHidden action h hIn),
          (fun h => Finset.disjoint_left.mp hDisjoint h.1 hFuture)⟩, hIn⟩
      · rintro ⟨⟨hOuter | ⟨hFuture, _⟩, _⟩, hIn⟩
        · exact False.elim (hFutHidden action hOuter hIn)
        · exact ⟨hFuture, hIn⟩

private theorem represented_skip_of_accepting {ty rho : PactType}
    {q : TypeAutomatonState} (hWF : ty.AlphabetWellFormed)
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q)
    (hAccept : q ∈ (compileType ty).accepting) : rho = .skip ty.alphabet := by
  obtain ⟨alphabet, hSkip⟩ := final_state_represents_skip ty hRelated hAccept
  have hAlpha := relationMembership_alphabet_eq_of_wellFormed ty rho q hWF hRelated
  rw [hSkip] at hAlpha
  change alphabet = ty.alphabet at hAlpha
  rw [hSkip, hAlpha]

private theorem related_accepting_iff {ty rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q) :
    q ∈ (compileTypeFuel (typeCompilationFuel ty) ty).accepting ↔
      rho = .skip rho.alphabet := by
  constructor
  · intro hAccept
    obtain ⟨alphabet, rfl⟩ := final_state_represents_skip ty hRelated hAccept
    rfl
  · intro hSkip
    exact accepting_of_skip_residual ty (hSkip ▸ hRelated)

private theorem localEnvironment_clock {outer : TypeEnvironment} {interface : Interface}
    {ty : PactType} {sibling edge : AutomatonFragmentEdge}
    (hLocal : LocalTypeOfferEnvironment outer interface ty sibling.environment
      sibling.current sibling.future edge.environment)
    (hClock : outer.clock = true) : edge.environment.clock = true := by
  cases (localEnvironment_iff outer interface ty sibling edge).mpr hLocal with
  | clock _ _ hE => simp [hE, TypeEnvironment.tock]
  | ordinary hNonClock _ _ _ _ => simp_all

private theorem sync_of_local {alphabet : PactTypeAlphabet} {interface : Interface}
    {outer : TypeEnvironment} {left right : PactType} {eL eR : AutomatonFragmentEdge}
    (hWF : outer.WellFormed alphabet)
    (hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface)
    (hL : LocalTypeOfferEnvironment outer interface left eR.environment
      eR.current eR.future eL.environment)
    (hR : LocalTypeOfferEnvironment outer interface right eL.environment
      eL.current eL.future eR.environment)
    (hLD : Disjoint eL.current eL.future) (hRD : Disjoint eR.current eR.future)
    (hLC : outer.clock = true → eL.current = ∅ ∧ eL.future = ∅)
    (hRC : outer.clock = true → eR.current = ∅ ∧ eR.future = ∅)
    (hSync : TypeLabel.Sync interface eL.label.semantic eR.label.semantic) :
    combineAutomatonEnvironment interface eL.environment eR.environment = outer ∧
      syncAutomatonEdges left.alphabet right.alphabet interface eL eR := by
  have hEnv := combineEnvironment_eq_outer hWF hHidden hL hR
  have hLI := localEnvironment_interface hWF hHidden hL hRD hRC
  have hRI := localEnvironment_interface hWF hHidden hR hLD hLC
  refine ⟨hEnv, ?_⟩
  unfold syncAutomatonEdges
  rw [hEnv]
  exact ⟨(localEnvironment_iff _ _ _ _ _).mpr hL,
    (localEnvironment_iff _ _ _ _ _).mpr hR,
    hRI.1, hLI.1, hRI.2, hLI.2, hSync⟩

/-- The synchronized family uses the original child edges and their complete
offers. Final-state equivalence decides whether its target is a pair or done. -/
theorem offer_par_sync_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR targetL targetR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {qL qR : TypeAutomatonState} {outer envL envR : TypeEnvironment}
    {labelL labelR : TypeLabel} {cL fL cR fR : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hStepL : DecoratedTypeTransition envL rhoL labelL ⟨cL, fL⟩ targetL)
    (hStepR : DecoratedTypeTransition envR rhoR labelR ⟨cR, fR⟩ targetR)
    (hLocalL : LocalTypeOfferEnvironment outer interface rhoL envR cR fR envL)
    (hLocalR : LocalTypeOfferEnvironment outer interface rhoR envL cL fL envR)
    (hOuter : outer.WellFormed alphabet)
    (hSync : TypeLabel.Sync interface labelL labelR)
    (hGuard : ¬ (targetL = .skip targetL.alphabet ∧ targetR = .skip targetR.alphabet) →
      rhoL ≠ .skip rhoL.alphabet ∧ rhoR ≠ .skip rhoR.alphabet) :
    ∃ qL' qR',
      relationMembership (buildRelationSet left (compileType left)) targetL qL' ∧
      relationMembership (buildRelationSet right (compileType right)) targetR qR' ∧
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer
        (TypeLabel.combine interface labelL labelR) ⟨hideTypeOffers interface (cL ∪ cR),
          if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (fL ∪ fR)⟩
        (if qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
            qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting
          then .final else .pair qL' qR') := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface :=
    fun _ hAction => parent_no_interface hCompat.2.1 hAction
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL qL hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR qR hRWF.1 hRelR
  obtain ⟨qL', hEdgeL, hTargetL⟩ := hLeft.1 hRelL hStepL
  obtain ⟨qR', hEdgeR, hTargetR⟩ := hRight.1 hRelR hStepR
  let eL : AutomatonFragmentEdge := ⟨qL, envL, .visible labelL, cL, fL, qL'⟩
  let eR : AutomatonFragmentEdge := ⟨qR, envR, .visible labelR, cR, fR, qR'⟩
  have hEL := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeL
  have hER := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeR
  have hLE : LocalTypeOfferEnvironment outer interface rhoL eR.environment
      eR.current eR.future eL.environment := hLocalL
  have hRE : LocalTypeOfferEnvironment outer interface rhoR eL.environment
      eL.current eL.future eR.environment := hLocalR
  obtain ⟨hEnv, hEdgesSync⟩ := sync_of_local hOuter hHidden hLE hRE
    (offers_disjoint hLWF hRelL hStepL.2) (offers_disjoint hRWF hRelR hStepR.2)
    (fun hClock => edge_offers_empty_of_clock hLeft hRelL hEdgeL
      (localEnvironment_clock hLE hClock))
    (fun hClock => edge_offers_empty_of_clock hRight hRelR hEdgeR
      (localEnvironment_clock hRE hClock)) hSync
  rw [hAlphaL, hAlphaR] at hEdgesSync
  let target : TypeAutomatonState :=
    if qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting
      then .final else .pair qL' qR'
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, combineAutomatonEnvironment interface envL envR,
      .visible (TypeLabel.combine interface labelL labelR), hideOffers interface (cL ∪ cR),
      parallelFutureSpec (.visible (TypeLabel.combine interface labelL labelR))
        (hideOffers interface (fL ∪ fR)), target⟩
  have hRaw : raw ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl
    simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter]
    refine ⟨eL, hEL, eR, ⟨hER, hEdgesSync, ?_⟩, rfl⟩
    intro hNotFinal
    have hLive := hGuard (by
      simpa only [← related_accepting_iff hTargetL, ← related_accepting_iff hTargetR] using hNotFinal)
    exact ⟨fun h => hLive.1 ((related_accepting_iff hRelL).mp h),
      fun h => hLive.2 ((related_accepting_iff hRelR).mp h)⟩
  refine ⟨qL', qR', hTargetL, hTargetR, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge]
  refine ⟨raw, hRaw, rfl, hEnv, rfl, rfl, ?_, rfl⟩
  change resolveFutureSpec (computeFutureOf (.par alphabet left right interface)) raw.future = _
  dsimp only [raw]
  simp only [parallelFutureSpec, AutomatonConstructionLabel.semantic]
  split_ifs <;> rfl

private theorem represented_alphabetWellFormed {ty rho : PactType} {q : TypeAutomatonState}
    {bound : List String} (hWF : TypeWellFormedIn bound ty)
    (hRelated : relationMembership (buildRelationSet ty (compileType ty)) rho q) :
    rho.AlphabetWellFormed := by
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  obtain ⟨hA, _, _, _, _, hTR, _, _, _, _, _, _, hIS, hIAS, _⟩ := hWF
  exact relationMembership_alphabetWellFormed
    committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
    ty rho q hA hIS hIAS hTR hDisjoint hRelated

private theorem resolved_hasEdge {ty : PactType} {edge : AutomatonFragmentEdge}
    {label : TypeLabel}
    (hMem : edge ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel ty) ty) (computeFutureOf ty))
    (hLabel : edge.label = .visible label) :
    (compileType ty).HasEdge edge.source edge.environment label
      ⟨edge.current, edge.future⟩ edge.target := by
  rw [compileType_hasEdge_iff_resolvedEdge_mem, ← hLabel]
  exact hMem

private theorem combined_environment_wellFormed {parent left right : PactTypeAlphabet}
    {interface : Interface} {eL eR : AutomatonFragmentEdge}
    (hHide : PactTypeAlphabet.hideInterface left interface = parent)
    (hWF : eL.environment.WellFormed left)
    (hSync : syncAutomatonEdges left right interface eL eR) :
    (combineAutomatonEnvironment interface eL.environment eR.environment).WellFormed parent := by
  obtain ⟨hL, hR, _⟩ := hSync
  apply PactTypeAlphabet.environment_wellFormed
  refine combineAutomatonEnvironment_mem_localEnvironments hHide hL hR ?_ ?_
  · cases hL with
    | clock _ hRE hLE => simp [combineAutomatonEnvironment, hLE, hRE, TypeEnvironment.tock]
    | ordinary _ _ _ hI _ =>
      intro action hAction
      exact hWF.2.2.1 (by rw [hI]; exact Finset.mem_union_left _ hAction)
  · cases hL with
    | clock _ hRE hLE => simp [combineAutomatonEnvironment, hLE, hRE, TypeEnvironment.tock]
    | ordinary _ _ _ hI hF =>
      intro action hAction
      by_cases hImm : action ∈ eL.environment.immediate
      · exact hWF.2.2.1 hImm
      · apply hWF.2.2.2
        rw [hF]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hAction, hImm⟩

/-- Invert a synchronized edge using the same child witnesses. The compiler's
final-state test selects the semantic parallel or fusion rule. -/
theorem offer_par_sync_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {eL eR : AutomatonFragmentEdge} {labelL labelR : TypeLabel}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL eL.source)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR eR.source)
    (hMemL : eL ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel left) left) (computeFutureOf left))
    (hMemR : eR ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel right) right) (computeFutureOf right))
    (hLabelL : eL.label = .visible labelL) (hLabelR : eR.label = .visible labelR)
    (hSync : syncAutomatonEdges left.alphabet right.alphabet interface eL eR)
    (hGuard : ¬ (eL.target ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        eR.target ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting) →
      eL.source ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        eR.source ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting) :
    ∃ target,
      DecoratedTypeTransition (combineAutomatonEnvironment interface eL.environment eR.environment)
        (.par alphabet rhoL rhoR interface) (TypeLabel.combine interface labelL labelR)
        ⟨hideTypeOffers interface (eL.current ∪ eR.current),
          if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target
        (if eL.target ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
            eR.target ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting
          then .final else .pair eL.target eR.target) := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL _ hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR _ hRWF.1 hRelR
  obtain ⟨targetL, hStepL, hTargetL⟩ := hLeft.2 hRelL
    (resolved_hasEdge hMemL hLabelL)
  obtain ⟨targetR, hStepR, hTargetR⟩ := hRight.2 hRelR
    (resolved_hasEdge hMemR hLabelR)
  have hEnvWF : eL.environment.WellFormed left.alphabet := by
    rw [← hAlphaL]
    exact PactType.typeOffers_env_wellFormed hStepL.2
      (represented_alphabetWellFormed hLWF hRelL)
  have hOuter := combined_environment_wellFormed hCompat.2.1.parent_eq_left hEnvWF hSync
  obtain ⟨hLE, hRE, _, _, _, _, hLabelSync⟩ := hSync
  rw [← hAlphaL] at hLE
  rw [← hAlphaR] at hRE
  have hLocalL := (localEnvironment_iff _ _ rhoL eR eL).mp hLE
  have hLocalR := (localEnvironment_iff _ _ rhoR eL eR).mp hRE
  simp only [hLabelL, hLabelR, AutomatonConstructionLabel.semantic] at hLabelSync
  by_cases hDone : eL.target ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
      eR.target ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting
  · have hSkipL : targetL = .skip rhoL.alphabet := by
      rw [represented_skip_of_accepting hLWF.1 hTargetL hDone.1, hAlphaL]
    have hSkipR : targetR = .skip rhoR.alphabet := by
      rw [represented_skip_of_accepting hRWF.1 hTargetR hDone.2, hAlphaR]
    rw [hSkipL] at hStepL
    rw [hSkipR] at hStepR
    rw [if_pos hDone]
    by_cases hClock : TypeLabel.combine interface labelL labelR = TypeLabel.tock
    · have hOffers := TypeOffers.par_fuse_tock _ _ _ interface alphabet rhoL rhoR
        labelL labelR _ _ _ _ hStepL.2 hStepR.2 hLocalL hLocalR ⟨hOuter, hLabelSync⟩ hClock
      obtain ⟨hCL, hCR⟩ := (TypeLabel.combine_eq_tock_iff _ _ _).mp hClock
      have hCurr : hideTypeOffers interface (eL.current ∪ eR.current) = ∅ := by
        have hEL : eL.current = ∅ := hStepL.2.current_eq_empty_of_label_tock hCL
        have hER : eR.current = ∅ := hStepR.2.current_eq_empty_of_label_tock hCR
        rw [hEL, hER]
        simp [hideTypeOffers]
      rw [hCurr, if_pos hClock]
      exact ⟨.skip alphabet, ⟨hOffers.toTypeTransition, hOffers⟩,
        relationMembership_par_final alphabet left right interface⟩
    · have hOffers := TypeOffers.par_fuse _ _ _ interface alphabet rhoL rhoR
        labelL labelR _ _ _ _ hStepL.2 hStepR.2 hLocalL hLocalR ⟨hOuter, hLabelSync⟩ hClock
      rw [if_neg hClock]
      exact ⟨.skip alphabet, ⟨hOffers.toTypeTransition, hOffers⟩,
        relationMembership_par_final alphabet left right interface⟩
  · have hLive := hGuard hDone
    have hNotDone : ¬ (targetL = .skip targetL.alphabet ∧ targetR = .skip targetR.alphabet) := by
      simpa only [← related_accepting_iff hTargetL, ← related_accepting_iff hTargetR] using hDone
    have hOffers := TypeOffers.par _ _ _ interface alphabet rhoL targetL rhoR targetR
      labelL labelR _ _ _ _ (mt (related_accepting_iff hRelL).mpr hLive.1)
      (mt (related_accepting_iff hRelR).mpr hLive.2) hStepL.2 hStepR.2 hNotDone
      hLocalL hLocalR ⟨hOuter, hLabelSync⟩
    rw [if_neg hDone]
    exact ⟨.par alphabet targetL targetR interface, ⟨hOffers.toTypeTransition, hOffers⟩,
      relationMembership_par_product alphabet left right interface hTargetL hTargetR⟩

/-- A `skip` source has only its silent self-loop, with empty current and
future offers. -/
private theorem skip_step_offers {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage} (hSource : source = .skip alphabet)
    (hOffers : TypeOffers env source label target current future) :
    label = TypeLabel.silent ∧ target = source ∧ current = ∅ ∧ future = ∅ := by
  subst hSource
  cases hOffers with
  | skip _ _ _ =>
    exact ⟨rfl, rfl, rfl, by simp [typeFutureOffers, typeFutureOffersFuel]⟩

/-- Survivor entry on the left.  The finished component contributes its silent
`skip` edge, whose source and target are both accepting and whose offers are
empty, so the `SyncEdges_I` witness carries `Sync_I(ε, α₂)`.  Hence
`ε ∪_I α₂ = α₂` and the published current offer is `hide_I(O_C₂)`. -/
theorem offer_par_leftComplete_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR targetR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {qL qR : TypeAutomatonState} {outer envL envR : TypeEnvironment}
    {label : TypeLabel} {cL fL cR fR : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hLeftSkip : rhoL = .skip rhoL.alphabet)
    (hRightLive : rhoR ≠ .skip rhoR.alphabet)
    (hTargetLive : targetR ≠ .skip targetR.alphabet)
    (hStepL : DecoratedTypeTransition envL rhoL TypeLabel.silent ⟨cL, fL⟩ rhoL)
    (hStepR : DecoratedTypeTransition envR rhoR label ⟨cR, fR⟩ targetR)
    (hLocalL : LocalTypeOfferEnvironment outer interface rhoL envR cR fR envL)
    (hLocalR : LocalTypeOfferEnvironment outer interface rhoR envL cL fL envR)
    (hOuter : outer.WellFormed alphabet)
    (hSync : TypeLabel.Sync interface TypeLabel.silent label) :
    ∃ q',
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer label
        ⟨hideTypeOffers interface cR, hideTypeOffers interface fR⟩ (.survivor 1 q') ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
        (targetR.reannotate alphabet) (.survivor 1 q') := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface :=
    fun _ hAction => parent_no_interface hCompat.2.1 hAction
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL qL hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR qR hRWF.1 hRelR
  have hEmptyL : cL = ∅ := (skip_step_offers hLeftSkip hStepL.2).2.2.1
  have hFutureEmpty : fL = ∅ :=
    (skip_step_offers hLeftSkip hStepL.2).2.2.2
  have hNotClock : label ≠ TypeLabel.tock := by
    intro hClock
    have h := hSync.2.2.mpr (by rw [hClock]; trivial)
    simpa [TypeLabel.silent, TypeLabel.isTock] using h
  obtain ⟨qL', hEdgeL, hTargetL⟩ := hLeft.1 hRelL hStepL
  obtain ⟨qR', hEdgeR, hTargetR⟩ := hRight.1 hRelR hStepR
  let eL : AutomatonFragmentEdge := ⟨qL, envL, .visible TypeLabel.silent, cL, fL, qL'⟩
  let eR : AutomatonFragmentEdge := ⟨qR, envR, .visible label, cR, fR, qR'⟩
  have hEL := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeL
  have hER := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeR
  have hLE : LocalTypeOfferEnvironment outer interface rhoL eR.environment
      eR.current eR.future eL.environment := hLocalL
  have hRE : LocalTypeOfferEnvironment outer interface rhoR eL.environment
      eL.current eL.future eR.environment := hLocalR
  obtain ⟨hEnv, hEdgesSync⟩ := sync_of_local hOuter hHidden hLE hRE
    (offers_disjoint hLWF hRelL hStepL.2) (offers_disjoint hRWF hRelR hStepR.2)
    (fun hClock => edge_offers_empty_of_clock hLeft hRelL hEdgeL
      (localEnvironment_clock hLE hClock))
    (fun hClock => edge_offers_empty_of_clock hRight hRelR hEdgeR
      (localEnvironment_clock hRE hClock)) hSync
  rw [hAlphaL, hAlphaR] at hEdgesSync
  -- Both left states represent `skip`, and both right states are live.
  have hSourceFinal : eL.source ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting :=
    (related_accepting_iff hRelL).mpr hLeftSkip
  have hTargetFinal : eL.target ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting :=
    (related_accepting_iff hTargetL).mpr hLeftSkip
  have hSourceLive : eR.source ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
    mt (related_accepting_iff hRelR).mp hRightLive
  have hTargetNotFinal :
      eR.target ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
    mt (related_accepting_iff hTargetR).mp hTargetLive
  let state : TypeAutomatonState := .survivor 1 qR'
  let combined := AutomatonConstructionLabel.combine interface eL.label eR.label
  let published := hideOffers interface (eL.current ∪ eR.current)
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, combineAutomatonEnvironment interface envL envR, combined,
      published, parallelFutureSpec combined (hideOffers interface (eL.future ∪ eR.future)), state⟩
  have hRaw : raw ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inr
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter]
    exact ⟨eL, hEL, eR, ⟨hER, hEdgesSync, hSourceFinal, hTargetFinal, hSourceLive,
      hTargetNotFinal⟩, rfl⟩
  have hLabelEq : raw.label = .visible label := by
    simp only [raw, combined, eL, eR, AutomatonConstructionLabel.combine,
      TypeLabel.combine_silent_left interface label hSync]
  have hCurrentEq : raw.current = hideTypeOffers interface cR := by
    simp only [raw, published, eL, eR, hEmptyL, Finset.empty_union, hideOffers,
      hideTypeOffers]
  refine ⟨qR', ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨raw, hRaw, rfl, hEnv, hLabelEq, hCurrentEq, ?_, rfl⟩
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      (parallelFutureSpec combined (hideOffers interface (eL.future ∪ eR.future))) = _
    change combined = .visible label at hLabelEq
    simp [hLabelEq, parallelFutureSpec, resolveFutureSpec,
      AutomatonConstructionLabel.semantic, hNotClock, eL, eR, hFutureEmpty,
      hideOffers, hideTypeOffers]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hRWF
    exact survivorRight_relationMembership alphabet left right interface
      (offerBranchesDisjoint_of_wellFormedIn hRWF)
      (relationMembership_reannotate hRWF hCompat.1
        (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
          (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1 hAction)) hTargetR)
      hTargetNotFinal

/-- Invert a left survivor-entry edge through the `SyncEdges_I` witness it was
built from.  The finished component's edge runs between accepting states, so it
carries `skip`'s silent step and `Sync_I(ε, α₂)` is exactly the premise
T-Par-Left needs. -/
theorem offer_par_leftComplete_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {eL eR : AutomatonFragmentEdge} {labelL labelR : TypeLabel}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL eL.source)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR eR.source)
    (hMemL : eL ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel left) left) (computeFutureOf left))
    (hMemR : eR ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel right) right) (computeFutureOf right))
    (hLabelL : eL.label = .visible labelL) (hLabelR : eR.label = .visible labelR)
    (hSync : syncAutomatonEdges left.alphabet right.alphabet interface eL eR)
    (hSourceFinal : eL.source ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hTargetFinal : eL.target ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hSourceLive : eR.source ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hTargetLive : eR.target ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting) :
    ∃ target,
      DecoratedTypeTransition
        (combineAutomatonEnvironment interface eL.environment eR.environment)
        (.par alphabet rhoL rhoR interface) (TypeLabel.combine interface labelL labelR)
        ⟨hideTypeOffers interface (eL.current ∪ eR.current),
          if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target
        (.survivor 1 eR.target) := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL _ hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR _ hRWF.1 hRelR
  obtain ⟨targetL, hStepL, hTargetL⟩ := hLeft.2 hRelL
    (resolved_hasEdge hMemL hLabelL)
  obtain ⟨targetR, hStepR, hTargetR⟩ := hRight.2 hRelR
    (resolved_hasEdge hMemR hLabelR)
  have hEnvWF : eL.environment.WellFormed left.alphabet := by
    rw [← hAlphaL]
    exact PactType.typeOffers_env_wellFormed hStepL.2
      (represented_alphabetWellFormed hLWF hRelL)
  have hOuter := combined_environment_wellFormed hCompat.2.1.parent_eq_left hEnvWF hSync
  obtain ⟨hLE, hRE, _, _, _, _, hLabelSync⟩ := hSync
  rw [← hAlphaL] at hLE
  rw [← hAlphaR] at hRE
  have hLocalL := (localEnvironment_iff _ _ rhoL eR eL).mp hLE
  have hLocalR := (localEnvironment_iff _ _ rhoR eL eR).mp hRE
  simp only [hLabelL, hLabelR, AutomatonConstructionLabel.semantic] at hLabelSync
  -- The finished component's edge is `skip`'s silent self-loop.
  have hLeftSkip : rhoL = .skip rhoL.alphabet := (related_accepting_iff hRelL).mp hSourceFinal
  obtain ⟨hSilent, hLoop, hEmptyRaw, hFutureEmpty⟩ := skip_step_offers hLeftSkip hStepL.2
  dsimp only at hFutureEmpty
  have hEmptyL : eL.current = ∅ := hEmptyRaw
  rw [hSilent] at hStepL hLabelSync
  rw [hLoop] at hStepL
  have hNotClock : labelR ≠ TypeLabel.tock := by
    intro hClock
    have h := hLabelSync.2.2.mpr (by rw [hClock]; trivial)
    simpa [TypeLabel.silent, TypeLabel.isTock] using h
  have hRightNotSkip := mt (related_accepting_iff hRelR).mpr hSourceLive
  have hTargetNotSkip := mt (related_accepting_iff hTargetR).mpr hTargetLive
  have hOffers := TypeOffers.left_complete
    (combineAutomatonEnvironment interface eL.environment eR.environment)
    eL.environment eR.environment interface alphabet rhoL rhoR targetR labelR
    eL.current eL.future eR.current eR.future hLeftSkip hRightNotSkip hStepL.2
    hStepR.2 hTargetNotSkip hLocalL hLocalR hOuter hLabelSync
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hRWF
  have hTargetRel := survivorRight_relationMembership alphabet left right interface
    (offerBranchesDisjoint_of_wellFormedIn hRWF)
    (relationMembership_reannotate hRWF hCompat.1
      (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
        (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1 hAction)) hTargetR)
    hTargetLive
  -- `ε ∪_I α₂ = α₂`, and the finished component published nothing.
  rw [hSilent, TypeLabel.combine_silent_left interface labelR hLabelSync, hEmptyL,
    Finset.empty_union, if_neg hNotClock, hFutureEmpty,
    Finset.empty_union]
  exact ⟨targetR.reannotate alphabet, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩

/-- A re-signed left-child step stays in its survivor copy, or enters the
parallel final state when the child completes. -/
theorem offer_par_survivorLeft_forward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : TypeAutomatonStepCorrespondence (left.reannotate alphabet))
    {rho rho' : PactType} {q : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (left.reannotate alphabet)
      (compileType (left.reannotate alphabet))) rho q)
    (hStep : DecoratedTypeTransition env rho label ⟨current, future⟩ rho') :
    ∃ q',
      (compileType (.par alphabet left right interface)).HasEdge (.survivor 0 q)
        env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hLeftWF := (typeWellFormedIn_par hWF).1
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).1
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLeftWF
  obtain ⟨q', hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
  let edge : AutomatonFragmentEdge :=
    ⟨q, env, .visible label, current, future, q'⟩
  have hEdgeMem := (compileType_hasEdge_iff_resolvedEdge_mem
    (left.reannotate alphabet) q q' env label ⟨current, future⟩).mp hEdge
  let lifted := survivorLeftEdge
    (compileTypeFuel (typeCompilationFuel (left.reannotate alphabet))
      (left.reannotate alphabet)) edge
  have hLifted : lifted ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    exact ((buildParallelAutomaton_outgoing_survivorLeft
      _ _ _ _ _ _ _ _ _ _ _ _ q lifted).mpr ⟨edge, hEdgeMem, rfl, rfl⟩).1
  refine ⟨lifted.target, ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨lifted, hLifted, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals try { simp only [lifted, survivorLeftEdge, edge]; split <;> rfl }
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      lifted.future = future
    dsimp only [lifted]
    have hClockEmpty : label = TypeLabel.tock → future = ∅ :=
      fun h => hStep.2.future_eq_empty_of_label_tock h
    unfold survivorLeftEdge
    split <;> by_cases hClock : label = TypeLabel.tock <;>
      simp [edge, parallelFutureSpec, resolveFutureSpec,
        AutomatonConstructionLabel.semantic, hClock, hClockEmpty]
  · by_cases hAccept : q' ∈ (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet)) (left.reannotate alphabet)).accepting
    · have hSkip := represented_skip_of_accepting hSurvivorWF.1 hTarget hAccept
      simp only [PactType.reannotate_alphabet] at hSkip
      rw [hSkip]
      simpa only [lifted, survivorLeftEdge, edge, if_pos hAccept] using
        relationMembership_par_final alphabet left right interface
    · have hNot : q' ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
        rw [← accepting_reannotate hDisjoint alphabet]
        exact hAccept
      simpa only [lifted, survivorLeftEdge, edge, if_neg hAccept] using
        survivorLeft_relationMembership alphabet left right interface hDisjoint hTarget hNot

theorem offer_par_survivorLeft_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : TypeAutomatonStepCorrespondence (left.reannotate alphabet))
    {rho : PactType} {q q' : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (left.reannotate alphabet)
      (compileType (left.reannotate alphabet))) rho q)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.survivor 0 q)
      env label ⟨current, future⟩ q') :
    ∃ rho', DecoratedTypeTransition env rho label ⟨current, future⟩ rho' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hLeftWF := (typeWellFormedIn_par hWF).1
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).1
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLeftWF
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrentEq, hFutureEq, hTargetEq⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  rw [compileTypeFuel_par_eq_children] at hMem
  obtain ⟨edge, hEdgeMem, hChildSource, rfl⟩ :=
    (buildParallelAutomaton_outgoing_survivorLeft
      _ _ _ _ _ _ _ _ _ _ _ _ q raw).mp ⟨hMem, hSource⟩
  have hFields : edge.environment = env ∧ edge.label = .visible label ∧
      edge.current = current := by
    unfold survivorLeftEdge at hEnv hLabel hCurrentEq
    split at hEnv <;> simp_all
  have hChild : (compileType (left.reannotate alphabet)).HasEdge q env label
      ⟨current, edge.future⟩ edge.target := by
    rw [compileType_hasEdge_iff_resolvedEdge_mem]
    have hEq : (⟨q, env, .visible label, current, edge.future, edge.target⟩ :
        AutomatonFragmentEdge) = edge := by
      cases edge
      simp_all
    rw [hEq]
    exact hEdgeMem
  obtain ⟨rho', hStep, hTarget⟩ := hCurrent.2 hRelated hChild
  have hFuture : edge.future = future := by
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      (survivorLeftEdge _ edge).future = future at hFutureEq
    have hClockEmpty : label = TypeLabel.tock → edge.future = ∅ :=
      fun h => hStep.2.future_eq_empty_of_label_tock h
    unfold survivorLeftEdge at hFutureEq
    split at hFutureEq <;> by_cases hClock : label = TypeLabel.tock
    all_goals
      simpa [parallelFutureSpec, resolveFutureSpec, hFields.2.1,
        AutomatonConstructionLabel.semantic, hClock, hClockEmpty] using hFutureEq
  rw [hFuture] at hStep
  refine ⟨rho', hStep, ?_⟩
  by_cases hAccept : edge.target ∈ (compileTypeFuel
      (typeCompilationFuel (left.reannotate alphabet)) (left.reannotate alphabet)).accepting
  · have hSkip := represented_skip_of_accepting hSurvivorWF.1 hTarget hAccept
    simp only [PactType.reannotate_alphabet] at hSkip
    simp only [survivorLeftEdge, if_pos hAccept] at hTargetEq
    rw [hSkip, ← hTargetEq]
    exact relationMembership_par_final alphabet left right interface
  · have hNot : edge.target ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting := by
      rw [← accepting_reannotate hDisjoint alphabet]
      exact hAccept
    simp only [survivorLeftEdge, if_neg hAccept] at hTargetEq
    rw [← hTargetEq]
    exact survivorLeft_relationMembership alphabet left right interface hDisjoint hTarget hNot

/-- A re-signed right-child step stays in its survivor copy, or enters the
parallel final state when the child completes. -/
theorem offer_par_survivorRight_forward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : TypeAutomatonStepCorrespondence (right.reannotate alphabet))
    {rho rho' : PactType} {q : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (right.reannotate alphabet)
      (compileType (right.reannotate alphabet))) rho q)
    (hStep : DecoratedTypeTransition env rho label ⟨current, future⟩ rho') :
    ∃ q',
      (compileType (.par alphabet left right interface)).HasEdge (.survivor 1 q)
        env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hRightWF := (typeWellFormedIn_par hWF).2
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).2
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRightWF
  obtain ⟨q', hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
  let edge : AutomatonFragmentEdge :=
    ⟨q, env, .visible label, current, future, q'⟩
  have hEdgeMem := (compileType_hasEdge_iff_resolvedEdge_mem
    (right.reannotate alphabet) q q' env label ⟨current, future⟩).mp hEdge
  let lifted := survivorRightEdge
    (compileTypeFuel (typeCompilationFuel (right.reannotate alphabet))
      (right.reannotate alphabet)) edge
  have hLifted : lifted ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    exact ((buildParallelAutomaton_outgoing_survivorRight
      _ _ _ _ _ _ _ _ _ _ _ _ q lifted).mpr ⟨edge, hEdgeMem, rfl, rfl⟩).1
  refine ⟨lifted.target, ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨lifted, hLifted, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals try { simp only [lifted, survivorRightEdge, edge]; split <;> rfl }
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      lifted.future = future
    dsimp only [lifted]
    have hClockEmpty : label = TypeLabel.tock → future = ∅ :=
      fun h => hStep.2.future_eq_empty_of_label_tock h
    unfold survivorRightEdge
    split <;> by_cases hClock : label = TypeLabel.tock <;>
      simp [edge, parallelFutureSpec, resolveFutureSpec,
        AutomatonConstructionLabel.semantic, hClock, hClockEmpty]
  · by_cases hAccept : q' ∈ (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet)) (right.reannotate alphabet)).accepting
    · have hSkip := represented_skip_of_accepting hSurvivorWF.1 hTarget hAccept
      simp only [PactType.reannotate_alphabet] at hSkip
      rw [hSkip]
      simpa only [lifted, survivorRightEdge, edge, if_pos hAccept] using
        relationMembership_par_final alphabet left right interface
    · have hNot : q' ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting := by
        rw [← accepting_reannotate hDisjoint alphabet]
        exact hAccept
      simpa only [lifted, survivorRightEdge, edge, if_neg hAccept] using
        survivorRight_relationMembership alphabet left right interface hDisjoint hTarget hNot

theorem offer_par_survivorRight_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : TypeAutomatonStepCorrespondence (right.reannotate alphabet))
    {rho : PactType} {q q' : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (right.reannotate alphabet)
      (compileType (right.reannotate alphabet))) rho q)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.survivor 1 q)
      env label ⟨current, future⟩ q') :
    ∃ rho', DecoratedTypeTransition env rho label ⟨current, future⟩ rho' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hRightWF := (typeWellFormedIn_par hWF).2
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).2
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRightWF
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrentEq, hFutureEq, hTargetEq⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  rw [compileTypeFuel_par_eq_children] at hMem
  obtain ⟨edge, hEdgeMem, hChildSource, rfl⟩ :=
    (buildParallelAutomaton_outgoing_survivorRight
      _ _ _ _ _ _ _ _ _ _ _ _ q raw).mp ⟨hMem, hSource⟩
  have hFields : edge.environment = env ∧ edge.label = .visible label ∧
      edge.current = current := by
    unfold survivorRightEdge at hEnv hLabel hCurrentEq
    split at hEnv <;> simp_all
  have hChild : (compileType (right.reannotate alphabet)).HasEdge q env label
      ⟨current, edge.future⟩ edge.target := by
    rw [compileType_hasEdge_iff_resolvedEdge_mem]
    have hEq : (⟨q, env, .visible label, current, edge.future, edge.target⟩ :
        AutomatonFragmentEdge) = edge := by
      cases edge
      simp_all
    rw [hEq]
    exact hEdgeMem
  obtain ⟨rho', hStep, hTarget⟩ := hCurrent.2 hRelated hChild
  have hFuture : edge.future = future := by
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      (survivorRightEdge _ edge).future = future at hFutureEq
    have hClockEmpty : label = TypeLabel.tock → edge.future = ∅ :=
      fun h => hStep.2.future_eq_empty_of_label_tock h
    unfold survivorRightEdge at hFutureEq
    split at hFutureEq <;> by_cases hClock : label = TypeLabel.tock
    all_goals
      simpa [parallelFutureSpec, resolveFutureSpec, hFields.2.1,
        AutomatonConstructionLabel.semantic, hClock, hClockEmpty] using hFutureEq
  rw [hFuture] at hStep
  refine ⟨rho', hStep, ?_⟩
  by_cases hAccept : edge.target ∈ (compileTypeFuel
      (typeCompilationFuel (right.reannotate alphabet)) (right.reannotate alphabet)).accepting
  · have hSkip := represented_skip_of_accepting hSurvivorWF.1 hTarget hAccept
    simp only [PactType.reannotate_alphabet] at hSkip
    simp only [survivorRightEdge, if_pos hAccept] at hTargetEq
    rw [hSkip, ← hTargetEq]
    exact relationMembership_par_final alphabet left right interface
  · have hNot : edge.target ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting := by
      rw [← accepting_reannotate hDisjoint alphabet]
      exact hAccept
    simp only [survivorRightEdge, if_neg hAccept] at hTargetEq
    rw [← hTargetEq]
    exact survivorRight_relationMembership alphabet left right interface hDisjoint hTarget hNot


/-- Survivor entry on the right: mirror of `offer_par_leftComplete_forward`.
The finished right component contributes its silent `skip` edge, so the witness
carries `Sync_I(α₁, ε)` and `α₁ ∪_I ε = α₁`. -/
theorem offer_par_rightComplete_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR targetL : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {qL qR : TypeAutomatonState} {outer envL envR : TypeEnvironment}
    {label : TypeLabel} {cL fL cR fR : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hRightSkip : rhoR = .skip rhoR.alphabet)
    (hLeftLive : rhoL ≠ .skip rhoL.alphabet)
    (hTargetLive : targetL ≠ .skip targetL.alphabet)
    (hStepL : DecoratedTypeTransition envL rhoL label ⟨cL, fL⟩ targetL)
    (hStepR : DecoratedTypeTransition envR rhoR TypeLabel.silent ⟨cR, fR⟩ rhoR)
    (hLocalL : LocalTypeOfferEnvironment outer interface rhoL envR cR fR envL)
    (hLocalR : LocalTypeOfferEnvironment outer interface rhoR envL cL fL envR)
    (hOuter : outer.WellFormed alphabet)
    (hSync : TypeLabel.Sync interface label TypeLabel.silent) :
    ∃ q',
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer label
        ⟨hideTypeOffers interface cL, hideTypeOffers interface fL⟩ (.survivor 0 q') ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
        (targetL.reannotate alphabet) (.survivor 0 q') := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hHidden : ∀ action ∈ alphabet.actions, action.1 ∉ interface :=
    fun _ hAction => parent_no_interface hCompat.2.1 hAction
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL qL hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR qR hRWF.1 hRelR
  have hEmptyR : cR = ∅ := (skip_step_offers hRightSkip hStepR.2).2.2.1
  have hFutureEmpty : fR = ∅ :=
    (skip_step_offers hRightSkip hStepR.2).2.2.2
  have hNotClock : label ≠ TypeLabel.tock := by
    intro hClock
    have h := hSync.2.2.mp (by rw [hClock]; trivial)
    simpa [TypeLabel.silent, TypeLabel.isTock] using h
  obtain ⟨qL', hEdgeL, hTargetL⟩ := hLeft.1 hRelL hStepL
  obtain ⟨qR', hEdgeR, hTargetR⟩ := hRight.1 hRelR hStepR
  let eL : AutomatonFragmentEdge := ⟨qL, envL, .visible label, cL, fL, qL'⟩
  let eR : AutomatonFragmentEdge := ⟨qR, envR, .visible TypeLabel.silent, cR, fR, qR'⟩
  have hEL := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeL
  have hER := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeR
  have hLE : LocalTypeOfferEnvironment outer interface rhoL eR.environment
      eR.current eR.future eL.environment := hLocalL
  have hRE : LocalTypeOfferEnvironment outer interface rhoR eL.environment
      eL.current eL.future eR.environment := hLocalR
  obtain ⟨hEnv, hEdgesSync⟩ := sync_of_local hOuter hHidden hLE hRE
    (offers_disjoint hLWF hRelL hStepL.2) (offers_disjoint hRWF hRelR hStepR.2)
    (fun hClock => edge_offers_empty_of_clock hLeft hRelL hEdgeL
      (localEnvironment_clock hLE hClock))
    (fun hClock => edge_offers_empty_of_clock hRight hRelR hEdgeR
      (localEnvironment_clock hRE hClock)) hSync
  rw [hAlphaL, hAlphaR] at hEdgesSync
  -- Both right states represent `skip`, and both left states are live.
  have hSourceFinal : eR.source ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
    (related_accepting_iff hRelR).mpr hRightSkip
  have hTargetFinal : eR.target ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
    (related_accepting_iff hTargetR).mpr hRightSkip
  have hSourceLive : eL.source ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting :=
    mt (related_accepting_iff hRelL).mp hLeftLive
  have hTargetNotFinal :
      eL.target ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting :=
    mt (related_accepting_iff hTargetL).mp hTargetLive
  let state : TypeAutomatonState := .survivor 0 qL'
  let combined := AutomatonConstructionLabel.combine interface eL.label eR.label
  let published := hideOffers interface (eL.current ∪ eR.current)
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, combineAutomatonEnvironment interface envL envR, combined,
      published, parallelFutureSpec combined (hideOffers interface (eL.future ∪ eR.future)), state⟩
  have hRaw : raw ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inr
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter]
    exact ⟨eL, hEL, eR, ⟨hER, hEdgesSync, hSourceFinal, hTargetFinal, hSourceLive,
      hTargetNotFinal⟩, rfl⟩
  have hLabelEq : raw.label = .visible label := by
    simp only [raw, combined, eL, eR, AutomatonConstructionLabel.combine,
      TypeLabel.combine_silent_right interface label hSync]
  have hCurrentEq : raw.current = hideTypeOffers interface cL := by
    simp only [raw, published, eL, eR, hEmptyR, Finset.union_empty, hideOffers,
      hideTypeOffers]
  refine ⟨qL', ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨raw, hRaw, rfl, hEnv, hLabelEq, hCurrentEq, ?_, rfl⟩
    change resolveFutureSpec (computeFutureOf (.par alphabet left right interface))
      (parallelFutureSpec combined (hideOffers interface (eL.future ∪ eR.future))) = _
    change combined = .visible label at hLabelEq
    simp [hLabelEq, parallelFutureSpec, resolveFutureSpec,
      AutomatonConstructionLabel.semantic, hNotClock, eL, eR, hFutureEmpty,
      hideOffers, hideTypeOffers]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hLWF
    exact survivorLeft_relationMembership alphabet left right interface
      (offerBranchesDisjoint_of_wellFormedIn hLWF)
      (relationMembership_reannotate hLWF hCompat.1
        (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
          (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1 hAction)) hTargetL)
      hTargetNotFinal

/-- Invert a right survivor-entry edge through its `SyncEdges_I` witness:
mirror of `offer_par_leftComplete_backward`. -/
theorem offer_par_rightComplete_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {eL eR : AutomatonFragmentEdge} {labelL labelR : TypeLabel}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL eL.source)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR eR.source)
    (hMemL : eL ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel left) left) (computeFutureOf left))
    (hMemR : eR ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel right) right) (computeFutureOf right))
    (hLabelL : eL.label = .visible labelL) (hLabelR : eR.label = .visible labelR)
    (hSync : syncAutomatonEdges left.alphabet right.alphabet interface eL eR)
    (hSourceFinal : eR.source ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hTargetFinal : eR.target ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hSourceLive : eL.source ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hTargetLive : eL.target ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting) :
    ∃ target,
      DecoratedTypeTransition
        (combineAutomatonEnvironment interface eL.environment eR.environment)
        (.par alphabet rhoL rhoR interface) (TypeLabel.combine interface labelL labelR)
        ⟨hideTypeOffers interface (eL.current ∪ eR.current),
          if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target
        (.survivor 0 eL.target) := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hAlphaL := relationMembership_alphabet_eq_of_wellFormed left rhoL _ hLWF.1 hRelL
  have hAlphaR := relationMembership_alphabet_eq_of_wellFormed right rhoR _ hRWF.1 hRelR
  obtain ⟨targetL, hStepL, hTargetL⟩ := hLeft.2 hRelL
    (resolved_hasEdge hMemL hLabelL)
  obtain ⟨targetR, hStepR, hTargetR⟩ := hRight.2 hRelR
    (resolved_hasEdge hMemR hLabelR)
  have hEnvWF : eL.environment.WellFormed left.alphabet := by
    rw [← hAlphaL]
    exact PactType.typeOffers_env_wellFormed hStepL.2
      (represented_alphabetWellFormed hLWF hRelL)
  have hOuter := combined_environment_wellFormed hCompat.2.1.parent_eq_left hEnvWF hSync
  obtain ⟨hLE, hRE, _, _, _, _, hLabelSync⟩ := hSync
  rw [← hAlphaL] at hLE
  rw [← hAlphaR] at hRE
  have hLocalL := (localEnvironment_iff _ _ rhoL eR eL).mp hLE
  have hLocalR := (localEnvironment_iff _ _ rhoR eL eR).mp hRE
  simp only [hLabelL, hLabelR, AutomatonConstructionLabel.semantic] at hLabelSync
  -- The finished component's edge is `skip`'s silent self-loop.
  have hRightSkip : rhoR = .skip rhoR.alphabet := (related_accepting_iff hRelR).mp hSourceFinal
  obtain ⟨hSilent, hLoop, hEmptyRaw, hFutureEmpty⟩ := skip_step_offers hRightSkip hStepR.2
  dsimp only at hFutureEmpty
  have hEmptyR : eR.current = ∅ := hEmptyRaw
  rw [hSilent] at hStepR hLabelSync
  rw [hLoop] at hStepR
  have hNotClock : labelL ≠ TypeLabel.tock := by
    intro hClock
    have h := hLabelSync.2.2.mp (by rw [hClock]; trivial)
    simpa [TypeLabel.silent, TypeLabel.isTock] using h
  have hLeftNotSkip := mt (related_accepting_iff hRelL).mpr hSourceLive
  have hTargetNotSkip := mt (related_accepting_iff hTargetL).mpr hTargetLive
  have hOffers := TypeOffers.right_complete
    (combineAutomatonEnvironment interface eL.environment eR.environment)
    eL.environment eR.environment interface alphabet rhoL targetL rhoR labelL
    eL.current eL.future eR.current eR.future hRightSkip hLeftNotSkip hStepR.2
    hStepL.2 hTargetNotSkip hLocalL hLocalR hOuter hLabelSync
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hLWF
  have hTargetRel := survivorLeft_relationMembership alphabet left right interface
    (offerBranchesDisjoint_of_wellFormedIn hLWF)
    (relationMembership_reannotate hLWF hCompat.1
      (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
        (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1 hAction)) hTargetL)
    hTargetLive
  -- `α₁ ∪_I ε = α₁`, and the finished component published nothing.
  rw [hSilent, TypeLabel.combine_silent_right interface labelL hLabelSync, hEmptyR,
    Finset.union_empty, if_neg hNotClock, hFutureEmpty,
    Finset.union_empty]
  exact ⟨targetL.reannotate alphabet, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩

/-- Forward direction at a product state, by the semantic parallel rule. -/
theorem offer_par_pair_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR target : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {qL qR : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hStep : DecoratedTypeTransition env (.par alphabet rhoL rhoR interface) label
      ⟨current, future⟩ target) :
    ∃ q', (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR)
        env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  cases decoratedTypeTransition_par_cases hStep with
  | step envL envR labelL labelR targetL targetR cL fL cR fR
      hTarget hNotDone hLiveL hLiveR hStepL hStepR hOuter hLocalL hLocalR hSync hLabel hCurrent hFuture =>
    obtain ⟨qL', qR', hTargetL, hTargetR, hEdge⟩ := offer_par_sync_forward
      hWF hLeft hRight hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (fun _ => ⟨hLiveL, hLiveR⟩)
    have hNotFinal : ¬ (qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting) := by
      simpa only [related_accepting_iff hTargetL, related_accepting_iff hTargetR] using hNotDone
    rw [if_neg hNotFinal] at hEdge
    rw [hTarget, hLabel, hCurrent, hFuture]
    exact ⟨.pair qL' qR', hEdge,
      relationMembership_par_product alphabet left right interface hTargetL hTargetR⟩
  | fuse envL envR labelL labelR cL fL cR fR hTarget hStepL hStepR hOuter
      hLocalL hLocalR hSync hNotClock hLabel hCurrent hFuture =>
    obtain ⟨qL', qR', hTargetL, hTargetR, hEdge⟩ := offer_par_sync_forward
      hWF hLeft hRight hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (by simp [PactType.alphabet])
    have hAccept : qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
      ⟨accepting_of_skip_residual left hTargetL, accepting_of_skip_residual right hTargetR⟩
    rw [if_pos hAccept] at hEdge
    rw [if_neg hNotClock] at hEdge
    rw [hTarget, hLabel, hCurrent, hFuture]
    exact ⟨.final, hEdge, relationMembership_par_final alphabet left right interface⟩
  | fuse_tock envL envR labelL labelR cL fL cR fR hTarget hStepL hStepR hOuter
      hLocalL hLocalR hSync hClock hLabel hCurrent hFuture =>
    obtain ⟨qL', qR', hTargetL, hTargetR, hEdge⟩ := offer_par_sync_forward
      hWF hLeft hRight hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (by simp [PactType.alphabet])
    have hAccept : qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting :=
      ⟨accepting_of_skip_residual left hTargetL, accepting_of_skip_residual right hTargetR⟩
    rw [if_pos hAccept] at hEdge
    obtain ⟨hLC, hRC⟩ := (TypeLabel.combine_eq_tock_iff _ _ _).mp hClock
    have hCL : cL = ∅ := hStepL.2.current_eq_empty_of_label_tock hLC
    have hCR : cR = ∅ := hStepR.2.current_eq_empty_of_label_tock hRC
    simp only [hCL, hCR, Finset.union_empty, hideTypeOffers, Finset.filter_empty,
      if_pos hClock] at hEdge
    rw [hTarget, hLabel, hCurrent, hFuture]
    exact ⟨.final, hEdge, relationMembership_par_final alphabet left right interface⟩
  | left_complete envL envR targetR cL fL cR fR hTarget hLeftSkip hRightLive
      hTargetLive hStepL hStepR hLocalL hLocalR hOuter hSync hCurrent hFuture =>
    obtain ⟨q', hEdge, hRelated⟩ := offer_par_leftComplete_forward
      hWF hLeft hRight hRelL hRelR hLeftSkip hRightLive
      hTargetLive hStepL hStepR hLocalL hLocalR hOuter hSync
    rw [hTarget, hCurrent, hFuture]
    exact ⟨.survivor 1 q', hEdge, hRelated⟩
  | right_complete envL envR targetL cL fL cR fR hTarget hRightSkip hLeftLive
      hTargetLive hStepR hStepL hLocalL hLocalR hOuter hSync hCurrent hFuture =>
    obtain ⟨q', hEdge, hRelated⟩ := offer_par_rightComplete_forward
      hWF hLeft hRight hRelL hRelR hRightSkip hLeftLive
      hTargetLive hStepL hStepR hLocalL hLocalR hOuter hSync
    rw [hTarget, hCurrent, hFuture]
    exact ⟨.survivor 0 q', hEdge, hRelated⟩

private theorem combine_visible_inv {interface : Interface}
    {left right : AutomatonConstructionLabel} {label : TypeLabel}
    (h : AutomatonConstructionLabel.combine interface left right = .visible label) :
    ∃ labelL labelR, left = .visible labelL ∧ right = .visible labelR ∧
      TypeLabel.combine interface labelL labelR = label := by
  cases left with
  | «variable» => simp [AutomatonConstructionLabel.combine] at h
  | visible labelL =>
    cases right with
    | «variable» => simp [AutomatonConstructionLabel.combine] at h
    | visible labelR =>
      exact ⟨labelL, labelR, rfl, rfl, by simpa [AutomatonConstructionLabel.combine] using h⟩

/-- Backward direction at a product state, by the three product edge families. -/
theorem offer_par_pair_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    {qL qR q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR)
      env label ⟨current, future⟩ q') :
    ∃ target, DecoratedTypeTransition env (.par alphabet rhoL rhoR interface)
        label ⟨current, future⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  change resolveFutureSpec (computeFutureOf (.par alphabet left right interface)) raw.future =
    future at hFuture
  rw [compileTypeFuel_par_eq_children] at hMem
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union] at hMem
  rcases hMem with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hRaw
    obtain ⟨eL, hEL, eR, ⟨hER, hSync, hGuard⟩, rfl⟩ := hRaw
    simp only at hSource hEnv hLabel hCurrent hTarget
    obtain ⟨labelL, labelR, hLL, hLR, hLabelEq⟩ := combine_visible_inv hLabel
    injection hSource with hQL hQR
    obtain ⟨target, hStep, hRelated⟩ := offer_par_sync_backward
      hWF hLeft hRight
      (by rw [hQL]; exact hRelL) (by rw [hQR]; exact hRelR)
      hEL hER hLL hLR hSync hGuard
    change hideTypeOffers interface (eL.current ∪ eR.current) = current at hCurrent
    have hFutureEq :
        (if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)) = future := by
      by_cases hClock : TypeLabel.combine interface labelL labelR = TypeLabel.tock <;>
        simpa [parallelFutureSpec, resolveFutureSpec, hLL, hLR,
          AutomatonConstructionLabel.combine, AutomatonConstructionLabel.semantic,
          hClock, hideOffers, hideTypeOffers] using hFuture
    rw [hFutureEq, hEnv, hLabelEq, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, hStep, hRelated⟩
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hLC
    obtain ⟨eL, hEL, eR, ⟨hER, hSync, hSourceFinal, hTargetFinal, hSourceLive,
      hTargetLive⟩, rfl⟩ := hLC
    simp only at hSource hEnv hLabel hCurrent hTarget
    obtain ⟨labelL, labelR, hLL, hLR, hLabelEq⟩ := combine_visible_inv hLabel
    injection hSource with hQL hQR
    obtain ⟨target, hStep, hRelated⟩ := offer_par_leftComplete_backward
      hWF hLeft hRight
      (by rw [hQL]; exact hRelL) (by rw [hQR]; exact hRelR)
      hEL hER hLL hLR hSync hSourceFinal hTargetFinal hSourceLive hTargetLive
    change hideTypeOffers interface (eL.current ∪ eR.current) = current at hCurrent
    have hFutureEq :
        (if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)) = future := by
      by_cases hClock : TypeLabel.combine interface labelL labelR = TypeLabel.tock <;>
        simpa [parallelFutureSpec, resolveFutureSpec, hLL, hLR,
          AutomatonConstructionLabel.combine, AutomatonConstructionLabel.semantic,
          hClock, hideOffers, hideTypeOffers] using hFuture
    rw [hFutureEq, hEnv, hLabelEq, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, hStep, hRelated⟩
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hRC
    obtain ⟨eL, hEL, eR, ⟨hER, hSync, hSourceFinal, hTargetFinal, hSourceLive,
      hTargetLive⟩, rfl⟩ := hRC
    simp only at hSource hEnv hLabel hCurrent hTarget
    obtain ⟨labelL, labelR, hLL, hLR, hLabelEq⟩ := combine_visible_inv hLabel
    injection hSource with hQL hQR
    obtain ⟨target, hStep, hRelated⟩ := offer_par_rightComplete_backward
      hWF hLeft hRight
      (by rw [hQL]; exact hRelL) (by rw [hQR]; exact hRelR)
      hEL hER hLL hLR hSync hSourceFinal hTargetFinal hSourceLive hTargetLive
    change hideTypeOffers interface (eL.current ∪ eR.current) = current at hCurrent
    have hFutureEq :
        (if TypeLabel.combine interface labelL labelR = TypeLabel.tock then ∅
          else hideTypeOffers interface (eL.future ∪ eR.future)) = future := by
      by_cases hClock : TypeLabel.combine interface labelL labelR = TypeLabel.tock <;>
        simpa [parallelFutureSpec, resolveFutureSpec, hLL, hLR,
          AutomatonConstructionLabel.combine, AutomatonConstructionLabel.semantic,
          hClock, hideOffers, hideTypeOffers] using hFuture
    rw [hFutureEq, hEnv, hLabelEq, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, hStep, hRelated⟩
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hLS
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hRS
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hLD
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hRD
    simp at hSource
  · obtain ⟨outer, _, rfl⟩ := Finset.mem_image.mp hDone
    simp at hSource

theorem offer_par_final_forward
    {alphabet : PactTypeAlphabet} {left right target : PactType} {interface : Interface}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hStep : DecoratedTypeTransition env (.skip alphabet) label ⟨current, future⟩ target) :
    ∃ q', (compileType (.par alphabet left right interface)).HasEdge .final
        env label ⟨current, future⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  cases hStep.2 with
  | skip _ _ hConditions =>
    refine ⟨.final, ?_, relationMembership_par_final alphabet left right interface⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨⟨.final, env, .visible TypeLabel.silent, ∅, .explicit ∅, .final⟩,
      ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inr
    exact Finset.mem_image.mpr ⟨env, Finset.mem_filter.mpr
      ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hConditions.1, hConditions.2⟩, rfl⟩

theorem offer_par_final_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge .final
      env label ⟨current, future⟩ q') :
    ∃ target, DecoratedTypeTransition env (.skip alphabet) label
        ⟨current, future⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  change resolveFutureSpec (computeFutureOf (.par alphabet left right interface)) raw.future =
    future at hFuture
  rw [compileTypeFuel_par_eq_children] at hMem
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union] at hMem
  rcases hMem with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hRaw
    obtain ⟨eL, _, eR, _, rfl⟩ := hRaw
    simp at hSource
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hLC
    obtain ⟨qL, _, edge, _, outer, _, rfl⟩ := hLC
    simp at hSource
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hRC
    obtain ⟨qR, _, edge, _, outer, _, rfl⟩ := hRC
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hLS
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hRS
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hLD
    simp at hSource
  · obtain ⟨edge, _, rfl⟩ := Finset.mem_image.mp hRD
    simp at hSource
  · obtain ⟨outer, hOuter, rfl⟩ := Finset.mem_image.mp hDone
    obtain ⟨hOuterMem, hClock⟩ := Finset.mem_filter.mp hOuter
    simp only [resolveFutureSpec] at hEnv hLabel hCurrent hFuture hTarget
    have hLabelEq : TypeLabel.silent = label := AutomatonConstructionLabel.visible.inj hLabel
    rw [← hEnv, ← hLabelEq, ← hCurrent, ← hFuture, ← hTarget]
    have hOffers := TypeOffers.skip outer alphabet
      ⟨PactTypeAlphabet.environment_wellFormed hOuterMem, hClock⟩
    exact ⟨.skip alphabet, ⟨hOffers.toTypeTransition, hOffers⟩,
      relationMembership_par_final alphabet left right interface⟩

/-- Parallel correspondence preserves the component offer witnesses through
product, survivor-entry, survivor-copy, and final-state clauses. -/
theorem offerCorrespondence_par
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left) (hRight : TypeAutomatonStepCorrespondence right)
    (hSurvivorLeft : TypeAutomatonStepCorrespondence (left.reannotate alphabet))
    (hSurvivorRight : TypeAutomatonStepCorrespondence (right.reannotate alphabet)) :
    TypeAutomatonStepCorrespondence (.par alphabet left right interface) := by
  constructor
  · -- Forward direction: invert the represented source, then the semantic step.
    intro rho target q env label offers hRelated hStep
    rcases offers with ⟨current, future⟩
    rcases relationMembership_par_cases alphabet left right interface hRelated with
      hPair | hSurvivorL | hSurvivorR | hDone
    · obtain ⟨qL, qR, rhoL, rhoR, hEntry, hRelL, hRelR⟩ := hPair
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_pair_forward hWF hLeft hRight hRelL hRelR hStep
    · obtain ⟨qL, residual, hEntry, hChild, _⟩ := hSurvivorL
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_survivorLeft_forward hWF hSurvivorLeft hChild hStep
    · obtain ⟨qR, residual, hEntry, hChild, _⟩ := hSurvivorR
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_survivorRight_forward hWF hSurvivorRight hChild hStep
    · injection hDone with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_final_forward hStep
  · -- Backward direction: the same source clauses determine the edge family.
    intro rho q q' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    rcases relationMembership_par_cases alphabet left right interface hRelated with
      hPair | hSurvivorL | hSurvivorR | hDone
    · obtain ⟨qL, qR, rhoL, rhoR, hEntry, hRelL, hRelR⟩ := hPair
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_pair_backward hWF hLeft hRight hRelL hRelR hEdge
    · obtain ⟨qL, residual, hEntry, hChild, _⟩ := hSurvivorL
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_survivorLeft_backward hWF hSurvivorLeft hChild hEdge
    · obtain ⟨qR, residual, hEntry, hChild, _⟩ := hSurvivorR
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_survivorRight_backward hWF hSurvivorRight hChild hEdge
    · injection hDone with hRho hQ
      subst hRho
      subst hQ
      exact offer_par_final_backward hEdge

/-- The current-offer stage is the projection of full parallel correspondence. -/
theorem currentOfferCorrespondence_par_of_typeWF
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : TypeAutomatonStepCorrespondence left)
    (hRight : TypeAutomatonStepCorrespondence right)
    (hSurvivorLeft : TypeAutomatonStepCorrespondence (left.reannotate alphabet))
    (hSurvivorRight : TypeAutomatonStepCorrespondence (right.reannotate alphabet)) :
    CurrentOfferCorrespondence (.par alphabet left right interface) :=
  (offerCorrespondence_par hWF hLeft hRight hSurvivorLeft hSurvivorRight).toCurrent

end
end Pact
