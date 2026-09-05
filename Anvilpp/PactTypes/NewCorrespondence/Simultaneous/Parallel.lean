import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.EdgeFuture

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

private theorem offers_disjoint {env : TypeEnvironment} {rho rho' : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (h : TypeOffers env rho label rho' current future) : Disjoint current future := by
  by_cases hClock : label = TypeLabel.tock
  · rw [h.future_eq_empty_of_label_tock hClock]; exact Finset.disjoint_empty_right _
  · rw [h.future_eq_sdiff_of_label_ne_tock hClock]
    exact Finset.sdiff_disjoint.symm

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
theorem currentOffer_par_sync_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR targetL targetR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hRight : CurrentOfferCorrespondence right)
    (hLeftMenu : FutureOffersAgree left) (hRightMenu : FutureOffersAgree right)
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
    ∃ qL' qR' future,
      relationMembership (buildRelationSet left (compileType left)) targetL qL' ∧
      relationMembership (buildRelationSet right (compileType right)) targetR qR' ∧
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer
        (TypeLabel.combine interface labelL labelR) ⟨hideTypeOffers interface (cL ∪ cR), future⟩
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
  obtain ⟨qL', hEdgeL, hTargetL⟩ := hLeft.forward_with_future hLeftMenu hRelL hStepL
  obtain ⟨qR', hEdgeR, hTargetR⟩ := hRight.forward_with_future hRightMenu hRelR hStepR
  let eL : AutomatonFragmentEdge := ⟨qL, envL, .visible labelL, cL, fL, qL'⟩
  let eR : AutomatonFragmentEdge := ⟨qR, envR, .visible labelR, cR, fR, qR'⟩
  have hEL := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeL
  have hER := (compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdgeR
  have hLE : LocalTypeOfferEnvironment outer interface rhoL eR.environment
      eR.current eR.future eL.environment := hLocalL
  have hRE : LocalTypeOfferEnvironment outer interface rhoR eL.environment
      eL.current eL.future eR.environment := hLocalR
  obtain ⟨hEnv, hEdgesSync⟩ := sync_of_local hOuter hHidden hLE hRE
    (offers_disjoint hStepL.2) (offers_disjoint hStepR.2)
    (fun hClock => edge_offers_empty_of_clock hLeftMenu hTargetL hEdgeL
      (localEnvironment_clock hLE hClock))
    (fun hClock => edge_offers_empty_of_clock hRightMenu hTargetR hEdgeR
      (localEnvironment_clock hRE hClock)) hSync
  rw [hAlphaL, hAlphaR] at hEdgesSync
  let target : TypeAutomatonState :=
    if qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting
      then .final else .pair qL' qR'
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, combineAutomatonEnvironment interface envL envR,
      .visible (TypeLabel.combine interface labelL labelR), hideOffers interface (cL ∪ cR),
      parallelFutureSpec (.visible (TypeLabel.combine interface labelL labelR)) target
        (hideOffers interface (cL ∪ cR)), target⟩
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
  refine ⟨qL', qR', (match raw.future with
    | .explicit future => future
    | .at state removed => computeFutureOf (.par alphabet left right interface) state \ removed),
    hTargetL, hTargetR, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge]
  exact ⟨raw, hRaw, rfl, hEnv, rfl, rfl, rfl, rfl⟩

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
theorem currentOffer_par_sync_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hRight : CurrentOfferCorrespondence right)
    (hLeftMenu : FutureOffersAgree left) (hRightMenu : FutureOffersAgree right)
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
    ∃ target future,
      DecoratedTypeTransition (combineAutomatonEnvironment interface eL.environment eR.environment)
        (.par alphabet rhoL rhoR interface) (TypeLabel.combine interface labelL labelR)
        ⟨hideTypeOffers interface (eL.current ∪ eR.current), future⟩ target ∧
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
  obtain ⟨targetL, hStepL, hTargetL⟩ := hLeft.backward_with_future hLeftMenu hRelL
    (resolved_hasEdge hMemL hLabelL)
  obtain ⟨targetR, hStepR, hTargetR⟩ := hRight.backward_with_future hRightMenu hRelR
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
      rw [hCurr]
      exact ⟨.skip alphabet, ∅, ⟨hOffers.toTypeTransition, hOffers⟩,
        relationMembership_par_final alphabet left right interface⟩
    · have hOffers := TypeOffers.par_fuse _ _ _ interface alphabet rhoL rhoR
        labelL labelR _ _ _ _ hStepL.2 hStepR.2 hLocalL hLocalR ⟨hOuter, hLabelSync⟩ hClock
      exact ⟨.skip alphabet, _, ⟨hOffers.toTypeTransition, hOffers⟩,
        relationMembership_par_final alphabet left right interface⟩
  · have hLive := hGuard hDone
    have hNotDone : ¬ (targetL = .skip targetL.alphabet ∧ targetR = .skip targetR.alphabet) := by
      simpa only [← related_accepting_iff hTargetL, ← related_accepting_iff hTargetR] using hDone
    have hOffers := TypeOffers.par _ _ _ interface alphabet rhoL targetL rhoR targetR
      labelL labelR _ _ _ _ (mt (related_accepting_iff hRelL).mpr hLive.1)
      (mt (related_accepting_iff hRelR).mpr hLive.2) hStepL.2 hStepR.2 hNotDone
      hLocalL hLocalR ⟨hOuter, hLabelSync⟩
    rw [if_neg hDone]
    exact ⟨.par alphabet targetL targetR interface, _, ⟨hOffers.toTypeTransition, hOffers⟩,
      relationMembership_par_product alphabet left right interface hTargetL hTargetR⟩

private theorem projectEnvironment_eq {parent child : PactTypeAlphabet}
    {env : TypeEnvironment} (hWF : env.WellFormed parent)
    (hSubset : parent.actions ⊆ child.actions) :
    projectAutomatonEnvironment child env = env := by
  have hI : projectTypeEnvironmentOffers child env.immediate = env.immediate := by
    apply Finset.filter_eq_self.mpr
    intro action hAction
    obtain ⟨base, hBase, rfl⟩ := Finset.mem_image.mp (hWF.2.2.1 hAction)
    exact Finset.mem_image_of_mem _ (hSubset hBase)
  have hF : projectTypeEnvironmentOffers child env.future = env.future := by
    apply Finset.filter_eq_self.mpr
    intro action hAction
    obtain ⟨base, hBase, rfl⟩ := Finset.mem_image.mp (hWF.2.2.2 hAction)
    exact Finset.mem_image_of_mem _ (hSubset hBase)
  cases hClock : env.clock with
  | true =>
    obtain ⟨hImm, hFut⟩ := hWF.1 hClock
    cases env
    simp_all [projectAutomatonEnvironment, TypeEnvironment.tock]
  | false =>
    cases env
    simp_all [projectAutomatonEnvironment]

private theorem completionEnvironment_eq {alphabet : PactTypeAlphabet}
    {outer localEnv : TypeEnvironment} {interface : Interface} {ty : PactType}
    (hWF : outer.WellFormed alphabet)
    (hLocal : LocalTypeOfferEnvironment outer interface ty localEnv ∅ ∅ localEnv) :
    localEnv = outer := by
  cases hLocal with
  | clock _ _ _ _ hClock =>
    obtain ⟨hI, hF⟩ := hWF.1 hClock
    cases outer
    simp_all [TypeEnvironment.tock]
  | ordinary _ _ _ _ _ _ hClock _ hLC hI hF =>
    simp only [restrictTypeOffers, Finset.filter_empty, Finset.union_empty] at hI hF
    rw [hI, Finset.sdiff_eq_self_of_disjoint
      (Finset.disjoint_iff_inter_eq_empty.mpr (hWF.2.1 hClock)).symm] at hF
    cases outer
    cases localEnv
    simp_all

private theorem hide_eq_of_restrict_empty {interface : Interface}
    {offers : Finset BareMessage} (h : restrictTypeOffers interface offers = ∅) :
    hideTypeOffers interface offers = offers := by
  apply Finset.filter_eq_self.mpr
  intro action hAction hInterface
  have hIn : action ∈ restrictTypeOffers interface offers :=
    Finset.mem_filter.mpr ⟨hAction, hInterface⟩
  rw [h] at hIn
  exact Finset.notMem_empty action hIn

private theorem completionEnvironment_self {alphabet : PactTypeAlphabet}
    {outer : TypeEnvironment} (hWF : outer.WellFormed alphabet)
    (interface : Interface) (ty : PactType) :
    LocalTypeOfferEnvironment outer interface ty outer ∅ ∅ outer := by
  cases hClock : outer.clock with
  | true =>
    have hEq := PactTypeAlphabet.eq_tock_of_mem_localEnvironments_of_clock
      (PactTypeAlphabet.mem_localEnvironments_of_wellFormed hWF) hClock
    rw [hEq]
    exact .clock _ _ _ _ _ rfl
  | false =>
    refine .ordinary _ _ _ _ _ _ _ hClock hClock hClock ?_ ?_
    · simp [restrictTypeOffers]
    · simp only [restrictTypeOffers, Finset.filter_empty, Finset.union_empty]
      exact (Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_iff_inter_eq_empty.mpr (hWF.2.1 hClock)).symm).symm

theorem currentOffer_par_leftComplete_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hRight : CurrentOfferCorrespondence right) (hRightMenu : FutureOffersAgree right)
    {qL : TypeAutomatonState} {edge : AutomatonFragmentEdge}
    {outer : TypeEnvironment} {label : TypeLabel}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR edge.source)
    (hLeftFinal : qL ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hMem : edge ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel right) right) (computeFutureOf right))
    (hLabel : edge.label = .visible label)
    (hRightLive : edge.source ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hTargetLive : edge.target ∉ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hCurrentHidden : restrictTypeOffers interface edge.current = ∅)
    (hFutureHidden : restrictTypeOffers interface edge.future = ∅)
    (hOuter : outer.WellFormed alphabet)
    (hProjection : projectAutomatonEnvironment right.alphabet outer = edge.environment) :
    ∃ target future,
      DecoratedTypeTransition outer (.par alphabet rhoL rhoR interface) label
        ⟨edge.current, future⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target (.survivor 1 edge.target) := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  obtain ⟨target, hStep, hTarget⟩ := hRight.backward_with_future hRightMenu hRelR
    (resolved_hasEdge hMem hLabel)
  have hLocal : LocalTypeOfferEnvironment outer interface rhoR edge.environment ∅ ∅
      edge.environment := by
    rw [← hProjection, projectEnvironment_eq hOuter
      (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1)]
    exact completionEnvironment_self hOuter interface rhoR
  have hLeftSkip := (related_accepting_iff hRelL).mp hLeftFinal
  have hRightNotSkip := mt (related_accepting_iff hRelR).mpr hRightLive
  have hTargetNotSkip := mt (related_accepting_iff hTarget).mpr hTargetLive
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRWF
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hRWF
  have hTargetRel := survivorRight_relationMembership alphabet left right interface hDisjoint
    (relationMembership_reannotate hRWF hCompat.1
      (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
        (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1 hAction)) hTarget) hTargetLive
  by_cases hClock : label = TypeLabel.tock
  · have hOffers := TypeOffers.left_complete_tock outer edge.environment interface alphabet
      rhoL rhoR target label edge.current edge.future hLeftSkip hRightNotSkip hStep.2
      hTargetNotSkip hCurrentHidden hFutureHidden hLocal hOuter hClock
    have hEmpty : edge.current = ∅ := hStep.2.current_eq_empty_of_label_tock hClock
    rw [hEmpty]
    exact ⟨target.reannotate alphabet, ∅, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩
  · have hOffers := TypeOffers.left_complete outer edge.environment interface alphabet
      rhoL rhoR target label edge.current edge.future hLeftSkip hRightNotSkip hStep.2
      hTargetNotSkip hCurrentHidden hFutureHidden hLocal hOuter hClock
    rw [hide_eq_of_restrict_empty hCurrentHidden] at hOffers
    exact ⟨target.reannotate alphabet, _, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩

/-- Entry into the right survivor uses an edge of the written right child.
Only its residual is re-signed; exact survivor transport supplies membership. -/
theorem currentOffer_par_leftComplete_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR target : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hRight : CurrentOfferCorrespondence right) (hRightMenu : FutureOffersAgree right)
    {qL qR : TypeAutomatonState} {outer envR : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hLeftSkip : rhoL = .skip rhoL.alphabet)
    (hRightLive : rhoR ≠ .skip rhoR.alphabet)
    (hTargetLive : target ≠ .skip target.alphabet)
    (hStep : DecoratedTypeTransition envR rhoR label ⟨current, future⟩ target)
    (hCurrentHidden : restrictTypeOffers interface current = ∅)
    (hFutureHidden : restrictTypeOffers interface future = ∅)
    (hLocal : LocalTypeOfferEnvironment outer interface rhoR envR ∅ ∅ envR)
    (hOuter : outer.WellFormed alphabet) :
    ∃ q' future',
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer label
        ⟨hideTypeOffers interface current, future'⟩ (.survivor 1 q') ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
        (target.reannotate alphabet) (.survivor 1 q') := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRWF
  have hFinal := (related_accepting_iff hRelL).mpr hLeftSkip
  have hState := relationMembership_state_mem left rhoL qL
    (offerBranchesDisjoint_of_wellFormedIn hLWF) hRelL
  obtain ⟨q', hEdge, hTarget⟩ := hRight.forward_with_future hRightMenu hRelR hStep
  have hRLive := mt (related_accepting_iff hRelR).mp hRightLive
  have hLive := mt (related_accepting_iff hTarget).mp hTargetLive
  have hProjection : projectAutomatonEnvironment right.alphabet outer = envR := by
    rw [projectEnvironment_eq hOuter (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1),
      completionEnvironment_eq hOuter hLocal]
  let edge : AutomatonFragmentEdge := ⟨qR, envR, .visible label, current, future, q'⟩
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, outer, .visible label, current,
      parallelFutureSpec (.visible label) (.survivor 1 q') current, .survivor 1 q'⟩
  have hRaw : raw ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inr
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter]
    exact ⟨qL, ⟨hFinal, hState⟩, edge,
      ⟨(compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdge,
        hRLive, hLive, hCurrentHidden, hFutureHidden⟩,
      outer, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hOuter, hProjection⟩, rfl⟩
  refine ⟨q', (match raw.future with
    | .explicit future => future
    | .at state removed => computeFutureOf (.par alphabet left right interface) state \ removed),
    ?_, ?_⟩
  · rw [hide_eq_of_restrict_empty hCurrentHidden, compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨raw, hRaw, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hRWF
    exact survivorRight_relationMembership alphabet left right interface hDisjoint
      (relationMembership_reannotate hRWF hCompat.1
        (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
          (PactTypeAlphabet.parent_actions_subset_right hCompat.2.1 hAction)) hTarget) hLive

/-- A re-signed left-child step stays in its survivor copy, or enters the
parallel final state when the child completes. -/
theorem currentOffer_par_survivorLeft_forward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : CurrentOfferCorrespondence (left.reannotate alphabet))
    {rho rho' : PactType} {q : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (left.reannotate alphabet)
      (compileType (left.reannotate alphabet))) rho q)
    (hStep : DecoratedTypeTransition env rho label ⟨current, future⟩ rho') :
    ∃ q' future',
      (compileType (.par alphabet left right interface)).HasEdge (.survivor 0 q)
        env label ⟨current, future'⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hLeftWF := (typeWellFormedIn_par hWF).1
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).1
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLeftWF
  obtain ⟨q', future', hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
  let edge : AutomatonFragmentEdge :=
    ⟨q, env, .visible label, current, future', q'⟩
  have hEdgeMem := (compileType_hasEdge_iff_resolvedEdge_mem
    (left.reannotate alphabet) q q' env label ⟨current, future'⟩).mp hEdge
  let lifted := survivorLeftEdge
    (compileTypeFuel (typeCompilationFuel (left.reannotate alphabet))
      (left.reannotate alphabet)) edge
  have hLifted : lifted ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    exact ((buildParallelAutomaton_outgoing_survivorLeft
      _ _ _ _ _ _ _ _ _ _ _ _ q lifted).mpr ⟨edge, hEdgeMem, rfl, rfl⟩).1
  refine ⟨lifted.target, (match lifted.future with
    | .explicit future => future
    | .at target removed => computeFutureOf (.par alphabet left right interface)
        target \ removed), ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨lifted, hLifted, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;>
      simp only [lifted, survivorLeftEdge, edge] <;> split <;> rfl
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

theorem currentOffer_par_survivorLeft_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : CurrentOfferCorrespondence (left.reannotate alphabet))
    {rho : PactType} {q q' : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (left.reannotate alphabet)
      (compileType (left.reannotate alphabet))) rho q)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.survivor 0 q)
      env label ⟨current, future⟩ q') :
    ∃ rho' future', DecoratedTypeTransition env rho label ⟨current, future'⟩ rho' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hLeftWF := (typeWellFormedIn_par hWF).1
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).1
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLeftWF
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrentEq, -, hTargetEq⟩ :=
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
  obtain ⟨rho', future', hStep, hTarget⟩ := hCurrent.2 hRelated hChild
  refine ⟨rho', future', hStep, ?_⟩
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
theorem currentOffer_par_survivorRight_forward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : CurrentOfferCorrespondence (right.reannotate alphabet))
    {rho rho' : PactType} {q : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (right.reannotate alphabet)
      (compileType (right.reannotate alphabet))) rho q)
    (hStep : DecoratedTypeTransition env rho label ⟨current, future⟩ rho') :
    ∃ q' future',
      (compileType (.par alphabet left right interface)).HasEdge (.survivor 1 q)
        env label ⟨current, future'⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hRightWF := (typeWellFormedIn_par hWF).2
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).2
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRightWF
  obtain ⟨q', future', hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
  let edge : AutomatonFragmentEdge :=
    ⟨q, env, .visible label, current, future', q'⟩
  have hEdgeMem := (compileType_hasEdge_iff_resolvedEdge_mem
    (right.reannotate alphabet) q q' env label ⟨current, future'⟩).mp hEdge
  let lifted := survivorRightEdge
    (compileTypeFuel (typeCompilationFuel (right.reannotate alphabet))
      (right.reannotate alphabet)) edge
  have hLifted : lifted ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    exact ((buildParallelAutomaton_outgoing_survivorRight
      _ _ _ _ _ _ _ _ _ _ _ _ q lifted).mpr ⟨edge, hEdgeMem, rfl, rfl⟩).1
  refine ⟨lifted.target, (match lifted.future with
    | .explicit future => future
    | .at target removed => computeFutureOf (.par alphabet left right interface)
        target \ removed), ?_, ?_⟩
  · rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨lifted, hLifted, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;>
      simp only [lifted, survivorRightEdge, edge] <;> split <;> rfl
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

theorem currentOffer_par_survivorRight_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hCurrent : CurrentOfferCorrespondence (right.reannotate alphabet))
    {rho : PactType} {q q' : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelated : relationMembership (buildRelationSet (right.reannotate alphabet)
      (compileType (right.reannotate alphabet))) rho q)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.survivor 1 q)
      env label ⟨current, future⟩ q') :
    ∃ rho' future', DecoratedTypeTransition env rho label ⟨current, future'⟩ rho' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) rho' q' := by
  have hRightWF := (typeWellFormedIn_par hWF).2
  have hSurvivorWF := (typeWellFormedIn_survivor hWF).2
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hRightWF
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrentEq, -, hTargetEq⟩ :=
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
  obtain ⟨rho', future', hStep, hTarget⟩ := hCurrent.2 hRelated hChild
  refine ⟨rho', future', hStep, ?_⟩
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


/-- Entry into the left survivor uses an edge of the written left child.
Only its residual is re-signed; exact survivor transport supplies membership. -/
theorem currentOffer_par_rightComplete_forward
    {alphabet : PactTypeAlphabet} {right left rhoR rhoL target : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hLeftMenu : FutureOffersAgree left)
    {qR qL : TypeAutomatonState} {outer envL : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRightSkip : rhoR = .skip rhoR.alphabet)
    (hLeftLive : rhoL ≠ .skip rhoL.alphabet)
    (hTargetLive : target ≠ .skip target.alphabet)
    (hStep : DecoratedTypeTransition envL rhoL label ⟨current, future⟩ target)
    (hCurrentHidden : restrictTypeOffers interface current = ∅)
    (hFutureHidden : restrictTypeOffers interface future = ∅)
    (hLocal : LocalTypeOfferEnvironment outer interface rhoL envL ∅ ∅ envL)
    (hOuter : outer.WellFormed alphabet) :
    ∃ q' future',
      (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR) outer label
        ⟨hideTypeOffers interface current, future'⟩ (.survivor 0 q') ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
        (target.reannotate alphabet) (.survivor 0 q') := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLWF
  have hFinal := (related_accepting_iff hRelR).mpr hRightSkip
  have hState := relationMembership_state_mem right rhoR qR
    (offerBranchesDisjoint_of_wellFormedIn hRWF) hRelR
  obtain ⟨q', hEdge, hTarget⟩ := hLeft.forward_with_future hLeftMenu hRelL hStep
  have hLLive := mt (related_accepting_iff hRelL).mp hLeftLive
  have hLive := mt (related_accepting_iff hTarget).mp hTargetLive
  have hProjection : projectAutomatonEnvironment left.alphabet outer = envL := by
    rw [projectEnvironment_eq hOuter (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1),
      completionEnvironment_eq hOuter hLocal]
  let edge : AutomatonFragmentEdge := ⟨qL, envL, .visible label, current, future, q'⟩
  let raw : PendingAutomatonEdge :=
    ⟨.pair qL qR, outer, .visible label, current,
      parallelFutureSpec (.visible label) (.survivor 0 q') current, .survivor 0 q'⟩
  have hRaw : raw ∈ (compileTypeFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)).edges := by
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inl ∘ Or.inr
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter]
    exact ⟨qR, ⟨hFinal, hState⟩, edge,
      ⟨(compileType_hasEdge_iff_resolvedEdge_mem _ _ _ _ _ _).mp hEdge,
        hLLive, hLive, hCurrentHidden, hFutureHidden⟩,
      outer, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hOuter, hProjection⟩, rfl⟩
  refine ⟨q', (match raw.future with
    | .explicit future => future
    | .at state removed => computeFutureOf (.par alphabet left right interface) state \ removed),
    ?_, ?_⟩
  · rw [hide_eq_of_restrict_empty hCurrentHidden, compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨raw, hRaw, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hLWF
    exact survivorLeft_relationMembership alphabet left right interface hDisjoint
      (relationMembership_reannotate hLWF hCompat.1
        (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
          (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1 hAction)) hTarget) hLive


theorem currentOffer_par_rightComplete_backward
    {alphabet : PactTypeAlphabet} {right left rhoR rhoL : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hLeftMenu : FutureOffersAgree left)
    {qR : TypeAutomatonState} {edge : AutomatonFragmentEdge}
    {outer : TypeEnvironment} {label : TypeLabel}
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL edge.source)
    (hRightFinal : qR ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting)
    (hMem : edge ∈ resolveAutomatonEdgesWith
      (compileTypeFuel (typeCompilationFuel left) left) (computeFutureOf left))
    (hLabel : edge.label = .visible label)
    (hLeftLive : edge.source ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hTargetLive : edge.target ∉ (compileTypeFuel (typeCompilationFuel left) left).accepting)
    (hCurrentHidden : restrictTypeOffers interface edge.current = ∅)
    (hFutureHidden : restrictTypeOffers interface edge.future = ∅)
    (hOuter : outer.WellFormed alphabet)
    (hProjection : projectAutomatonEnvironment left.alphabet outer = edge.environment) :
    ∃ target future,
      DecoratedTypeTransition outer (.par alphabet rhoL rhoR interface) label
        ⟨edge.current, future⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target (.survivor 0 edge.target) := by
  obtain ⟨hLWF, hRWF⟩ := typeWellFormedIn_par hWF
  have hCompat := hWF.1
  simp only [PactType.AlphabetWellFormed] at hCompat
  obtain ⟨target, hStep, hTarget⟩ := hLeft.backward_with_future hLeftMenu hRelL
    (resolved_hasEdge hMem hLabel)
  have hLocal : LocalTypeOfferEnvironment outer interface rhoL edge.environment ∅ ∅
      edge.environment := by
    rw [← hProjection, projectEnvironment_eq hOuter
      (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1)]
    exact completionEnvironment_self hOuter interface rhoL
  have hRightSkip := (related_accepting_iff hRelR).mp hRightFinal
  have hLeftNotSkip := mt (related_accepting_iff hRelL).mpr hLeftLive
  have hTargetNotSkip := mt (related_accepting_iff hTarget).mpr hTargetLive
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hLWF
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hIAS, _⟩ := id hLWF
  have hTargetRel := survivorLeft_relationMembership alphabet left right interface hDisjoint
    (relationMembership_reannotate hLWF hCompat.1
      (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS action
        (PactTypeAlphabet.parent_actions_subset_left hCompat.2.1 hAction)) hTarget) hTargetLive
  by_cases hClock : label = TypeLabel.tock
  · have hOffers := TypeOffers.right_complete_tock outer edge.environment interface alphabet
      rhoL target rhoR label edge.current edge.future hRightSkip hLeftNotSkip hStep.2
      hTargetNotSkip hCurrentHidden hFutureHidden hLocal hOuter hClock
    have hEmpty : edge.current = ∅ := hStep.2.current_eq_empty_of_label_tock hClock
    rw [hEmpty]
    exact ⟨target.reannotate alphabet, ∅, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩
  · have hOffers := TypeOffers.right_complete outer edge.environment interface alphabet
      rhoL target rhoR label edge.current edge.future hRightSkip hLeftNotSkip hStep.2
      hTargetNotSkip hCurrentHidden hFutureHidden hLocal hOuter hClock
    rw [hide_eq_of_restrict_empty hCurrentHidden] at hOffers
    exact ⟨target.reannotate alphabet, _, ⟨hOffers.toTypeTransition, hOffers⟩, hTargetRel⟩


private theorem source_live_of_target_live {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hStep : DecoratedTypeTransition env source label ⟨current, future⟩ target)
    (hTarget : target ≠ .skip target.alphabet) : source ≠ .skip source.alphabet := by
  intro hSource
  rw [hSource] at hStep
  cases hStep.1
  exact hTarget rfl

/-- Forward direction at a product state, by the semantic parallel rule. -/
theorem currentOffer_par_pair_forward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR target : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hRight : CurrentOfferCorrespondence right)
    (hLeftMenu : FutureOffersAgree left) (hRightMenu : FutureOffersAgree right)
    {qL qR : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hStep : DecoratedTypeTransition env (.par alphabet rhoL rhoR interface) label
      ⟨current, future⟩ target) :
    ∃ q' future', (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR)
        env label ⟨current, future'⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  cases decoratedTypeTransition_par_cases hStep with
  | step envL envR labelL labelR targetL targetR cL fL cR fR
      hTarget hNotDone hLiveL hLiveR hStepL hStepR hOuter hLocalL hLocalR hSync hLabel hCurrent _ =>
    obtain ⟨qL', qR', future', hTargetL, hTargetR, hEdge⟩ := currentOffer_par_sync_forward
      hWF hLeft hRight hLeftMenu hRightMenu hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (fun _ => ⟨hLiveL, hLiveR⟩)
    have hNotFinal : ¬ (qL' ∈ (compileTypeFuel (typeCompilationFuel left) left).accepting ∧
        qR' ∈ (compileTypeFuel (typeCompilationFuel right) right).accepting) := by
      simpa only [related_accepting_iff hTargetL, related_accepting_iff hTargetR] using hNotDone
    rw [if_neg hNotFinal] at hEdge
    rw [hTarget, hLabel, hCurrent]
    exact ⟨.pair qL' qR', future', hEdge,
      relationMembership_par_product alphabet left right interface hTargetL hTargetR⟩
  | fuse envL envR labelL labelR cL fL cR fR hTarget hStepL hStepR hOuter
      hLocalL hLocalR hSync hNotClock hLabel hCurrent _ =>
    obtain ⟨qL', qR', future', hTargetL, hTargetR, hEdge⟩ := currentOffer_par_sync_forward
      hWF hLeft hRight hLeftMenu hRightMenu hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (by simp [PactType.alphabet])
    rw [if_pos ⟨accepting_of_skip_residual left hTargetL,
      accepting_of_skip_residual right hTargetR⟩] at hEdge
    rw [hTarget, hLabel, hCurrent]
    exact ⟨.final, future', hEdge, relationMembership_par_final alphabet left right interface⟩
  | fuse_tock envL envR labelL labelR cL fL cR fR hTarget hStepL hStepR hOuter
      hLocalL hLocalR hSync hClock hLabel hCurrent _ =>
    obtain ⟨qL', qR', future', hTargetL, hTargetR, hEdge⟩ := currentOffer_par_sync_forward
      hWF hLeft hRight hLeftMenu hRightMenu hRelL hRelR hStepL hStepR hLocalL hLocalR
      hOuter hSync (by simp [PactType.alphabet])
    rw [if_pos ⟨accepting_of_skip_residual left hTargetL,
      accepting_of_skip_residual right hTargetR⟩] at hEdge
    obtain ⟨hLC, hRC⟩ := (TypeLabel.combine_eq_tock_iff _ _ _).mp hClock
    have hCL : cL = ∅ := hStepL.2.current_eq_empty_of_label_tock hLC
    have hCR : cR = ∅ := hStepR.2.current_eq_empty_of_label_tock hRC
    simp only [hCL, hCR, Finset.union_empty, hideTypeOffers, Finset.filter_empty] at hEdge
    rw [hTarget, hLabel, hCurrent]
    exact ⟨.final, future', hEdge, relationMembership_par_final alphabet left right interface⟩
  | left_complete envR targetR cR fR hTarget hLeftSkip hTargetLive hRightStep
      hCurrentHidden hFutureHidden hLocal hOuter hNotClock hCurrent _ =>
    obtain ⟨q', future', hEdge, hRelated⟩ := currentOffer_par_leftComplete_forward
      hWF hRight hRightMenu hRelL hRelR hLeftSkip
      (source_live_of_target_live hRightStep hTargetLive) hTargetLive hRightStep
      hCurrentHidden hFutureHidden hLocal hOuter
    rw [hTarget, hCurrent]
    exact ⟨.survivor 1 q', future', hEdge, hRelated⟩
  | left_complete_tock envR targetR cR fR hTarget hLeftSkip hTargetLive hRightStep
      hCurrentHidden hFutureHidden hLocal hOuter hClock hCurrent _ =>
    obtain ⟨q', future', hEdge, hRelated⟩ := currentOffer_par_leftComplete_forward
      hWF hRight hRightMenu hRelL hRelR hLeftSkip
      (source_live_of_target_live hRightStep hTargetLive) hTargetLive hRightStep
      hCurrentHidden hFutureHidden hLocal hOuter
    have hEmpty : cR = ∅ := hRightStep.2.current_eq_empty_of_label_tock hClock
    simp only [hEmpty, hideTypeOffers, Finset.filter_empty] at hEdge
    rw [hTarget, hCurrent]
    exact ⟨.survivor 1 q', future', hEdge, hRelated⟩
  | right_complete envL targetL cL fL hTarget hRightSkip hTargetLive hLeftStep
      hCurrentHidden hFutureHidden hLocal hOuter hNotClock hCurrent _ =>
    obtain ⟨q', future', hEdge, hRelated⟩ := currentOffer_par_rightComplete_forward
      hWF hLeft hLeftMenu hRelR hRelL hRightSkip
      (source_live_of_target_live hLeftStep hTargetLive) hTargetLive hLeftStep
      hCurrentHidden hFutureHidden hLocal hOuter
    rw [hTarget, hCurrent]
    exact ⟨.survivor 0 q', future', hEdge, hRelated⟩
  | right_complete_tock envL targetL cL fL hTarget hRightSkip hTargetLive hLeftStep
      hCurrentHidden hFutureHidden hLocal hOuter hClock hCurrent _ =>
    obtain ⟨q', future', hEdge, hRelated⟩ := currentOffer_par_rightComplete_forward
      hWF hLeft hLeftMenu hRelR hRelL hRightSkip
      (source_live_of_target_live hLeftStep hTargetLive) hTargetLive hLeftStep
      hCurrentHidden hFutureHidden hLocal hOuter
    have hEmpty : cL = ∅ := hLeftStep.2.current_eq_empty_of_label_tock hClock
    simp only [hEmpty, hideTypeOffers, Finset.filter_empty] at hEdge
    rw [hTarget, hCurrent]
    exact ⟨.survivor 0 q', future', hEdge, hRelated⟩

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
theorem currentOffer_par_pair_backward
    {alphabet : PactTypeAlphabet} {left right rhoL rhoR : PactType}
    {interface : Interface} {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hRight : CurrentOfferCorrespondence right)
    (hLeftMenu : FutureOffersAgree left) (hRightMenu : FutureOffersAgree right)
    {qL qR q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hRelL : relationMembership (buildRelationSet left (compileType left)) rhoL qL)
    (hRelR : relationMembership (buildRelationSet right (compileType right)) rhoR qR)
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge (.pair qL qR)
      env label ⟨current, future⟩ q') :
    ∃ target future', DecoratedTypeTransition env (.par alphabet rhoL rhoR interface)
        label ⟨current, future'⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrent, _, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  rw [compileTypeFuel_par_eq_children] at hMem
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union] at hMem
  rcases hMem with ((((((hRaw | hLC) | hRC) | hLS) | hRS) | hLD) | hRD) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter] at hRaw
    obtain ⟨eL, hEL, eR, ⟨hER, hSync, hGuard⟩, rfl⟩ := hRaw
    simp only at hSource hEnv hLabel hCurrent hTarget
    obtain ⟨labelL, labelR, hLL, hLR, hLabelEq⟩ := combine_visible_inv hLabel
    injection hSource with hQL hQR
    obtain ⟨target, future', hStep, hRelated⟩ := currentOffer_par_sync_backward
      hWF hLeft hRight hLeftMenu hRightMenu
      (by rw [hQL]; exact hRelL) (by rw [hQR]; exact hRelR)
      hEL hER hLL hLR hSync hGuard
    change hideTypeOffers interface (eL.current ∪ eR.current) = current at hCurrent
    rw [hEnv, hLabelEq, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, future', hStep, hRelated⟩
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter] at hLC
    obtain ⟨qLF, ⟨hFinal, _⟩, edge, ⟨hEdgeMem, hLive, hTargetLive, hCH, hFH⟩,
      outer, ⟨hOuter, hProjection⟩, rfl⟩ := hLC
    simp only at hSource hEnv hLabel hCurrent hTarget
    injection hSource with hQL hQR
    obtain ⟨target, future', hStep, hRelated⟩ := currentOffer_par_leftComplete_backward
      hWF hRight hRightMenu (by rw [hQL]; exact hRelL) (by rw [hQR]; exact hRelR)
      hFinal hEdgeMem hLabel hLive hTargetLive hCH hFH
      (PactTypeAlphabet.environment_wellFormed hOuter) hProjection
    rw [hEnv, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, future', hStep, hRelated⟩
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter] at hRC
    obtain ⟨qRF, ⟨hFinal, _⟩, edge, ⟨hEdgeMem, hLive, hTargetLive, hCH, hFH⟩,
      outer, ⟨hOuter, hProjection⟩, rfl⟩ := hRC
    simp only at hSource hEnv hLabel hCurrent hTarget
    injection hSource with hQL hQR
    obtain ⟨target, future', hStep, hRelated⟩ := currentOffer_par_rightComplete_backward
      hWF hLeft hLeftMenu (by rw [hQR]; exact hRelR) (by rw [hQL]; exact hRelL)
      hFinal hEdgeMem hLabel hLive hTargetLive hCH hFH
      (PactTypeAlphabet.environment_wellFormed hOuter) hProjection
    rw [hEnv, hCurrent] at hStep
    rw [hTarget] at hRelated
    exact ⟨target, future', hStep, hRelated⟩
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

theorem currentOffer_par_final_forward
    {alphabet : PactTypeAlphabet} {left right target : PactType} {interface : Interface}
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    (hStep : DecoratedTypeTransition env (.skip alphabet) label ⟨current, future⟩ target) :
    ∃ q' future', (compileType (.par alphabet left right interface)).HasEdge .final
        env label ⟨current, future'⟩ q' ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  cases hStep.2 with
  | skip _ _ hConditions =>
    refine ⟨.final, ∅, ?_, relationMembership_par_final alphabet left right interface⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    refine ⟨⟨.final, env, .visible TypeLabel.silent, ∅, .explicit ∅, .final⟩,
      ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [compileTypeFuel_par_eq_children]
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    apply Or.inr
    exact Finset.mem_image.mpr ⟨env, Finset.mem_filter.mpr
      ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hConditions.1, hConditions.2⟩, rfl⟩

theorem currentOffer_par_final_backward
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge .final
      env label ⟨current, future⟩ q') :
    ∃ target future', DecoratedTypeTransition env (.skip alphabet) label
        ⟨current, future'⟩ target ∧
      relationMembership (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface))) target q' := by
  obtain ⟨raw, hMem, hSource, hEnv, hLabel, hCurrent, _, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
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
    simp only at hEnv hLabel hCurrent hTarget
    have hLabelEq : TypeLabel.silent = label := AutomatonConstructionLabel.visible.inj hLabel
    rw [← hEnv, ← hLabelEq, ← hCurrent, ← hTarget]
    have hOffers := TypeOffers.skip outer alphabet
      ⟨PactTypeAlphabet.environment_wellFormed hOuterMem, hClock⟩
    exact ⟨.skip alphabet, ∅, ⟨hOffers.toTypeTransition, hOffers⟩,
      relationMembership_par_final alphabet left right interface⟩

/-- Parallel current-offer correspondence follows the relation's product,
survivor, and final-state clauses. Only lower-rank child hypotheses are used. -/
theorem currentOfferCorrespondence_par_of_typeWF
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeft : CurrentOfferCorrespondence left) (hRight : CurrentOfferCorrespondence right)
    (hSurvivorLeft : CurrentOfferCorrespondence (left.reannotate alphabet))
    (hSurvivorRight : CurrentOfferCorrespondence (right.reannotate alphabet))
    (hLeftMenu : FutureOffersAgree left) (hRightMenu : FutureOffersAgree right) :
    CurrentOfferCorrespondence (.par alphabet left right interface) := by
  constructor
  · -- Forward direction: invert the represented source, then the semantic step.
    intro rho target q env label current future hRelated hStep
    rcases relationMembership_par_cases alphabet left right interface hRelated with
      hPair | hSurvivorL | hSurvivorR | hDone
    · obtain ⟨qL, qR, rhoL, rhoR, hEntry, hRelL, hRelR⟩ := hPair
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_pair_forward hWF hLeft hRight hLeftMenu hRightMenu hRelL hRelR hStep
    · obtain ⟨qL, residual, hEntry, hChild, _⟩ := hSurvivorL
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_survivorLeft_forward hWF hSurvivorLeft hChild hStep
    · obtain ⟨qR, residual, hEntry, hChild, _⟩ := hSurvivorR
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_survivorRight_forward hWF hSurvivorRight hChild hStep
    · injection hDone with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_final_forward hStep
  · -- Backward direction: the same source clauses determine the edge family.
    intro rho q q' env label current future hRelated hEdge
    rcases relationMembership_par_cases alphabet left right interface hRelated with
      hPair | hSurvivorL | hSurvivorR | hDone
    · obtain ⟨qL, qR, rhoL, rhoR, hEntry, hRelL, hRelR⟩ := hPair
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_pair_backward hWF hLeft hRight hLeftMenu hRightMenu hRelL hRelR hEdge
    · obtain ⟨qL, residual, hEntry, hChild, _⟩ := hSurvivorL
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_survivorLeft_backward hWF hSurvivorLeft hChild hEdge
    · obtain ⟨qR, residual, hEntry, hChild, _⟩ := hSurvivorR
      injection hEntry with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_survivorRight_backward hWF hSurvivorRight hChild hEdge
    · injection hDone with hRho hQ
      subst hRho
      subst hQ
      exact currentOffer_par_final_backward hEdge

end
end Pact
