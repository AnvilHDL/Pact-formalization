import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore

namespace Pact

open Classical

namespace NewCorrespondence

noncomputable section

/-- A state whose only same-cycle reference is itself closes at once: its
reference closure is the singleton. -/
lemma futureReachable_eq_singleton_of_referencedStates_subset_self
    (automaton : PendingAutomaton) (state : TypeAutomatonState)
    (hReferences : automaton.referencedStates state ⊆ {state}) :
    automaton.futureReachable state = {state} :=
  Finset.Subset.antisymm
    (automaton.futureReachable_subset_of_reference_closed state {state}
      (Finset.mem_singleton_self _)
      (fun other hOther => by
        rw [Finset.mem_singleton] at hOther
        subst hOther
        exact hReferences))
    (Finset.singleton_subset_iff.mpr
      (automaton.mem_futureReachable_self state))

/-- A symbol in a type's fixed public alphabet uses an environment over that
same fixed alphabet. -/
lemma transitionAlphabetFor_localEnvironment_mem
     (processType : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      processType.transitionAlphabet) :
    env ∈ processType.alphabet.localEnvironments := by
  classical
  unfold PactType.transitionAlphabet at hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  rcases hSymbol with ⟨env0, hEnv0, hRest⟩
  rw [Finset.mem_biUnion] at hRest
  rcases hRest with ⟨_label0, _hLabel0, hImage⟩
  rw [Finset.mem_image] at hImage
  rcases hImage with ⟨_offers0, _hOffers0, hEq⟩
  injection hEq with hEnvEq _ _
  simpa [hEnvEq] using hEnv0

/-- A symbol in a type's fixed public alphabet reports only current offers
owned by that alphabet. -/
lemma transitionAlphabetFor_current_mem
     (processType : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {action : BareMessage}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      processType.transitionAlphabet)
    (hAction : action ∈ offers.current) :
    action ∈ processType.alphabet.actions := by
  classical
  unfold PactType.transitionAlphabet at hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  rcases hSymbol with ⟨_env0, _hEnv0, hRest⟩
  rw [Finset.mem_biUnion] at hRest
  rcases hRest with ⟨_label0, _hLabel0, hImage⟩
  rw [Finset.mem_image] at hImage
  rcases hImage with ⟨offers0, hOffers0, hEq⟩
  injection hEq with _ _ hOffersEq
  subst hOffersEq
  simp only [PactTypeAlphabet.localOfferSummaries, Finset.mem_biUnion,
    Finset.mem_powerset, Finset.mem_image] at hOffers0
  rcases hOffers0 with ⟨current, hCurrent, future, _hFuture, hMk⟩
  rw [← hMk] at hAction
  exact hCurrent hAction

/-- Proves that compiled `skip`'s root offers nothing: its only edge is the
idle self-loop, which carries no current offers and references its own state. -/
lemma computeFutureOf_skip_root
     {alphabet : PactTypeAlphabet} :
    computeFutureOf (.skip alphabet) .root = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.skip alphabet))
    (.skip alphabet) .root = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1 (.skip alphabet)).states,
          edges := (compileTypeFuel 1 (.skip alphabet)).edges } :
        PendingAutomaton).referencedStates .root ⊆
        {TypeAutomatonState.root} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, _hSource⟩, hReference⟩ := hReference
    obtain ⟨environment, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hReference
    simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      using hReference
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.skip alphabet) TypeAutomatonState.root = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, _hSource⟩, hAction⟩ := hAction
  obtain ⟨environment, _, hEq⟩ := hEdgeMem
  rw [← hEq] at hAction
  simp [AutomatonConstructionLabel.semantic] at hAction

/-- Proves that compiled `skip` has the non-clock silent self-loop edge. -/
lemma compileType_skip_edge
     {alphabet : PactTypeAlphabet}
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.skip alphabet)).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge (.skip alphabet)
    .root .root env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .at .root ∅
      target := .root }, ?_, rfl, rfl, rfl, rfl,
    by simp [computeFutureOf_skip_root], rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled `skip` edge is the non-clock silent root self-loop. -/
lemma compileType_skip_edge_cases
     {alphabet : PactTypeAlphabet}
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType (.skip alphabet)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
      current = ∅ ∧ future = ∅ ∧ env.clock = false := by
  classical
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge
    (.skip alphabet) source target env label
    (TypeOfferSummary.mk current future)).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
  rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
  simp only at hSource hEnv hLabel hCurrent hFuture hTarget
  subst source
  subst env
  injection hLabel with hLabelVisible
  subst label
  subst current
  simp only [computeFutureOf_skip_root] at hFuture
  subst target
  exact ⟨rfl, rfl, rfl, rfl, hFuture.symm, hClock⟩

/-- Proves that a compiled message's `.final` state has no further same-cycle
future offers: its only edge is its own idle self-loop, and that self-loop's
future field is genuinely `.explicit ∅`, so there is nothing to reference. -/
lemma computeFutureOf_message_final
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir) :
    computeFutureOf (.message alphabet msg dir) .final = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.message alphabet msg dir))
    (.message alphabet msg dir) .final = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1
            (.message alphabet msg dir)).states,
          edges := (compileTypeFuel 1
            (.message alphabet msg dir)).edges } :
        PendingAutomaton).referencedStates .final ⊆
        {TypeAutomatonState.final} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hReference
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.message alphabet msg dir)
        TypeAutomatonState.final = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
  rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
  · rw [← hEq] at hSource; simp at hSource
  · rw [← hEq] at hSource; simp at hSource
  · rw [← hEq] at hAction; simp [AutomatonConstructionLabel.semantic] at hAction

/-- Proves that compiled message has the firing edge when the action is needed now. -/
lemma compileType_message_action_edge
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈
        (PactType.message alphabet msg dir).transitionAlphabet) :
    (compileType (.message alphabet msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (.message alphabet msg dir)
    .root .final env (TypeLabel.message msg dir)
    (TypeOfferSummary.mk {(msg, dir)} ∅)]
  -- The alphabet gate is recovered from the symbol's own current offers.
  have hAction : (msg, dir) ∈ alphabet.actions :=
    transitionAlphabetFor_current_mem (.message alphabet msg dir) hSymbol (by simp)
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.message msg dir)
      current := {(msg, dir)}
      future := .at .final ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocal, hNeed, hAction]
  · simp [computeFutureOf_message_final]

/-- Proves that compiled message has the waiting edge in a non-clock no-need environment. -/
lemma computeFutureOf_message_root
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir)
    (hDeclared : (msg, dir) ∈ alphabet.actions) :
    computeFutureOf (.message alphabet msg dir) .root =
      {(msg, dir)} := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.message alphabet msg dir))
    (.message alphabet msg dir) .root = {(msg, dir)}
  simp only [typeCompilationFuel, computeFutureOfFuel]
  set pending : PendingAutomaton :=
    { states := (compileTypeFuel 1
          (.message alphabet msg dir)).states,
      edges := (compileTypeFuel 1
          (.message alphabet msg dir)).edges } with hPendingDef
  have hReferencesFinal : pending.referencedStates .final ⊆
      insert TypeAutomatonState.root
        ({TypeAutomatonState.final} : Finset _) := by
    simp only [hPendingDef, PendingAutomaton.referencedStates,
      compileTypeFuel, finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hReference
      simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        at hReference
      exact Or.inr hReference
  have hReferencesRoot : pending.referencedStates .root ⊆
      insert TypeAutomatonState.root ({TypeAutomatonState.final} : Finset _) := by
    simp only [hPendingDef, PendingAutomaton.referencedStates, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
    · rw [← hEq] at hReference
      simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.message]
        at hReference
      exact Or.inr hReference
    · rw [← hEq] at hReference
      simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
        at hReference
      exact Or.inl hReference
    · rw [← hEq] at hSource; simp at hSource
  -- Upper bound: no more than `{root, final}` is same-cycle reachable from
  -- `root`, regardless of whether the firing edge actually exists (that
  -- depends on `` supporting `(msg, dir)`, which this lemma does
  -- not assume). `offersAt final = ∅` either way, so the bound is tight
  -- enough without pinning down reachability exactly.
  have hUpper : pending.futureReachable TypeAutomatonState.root ⊆
      insert TypeAutomatonState.root ({TypeAutomatonState.final} : Finset _) := by
    apply pending.futureReachable_subset_of_reference_closed TypeAutomatonState.root
      (insert TypeAutomatonState.root {TypeAutomatonState.final})
    · simp
    · intro state hState
      simp only [Finset.mem_insert, Finset.mem_singleton] at hState
      rcases hState with rfl | rfl
      · exact hReferencesRoot
      · exact hReferencesFinal
  have hLower : TypeAutomatonState.root ∈ pending.futureReachable TypeAutomatonState.root :=
    pending.mem_futureReachable_self TypeAutomatonState.root
  have hNoProductRoot :
      stateProductInfo (.message alphabet msg dir)
        TypeAutomatonState.root = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  have hNoProductFinal :
      stateProductInfo (.message alphabet msg dir)
        TypeAutomatonState.final = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  have hOffersRoot : pending.offersAt TypeAutomatonState.root = {(msg, dir)} := by
    apply Finset.ext
    intro action
    simp only [hPendingDef, PendingAutomaton.offersAt, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩
      rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
      · rw [← hEq] at hSource hAction
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.message] using hAction
      · rw [← hEq] at hSource hAction
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent] using hAction
      · rw [← hEq] at hSource; simp at hSource
    · intro hAction
      subst hAction
      have hEmptyLocal :
          TypeEnvironment.empty ∈ alphabet.localEnvironments := by
        simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
        exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
      have hEmptyNoNeed : ¬ TypeEnvironment.empty.hasNeed (msg, dir) := by
        simp [TypeEnvironment.hasNeed, TypeEnvironment.empty]
      refine ⟨_, ⟨Or.inl (Or.inr ⟨TypeEnvironment.empty,
        ⟨hEmptyLocal, rfl, hEmptyNoNeed, hDeclared⟩, rfl⟩), rfl⟩, ?_⟩
      simp [AutomatonConstructionLabel.semantic, TypeLabel.isTock, TypeLabel.silent]
  have hOffersFinal : pending.offersAt TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hAction
    simp only [hPendingDef, PendingAutomaton.offersAt, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
    rcases hEdgeMem with (⟨_, _, hEq⟩ | ⟨_, _, hEq⟩) | ⟨environment, _, hEq⟩
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hAction; simp [AutomatonConstructionLabel.semantic] at hAction
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [Finset.mem_biUnion] at hAction
    obtain ⟨visited, hVisited, hAction⟩ := hAction
    have hVisitedMem := hUpper hVisited
    simp only [Finset.mem_insert, Finset.mem_singleton] at hVisitedMem
    rcases hVisitedMem with rfl | rfl
    · rwa [hNoProductRoot, Finset.union_empty, hOffersRoot] at hAction
    · rw [hNoProductFinal, Finset.union_empty, hOffersFinal] at hAction
      exact absurd hAction (by simp)
  · intro action hAction
    refine Finset.mem_biUnion.mpr ⟨TypeAutomatonState.root, hLower, ?_⟩
    rw [hNoProductRoot, Finset.union_empty]
    rwa [hOffersRoot]

/-- Proves that compiled message has the waiting edge in a non-clock no-need environment. -/
lemma compileType_message_wait_edge
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hNoNeed : ¬ env.hasNeed (msg, dir))
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈
        (PactType.message alphabet msg dir).transitionAlphabet) :
    (compileType (.message alphabet msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (.message alphabet msg dir)
    .root .root env TypeLabel.silent
    (TypeOfferSummary.mk {(msg, dir)} ∅)]
  -- The alphabet gate is recovered from the symbol's own current offers.
  have hDeclared : (msg, dir) ∈ alphabet.actions :=
    transitionAlphabetFor_current_mem (.message alphabet msg dir) hSymbol (by simp)
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := {(msg, dir)}
      future := .at .root {(msg, dir)}
      target := .root }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocal, hClock, hNoNeed, hDeclared]
  · simp [PactType.alphabet,
      computeFutureOf_message_root msg dir hDeclared]

/-- Proves that compiled message has the final-state non-clock idle edge. -/
lemma compileType_message_final_edge
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.message alphabet msg dir)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (.message alphabet msg dir)
    .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .at .final ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl,
    by simp [computeFutureOf_message_final], rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled message edge is fire, wait, or final idle. -/
lemma compileType_message_edge_cases
     {alphabet : PactTypeAlphabet}
    (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType (.message alphabet msg dir)).HasEdge
      source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = {(msg, dir)} ∧ future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by

  classical
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge
    (.message alphabet msg dir) source target env label
    (TypeOfferSummary.mk current future)).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with (hFiring | hWaiting) | hFinal
  · rcases hFiring with ⟨edgeEnv, ⟨_hLocal, hNeed, _hDeclared⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [computeFutureOf_message_final] at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inl ⟨rfl, rfl, rfl, rfl, hFuture.symm, hNeed⟩
  · rcases hWaiting with ⟨edgeEnv, ⟨_hLocal, hClock, hNoNeed, hDeclared⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [PactType.alphabet,
      computeFutureOf_message_root msg dir hDeclared]
      at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, by simp [← hFuture], hClock, hNoNeed⟩)
  · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [computeFutureOf_message_final] at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, hFuture.symm, hClock⟩)

/-- Proves that compiled `#` has the clock edge in a clock environment. -/
lemma compileType_tock_action_edge
     {alphabet : PactTypeAlphabet}
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = true) :
    (compileType (.tock alphabet)).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge (.tock alphabet)
    .root .final env TypeLabel.tock (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.tock
      current := ∅
      future := .explicit ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  left
  exact ⟨env, hLocal, by simp [hClock]⟩

/-- Proves that compiled `#`'s root offers nothing: the clock edge ends the
cycle and the non-clock wait edge carries no current offers, referencing only
the root itself. -/
lemma computeFutureOf_tock_root
     {alphabet : PactTypeAlphabet} :
    computeFutureOf (.tock alphabet) .root = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.tock alphabet)) (.tock alphabet) .root = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1 (.tock alphabet)).states,
          edges := (compileTypeFuel 1 (.tock alphabet)).edges } :
        PendingAutomaton).referencedStates .root ⊆
        {TypeAutomatonState.root} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    rcases hEdgeMem with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
    · by_cases hClock : environment.clock = true
      · rw [if_pos hClock] at hEq
        rw [← hEq] at hReference
        simp [AutomatonConstructionLabel.semantic] at hReference
      · rw [if_neg hClock] at hEq
        rw [← hEq] at hReference
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hReference
    · rw [← hEq] at hSource; simp at hSource
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.tock alphabet) TypeAutomatonState.root = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_union, Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
  rcases hEdgeMem with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
  · by_cases hClock : environment.clock = true
    · rw [if_pos hClock] at hEq
      rw [← hEq] at hAction
      simp [AutomatonConstructionLabel.semantic] at hAction
    · rw [if_neg hClock] at hEq
      rw [← hEq] at hAction
      simp [AutomatonConstructionLabel.semantic] at hAction
  · rw [← hEq] at hSource; simp at hSource

/-- Proves that compiled `#`'s final state offers nothing: its only edge is
the idle self-loop. -/
lemma computeFutureOf_tock_final
     {alphabet : PactTypeAlphabet} :
    computeFutureOf (.tock alphabet) .final = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.tock alphabet)) (.tock alphabet) .final = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1 (.tock alphabet)).states,
          edges := (compileTypeFuel 1 (.tock alphabet)).edges } :
        PendingAutomaton).referencedStates .final ⊆
        {TypeAutomatonState.final} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    rcases hEdgeMem with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
    · by_cases hClock : environment.clock = true
      · rw [if_pos hClock] at hEq
        rw [← hEq] at hSource; simp at hSource
      · rw [if_neg hClock] at hEq
        rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hReference
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.tock alphabet) TypeAutomatonState.final = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_union, Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
  rcases hEdgeMem with ⟨environment, _, hEq⟩ | ⟨environment, _, hEq⟩
  · by_cases hClock : environment.clock = true
    · rw [if_pos hClock] at hEq
      rw [← hEq] at hSource; simp at hSource
    · rw [if_neg hClock] at hEq
      rw [← hEq] at hSource; simp at hSource
  · rw [← hEq] at hAction
    simp [AutomatonConstructionLabel.semantic] at hAction

/-- Proves that compiled `#` has the non-clock waiting edge. -/
lemma compileType_tock_wait_edge
     {alphabet : PactTypeAlphabet}
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.tock alphabet)).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge (.tock alphabet)
    .root .root env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .at .root ∅
      target := .root }, ?_, rfl, rfl, rfl, rfl,
    by simp [computeFutureOf_tock_root], rfl⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  left
  exact ⟨env, hLocal, by simp [hClock]⟩

/-- Proves that compiled `#` has the final-state non-clock idle edge. -/
lemma compileType_tock_final_edge
     {alphabet : PactTypeAlphabet}
    {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.tock alphabet)).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge (.tock alphabet)
    .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .at .final ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl,
    by simp [computeFutureOf_tock_final], rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled `#` edge is clock fire, non-clock wait, or final idle. -/
lemma compileType_tock_edge_cases
     {alphabet : PactTypeAlphabet}
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType (.tock alphabet)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by
  classical
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge
    (.tock alphabet) source target env label
    (TypeOfferSummary.mk current future)).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnv, _hLocal, hEdgeEq⟩
    by_cases hClock : edgeEnv.clock = true
    · rw [if_pos hClock] at hEdgeEq
      rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget
      subst source; subst env
      injection hLabel with hLabelVisible
      subst label; subst current; subst future; subst target
      exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    · rw [if_neg hClock] at hEdgeEq
      rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only [computeFutureOf_tock_root] at hFuture
      simp only at hSource hEnv hLabel hCurrent hTarget
      subst source; subst env
      injection hLabel with hLabelVisible
      subst label; subst current; subst target
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, hFuture.symm,
        by simpa using hClock⟩)
  · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [computeFutureOf_tock_final] at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, hFuture.symm, hClock⟩)

/-- Proves that a compiled progress's `.final` state has no further same-cycle
future offers: its only edge is its own idle self-loop, whose future field is
genuinely `.explicit ∅`, so there is nothing to reference. -/
lemma computeFutureOf_progress_final
     {alphabet : PactTypeAlphabet} (pid : ProcId) :
    computeFutureOf (.progress alphabet pid) .final = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.progress alphabet pid))
    (.progress alphabet pid) .final = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1
            (.progress alphabet pid)).states,
          edges := (compileTypeFuel 1
            (.progress alphabet pid)).edges } :
        PendingAutomaton).referencedStates .final ⊆
        {TypeAutomatonState.final} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨environment, _, hEq⟩
    · rw [← hEq] at hSource; simp at hSource
    · rw [← hEq] at hReference
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hReference
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.progress alphabet pid)
        TypeAutomatonState.final = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
    Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
  rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨environment, _, hEq⟩
  · rw [← hEq] at hSource; simp at hSource
  · rw [← hEq] at hAction; simp [AutomatonConstructionLabel.semantic] at hAction

/-- Proves that compiled progress has the root-to-final progress edge. -/
lemma compileType_progress_action_edge
     {alphabet : PactTypeAlphabet}
    (pid : ProcId) {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.progress alphabet pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (.progress alphabet pid)
    .root .final env (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.progress pid)
      current := ∅
      future := .at .final ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocal, hClock]
  · simp [computeFutureOf_progress_final]

/-- Proves that compiled progress has the final-state non-clock idle edge. -/
lemma compileType_progress_final_edge
     {alphabet : PactTypeAlphabet}
    (pid : ProcId) {env : TypeEnvironment}
    (hLocal : env ∈ alphabet.localEnvironments)
    (hClock : env.clock = false) :
    (compileType (.progress alphabet pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  classical
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (.progress alphabet pid)
    .final .final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := .at .final ∅
      target := .final }, ?_, rfl, rfl, rfl, rfl,
    by simp [computeFutureOf_progress_final], rfl⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    hLocal, hClock]

/-- Proves that every compiled progress edge is progress fire or final idle. -/
lemma compileType_progress_edge_cases
     {alphabet : PactTypeAlphabet} (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType (.progress alphabet pid)).HasEdge
      source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.progress pid ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) := by
  classical
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge
    (.progress alphabet pid) source target env label
    (TypeOfferSummary.mk current future)).mp hEdge
  rcases hResolved with ⟨edge, hPending, hSource, hEnv, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [computeFutureOf_progress_final] at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inl ⟨rfl, rfl, rfl, rfl, hFuture.symm, hClock⟩
  · rcases hFinal with ⟨edgeEnv, ⟨_hLocal, hClock⟩, hEdgeEq⟩
    rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTarget
    simp only [computeFutureOf_progress_final] at hFuture
    simp only at hSource hEnv hLabel hCurrent hTarget
    subst source; subst env
    injection hLabel with hLabelVisible
    subst label; subst current; subst target
    exact Or.inr ⟨rfl, rfl, rfl, rfl, hFuture.symm, hClock⟩

/-- Proves that any decorated message fire step from `a` targets `skip`. -/
lemma decorated_message_action_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {msg : MessageId} {dir : MessageDir}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.message alphabet msg dir)
      (TypeLabel.message msg dir) offers target) :
    target = .skip alphabet := by
  generalize hLabelEq : TypeLabel.message msg dir = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.message, TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated message wait step from `a` stays at `a`. -/
lemma decorated_message_wait_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {msg : MessageId} {dir : MessageDir}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.message alphabet msg dir)
      TypeLabel.silent offers target) :
    target = .message alphabet msg dir := by
  generalize hLabelEq : TypeLabel.silent = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.message, TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated step from `skip` targets `skip`. -/
lemma decorated_skip_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType}
    (hStep : DecoratedTypeTransition env (.skip alphabet) label offers target) :
    target = .skip alphabet := by
  generalize hLabelEq : label = actualLabel at hStep
  cases hStep.1
  simp_all

/-- Proves that any decorated clock step from `#` targets `skip`. -/
lemma decorated_tock_action_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.tock alphabet) TypeLabel.tock
      offers target) :
    target = .skip alphabet := by
  generalize hLabelEq : TypeLabel.tock = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated non-clock wait step from `#` stays at `#`. -/
lemma decorated_tock_wait_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {offers : TypeOfferSummary} {target : PactType}
    (hStep : DecoratedTypeTransition env (.tock alphabet) TypeLabel.silent
      offers target) :
    target = .tock alphabet := by
  generalize hLabelEq : TypeLabel.silent = actualLabel at hStep
  cases hStep.1 <;> simp [TypeLabel.silent] at hLabelEq ⊢

/-- Proves that any decorated progress step from `$t` targets `skip`. -/
lemma decorated_progress_target
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {pid : ProcId} {offers : TypeOfferSummary}
    {target : PactType}
    (hStep : DecoratedTypeTransition env (.progress alphabet pid)
      (TypeLabel.progress pid) offers target) :
    target = .skip alphabet := by
  generalize hLabelEq : TypeLabel.progress pid = actualLabel at hStep
  cases hStep.1
  all_goals simp [TypeLabel.progress] at hLabelEq ⊢

/-- Proves that any generated `skip` relation member has the `skip` relation
shape. Provenance-directed relation (Task 4): `buildRelationSetCoreFuel`'s
`.skip` case is the literal singleton `{(.skip, .root)}`, so this is now a
direct `Finset` unfold, no worklist-closure induction needed. -/
lemma relationMembership_skip_cases
     (alphabet : PactTypeAlphabet)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.skip alphabet)
          (compileType (.skip alphabet)))
        residual state) :
    residual = .skip alphabet ∧ state = .root := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_singleton,
    Prod.mk.injEq] at hRelated
  exact hRelated

/-- Proves that any generated message relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_message_cases
     (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.message alphabet msg dir)
          (compileType (.message alphabet msg dir)))
        residual state) :
    (residual = .message alphabet msg dir ∧ state = .root) ∨
      (residual = .skip alphabet ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

/-- Proves that any generated `#` relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_tock_cases
     (alphabet : PactTypeAlphabet)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.tock alphabet)
          (compileType (.tock alphabet)))
        residual state) :
    (residual = .tock alphabet ∧ state = .root) ∨
      (residual = .skip alphabet ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

/-- Proves that any generated progress relation member is one of the two PDF
pairs. See `relationMembership_skip_cases`'s doc comment for the
Task-4-enabled proof shape. -/
lemma relationMembership_progress_cases
     (alphabet : PactTypeAlphabet) (pid : ProcId)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.progress alphabet pid)
          (compileType (.progress alphabet pid)))
        residual state) :
    (residual = .progress alphabet pid ∧ state = .root) ∨
      (residual = .skip alphabet ∧ state = .final) := by
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  exact hRelated

end
end NewCorrespondence
end Pact
