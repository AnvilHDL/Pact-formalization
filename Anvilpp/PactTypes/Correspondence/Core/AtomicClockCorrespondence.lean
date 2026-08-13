import Anvilpp.PactTypes.Correspondence.Core.AtomicMessageCorrespondence

/-!
# Atomic tock correspondence
-/

namespace Pact

noncomputable section

/-! ### Atomic clock correspondence -/

/-- The firing edge of an atomic clock is present with its exact decoration. -/
theorem compileType_tock_action_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = true)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.tock
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.tock
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A non-clock environment gives an atomic clock its silent waiting edge. -/
theorem compileType_tock_wait_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A completed atomic clock has the standard silent idle edge. -/
theorem compileType_tock_final_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.tock_action_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.tock .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.tock = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.tock_wait_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.silent .tock current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic clock have matching compiled edges. -/
theorem compileType_tock_step_to_edge
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation .tock state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature .tock).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature .tock).HasEdge state env label offers state' ∧
        TypeCompilationRelation .tock state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | cycle_source =>
      cases hTransition with
      | cycle _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_action_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | cycle_wait _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.cycle_source⟩
          apply compileType_tock_wait_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
  | cycle_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_final_edge signature
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_tock_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature .tock).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | future => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hAction | hFinal
        · rcases hAction with ⟨edgeEnv, hLocal, rfl⟩
          by_cases hClock : edgeEnv.clock
          · left
            simp_all
          · right
            left
            simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic clock is justified by its semantic step. -/
theorem compileType_tock_edge_to_step
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation .tock state residual)
    (hEdge : (compileType signature .tock).HasEdge state env label offers state')
    (hTarget : TypeCompilationRelation .tock state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_tock_edge_cases signature hEdge
  rcases hCases with hAction | hWaiting | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.cycle env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle env ⟨hWellFormed, hClock⟩⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_source =>
            exact ⟨TypeTransition.cycle_wait env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle_wait env ⟨hWellFormed, hClock⟩⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | cycle_final =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic clock constructor satisfies the complete step correspondence. -/
theorem compileType_tock_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .tock
      (compileType signature .tock)) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation .tock state residual
      initial := compileType_initial_relation signature .tock
      initial_mem := compileType_initial_mem signature .tock
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_tock_step_to_edge signature hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_tock_edge_to_step signature
      hEnvironment hRelated hEdge hTarget

end

end Pact
