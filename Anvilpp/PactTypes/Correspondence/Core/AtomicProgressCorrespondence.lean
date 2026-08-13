import Anvilpp.PactTypes.Correspondence.Core.AtomicClockCorrespondence

/-!
# Atomic progress correspondence and compilationResolvedEdgeTargetsRelated for every atomic constructor
-/

namespace Pact

noncomputable section

/-! ### Atomic progress correspondence -/

/-- The emitting edge of an atomic progress marker is present. -/
theorem compileType_progress_action_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.progress pid)
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.progress pid)
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.progress pid)
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment]
  · simp [hSymbol]

/-- A completed progress marker has the standard silent idle edge. -/
theorem compileType_progress_final_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
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

private theorem TypeOffers.progress_fields
    {env : TypeEnvironment} {pid : ProcId}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.progress pid) (TypeLabel.progress pid)
      .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.progress pid = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic progress marker have matching compiled edges. -/
theorem compileType_progress_step_to_edge
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.progress pid)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.progress pid)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.progress pid) state' residual' := by
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
  | progress_source =>
      cases hTransition with
      | progress _ _ =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.progress_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_action_edge signature pid
          · exact hEnvironment
          · simpa [compileType] using hSymbol
  | progress_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_final_edge signature pid
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_progress_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.progress pid)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.progress pid ∧ current = ∅ ∧ future = ∅) ∨
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
        · rcases hAction with ⟨edgeEnv, _, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic progress marker has a semantic step. -/
theorem compileType_progress_edge_to_step
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hEdge : (compileType signature (.progress pid)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.progress pid) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_progress_edge_cases signature pid hEdge
  rcases hCases with hAction | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl⟩
    cases hRelated with
    | progress_source =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.progress env pid hWellFormed,
              TypeOffers.progress env pid hWellFormed⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | progress_final =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic progress constructor satisfies the complete correspondence. -/
theorem compileType_progress_correspondence
    (signature : TypeAlphabet) (pid : ProcId) :
    Nonempty (TypeAutomatonCorrespondence (.progress pid)
      (compileType signature (.progress pid))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.progress pid) state residual
      initial := compileType_initial_relation signature (.progress pid)
      initial_mem := compileType_initial_mem signature (.progress pid)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_progress_step_to_edge signature pid hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_progress_edge_to_step signature pid
      hEnvironment hRelated hEdge hTarget

/-! ### Visible-edge target relatedness for atomic fragments -/

theorem compilationResolvedEdgeTargetsRelated_skip
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .skip := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with ⟨edgeEnvironment, _, rfl⟩
  simp only at hSource hTarget
  subst target
  exact ⟨.skip, TypeCompilationRelation.skip⟩

theorem compilationResolvedEdgeTargetsRelated_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationResolvedEdgeTargetsRelated signature (.message msg dir) := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with (hFiring | hWaiting) | hFinal
  · rcases hFiring with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩
    | message_final => simp at hSource
  · rcases hWaiting with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source =>
        subst target
        exact ⟨.message msg dir,
          TypeCompilationRelation.message_source msg dir⟩
    | message_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | message_source => simp at hSource
    | message_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩

theorem compilationResolvedEdgeTargetsRelated_tock
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .tock := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    by_cases hClock : edgeEnvironment.clock
    · simp only [hClock, if_true] at hSource hTarget
      cases hRelated with
      | cycle_source =>
          subst target
          exact ⟨.skip, TypeCompilationRelation.cycle_final⟩
      | cycle_final => simp at hSource
    · simp only [hClock, if_false] at hSource hTarget
      cases hRelated with
      | cycle_source =>
          subst target
          exact ⟨.tock, TypeCompilationRelation.cycle_source⟩
      | cycle_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | cycle_source => simp at hSource
    | cycle_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.cycle_final⟩

theorem compilationResolvedEdgeTargetsRelated_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationResolvedEdgeTargetsRelated signature (.progress pid) := by
  intro source residual environment label offers target hRelated hEdge
  rcases hEdge with ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | progress_source =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩
    | progress_final => simp at hSource
  · rcases hFinal with ⟨edgeEnvironment, _, rfl⟩
    simp only at hSource hTarget
    cases hRelated with
    | progress_source => simp at hSource
    | progress_final =>
        subst target
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩

theorem compilationResolvedEdgeTargetsRelated_var
    (signature : TypeAlphabet) (name : String) :
    CompilationResolvedEdgeTargetsRelated signature (.var name) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, _, _, hLabel, _, _, _⟩
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image] at hPending
  rcases hPending with ⟨edgeEnvironment, _, rfl⟩
  simp at hLabel

end

end Pact
