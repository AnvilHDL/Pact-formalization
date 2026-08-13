import Anvilpp.PactTypes.Correspondence.Core.SyncEdgeReconstruction

/-!
# TypeAutomatonCorrespondence and the atomic skip/message correspondence
-/

namespace Pact

noncomputable section

/-- The step-for-step relation of Lemma 4.5. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')

/-- The atomic `skip` constructor already satisfies the full step correspondence. -/
theorem compileType_skip_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .skip (compileType signature .skip)) := by
  let related : PactType → TypeAutomatonState → Prop :=
    fun residual state => residual = .skip ∧ state = .root
  refine ⟨
    { relation := related
      initial := by simp [related, compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      initial_mem := by simp [compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hAlphabet
  rcases hRelated with ⟨rfl, rfl⟩
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hAlphabetParts :
        env ∈ signature.environments ∧
          label ∈ signature.labels ∧
          { current := current, future := future } ∈
            signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hAlphabet
    exact hAlphabetParts.1
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  constructor
  · rintro ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
            refine ⟨.root, ?_, by simp [related]⟩
            simp only [TypeAutomaton.HasEdge]
            have hSymbol :
                { environment := env, label := TypeLabel.silent,
                  offers := { current := ∅, future := ∅ } } ∈
                    signature.transitionAlphabet := by
              simpa [compileType] using hAlphabet
            simp [compileType, typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, resolvedAutomatonEdges]
            exact ⟨env, ⟨hLocalEnvironment, conditions.2.1,
              conditions.2.2⟩, by simp [hSymbol]⟩
  · rintro ⟨state', hEdge, hTarget⟩
    rcases hTarget with ⟨rfl, rfl⟩
    have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
    simp only [TypeAutomaton.HasEdge] at hEdge
    simp [compileType, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, resolvedAutomatonEdges] at hEdge
    simp only [DecoratedTypeTransition]
    aesop

/-- The firing edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_action_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.message msg dir)
      current := {(msg, dir)}
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.message msg dir)
        current := {(msg, dir)}
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNeed]
  · simp [hSymbol]

/-- The waiting edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_wait_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNoNeed : ¬ env.hasNeed (msg, dir)) (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := {(msg, dir)}
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := {(msg, dir)}
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNoNeed, hClock]
  · simp [hSymbol]

/-- The completed atomic message idles exactly like semantic `skip`. -/
theorem compileType_message_final_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .final env
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

private theorem TypeOffers.message_action_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) (TypeLabel.message msg dir)
      .skip current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.message msg dir = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.message, typeFutureOffers, typeFutureOffersFuel]

private theorem TypeOffers.message_wait_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) TypeLabel.silent
      (.message msg dir) current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.silent, typeFutureOffers, typeFutureOffersFuel]

private theorem TypeOffers.skip_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .skip TypeLabel.silent .skip current future) :
    current = ∅ ∧ future = ∅ := by
  cases hOffers <;>
    simp_all

/-- Semantic steps of an atomic message have matching compiled edges. -/
theorem compileType_message_step_to_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.message msg dir)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.message msg dir)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.message msg dir) state' residual' := by
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
  | message_source =>
      cases hTransition with
      | action _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_action_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | action_wait _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.message_source msg dir⟩
          apply compileType_message_wait_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

  | message_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_final_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_message_edge_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.message msg dir)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = {(msg, dir)} ∧ future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
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
        rcases hPendingEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨edgeEnv, ⟨_, hNeed⟩, rfl⟩
          simp_all
        · rcases hWaiting with ⟨edgeEnv, ⟨_, hClock, hNoNeed⟩, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic message is justified by its semantic step. -/
theorem compileType_message_edge_to_step
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hEdge : (compileType signature (.message msg dir)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.message msg dir) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_message_edge_cases signature msg dir hEdge
  rcases hCases with hFiring | hWaiting | hFinal
  · rcases hFiring with ⟨rfl, rfl, rfl, rfl, rfl, hNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_final =>
            refine ⟨TypeTransition.action env msg dir
              ⟨hWellFormed, hNeed⟩, ?_⟩
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_source =>
            refine ⟨TypeTransition.action_wait env msg dir
              ⟨hWellFormed, hNoNeed, hClock⟩, ?_⟩
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action_wait env msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | message_final =>
        cases hTarget with
        | message_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic message constructor satisfies the complete step correspondence. -/
theorem compileType_message_correspondence
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    Nonempty (TypeAutomatonCorrespondence (.message msg dir)
      (compileType signature (.message msg dir))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.message msg dir) state residual
      initial := compileType_initial_relation signature (.message msg dir)
      initial_mem := compileType_initial_mem signature (.message msg dir)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_message_step_to_edge signature msg dir
      hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_message_edge_to_step signature msg dir
      hEnvironment hRelated hEdge hTarget

end

end Pact
