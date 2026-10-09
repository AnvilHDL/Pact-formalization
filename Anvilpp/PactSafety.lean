import Anvilpp.ProofHelpers
import Anvilpp.ProofHelpers.Inference.DecoratedLifting
import Anvilpp.ProofHelpers.Inference.AbstractionIdentifiers
import Anvilpp.PactTypes.Proofs.Correspondence.TypeAutoRelCore
import Anvilpp.PactTypes.Proofs.Correspondence.CasesTop
import Anvilpp.PactSafetyStructures
import Anvilpp.ProofHelpers.PrefixPlayMatch
import Anvilpp.ProofHelpers.CompatibilitySoundness
import Anvilpp.ProofHelpers.RefinementLifting

/-! # Communication safety -/

namespace Pact

noncomputable section

/-- A process is well formed when its data and inferred type are well formed. -/
def WFProc (process : Proc) : Prop :=
  DataWFProc process ∧ TypeWellFormedIn [] (inferProcess process)

end

noncomputable section

open Classical

/-! ## Type inference, refinement, and checking -/

/-- Honest strategies enforcing value-oblivious objectives transfer from types to conforming processes. -/
theorem strategy_transfer
    {process : Proc} {processType : PactType} {objective : ProcessObjective}
    (hConforms : Conforms process processType)
    (hOblivious : ValueOblivious objective)
    (hTypeStrategy :
      ∃ strategy : TypeStrategy,
        HonestTypeStrategy processType strategy ∧
        ∀ log, CompletedTypeLog processType strategy log →
          ErasedObjective objective log) :
    ∃ strategy : ProcessStrategy process,
      HonestProcessStrategy strategy ∧
      ∀ log, CompletedProcessLog strategy log → log ∈ objective := by
  obtain ⟨typeStrategy, hHonestType, hEnsures⟩ := hTypeStrategy

  -- Concretization preserves completed logs and honesty.
  refine ⟨concretizingStrategy hConforms.some typeStrategy, ?_, ?_⟩
  ·

    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    exact helper_h5_honesty_preserved_by_concretization hErase
      (hHonestType typeLog hCompletedType)
  ·

    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    obtain ⟨witnessLog, hWitnessErase, hWitnessMem⟩ := hEnsures typeLog hCompletedType
    exact (hOblivious log witnessLog (hErase.trans hWitnessErase.symm)).mpr hWitnessMem

/-! ### Inference soundness -/

/-- `P₀` is reachable from `P` when some finite execution leads to it. -/
def ProcReachable (initial residual : Proc) : Prop :=
  ∃ entries, PrefixValid initial entries residual

theorem ProcReachable.refl (process : Proc) : ProcReachable process process :=
  ⟨[], .root⟩

/-- Well-formed processes satisfy conjunctive branch regularity. -/
theorem WFProc.conjunctRegular {process : Proc} (hWF : WFProc process) :
    Proc.ConjunctRegular process := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hOwnership, -⟩ := hWF
  exact Proc.conjunctRegular_of_conjunctiveMessageOwnership hOwnership

/-- Reachable residuals preserve alphabet well-formedness and conjunctive branch regularity. -/
theorem WFProc.sideConditions {initial residual : Proc} (hWF : WFProc initial)
    (hReach : ProcReachable initial residual) :
    Proc.AlphabetWellFormed residual ∧ Proc.ConjunctRegular residual := by
  obtain ⟨entries, hValid⟩ := hReach
  exact prefixValid_sideConditions hWF.2 hWF.conjunctRegular hValid

theorem ProcReachable.step {initial current next : Proc} {env : Environment}
    {label : Label} (hReach : ProcReachable initial current)
    (hStep : ProcessTransition env current label next) :
    ProcReachable initial next := by
  obtain ⟨entries, hValid⟩ := hReach
  obtain ⟨_, _, hOffers⟩ := hStep
  exact ⟨entries ++ [(env, label, next)], hValid.step ⟨_, _, hOffers⟩⟩

/-- Process transitions preserve data well-formedness. -/
theorem dataWFProc_step {env : Environment} {source target : Proc}
    {label : Label} (hData : DataWFProc source)
    (hStep : ProcessTransition env source label target) :
    DataWFProc target := by
  obtain ⟨_, _, hOffers⟩ := hStep
  exact dataWFProc_offers hOffers hData

/-- An abstract step at a reachable residual has a concrete step with the same
erased current offers and future offers; their targets need not correspond. -/
theorem decorated_step_lifting
    {initial process : Proc} (hWF : WFProc initial)
    (hReach : ProcReachable initial process) (hData : DataWFProc process)
    {env : Environment} {typeTarget : PactType} {typeLabel : TypeLabel}
    {current future : Finset BareMessage}
    (hStep : TypeOffers (eraseEnvironment env) (inferProcess process)
      typeLabel typeTarget current future) :
    ∃ target label processCurrent,
      Offers env process label target processCurrent future ∧
        processCurrent.image Offer.bare = current := by
  obtain ⟨hAlpha, hConj⟩ := hWF.sideConditions hReach
  by_cases hClock : (eraseEnvironment env).clock = false
  ·
    obtain ⟨processCurrent, hImage, hLift⟩ :=
      lifting_core hStep process rfl hClock hAlpha hConj hData
    obtain ⟨target, label, hOffers, -⟩ := hLift env rfl
    exact ⟨target, label, processCurrent, hOffers, hImage⟩
  ·
    have hEnvClock : env.clock = true := by
      have : env.clock = (eraseEnvironment env).clock := rfl
      rw [this]
      cases hBool : (eraseEnvironment env).clock with
      | false => exact absurd hBool hClock
      | true => rfl
    have hTypeWF := hStep.env_wellFormed
      ((Proc.alphabetWellFormed_iff process).1 hAlpha)
    have hEnvWF : env.WellFormed (inferProcess process).alphabet :=
      (environment_wellFormed_iff env _).2 hTypeWF
    have hEnvTock : env = Environment.tock := environment_eq_tock hEnvWF hEnvClock
    have hEraseTock : eraseEnvironment env = TypeEnvironment.tock := by
      rw [hEnvTock]; exact eraseEnvironment_tock
    obtain ⟨hLabel, hCurrent, hFuture⟩ := hStep.clock_shape hEraseTock
    obtain ⟨target, hOffers⟩ :=
      clock_step_reflection hStep hEraseTock process rfl hAlpha
    subst hCurrent; subst hFuture
    exact ⟨target, Label.tock, ∅, by rw [hEnvTock]; exact hOffers, by simp⟩

/-- Readiness of the inferred type implies readiness of the reachable process residual. -/
theorem readiness_abstraction
    {initial process : Proc} (hWF : WFProc initial)
    (hReach : ProcReachable initial process) (hData : DataWFProc process)
    {env : Environment} :
    TypeReady (eraseEnvironment env) (inferProcess process) →
      ProcessReady env process := by
  intro hReady
  obtain ⟨typeLabel, typeTarget, hTransition⟩ := hReady

  obtain ⟨current, future, hOffers⟩ := hTransition.exists_typeOffers
  obtain ⟨target, label, _, hProcess, -⟩ :=
    decorated_step_lifting hWF hReach hData hOffers
  exact ⟨label, target, _, _, hProcess⟩

/-- Every well-formed process conforms to its inferred type. -/
theorem inferred_type_soundness {process : Proc} (hWF : WFProc process) :
    Conforms process (inferProcess process) := by
  refine ⟨{
    relation := fun residual residualType =>
      ProcReachable process residual ∧ DataWFProc residual ∧
        residualType = inferProcess residual
    initial := ⟨ProcReachable.refl process, hWF.1, rfl⟩
    readyReflect := ?_
    matchStep := ?_ }⟩
  ·
    rintro p₀ τ₀ env ⟨hReach, hData, rfl⟩ hReady
    exact readiness_abstraction hWF hReach hData hReady
  ·
    rintro p₀ p₁ τ₀ env label ⟨hReach, hData, rfl⟩ hStep
    obtain ⟨hAlpha, hConj⟩ := hWF.sideConditions hReach
    exact ⟨inferProcess p₁, one_step_abstraction hAlpha hConj hStep,
      hReach.step hStep, dataWFProc_step hData hStep, rfl⟩

/-- A process conforming to a precise type also conforms to any type it refines. -/
theorem conformance_closed_under_refinement
    {process : Proc} {precise abstract : PactType}
    (hConforms : Conforms process precise)
    (hRefines : Refines precise abstract) :
    Conforms process abstract := by
    let witness_relation_fun :  Proc → PactType → Prop := fun p τ =>
      ∃ τ', hConforms.some.relation p τ' ∧ hRefines.some.relation τ' τ
    exact ⟨{
      relation := witness_relation_fun
      initial := by
        have hProcPreciseInitial := hConforms.some.initial
        have hPreciseAbsRefinesInitial := hRefines.some.initial
        refine ⟨precise, hProcPreciseInitial, hPreciseAbsRefinesInitial⟩
      readyReflect := by
        intro p τ hWitnessEnv hWitnessRel hTypeReady
        rcases hWitnessRel with ⟨τ', hConformRel, hRefineRel⟩
        have hPreciseReady : TypeReady (eraseEnvironment hWitnessEnv) τ' := by

          rcases hTypeReady with ⟨label, target, hStep⟩

          obtain ⟨offers, hDecoratedStep⟩ := helper_h17_every_type_step_has_decoration hStep

          obtain ⟨target', hDecoratedStep'⟩ :=
            hRefines.some.availability hRefineRel hDecoratedStep

          exact ⟨label, target', hDecoratedStep'.1⟩
        exact hConforms.some.readyReflect
          hConformRel hPreciseReady
      matchStep := by
        intro p p' τ hWitnessEnv label hConformWitnessRel hProcessStep

        rcases hConformWitnessRel with ⟨τₒ , hConformRel, hRefineRel⟩
        obtain ⟨τ₁, hPrecTypeStep, hPrecConformRel'⟩ :=
          helper_h9_one_step_conformance_match
          hConforms.some
          hConformRel hProcessStep

        obtain ⟨τ', hTypeTrans, hRefineRel'⟩ :=
          helper_h10_refinement_response_coherence
            hRefines.some hRefineRel hPrecTypeStep
        exact ⟨τ', hTypeTrans, ⟨τ₁, hPrecConformRel', hRefineRel'⟩⟩
    }
    ⟩

/-- A well-formed process conforms to every type accepted by data-oblivious checking. -/
theorem type_checking_soundness
    {process : Proc} {claimed : PactType} (hWF : WFProc process)
    (hChecks : DataObliviousChecks process claimed) :
    Conforms process claimed := by
  have hPreciseConfirms : Conforms process (inferProcess process) := by
    simpa using inferred_type_soundness hWF
  have hRefines : Refines (inferProcess process) claimed := by
    simpa using hChecks
  simpa using conformance_closed_under_refinement hPreciseConfirms hRefines

/-- Componentwise checking gives parallel conformance when component alphabets
agree and the process and claimed type compositions are well formed. -/
theorem compositional_type_checking_soundness
    {left right : Proc} {leftType rightType : PactType} {interface : Interface}
    (hWF : WFProc (parallelProc left right interface))
    (hClaimedWF : TypeWellFormedIn [] (parallelType leftType rightType interface))
    (hLeftAlphabet : left.alphabet = leftType.alphabet)
    (hRightAlphabet : right.alphabet = rightType.alphabet)
    (hLeftChecks : DataObliviousChecks left leftType)
    (hRightChecks : DataObliviousChecks right rightType) :
    Conforms (parallelProc left right interface)
      (parallelType leftType rightType interface) := by
  have hAbstraction : inferProcess (parallelProc left right interface) =
      parallelType (inferProcess left) (inferProcess right) interface := by
    simp [parallelProc, parallelType, inferProcess]
  apply conformance_closed_under_refinement (inferred_type_soundness hWF)
  rw [hAbstraction]
  exact refines_parallel hLeftChecks hRightChecks
    (by simpa using hLeftAlphabet) (by simpa using hRightAlphabet)
    (ResignRegular.of_typeWellFormedIn (hAbstraction ▸ hWF.2))
    (ResignRegular.of_typeWellFormedIn hClaimedWF)

/-! ## Type compatibility checking -/

/-- The completed-log objective over the finite boundary alphabet is omega-regular. -/
theorem log_objective_regular
    (initial : PactType) (progress : Finset ProcId) :
    OmegaRegular initial progress :=
  omegaRegular_log_objective initial progress

/-- An admissible type and its compiled automaton match decorated steps in both directions. -/
theorem type_automaton_correspondence
     {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    Nonempty
      (TypeAutomatonCorrespondence processType
        (compileType processType)) := by

  let typeAutomaton := compileType processType

  let relation_set : Finset (PactType × TypeAutomatonState) :=
    buildRelationSet processType typeAutomaton

  exact ⟨{
      relation := relationMembership relation_set
      initial := by
        simpa [relation_set, typeAutomaton] using
          buildRelationSet_initial processType typeAutomaton
      initial_mem := by
        have hInitialRelated :
            relationMembership
              (buildRelationSet processType (compileType processType))
              processType (compileType processType).initial := by
          simpa using
            buildRelationSet_initial processType
              (compileType processType)
        simpa [typeAutomaton] using
          helper_h12_compiled_state_shape hInitialRelated
      forward := by
        intro residual residual' state env label offers hRelated hStep
        exact (correspondence_steps processType hAdmissible).1
          (by simpa [relation_set, typeAutomaton] using hRelated) hStep
      backward := by
        intro residual state state' env label offers hRelated hEdge
        exact (correspondence_steps processType hAdmissible).2
          (by simpa [relation_set, typeAutomaton] using hRelated)
          (by simpa [typeAutomaton] using hEdge)
    }⟩

/-- A conforming process matches steps and readiness with its type's compiled automaton. -/
theorem process_automaton_correspondence
     {process : Proc} {processType : PactType}
    (hAdmissible : AdmissibleType processType)
    (hConforms : Conforms process processType) :
    Nonempty
      (ProcessAutomatonCorrespondence
        process processType (compileType processType)) := by

  let typeCorrespondence := (type_automaton_correspondence hAdmissible).some
  let conformance := hConforms.some
  have hMatch : ∀ {p₀ p₁ : Proc} {state : TypeAutomatonState}
      {env : Environment} {label : Label},
      (∃ residual, conformance.relation p₀ residual ∧
        typeCorrespondence.relation residual state) →
      ProcessTransition env p₀ label p₁ →
      ∃ state' offers,
        (compileType processType).HasEdge state (eraseEnvironment env)
          (eraseLabel label) offers state' ∧
        ∃ residual, conformance.relation p₁ residual ∧
          typeCorrespondence.relation residual state' := by
    rintro p₀ p₁ state env label ⟨residual, hConformRel, hAutoRel⟩ hStep

    obtain ⟨residual₁, hTypeStep, hRelated₁⟩ :=
      conformance.matchStep hConformRel hStep

    obtain ⟨offers, hDecorated⟩ := hTypeStep.exists_decorated
    obtain ⟨state', hEdge, hAutoRel₁⟩ :=
      typeCorrespondence.forward hAutoRel hDecorated
    exact ⟨state', offers, hEdge, residual₁, hRelated₁, hAutoRel₁⟩
  exact ⟨{
    relation := fun residual state =>
      ∃ residualType, conformance.relation residual residualType ∧
        typeCorrespondence.relation residualType state
    initial := ⟨processType, conformance.initial, typeCorrespondence.initial⟩
    matchStep := hMatch
    readyAgree := by
      rintro p₀ state env ⟨residual, hConformRel, hAutoRel⟩
      constructor
      ·
        rintro ⟨label, offers, state', hEdge⟩
        obtain ⟨residual', hDecorated, -⟩ :=
          typeCorrespondence.backward hAutoRel hEdge
        exact conformance.readyReflect hConformRel ⟨label, residual', hDecorated.1⟩
      ·
        rintro ⟨label, target, hStep⟩
        obtain ⟨state', offers, hEdge, -⟩ :=
          hMatch ⟨residual, hConformRel, hAutoRel⟩ hStep
        exact ⟨eraseLabel label, offers, state', hEdge⟩ }⟩

/-- Every finite process execution has an automaton path with the same erased labels
and environments, ending at a related state. -/
theorem process_automaton_path
    {process : Proc} {processType : PactType}
    (correspondence :
      ProcessAutomatonCorrespondence process processType (compileType processType))
    {entries : List (Environment × Label × Proc)} {residual : Proc}
    (hValid : PrefixValid process entries residual) :
    ∃ state,
      AutomatonPath (compileType processType) (compileType processType).initial
        (entries.map fun entry => (eraseEnvironment entry.1, eraseLabel entry.2.1))
        state ∧
      correspondence.relation residual state := by
  induction hValid with
  | root => exact ⟨_, AutomatonPath.root, correspondence.initial⟩
  | step hPrefix hStep ih =>
      obtain ⟨state, hPath, hRelated⟩ := ih
      obtain ⟨state', offers, hEdge, hRelated'⟩ :=
        correspondence.matchStep hRelated hStep
      exact ⟨state', by simpa using hPath.step hEdge, hRelated'⟩

/-- Game-based and completed-log compatibility agree for well-formed types. -/
theorem game_reduction_correctness
     (initial : PactType) (progress : Finset ProcId)
    (hWellFormed : TypeWellFormedIn [] initial) :
    TypeCompatible initial progress ↔
      SemanticTypeCompatible initial progress := by
  constructor
  · exact game_reduction_forward hWellFormed
  · exact game_reduction_backward hWellFormed

/-- Compatibility transfers to a conforming process with the same fair-choice
and progress identifiers. -/
theorem type_compatibility_soundness
     {process : Proc} {processType : PactType}
    {progress : Finset ProcId}
    (hWellFormed : TypeWellFormedIn [] processType)
    (hFairIds : typeFairIds processType = processFairIds process)
    (_hProgressIds : processType.ProgressIds = processProgressIds process)
    (hConforms : Conforms process processType)
    (hCompatible : TypeCompatible processType progress) :
    ProcessCompatible process progress := by

  obtain ⟨typeStrategy, hTypeWins⟩ :=
    (game_reduction_correctness processType progress hWellFormed).mp hCompatible

  -- The objective depends only on the erased log.
  obtain ⟨strategy, hHonest, hEnsures⟩ :=
    strategy_transfer (objective :=
        {log | TypeWinningObjective processType progress (eraseProcessLog log)})
      hConforms
      (fun left right hErase => by simp only [Set.mem_setOf_eq, hErase])
      ⟨typeStrategy, fun log hCompleted => (hTypeWins log hCompleted).1,
        fun log hCompleted =>
          ⟨concreteLog log, eraseProcessLog_concreteLog log, by
            simp only [Set.mem_setOf_eq, eraseProcessLog_concreteLog]
            exact hTypeWins log hCompleted⟩⟩
  refine ⟨strategy, hHonest, ?_, ?_⟩
  ·

    intro historyPrefix hFollows hStuck
    obtain ⟨log, bound, hCompleted, hTail⟩ := completedProcessLog_of_stuck hFollows hStuck
    obtain ⟨-, hTock, -⟩ := hEnsures log hCompleted
    rw [tockOccursInfinitely_erase] at hTock
    obtain ⟨index, hMem, hGe⟩ := set_infinite_nat_iff.mp hTock (bound + 1)
    have hTockAt : (log index).2 = Label.tock := hMem
    rw [hTail index (by omega)] at hTockAt
    exact absurd hTockAt (by simp [Label.silent])
  ·

    intro log hCompleted
    obtain ⟨-, hTock, hLive⟩ := hEnsures log hCompleted
    refine ⟨(tockOccursInfinitely_erase log).mp hTock, fun hFair pid hPid => ?_⟩
    refine (progressOccursInfinitely_erase log pid).mp (hLive ?_ pid hPid)
    intro bid hBid
    rw [fairOccursInfinitely_erase, fairOccursInfinitely_erase]
    exact hFair bid (hFairIds ▸ hBid)

/-! ## Optimality of inferred types -/

/-- Componentwise refinement preserves compatibility at equal component
alphabets, fair-choice identifiers, and progress identifiers. -/
theorem compatibility_monotone_under_refinement
     {precise abstract : List PactType}
    {interfaces : List Interface} {progress : Finset ProcId}
    (hRefines : ComponentwiseRefines precise abstract)
    (hAlphabets : List.Forall₂
      (fun left right => left.alphabet = right.alphabet) precise abstract)
    (hIdentifiers : List.Forall₂ (fun left right =>
      typeFairIds left = typeFairIds right ∧ left.ProgressIds = right.ProgressIds)
      precise abstract)
    (hPreciseWF : ∀ composition, composeTypes precise interfaces = some composition →
      TypeWellFormedIn [] composition)
    (hAbstractWF : ∀ composition, composeTypes abstract interfaces = some composition →
      TypeWellFormedIn [] composition)
    (hCompatible : TypeTupleCompatible abstract interfaces progress) :
    TypeTupleCompatible precise interfaces progress := by
  obtain ⟨abstractComposition, hAbstract, hComp⟩ := hCompatible
  obtain ⟨preciseComposition, hPrecise⟩ :=
    composeTypes_congr_length precise abstract interfaces abstractComposition
      hRefines.length_eq hAbstract
  obtain ⟨hFairIds, hProgressIds⟩ :=
    composeTypes_identifier_congr hIdentifiers hPrecise hAbstract
  exact ⟨preciseComposition, hPrecise,
    compatibility_monotone_of_refines (hPreciseWF _ hPrecise) (hAbstractWF _ hAbstract)
      hFairIds hProgressIds
      (helper_h21_componentwise_product_lifting hRefines hAlphabets hPrecise
        hAbstract (hPreciseWF _ hPrecise) (hAbstractWF _ hAbstract)) hComp⟩

/-- Claimed components match the processes' alphabets and identifiers, and
their composition is well formed. -/
def UserTypeDomain (processes : List Proc) (interfaces : List Interface)
    (claimedTypes : List PactType) : Prop :=
  List.Forall₂
      (fun process claimed => claimed.alphabet = (inferProcess process).alphabet ∧
        typeFairIds claimed = processFairIds process ∧
        claimed.ProgressIds = processProgressIds process)
      processes claimedTypes ∧
    (∀ composition, composeTypes claimedTypes interfaces = some composition →
      TypeWellFormedIn [] composition)

/-- Inferred types are compatible exactly when some well-formed claimed tuple
with matching component alphabets and identifiers checks and is compatible. -/
theorem inferred_types_optimal
     (processes : List Proc) (interfaces : List Interface)
    (progress : Finset ProcId)
    (hInferredWF : ∀ composition,
      composeTypes (processes.map inferProcess) interfaces = some composition →
      TypeWellFormedIn [] composition) :
    TypeTupleCompatible (processes.map inferProcess) interfaces progress ↔
      ∃ claimedTypes,
        UserTypeDomain processes interfaces claimedTypes ∧
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible claimedTypes interfaces progress := by
  constructor
  · intro hCompatible
    have hDomain : ∀ list : List Proc,
        List.Forall₂
          (fun process claimed => claimed.alphabet = (inferProcess process).alphabet ∧
            typeFairIds claimed = processFairIds process ∧
            claimed.ProgressIds = processProgressIds process)
          list (list.map inferProcess) := by
      intro list
      induction list with
      | nil => exact List.Forall₂.nil
      | cons head tail ih =>
          exact List.Forall₂.cons
            ⟨rfl, typeFairIds_inferProcess head, progressIds_inferProcess head⟩ ih
    have hChecks : ∀ list : List Proc,
        List.Forall₂ (fun process claimed => DataObliviousChecks process claimed)
          list (list.map inferProcess) := by
      intro list
      induction list with
      | nil => exact List.Forall₂.nil
      | cons head tail ih =>
          exact List.Forall₂.cons (Refines.refl (inferProcess head)) ih
    exact ⟨processes.map inferProcess,
      ⟨hDomain processes, hInferredWF⟩, hChecks processes, hCompatible⟩
  · rintro ⟨claimedTypes, ⟨hDomain, hClaimedWF⟩, hChecks, hCompatible⟩
    exact compatibility_monotone_under_refinement
      (List.forall₂_map_left_iff.mpr hChecks)
      (List.forall₂_map_left_iff.mpr (hDomain.imp fun _ _ h => h.1.symm))
      (List.forall₂_map_left_iff.mpr (hDomain.imp fun process _ h =>
        ⟨(typeFairIds_inferProcess process).trans h.2.1.symm,
          (progressIds_inferProcess process).trans h.2.2.symm⟩))
      hInferredWF hClaimedWF hCompatible

/-- Failure of inferred-type compatibility excludes every compatible checked tuple
with matching alphabets and identifiers. -/
theorem inferred_failure_rules_out_data_oblivious_proofs
     {processes : List Proc} {interfaces : List Interface}
    {progress : Finset ProcId}
    (hInferredWF : ∀ composition,
      composeTypes (processes.map inferProcess) interfaces = some composition →
      TypeWellFormedIn [] composition)
    (hFailure :
      ¬ TypeTupleCompatible (processes.map inferProcess) interfaces
        progress) :
    ¬ ∃ claimedTypes,
        UserTypeDomain processes interfaces claimedTypes ∧
        List.Forall₂
          (fun process claimed => DataObliviousChecks process claimed)
          processes claimedTypes ∧
        TypeTupleCompatible claimedTypes interfaces progress :=
  fun hClaimed =>
    hFailure ((inferred_types_optimal processes interfaces progress
      hInferredWF).mpr hClaimed)

end

end Pact
