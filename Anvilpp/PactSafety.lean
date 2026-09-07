import Anvilpp.ProofHelpers
import Anvilpp.ProofHelpers.Inference.DecoratedLifting
import Anvilpp.PactTypes.Proofs.Correspondence.TypeAutoRelCore
import Anvilpp.PactTypes.Proofs.Correspondence.CasesTop
import Anvilpp.PactSafetyStructures
import Anvilpp.ProofHelpers.PrefixPlayMatch
import Anvilpp.ProofHelpers.CompatibilitySoundness
import Anvilpp.ProofHelpers.RefinementLifting

/-!
# Communication safety

Supporting definitions live in `Anvilpp/ProofHelpers.lean`.
-/

namespace Pact

noncomputable section

/-- `WFProc(P) iff DataWF(P) and TypeWF(abs(P))`.  The process alphabet checks
and regularity conditions are exactly those of its abstraction, so the process
side reuses `TypeWellFormedIn` rather than restating them. -/
def WFProc (process : Proc) : Prop :=
  DataWFProc process ∧ TypeWellFormedIn [] (inferProcess process)

end

noncomputable section

open Classical

/-! ## Type inference, refinement, and checking -/

/-- Lemma 4.1, "Strategy transfer": honest winning strategies transfer from
types to processes along conformance.

The proof follows `pactproofdetails.typ` step for step.  Build `S_P` from
`S_τ` by concretizing each chosen erased environment (Helper Lemma H3, using
the representative `γ` of Helper Lemma H2).  Take an arbitrary completed
process log `ℓ_P` under `S_P`; Helper Lemma H4 supplies a completed type log
`ℓ_τ` under `S_τ` with `Erase(ℓ_P) = ℓ_τ`.  Since `S_τ` ensures `Φ`, we get
`ℓ_τ ∈ Φ`, and since `Φ` is value-oblivious — membership depends only on the
erased log — also `ℓ_P ∈ Φ`.  Honesty of `ℓ_P` is Helper Lemma H5 applied to
the honest `ℓ_τ`.  As `ℓ_P` was arbitrary, `S_P` is honest and ensures `Φ`. -/
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
  -- Build `S_P` from `S_τ` by concretizing each chosen erased environment
  -- (Helper Lemma H3, via `helper_h2`'s representative `γ`).
  refine ⟨concretizingStrategy hConforms.some typeStrategy, ?_, ?_⟩
  · -- Honesty: the matching completed type log is honest (`S_τ` is honest),
    -- and honesty is preserved by concretization (Helper Lemmas H4, H5).
    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    exact helper_h5_honesty_preserved_by_concretization hErase
      (hHonestType typeLog hCompletedType)
  · -- The objective: `S_τ` ensures `Φ` on the matching type log, and `Φ` is
    -- value-oblivious, so it depends only on the erased log (Helper Lemma H4).
    intro log hCompleted
    obtain ⟨typeLog, hCompletedType, hErase⟩ :=
      helper_h4_completed_process_logs_erase hConforms.some typeStrategy hCompleted
    obtain ⟨witnessLog, hWitnessErase, hWitnessMem⟩ := hEnsures typeLog hCompletedType
    exact (hOblivious log witnessLog (hErase.trans hWitnessErase.symm)).mpr hWitnessMem

/-! ### Lemma 4.2

The paper's helper chain, in order: abstraction and substitution, one-step
abstraction, decorated-step lifting, clock-step reflection, readiness
reflection, and then the two closure clauses of the conformance relation. -/

/-- `P₀` is reachable from `P` when some finite execution leads to it. -/
def ProcReachable (initial residual : Proc) : Prop :=
  ∃ entries, PrefixValid initial entries residual

theorem ProcReachable.refl (process : Proc) : ProcReachable process process :=
  ⟨[], .root⟩

/-- `ConjMsgOwn` is one of the conjuncts of `TypeWF(abs(P))`. -/
theorem WFProc.conjunctRegular {process : Proc} (hWF : WFProc process) :
    Proc.ConjunctRegular process := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hOwnership, -⟩ := hWF
  exact Proc.conjunctRegular_of_conjunctiveMessageOwnership hOwnership

/-- Represented residuals: the two structural facts the conjunctive commitment
reads survive to every reachable residual. -/
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

/-- Data well-formedness is preserved along a step: the only substitutions a
rule performs are a value for a data variable and a closed recursive process
for its own binder. -/
theorem dataWFProc_step {env : Environment} {source target : Proc}
    {label : Label} (hData : DataWFProc source)
    (hStep : ProcessTransition env source label target) :
    DataWFProc target := by
  obtain ⟨_, _, hOffers⟩ := hStep
  exact dataWFProc_offers hOffers hData

/-- Helper for Lemma 4.2: decorated steps lift.

An abstract decorated step at a reachable residual is realised by a concrete
step exposing the erased current offer and the *same* future component.  The
concrete label agrees with `β` on every message observation and on the clock,
differing at most in fair-choice outcomes, and the concrete target need not
abstract to `ρ`: a conditional takes the branch its own guard selects. -/
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
  · -- `Imm(E_P) ≠ {#}`: the lifting induction
    obtain ⟨processCurrent, hImage, hLift⟩ :=
      lifting_core hStep process rfl hClock hAlpha hConj hData
    obtain ⟨target, label, hOffers, -⟩ := hLift env rfl
    exact ⟨target, label, processCurrent, hOffers, hImage⟩
  · -- `Imm(E_P) = {#}`: clock-step reflection supplies the step
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

/-- Helper for Lemma 4.2: abstraction reflects readiness. -/
theorem readiness_abstraction
    {initial process : Proc} (hWF : WFProc initial)
    (hReach : ProcReachable initial process) (hData : DataWFProc process)
    {env : Environment} :
    TypeReady (eraseEnvironment env) (inferProcess process) →
      ProcessReady env process := by
  intro hReady
  obtain ⟨typeLabel, typeTarget, hTransition⟩ := hReady
  -- Every derivable type step exposes at least one offer pair.
  obtain ⟨current, future, hOffers⟩ := hTransition.exists_typeOffers
  obtain ⟨target, label, _, hProcess, -⟩ :=
    decorated_step_lifting hWF hReach hData hOffers
  exact ⟨label, target, _, _, hProcess⟩

/-- Lemma 4.2, "Soundness of inferred types": `WFProc(P) ⟹ P ⊧ abs(P)`.

The witness relates each reachable residual to its own abstraction.  Step
matching is one-step abstraction; the availability clause is readiness
reflection at that pair. -/
theorem inferred_type_soundness {process : Proc} (hWF : WFProc process) :
    Conforms process (inferProcess process) := by
  refine ⟨{
    relation := fun residual residualType =>
      ProcReachable process residual ∧ DataWFProc residual ∧
        residualType = inferProcess residual
    initial := ⟨ProcReachable.refl process, hWF.1, rfl⟩
    readyReflect := ?_
    matchStep := ?_ }⟩
  · -- Availability: readiness reflection at the related pair.
    rintro p₀ τ₀ env ⟨hReach, hData, rfl⟩ hReady
    exact readiness_abstraction hWF hReach hData hReady
  · -- Step matching: one-step abstraction, and the target stays reachable.
    rintro p₀ p₁ τ₀ env label ⟨hReach, hData, rfl⟩ hStep
    obtain ⟨hAlpha, hConj⟩ := hWF.sideConditions hReach
    exact ⟨inferProcess p₁, one_step_abstraction hAlpha hConj hStep,
      hReach.step hStep, dataWFProc_step hData hStep, rfl⟩

#print axioms inferred_type_soundness
/-- Lemma 4.3, "Conformance is closed under refinement". -/
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
          -- Ready abstract type gives us a transition
          rcases hTypeReady with ⟨label, target, hStep⟩
          -- H17 decorates that transition
          obtain ⟨offers, hDecoratedStep⟩ := helper_h17_every_type_step_has_decoration hStep
          -- Refinement availability transfers the transition
          -- from τ back to τ'
          obtain ⟨target', hDecoratedStep'⟩ :=
            hRefines.some.availability hRefineRel hDecoratedStep
          -- A decorated transition contains/is backed by an ordinary transition.
          -- Need to extract it and rebuild TypeReady here.
          exact ⟨label, target', hDecoratedStep'.1⟩
        exact hConforms.some.readyReflect
          hConformRel hPreciseReady
      matchStep := by
        intro p p' τ hWitnessEnv label hConformWitnessRel hProcessStep
        -- Given p ⊧ τ there exists τ₀ such that p ⊧ τ₀ and τ τ₀ in R
        rcases hConformWitnessRel with ⟨τₒ , hConformRel, hRefineRel⟩
        obtain ⟨τ₁, hPrecTypeStep, hPrecConformRel'⟩ :=
          helper_h9_one_step_conformance_match
          hConforms.some
          hConformRel hProcessStep
        -- Given τ τ₀ in R and τ₀ -> τ₁, then we can use h10 to
        --  obtain τ' such that τ -> τ' and τ₁ τ' in R
        obtain ⟨τ', hTypeTrans, hRefineRel'⟩ :=
          helper_h10_refinement_response_coherence
            hRefines.some hRefineRel hPrecTypeStep
        exact ⟨τ', hTypeTrans, ⟨τ₁, hPrecConformRel', hRefineRel'⟩⟩
    }
    ⟩


/-- Lemma 4.4, "Soundness of type checking":
`WFProc(P) ∧ checkdo(P,τ) ⟹ P ⊧ τ`. -/
theorem type_checking_soundness
    {process : Proc} {claimed : PactType} (hWF : WFProc process)
    (hChecks : DataObliviousChecks process claimed) :
    Conforms process claimed := by
  have hPreciseConfirms : Conforms process (inferProcess process) := by
    simpa using inferred_type_soundness hWF
  have hRefines : Refines (inferProcess process) claimed := by
    simpa using hChecks
  simpa using conformance_closed_under_refinement hPreciseConfirms hRefines

#print axioms type_checking_soundness

/-- Theorem 4.1, "Decidability and complexity of type inference and
checking": inference and checking are decidable; inference runs in `O(|P|)`
and checking (given explicit automata of sizes `m`, `n`) in `O(mn)`. -/
theorem inference_checking_decidable_and_efficient
    (process : Proc) (claimed : PactType) :
    (∃ answer : Bool, answer = true ↔ DataObliviousChecks process claimed) ∧
    RunsInLinearTime inferProcess ∧
    RunsInProductTime refinementChecker := by
  sorry

/-! ## Type compatibility checking -/

/-- Proposition 4.1, "Regularity of the log objective": `Ω_T` is
omega-regular. -/
theorem log_objective_regular
    (initial : PactType) (progress : Finset ProcId) :
    OmegaRegular initial progress := by
  sorry

/-- Lemma 4.5, "Type--automaton correspondence". -/
theorem type_automaton_correspondence
     {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    Nonempty
      (TypeAutomatonCorrespondence processType
        (compileType processType)) := by
  -- The automaton
  let typeAutomaton := compileType processType
  -- The relation set
  let relation_set : Finset (PactType × TypeAutomatonState) :=
    buildRelationSet processType typeAutomaton
  -- proof witness
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

#print axioms type_automaton_correspondence
/-- Lemma 4.6, "Process--automaton correspondence": conforming processes
simulate into the type automaton. -/
theorem process_automaton_correspondence
     {process : Proc} {processType : PactType}
    (hAdmissible : AdmissibleType processType)
    (hConforms : Conforms process processType) :
    Nonempty
      (ProcessAutomatonCorrespondence
        process processType (compileType processType)) := by
  -- Compose the conformance witness with Lemma 4.5 through the type residual.
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
    -- Erased-step conformance supplies the type target.
    obtain ⟨residual₁, hTypeStep, hRelated₁⟩ :=
      conformance.matchStep hConformRel hStep
    -- Type-step decoration, then the forward direction of Lemma 4.5.
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
      · -- An edge gives a type step by Lemma 4.5, then availability reflection.
        rintro ⟨label, offers, state', hEdge⟩
        obtain ⟨residual', hDecorated, -⟩ :=
          typeCorrespondence.backward hAutoRel hEdge
        exact conformance.readyReflect hConformRel ⟨label, residual', hDecorated.1⟩
      · -- A process step gives its matching edge.
        rintro ⟨label, target, hStep⟩
        obtain ⟨state', offers, hEdge, -⟩ :=
          hMatch ⟨residual, hConformRel, hAutoRel⟩ hStep
        exact ⟨eraseLabel label, offers, state', hEdge⟩ }⟩

#print axioms process_automaton_correspondence

/-- The finite-path consequence of Lemma 4.6: every finite process execution
has a matching automaton path with the same erased environments and
observations, ending at a related state. -/
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

/-- Theorem 4.2, "Correctness of the game reduction": the honesty-aware
Rabin game exactly captures semantic compatibility.  The paper's premise is
`TypeWF(Theta_0)`, which it records as replacing the stale `AdmissibleType`. -/
theorem game_reduction_correctness
     (initial : PactType) (progress : Finset ProcId)
    (hWellFormed : TypeWellFormedIn [] initial) :
    TypeCompatible initial progress ↔
      SemanticTypeCompatible initial progress := by
  constructor
  · exact game_reduction_forward hWellFormed
  · exact game_reduction_backward hWellFormed

#print axioms game_reduction_correctness

/-- Theorem 4.3, "Soundness of type compatibility" (the main soundness
theorem): conformance of the fixed process composition plus compatibility of
the matching type composition implies communication safety of the processes.

`hFairIds` is the paper's "matching type composition": Step 3a reads
`Fair(ℓ_P)` off `TypeFair(Erase(ℓ_P))`, and the two range over `cal(Eta)(Q_0)`
and `cal(Eta)(Θ_0)` respectively. -/
theorem type_compatibility_soundness
     {process : Proc} {processType : PactType}
    {progress : Finset ProcId}
    (hWellFormed : TypeWellFormedIn [] processType)
    (hFairIds : typeFairIds processType ⊆ processFairIds process)
    (hConforms : Conforms process processType)
    (hCompatible : TypeCompatible processType progress) :
    ProcessCompatible process progress := by
  -- Step 1: Theorem 4.2 turns compatibility into a winning boundary strategy.
  obtain ⟨typeStrategy, hTypeWins⟩ :=
    (game_reduction_correctness processType progress hWellFormed).mp hCompatible
  -- Step 2: Lemma 4.1 transfers it along conformance against the objective
  -- `Φ(ℓ) = Ω_T(Erase(ℓ))`, which is value-oblivious by construction.
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
  · -- Step 3b: a stuck reachable prefix completes with the absorbing suffix, so
    -- its clock stops recurring, contradicting the transferred objective.
    intro historyPrefix hFollows hStuck
    obtain ⟨log, bound, hCompleted, hTail⟩ := completedProcessLog_of_stuck hFollows hStuck
    obtain ⟨-, hTock, -⟩ := hEnsures log hCompleted
    rw [tockOccursInfinitely_erase] at hTock
    obtain ⟨index, hMem, hGe⟩ := set_infinite_nat_iff.mp hTock (bound + 1)
    have hTockAt : (log index).2 = Label.tock := hMem
    rw [hTail index (by omega)] at hTockAt
    exact absurd hTockAt (by simp [Label.silent])
  · -- Step 3a: erasure preserves the clock, the progress markers and the
    -- fair-choice outcomes, so liveness translates entry by entry.
    intro log hCompleted
    obtain ⟨-, hTock, hLive⟩ := hEnsures log hCompleted
    refine ⟨(tockOccursInfinitely_erase log).mp hTock, fun hFair pid hPid => ?_⟩
    refine (progressOccursInfinitely_erase log pid).mp (hLive ?_ pid hPid)
    intro bid hBid
    rw [fairOccursInfinitely_erase, fairOccursInfinitely_erase]
    exact hFair bid (hFairIds hBid)

  #print axioms type_compatibility_soundness

/-- Theorem 4.4, "Decidability and complexity of compatibility": for a
monitored game with `N` vertices, `M` edges, and `K = 1+2|cal(Eta)(Θ_0)|`
Rabin pairs, compatibility is decidable in `Õ(MN(K!)^{1+o(1)})` time. -/
theorem type_compatibility_decidable_and_efficient
     (processType : PactType) (progress : Finset ProcId) :
    (∃ answer : Bool,
      answer = true ↔ TypeCompatible processType progress) ∧
    CompatibilityGameComplexityBound processType progress := by
  sorry

/-! ## Optimality of inferred types -/

/-- Lemma 4.7, "Compatibility is monotone under type refinement".

The proof is the paper's: lift the componentwise refinements to a refinement of
the whole composition (Helper Lemma H21), transfer the winning boundary strategy
along it (Helper Lemma H22), and read off compatibility with Theorem 4.2.

`hAlphabets` is the paper's `Omega(tau_i) = Omega(tau_i')`: refinement relates
behaviour, not the fixed alphabets, so H21 states the equality separately.

`hFairIds` is the counterpart of Theorem 4.3's premise: `Ω_T` quantifies its
fairness hypothesis over `cal(Eta)` of the composition it is stated for, and
`Refine` does not relate the two syntactic sets. -/
theorem compatibility_monotone_under_refinement
     {precise abstract : List PactType}
    {interfaces : List Interface} {progress : Finset ProcId}
    (hRefines : ComponentwiseRefines precise abstract)
    (hAlphabets : List.Forall₂
      (fun left right => left.alphabet = right.alphabet) precise abstract)
    (hPreciseWF : ∀ composition, composeTypes precise interfaces = some composition →
      TypeWellFormedIn [] composition)
    (hAbstractWF : ∀ composition, composeTypes abstract interfaces = some composition →
      TypeWellFormedIn [] composition)
    (hFairIds : ∀ preciseComposition abstractComposition,
      composeTypes precise interfaces = some preciseComposition →
      composeTypes abstract interfaces = some abstractComposition →
      typeFairIds abstractComposition ⊆ typeFairIds preciseComposition)
    (hCompatible : TypeTupleCompatible abstract interfaces progress) :
    TypeTupleCompatible precise interfaces progress := by
  obtain ⟨abstractComposition, hAbstract, hComp⟩ := hCompatible
  obtain ⟨preciseComposition, hPrecise⟩ :=
    composeTypes_congr_length precise abstract interfaces abstractComposition
      hRefines.length_eq hAbstract
  exact ⟨preciseComposition, hPrecise,
    compatibility_monotone_of_refines (hPreciseWF _ hPrecise) (hAbstractWF _ hAbstract)
      (hFairIds _ _ hPrecise hAbstract)
      (helper_h21_componentwise_product_lifting hRefines hAlphabets hPrecise
        hAbstract (hPreciseWF _ hPrecise) (hAbstractWF _ hAbstract)) hComp⟩

#print axioms compatibility_monotone_under_refinement

/-- The user-type domain of Theorem 4.5: the claimed tuple carries the component
alphabets of the inferred one, its composition is well formed, and it declares no
fair identifier the inferred composition lacks. -/
def UserTypeDomain (processes : List Proc) (interfaces : List Interface)
    (claimedTypes : List PactType) : Prop :=
  List.Forall₂
      (fun process claimed => claimed.alphabet = (inferProcess process).alphabet)
      processes claimedTypes ∧
    (∀ composition, composeTypes claimedTypes interfaces = some composition →
      TypeWellFormedIn [] composition) ∧
    (∀ preciseComposition abstractComposition,
      composeTypes (processes.map inferProcess) interfaces =
        some preciseComposition →
      composeTypes claimedTypes interfaces = some abstractComposition →
      typeFairIds abstractComposition ⊆ typeFairIds preciseComposition)

/-- Theorem 4.5, "Optimality of inferred types".

The forward direction exhibits the inferred tuple itself, which checks against
itself because refinement is reflexive.  The backward direction is Lemma 4.7
applied to the inferred tuple and the claimed one.  `hInferredWF` is the paper's
`WFProc` on the composition, and `UserTypeDomain` is the domain the paper's
quantifier ranges over. -/
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
    have hAlphabets : ∀ list : List Proc,
        List.Forall₂
          (fun process claimed => claimed.alphabet = (inferProcess process).alphabet)
          list (list.map inferProcess) := by
      intro list
      induction list with
      | nil => exact List.Forall₂.nil
      | cons head tail ih => exact List.Forall₂.cons rfl ih
    have hChecks : ∀ list : List Proc,
        List.Forall₂ (fun process claimed => DataObliviousChecks process claimed)
          list (list.map inferProcess) := by
      intro list
      induction list with
      | nil => exact List.Forall₂.nil
      | cons head tail ih =>
          exact List.Forall₂.cons (Refines.refl (inferProcess head)) ih
    refine ⟨processes.map inferProcess,
      ⟨hAlphabets processes, hInferredWF, ?_⟩, hChecks processes, hCompatible⟩
    intro preciseComposition abstractComposition hPrecise hAbstract
    rw [Option.some.inj (hPrecise.symm.trans hAbstract)]
  · rintro ⟨claimedTypes, ⟨hAlphabets, hClaimedWF, hFairIds⟩, hChecks, hCompatible⟩
    exact compatibility_monotone_under_refinement
      (List.forall₂_map_left_iff.mpr hChecks)
      (List.forall₂_map_left_iff.mpr (hAlphabets.imp fun _ _ h => h.symm))
      hInferredWF hClaimedWF hFairIds hCompatible

#print axioms inferred_types_optimal

/-- Corollary 4.1, "Failure rules out data-oblivious proofs".

Exactly the contrapositive of the backward direction of Theorem 4.5. -/
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

#print axioms inferred_failure_rules_out_data_oblivious_proofs

end

end Pact
