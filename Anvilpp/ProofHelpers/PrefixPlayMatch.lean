import Anvilpp.ProofHelpers.StrategyExtension
import Anvilpp.ProofHelpers.CompatibilityBridge
import Anvilpp.ProofHelpers.Inference.RepresentedResiduals

namespace Pact

noncomputable section

open Classical

/-! ## Matching represented prefixes with plays

The alphabet discipline along a represented type prefix, which is what makes
the strategy's environments legal Player-0 moves. -/

variable {initial : PactType}

/-- Every residual of a represented prefix is itself represented. -/
lemma typePrefix_represented (hWF : TypeWellFormedIn [] initial)
    {entries : TypeHistory} {residual : PactType}
    (hValid : TypePrefixValid initial entries residual) :
    ∃ state, relationMembership (buildRelationSet initial (compileType initial))
      residual state := by
  induction hValid with
  | root => exact ⟨_, buildRelationSet_initial initial (compileType initial)⟩
  | step hPrefix hStep ih =>
      obtain ⟨state, hRelated⟩ := ih
      exact represented_step (admissibleType_of_typeWellFormedIn_nil hWF) hRelated hStep

lemma typePrefix_alphabetWellFormed (hWF : TypeWellFormedIn [] initial)
    {entries : TypeHistory} {residual : PactType}
    (hValid : TypePrefixValid initial entries residual) :
    residual.AlphabetWellFormed :=
  represented_alphabetWellFormed hWF (typePrefix_represented hWF hValid).choose_spec

lemma typePrefix_alphabet (hWF : TypeWellFormedIn [] initial)
    {entries : TypeHistory} {residual : PactType}
    (hValid : TypePrefixValid initial entries residual) :
    residual.alphabet = initial.alphabet :=
  relationMembership_alphabet_eq initial residual _
    (PactType.alphabetCoherent_of_wellFormed initial hWF.1)
    (typePrefix_represented hWF hValid).choose_spec

/-- An environment that enables a step at a represented residual is a legal
Player-0 move. -/
lemma env_wellFormed_of_step (hWF : TypeWellFormedIn [] initial)
    {history : TypePrefix initial} {env : TypeEnvironment}
    (hReady : TypeReady env history.residual) :
    env.WellFormed initial.alphabet := by
  obtain ⟨label, target, hStep⟩ := hReady
  obtain ⟨current, future, hOffers⟩ := hStep.exists_typeOffers
  have hAlphabet := typePrefix_alphabetWellFormed hWF history.valid
  have hEnv := PactType.typeOffers_env_wellFormed hOffers hAlphabet
  rwa [typePrefix_alphabet hWF history.valid] at hEnv

/-- The environments a winning strategy names at the prefixes it generates are
well-formed, so they label `E_choice` edges. -/
lemma strategy_wellFormed {progress : Finset ProcId} {strategy : TypeStrategy}
    (hWF : TypeWellFormedIn [] initial)
    (hWins : ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log)
    {history : TypePrefix initial}
    (hFollows : FollowsTypeStrategy initial strategy history) :
    (strategy history.entries).WellFormed initial.alphabet :=
  env_wellFormed_of_step hWF (strategy_ready hWins hFollows)

/-! ### The Player-0 strategy read off a semantic strategy -/

lemma typeEnvironment_empty_wellFormed (alphabet : PactTypeAlphabet) :
    TypeEnvironment.empty.WellFormed alphabet := by
  refine ⟨fun h => absurd h (by simp [TypeEnvironment.empty]), fun _ => ?_, ?_, ?_⟩ <;>
    simp [TypeEnvironment.empty]

/-- The residual a resolving edge leads to: the one Lemma 4.5 matches with the
automaton state the play reaches. -/
noncomputable def recoveredResidual (initial residual : PactType)
    (env : TypeEnvironment) (label : TypeLabel) (state : TypeAutomatonState) :
    PactType :=
  if h : ∃ target, TypeTransition env residual label target ∧
      relationMembership (buildRelationSet initial (compileType initial)) target state then
    h.choose
  else residual

/-- Read one vertex of a play prefix: a resolving entry extends the recovered
history, everything else leaves it alone. -/
noncomputable def recoverStep {progress : Finset ProcId}
    (state : TypeHistory × PactType) (vertex : MonitoredVertex initial progress) :
    TypeHistory × PactType :=
  match vertex.entry, vertex.base with
  | some entry, .choice target _ =>
      (state.1 ++ [(entry.1, entry.2,
          recoveredResidual initial state.2 entry.1 entry.2 target)],
        recoveredResidual initial state.2 entry.1 entry.2 target)
  | _, _ => state

/-- The represented prefix a play prefix corresponds to. -/
noncomputable def recoverHistory {progress : Finset ProcId}
    (vertices : List (MonitoredVertex initial progress)) : TypeHistory × PactType :=
  vertices.foldl recoverStep ([], initial)

/-- The boundary environment Player 0 offers: the strategy's, guarded so that
the move is always legal. -/
noncomputable def gameEnv {progress : Finset ProcId} (strategy : TypeStrategy)
    (vertices : List (MonitoredVertex initial progress)) : TypeEnvironment :=
  if (strategy (recoverHistory vertices).1).WellFormed initial.alphabet then
    strategy (recoverHistory vertices).1
  else TypeEnvironment.empty

lemma gameEnv_wellFormed {progress : Finset ProcId} (strategy : TypeStrategy)
    (vertices : List (MonitoredVertex initial progress)) :
    (gameEnv strategy vertices).WellFormed initial.alphabet := by
  rw [gameEnv]
  split
  · assumption
  · exact typeEnvironment_empty_wellFormed _

/-- `σ_0` from `S_Θ`: at a choice vertex offer the strategy's environment for
the represented prefix the play has reached. -/
noncomputable def gameStrategyOf {progress : Finset ProcId} (strategy : TypeStrategy) :
    (compatibilityGame initial progress).Strategy :=
  fun vertices =>
    match vertices.getLast? with
    | some current =>
        { base :=
            match current.base with
            | .choice state memory => .resolve state memory (gameEnv strategy vertices)
            | other => other
          pending := current.pending
          flag := fun _ => false
          entry := none }
    | none => monitoredInitial initial progress

lemma gameStrategyOf_legal {progress : Finset ProcId} (strategy : TypeStrategy) :
    (compatibilityGame initial progress).Legal (gameStrategyOf strategy) := by
  intro history current hLast hPlayerZero
  obtain ⟨state, memory, hChoice⟩ : ∃ state memory, current.base = .choice state memory := by
    cases hBase : current.base with
    | choice state memory => exact ⟨state, memory, rfl⟩
    | resolve _ _ _ =>
        exact absurd hPlayerZero (by
          show ¬ current.base.isPlayerZero
          rw [hBase]; simp [CompatibilityVertex.isPlayerZero])
    | fail =>
        exact absurd hPlayerZero (by
          show ¬ current.base.isPlayerZero
          rw [hBase]; simp [CompatibilityVertex.isPlayerZero])
  refine ⟨?_, ?_, ?_⟩
  · show compatibilityEdge (compileType initial) initial.alphabet current.base _
    rw [gameStrategyOf]
    simp only [hLast, hChoice]
    refine ⟨?_, ?_, gameEnv_wellFormed strategy history⟩ <;> trivial
  · show compatibilityStepEntry (compileType initial) current.base _ _
    rw [gameStrategyOf]
    simp only [hLast, hChoice]
    rfl
  · rw [gameStrategyOf]
    simp only [hLast]
    refine ⟨?_, ?_⟩ <;> trivial

/-! ### The represented prefix reached after `k` rounds -/

/-- `hat(rho)_k`: the represented prefix the play has reached after `k` rounds. -/
noncomputable def playHistory {progress : Finset ProcId}
    (play : ℕ → MonitoredVertex initial progress) (round : ℕ) : TypeHistory × PactType :=
  recoverHistory ((List.range (2 * round + 1)).map play)

/-- The same prefix packaged with its validity proof. -/
noncomputable def playTypePrefix {progress : Finset ProcId}
    (play : ℕ → MonitoredVertex initial progress) (round : ℕ) : TypePrefix initial :=
  if h : TypePrefixValid initial (playHistory play round).1 (playHistory play round).2 then
    ⟨(playHistory play round).1, (playHistory play round).2, h⟩
  else ⟨[], initial, .root⟩

lemma playTypePrefix_spec {progress : Finset ProcId}
    {play : ℕ → MonitoredVertex initial progress} {round : ℕ}
    (hValid : TypePrefixValid initial (playHistory play round).1
      (playHistory play round).2) :
    (playTypePrefix play round).entries = (playHistory play round).1 ∧
      (playTypePrefix play round).residual = (playHistory play round).2 := by
  rw [playTypePrefix, dif_pos hValid]
  exact ⟨rfl, rfl⟩

lemma recoverStep_of_entry_none {progress : Finset ProcId}
    {state : TypeHistory × PactType} {vertex : MonitoredVertex initial progress}
    (hEntry : vertex.entry = none) : recoverStep state vertex = state := by
  rw [recoverStep, hEntry]

lemma playHistory_zero {progress : Finset ProcId}
    {play : ℕ → MonitoredVertex initial progress}
    (hRoot : play 0 = monitoredInitial initial progress) :
    playHistory play 0 = ([], initial) := by
  have hList : (List.range (2 * 0 + 1)).map play = [play 0] := by simp
  rw [playHistory, hList, recoverHistory, List.foldl_cons, List.foldl_nil,
    recoverStep_of_entry_none (by rw [hRoot]; rfl)]

lemma playHistory_succ {progress : Finset ProcId}
    {play : ℕ → MonitoredVertex initial progress} (round : ℕ)
    (hOdd : (play (2 * round + 1)).entry = none) :
    playHistory play (round + 1) =
      recoverStep (playHistory play round) (play (2 * round + 2)) := by
  have hIndex : 2 * (round + 1) + 1 = (2 * round + 1) + 1 + 1 := by omega
  rw [playHistory, hIndex, List.range_succ, List.range_succ, List.map_append,
    List.map_append, recoverHistory, List.foldl_append, List.foldl_append]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [recoverStep_of_entry_none hOdd]
  rfl

lemma TypePrefix.ext' {left right : TypePrefix initial}
    (hEntries : left.entries = right.entries) (hResidual : left.residual = right.residual) :
    left = right := by
  cases left; cases right; cases hEntries; cases hResidual; rfl

lemma FollowsTypeStrategy.congr {strategy : TypeStrategy} {left right : TypePrefix initial}
    (hFollows : FollowsTypeStrategy initial strategy left)
    (hEntries : left.entries = right.entries) (hResidual : left.residual = right.residual) :
    FollowsTypeStrategy initial strategy right := by
  rwa [TypePrefix.ext' hEntries hResidual] at hFollows

/-- The induction hypothesis of the paper's prefix/play match: the play sits at
`q_k^(P,F_k)` with `(Θ_k,q_k) ∈ cal(C)`, the recovered prefix is the one
`S_Θ` generated, and `F_k` admits the environment `S_Θ` is about to name. -/
def PlayMatch {progress : Finset ProcId} (strategy : TypeStrategy)
    (play : ℕ → MonitoredVertex initial progress) (round : ℕ) : Prop :=
  ∃ (state : TypeAutomatonState) (memory : HonestyMemory),
    (play (2 * round)).base = .choice state memory ∧
    relationMembership (buildRelationSet initial (compileType initial))
      (playHistory play round).2 state ∧
    (playTypePrefix play round).entries = (playHistory play round).1 ∧
    (playTypePrefix play round).residual = (playHistory play round).2 ∧
    FollowsTypeStrategy initial strategy (playTypePrefix play round) ∧
    memory.Admissible (strategy (playHistory play round).1)

/-- Base case: the empty prefix matches `s_0 = (q_0^(P,star),c_0)`. -/
lemma playMatch_zero {progress : Finset ProcId} {strategy : TypeStrategy}
    {play : ℕ → MonitoredVertex initial progress}
    (hRoot : play 0 = monitoredInitial initial progress) :
    PlayMatch strategy play 0 := by
  have hHistory := playHistory_zero (initial := initial) (progress := progress) hRoot
  have hValid : TypePrefixValid initial (playHistory play 0).1
      (playHistory play 0).2 := by rw [hHistory]; exact .root
  obtain ⟨hEntries, hResidual⟩ := playTypePrefix_spec hValid
  refine ⟨(compileType initial).initial, .star, by rw [show 2 * 0 = 0 from rfl, hRoot]; rfl,
    ?_, hEntries, hResidual, ?_, trivial⟩
  · rw [hHistory]
    exact buildRelationSet_initial initial (compileType initial)
  · have hEq : playTypePrefix play 0 = ⟨[], initial, .root⟩ :=
      TypePrefix.ext' (by rw [hEntries, hHistory]) (by rw [hResidual, hHistory])
    rw [hEq]
    exact .root

/-- The induction step of the paper's prefix/play match, in the enabled-and-honest
case: for a winning `S_Θ` the unready and dishonest cases cannot arise, so every
round fires one ordinary entry and the match extends. -/
lemma playMatch_step {progress : Finset ProcId} (hWF : TypeWellFormedIn [] initial)
    {strategy : TypeStrategy}
    (hWins : ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log)
    {play : ℕ → MonitoredVertex initial progress}
    (hConsistent : (compatibilityGame initial progress).Consistent
      (gameStrategyOf strategy) play)
    {round : ℕ} (hMatch : PlayMatch strategy play round) :
    OrdinaryTypeStep initial strategy (compatibilityPlayLog play)
        (playTypePrefix play) round ∧
      PlayMatch strategy play (round + 1) := by
  classical
  obtain ⟨state, memory, hBase, hRelated, hEntries, hResidual, hFollows, hAdm⟩ := hMatch
  have hAdmissible := admissibleType_of_typeWellFormedIn_nil hWF
  -- Player 0 offers the strategy's environment.
  have hPlayerZero : (compatibilityGame initial progress).isPlayerZero (play (2 * round)) := by
    show (play (2 * round)).base.isPlayerZero
    rw [hBase]; trivial
  have hMove := (hConsistent (2 * round)).2 hPlayerZero
  have hLast : ((List.range (2 * round + 1)).map play).getLast? = some (play (2 * round)) := by
    simp [List.range_succ]
  have hEnvWF : (strategy (playHistory play round).1).WellFormed initial.alphabet := by
    have := strategy_wellFormed hWF hWins hFollows
    rwa [hEntries] at this
  have hGameEnv : gameEnv strategy ((List.range (2 * round + 1)).map play) =
      strategy (playHistory play round).1 := by
    rw [gameEnv, show recoverHistory ((List.range (2 * round + 1)).map play) =
      playHistory play round from rfl, if_pos hEnvWF]
  have hResolveBase : (play (2 * round + 1)).base =
      .resolve state memory (strategy (playHistory play round).1) := by
    rw [hMove, gameStrategyOf]
    simp only [hLast, hBase, hGameEnv]
  have hOddEntry : (play (2 * round + 1)).entry = none := by
    rw [hMove, gameStrategyOf]
    simp only [hLast]
  -- Readiness supplies an outgoing product edge.
  have hReady : TypeReady (strategy (playHistory play round).1)
      (playHistory play round).2 := by
    have := strategy_ready hWins hFollows
    rwa [hEntries, hResidual] at this
  obtain ⟨labelWitness, targetWitness, hStepWitness⟩ := hReady
  obtain ⟨currentWitness, futureWitness, hOffersWitness⟩ := hStepWitness.exists_typeOffers
  obtain ⟨stateWitness, hEdgeWitness, -⟩ :=
    (correspondence_steps initial hAdmissible).1 (offers := ⟨currentWitness, futureWitness⟩)
      hRelated ⟨hStepWitness, hOffersWitness⟩
  have hAutoReady : ∃ label target,
      compiledTypeEdge (compileType initial) state
        (strategy (playHistory play round).1) label target :=
    ⟨labelWitness, stateWitness, _, hEdgeWitness⟩
  -- Neither failure edge is available.
  have hBaseEdge := (hConsistent (2 * round + 1)).1.1
  rw [hResolveBase] at hBaseEdge
  obtain ⟨state', memory', hChoiceBase⟩ :
      ∃ st mem, (play (2 * round + 2)).base = .choice st mem := by
    rcases compatibilityEdge_resolve_left hBaseEdge with ⟨st, mem, hEq⟩ | hFail
    · exact ⟨st, mem, hEq⟩
    · rw [hFail] at hBaseEdge
      simp only [compatibilityEdge] at hBaseEdge
      rcases hBaseEdge with hNotAdm | hNotReady
      · exact absurd hAdm hNotAdm
      · exact absurd hAutoReady hNotReady
  -- The resolving edge fires its own label.
  have hStepEntry := (hConsistent (2 * round + 1)).1.2.1
  rw [hResolveBase, hChoiceBase] at hStepEntry
  simp only [compatibilityStepEntry] at hStepEntry
  obtain ⟨label, hCompiled, hMemory, hEntry⟩ := hStepEntry
  have hLog : compatibilityPlayLog play round =
      (strategy (playHistory play round).1, label) := by
    rw [compatibilityPlayLog]
    simp only [hEntry]
    rfl
  -- Lemma 4.5 backward matches the edge with a semantic step.
  obtain ⟨offers, hHasEdge⟩ := hCompiled
  obtain ⟨residual', hDecorated, hRelated'⟩ :=
    (correspondence_steps initial hAdmissible).2 hRelated hHasEdge
  have hExists : ∃ target,
      TypeTransition (strategy (playHistory play round).1) (playHistory play round).2
          label target ∧
        relationMembership (buildRelationSet initial (compileType initial)) target state' :=
    ⟨residual', hDecorated.1, hRelated'⟩
  have hNextSpec :
      TypeTransition (strategy (playHistory play round).1) (playHistory play round).2 label
          (recoveredResidual initial (playHistory play round).2
            (strategy (playHistory play round).1) label state') ∧
        relationMembership (buildRelationSet initial (compileType initial))
          (recoveredResidual initial (playHistory play round).2
            (strategy (playHistory play round).1) label state') state' := by
    rw [recoveredResidual, dif_pos hExists]
    exact hExists.choose_spec
  have hSucc : playHistory play (round + 1) =
      ((playHistory play round).1 ++
        [(strategy (playHistory play round).1, label,
          recoveredResidual initial (playHistory play round).2
            (strategy (playHistory play round).1) label state')],
        recoveredResidual initial (playHistory play round).2
          (strategy (playHistory play round).1) label state') := by
    rw [playHistory_succ round hOddEntry]
    simp only [recoverStep, hEntry, hChoiceBase]
  -- Validity of both prefixes.
  have hValidRound : TypePrefixValid initial (playHistory play round).1
      (playHistory play round).2 := by
    rw [← hEntries, ← hResidual]; exact (playTypePrefix play round).valid
  have hValidNext : TypePrefixValid initial (playHistory play (round + 1)).1
      (playHistory play (round + 1)).2 := by
    rw [hSucc]; exact hValidRound.step hNextSpec.1
  obtain ⟨hEntries', hResidual'⟩ := playTypePrefix_spec hValidNext
  have hFollowsStep : TypeTransition (strategy (playTypePrefix play round).entries)
      (playTypePrefix play round).residual label
      (recoveredResidual initial (playHistory play round).2
        (strategy (playHistory play round).1) label state') := by
    rw [hEntries, hResidual]; exact hNextSpec.1
  refine ⟨⟨?_, ?_, ?_⟩, state', memory', ?_, ?_, hEntries', hResidual', ?_, ?_⟩
  · simp only [hLog, hEntries]
  · simp only [hLog, hEntries, hEntries', hResidual', hSucc]
  · simp only [hLog, hResidual, hResidual', hSucc]
    exact hNextSpec.1
  · rw [show 2 * (round + 1) = 2 * round + 2 from by omega]; exact hChoiceBase
  · rw [hSucc]; exact hNextSpec.2
  · refine (hFollows.step hFollowsStep).congr ?_ ?_
    · simp only [hEntries', hSucc, hEntries]
    · simp only [hResidual', hSucc]
  · rw [hMemory]
    simp only [hSucc]
    cases label with
    | tock => trivial
    | actions observations =>
        have hHonest := strategy_honest hWins hFollows hFollowsStep
          (by simp [TypeLabel.isTock])
        rw [hEntries] at hHonest
        simp only [honestyNext, HonestyMemory.Admissible]
        exact hHonest

/-- Helper Lemma H20, the `S_Θ ↦ σ_0` direction: the Player-0 strategy read off a
winning semantic strategy is legal, and every play it generates from `s_0` has a
log that `S_Θ` itself generates. -/
theorem helper_h20_strategy_to_play (hWF : TypeWellFormedIn [] initial)
    {progress : Finset ProcId} (strategy : TypeStrategy)
    (hWins : ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log) :
    (compatibilityGame initial progress).Legal (gameStrategyOf strategy) ∧
      ∀ play, play 0 = (compatibilityGame initial progress).initial →
        (compatibilityGame initial progress).Consistent (gameStrategyOf strategy) play →
        CompletedTypeLog initial strategy (compatibilityPlayLog play) := by
  refine ⟨gameStrategyOf_legal strategy, ?_⟩
  intro play hRoot hConsistent
  have hHistory := playHistory_zero (initial := initial) (progress := progress) hRoot
  have hValid : TypePrefixValid initial (playHistory play 0).1 (playHistory play 0).2 := by
    rw [hHistory]; exact .root
  obtain ⟨hEntriesRoot, hResidualRoot⟩ := playTypePrefix_spec hValid
  have hMatch : ∀ round, PlayMatch strategy play round := by
    intro round
    induction round with
    | zero => exact playMatch_zero hRoot
    | succ round ih => exact (playMatch_step hWF hWins hConsistent ih).2
  exact ⟨playTypePrefix play,
    TypePrefix.ext' (by rw [hEntriesRoot, hHistory]) (by rw [hResidualRoot, hHistory]),
    Or.inl fun round => (playMatch_step hWF hWins hConsistent (hMatch round)).1⟩

/-- Theorem 4.2, backward direction: a winning semantic strategy makes `s_0`
winning in the monitored game. -/
theorem game_reduction_backward (hWF : TypeWellFormedIn [] initial)
    {progress : Finset ProcId}
    (hSemantic : SemanticTypeCompatible initial progress) :
    TypeCompatible initial progress := by
  obtain ⟨strategy, hWins⟩ := hSemantic
  obtain ⟨hLegal, hPlays⟩ := helper_h20_strategy_to_play hWF strategy hWins
  refine ⟨gameStrategyOf strategy, hLegal, fun play hRoot hConsistent => ?_⟩
  have hPath : CompatibilityPath play :=
    ⟨hRoot, fun index => (hConsistent index).1⟩
  exact (helper_h18_objective_monitor initial progress play hPath).mpr
    (hWins _ (hPlays play hRoot hConsistent))

/-! ### The absorbing failure continuation

A dishonest or unready Player-0 choice sends the play to `⊥`, and by the sink
case of H18 such a play loses.  Making that argument needs the losing play built
explicitly. -/

/-- The environment a resolving vertex carries. -/
def CompatibilityVertex.env : CompatibilityVertex → TypeEnvironment
  | .resolve _ _ env => env
  | _ => TypeEnvironment.empty

/-- The entry a failure edge out of a vertex fires. -/
def failEntry (source : CompatibilityVertex) : TypeEnvironment × TypeLabel :=
  (source.env, TypeLabel.silent)

/-- The absorbing failure continuation of a vertex. -/
noncomputable def failTail {progress : Finset ProcId}
    (source : MonitoredVertex initial progress) : ℕ → MonitoredVertex initial progress
  | 0 => source
  | n + 1 =>
      { base := .fail
        pending := fun disjunct =>
          (monitorAdvance (ObjectiveDisjunct.req progress disjunct)
            ((failTail source n).pending disjunct)
            (typeLabelMarks (failEntry (failTail source n).base).2)).1
        flag := fun disjunct =>
          (monitorAdvance (ObjectiveDisjunct.req progress disjunct)
            ((failTail source n).pending disjunct)
            (typeLabelMarks (failEntry (failTail source n).base).2)).2
        entry := some (failEntry (failTail source n).base) }

@[simp] lemma failTail_zero {progress : Finset ProcId}
    (source : MonitoredVertex initial progress) : failTail source 0 = source := rfl

lemma failTail_base {progress : Finset ProcId}
    (source : MonitoredVertex initial progress) (n : ℕ) :
    (failTail source (n + 1)).base = .fail := rfl

lemma failTail_edge {progress : Finset ProcId}
    {source : MonitoredVertex initial progress}
    (hFail : compatibilityEdge (compileType initial) initial.alphabet source.base .fail)
    (hEntry : compatibilityStepEntry (compileType initial) source.base .fail
      (some (failEntry source.base))) (n : ℕ) :
    monitoredEdge initial progress (failTail source n) (failTail source (n + 1)) := by
  cases n with
  | zero => exact ⟨hFail, hEntry, fun _ => rfl⟩
  | succ n =>
      refine ⟨?_, ?_, fun _ => rfl⟩
      · rw [failTail_base source n]; trivial
      · rw [failTail_base source n]
        simp only [compatibilityStepEntry]
        rfl

/-- Cut a play at `cut` and let it fail forever after. -/
noncomputable def abortPlay {progress : Finset ProcId}
    (play : ℕ → MonitoredVertex initial progress) (cut : ℕ) :
    ℕ → MonitoredVertex initial progress :=
  fun index => if index ≤ cut then play index else failTail (play cut) (index - cut)

lemma abortPlay_of_le {progress : Finset ProcId}
    {play : ℕ → MonitoredVertex initial progress} {cut index : ℕ} (hLe : index ≤ cut) :
    abortPlay play cut index = play index := if_pos hLe

lemma abortPlay_of_gt {progress : Finset ProcId}
    {play : ℕ → MonitoredVertex initial progress} {cut index : ℕ} (hGt : cut < index) :
    abortPlay play cut index = failTail (play cut) (index - cut) :=
  if_neg (Nat.not_le.mpr hGt)

/-- A play cut off by a failure edge is still consistent with the strategy, and
it sinks. -/
lemma abortPlay_consistent {progress : Finset ProcId}
    {gameStrategy : (compatibilityGame initial progress).Strategy}
    {play : ℕ → MonitoredVertex initial progress} {cut : ℕ}
    (hRoot : play 0 = monitoredInitial initial progress)
    (hEdges : ∀ n, n < cut → monitoredEdge initial progress (play n) (play (n + 1)))
    (hMoves : ∀ n, n < cut → (play n).base.isPlayerZero →
      play (n + 1) = gameStrategy ((List.range (n + 1)).map play))
    (hNotZero : ¬ (play cut).base.isPlayerZero)
    (hFail : compatibilityEdge (compileType initial) initial.alphabet (play cut).base .fail)
    (hEntry : compatibilityStepEntry (compileType initial) (play cut).base .fail
      (some (failEntry (play cut).base))) :
    abortPlay play cut 0 = monitoredInitial initial progress ∧
      (compatibilityGame initial progress).Consistent gameStrategy (abortPlay play cut) ∧
      CompatibilityPath (abortPlay play cut) ∧
      (abortPlay play cut (cut + 1)).base = .fail := by
  have hStep : ∀ n, monitoredEdge initial progress
      (abortPlay play cut n) (abortPlay play cut (n + 1)) := by
    intro n
    rcases Nat.lt_trichotomy n cut with hLt | hEq | hGt
    · rw [abortPlay_of_le (Nat.le_of_lt hLt), abortPlay_of_le (Nat.succ_le_of_lt hLt)]
      exact hEdges n hLt
    · subst hEq
      rw [abortPlay_of_le (Nat.le_refl n), abortPlay_of_gt (Nat.lt_succ_self n)]
      have := failTail_edge (source := play n) hFail hEntry 0
      rw [failTail_zero] at this
      simpa using this
    · rw [abortPlay_of_gt hGt, abortPlay_of_gt (Nat.lt_succ_of_lt hGt),
        show n + 1 - cut = (n - cut) + 1 from by omega]
      exact failTail_edge hFail hEntry _
  have hZero : abortPlay play cut 0 = monitoredInitial initial progress := by
    rw [abortPlay_of_le (Nat.zero_le cut), hRoot]
  refine ⟨hZero, fun n => ⟨hStep n, ?_⟩, ⟨hZero, hStep⟩, ?_⟩
  · intro hPlayerZero
    rcases Nat.lt_or_ge n cut with hLt | hGe
    · have hList : (List.range (n + 1)).map (abortPlay play cut) =
          (List.range (n + 1)).map play := by
        refine List.map_congr_left fun index hMem => ?_
        exact abortPlay_of_le (by
          have := List.mem_range.mp hMem
          omega)
      rw [abortPlay_of_le (Nat.succ_le_of_lt hLt), hList]
      refine hMoves n hLt ?_
      rwa [abortPlay_of_le (Nat.le_of_lt hLt)] at hPlayerZero
    · rcases Nat.eq_or_lt_of_le hGe with hEq | hGt
      · rw [abortPlay_of_le (Nat.le_of_eq hEq.symm)] at hPlayerZero
        exact absurd (hEq ▸ hPlayerZero) hNotZero
      · rw [abortPlay_of_gt hGt] at hPlayerZero
        obtain ⟨earlier, hEarlier⟩ : ∃ earlier, n - cut = earlier + 1 :=
          ⟨n - cut - 1, by omega⟩
        rw [hEarlier] at hPlayerZero
        have hBase : (failTail (play cut) (earlier + 1)).base.isPlayerZero := hPlayerZero
        rw [failTail_base] at hBase
        exact absurd hBase (by simp [CompatibilityVertex.isPlayerZero])
  · rw [abortPlay_of_gt (Nat.lt_succ_self cut),
      show cut + 1 - cut = 0 + 1 from by omega, failTail_base]

/-! ### The semantic strategy read off a Player-0 strategy

The mirror of `recoverHistory`/`gameStrategyOf`: a represented prefix is turned
into the play prefix `sigma_0` generates, choosing at each resolving edge the
automaton state Lemma 4.5 matches with the semantic residual. -/

/-- The automaton state a vertex carries. -/
def CompatibilityVertex.stateOf : CompatibilityVertex → TypeAutomatonState
  | .choice state _ => state
  | .resolve state _ _ => state
  | .fail => .root

/-- The state Lemma 4.5 matches with a semantic step. -/
noncomputable def matchedState (initial : PactType) (state : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel) (residual : PactType) :
    TypeAutomatonState :=
  if h : ∃ state', compiledTypeEdge (compileType initial) state env label state' ∧
      relationMembership (buildRelationSet initial (compileType initial)) residual state' then
    h.choose
  else state

/-- Player 1's resolving move: the choice vertex the matched edge leads to. -/
noncomputable def matchingTargetVertex {progress : Finset ProcId}
    (resolve : MonitoredVertex initial progress) (label : TypeLabel)
    (target : TypeAutomatonState) : MonitoredVertex initial progress where
  base := .choice target (honestyNext resolve.base.env label)
  pending := fun disjunct => (monitorAdvance (ObjectiveDisjunct.req progress disjunct)
    (resolve.pending disjunct) (typeLabelMarks label)).1
  flag := fun disjunct => (monitorAdvance (ObjectiveDisjunct.req progress disjunct)
    (resolve.pending disjunct) (typeLabelMarks label)).2
  entry := some (resolve.base.env, label)

lemma matchingTargetVertex_edge {progress : Finset ProcId}
    {resolve : MonitoredVertex initial progress} {state : TypeAutomatonState}
    {memory : HonestyMemory} {env : TypeEnvironment}
    (hBase : resolve.base = .resolve state memory env)
    (hAdm : memory.Admissible env) {label : TypeLabel} {target : TypeAutomatonState}
    (hEdge : compiledTypeEdge (compileType initial) state env label target) :
    monitoredEdge initial progress resolve (matchingTargetVertex resolve label target) := by
  have hEnv : resolve.base.env = env := by rw [hBase]; rfl
  refine ⟨?_, ?_, ?_⟩
  · show compatibilityEdge (compileType initial) initial.alphabet resolve.base _
    rw [hBase]
    simp only [matchingTargetVertex, hEnv]
    exact ⟨hAdm, label, hEdge, by trivial⟩
  · show compatibilityStepEntry (compileType initial) resolve.base _ _
    rw [hBase]
    simp only [matchingTargetVertex, hEnv]
    refine ⟨label, hEdge, ?_, ?_⟩ <;> trivial
  · simp [matchingTargetVertex]

/-- One round of the play prefix generated by `sigma_0` along a represented
prefix. -/
noncomputable def matchingPlayStep {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (vertices : List (MonitoredVertex initial progress))
    (entry : TypeEnvironment × TypeLabel × PactType) :
    List (MonitoredVertex initial progress) :=
  vertices ++ ([gameStrategy vertices,
    matchingTargetVertex (gameStrategy vertices) entry.2.1
      (matchedState initial (gameStrategy vertices).base.stateOf
        (gameStrategy vertices).base.env entry.2.1 entry.2.2)] :
      List (MonitoredVertex initial progress))

/-- The play prefix `sigma_0` generates along a represented prefix. -/
noncomputable def matchingPlayPrefix {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (entries : TypeHistory) : List (MonitoredVertex initial progress) :=
  entries.foldl (matchingPlayStep gameStrategy) [monitoredInitial initial progress]

lemma matchingPlayPrefix_append {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (entries : TypeHistory) (entry : TypeEnvironment × TypeLabel × PactType) :
    matchingPlayPrefix gameStrategy (entries ++ [entry]) =
      matchingPlayStep gameStrategy (matchingPlayPrefix gameStrategy entries) entry := by
  simp [matchingPlayPrefix]

/-- `S_Θ` from `sigma_0`: the environment Player 0 offers at the matching play
prefix. -/
noncomputable def strategyOfGame {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy) : TypeStrategy :=
  fun entries => (gameStrategy (matchingPlayPrefix gameStrategy entries)).base.env

/-- The play prefix after `round` rounds, driven by a completed log. -/
noncomputable def gameVertices {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) :
    ℕ → List (MonitoredVertex initial progress)
  | 0 => [monitoredInitial initial progress]
  | round + 1 =>
      matchingPlayStep gameStrategy (gameVertices gameStrategy log prefixAt round)
        ((log round).1, (log round).2, (prefixAt (round + 1)).residual)

/-- Player 0's resolving vertex at round `round`. -/
noncomputable def gameResolve {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    MonitoredVertex initial progress :=
  gameStrategy (gameVertices gameStrategy log prefixAt round)

/-- The choice vertex `q_k^(P,F_k)` the play has reached. -/
noncomputable def gameChoice {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) :
    ℕ → MonitoredVertex initial progress
  | 0 => monitoredInitial initial progress
  | round + 1 =>
      matchingTargetVertex (gameResolve gameStrategy log prefixAt round) (log round).2
        (matchedState initial (gameResolve gameStrategy log prefixAt round).base.stateOf
          (gameResolve gameStrategy log prefixAt round).base.env (log round).2
          (prefixAt (round + 1)).residual)

/-- The play itself: choice vertices at even positions, resolving vertices at
odd ones. -/
noncomputable def gamePlay {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (index : ℕ) :
    MonitoredVertex initial progress :=
  if index % 2 = 0 then gameChoice gameStrategy log prefixAt (index / 2)
  else gameResolve gameStrategy log prefixAt (index / 2)

lemma gamePlay_even {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    gamePlay gameStrategy log prefixAt (2 * round) =
      gameChoice gameStrategy log prefixAt round := by
  rw [gamePlay, if_pos (by omega), show 2 * round / 2 = round from by omega]

lemma gamePlay_odd {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    gamePlay gameStrategy log prefixAt (2 * round + 1) =
      gameResolve gameStrategy log prefixAt round := by
  rw [gamePlay, if_neg (by omega), show (2 * round + 1) / 2 = round from by omega]

lemma gameVertices_eq_map {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    gameVertices gameStrategy log prefixAt round =
      (List.range (2 * round + 1)).map (gamePlay gameStrategy log prefixAt) := by
  induction round with
  | zero =>
      have hZero : gamePlay gameStrategy log prefixAt 0 =
          monitoredInitial initial progress := by
        rw [gamePlay, if_pos rfl]; rfl
      rw [gameVertices]
      simp [hZero]
  | succ round ih =>
      have hRange : List.range (2 * (round + 1) + 1) =
          List.range (2 * round + 1) ++ [2 * round + 1, 2 * round + 2] := by
        rw [show 2 * (round + 1) + 1 = (2 * round + 1) + 1 + 1 from by omega,
          List.range_succ, List.range_succ]
        simp
      rw [hRange, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [gamePlay_odd, show 2 * round + 2 = 2 * (round + 1) from by omega, gamePlay_even,
        gameChoice, gameResolve, ← ih, gameVertices, matchingPlayStep]

lemma gameVertices_eq_prefix {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    {log : TypeLog} {prefixAt : ℕ → TypePrefix initial} {bound : ℕ}
    (hRoot : prefixAt 0 = ⟨[], initial, .root⟩)
    (hSteps : ∀ n, n < bound →
      OrdinaryTypeStep initial (strategyOfGame gameStrategy) log prefixAt n) :
    ∀ {round : ℕ}, round ≤ bound →
      gameVertices gameStrategy log prefixAt round =
        matchingPlayPrefix gameStrategy (prefixAt round).entries := by
  intro round
  induction round with
  | zero => intro _; rw [gameVertices, hRoot]; rfl
  | succ round ih =>
      intro hLe
      have hStep := hSteps round (by omega)
      rw [gameVertices, ih (by omega), ← hStep.2.1, matchingPlayPrefix_append]

lemma gameVertices_getLast? {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    (gameVertices gameStrategy log prefixAt round).getLast? =
      some (gameChoice gameStrategy log prefixAt round) := by
  rw [gameVertices_eq_map, List.range_succ, List.map_append]
  simp [gamePlay_even]

lemma gamePlay_move {progress : Finset ProcId}
    (gameStrategy : (compatibilityGame initial progress).Strategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (round : ℕ) :
    gamePlay gameStrategy log prefixAt (2 * round + 1) =
      gameStrategy ((List.range (2 * round + 1)).map (gamePlay gameStrategy log prefixAt)) := by
  rw [gamePlay_odd, gameResolve, gameVertices_eq_map]

/-- Player 0's move at a choice vertex: the resolving vertex and its edge. -/
lemma gameResolve_edge {progress : Finset ProcId}
    {gameStrategy : (compatibilityGame initial progress).Strategy}
    (hLegal : (compatibilityGame initial progress).Legal gameStrategy)
    {log : TypeLog} {prefixAt : ℕ → TypePrefix initial} {round : ℕ}
    {state : TypeAutomatonState} {memory : HonestyMemory}
    (hChoice : (gameChoice gameStrategy log prefixAt round).base = .choice state memory) :
    (∃ env, (gameResolve gameStrategy log prefixAt round).base =
        .resolve state memory env) ∧
      monitoredEdge initial progress (gameChoice gameStrategy log prefixAt round)
        (gameResolve gameStrategy log prefixAt round) := by
  have hEdge := hLegal (gameVertices gameStrategy log prefixAt round)
    (gameChoice gameStrategy log prefixAt round)
    (gameVertices_getLast? gameStrategy log prefixAt round)
    (by show (gameChoice gameStrategy log prefixAt round).base.isPlayerZero
        rw [hChoice]; trivial)
  refine ⟨?_, hEdge⟩
  have hBaseEdge : compatibilityEdge (compileType initial) initial.alphabet
      (.choice state memory) (gameResolve gameStrategy log prefixAt round).base := by
    rw [← hChoice]; exact hEdge.1
  exact compatibilityEdge_choice_left hBaseEdge

/-- The environment Player 0 offers is the one `S_Θ` names. -/
lemma gameResolve_env {progress : Finset ProcId}
    {gameStrategy : (compatibilityGame initial progress).Strategy}
    {log : TypeLog} {prefixAt : ℕ → TypePrefix initial} {bound round : ℕ}
    (hRoot : prefixAt 0 = ⟨[], initial, .root⟩)
    (hSteps : ∀ n, n < bound →
      OrdinaryTypeStep initial (strategyOfGame gameStrategy) log prefixAt n)
    (hLe : round ≤ bound) :
    (gameResolve gameStrategy log prefixAt round).base.env =
      strategyOfGame gameStrategy (prefixAt round).entries := by
  rw [gameResolve, strategyOfGame,
    gameVertices_eq_prefix gameStrategy hRoot hSteps hLe]

/-- The paper's prefix/play match read backward: along a completed log of
`S_Θ = strategyOfGame σ_0`, the play `σ_0` generates stays at `q_k^(P,F_k)` with
`(Θ_k,q_k) ∈ cal(C)`, and `F_k` admits the environment `σ_0` names next. -/
lemma gameMatch {progress : Finset ProcId} (hWF : TypeWellFormedIn [] initial)
    {gameStrategy : (compatibilityGame initial progress).Strategy}
    (hLegal : (compatibilityGame initial progress).Legal gameStrategy)
    (hWins : ∀ play, play 0 = (compatibilityGame initial progress).initial →
      (compatibilityGame initial progress).Consistent gameStrategy play →
      RabinGame.Accepts (compatibilityGame initial progress) play)
    {log : TypeLog} {prefixAt : ℕ → TypePrefix initial} {bound : ℕ}
    (hRoot : prefixAt 0 = ⟨[], initial, .root⟩)
    (hSteps : ∀ n, n < bound →
      OrdinaryTypeStep initial (strategyOfGame gameStrategy) log prefixAt n) :
    ∀ round, round ≤ bound →
      (∃ state memory,
        (gameChoice gameStrategy log prefixAt round).base = .choice state memory ∧
        relationMembership (buildRelationSet initial (compileType initial))
          (prefixAt round).residual state ∧
        memory.Admissible (strategyOfGame gameStrategy (prefixAt round).entries)) ∧
      (∀ n, n < 2 * round + 1 → monitoredEdge initial progress
        (gamePlay gameStrategy log prefixAt n)
        (gamePlay gameStrategy log prefixAt (n + 1))) ∧
      (∀ n, n < 2 * round + 1 → (gamePlay gameStrategy log prefixAt n).base.isPlayerZero →
        gamePlay gameStrategy log prefixAt (n + 1) =
          gameStrategy ((List.range (n + 1)).map (gamePlay gameStrategy log prefixAt))) := by
  classical
  have hAdmissible := admissibleType_of_typeWellFormedIn_nil hWF
  have hRootPlay : gamePlay gameStrategy log prefixAt 0 = monitoredInitial initial progress := by
    rw [show (0 : ℕ) = 2 * 0 from rfl, gamePlay_even]; rfl
  intro round
  induction round with
  | zero =>
      intro _
      have hChoice : (gameChoice gameStrategy log prefixAt 0).base =
          .choice (compileType initial).initial .star := rfl
      obtain ⟨-, hEdgeAt⟩ := gameResolve_edge hLegal hChoice
      refine ⟨⟨_, _, hChoice, ?_, trivial⟩, ?_, ?_⟩
      · rw [hRoot]
        exact buildRelationSet_initial initial (compileType initial)
      · intro n hn
        have hn0 : n = 0 := by omega
        subst hn0
        rw [show (0 : ℕ) = 2 * 0 from rfl, gamePlay_even, gamePlay_odd]
        exact hEdgeAt
      · intro n hn _
        have hn0 : n = 0 := by omega
        subst hn0
        exact gamePlay_move gameStrategy log prefixAt 0
  | succ round ih =>
      intro hLe
      obtain ⟨⟨state, memory, hChoice, hRelated, hAdm⟩, hEdges, hMoves⟩ := ih (by omega)
      obtain ⟨⟨env, hResolveBase⟩, hEdgeAt⟩ := gameResolve_edge hLegal hChoice
      have hEnv : env = strategyOfGame gameStrategy (prefixAt round).entries := by
        have hE := gameResolve_env (bound := bound) hRoot hSteps (by omega :  round ≤ bound)
        rw [hResolveBase] at hE
        exact hE
      have hStep := hSteps round (by omega)
      have hSemantic : TypeTransition env (prefixAt round).residual (log round).2
          (prefixAt (round + 1)).residual := by
        rw [hEnv, ← hStep.1]; exact hStep.2.2
      obtain ⟨current, future, hOffers⟩ := hSemantic.exists_typeOffers
      obtain ⟨target, hHasEdge, hRelatedTarget⟩ :=
        (correspondence_steps initial hAdmissible).1 (offers := ⟨current, future⟩)
          hRelated ⟨hSemantic, hOffers⟩
      have hExists : ∃ state', compiledTypeEdge (compileType initial) state env
          (log round).2 state' ∧
          relationMembership (buildRelationSet initial (compileType initial))
            (prefixAt (round + 1)).residual state' :=
        ⟨target, ⟨_, hHasEdge⟩, hRelatedTarget⟩
      have hMatchedSpec : compiledTypeEdge (compileType initial) state env (log round).2
            (matchedState initial state env (log round).2 (prefixAt (round + 1)).residual) ∧
          relationMembership (buildRelationSet initial (compileType initial))
            (prefixAt (round + 1)).residual
            (matchedState initial state env (log round).2
              (prefixAt (round + 1)).residual) := by
        rw [matchedState, dif_pos hExists]
        exact hExists.choose_spec
      have hChoiceNext : (gameChoice gameStrategy log prefixAt (round + 1)).base =
          .choice (matchedState initial state env (log round).2
            (prefixAt (round + 1)).residual) (honestyNext env (log round).2) := by
        simp only [gameChoice, matchingTargetVertex, hResolveBase,
          CompatibilityVertex.stateOf, CompatibilityVertex.env]
      have hEdgeResolve : monitoredEdge initial progress
          (gamePlay gameStrategy log prefixAt (2 * round + 1))
          (gamePlay gameStrategy log prefixAt (2 * round + 1 + 1)) := by
        rw [gamePlay_odd, show 2 * round + 1 + 1 = 2 * (round + 1) from by omega,
          gamePlay_even, gameChoice]
        refine matchingTargetVertex_edge hResolveBase (by rw [hEnv]; exact hAdm) ?_
        simp only [hResolveBase, CompatibilityVertex.stateOf, CompatibilityVertex.env]
        exact hMatchedSpec.1
      obtain ⟨⟨envNext, hResolveNext⟩, hEdgeAtNext⟩ := gameResolve_edge hLegal hChoiceNext
      have hEdgesNext : ∀ n, n < 2 * (round + 1) + 1 → monitoredEdge initial progress
          (gamePlay gameStrategy log prefixAt n)
          (gamePlay gameStrategy log prefixAt (n + 1)) := by
        intro n hn
        rcases Nat.lt_or_ge n (2 * round + 1) with hLt | hGe
        · exact hEdges n hLt
        · rcases Nat.eq_or_lt_of_le hGe with hEq | hGt
          · rw [← hEq]; exact hEdgeResolve
          · have hn2 : n = 2 * (round + 1) := by omega
            subst hn2
            rw [gamePlay_even, show 2 * (round + 1) + 1 = 2 * (round + 1) + 1 from rfl,
              gamePlay_odd]
            exact hEdgeAtNext
      have hMovesNext : ∀ n, n < 2 * (round + 1) + 1 →
          (gamePlay gameStrategy log prefixAt n).base.isPlayerZero →
          gamePlay gameStrategy log prefixAt (n + 1) =
            gameStrategy ((List.range (n + 1)).map
              (gamePlay gameStrategy log prefixAt)) := by
        intro n hn hZero
        rcases Nat.lt_or_ge n (2 * round + 1) with hLt | hGe
        · exact hMoves n hLt hZero
        · rcases Nat.eq_or_lt_of_le hGe with hEq | hGt
          · exfalso
            rw [← hEq, gamePlay_odd, hResolveBase] at hZero
            exact absurd hZero (by simp [CompatibilityVertex.isPlayerZero])
          · have hn2 : n = 2 * (round + 1) := by omega
            subst hn2
            exact gamePlay_move gameStrategy log prefixAt (round + 1)
      have hAdmNext : (honestyNext env (log round).2).Admissible
          (strategyOfGame gameStrategy (prefixAt (round + 1)).entries) := by
        by_contra hNotAdm
        have hEnvNext : envNext =
            strategyOfGame gameStrategy (prefixAt (round + 1)).entries := by
          have hE := gameResolve_env (bound := bound) hRoot hSteps hLe
          rw [hResolveNext] at hE
          exact hE
        have hCut : (gamePlay gameStrategy log prefixAt (2 * (round + 1) + 1)).base =
            .resolve (matchedState initial state env (log round).2
              (prefixAt (round + 1)).residual) (honestyNext env (log round).2) envNext := by
          rw [gamePlay_odd]; exact hResolveNext
        have hFail : compatibilityEdge (compileType initial) initial.alphabet
            (gamePlay gameStrategy log prefixAt (2 * (round + 1) + 1)).base .fail := by
          rw [hCut]
          exact Or.inl (by rw [hEnvNext]; exact hNotAdm)
        have hEntryFail : compatibilityStepEntry (compileType initial)
            (gamePlay gameStrategy log prefixAt (2 * (round + 1) + 1)).base .fail
            (some (failEntry
              (gamePlay gameStrategy log prefixAt (2 * (round + 1) + 1)).base)) := by
          rw [hCut]; rfl
        have hNotZero : ¬ (gamePlay gameStrategy log prefixAt
            (2 * (round + 1) + 1)).base.isPlayerZero := by
          rw [hCut]; simp [CompatibilityVertex.isPlayerZero]
        obtain ⟨hZeroAbort, hConsistentAbort, hPathAbort, hSinkAbort⟩ :=
          abortPlay_consistent (gameStrategy := gameStrategy)
            (play := gamePlay gameStrategy log prefixAt) (cut := 2 * (round + 1) + 1)
            hRootPlay (fun n hn => hEdgesNext n hn) (fun n hn => hMovesNext n hn)
            hNotZero hFail hEntryFail
        exact absurd (hWins _ hZeroAbort hConsistentAbort)
          (hPathAbort.sink_not_accepts hSinkAbort)
      exact ⟨⟨_, _, hChoiceNext, hMatchedSpec.2, hAdmNext⟩, hEdgesNext, hMovesNext⟩

/-- Helper Lemma H20, the `sigma_0 ↦ S_Θ` direction: every completed log of the
semantic strategy read off a winning `sigma_0` is the log of a play `sigma_0`
generates from `s_0`. -/
theorem helper_h20_play_to_strategy (hWF : TypeWellFormedIn [] initial)
    {progress : Finset ProcId}
    {gameStrategy : (compatibilityGame initial progress).Strategy}
    (hLegal : (compatibilityGame initial progress).Legal gameStrategy)
    (hWins : ∀ play, play 0 = (compatibilityGame initial progress).initial →
      (compatibilityGame initial progress).Consistent gameStrategy play →
      RabinGame.Accepts (compatibilityGame initial progress) play)
    {log : TypeLog}
    (hCompleted : CompletedTypeLog initial (strategyOfGame gameStrategy) log) :
    ∃ play, play 0 = (compatibilityGame initial progress).initial ∧
      (compatibilityGame initial progress).Consistent gameStrategy play ∧
      CompatibilityPath play ∧ compatibilityPlayLog play = log := by
  obtain ⟨prefixAt, hRoot, hRun⟩ := hCompleted
  have hRootPlay : gamePlay gameStrategy log prefixAt 0 =
      monitoredInitial initial progress := by
    rw [show (0 : ℕ) = 2 * 0 from rfl, gamePlay_even]; rfl
  rcases hRun with hAll | ⟨stop, hBefore, hStuck, hLogStop, hTail⟩
  · refine ⟨gamePlay gameStrategy log prefixAt, hRootPlay, ?_, ?_, ?_⟩
    · intro n
      obtain ⟨-, hEdges, hMoves⟩ :=
        gameMatch hWF hLegal hWins hRoot (bound := n) (fun m _ => hAll m) n (Nat.le_refl n)
      exact ⟨hEdges n (by omega), hMoves n (by omega)⟩
    · refine ⟨hRootPlay, fun n => ?_⟩
      obtain ⟨-, hEdges, -⟩ :=
        gameMatch hWF hLegal hWins hRoot (bound := n) (fun m _ => hAll m) n (Nat.le_refl n)
      exact hEdges n (by omega)
    · funext round
      obtain ⟨⟨state, memory, hChoice, -, -⟩, -, -⟩ :=
        gameMatch hWF hLegal hWins hRoot (bound := round) (fun m _ => hAll m) round
          (Nat.le_refl round)
      obtain ⟨⟨env, hResolveBase⟩, -⟩ := gameResolve_edge hLegal hChoice
      have hEnv : env = strategyOfGame gameStrategy (prefixAt round).entries := by
        have hE := gameResolve_env (bound := round) hRoot (fun m _ => hAll m)
          (Nat.le_refl round)
        rw [hResolveBase] at hE
        exact hE
      have hEntry : (gamePlay gameStrategy log prefixAt (2 * round + 2)).entry =
          some (env, (log round).2) := by
        rw [show 2 * round + 2 = 2 * (round + 1) from by omega, gamePlay_even, gameChoice]
        simp only [matchingTargetVertex, hResolveBase, CompatibilityVertex.env]
      simp only [compatibilityPlayLog, hEntry, Option.getD_some, hEnv, ← (hAll round).1]
  · exfalso
    obtain ⟨⟨state, memory, hChoice, hRelated, -⟩, hEdges, hMoves⟩ :=
      gameMatch hWF hLegal hWins hRoot (bound := stop) hBefore stop (Nat.le_refl stop)
    obtain ⟨⟨env, hResolveBase⟩, -⟩ := gameResolve_edge hLegal hChoice
    have hEnv : env = strategyOfGame gameStrategy (prefixAt stop).entries := by
      have hE := gameResolve_env (bound := stop) hRoot hBefore (Nat.le_refl stop)
      rw [hResolveBase] at hE
      exact hE
    have hNoEdge : ¬ ∃ label target,
        compiledTypeEdge (compileType initial) state env label target := by
      rintro ⟨label, target, offers, hHasEdge⟩
      obtain ⟨residual', hDecorated, -⟩ :=
        (correspondence_steps initial (admissibleType_of_typeWellFormedIn_nil hWF)).2
          hRelated hHasEdge
      exact hStuck ⟨label, residual', by rw [← hEnv]; exact hDecorated.1⟩
    have hCut : (gamePlay gameStrategy log prefixAt (2 * stop + 1)).base =
        .resolve state memory env := by rw [gamePlay_odd]; exact hResolveBase
    have hFail : compatibilityEdge (compileType initial) initial.alphabet
        (gamePlay gameStrategy log prefixAt (2 * stop + 1)).base .fail := by
      rw [hCut]; exact Or.inr hNoEdge
    have hEntryFail : compatibilityStepEntry (compileType initial)
        (gamePlay gameStrategy log prefixAt (2 * stop + 1)).base .fail
        (some (failEntry (gamePlay gameStrategy log prefixAt (2 * stop + 1)).base)) := by
      rw [hCut]; rfl
    have hNotZero : ¬ (gamePlay gameStrategy log prefixAt
        (2 * stop + 1)).base.isPlayerZero := by
      rw [hCut]; simp [CompatibilityVertex.isPlayerZero]
    obtain ⟨hZeroAbort, hConsistentAbort, hPathAbort, hSinkAbort⟩ :=
      abortPlay_consistent (gameStrategy := gameStrategy)
        (play := gamePlay gameStrategy log prefixAt) (cut := 2 * stop + 1)
        hRootPlay (fun n hn => hEdges n hn) (fun n hn => hMoves n hn)
        hNotZero hFail hEntryFail
    exact absurd (hWins _ hZeroAbort hConsistentAbort)
      (hPathAbort.sink_not_accepts hSinkAbort)

/-- Theorem 4.2, forward direction: a winning Player-0 strategy yields a
winning semantic strategy. -/
theorem game_reduction_forward (hWF : TypeWellFormedIn [] initial)
    {progress : Finset ProcId}
    (hCompatible : TypeCompatible initial progress) :
    SemanticTypeCompatible initial progress := by
  obtain ⟨gameStrategy, hLegal, hWins⟩ := hCompatible
  refine ⟨strategyOfGame gameStrategy, fun log hCompleted => ?_⟩
  obtain ⟨play, hRoot, hConsistent, hPath, hLogEq⟩ :=
    helper_h20_play_to_strategy hWF hLegal hWins hCompleted
  rw [← hLogEq]
  exact (helper_h18_objective_monitor initial progress play hPath).mp
    (hWins play hRoot hConsistent)

end

end Pact
