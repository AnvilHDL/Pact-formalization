import Anvilpp.ProofHelpers.WeakRefinementParallel
import Anvilpp.ProofHelpers.WeakRefinementComparison
import Anvilpp.ProofHelpers.ObjectiveRegularity

namespace Pact

noncomputable section

open Classical

namespace WeakRefinement

/-- A type with a leading skip. -/
def skipPrefix (source : PactType) : PactType :=
  .seq source.alphabet (.skip source.alphabet) source

/-- A leading skip leaves the optimistic future menu unchanged. -/
@[simp] theorem typeFutureOffers_skipPrefix (source : PactType) :
    typeFutureOffers (skipPrefix source) = typeFutureOffers source := by
  simp [skipPrefix, typeFutureOffers_sequence]

/-- The forced skip round offers nothing now and advertises the continuation's entire menu. -/
theorem skipPrefix_offers_iff {source target : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage} :
    TypeOffers env (skipPrefix source) label target current future ↔
      env.WellFormed source.alphabet ∧ env.clock = false ∧
      label = TypeLabel.silent ∧ target = source ∧
      current = ∅ ∧ future = typeFutureOffers source := by
  constructor
  · intro hOffers
    cases hOffers with
    | seq _ _ _ _ _ _ _ _ hChild hNotSkip _ =>
        cases hChild
        exact (hNotSkip rfl).elim
    | seq_tock _ _ _ _ _ _ _ hChild _ => cases hChild
    | seq_fuse _ _ _ _ _ _ _ _ hChild _ =>
        cases hChild with
        | skip _ _ hPrem => simpa [sequenceRightMenu] using hPrem
    | seq_fuse_tock _ _ _ _ _ _ _ hChild => cases hChild
  · rintro ⟨hWF, hClock, hLabel, hTarget, hCurrent, hFuture⟩
    subst label target current future
    simpa [skipPrefix, sequenceRightMenu] using
      TypeOffers.seq_fuse env source.alphabet source.alphabet (.skip source.alphabet)
        source TypeLabel.silent ∅ (typeFutureOffers (.skip source.alphabet))
        (.skip _ _ ⟨hWF, hClock⟩) (by simp [TypeLabel.silent])

/-- Use the supplied initial environment, then run the strategy on the tail history. -/
def skipPrefixStrategy (env : TypeEnvironment) (strategy : TypeStrategy) : TypeStrategy :=
  fun entries => if entries = [] then env else strategy entries.tail

private theorem prefix_nil_residual {initial residual : PactType}
    (hValid : TypePrefixValid initial [] residual) : residual = initial := by
  generalize hEntries : [] = entries at hValid
  cases hValid with
  | root => rfl
  | step => simp at hEntries

private theorem skipPrefix_tail_valid {source residual : PactType} {entries : TypeHistory}
    (hValid : TypePrefixValid (skipPrefix source) entries residual)
    (hNonempty : entries ≠ []) :
    TypePrefixValid source entries.tail residual := by
  induction hValid with
  | root => exact (hNonempty rfl).elim
  | @step entries current next env label hValid hStep ih =>
      cases entries with
      | nil =>
          have hCurrent := prefix_nil_residual hValid
          subst current
          have hTarget := (skip_prefix_transition_iff.mp hStep).2.2.2
          subst next
          exact .root
      | cons entry entries =>
          simpa using (ih (by simp)).step hStep

private def skipPrefixTail {source : PactType} (history : TypePrefix (skipPrefix source)) :
    TypePrefix source :=
  if h : history.entries = [] then ⟨[], source, .root⟩
  else ⟨history.entries.tail, history.residual, skipPrefix_tail_valid history.valid h⟩

private theorem skipPrefixTail_entries {source : PactType}
    (history : TypePrefix (skipPrefix source)) (h : history.entries ≠ []) :
    (skipPrefixTail history).entries = history.entries.tail := by
  simp [skipPrefixTail, h]

private theorem skipPrefixTail_residual {source : PactType}
    (history : TypePrefix (skipPrefix source)) (h : history.entries ≠ []) :
    (skipPrefixTail history).residual = history.residual := by
  simp [skipPrefixTail, h]

private theorem skipPrefixTail_follows {source : PactType} {env : TypeEnvironment}
    {strategy : TypeStrategy} {history : TypePrefix (skipPrefix source)}
    (hFollows : FollowsTypeStrategy (skipPrefix source)
      (skipPrefixStrategy env strategy) history) :
    FollowsTypeStrategy source strategy (skipPrefixTail history) := by
  induction hFollows with
  | root => simpa [skipPrefixTail] using (FollowsTypeStrategy.root (initial := source)
      (strategy := strategy))
  | @step history label next hFollows hStep ih =>
      by_cases hEntries : history.entries = []
      · have hCurrent := prefix_nil_residual (hEntries ▸ history.valid)
        have hTarget := (skip_prefix_transition_iff.mp (hCurrent ▸ hStep)).2.2.2
        subst next
        simpa [skipPrefixTail, hEntries] using
          (FollowsTypeStrategy.root (initial := source) (strategy := strategy))
      · have hTailStep : TypeTransition (strategy (skipPrefixTail history).entries)
            (skipPrefixTail history).residual label next := by
          simpa [skipPrefixStrategy, skipPrefixTail, hEntries] using hStep
        have hTailAppend (entry : TypeEnvironment × TypeLabel × PactType) :
            (history.entries ++ [entry]).tail = history.entries.tail ++ [entry] := by
          obtain ⟨head, tail, hCons⟩ := List.exists_cons_of_ne_nil hEntries
          rw [hCons]
          rfl
        simpa [skipPrefixTail, skipPrefixStrategy, hEntries, hTailAppend]
          using ih.step hTailStep

/-- The leading-skip strategy preserves admissibility at every generated prefix. -/
theorem skipPrefixStrategy_wellFormed {source : PactType} {env : TypeEnvironment}
    {strategy : TypeStrategy} (hFirst : env.WellFormed source.alphabet)
    (hStrategy : WellFormedTypeStrategy source strategy) :
    WellFormedTypeStrategy (skipPrefix source) (skipPrefixStrategy env strategy) := by
  intro history hFollows
  by_cases hEmpty : history.entries = []
  · simpa [skipPrefixStrategy, hEmpty, skipPrefix, PactType.alphabet] using hFirst
  · simpa [skipPrefixStrategy, skipPrefixTail, hEmpty, skipPrefix, PactType.alphabet] using
      hStrategy (skipPrefixTail history) (skipPrefixTail_follows hFollows)

private theorem ordinary_entries_length {initial : PactType} {strategy : TypeStrategy}
    {log : TypeLog} {prefixAt : Nat → TypePrefix initial}
    (hRoot : prefixAt 0 = ⟨[], initial, .root⟩) {bound : Nat}
    (hSteps : ∀ n, n < bound → OrdinaryTypeStep initial strategy log prefixAt n) :
    (prefixAt bound).entries.length = bound := by
  induction bound with
  | zero => simp [hRoot]
  | succ bound ih =>
      have hLength := ih (fun n hn => hSteps n (by omega))
      rw [← (hSteps bound (by omega)).2.1, List.length_append, hLength]
      rfl

/-- Removing the forced first round yields a completed execution of the original strategy. -/
theorem completedTypeLog_skipPrefix_tail {source : PactType} {env : TypeEnvironment}
    {strategy : TypeStrategy} {log : TypeLog}
    (hWF : env.WellFormed source.alphabet) (hClock : env.clock = false)
    (hCompleted : CompletedTypeLog (skipPrefix source)
      (skipPrefixStrategy env strategy) log) :
    log 0 = (env, TypeLabel.silent) ∧
      (log 1).1 = strategy [] ∧
      CompletedTypeLog source strategy (fun n => log (n + 1)) := by
  obtain ⟨prefixAt, hRoot, hRun⟩ := hCompleted
  have hReady : TypeReady env (skipPrefix source) :=
    ⟨_, _, skip_prefix_transition_iff.mpr ⟨hWF, hClock, rfl, rfl⟩⟩
  have hFirst : OrdinaryTypeStep (skipPrefix source)
      (skipPrefixStrategy env strategy) log prefixAt 0 := by
    rcases hRun with hAll | ⟨stop, hBefore, hStuck, _, _⟩
    · exact hAll 0
    · have hPositive : 0 < stop := by
        by_contra h
        have : stop = 0 := by omega
        subst stop
        exact hStuck (by simpa [hRoot, skipPrefixStrategy] using hReady)
      exact hBefore 0 hPositive
  have hFirstEnv : (log 0).1 = env := by
    simpa [hRoot, skipPrefixStrategy] using hFirst.1
  have hFirstStep := hFirst.2.2
  rw [hRoot] at hFirstStep
  obtain ⟨_, _, hFirstLabel, hFirstTarget⟩ := skip_prefix_transition_iff.mp hFirstStep
  have hEntriesOne : (prefixAt 1).entries = [(env, TypeLabel.silent, source)] := by
    simpa [hRoot, hFirstEnv, hFirstLabel, hFirstTarget] using hFirst.2.1.symm
  have hTailRoot : skipPrefixTail (prefixAt 1) = ⟨[], source, .root⟩ := by
    simp [skipPrefixTail, hEntriesOne, hFirstTarget]
  have hNonempty (n : Nat)
      (hBefore : ∀ k, k < n + 1 →
        OrdinaryTypeStep (skipPrefix source) (skipPrefixStrategy env strategy) log prefixAt k) :
      (prefixAt (n + 1)).entries ≠ [] := by
    have hLength := ordinary_entries_length hRoot hBefore
    intro hEmpty
    simp [hEmpty] at hLength
  have hOrdinary (n : Nat) (hNe : (prefixAt (n + 1)).entries ≠ [])
      (hStep : OrdinaryTypeStep (skipPrefix source)
        (skipPrefixStrategy env strategy) log prefixAt (n + 1)) :
      OrdinaryTypeStep source strategy (fun n => log (n + 1))
        (fun n => skipPrefixTail (prefixAt (n + 1))) n := by
    have hNextNe : (prefixAt (n + 1 + 1)).entries ≠ [] := by
      rw [← hStep.2.1]
      simp
    refine ⟨?_, ?_, ?_⟩
    · simpa [skipPrefixStrategy, hNe, skipPrefixTail] using hStep.1
    · rw [skipPrefixTail_entries _ hNe, skipPrefixTail_entries _ hNextNe,
        skipPrefixTail_residual _ hNextNe, ← hStep.2.1]
      cases hEntries : (prefixAt (n + 1)).entries with
      | nil => exact (hNe hEntries).elim
      | cons entry entries => rfl
    · simpa only [skipPrefixTail_residual _ hNe, skipPrefixTail_residual _ hNextNe]
        using hStep.2.2
  have hCompletedTail : CompletedTypeLog source strategy (fun n => log (n + 1)) := by
    refine ⟨fun n => skipPrefixTail (prefixAt (n + 1)), hTailRoot, ?_⟩
    rcases hRun with hAll | ⟨stop, hBefore, hStuck, hAtStop, hAfter⟩
    · exact Or.inl fun n => hOrdinary n (hNonempty n (fun k _ => hAll k)) (hAll _)
    · have hPositive : 0 < stop := by
        by_contra h
        have : stop = 0 := by omega
        subst stop
        exact hStuck (by simpa [hRoot, skipPrefixStrategy] using hReady)
      have hStop : stop - 1 + 1 = stop := by omega
      have hStopNe : (prefixAt stop).entries ≠ [] := by
        simpa only [hStop] using hNonempty (stop - 1) (by simpa only [hStop] using hBefore)
      refine Or.inr ⟨stop - 1, ?_, ?_, ?_, ?_⟩
      · intro n hn
        exact hOrdinary n (hNonempty n (fun k hk => hBefore k (by omega)))
          (hBefore (n + 1) (by omega))
      · simpa [hStop, skipPrefixStrategy, skipPrefixTail, hStopNe] using hStuck
      · simpa [hStop, skipPrefixStrategy, skipPrefixTail, hStopNe] using hAtStop
      · intro n hn
        exact hAfter (n + 1) (by omega)
  have hSecondEnv : (log 1).1 = strategy [] := by
    obtain ⟨tailPrefix, hTailRoot, hTailRun⟩ := hCompletedTail
    rcases hTailRun with hAll | ⟨stop, hBefore, _, hStop, _⟩
    · simpa [hTailRoot] using (hAll 0).1
    · cases stop with
      | zero => simpa [hTailRoot] using congrArg Prod.fst hStop
      | succ stop => simpa [hTailRoot] using (hBefore 0 (by omega)).1
  exact ⟨Prod.ext hFirstEnv hFirstLabel, hSecondEnv, hCompletedTail⟩

/-- Every admissible honest strategy admits a clock-aligned leading-skip implementation. -/
theorem honestBlockRefinement_skipPrefix (source : PactType) :
    HonestBlockRefinement (skipPrefix source) source := by
  refine ⟨rfl, by simp [skipPrefix, typeFairIds],
    by simp [skipPrefix, PactType.ProgressIds], ?_⟩
  intro strategy hAdmissible hHonest
  have hWF := hAdmissible _ FollowsTypeStrategy.root
  let first : TypeEnvironment := { strategy [] with clock := false }
  have hFirstWF : first.WellFormed source.alphabet := by
    refine ⟨by simp [first], ?_, hWF.2.2.1, hWF.2.2.2⟩
    intro _
    cases hClock : (strategy []).clock with
    | false => exact hWF.2.1 hClock
    | true => simp [first, (hWF.1 hClock).1, (hWF.1 hClock).2]
  refine ⟨skipPrefixStrategy first strategy,
    skipPrefixStrategy_wellFormed hFirstWF hAdmissible, ?_, ?_⟩
  · intro log hCompleted
    obtain ⟨hFirst, hSecond, hTail⟩ :=
      completedTypeLog_skipPrefix_tail hFirstWF rfl hCompleted
    intro index
    cases index with
    | zero =>
        right
        rw [hFirst, hSecond, TypeEnvironment.honestyRemainder_silent]
        exact Finset.subset_of_eq (Finset.union_comm _ _)
    | succ index => exact hHonest _ hTail index
  · intro log hCompleted
    obtain ⟨hFirst, _, hTail⟩ :=
      completedTypeLog_skipPrefix_tail hFirstWF rfl hCompleted
    exact ⟨fun n => log (n + 1), hTail,
      ⟨TypeLogClockBlockMatch.silentHead (congrArg Prod.snd hFirst)⟩⟩

private theorem objective_of_tail {initial : PactType} {progress : Finset ProcId}
    {log : TypeLog} (hBoundary : (log 0).2.isTock ∨
      typeAvailable (log 1).1 ⊆ (log 0).1.honestyRemainder (log 0).2)
    (hWinning : TypeWinningObjective initial progress (fun n => log (n + 1))) :
    TypeWinningObjective initial progress log := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hBoundary
    | succ n => exact hWinning.1 n
  · exact (LogMonitor.infinite_succ_iff _).mp hWinning.2.1
  · intro hFair pid hPid
    apply (LogMonitor.infinite_succ_iff _).mp
    apply hWinning.2.2 _ pid hPid
    intro bid hBid
    exact (LogMonitor.infinite_succ_iff _).trans
      ((hFair bid hBid).trans (LogMonitor.infinite_succ_iff _).symm)

/-- A leading skip preserves semantic compatibility, including clock-first continuations. -/
theorem semantic_compatible_skipPrefix {source : PactType} {progress : Finset ProcId}
    (hAlphabet : source.AlphabetWellFormed)
    (hCompatible : SemanticTypeCompatible source progress) :
    SemanticTypeCompatible (skipPrefix source) progress := by
  obtain ⟨strategy, hWins⟩ := hCompatible
  have hReady := strategy_ready hWins FollowsTypeStrategy.root
  obtain ⟨label, target, hStep⟩ := hReady
  obtain ⟨offers, hOffers⟩ := hStep.exists_decorated
  have hWF : (strategy []).WellFormed source.alphabet :=
    hOffers.2.env_wellFormed hAlphabet
  let first : TypeEnvironment := { strategy [] with clock := false }
  have hFirstWF : first.WellFormed source.alphabet := by
    refine ⟨by simp [first], ?_, hWF.2.2.1, hWF.2.2.2⟩
    intro _
    cases hClock : (strategy []).clock with
    | false => exact hWF.2.1 hClock
    | true => simp [first, (hWF.1 hClock).1, (hWF.1 hClock).2]
  refine ⟨skipPrefixStrategy first strategy, fun log hCompleted => ?_⟩
  obtain ⟨hFirst, hSecond, hTail⟩ :=
    completedTypeLog_skipPrefix_tail hFirstWF rfl hCompleted
  have hTailWins := hWins _ hTail
  have hTailWins' : TypeWinningObjective (skipPrefix source) progress
      (fun n => log (n + 1)) := by
    simpa [TypeWinningObjective, FairTypeLog, typeFairIds, skipPrefix] using hTailWins
  apply objective_of_tail (log := log) _ hTailWins'
  right
  rw [hFirst, hSecond, TypeEnvironment.honestyRemainder_silent]
  exact Finset.subset_of_eq (Finset.union_comm _ _)

private def prependLog (env : TypeEnvironment) (label : TypeLabel) (log : TypeLog) : TypeLog
  | 0 => (env, label)
  | n + 1 => log n

private theorem prepend_valid {initial source residual : PactType} {env : TypeEnvironment}
    {label : TypeLabel} {entries : TypeHistory} (hStep : TypeTransition env initial label source)
    (hValid : TypePrefixValid source entries residual) :
    TypePrefixValid initial ((env, label, source) :: entries) residual := by
  induction hValid with
  | root => exact TypePrefixValid.root.step hStep
  | step _ hNext ih => simpa using ih.step hNext

private def prependPrefix {initial source : PactType} {env : TypeEnvironment}
    {label : TypeLabel} (hStep : TypeTransition env initial label source)
    (history : TypePrefix source) : TypePrefix initial :=
  ⟨(env, label, source) :: history.entries, history.residual,
    prepend_valid hStep history.valid⟩

/-- A completed continuation can be prefixed by a strategy's first step. -/
theorem completedTypeLog_prepend {initial source : PactType} {strategy : TypeStrategy}
    {label : TypeLabel} {log : TypeLog}
    (hStep : TypeTransition (strategy []) initial label source)
    (hCompleted : CompletedTypeLog source
      (fun entries => strategy ((strategy [], label, source) :: entries)) log) :
    CompletedTypeLog initial strategy (prependLog (strategy []) label log) := by
  obtain ⟨prefixAt, hRoot, hRun⟩ := hCompleted
  let lifted : Nat → TypePrefix initial
    | 0 => ⟨[], initial, .root⟩
    | n + 1 => prependPrefix hStep (prefixAt n)
  have hFirst : OrdinaryTypeStep initial strategy
      (prependLog (strategy []) label log) lifted 0 := by
    simpa [OrdinaryTypeStep, prependLog, lifted, prependPrefix, hRoot] using hStep
  have hOrdinary (n : Nat)
      (hOrdinary : OrdinaryTypeStep source
        (fun entries => strategy ((strategy [], label, source) :: entries)) log prefixAt n) :
      OrdinaryTypeStep initial strategy
        (prependLog (strategy []) label log) lifted (n + 1) := by
    refine ⟨hOrdinary.1, ?_, hOrdinary.2.2⟩
    simpa only [List.cons_append, prependLog, lifted, prependPrefix] using
      congrArg (List.cons (strategy [], label, source)) hOrdinary.2.1
  refine ⟨lifted, rfl, ?_⟩
  rcases hRun with hAll | ⟨stop, hBefore, hStuck, hAtStop, hAfter⟩
  · refine Or.inl fun n => ?_
    cases n with
    | zero => exact hFirst
    | succ n => exact hOrdinary n (hAll n)
  · refine Or.inr ⟨stop + 1, ?_, hStuck, hAtStop, ?_⟩
    · intro n hn
      cases n with
      | zero => exact hFirst
      | succ n => exact hOrdinary n (hBefore n (by omega))
    · intro n hn
      cases n with
      | zero => omega
      | succ n => exact hAfter n (by omega)

private theorem objective_tail {initial : PactType} {progress : Finset ProcId}
    {log : TypeLog} (hWinning : TypeWinningObjective initial progress log) :
    TypeWinningObjective initial progress (fun n => log (n + 1)) := by
  refine ⟨fun n => hWinning.1 (n + 1),
    (LogMonitor.infinite_succ_iff _).mpr hWinning.2.1, ?_⟩
  intro hFair pid hPid
  apply (LogMonitor.infinite_succ_iff (fun n => (log n).2.contains (.progress pid))).mpr
  apply hWinning.2.2 _ pid hPid
  intro bid hBid
  exact (LogMonitor.infinite_succ_iff (fun n => (log n).2.contains (.fair bid true))).symm.trans
    ((hFair bid hBid).trans
      (LogMonitor.infinite_succ_iff (fun n => (log n).2.contains (.fair bid false))))

/-- A winning strategy for a leading skip restricts to a winning continuation strategy. -/
theorem semantic_compatible_of_skipPrefix {source : PactType} {progress : Finset ProcId}
    (hCompatible : SemanticTypeCompatible (skipPrefix source) progress) :
    SemanticTypeCompatible source progress := by
  obtain ⟨strategy, hWins⟩ := hCompatible
  obtain ⟨label, target, hStep⟩ := strategy_ready hWins FollowsTypeStrategy.root
  obtain ⟨_, _, hLabel, hTarget⟩ := skip_prefix_transition_iff.mp hStep
  subst label target
  refine ⟨fun entries => strategy ((strategy [], TypeLabel.silent, source) :: entries),
    fun log hCompleted => ?_⟩
  have hLifted := hWins _ (completedTypeLog_prepend hStep hCompleted)
  have hTail := objective_tail hLifted
  simpa [TypeWinningObjective, FairTypeLog, typeFairIds, skipPrefix, prependLog] using hTail

/-- Adding or removing a leading skip preserves semantic compatibility. -/
theorem semantic_compatible_skipPrefix_iff {source : PactType} {progress : Finset ProcId}
    (hAlphabet : source.AlphabetWellFormed) :
    SemanticTypeCompatible (skipPrefix source) progress ↔
      SemanticTypeCompatible source progress :=
  ⟨semantic_compatible_of_skipPrefix, semantic_compatible_skipPrefix hAlphabet⟩

/-- A leading skip preserves all type well-formedness conditions. -/
theorem skipPrefix_wellFormed {bound : List String} {source : PactType}
    (hWF : TypeWellFormedIn bound source) : TypeWellFormedIn bound (skipPrefix source) := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO, hMenu⟩ := hWF
  have hAlphabet := hA.alphabet_wellFormed
  simp only [TypeWellFormedIn, skipPrefix, PactType.AlphabetWellFormed,
    PactType.alphabet, PactType.AllVariablesBound, PactType.BinderHygienic,
    PactType.TailClosed, PactType.TailOccurrences, PactType.ClockGuarded,
    PactType.TailRecursive, PactType.SameCycleMessageLinear, PactType.SuffixMessageIds,
    PactType.ProgressLinear, PactType.ProgressIds, PactType.FairChoiceLinear,
    PactType.FairChoiceIds, PactType.ParallelMessageOwnership,
    PactType.ParallelProgressOwnership, PactType.ParallelFairChoiceOwnership,
    PactType.InterfaceScoped, PactType.InterfaceAlphabetScoped, PactType.ParallelInterfaces,
    PactType.ConjunctiveMessageOwnership, OfferMenuLinear]
  simp_all [PactType.TailClosed]
  change source.alphabet.WellFormed ∧ Disjoint source.alphabet.messageIds source.ParallelInterfaces
  refine ⟨hAlphabet, Finset.disjoint_left.mpr ?_⟩
  intro msg hMsg hInterface
  obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp hMsg
  exact hIAS.avoids action hAction hInterface

/-- Leading skip elimination preserves the automaton-game compatibility judgment. -/
theorem compatible_skipPrefix_iff {source : PactType} {progress : Finset ProcId}
    (hWF : TypeWellFormedIn [] source) :
    TypeCompatible (skipPrefix source) progress ↔ TypeCompatible source progress := by
  have hSkipWF := skipPrefix_wellFormed hWF
  constructor
  · intro hCompatible
    exact game_reduction_backward hWF
      (semantic_compatible_of_skipPrefix (game_reduction_forward hSkipWF hCompatible))
  · intro hCompatible
    exact game_reduction_backward hSkipWF
      (semantic_compatible_skipPrefix hWF.1 (game_reduction_forward hWF hCompatible))

end WeakRefinement

end

end Pact
