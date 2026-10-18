import Anvilpp.Examples.WeakRefinementComparison

namespace Pact

noncomputable section

open Classical

/-- The rounds preceding an optional failure index. -/
def BeforeTypeFailure (stop : Option Nat) (index : Nat) : Prop :=
  ∀ failure, stop = some failure → index < failure

/-- A completed execution retains its residuals, actual offers, and failure index. -/
structure CompletedTypeExecution (initial : PactType) (strategy : TypeStrategy)
    (log : TypeLog) where
  prefixAt : Nat → TypePrefix initial
  stop : Option Nat
  current : Nat → Finset BareMessage
  future : Nat → Finset BareMessage
  root : prefixAt 0 = ⟨[], initial, .root⟩
  ordinary : ∀ n, BeforeTypeFailure stop n →
    OrdinaryTypeStep initial strategy log prefixAt n
  offers : ∀ n, BeforeTypeFailure stop n →
    TypeOffers (log n).1 (prefixAt n).residual (log n).2
      (prefixAt (n + 1)).residual (current n) (future n)
  failure : ∀ n, stop = some n →
    (¬ TypeReady (strategy (prefixAt n).entries) (prefixAt n).residual) ∧
    log n = (strategy (prefixAt n).entries, TypeLabel.silent) ∧
    ∀ m, n < m → log m = (TypeEnvironment.empty, TypeLabel.silent)
  frozen : ∀ n, stop = some n → ∀ m, n ≤ m → prefixAt m = prefixAt n
  noOffers : ∀ n, ¬ BeforeTypeFailure stop n → current n = ∅ ∧ future n = ∅

namespace CompletedTypeExecution

/-- Forgetting decorations and the frozen failure tail gives a completed log. -/
theorem completed {initial : PactType} {strategy : TypeStrategy} {log : TypeLog}
    (run : CompletedTypeExecution initial strategy log) :
    CompletedTypeLog initial strategy log := by
  refine ⟨run.prefixAt, run.root, ?_⟩
  cases hStop : run.stop with
  | none => exact Or.inl fun n => run.ordinary n (by simp [BeforeTypeFailure, hStop])
  | some stop =>
      obtain ⟨hStuck, hAt, hAfter⟩ := run.failure stop hStop
      exact Or.inr ⟨stop, fun n hn => run.ordinary n
        (by simpa [BeforeTypeFailure, hStop] using hn), hStuck, hAt, hAfter⟩

/-- Every completed log has decorations and a residual frozen at failure. -/
theorem exists_of_completed {initial : PactType} {strategy : TypeStrategy} {log : TypeLog}
    (hCompleted : CompletedTypeLog initial strategy log) :
    Nonempty (CompletedTypeExecution initial strategy log) := by
  obtain ⟨prefixAt, hRoot, hRun⟩ := hCompleted
  have decorate (prefixAt : Nat → TypePrefix initial) (stop : Option Nat)
      (hSteps : ∀ n, BeforeTypeFailure stop n →
        OrdinaryTypeStep initial strategy log prefixAt n) :
      ∃ current future : Nat → Finset BareMessage,
        (∀ n, BeforeTypeFailure stop n →
          TypeOffers (log n).1 (prefixAt n).residual (log n).2
            (prefixAt (n + 1)).residual (current n) (future n)) ∧
        (∀ n, ¬ BeforeTypeFailure stop n → current n = ∅ ∧ future n = ∅) := by
    have hExists (n : Nat) : ∃ pair : Finset BareMessage × Finset BareMessage,
        (BeforeTypeFailure stop n →
          TypeOffers (log n).1 (prefixAt n).residual (log n).2
            (prefixAt (n + 1)).residual pair.1 pair.2) ∧
        (¬ BeforeTypeFailure stop n → pair = (∅, ∅)) := by
      by_cases hActive : BeforeTypeFailure stop n
      · obtain ⟨pair, hPair⟩ := (hSteps n hActive).2.2.exists_decorated
        exact ⟨(pair.current, pair.future), fun _ => hPair.2, fun h => (h hActive).elim⟩
      · exact ⟨(∅, ∅), fun h => (hActive h).elim, fun _ => rfl⟩
    choose pair hPair using hExists
    exact ⟨fun n => (pair n).1, fun n => (pair n).2,
      fun n h => (hPair n).1 h, fun n h => by simp [(hPair n).2 h]⟩
  rcases hRun with hAll | ⟨stop, hBefore, hStuck, hAt, hAfter⟩
  · obtain ⟨current, future, hOffers, hNone⟩ :=
      decorate prefixAt none (fun n _ => hAll n)
    exact ⟨⟨prefixAt, none, current, future, hRoot, fun n _ => hAll n,
      hOffers, by simp, by simp, hNone⟩⟩
  · let frozen : Nat → TypePrefix initial := fun n => prefixAt (min n stop)
    have hSteps (n : Nat) (hn : BeforeTypeFailure (some stop) n) :
        OrdinaryTypeStep initial strategy log frozen n := by
      have hLt : n < stop := hn stop rfl
      simpa [OrdinaryTypeStep, frozen, Nat.min_eq_left (Nat.le_of_lt hLt),
        Nat.min_eq_left (show n + 1 ≤ stop by omega)] using hBefore n hLt
    obtain ⟨current, future, hOffers, hNone⟩ := decorate frozen (some stop) hSteps
    refine ⟨⟨frozen, some stop, current, future, by simpa [frozen] using hRoot,
      hSteps, hOffers, ?_, ?_, hNone⟩⟩
    · intro n hn
      have : stop = n := Option.some.inj hn
      subst n
      simpa [frozen, TypeReady] using And.intro hStuck (And.intro hAt hAfter)
    · intro n hn m hm
      have : stop = n := Option.some.inj hn
      subst n
      simp [frozen, Nat.min_eq_right hm]

/-- The completion predicate reads the actual residual, including after failure. -/
def Finished {initial : PactType} {strategy : TypeStrategy} {log : TypeLog}
    (run : CompletedTypeExecution initial strategy log) (index : Nat) : Prop :=
  (run.prefixAt index).residual = .skip (run.prefixAt index).residual.alphabet

/-- Failure padding leaves the entire represented prefix unchanged. -/
theorem prefix_succ_of_failure {initial : PactType} {strategy : TypeStrategy} {log : TypeLog}
    (run : CompletedTypeExecution initial strategy log) {index : Nat}
    (hFailed : ¬ BeforeTypeFailure run.stop index) :
    run.prefixAt (index + 1) = run.prefixAt index := by
  cases hStop : run.stop with
  | none => simp [BeforeTypeFailure, hStop] at hFailed
  | some stop =>
      have hLe : stop ≤ index := by simpa [BeforeTypeFailure, hStop] using hFailed
      exact (run.frozen stop hStop (index + 1) (by omega)).trans
        (run.frozen stop hStop index hLe).symm

end CompletedTypeExecution

/-- Matching blocks agree on initial availability and closing futures, completion, and failure. -/
structure CompletionBlockMatch
    {left right : PactType} {leftStrategy rightStrategy : TypeStrategy}
    {leftLog rightLog : TypeLog}
    (leftRun : CompletedTypeExecution left leftStrategy leftLog)
    (rightRun : CompletedTypeExecution right rightStrategy rightLog)
    extends TypeLogClockBlockMatch leftLog rightLog where
  availability : ∀ block,
    typeAvailable (leftLog (leftBlocks.cut block)).1 =
      typeAvailable (rightLog (rightBlocks.cut block)).1
  futures : ∀ block,
    leftRun.future (leftBlocks.cut (block + 1) - 1) =
      rightRun.future (rightBlocks.cut (block + 1) - 1)
  completion : ∀ block,
    leftRun.Finished (leftBlocks.cut (block + 1)) ↔
      rightRun.Finished (rightBlocks.cut (block + 1))
  failure : ∀ block,
    BeforeTypeFailure leftRun.stop (leftBlocks.cut (block + 1)) ↔
      BeforeTypeFailure rightRun.stop (rightBlocks.cut (block + 1))

namespace CompletionBlockMatch

/-- Identical executions match in singleton blocks with identical boundary states. -/
def refl {initial : PactType} {strategy : TypeStrategy} {log : TypeLog}
    (run : CompletedTypeExecution initial strategy log) : CompletionBlockMatch run run where
  toTypeLogClockBlockMatch := .refl log
  availability := fun _ => rfl
  futures := fun _ => rfl
  completion := fun _ => Iff.rfl
  failure := fun _ => Iff.rfl

end CompletionBlockMatch

/-- Honest strategy comparison matches input availability and completion-aware block boundaries. -/
structure CompletionBlockRefinement (precise abstract : PactType) : Prop where
  alphabet : precise.alphabet = abstract.alphabet
  fairIds : typeFairIds precise = typeFairIds abstract
  progressIds : precise.ProgressIds = abstract.ProgressIds
  transfer : ∀ strategy, WellFormedTypeStrategy abstract strategy →
    HonestTypeStrategy abstract strategy →
    ∃ preciseStrategy,
      WellFormedTypeStrategy precise preciseStrategy ∧
      HonestTypeStrategy precise preciseStrategy ∧
      ∀ log (run : CompletedTypeExecution precise preciseStrategy log),
        ∃ abstractLog, ∃ abstractRun : CompletedTypeExecution abstract strategy abstractLog,
          Nonempty (CompletionBlockMatch run abstractRun)

namespace CompletionBlockRefinement

/-- Each strategy matches itself, including its failure and completion states. -/
theorem refl (source : PactType) : CompletionBlockRefinement source source := by
  refine ⟨rfl, rfl, rfl, fun strategy hWF hHonest =>
    ⟨strategy, hWF, hHonest, fun log run => ?_⟩⟩
  exact ⟨log, run, ⟨CompletionBlockMatch.refl run⟩⟩

/-- Forgetting boundary states recovers honest block comparison. -/
theorem toHonestBlockRefinement {precise abstract : PactType}
    (refinement : CompletionBlockRefinement precise abstract) :
    HonestBlockRefinement precise abstract := by
  refine ⟨refinement.alphabet, refinement.fairIds, refinement.progressIds, ?_⟩
  intro strategy hWF hHonest
  obtain ⟨preciseStrategy, hPreciseWF, hPreciseHonest, hMatch⟩ :=
    refinement.transfer strategy hWF hHonest
  refine ⟨preciseStrategy, hPreciseWF, hPreciseHonest, fun log hCompleted => ?_⟩
  obtain ⟨run⟩ := CompletedTypeExecution.exists_of_completed hCompleted
  obtain ⟨abstractLog, abstractRun, ⟨matching⟩⟩ := hMatch log run
  exact ⟨abstractLog, abstractRun.completed, ⟨matching.toTypeLogClockBlockMatch⟩⟩

/-- Completion-aware comparison preserves compiled-game compatibility. -/
theorem compatible {precise abstract : PactType} {progress : Finset ProcId}
    (refinement : CompletionBlockRefinement precise abstract)
    (hPrecise : TypeWellFormedIn [] precise) (hAbstract : TypeWellFormedIn [] abstract)
    (hCompatible : TypeCompatible abstract progress) : TypeCompatible precise progress :=
  refinement.toHonestBlockRefinement.compatible hPrecise hAbstract hCompatible

end CompletionBlockRefinement

end

end Pact
