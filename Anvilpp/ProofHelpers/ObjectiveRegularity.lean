import Anvilpp.ProofHelpers.LogRecognizer
import Anvilpp.ProofHelpers.ObjectiveMonitor
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace Pact

noncomputable section

open Classical

instance objectiveDisjunctFintype (initial : PactType) : Fintype (ObjectiveDisjunct initial) :=
  Fintype.ofList (objectiveDisjuncts initial) fun disjunct => by
    cases disjunct with
    | live => exact live_mem_objectiveDisjuncts initial
    | fair _ _ hMem => exact fair_mem_objectiveDisjuncts hMem

/-- Outstanding requests, a completion flag, and a forbidden-observation flag. -/
abbrev LogRoundState (req : Finset TypeMark) :=
  {pending : Finset TypeMark // pending ∈ req.powerset} × Bool × Bool

/-- Honest-prefix status, retained availability, and finite acceptance monitors. -/
structure FiniteLogMonitorState (Memory Disjunct : Type) (req : Disjunct → Finset TypeMark) where
  valid : Bool
  memory : Option Memory
  rounds : (disjunct : Disjunct) → LogRoundState (req disjunct)

instance finiteLogMonitorStateFintype (Memory Disjunct : Type) [Fintype Memory]
    [Fintype Disjunct] (req : Disjunct → Finset TypeMark) :
    Fintype (FiniteLogMonitorState Memory Disjunct req) :=
  Fintype.ofInjective (fun state => (state.valid, state.memory, state.rounds)) (by
    intro left right h
    cases left; cases right
    simpa only [Prod.mk.injEq, FiniteLogMonitorState.mk.injEq] using h)

abbrev LogMonitorState (initial : PactType) (progress : Finset ProcId) :=
  FiniteLogMonitorState
    {allowed : Finset BareMessage //
      allowed ∈ initial.alphabet.localEnvironmentActions.powerset}
    (ObjectiveDisjunct initial) (ObjectiveDisjunct.req progress)

/-- Initial honesty memory and one outstanding request set per Rabin pair. -/
def logMonitorInitial (initial : PactType) (progress : Finset ProcId) :
    LogMonitorState initial progress :=
  ⟨true, none, fun disjunct => ⟨⟨disjunct.req progress, by simp⟩, false, false⟩⟩

/-- One entry updates honesty and every acceptance monitor; rejection is permanent. -/
def logMonitorStep {initial : PactType} {progress : Finset ProcId}
    (state : LogMonitorState initial progress) (letter : TypeLogLetter initial) :
    LogMonitorState initial progress where
  valid := state.valid && decide (match state.memory with
    | none => True
    | some allowed => typeAvailable letter.val.1 ⊆ allowed.val)
  memory := match letter.val.2 with
    | .tock => none
    | .actions _ => some ⟨letter.val.1.honestyRemainder letter.val.2, by
        apply Finset.mem_powerset.mpr
        have hWF := PactTypeAlphabet.environment_wellFormed
          (Finset.mem_product.mp letter.property).1
        exact (letter.val.1.honestyRemainder_subset letter.val.2).trans
          (Finset.union_subset hWF.2.2.1 hWF.2.2.2)⟩
  rounds := fun disjunct =>
    let next := monitorAdvance (disjunct.req progress) (state.rounds disjunct).1.val
      (typeLabelMarks letter.val.2)
    ⟨⟨next.1, by
      apply Finset.mem_powerset.mpr
      dsimp [next]
      rw [monitorAdvance_eq]
      split
      · exact Finset.Subset.refl _
      · exact Finset.sdiff_subset.trans (Finset.mem_powerset.mp (state.rounds disjunct).1.property)
    ⟩, next.2, decide ((typeLabelMarks letter.val.2 ∩ disjunct.forbid).Nonempty)⟩

/-- The finite product recognizer for honesty and the liveness/fairness disjunction. -/
def logObjectiveRecognizer (initial : PactType) (progress : Finset ProcId) :
    FiniteRabinAutomaton (TypeLogLetter initial) where
  State := LogMonitorState initial progress
  initial := logMonitorInitial initial progress
  step := logMonitorStep
  pairs := (objectiveDisjuncts initial).map fun disjunct =>
    ({state | state.valid = true ∧ (state.rounds disjunct).2.1 = true},
      {state | (state.rounds disjunct).2.2 = true})

namespace LogMonitor

variable {initial : PactType} (progress : Finset ProcId) (word : ℕ → TypeLogLetter initial)

abbrev run := (logObjectiveRecognizer initial progress).run word

lemma valid_prev (n : ℕ) (h : (run progress word (n + 1)).valid = true) :
    (run progress word n).valid = true := by
  change (_ && decide _) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

lemma valid_of_le {m n : ℕ} (hLe : m ≤ n) (h : (run progress word n).valid = true) :
    (run progress word m).valid = true := by
  induction hLe with
  | refl => exact h
  | @step n _ ih => exact ih (valid_prev progress word n h)

lemma valid_next_iff (n : ℕ) :
    (run progress word (n + 2)).valid = true ↔
      (run progress word (n + 1)).valid = true ∧
        ((word n).val.2.isTock ∨
          typeAvailable (word (n + 1)).val.1 ⊆
            (word n).val.1.honestyRemainder (word n).val.2) := by
  change (_ && decide _) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  cases hLabel : (word n).val.2 <;>
    simp [FiniteRabinAutomaton.run, logObjectiveRecognizer, logMonitorStep,
      hLabel, TypeLabel.isTock]

/-- The honesty flag remains true exactly on honest words. -/
lemma all_valid_iff :
    (∀ n, (run progress word n).valid = true) ↔
      HonestTypeLog (fun n => (word n).val) := by
  constructor
  · intro h n
    exact ((valid_next_iff progress word n).mp (h (n + 2))).2
  · intro h n
    induction n with
    | zero => rfl
    | succ n ih =>
        cases n with
        | zero =>
            simp [run, FiniteRabinAutomaton.run, logObjectiveRecognizer,
              logMonitorInitial, logMonitorStep]
        | succ n => exact (valid_next_iff progress word n).mpr ⟨ih, h n⟩

/-- Each request component follows the existing round-robin run. -/
lemma rounds_eq (disjunct : ObjectiveDisjunct initial) (n : ℕ) :
    ((run progress word n).rounds disjunct).1.val =
        (monitorRun (disjunct.req progress) (fun n => typeLabelMarks (word n).val.2) n).1 ∧
      ((run progress word n).rounds disjunct).2.1 =
        (monitorRun (disjunct.req progress) (fun n => typeLabelMarks (word n).val.2) n).2 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      change (monitorAdvance _ ((run progress word n).rounds disjunct).1.val _).1 = _ ∧
        (monitorAdvance _ ((run progress word n).rounds disjunct).1.val _).2 = _
      rw [ih.1]
      exact ⟨rfl, rfl⟩

/-- Infinitely many good visits require honesty and infinitely many completed rounds. -/
lemma good_infinite_iff (disjunct : ObjectiveDisjunct initial) :
    Set.Infinite {n | (run progress word n).valid = true ∧
        ((run progress word n).rounds disjunct).2.1 = true} ↔
      HonestTypeLog (fun n => (word n).val) ∧
        ∀ mark ∈ disjunct.req progress,
          Set.Infinite {n | mark ∈ typeLabelMarks (word n).val.2} := by
  have hRounds : Set.Infinite {n | ((run progress word n).rounds disjunct).2.1 = true} ↔
      ∀ mark ∈ disjunct.req progress,
        Set.Infinite {n | mark ∈ typeLabelMarks (word n).val.2} := by
    exact (infinite_congr fun n => by
      simp only [Set.mem_setOf_eq, (rounds_eq progress word disjunct n).2]).trans
      (monitorRun_flag_infinite_iff _ _)
  constructor
  · intro hGood
    have hValid : ∀ n, (run progress word n).valid = true := by
      intro n
      obtain ⟨m, hMem, hLe⟩ := set_infinite_nat_iff.mp hGood n
      exact valid_of_le progress word hLe hMem.1
    exact ⟨(all_valid_iff progress word).mp hValid,
      hRounds.mp (hGood.mono fun _ h => h.2)⟩
  · rintro ⟨hHonest, hReq⟩
    have hValid := (all_valid_iff progress word).mpr hHonest
    exact (infinite_congr fun n => by
      simp only [Set.mem_setOf_eq, hValid n, true_and]).mpr (hRounds.mpr hReq)

lemma infinite_succ_iff (predicate : ℕ → Prop) :
    Set.Infinite {n | predicate (n + 1)} ↔ Set.Infinite {n | predicate n} := by
  simp only [set_infinite_nat_iff, Set.mem_setOf_eq]
  constructor
  · intro h bound
    obtain ⟨n, hMem, hLe⟩ := h bound
    exact ⟨n + 1, hMem, by omega⟩
  · intro h bound
    obtain ⟨n, hMem, hLe⟩ := h (bound + 1)
    exact ⟨n - 1, by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hMem, by omega⟩

/-- Bad-state visits record exactly the forbidden observations, shifted by one entry. -/
lemma bad_infinite_iff (disjunct : ObjectiveDisjunct initial) :
    Set.Infinite {n | ((run progress word n).rounds disjunct).2.2 = true} ↔
      Set.Infinite {n | (typeLabelMarks (word n).val.2 ∩ disjunct.forbid).Nonempty} := by
  rw [← infinite_succ_iff]
  apply infinite_congr
  intro n
  change decide ((typeLabelMarks (word n).val.2 ∩ disjunct.forbid).Nonempty) = true ↔ _
  simp only [decide_eq_true_eq, Set.mem_setOf_eq]

end LogMonitor

/-- Required live marks recur exactly when the clock and all progress marks recur. -/
lemma log_live_requests_iff (initial : PactType) (progress : Finset ProcId) (log : TypeLog) :
    (∀ mark ∈ (ObjectiveDisjunct.live : ObjectiveDisjunct initial).req progress,
      Set.Infinite {n | mark ∈ typeLabelMarks (log n).2}) ↔
    (TypeTockOccursInfinitely log ∧
      ∀ pid ∈ progress, TypeObservationOccursInfinitely (.progress pid) log) := by
  simp only [ObjectiveDisjunct.req, Finset.forall_mem_insert, Finset.forall_mem_image,
    mem_typeLabelMarks_clock, mem_typeLabelMarks_observation]
  rfl

/-- Required unfairness marks recur exactly when the clock and one outcome recur. -/
lemma log_fair_requests_iff {initial : PactType} (progress : Finset ProcId) (log : TypeLog)
    {bid : BranchId} {outcome : Bool} (hMem : bid ∈ typeFairIds initial) :
    (∀ mark ∈ (ObjectiveDisjunct.fair bid outcome hMem).req progress,
      Set.Infinite {n | mark ∈ typeLabelMarks (log n).2}) ↔
    (TypeTockOccursInfinitely log ∧ TypeObservationOccursInfinitely (.fair bid outcome) log) := by
  simp only [ObjectiveDisjunct.req, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
    mem_typeLabelMarks_clock, mem_typeLabelMarks_observation]
  rfl

lemma log_fair_forbidden_iff {initial : PactType} (log : TypeLog)
    {bid : BranchId} {outcome : Bool} (hMem : bid ∈ typeFairIds initial) :
    Set.Infinite {n | (typeLabelMarks (log n).2 ∩
        (ObjectiveDisjunct.fair bid outcome hMem).forbid).Nonempty} ↔
      TypeObservationOccursInfinitely (.fair bid (!outcome)) log := by
  apply infinite_congr
  intro n
  simp [ObjectiveDisjunct.forbid, Finset.Nonempty, Finset.mem_inter]

/-- The liveness implication is the union of the live pair and the unfairness pairs. -/
lemma log_objective_disjuncts_iff (initial : PactType) (progress : Finset ProcId) (log : TypeLog) :
    (HonestTypeLog log ∧ ∃ disjunct ∈ objectiveDisjuncts initial,
      (∀ mark ∈ disjunct.req progress, Set.Infinite {n | mark ∈ typeLabelMarks (log n).2}) ∧
      ¬ Set.Infinite {n | (typeLabelMarks (log n).2 ∩ disjunct.forbid).Nonempty}) ↔
    TypeWinningObjective initial progress log := by
  constructor
  · rintro ⟨hHonest, disjunct, -, hReq, hForbid⟩
    cases disjunct with
    | live =>
        obtain ⟨hClock, hProgress⟩ := (log_live_requests_iff initial progress log).mp hReq
        exact ⟨hHonest, hClock, fun _ => hProgress⟩
    | fair bid outcome hMem =>
        obtain ⟨hClock, hOutcome⟩ := (log_fair_requests_iff progress log hMem).mp hReq
        rw [log_fair_forbidden_iff] at hForbid
        refine ⟨hHonest, hClock, fun hFair => False.elim (hForbid ?_)⟩
        cases outcome with
        | true => exact (hFair bid hMem).mp hOutcome
        | false => exact (hFair bid hMem).mpr hOutcome
  · rintro ⟨hHonest, hClock, hProgress⟩
    refine ⟨hHonest, ?_⟩
    by_cases hFair : FairTypeLog initial log
    · refine ⟨.live, live_mem_objectiveDisjuncts initial,
        (log_live_requests_iff initial progress log).mpr ⟨hClock, hProgress hFair⟩, ?_⟩
      simp [ObjectiveDisjunct.forbid]
    · have hUnfair : ¬ ∀ bid ∈ typeFairIds initial,
          (TypeObservationOccursInfinitely (.fair bid true) log ↔
            TypeObservationOccursInfinitely (.fair bid false) log) := hFair
      push_neg at hUnfair
      obtain ⟨bid, hMem, hNot⟩ := hUnfair
      rcases hNot with ⟨hTrue, hFalse⟩ | ⟨hTrue, hFalse⟩
      · exact ⟨.fair bid true hMem, fair_mem_objectiveDisjuncts hMem,
          (log_fair_requests_iff progress log hMem).mpr ⟨hClock, hTrue⟩,
          fun h => hFalse ((log_fair_forbidden_iff log hMem).mp h)⟩
      · exact ⟨.fair bid false hMem, fair_mem_objectiveDisjuncts hMem,
          (log_fair_requests_iff progress log hMem).mpr ⟨hClock, hFalse⟩,
          fun h => hTrue ((log_fair_forbidden_iff log hMem).mp h)⟩

/-- The finite recognizer accepts exactly the log objective. -/
theorem logObjectiveRecognizer_accepts_iff (initial : PactType) (progress : Finset ProcId)
    (word : ℕ → TypeLogLetter initial) :
    (logObjectiveRecognizer initial progress).Accepts word ↔
      TypeWinningObjective initial progress (fun n => (word n).val) := by
  rw [← log_objective_disjuncts_iff]
  constructor
  · rintro ⟨pair, hPair, hGood, hBad⟩
    obtain ⟨disjunct, hDisjunct, rfl⟩ := List.mem_map.mp hPair
    obtain ⟨hHonest, hReq⟩ := (LogMonitor.good_infinite_iff progress word disjunct).mp hGood
    exact ⟨hHonest, disjunct, hDisjunct, hReq,
      fun h => hBad ((LogMonitor.bad_infinite_iff progress word disjunct).mpr h)⟩
  · rintro ⟨hHonest, disjunct, hDisjunct, hReq, hBad⟩
    refine ⟨_, List.mem_map.mpr ⟨disjunct, hDisjunct, rfl⟩,
      (LogMonitor.good_infinite_iff progress word disjunct).mpr ⟨hHonest, hReq⟩, ?_⟩
    exact fun h => hBad ((LogMonitor.bad_infinite_iff progress word disjunct).mp h)

/-- Every finite boundary log objective has a finite Rabin recognizer. -/
theorem omegaRegular_log_objective (initial : PactType) (progress : Finset ProcId) :
    OmegaRegular initial progress :=
  ⟨logObjectiveRecognizer initial progress, logObjectiveRecognizer_accepts_iff initial progress⟩

end

end Pact
