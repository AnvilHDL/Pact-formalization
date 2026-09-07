import Anvilpp.ProofHelpers.RoundRobin
import Anvilpp.ProofHelpers.SameCycleHonesty

namespace Pact

noncomputable section

open Classical

/-! ## Reading `Ω_T` off a play of the monitored game -/

/-- A path in the monitored arena. -/
def CompatibilityPath {initial : PactType} {progress : Finset ProcId}
    (play : ℕ → MonitoredVertex initial progress) : Prop :=
  play 0 = monitoredInitial initial progress ∧
    ∀ index, monitoredEdge initial progress (play index) (play (index + 1))

/-- `Label(π)`: the labels the play's edges fired.  The arena alternates
Player-0 choice vertices with Player-1 resolving vertices, so the resolving and
failure entries sit on the vertices at even positions `2k+2`. -/
def compatibilityPlayLog {initial : PactType} {progress : Finset ProcId}
    (play : ℕ → MonitoredVertex initial progress) : TypeLog :=
  fun index =>
    (play (2 * index + 2)).entry.getD (TypeEnvironment.empty, TypeLabel.silent)

/-! ### Shape of the arena

A choice vertex only leads to a resolving vertex, a resolving vertex to a
choice vertex or the sink, and the sink only to itself. -/

lemma compatibilityEdge_fail_left {automaton : TypeAutomaton}
    {alphabet : PactTypeAlphabet} {target : CompatibilityVertex}
    (hEdge : compatibilityEdge automaton alphabet .fail target) :
    target = .fail := by
  cases target with
  | choice _ _ => simp only [compatibilityEdge] at hEdge
  | resolve _ _ _ => simp only [compatibilityEdge] at hEdge
  | fail => rfl

lemma compatibilityEdge_choice_left {automaton : TypeAutomaton}
    {alphabet : PactTypeAlphabet} {state : TypeAutomatonState}
    {memory : HonestyMemory} {target : CompatibilityVertex}
    (hEdge : compatibilityEdge automaton alphabet (.choice state memory) target) :
    ∃ env, target = .resolve state memory env := by
  cases target with
  | choice _ _ => simp only [compatibilityEdge] at hEdge
  | resolve state' memory' env =>
      obtain ⟨hState, hMemory, -⟩ := hEdge
      exact ⟨env, by rw [hState, hMemory]⟩
  | fail => simp only [compatibilityEdge] at hEdge

lemma compatibilityEdge_resolve_left {automaton : TypeAutomaton}
    {alphabet : PactTypeAlphabet} {state : TypeAutomatonState}
    {memory : HonestyMemory} {env : TypeEnvironment} {target : CompatibilityVertex}
    (hEdge : compatibilityEdge automaton alphabet (.resolve state memory env) target) :
    (∃ state' memory', target = .choice state' memory') ∨ target = .fail := by
  cases target with
  | choice state' memory' => exact Or.inl ⟨state', memory', rfl⟩
  | resolve _ _ _ => simp only [compatibilityEdge] at hEdge
  | fail => exact Or.inr rfl

/-! ### Parity and the absorbing sink -/

variable {initial : PactType} {progress : Finset ProcId}
  {play : ℕ → MonitoredVertex initial progress}

lemma CompatibilityPath.parity (hPath : CompatibilityPath play) : ∀ index,
    ((play (2 * index)).base = .fail ∨
      ∃ state memory, (play (2 * index)).base = .choice state memory) ∧
    ((play (2 * index + 1)).base = .fail ∨
      ∃ state memory env, (play (2 * index + 1)).base = .resolve state memory env) := by
  intro index
  induction index with
  | zero =>
      have hRoot : (play 0).base = .choice (compileType initial).initial .star := by
        rw [hPath.1]; rfl
      refine ⟨Or.inr ⟨_, _, by simpa using hRoot⟩, ?_⟩
      have hEdge := (hPath.2 0).1
      rw [hRoot] at hEdge
      obtain ⟨env, hTarget⟩ := compatibilityEdge_choice_left hEdge
      exact Or.inr ⟨_, _, env, by simpa using hTarget⟩
  | succ index ih =>
      have hEven : 2 * (index + 1) = 2 * index + 1 + 1 := by omega
      have hOdd : 2 * (index + 1) + 1 = 2 * index + 1 + 1 + 1 := by omega
      have hFirst : (play (2 * index + 1 + 1)).base = .fail ∨
          ∃ state memory, (play (2 * index + 1 + 1)).base = .choice state memory := by
        have hEdge := (hPath.2 (2 * index + 1)).1
        rcases ih.2 with hFail | ⟨state, memory, env, hResolve⟩
        · rw [hFail] at hEdge
          exact Or.inl (compatibilityEdge_fail_left hEdge)
        · rw [hResolve] at hEdge
          rcases compatibilityEdge_resolve_left hEdge with ⟨s, m, hEq⟩ | hEq
          · exact Or.inr ⟨s, m, hEq⟩
          · exact Or.inl hEq
      refine ⟨by rw [hEven]; exact hFirst, ?_⟩
      rw [hOdd]
      have hEdge := (hPath.2 (2 * index + 1 + 1)).1
      rcases hFirst with hFail | ⟨state, memory, hChoice⟩
      · rw [hFail] at hEdge
        exact Or.inl (compatibilityEdge_fail_left hEdge)
      · rw [hChoice] at hEdge
        obtain ⟨env, hTarget⟩ := compatibilityEdge_choice_left hEdge
        exact Or.inr ⟨state, memory, env, hTarget⟩

lemma CompatibilityPath.fail_persists (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) :
    ∀ later, index ≤ later → (play later).base = .fail := by
  intro later hLe
  induction later with
  | zero => exact (Nat.le_zero.mp hLe) ▸ hFail
  | succ later ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hLe) with hLt | hEq
      · have hPrev := ih (Nat.lt_succ_iff.mp hLt)
        have hEdge := (hPath.2 later).1
        rw [hPrev] at hEdge
        exact compatibilityEdge_fail_left hEdge
      · exact hEq ▸ hFail

/-- Every step out of the sink fires the absorbing entry `⟨(∅,∅),ε⟩`. -/
lemma CompatibilityPath.sink_entry (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) :
    (play (index + 1)).entry = some (TypeEnvironment.empty, TypeLabel.silent) := by
  have hStep := (hPath.2 index).2.1
  rw [hFail] at hStep
  simpa only [compatibilityStepEntry] using hStep

/-! ### The request sets -/

lemma clock_mem_req (progress : Finset ProcId) (disjunct : ObjectiveDisjunct initial) :
    TypeMark.clock ∈ ObjectiveDisjunct.req progress disjunct := by
  cases disjunct with
  | live => simp [ObjectiveDisjunct.req]
  | fair => simp [ObjectiveDisjunct.req]

lemma req_ne_empty (progress : Finset ProcId) (disjunct : ObjectiveDisjunct initial) :
    ObjectiveDisjunct.req progress disjunct ≠ ∅ :=
  Finset.ne_empty_of_mem (clock_mem_req progress disjunct)

@[simp] lemma typeLabelMarks_silent : typeLabelMarks TypeLabel.silent = ∅ := by
  simp [typeLabelMarks, TypeLabel.silent]

lemma monitorAdvance_empty_ne (req pending : Finset TypeMark) (hReq : req ≠ ∅) :
    (monitorAdvance req pending ∅).1 ≠ ∅ := by
  rw [monitorAdvance_eq, Finset.sdiff_empty]
  by_cases hEmpty : pending = ∅ <;> simp [hEmpty, hReq]

lemma monitorAdvance_empty_of_ne (req pending : Finset TypeMark) (hPending : pending ≠ ∅) :
    monitorAdvance req pending ∅ = (pending, false) := by
  rw [monitorAdvance_eq, Finset.sdiff_empty, if_neg hPending]

/-- Inside the sink every step advances the monitors on no marks at all. -/
lemma CompatibilityPath.sink_monitor_step (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) (later : ℕ) (hLe : index ≤ later)
    (disjunct : ObjectiveDisjunct initial) :
    ((play (later + 1)).pending disjunct, (play (later + 1)).flag disjunct) =
      monitorAdvance (ObjectiveDisjunct.req progress disjunct)
        ((play later).pending disjunct) ∅ := by
  have hEntry := hPath.sink_entry (hPath.fail_persists hFail later hLe)
  have hMonitor := (hPath.2 later).2.2
  rw [hEntry] at hMonitor
  simpa using hMonitor disjunct

lemma CompatibilityPath.sink_pending_ne (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) (later : ℕ) (hLe : index ≤ later)
    (disjunct : ObjectiveDisjunct initial) :
    (play (later + 1)).pending disjunct ≠ ∅ := by
  have hStep : (play (later + 1)).pending disjunct =
      (monitorAdvance (ObjectiveDisjunct.req progress disjunct)
        ((play later).pending disjunct) ∅).1 :=
    congrArg Prod.fst (hPath.sink_monitor_step hFail later hLe disjunct)
  rw [hStep]
  exact monitorAdvance_empty_ne _ _ (req_ne_empty progress disjunct)

lemma CompatibilityPath.sink_flag_false (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) (later : ℕ) (hLt : index + 1 < later)
    (disjunct : ObjectiveDisjunct initial) :
    (play later).flag disjunct = false := by
  obtain ⟨previous, rfl⟩ : ∃ previous, later = previous + 1 := by
    cases later with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  obtain ⟨earlier, rfl⟩ : ∃ earlier, previous = earlier + 1 := by
    cases previous with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  have hPending := hPath.sink_pending_ne hFail earlier (by omega) disjunct
  have hStep := hPath.sink_monitor_step hFail (earlier + 1) (by omega) disjunct
  rw [monitorAdvance_empty_of_ne _ _ hPending] at hStep
  exact congrArg Prod.snd hStep

lemma CompatibilityPath.sink_not_accepts (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) :
    ¬ RabinGame.Accepts (compatibilityGame initial progress) play := by
  rintro ⟨pair, hMem, hInfinite, -⟩
  obtain ⟨disjunct, -, rfl⟩ := List.mem_map.mp hMem
  obtain ⟨position, hFlag, hLe⟩ := set_infinite_nat_iff.mp hInfinite (index + 2)
  have hTrue : (play position).flag disjunct = true := hFlag
  rw [hPath.sink_flag_false hFail position (by omega) disjunct] at hTrue
  exact Bool.noConfusion hTrue

lemma CompatibilityPath.sink_log_silent (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) (position : ℕ) (hLe : index ≤ 2 * position + 1) :
    (compatibilityPlayLog play position).2 = TypeLabel.silent := by
  have hEntry := hPath.sink_entry (hPath.fail_persists hFail (2 * position + 1) hLe)
  simp [compatibilityPlayLog, hEntry]

lemma CompatibilityPath.sink_not_objective (hPath : CompatibilityPath play) {index : ℕ}
    (hFail : (play index).base = .fail) :
    ¬ TypeWinningObjective initial progress (compatibilityPlayLog play) := by
  rintro ⟨-, hTock, -⟩
  obtain ⟨position, hMem, hLe⟩ := set_infinite_nat_iff.mp hTock index
  simp only [Set.mem_setOf_eq] at hMem
  rw [hPath.sink_log_silent hFail position (by omega)] at hMem
  exact absurd hMem (by simp [TypeLabel.silent])

/-! ### Sink-avoiding plays

Player-0 choice vertices sit at even positions and Player-1 resolving vertices
at odd positions, so each round `2k+1 → 2k+2` fires exactly one log entry. -/

/-- The marks fired by the `k`-th log entry of a play. -/
def playMarks (play : ℕ → MonitoredVertex initial progress) (index : ℕ) :
    Finset TypeMark :=
  typeLabelMarks (compatibilityPlayLog play index).2

lemma CompatibilityPath.choice_at_even (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    ∃ state memory, (play (2 * index)).base = .choice state memory := by
  rcases (hPath.parity index).1 with hFail | hChoice
  · exact absurd hFail (hFree _)
  · exact hChoice

lemma CompatibilityPath.resolve_at_odd (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    ∃ state memory env, (play (2 * index + 1)).base = .resolve state memory env := by
  rcases (hPath.parity index).2 with hFail | hResolve
  · exact absurd hFail (hFree _)
  · exact hResolve

/-- The bookkeeping half-edge `θ_e` fires no entry. -/
lemma CompatibilityPath.entry_odd (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    (play (2 * index + 1)).entry = none := by
  obtain ⟨state, memory, hChoice⟩ := hPath.choice_at_even hFree index
  have hStep := (hPath.2 (2 * index)).2.1
  rw [hChoice] at hStep
  simpa only [compatibilityStepEntry] using hStep

/-- One resolving round: the play passes through `q^{F,e}` and lands on
`q'^{P,Next(e,α)}` having fired `⟨e,α⟩`. -/
lemma CompatibilityPath.step_shape (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    ∃ state memory env state' label,
      (play (2 * index + 1)).base = .resolve state memory env ∧
      (play (2 * index + 1 + 1)).base = .choice state' (honestyNext env label) ∧
      memory.Admissible env ∧
      (play (2 * index + 1 + 1)).entry = some (env, label) := by
  obtain ⟨state, memory, env, hResolve⟩ := hPath.resolve_at_odd hFree index
  obtain ⟨state', memory', hChoice⟩ : ∃ state' memory',
      (play (2 * index + 1 + 1)).base = .choice state' memory' := by
    have := hPath.choice_at_even hFree (index + 1)
    rw [show 2 * (index + 1) = 2 * index + 1 + 1 from by omega] at this
    exact this
  have hEdge := (hPath.2 (2 * index + 1)).1
  have hStep := (hPath.2 (2 * index + 1)).2.1
  rw [hResolve, hChoice] at hEdge hStep
  simp only [compatibilityStepEntry] at hStep
  obtain ⟨label, -, hMemory, hEntry⟩ := hStep
  exact ⟨state, memory, env, state', label, hResolve, hMemory ▸ hChoice, hEdge.1, hEntry⟩

lemma CompatibilityPath.log_entry (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    (play (2 * index + 1 + 1)).entry = some (compatibilityPlayLog play index) := by
  obtain ⟨state, memory, env, state', label, hResolve, hChoice, hAdm, hEntry⟩ :=
    hPath.step_shape hFree index
  have hUnfold : compatibilityPlayLog play index = (env, label) := by
    simp [compatibilityPlayLog, show 2 * index + 2 = 2 * index + 1 + 1 from rfl, hEntry]
  rw [hUnfold, hEntry]

/-- Honesty of the play's log is exactly what the honesty memory enforces. -/
lemma CompatibilityPath.honest (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) :
    HonestTypeLog (compatibilityPlayLog play) := by
  intro index
  obtain ⟨state, memory, env, state', label, hResolve, hChoice, hAdm, hEntry⟩ :=
    hPath.step_shape hFree index
  obtain ⟨state₂, memory₂, env₂, state₂', label₂, hResolve₂, hChoice₂, hAdm₂, hEntry₂⟩ :=
    hPath.step_shape hFree (index + 1)
  rw [show 2 * (index + 1) + 1 = 2 * index + 1 + 1 + 1 from by omega] at hResolve₂
  rw [show 2 * (index + 1) + 1 + 1 = 2 * index + 1 + 1 + 1 + 1 from by omega] at hEntry₂
  have hEdge := (hPath.2 (2 * index + 1 + 1)).1
  rw [hChoice] at hEdge
  obtain ⟨envNext, hNext⟩ := compatibilityEdge_choice_left hEdge
  rw [hNext] at hResolve₂
  simp only [CompatibilityVertex.resolve.injEq] at hResolve₂
  have hLog : compatibilityPlayLog play index = (env, label) := by
    simp [compatibilityPlayLog, show 2 * index + 2 = 2 * index + 1 + 1 from rfl, hEntry]
  have hLog₂ : compatibilityPlayLog play (index + 1) = (env₂, label₂) := by
    simp [compatibilityPlayLog,
      show 2 * (index + 1) + 2 = 2 * index + 1 + 1 + 1 + 1 from by omega, hEntry₂]
  rw [← hResolve₂.2.1] at hAdm₂
  rw [hLog, hLog₂]
  cases label with
  | tock => exact Or.inl trivial
  | actions observations =>
      refine Or.inr ?_
      simpa [honestyNext, HonestyMemory.Admissible] using hAdm₂

/-! ### The monitors along a sink-avoiding play -/

lemma CompatibilityPath.monitor_odd (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    (play (2 * index + 1)).pending = (play (2 * index)).pending ∧
      (play (2 * index + 1)).flag = fun _ => false := by
  have hMonitor := (hPath.2 (2 * index)).2.2
  rw [hPath.entry_odd hFree index] at hMonitor
  exact hMonitor

lemma CompatibilityPath.flag_odd (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ)
    (disjunct : ObjectiveDisjunct initial) :
    (play (2 * index + 1)).flag disjunct = false := by
  rw [(hPath.monitor_odd hFree index).2]

lemma CompatibilityPath.monitor_even (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ)
    (disjunct : ObjectiveDisjunct initial) :
    ((play (2 * index + 1 + 1)).pending disjunct,
        (play (2 * index + 1 + 1)).flag disjunct) =
      monitorAdvance (ObjectiveDisjunct.req progress disjunct)
        ((play (2 * index)).pending disjunct) (playMarks play index) := by
  have hMonitor := (hPath.2 (2 * index + 1)).2.2
  rw [hPath.log_entry hFree index] at hMonitor
  have hStep := hMonitor disjunct
  rw [(hPath.monitor_odd hFree index).1] at hStep
  exact hStep

/-- The monitor components of the even vertices are exactly the round-robin
run over the play's log. -/
lemma CompatibilityPath.monitor_run (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ)
    (disjunct : ObjectiveDisjunct initial) :
    ((play (2 * index)).pending disjunct, (play (2 * index)).flag disjunct) =
      monitorRun (ObjectiveDisjunct.req progress disjunct) (playMarks play) index := by
  induction index with
  | zero => rw [hPath.1]; rfl
  | succ index ih =>
      rw [show 2 * (index + 1) = 2 * index + 1 + 1 from by omega,
        hPath.monitor_even hFree index disjunct, monitorRun_succ]
      have hFst : (play (2 * index)).pending disjunct =
          (monitorRun (ObjectiveDisjunct.req progress disjunct)
            (playMarks play) index).1 := congrArg Prod.fst ih
      rw [hFst]

lemma parity_cases (index : ℕ) : (∃ half, index = 2 * half) ∨ ∃ half, index = 2 * half + 1 := by
  rcases Nat.eq_zero_or_pos (index % 2) with hMod | hMod
  · exact Or.inl ⟨index / 2, by omega⟩
  · exact Or.inr ⟨index / 2, by omega⟩

lemma CompatibilityPath.flag_infinite_iff (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail)
    (disjunct : ObjectiveDisjunct initial) :
    Set.Infinite {n | (play n).flag disjunct = true} ↔
      Set.Infinite {n | (monitorRun (ObjectiveDisjunct.req progress disjunct)
        (playMarks play) n).2 = true} := by
  rw [set_infinite_nat_iff, set_infinite_nat_iff]
  constructor
  · intro hFlags bound
    obtain ⟨position, hFlag, hLe⟩ := hFlags (2 * bound)
    have hTrue : (play position).flag disjunct = true := hFlag
    rcases parity_cases position with ⟨half, rfl⟩ | ⟨half, rfl⟩
    · have hEq : (play (2 * half)).flag disjunct =
          (monitorRun (ObjectiveDisjunct.req progress disjunct)
            (playMarks play) half).2 :=
        congrArg Prod.snd (hPath.monitor_run hFree half disjunct)
      refine ⟨half, ?_, by omega⟩
      show (monitorRun (ObjectiveDisjunct.req progress disjunct)
        (playMarks play) half).2 = true
      rw [← hEq]; exact hTrue
    · rw [hPath.flag_odd hFree half disjunct] at hTrue
      exact absurd hTrue (by simp)
  · intro hFlags bound
    obtain ⟨position, hFlag, hLe⟩ := hFlags bound
    have hTrue : (monitorRun (ObjectiveDisjunct.req progress disjunct)
        (playMarks play) position).2 = true := hFlag
    have hEq : (play (2 * position)).flag disjunct =
        (monitorRun (ObjectiveDisjunct.req progress disjunct)
          (playMarks play) position).2 :=
      congrArg Prod.snd (hPath.monitor_run hFree position disjunct)
    refine ⟨2 * position, ?_, by omega⟩
    show (play (2 * position)).flag disjunct = true
    rw [hEq]; exact hTrue

lemma CompatibilityPath.marks_odd (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    (play (2 * index + 1)).marks = ∅ := by
  simp [MonitoredVertex.marks, hPath.entry_odd hFree index]

lemma CompatibilityPath.marks_even_succ (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (index : ℕ) :
    (play (2 * index + 1 + 1)).marks = playMarks play index := by
  simp [MonitoredVertex.marks, hPath.log_entry hFree index, playMarks]

lemma CompatibilityPath.marks_zero (hPath : CompatibilityPath play) :
    (play 0).marks = ∅ := by
  rw [hPath.1]; rfl

lemma CompatibilityPath.marks_infinite_iff (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail) (forbid : Finset TypeMark) :
    Set.Infinite {n | ((play n).marks ∩ forbid).Nonempty} ↔
      Set.Infinite {n | (playMarks play n ∩ forbid).Nonempty} := by
  rw [set_infinite_nat_iff, set_infinite_nat_iff]
  constructor
  · intro hMarks bound
    obtain ⟨position, hMem, hLe⟩ := hMarks (2 * bound + 2)
    have hNonempty : ((play position).marks ∩ forbid).Nonempty := hMem
    rcases parity_cases position with ⟨half, rfl⟩ | ⟨half, rfl⟩
    · obtain ⟨earlier, rfl⟩ : ∃ earlier, half = earlier + 1 := by
        cases half with
        | zero => omega
        | succ k => exact ⟨k, rfl⟩
      rw [show 2 * (earlier + 1) = 2 * earlier + 1 + 1 from by omega,
        hPath.marks_even_succ hFree earlier] at hNonempty
      exact ⟨earlier, hNonempty, by omega⟩
    · rw [hPath.marks_odd hFree half] at hNonempty
      simp at hNonempty
  · intro hMarks bound
    obtain ⟨position, hMem, hLe⟩ := hMarks bound
    have hNonempty : (playMarks play position ∩ forbid).Nonempty := hMem
    have hEq := hPath.marks_even_succ hFree position
    refine ⟨2 * position + 1 + 1, ?_, by omega⟩
    show ((play (2 * position + 1 + 1)).marks ∩ forbid).Nonempty
    rw [hEq]; exact hNonempty

/-! ### Reading the log predicates off the marks -/

lemma infinite_congr {left right : Set ℕ} (hIff : ∀ n, n ∈ left ↔ n ∈ right) :
    left.Infinite ↔ right.Infinite := by
  rw [Set.ext hIff]

@[simp] lemma mem_typeLabelMarks_clock (label : TypeLabel) :
    TypeMark.clock ∈ typeLabelMarks label ↔ label = TypeLabel.tock := by
  cases label with
  | tock => simp [typeLabelMarks]
  | actions observations => simp [typeLabelMarks]

@[simp] lemma mem_typeLabelMarks_observation (label : TypeLabel)
    (observation : TypeObservation) :
    TypeMark.observation observation ∈ typeLabelMarks label ↔
      label.contains observation := by
  cases label with
  | tock => simp [typeLabelMarks, TypeLabel.contains]
  | actions observations => simp [typeLabelMarks, TypeLabel.contains]

lemma clock_marks_infinite_iff (play : ℕ → MonitoredVertex initial progress) :
    Set.Infinite {n | TypeMark.clock ∈ playMarks play n} ↔
      TypeTockOccursInfinitely (compatibilityPlayLog play) :=
  infinite_congr fun _ => by simp [playMarks, TypeTockOccursInfinitely]

lemma observation_marks_infinite_iff (play : ℕ → MonitoredVertex initial progress)
    (observation : TypeObservation) :
    Set.Infinite {n | TypeMark.observation observation ∈ playMarks play n} ↔
      TypeObservationOccursInfinitely observation (compatibilityPlayLog play) :=
  infinite_congr fun _ => by simp [playMarks, TypeObservationOccursInfinitely]

lemma req_live_infinite_iff (play : ℕ → MonitoredVertex initial progress) :
    (∀ mark ∈ ObjectiveDisjunct.req progress (ObjectiveDisjunct.live : ObjectiveDisjunct initial),
        Set.Infinite {n | mark ∈ playMarks play n}) ↔
      (TypeTockOccursInfinitely (compatibilityPlayLog play) ∧
        ∀ pid ∈ progress,
          TypeObservationOccursInfinitely (.progress pid) (compatibilityPlayLog play)) := by
  constructor
  · intro hAll
    refine ⟨(clock_marks_infinite_iff play).mp (hAll _ (by simp [ObjectiveDisjunct.req])), ?_⟩
    intro pid hPid
    exact (observation_marks_infinite_iff play _).mp
      (hAll _ (by
        simp only [ObjectiveDisjunct.req, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨pid, hPid, rfl⟩))
  · rintro ⟨hTock, hProgress⟩ mark hMark
    simp only [ObjectiveDisjunct.req, Finset.mem_insert, Finset.mem_image] at hMark
    rcases hMark with rfl | ⟨pid, hPid, rfl⟩
    · exact (clock_marks_infinite_iff play).mpr hTock
    · exact (observation_marks_infinite_iff play _).mpr (hProgress pid hPid)

lemma req_fair_infinite_iff (play : ℕ → MonitoredVertex initial progress)
    {bid : BranchId} {outcome : Bool} (hMem : bid ∈ typeFairIds initial) :
    (∀ mark ∈ ObjectiveDisjunct.req progress (ObjectiveDisjunct.fair bid outcome hMem),
        Set.Infinite {n | mark ∈ playMarks play n}) ↔
      (TypeTockOccursInfinitely (compatibilityPlayLog play) ∧
        TypeObservationOccursInfinitely (.fair bid outcome) (compatibilityPlayLog play)) := by
  constructor
  · intro hAll
    exact ⟨(clock_marks_infinite_iff play).mp (hAll _ (by simp [ObjectiveDisjunct.req])),
      (observation_marks_infinite_iff play _).mp (hAll _ (by simp [ObjectiveDisjunct.req]))⟩
  · rintro ⟨hTock, hFair⟩ mark hMark
    simp only [ObjectiveDisjunct.req, Finset.mem_insert, Finset.mem_singleton] at hMark
    rcases hMark with rfl | rfl
    · exact (clock_marks_infinite_iff play).mpr hTock
    · exact (observation_marks_infinite_iff play _).mpr hFair

lemma forbid_live_never (play : ℕ → MonitoredVertex initial progress) :
    ¬ Set.Infinite {n | (playMarks play n ∩
      ObjectiveDisjunct.forbid (ObjectiveDisjunct.live : ObjectiveDisjunct initial)).Nonempty} := by
  intro hInfinite
  obtain ⟨position, hMem, -⟩ := set_infinite_nat_iff.mp hInfinite 0
  have hNonempty : (playMarks play position ∩
    ObjectiveDisjunct.forbid (ObjectiveDisjunct.live : ObjectiveDisjunct initial)).Nonempty := hMem
  simp [ObjectiveDisjunct.forbid] at hNonempty

lemma forbid_fair_infinite_iff (play : ℕ → MonitoredVertex initial progress)
    {bid : BranchId} {outcome : Bool} (hMem : bid ∈ typeFairIds initial) :
    Set.Infinite {n | (playMarks play n ∩
        ObjectiveDisjunct.forbid (ObjectiveDisjunct.fair bid outcome hMem)).Nonempty} ↔
      TypeObservationOccursInfinitely (.fair bid (!outcome)) (compatibilityPlayLog play) := by
  refine Iff.trans (infinite_congr fun n => ?_)
    (observation_marks_infinite_iff play (.fair bid (!outcome)))
  simp [ObjectiveDisjunct.forbid, Finset.Nonempty, Finset.mem_inter]

lemma live_mem_objectiveDisjuncts (initial : PactType) :
    ObjectiveDisjunct.live ∈ objectiveDisjuncts initial := by
  simp [objectiveDisjuncts]

lemma fair_mem_objectiveDisjuncts {initial : PactType} {bid : BranchId} {outcome : Bool}
    (hMem : bid ∈ typeFairIds initial) :
    ObjectiveDisjunct.fair bid outcome hMem ∈ objectiveDisjuncts initial := by
  refine List.mem_cons_of_mem _ ?_
  rw [List.mem_flatMap]
  refine ⟨⟨bid, hMem⟩, by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, ?_⟩
  cases outcome <;> simp

lemma accepts_iff (initial : PactType) (progress : Finset ProcId)
    (play : ℕ → MonitoredVertex initial progress) :
    RabinGame.Accepts (compatibilityGame initial progress) play ↔
      ∃ disjunct ∈ objectiveDisjuncts initial,
        Set.Infinite {n | (play n).flag disjunct = true} ∧
        ¬ Set.Infinite {n |
          ((play n).marks ∩ ObjectiveDisjunct.forbid disjunct).Nonempty} := by
  constructor
  · rintro ⟨pair, hMem, hCompletion, hForbidden⟩
    obtain ⟨disjunct, hDisjunct, rfl⟩ := List.mem_map.mp hMem
    exact ⟨disjunct, hDisjunct, hCompletion, hForbidden⟩
  · rintro ⟨disjunct, hDisjunct, hCompletion, hForbidden⟩
    exact ⟨_, List.mem_map.mpr ⟨disjunct, hDisjunct, rfl⟩, hCompletion, hForbidden⟩

lemma CompatibilityPath.completion_iff (hPath : CompatibilityPath play)
    (hFree : ∀ index, (play index).base ≠ .fail)
    (disjunct : ObjectiveDisjunct initial) :
    Set.Infinite {n | (play n).flag disjunct = true} ↔
      ∀ mark ∈ ObjectiveDisjunct.req progress disjunct,
        Set.Infinite {n | mark ∈ playMarks play n} := by
  rw [hPath.flag_infinite_iff hFree disjunct, monitorRun_flag_infinite_iff]

/-- Helper Lemma H18: the objective monitor recognizes exactly `Ω_T`. -/
theorem helper_h18_objective_monitor
    (initial : PactType) (progress : Finset ProcId)
    (play : ℕ → MonitoredVertex initial progress)
    (hPath : CompatibilityPath play) :
    RabinGame.Accepts (compatibilityGame initial progress) play ↔
      TypeWinningObjective initial progress (compatibilityPlayLog play) := by
  by_cases hSink : ∃ index, (play index).base = .fail
  · obtain ⟨index, hFail⟩ := hSink
    exact ⟨fun hAccepts => absurd hAccepts (hPath.sink_not_accepts hFail),
      fun hObjective => absurd hObjective (hPath.sink_not_objective hFail)⟩
  push_neg at hSink
  rw [accepts_iff]
  constructor
  · rintro ⟨disjunct, -, hCompletion, hForbidden⟩
    rw [hPath.completion_iff hSink disjunct] at hCompletion
    rw [hPath.marks_infinite_iff hSink] at hForbidden
    cases disjunct with
    | live =>
        obtain ⟨hTock, hProgress⟩ := (req_live_infinite_iff play).mp hCompletion
        exact ⟨hPath.honest hSink, hTock, fun _ => hProgress⟩
    | fair bid outcome hMem =>
        obtain ⟨hTock, hOutcome⟩ := (req_fair_infinite_iff play hMem).mp hCompletion
        rw [forbid_fair_infinite_iff play hMem] at hForbidden
        refine ⟨hPath.honest hSink, hTock, fun hFair => ?_⟩
        exact absurd (by
          cases outcome with
          | true => exact (hFair bid hMem).mp hOutcome
          | false => exact (hFair bid hMem).mpr hOutcome) hForbidden
  · rintro ⟨-, hTock, hLive⟩
    by_cases hFair : FairTypeLog initial (compatibilityPlayLog play)
    · refine ⟨ObjectiveDisjunct.live, live_mem_objectiveDisjuncts initial, ?_, ?_⟩
      · rw [hPath.completion_iff hSink]
        exact (req_live_infinite_iff play).mpr ⟨hTock, hLive hFair⟩
      · rw [hPath.marks_infinite_iff hSink]
        exact forbid_live_never play
    · have hUnfair : ¬ ∀ bid ∈ typeFairIds initial,
          (TypeObservationOccursInfinitely (.fair bid true) (compatibilityPlayLog play) ↔
            TypeObservationOccursInfinitely (.fair bid false)
              (compatibilityPlayLog play)) := hFair
      push_neg at hUnfair
      obtain ⟨bid, hMem, hNot⟩ := hUnfair
      rcases hNot with ⟨hTrue, hFalse⟩ | ⟨hTrue, hFalse⟩
      · refine ⟨ObjectiveDisjunct.fair bid true hMem,
          fair_mem_objectiveDisjuncts hMem, ?_, ?_⟩
        · rw [hPath.completion_iff hSink]
          exact (req_fair_infinite_iff play hMem).mpr ⟨hTock, hTrue⟩
        · rw [hPath.marks_infinite_iff hSink, forbid_fair_infinite_iff play hMem]
          exact hFalse
      · refine ⟨ObjectiveDisjunct.fair bid false hMem,
          fair_mem_objectiveDisjuncts hMem, ?_, ?_⟩
        · rw [hPath.completion_iff hSink]
          exact (req_fair_infinite_iff play hMem).mpr ⟨hTock, hFalse⟩
        · rw [hPath.marks_infinite_iff hSink, forbid_fair_infinite_iff play hMem]
          exact hTrue

end

end Pact
