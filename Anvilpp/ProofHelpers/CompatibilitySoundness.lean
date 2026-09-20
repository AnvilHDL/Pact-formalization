import Anvilpp.ProofHelpers.PrefixPlayMatch

namespace Pact

noncomputable section

open Classical

/-! ## Log erasure and failure completion -/

/-- A concrete observation erasing to a given type observation. -/
def concreteObservation : TypeObservation → Observation
  | .message msg dir => .message msg dir false
  | .resolved msg => .resolved msg
  | .fair bid taken => .fair bid taken
  | .progress pid => .progress pid

@[simp] lemma eraseObservation_concreteObservation (observation : TypeObservation) :
    eraseObservation (concreteObservation observation) = observation := by
  cases observation <;> rfl

/-- A concrete label erasing to a given type label. -/
def concreteLabel : TypeLabel → Label
  | .actions observations => .actions (observations.image concreteObservation)
  | .tock => .tock

@[simp] lemma eraseLabel_concreteLabel (label : TypeLabel) :
    eraseLabel (concreteLabel label) = label := by
  cases label with
  | tock => rfl
  | actions observations =>
      show TypeLabel.actions _ = TypeLabel.actions _
      congr 1
      rw [Finset.image_image]
      conv_rhs => rw [← Finset.image_id (s := observations)]
      exact Finset.image_congr fun observation _ => by simp

/-- A concrete process log erasing to a given type log. -/
def concreteLog (log : TypeLog) : ProcessLog :=
  fun index => (concreteRepresentative (log index).1, concreteLabel (log index).2)

@[simp] lemma eraseProcessLog_concreteLog (log : TypeLog) :
    eraseProcessLog (concreteLog log) = log := by
  funext index
  show (eraseEnvironment (concreteRepresentative (log index).1),
    eraseLabel (concreteLabel (log index).2)) = log index
  rw [eraseEnvironment_concreteRepresentative, eraseLabel_concreteLabel]

/-! ### Erasure preserves clock and identifier observations -/

lemma mem_image_eraseObservation_progress {observations : Finset Observation}
    {pid : ProcId} :
    TypeObservation.progress pid ∈ observations.image eraseObservation ↔
      Observation.progress pid ∈ observations := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨observation, hMem, hEq⟩
    cases observation <;> simp [eraseObservation] at hEq
    subst hEq
    exact hMem
  · intro hMem
    exact ⟨_, hMem, rfl⟩

lemma mem_image_eraseObservation_fair {observations : Finset Observation}
    {bid : BranchId} {taken : Bool} :
    TypeObservation.fair bid taken ∈ observations.image eraseObservation ↔
      Observation.fair bid taken ∈ observations := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨observation, hMem, hEq⟩
    cases observation <;> simp [eraseObservation] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact hMem
  · intro hMem
    exact ⟨_, hMem, rfl⟩

lemma contains_eraseLabel_progress (label : Label) (pid : ProcId) :
    (eraseLabel label).contains (.progress pid) ↔ label.contains (.progress pid) := by
  cases label with
  | tock => simp [eraseLabel, TypeLabel.contains, Label.contains]
  | actions observations =>
      simpa [eraseLabel, TypeLabel.contains, Label.contains] using
        mem_image_eraseObservation_progress (observations := observations) (pid := pid)

lemma contains_eraseLabel_fair (label : Label) (bid : BranchId) (taken : Bool) :
    (eraseLabel label).contains (.fair bid taken) ↔ label.contains (.fair bid taken) := by
  cases label with
  | tock => simp [eraseLabel, TypeLabel.contains, Label.contains]
  | actions observations =>
      simpa [eraseLabel, TypeLabel.contains, Label.contains] using
        mem_image_eraseObservation_fair (observations := observations) (bid := bid)
          (taken := taken)

lemma tockOccursInfinitely_erase (log : ProcessLog) :
    TypeTockOccursInfinitely (eraseProcessLog log) ↔ TockOccursInfinitely log :=
  infinite_congr fun index => by
    show eraseLabel (log index).2 = TypeLabel.tock ↔ (log index).2 = Label.tock
    exact eraseLabel_eq_tock_iff _

lemma progressOccursInfinitely_erase (log : ProcessLog) (pid : ProcId) :
    TypeObservationOccursInfinitely (.progress pid) (eraseProcessLog log) ↔
      ObservationOccursInfinitely (.progress pid) log :=
  infinite_congr fun index => contains_eraseLabel_progress (log index).2 pid

lemma fairOccursInfinitely_erase (log : ProcessLog) (bid : BranchId) (taken : Bool) :
    TypeObservationOccursInfinitely (.fair bid taken) (eraseProcessLog log) ↔
      ObservationOccursInfinitely (.fair bid taken) log :=
  infinite_congr fun index => contains_eraseLabel_fair (log index).2 bid taken

/-! ### Failure-completed logs -/

lemma extendProcess_head {initial : Proc} {strategy : ProcessStrategy initial}
    {history : ProcessPrefix initial} {bound : ℕ}
    {headPrefix : ℕ → ProcessPrefix initial} {headLog : ProcessLog}
    (hRoot : headPrefix 0 = ⟨[], initial, .root⟩)
    (hFollows : ∀ n, FollowsProcessStrategy strategy (headPrefix n))
    (hLast : headPrefix bound = history)
    (hSteps : ∀ n, n < bound → OrdinaryProcessStep strategy headLog headPrefix n)
    {label : Label} {next : Proc}
    (hStep : ProcessTransition (strategy history) history.residual label next) :
    ∃ (headPrefix' : ℕ → ProcessPrefix initial) (headLog' : ProcessLog),
      headPrefix' 0 = ⟨[], initial, .root⟩ ∧
      (∀ n, FollowsProcessStrategy strategy (headPrefix' n)) ∧
      headPrefix' (bound + 1) =
        ⟨history.entries ++ [(strategy history, label, next)], next,
          history.valid.step hStep⟩ ∧
      (∀ n, n < bound + 1 → OrdinaryProcessStep strategy headLog' headPrefix' n) := by
  classical
  refine ⟨fun n => if n ≤ bound then headPrefix n else
      ⟨history.entries ++ [(strategy history, label, next)], next,
        history.valid.step hStep⟩,
    fun n => if n < bound then headLog n else (strategy history, label),
    by simpa using hRoot, ?_, by simp, ?_⟩
  · intro n
    simp only []
    by_cases hLe : n ≤ bound
    · rw [if_pos hLe]; exact hFollows n
    · rw [if_neg hLe]
      have := (hLast ▸ hFollows bound).step hStep
      exact this
  · intro n hLt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hLt with hHead | hEq
    · have hStepN := hSteps n hHead
      simp only [OrdinaryProcessStep, if_pos (Nat.le_of_lt hHead),
        if_pos (Nat.succ_le_of_lt hHead), if_pos hHead]
      exact hStepN
    · subst hEq
      simp only [OrdinaryProcessStep, if_pos (Nat.le_refl n),
        if_neg (Nat.not_succ_le_self n), if_neg (Nat.lt_irrefl n), hLast]
      exact ⟨trivial, trivial, hStep⟩

lemma followsProcess_head {initial : Proc} {strategy : ProcessStrategy initial}
    {history : ProcessPrefix initial}
    (hFollows : FollowsProcessStrategy strategy history) :
    ∃ (bound : ℕ) (headPrefix : ℕ → ProcessPrefix initial) (headLog : ProcessLog),
      headPrefix 0 = ⟨[], initial, .root⟩ ∧
      (∀ n, FollowsProcessStrategy strategy (headPrefix n)) ∧
      headPrefix bound = history ∧
      (∀ n, n < bound → OrdinaryProcessStep strategy headLog headPrefix n) := by
  induction hFollows with
  | root =>
      exact ⟨0, fun _ => ⟨[], initial, .root⟩,
        fun _ => (Environment.empty, Label.silent), rfl, fun _ => .root, rfl,
        fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | step hFollows hStep ih =>
      obtain ⟨bound, headPrefix, headLog, hRoot, hAll, hLast, hSteps⟩ := ih
      obtain ⟨headPrefix', headLog', hRoot', hAll', hLast', hSteps'⟩ :=
        extendProcess_head hRoot hAll hLast hSteps hStep
      exact ⟨bound + 1, headPrefix', headLog', hRoot', hAll', hLast', hSteps'⟩

/-- A stuck strategy-reachable prefix extends to a failure-completed log whose clock stops. -/
lemma completedProcessLog_of_stuck {initial : Proc} {strategy : ProcessStrategy initial}
    {history : ProcessPrefix initial}
    (hFollows : FollowsProcessStrategy strategy history)
    (hStuck : Stuck (strategy history) history.residual) :
    ∃ (log : ProcessLog) (bound : ℕ), CompletedProcessLog strategy log ∧
      ∀ m, bound < m → log m = (Environment.empty, Label.silent) := by
  classical
  obtain ⟨bound, headPrefix, headLog, hRoot, hAll, hLast, hSteps⟩ :=
    followsProcess_head hFollows
  refine ⟨fun n => if n < bound then headLog n else if n = bound then
      (strategy history, Label.silent) else (Environment.empty, Label.silent),
    bound, ⟨fun n => if n < bound then headPrefix n else history, ?_, ?_, ?_⟩, ?_⟩
  · simp only []
    by_cases hZero : 0 < bound
    · rw [if_pos hZero]; exact hRoot
    · rw [if_neg hZero, ← hLast, show bound = 0 from by omega]; exact hRoot
  · intro n
    simp only []
    by_cases hLt : n < bound
    · rw [if_pos hLt]; exact hAll n
    · rw [if_neg hLt, ← hLast]; exact hAll bound
  · have hPrefix : ∀ n, n ≤ bound →
        (if n < bound then headPrefix n else history) = headPrefix n := by
      intro n hLe
      rcases Nat.lt_or_ge n bound with hLt | hGe
      · rw [if_pos hLt]
      · rw [if_neg (Nat.not_lt.mpr hGe), ← hLast, Nat.le_antisymm hLe hGe]
    refine Or.inr ⟨bound, ?_, ?_, ?_, ?_⟩
    · intro n hLt
      simp only [OrdinaryProcessStep, if_pos hLt, hPrefix (n + 1) (Nat.succ_le_of_lt hLt)]
      exact hSteps n hLt
    · simp only []
      rw [if_neg (Nat.lt_irrefl bound)]
      exact hStuck
    · simp only []
      simp
    · intro m hLt
      simp only []
      rw [if_neg (by omega : ¬ m < bound), if_neg (by omega : ¬ m = bound)]
  · intro m hLt
    simp only []
    rw [if_neg (by omega : ¬ m < bound), if_neg (by omega : ¬ m = bound)]

end

end Pact
