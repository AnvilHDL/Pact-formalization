import Anvilpp.ProofHelpers.RoundRobin

namespace Pact

noncomputable section

open Classical

/-! ## Extending a generated prefix to a completed log

Honesty and readiness of a winning strategy are only available through its
completed logs, so every prefix the strategy generates has to be shown to occur
in one.  The continuation runs the strategy canonically: it takes some enabled
step while one exists, and completes with the absorbing failure suffix once the
run gets stuck. -/

variable {initial : PactType}

/-- No step is available under the strategy's environment. -/
def PrefixStuck (initial : PactType) (strategy : TypeStrategy)
    (history : TypePrefix initial) : Prop :=
  ¬ ∃ label target,
    TypeTransition (strategy history.entries) history.residual label target

/-- One canonical continuation step. -/
noncomputable def canonicalStep (initial : PactType) (strategy : TypeStrategy)
    (history : TypePrefix initial) : TypePrefix initial :=
  if h : ∃ label target,
      TypeTransition (strategy history.entries) history.residual label target then
    ⟨history.entries ++
        [(strategy history.entries, h.choose, h.choose_spec.choose)],
      h.choose_spec.choose,
      history.valid.step h.choose_spec.choose_spec⟩
  else history

/-- The label the canonical continuation fires. -/
noncomputable def canonicalLabel (initial : PactType) (strategy : TypeStrategy)
    (history : TypePrefix initial) : TypeLabel :=
  if h : ∃ label target,
      TypeTransition (strategy history.entries) history.residual label target then
    h.choose
  else TypeLabel.silent

lemma canonicalStep_of_stuck {strategy : TypeStrategy} {history : TypePrefix initial}
    (hStuck : PrefixStuck initial strategy history) :
    canonicalStep initial strategy history = history :=
  dif_neg hStuck

lemma canonicalLabel_of_stuck {strategy : TypeStrategy} {history : TypePrefix initial}
    (hStuck : PrefixStuck initial strategy history) :
    canonicalLabel initial strategy history = TypeLabel.silent :=
  dif_neg hStuck

/-- An unstuck canonical step is an ordinary step: it fires the strategy's
environment and the chosen label, and appends the matching entry. -/
lemma canonicalStep_spec {strategy : TypeStrategy} {history : TypePrefix initial}
    (hReady : ¬ PrefixStuck initial strategy history) :
    (canonicalStep initial strategy history).entries =
        history.entries ++
          [(strategy history.entries, canonicalLabel initial strategy history,
            (canonicalStep initial strategy history).residual)] ∧
      TypeTransition (strategy history.entries) history.residual
        (canonicalLabel initial strategy history)
        (canonicalStep initial strategy history).residual := by
  have hExists : ∃ label target,
      TypeTransition (strategy history.entries) history.residual label target := by
    simpa [PrefixStuck] using hReady
  rw [canonicalStep, dif_pos hExists, canonicalLabel, dif_pos hExists]
  exact ⟨rfl, hExists.choose_spec.choose_spec⟩

/-- The canonical continuation from a starting prefix. -/
noncomputable def canonicalRun (initial : PactType) (strategy : TypeStrategy)
    (start : TypePrefix initial) : ℕ → TypePrefix initial
  | 0 => start
  | n + 1 => canonicalStep initial strategy (canonicalRun initial strategy start n)

@[simp] lemma canonicalRun_zero (strategy : TypeStrategy) (start : TypePrefix initial) :
    canonicalRun initial strategy start 0 = start := rfl

@[simp] lemma canonicalRun_succ (strategy : TypeStrategy) (start : TypePrefix initial)
    (n : ℕ) :
    canonicalRun initial strategy start (n + 1) =
      canonicalStep initial strategy (canonicalRun initial strategy start n) := rfl

/-- Once stuck the canonical continuation stands still. -/
lemma canonicalRun_of_stuck {strategy : TypeStrategy} {start : TypePrefix initial}
    {stop : ℕ} (hStuck : PrefixStuck initial strategy
      (canonicalRun initial strategy start stop)) :
    ∀ later, stop ≤ later →
      canonicalRun initial strategy start later =
        canonicalRun initial strategy start stop := by
  intro later hLe
  induction later with
  | zero => rw [Nat.le_zero.mp hLe]
  | succ later ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hLe) with hLt | hEq
      · rw [canonicalRun_succ, ih (Nat.lt_succ_iff.mp hLt),
          canonicalStep_of_stuck hStuck]
      · rw [hEq]

/-- The continuation has already failed by step `count`. -/
def CanonicalFailedBefore (initial : PactType) (strategy : TypeStrategy)
    (start : TypePrefix initial) (count : ℕ) : Prop :=
  ∃ earlier, earlier < count ∧
    PrefixStuck initial strategy (canonicalRun initial strategy start earlier)

/-- Follow the given head for `bound` entries, then continue canonically. -/
noncomputable def spliceRun (initial : PactType) (strategy : TypeStrategy)
    (headPrefix : ℕ → TypePrefix initial) (bound : ℕ) (start : TypePrefix initial) :
    ℕ → TypePrefix initial :=
  fun index =>
    if index < bound then headPrefix index
    else canonicalRun initial strategy start (index - bound)

/-- The log of that splice: the head entries, then the canonical entries, then
the absorbing failure suffix. -/
noncomputable def spliceLog (initial : PactType) (strategy : TypeStrategy)
    (headLog : TypeLog) (bound : ℕ) (start : TypePrefix initial) : TypeLog :=
  fun index =>
    if index < bound then headLog index
    else if CanonicalFailedBefore initial strategy start (index - bound) then
      (TypeEnvironment.empty, TypeLabel.silent)
    else
      (strategy (canonicalRun initial strategy start (index - bound)).entries,
        canonicalLabel initial strategy
          (canonicalRun initial strategy start (index - bound)))

lemma spliceLog_of_lt {strategy : TypeStrategy} {headLog : TypeLog} {bound : ℕ}
    {start : TypePrefix initial} {index : ℕ} (hLt : index < bound) :
    spliceLog initial strategy headLog bound start index = headLog index :=
  if_pos hLt

lemma spliceRun_of_le {strategy : TypeStrategy} {headPrefix : ℕ → TypePrefix initial}
    {bound : ℕ} {start : TypePrefix initial}
    (hLast : headPrefix bound = start) {index : ℕ} (hLe : index ≤ bound) :
    spliceRun initial strategy headPrefix bound start index = headPrefix index := by
  rcases Nat.lt_or_ge index bound with hLt | hGe
  · exact if_pos hLt
  · have hEq : index = bound := Nat.le_antisymm hLe hGe
    subst hEq
    rw [spliceRun, if_neg (Nat.lt_irrefl index), Nat.sub_self, canonicalRun_zero, hLast]

lemma spliceRun_of_ge {strategy : TypeStrategy} {headPrefix : ℕ → TypePrefix initial}
    {bound : ℕ} {start : TypePrefix initial} {index : ℕ} (hGe : bound ≤ index) :
    spliceRun initial strategy headPrefix bound start index =
      canonicalRun initial strategy start (index - bound) :=
  if_neg (Nat.not_lt.mpr hGe)

lemma spliceOrdinary_head {strategy : TypeStrategy} {headLog : TypeLog}
    {headPrefix : ℕ → TypePrefix initial} {bound : ℕ} {start : TypePrefix initial}
    (hLast : headPrefix bound = start)
    (hSteps : ∀ n, n < bound → OrdinaryTypeStep initial strategy headLog headPrefix n)
    {index : ℕ} (hLt : index < bound) :
    OrdinaryTypeStep initial strategy
      (spliceLog initial strategy headLog bound start)
      (spliceRun initial strategy headPrefix bound start) index := by
  simp only [OrdinaryTypeStep, spliceLog_of_lt hLt,
    spliceRun_of_le hLast (Nat.le_of_lt hLt),
    spliceRun_of_le hLast (Nat.succ_le_of_lt hLt)]
  exact hSteps index hLt

lemma spliceOrdinary_canonical {strategy : TypeStrategy} {headLog : TypeLog}
    {headPrefix : ℕ → TypePrefix initial} {bound : ℕ} {start : TypePrefix initial}
    {index : ℕ} (hGe : bound ≤ index)
    (hFresh : ∀ earlier, earlier ≤ index - bound →
      ¬ PrefixStuck initial strategy (canonicalRun initial strategy start earlier)) :
    OrdinaryTypeStep initial strategy
      (spliceLog initial strategy headLog bound start)
      (spliceRun initial strategy headPrefix bound start) index := by
  have hNotFailed : ¬ CanonicalFailedBefore initial strategy start (index - bound) := by
    rintro ⟨earlier, hLt, hStuck⟩
    exact hFresh earlier (Nat.le_of_lt hLt) hStuck
  have hSucc : index + 1 - bound = (index - bound) + 1 := by omega
  have hReady := hFresh (index - bound) (Nat.le_refl _)
  obtain ⟨hEntries, hStep⟩ := canonicalStep_spec (initial := initial) hReady
  simp only [OrdinaryTypeStep, spliceLog, spliceRun_of_ge hGe,
    spliceRun_of_ge (Nat.le_succ_of_le hGe), hSucc, canonicalRun_succ,
    if_neg (Nat.not_lt.mpr hGe), if_neg hNotFailed]
  exact ⟨trivial, hEntries.symm, hStep⟩

/-- Every head that the strategy generates extends to a completed log. -/
theorem completedTypeLog_splice {strategy : TypeStrategy} {headLog : TypeLog}
    {headPrefix : ℕ → TypePrefix initial} {bound : ℕ} {start : TypePrefix initial}
    (hRoot : headPrefix 0 = ⟨[], initial, .root⟩)
    (hLast : headPrefix bound = start)
    (hSteps : ∀ n, n < bound → OrdinaryTypeStep initial strategy headLog headPrefix n) :
    CompletedTypeLog initial strategy
      (spliceLog initial strategy headLog bound start) := by
  refine ⟨spliceRun initial strategy headPrefix bound start, ?_, ?_⟩
  · rw [spliceRun_of_le hLast (Nat.zero_le bound), hRoot]
  by_cases hStuck : ∃ n, PrefixStuck initial strategy (canonicalRun initial strategy start n)
  · refine Or.inr ⟨bound + Nat.find hStuck, ?_, ?_, ?_, ?_⟩
    · intro n hLt
      rcases Nat.lt_or_ge n bound with hHead | hTail
      · exact spliceOrdinary_head hLast hSteps hHead
      · refine spliceOrdinary_canonical hTail fun earlier hLe => ?_
        exact Nat.find_min hStuck (by omega)
    · rw [spliceRun_of_ge (Nat.le_add_right bound _), Nat.add_sub_cancel_left]
      exact Nat.find_spec hStuck
    · have hFresh : ¬ CanonicalFailedBefore initial strategy start (Nat.find hStuck) := by
        rintro ⟨earlier, hLt, hEarlier⟩
        exact Nat.find_min hStuck hLt hEarlier
      rw [spliceRun_of_ge (Nat.le_add_right bound _), Nat.add_sub_cancel_left]
      simp only [spliceLog, if_neg (Nat.not_lt.mpr (Nat.le_add_right bound _)),
        Nat.add_sub_cancel_left,
        canonicalLabel_of_stuck (Nat.find_spec hStuck)]
      rw [if_neg hFresh]
    · intro m hLt
      have hFailed : CanonicalFailedBefore initial strategy start (m - bound) :=
        ⟨Nat.find hStuck, by omega, Nat.find_spec hStuck⟩
      simp only [spliceLog, if_neg (Nat.not_lt.mpr (by omega : bound ≤ m)), if_pos hFailed]
  · refine Or.inl fun n => ?_
    rcases Nat.lt_or_ge n bound with hHead | hTail
    · exact spliceOrdinary_head hLast hSteps hHead
    · exact spliceOrdinary_canonical hTail fun earlier _ hEarlier =>
        hStuck ⟨earlier, hEarlier⟩

/-! ### Consequences for a winning strategy -/

/-- Extend an ordinary head by one generated step. -/
lemma extend_head {strategy : TypeStrategy} {history : TypePrefix initial}
    {bound : ℕ} {headPrefix : ℕ → TypePrefix initial} {headLog : TypeLog}
    (hRoot : headPrefix 0 = ⟨[], initial, .root⟩)
    (hLast : headPrefix bound = history)
    (hSteps : ∀ n, n < bound → OrdinaryTypeStep initial strategy headLog headPrefix n)
    {label : TypeLabel} {next : PactType}
    (hStep : TypeTransition (strategy history.entries) history.residual label next) :
    ∃ (headPrefix' : ℕ → TypePrefix initial) (headLog' : TypeLog),
      headPrefix' 0 = ⟨[], initial, .root⟩ ∧
      headPrefix' (bound + 1) =
        ⟨history.entries ++ [(strategy history.entries, label, next)], next,
          history.valid.step hStep⟩ ∧
      headLog' bound = (strategy history.entries, label) ∧
      (∀ n, n < bound + 1 → OrdinaryTypeStep initial strategy headLog' headPrefix' n) := by
  classical
  refine ⟨fun n => if n ≤ bound then headPrefix n else
      ⟨history.entries ++ [(strategy history.entries, label, next)], next,
        history.valid.step hStep⟩,
    fun n => if n < bound then headLog n else (strategy history.entries, label),
    by simpa using hRoot, by simp, by simp, ?_⟩
  intro n hLt
  rcases Nat.lt_succ_iff_lt_or_eq.mp hLt with hHead | hEq
  · have hStepN := hSteps n hHead
    simp only [OrdinaryTypeStep, if_pos (Nat.le_of_lt hHead),
      if_pos (Nat.succ_le_of_lt hHead), if_pos hHead]
    exact hStepN
  · subst hEq
    simp only [OrdinaryTypeStep, if_pos (Nat.le_refl n), if_neg (Nat.not_succ_le_self n),
      if_neg (Nat.lt_irrefl n), hLast]
    exact ⟨trivial, trivial, hStep⟩

/-- Every prefix the strategy generates is the endpoint of an ordinary head. -/
lemma follows_head {strategy : TypeStrategy} {history : TypePrefix initial}
    (hFollows : FollowsTypeStrategy initial strategy history) :
    ∃ (bound : ℕ) (headPrefix : ℕ → TypePrefix initial) (headLog : TypeLog),
      headPrefix 0 = ⟨[], initial, .root⟩ ∧ headPrefix bound = history ∧
      (∀ n, n < bound → OrdinaryTypeStep initial strategy headLog headPrefix n) := by
  induction hFollows with
  | root =>
      exact ⟨0, fun _ => ⟨[], initial, .root⟩,
        fun _ => (TypeEnvironment.empty, TypeLabel.silent), rfl, rfl,
        fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | step hFollows hStep ih =>
      obtain ⟨bound, headPrefix, headLog, hRoot, hLast, hSteps⟩ := ih
      obtain ⟨headPrefix', headLog', hRoot', hLast', -, hSteps'⟩ :=
        extend_head hRoot hLast hSteps hStep
      exact ⟨bound + 1, headPrefix', headLog', hRoot', hLast', hSteps'⟩

lemma spliceLog_at_bound {strategy : TypeStrategy} {headLog : TypeLog} {bound : ℕ}
    {start : TypePrefix initial} :
    (spliceLog initial strategy headLog bound start bound).1 =
      strategy start.entries := by
  have hNotFailed : ¬ CanonicalFailedBefore initial strategy start 0 := by
    rintro ⟨earlier, hLt, -⟩
    omega
  simp only [spliceLog, if_neg (Nat.lt_irrefl bound), Nat.sub_self, canonicalRun_zero,
    if_neg hNotFailed]

lemma spliceLog_silent_of_stuck {strategy : TypeStrategy} {headLog : TypeLog}
    {bound : ℕ} {start : TypePrefix initial}
    (hStuck : PrefixStuck initial strategy start) {index : ℕ} (hGe : bound ≤ index) :
    (spliceLog initial strategy headLog bound start index).2 = TypeLabel.silent := by
  by_cases hFailed : CanonicalFailedBefore initial strategy start (index - bound)
  · simp only [spliceLog, if_neg (Nat.not_lt.mpr hGe), if_pos hFailed]
  · have hFrozen : canonicalRun initial strategy start (index - bound) = start :=
      canonicalRun_of_stuck (by simpa using hStuck) (index - bound) (Nat.zero_le _)
    simp only [spliceLog, if_neg (Nat.not_lt.mpr hGe), if_neg hFailed, hFrozen,
      canonicalLabel_of_stuck hStuck]

/-- A winning strategy is never stuck on a prefix it generates: a stuck run
completes with the absorbing suffix, and its clock stops recurring. -/
theorem strategy_ready {progress : Finset ProcId} {strategy : TypeStrategy}
    (hWins : ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log)
    {history : TypePrefix initial}
    (hFollows : FollowsTypeStrategy initial strategy history) :
    TypeReady (strategy history.entries) history.residual := by
  by_contra hStuck
  obtain ⟨bound, headPrefix, headLog, hRoot, hLast, hSteps⟩ := follows_head hFollows
  obtain ⟨-, hTock, -⟩ := hWins _ (completedTypeLog_splice hRoot hLast hSteps)
  obtain ⟨index, hMem, hGe⟩ := set_infinite_nat_iff.mp hTock bound
  have hTockAt : (spliceLog initial strategy headLog bound history index).2 =
      TypeLabel.tock := hMem
  rw [spliceLog_silent_of_stuck hStuck hGe] at hTockAt
  exact absurd hTockAt (by simp [TypeLabel.silent])

/-- A winning strategy retains only promises and unconsumed offers after a non-clock step. -/
theorem strategy_honest {progress : Finset ProcId} {strategy : TypeStrategy}
    (hWins : ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log)
    {history : TypePrefix initial}
    (hFollows : FollowsTypeStrategy initial strategy history)
    {label : TypeLabel} {next : PactType}
    (hStep : TypeTransition (strategy history.entries) history.residual label next)
    (hNotTock : ¬ label.isTock) :
    typeAvailable
        (strategy (history.entries ++ [(strategy history.entries, label, next)])) ⊆
      (strategy history.entries).honestyRemainder label := by
  obtain ⟨bound, headPrefix, headLog, hRoot, hLast, hSteps⟩ := follows_head hFollows
  obtain ⟨headPrefix', headLog', hRoot', hLast', hLogAt, hSteps'⟩ :=
    extend_head hRoot hLast hSteps hStep
  obtain ⟨hHonest, -, -⟩ :=
    hWins _ (completedTypeLog_splice hRoot' hLast' hSteps')
  have hEntry : spliceLog initial strategy headLog' (bound + 1)
      ⟨history.entries ++ [(strategy history.entries, label, next)], next,
        history.valid.step hStep⟩ bound = (strategy history.entries, label) := by
    rw [spliceLog_of_lt (Nat.lt_succ_self bound), hLogAt]
  have hNext := spliceLog_at_bound (initial := initial) (strategy := strategy)
    (headLog := headLog') (bound := bound + 1)
    (start := ⟨history.entries ++ [(strategy history.entries, label, next)], next,
      history.valid.step hStep⟩)
  rcases hHonest bound with hTock | hAvail
  · rw [hEntry] at hTock
    exact absurd hTock hNotTock
  · rw [hEntry] at hAvail
    rw [hNext] at hAvail
    exact hAvail

end

end Pact
