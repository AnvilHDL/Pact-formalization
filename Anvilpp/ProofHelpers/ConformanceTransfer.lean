import Anvilpp.ProofHelpers.Regularity

namespace Pact

noncomputable section

open Classical

/-! ## Helper-lemma scaffold

These are the named helper lemmas, stated against
the current Lean scaffold.  The substantial proof content is intentionally
left as redevelopment work. -/

/-- `γ(e)`: put back a payload only where erasure removed one.
Each erased immediate send is given the (arbitrary, but fixed) payload
`false`; each erased immediate receive and the whole future menu are copied
unchanged, since erasure does not touch them. -/
def concreteRepresentative (env : TypeEnvironment) : Environment :=
  { immediate := env.immediate.image fun action =>
      match action.2 with
      | .send => Offer.send action.1 false
      | .recv => Offer.recv action.1
    future := env.future
    clock := env.clock }

/-- `γ` is a one-sided inverse of erasure, unconditionally (well-formedness
of the source is not needed: erasure only ever forgets a payload, so putting
one back and erasing again reproduces the original bare environment exactly).
This is the equational content of Helper Lemma H2's first clause, exposed for
reuse by the strategy-matching construction below. -/
theorem eraseEnvironment_concreteRepresentative (env : TypeEnvironment) :
    eraseEnvironment (concreteRepresentative env) = env := by
  have hBareImmediate : (concreteRepresentative env).bareImmediate = env.immediate := by
    show (env.immediate.image fun action =>
        match action.2 with
        | .send => Offer.send action.1 false
        | .recv => Offer.recv action.1).image Offer.bare = env.immediate
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := env.immediate)]
    apply Finset.image_congr
    intro action _
    rcases action with ⟨msg, dir⟩
    cases dir <;> rfl
  have hFuture : (concreteRepresentative env).future = env.future := rfl
  have hClock : (concreteRepresentative env).clock = env.clock := rfl
  unfold eraseEnvironment
  rw [hBareImmediate, hFuture, hClock]

/-- Helper Lemma H2 — "Concrete
representatives of erased environments".  Every well-formed erased
environment `e` has a concrete representative `γ(e)` with
`Erase(γ(e)) = e`, `Avail(γ(e)) = Avail(e)`, and `γ(∅,∅) = (∅,∅)`. -/
lemma helper_h2_concrete_representative_of_erased_environment
    (env : TypeEnvironment) {alphabet : PactTypeAlphabet}
    (hWellFormed : env.WellFormed alphabet) :
    ∃ concrete : Environment,
      eraseEnvironment concrete = env ∧
      concrete.available = typeAvailable env ∧
      (env = TypeEnvironment.empty → concrete = Environment.empty) := by
  have hBareImmediate : (concreteRepresentative env).bareImmediate = env.immediate := by
    have hErase := eraseEnvironment_concreteRepresentative env
    have := congrArg TypeEnvironment.immediate hErase
    simpa [eraseEnvironment] using this
  refine ⟨concreteRepresentative env, eraseEnvironment_concreteRepresentative env, ?_, ?_⟩
  · unfold Environment.available typeAvailable
    have hFuture : (concreteRepresentative env).future = env.future := rfl
    rw [hBareImmediate, hFuture, Finset.union_comm]
  · intro hEmpty
    subst hEmpty
    simp only [concreteRepresentative, TypeEnvironment.empty, Finset.image_empty]
    rfl

/-- The matching type residual chosen at one recorded entry.  Conformance's
step-matching supplies at least one; the construction fixes a choice, which is
all the paper's simultaneous induction needs. -/
noncomputable def matchingResidual {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType) (source : PactType)
    (entry : Environment × Label × Proc) : PactType :=
  if h : ∃ target, TypeTransition (eraseEnvironment entry.1) source
      (eraseLabel entry.2.1) target ∧ witness.relation entry.2.2 target then
    h.choose
  else source

theorem matchingResidual_spec {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType) (source : PactType)
    (env : Environment) (label : Label) (next : Proc)
    (hExists : ∃ target, TypeTransition (eraseEnvironment env) source
      (eraseLabel label) target ∧ witness.relation next target) :
    TypeTransition (eraseEnvironment env) source (eraseLabel label)
        (matchingResidual witness source (env, label, next)) ∧
      witness.relation next (matchingResidual witness source (env, label, next)) := by
  rw [matchingResidual, dif_pos hExists]
  exact hExists.choose_spec

/-- One step of the paper's simultaneous induction: extend the matching type
history by the erased entry and its chosen residual. -/
noncomputable def matchingTypeStep {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType)
    (state : TypeHistory × PactType) (entry : Environment × Label × Proc) :
    TypeHistory × PactType :=
  (state.1 ++ [(eraseEnvironment entry.1, eraseLabel entry.2.1,
      matchingResidual witness state.2 entry)],
    matchingResidual witness state.2 entry)

/-- The matching type history of a represented process prefix, `h_τ` of the
paper's Helper Lemma H3, as a function of `h_P`. -/
noncomputable def matchingTypeRun {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType)
    (entries : List (Environment × Label × Proc)) : TypeHistory × PactType :=
  entries.foldl (matchingTypeStep witness) ([], processType)

@[simp] theorem matchingTypeRun_nil {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType) :
    matchingTypeRun witness [] = ([], processType) := rfl

theorem matchingTypeRun_append {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType)
    (entries : List (Environment × Label × Proc))
    (entry : Environment × Label × Proc) :
    matchingTypeRun witness (entries ++ [entry]) =
      matchingTypeStep witness (matchingTypeRun witness entries) entry := by
  simp [matchingTypeRun]

/-- Helper Lemma H3 — "Matching finite strategy histories": the matching type
history is a valid represented type prefix ending at a related residual. -/
theorem matchingTypeRun_spec {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType) :
    ∀ {entries : List (Environment × Label × Proc)} {residual : Proc},
      PrefixValid process entries residual →
      TypePrefixValid processType (matchingTypeRun witness entries).1
          (matchingTypeRun witness entries).2 ∧
        witness.relation residual (matchingTypeRun witness entries).2 := by
  intro entries residual hValid
  induction hValid with
  | root => exact ⟨.root, witness.initial⟩
  | step hPrefix hStep ih =>
      obtain ⟨hValidType, hRelated⟩ := ih
      obtain ⟨hTypeStep, hRelated'⟩ :=
        matchingResidual_spec witness _ _ _ _ (witness.matchStep hRelated hStep)
      rw [matchingTypeRun_append, matchingTypeStep]
      exact ⟨hValidType.step hTypeStep, hRelated'⟩

/-- The matching type prefix of a represented process prefix. -/
noncomputable def matchingTypePrefix {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType)
    (history : ProcessPrefix process) : TypePrefix processType where
  entries := (matchingTypeRun witness history.entries).1
  residual := (matchingTypeRun witness history.entries).2
  valid := (matchingTypeRun_spec witness history.valid).1

/-- `S_P` from `S_τ`: read the matching type history off the process history,
ask the type strategy, then concretize its environment with `γ`. -/
noncomputable def concretizingStrategy {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType)
    (typeStrategy : TypeStrategy) : ProcessStrategy process :=
  fun history => concreteRepresentative
    (typeStrategy (matchingTypePrefix witness history).entries)

theorem eraseEnvironment_concretizingStrategy {process : Proc}
    {processType : PactType} (witness : ConformanceWitness process processType)
    (typeStrategy : TypeStrategy) (history : ProcessPrefix process) :
    eraseEnvironment (concretizingStrategy witness typeStrategy history) =
      typeStrategy (matchingTypePrefix witness history).entries :=
  eraseEnvironment_concreteRepresentative _

/-- Helper Lemma H4 — "Completed process logs erase to type logs".  Every
completed process log under `S_P` erases to a completed type log under `S_τ`. -/
theorem helper_h4_completed_process_logs_erase
    {process : Proc} {processType : PactType}
    (witness : ConformanceWitness process processType) (typeStrategy : TypeStrategy)
    {processLog : ProcessLog}
    (hCompleted :
      CompletedProcessLog (concretizingStrategy witness typeStrategy) processLog) :
    ∃ typeLog : TypeLog,
      CompletedTypeLog processType typeStrategy typeLog ∧
      eraseProcessLog processLog = typeLog := by
  obtain ⟨procPrefixAt, hRoot, hFollows, hRun⟩ := hCompleted
  have hSilent : eraseLabel Label.silent = TypeLabel.silent := by
    simp [eraseLabel, Label.silent, TypeLabel.silent]
  have hEmptyEnv : eraseEnvironment Environment.empty = TypeEnvironment.empty := by
    simp [eraseEnvironment, Environment.empty, TypeEnvironment.empty,
      Environment.bareImmediate]
  -- Each ordinary process step erases to an ordinary type step at the matching
  -- residual.
  have hOrdinary : ∀ n,
      OrdinaryProcessStep (concretizingStrategy witness typeStrategy) processLog
        procPrefixAt n →
      OrdinaryTypeStep processType typeStrategy (eraseProcessLog processLog)
        (fun k => matchingTypePrefix witness (procPrefixAt k)) n := by
    rintro n ⟨hEnv, hEntries, hStep⟩
    simp only [OrdinaryTypeStep]
    rw [← hEnv] at hStep
    have hRelated := (matchingTypeRun_spec witness (procPrefixAt n).valid).2
    have hExists := witness.matchStep hRelated hStep
    have hEntry :
        (matchingTypeRun witness (procPrefixAt (n + 1)).entries) =
          matchingTypeStep witness
            (matchingTypeRun witness (procPrefixAt n).entries)
            ((processLog n).1, (processLog n).2, (procPrefixAt (n + 1)).residual) := by
      rw [← hEntries, matchingTypeRun_append]
    have hResidual :
        (matchingTypePrefix witness (procPrefixAt (n + 1))).residual =
          matchingResidual witness
            (matchingTypePrefix witness (procPrefixAt n)).residual
            ((processLog n).1, (processLog n).2, (procPrefixAt (n + 1)).residual) := by
      show (matchingTypeRun witness (procPrefixAt (n + 1)).entries).2 = _
      rw [hEntry, matchingTypeStep]
      rfl
    obtain ⟨hTypeStep, -⟩ := matchingResidual_spec witness
      (matchingTypePrefix witness (procPrefixAt n)).residual
      (processLog n).1 (processLog n).2 (procPrefixAt (n + 1)).residual hExists
    refine ⟨?_, ?_, ?_⟩
    · show eraseEnvironment (processLog n).1 = _
      rw [hEnv]
      exact eraseEnvironment_concretizingStrategy witness typeStrategy _
    · show (matchingTypeRun witness (procPrefixAt n).entries).1 ++ _ =
        (matchingTypeRun witness (procPrefixAt (n + 1)).entries).1
      rw [hEntry, matchingTypeStep, hResidual]
      rfl
    · rw [hResidual]
      exact hTypeStep
  refine ⟨eraseProcessLog processLog,
    ⟨fun n => matchingTypePrefix witness (procPrefixAt n),
      by simp only [hRoot]; rfl, ?_⟩, rfl⟩
  rcases hRun with hAll | ⟨stop, hBefore, hStuck, hLogEq, hTail⟩
  · exact Or.inl fun n => hOrdinary n (hAll n)
  -- Failure completion: availability reflection makes the type side stuck too,
  -- and the absorbing suffix erases entry for entry.
  refine Or.inr ⟨stop, fun n hn => hOrdinary n (hBefore n hn), ?_, ?_, ?_⟩
  · have hRelated := (matchingTypeRun_spec witness (procPrefixAt stop).valid).2
    rintro ⟨label, target, hTypeStep⟩
    refine hStuck (witness.readyReflect hRelated ?_)
    rw [eraseEnvironment_concretizingStrategy witness typeStrategy]
    exact ⟨label, target, hTypeStep⟩
  · show (eraseEnvironment (processLog stop).1, eraseLabel (processLog stop).2) = _
    rw [hLogEq, hSilent, eraseEnvironment_concretizingStrategy witness typeStrategy]
  · intro m hm
    show (eraseEnvironment (processLog m).1, eraseLabel (processLog m).2) = _
    rw [hTail m hm, hEmptyEnv, hSilent]

/-- Helper Lemma H5 — "Honesty is preserved
by concretization".  Erasure keeps clock observations, copies the future menu
unchanged, and preserves availability (`Avail(γ(e)) = Avail(e)`), so each
honesty clause transfers index by index. -/
lemma helper_h5_honesty_preserved_by_concretization
    {processLog : ProcessLog} {typeLog : TypeLog}
    (hErase : eraseProcessLog processLog = typeLog)
    (hHonest : HonestTypeLog typeLog) :
    HonestProcessLog processLog := by
  subst hErase
  intro index
  rcases hHonest index with hTock | hAvail
  · left
    show (processLog index).2.isTock
    have hEq : (eraseProcessLog processLog index).2 = eraseLabel (processLog index).2 := rfl
    rw [hEq] at hTock
    cases hLabel : (processLog index).2 with
    | actions observations =>
        rw [hLabel] at hTock
        simp [eraseLabel, TypeLabel.isTock] at hTock
    | tock => trivial
  · right
    show (processLog (index + 1)).1.available ⊆ (processLog index).1.future
    have hAvailEq : typeAvailable (eraseEnvironment (processLog (index + 1)).1) =
        (processLog (index + 1)).1.available := by
      simp [typeAvailable, eraseEnvironment, Environment.available]
    have hFutureEq : (eraseEnvironment (processLog index).1).future =
        (processLog index).1.future := rfl
    rw [← hAvailEq, ← hFutureEq]
    exact hAvail

/-- Helper Lemma H9: one-step conformance match. -/
lemma helper_h9_one_step_conformance_match
    {process process₀ process₁ : Proc} {processType type₀ : PactType}
    {env : Environment} {label : Label}
    (witness : ConformanceWitness process processType)
    (hRelated : witness.relation process₀ type₀)
    (hStep : ProcessTransition env process₀ label process₁) :
    ∃ type₁,
      TypeTransition (eraseEnvironment env) type₀ (eraseLabel label) type₁ ∧
      witness.relation process₁ type₁ := by
  exact witness.matchStep hRelated hStep

/-- Helper Lemma H10: refinement response coherence for undecorated steps. -/
lemma helper_h10_refinement_response_coherence
    {precise abstract type₀ type₀' type₁ : PactType}
    {env : TypeEnvironment} {label : TypeLabel}
    (witness : RefinementWitness precise abstract)
    (hRelated : witness.relation type₀ type₀')
    (hStep : TypeTransition env type₀ label type₁) :
    ∃ type₁',
      TypeTransition env type₀' label type₁' ∧
      witness.relation type₁ type₁' := by
  -- Decorate the step (Helper Lemma H17), then use the response clause of
  -- refinement, which is indexed by that decoration.
  obtain ⟨offers, hDecorated⟩ := hStep.exists_decorated
  obtain ⟨type₁', hDecorated', hRelated'⟩ := witness.response hRelated hDecorated
  exact ⟨type₁', hDecorated'.1, hRelated'⟩

end

end Pact
