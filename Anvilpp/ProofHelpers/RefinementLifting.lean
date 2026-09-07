import Anvilpp.ProofHelpers.CompatibilitySoundness

namespace Pact

noncomputable section

open Classical

/-- Helper Lemma H21: componentwise refinement lifts through a fixed
composition. -/
lemma helper_h21_componentwise_product_lifting
    {precise abstract : List PactType} {interfaces : List Interface}
    {preciseComposition abstractComposition : PactType}
    (hComponentwise : ComponentwiseRefines precise abstract)
    (hPrecise :
      composeTypes precise interfaces = some preciseComposition)
    (hAbstract :
      composeTypes abstract interfaces = some abstractComposition) :
    Refines preciseComposition abstractComposition := by
  sorry -- TODO(section7): induction on the parenthesized composition.

/-! ## Helper Lemma H22: matching histories along refinement

The same recipe as the strategy-matching construction of Helper Lemma H3,
specialized to the case where both sides range over the same environment
alphabet, so no concretization step is needed: the precise strategy simply
copies the abstract strategy's choice at the matched prefix. -/

/-- The abstract residual answering a precise step, chosen by the response
clause of refinement. -/
noncomputable def matchingAbstractResidual {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (state : PactType)
    (entry : TypeEnvironment × TypeLabel × PactType) : PactType :=
  if h : ∃ target, TypeTransition entry.1 state entry.2.1 target ∧
      witness.relation entry.2.2 target then h.choose else state

lemma matchingAbstractResidual_spec {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (state : PactType)
    (env : TypeEnvironment) (label : TypeLabel) (source target : PactType)
    (hRelated : witness.relation source state)
    (hStep : TypeTransition env source label target) :
    TypeTransition env state label
        (matchingAbstractResidual witness state (env, label, target)) ∧
      witness.relation target
        (matchingAbstractResidual witness state (env, label, target)) := by
  have hExists : ∃ answer, TypeTransition env state label answer ∧
      witness.relation target answer :=
    helper_h10_refinement_response_coherence witness hRelated hStep
  rw [matchingAbstractResidual, dif_pos hExists]
  exact hExists.choose_spec

/-- One step of the simultaneous induction: extend the matching abstract
history by the *same* entry and its chosen residual. -/
noncomputable def matchingAbstractStep {precise abstract : PactType}
    (witness : RefinementWitness precise abstract)
    (state : TypeHistory × PactType)
    (entry : TypeEnvironment × TypeLabel × PactType) : TypeHistory × PactType :=
  (state.1 ++ [(entry.1, entry.2.1, matchingAbstractResidual witness state.2 entry)],
    matchingAbstractResidual witness state.2 entry)

/-- The matching abstract history of a precise prefix. -/
noncomputable def matchingAbstractRun {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (entries : TypeHistory) :
    TypeHistory × PactType :=
  entries.foldl (matchingAbstractStep witness) ([], abstract)

@[simp] lemma matchingAbstractRun_nil {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) :
    matchingAbstractRun witness [] = ([], abstract) := rfl

lemma matchingAbstractRun_append {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (entries : TypeHistory)
    (entry : TypeEnvironment × TypeLabel × PactType) :
    matchingAbstractRun witness (entries ++ [entry]) =
      matchingAbstractStep witness (matchingAbstractRun witness entries) entry := by
  simp [matchingAbstractRun]

/-- Helper Lemma H22: the matching abstract history is a valid prefix ending at
a related residual, with the identical environment and label at every
position. -/
theorem helper_h22_matching_histories_along_refinement {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) :
    ∀ {entries : TypeHistory} {residual : PactType},
      TypePrefixValid precise entries residual →
      TypePrefixValid abstract (matchingAbstractRun witness entries).1
          (matchingAbstractRun witness entries).2 ∧
        witness.relation residual (matchingAbstractRun witness entries).2 := by
  intro entries residual hValid
  induction hValid with
  | root => exact ⟨.root, witness.initial⟩
  | step hPrefix hStep ih =>
      obtain ⟨hValidAbstract, hRelated⟩ := ih
      obtain ⟨hAbstractStep, hRelated'⟩ :=
        matchingAbstractResidual_spec witness _ _ _ _ _ hRelated hStep
      rw [matchingAbstractRun_append, matchingAbstractStep]
      exact ⟨hValidAbstract.step hAbstractStep, hRelated'⟩

/-- The matching abstract prefix, packaged. -/
noncomputable def matchingAbstractPrefix {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (history : TypePrefix precise) :
    TypePrefix abstract where
  entries := (matchingAbstractRun witness history.entries).1
  residual := (matchingAbstractRun witness history.entries).2
  valid := (helper_h22_matching_histories_along_refinement witness history.valid).1

/-- `S_Θ` from `S_Θ'`: copy the abstract strategy's choice at the matched
prefix. -/
noncomputable def refiningStrategy {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (abstractStrategy : TypeStrategy) :
    TypeStrategy :=
  fun entries => abstractStrategy (matchingAbstractRun witness entries).1

/-- Every completed log of the copying strategy is, entry for entry, a completed
log of the abstract strategy — not merely erasure-equal, since no concretization
step is involved. -/
theorem completedTypeLog_of_refining {precise abstract : PactType}
    (witness : RefinementWitness precise abstract) (abstractStrategy : TypeStrategy)
    {log : TypeLog}
    (hCompleted :
      CompletedTypeLog precise (refiningStrategy witness abstractStrategy) log) :
    CompletedTypeLog abstract abstractStrategy log := by
  obtain ⟨prefixAt, hRoot, hRun⟩ := hCompleted
  have hOrdinary : ∀ n,
      OrdinaryTypeStep precise (refiningStrategy witness abstractStrategy) log prefixAt n →
      OrdinaryTypeStep abstract abstractStrategy log
        (fun k => matchingAbstractPrefix witness (prefixAt k)) n := by
    rintro n ⟨hEnv, hEntries, hStep⟩
    simp only [OrdinaryTypeStep]
    have hRelated :=
      (helper_h22_matching_histories_along_refinement witness (prefixAt n).valid).2
    have hRun :
        matchingAbstractRun witness (prefixAt (n + 1)).entries =
          matchingAbstractStep witness (matchingAbstractRun witness (prefixAt n).entries)
            ((log n).1, (log n).2, (prefixAt (n + 1)).residual) := by
      rw [← hEntries, matchingAbstractRun_append]
    have hResidual :
        (matchingAbstractPrefix witness (prefixAt (n + 1))).residual =
          matchingAbstractResidual witness
            (matchingAbstractPrefix witness (prefixAt n)).residual
            ((log n).1, (log n).2, (prefixAt (n + 1)).residual) := by
      show (matchingAbstractRun witness (prefixAt (n + 1)).entries).2 = _
      rw [hRun, matchingAbstractStep]
      rfl
    obtain ⟨hAbstractStep, -⟩ := matchingAbstractResidual_spec witness
      (matchingAbstractPrefix witness (prefixAt n)).residual
      (log n).1 (log n).2 (prefixAt n).residual (prefixAt (n + 1)).residual hRelated
      (by rw [hEnv] at hStep ⊢; exact hStep)
    refine ⟨?_, ?_, ?_⟩
    · show (log n).1 = abstractStrategy (matchingAbstractRun witness (prefixAt n).entries).1
      rw [hEnv]; rfl
    · show (matchingAbstractRun witness (prefixAt n).entries).1 ++ _ =
        (matchingAbstractRun witness (prefixAt (n + 1)).entries).1
      rw [hRun, matchingAbstractStep, hResidual]
      rfl
    · rw [hResidual]
      exact hAbstractStep
  refine ⟨fun n => matchingAbstractPrefix witness (prefixAt n), ?_, ?_⟩
  · simp only [hRoot]; rfl
  rcases hRun with hAll | ⟨stop, hBefore, hStuck, hLogStop, hTail⟩
  · exact Or.inl fun n => hOrdinary n (hAll n)
  refine Or.inr ⟨stop, fun n hn => hOrdinary n (hBefore n hn), ?_, ?_, hTail⟩
  · -- availability: an abstract step would force a precise step
    rintro ⟨label, target, hAbstractStep⟩
    have hRelated :=
      (helper_h22_matching_histories_along_refinement witness (prefixAt stop).valid).2
    obtain ⟨offers, hDecorated⟩ := hAbstractStep.exists_decorated
    obtain ⟨preciseTarget, hPreciseStep⟩ := witness.availability hRelated hDecorated
    exact hStuck ⟨label, preciseTarget, hPreciseStep.1⟩
  · exact hLogStop

/-- Compatibility is monotone along a refinement of the whole composition: this
is Lemma 4.7 once componentwise lifting has produced the refinement. -/
theorem compatibility_monotone_of_refines {precise abstract : PactType}
    {progress : Finset ProcId}
    (hPreciseWF : TypeWellFormedIn [] precise)
    (hAbstractWF : TypeWellFormedIn [] abstract)
    (hFairIds : typeFairIds abstract ⊆ typeFairIds precise)
    (hRefines : Refines precise abstract)
    (hCompatible : TypeCompatible abstract progress) :
    TypeCompatible precise progress := by
  obtain ⟨abstractStrategy, hAbstractWins⟩ :=
    game_reduction_forward hAbstractWF hCompatible
  refine game_reduction_backward hPreciseWF
    ⟨refiningStrategy hRefines.some abstractStrategy, fun log hCompleted => ?_⟩
  obtain ⟨hHonest, hTock, hLive⟩ := hAbstractWins log
    (completedTypeLog_of_refining hRefines.some abstractStrategy hCompleted)
  exact ⟨hHonest, hTock, fun hFair => hLive fun bid hBid => hFair bid (hFairIds hBid)⟩

/-- Helper Lemma H23: refinement is reflexive. -/
lemma helper_h23_refinement_refl (processType : PactType) :
    Refines processType processType := by
  refine ⟨{
    relation := Eq
    initial := rfl
    skipIff := ?_
    availability := ?_
    response := ?_
  }⟩
  · intro left right hRelated
    subst right
    simp
  · intro left right right' env label offers hRelated hStep
    subst right
    exact ⟨right', hStep⟩
  · intro left right left' env label offers hRelated hStep
    subst right
    exact ⟨left', hStep, rfl⟩

/-- Helper Lemma H23: refinement is transitive. -/
lemma helper_h23_refinement_trans
    {left middle right : PactType}
    (hLeft : Refines left middle) (hRight : Refines middle right) :
    Refines left right := by
  sorry -- TODO(section7): compose refinement witnesses.

end

end Pact
