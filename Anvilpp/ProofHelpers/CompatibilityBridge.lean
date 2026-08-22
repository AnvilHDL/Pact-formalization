import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers

namespace Pact

noncomputable section

open Classical

lemma helper_h16_erased_step_conformance
    {process process₀ process₁ : Proc} {processType type₀ : PactType}
    {env : Environment} {label : Label}
    (witness : ConformanceWitness process processType)
    (hRelated : witness.relation process₀ type₀)
    (hStep : ProcessTransition env process₀ label process₁) :
    ∃ type₁,
      TypeTransition (eraseEnvironment env) type₀ (eraseLabel label) type₁ ∧
      witness.relation process₁ type₁ := by
  exact witness.matchStep hRelated hStep

/-- Helper Lemma H17: every type step has a decoration. -/
lemma helper_h17_every_type_step_has_decoration
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hStep : TypeTransition env source label target) :
    ∃ offers, DecoratedTypeTransition env source label offers target := by
  exact hStep.exists_decorated

/-- Log read from resolving/failure moves of a compatibility-game play. -/
def compatibilityPlayLog
    (automaton : TypeAutomaton) (play : ℕ → CompatibilityVertex) : TypeLog :=
  fun index =>
    match compatibilityStepLabel automaton (play index) (play (index + 1)) with
    | some entry => entry
    | none => (TypeEnvironment.empty, TypeLabel.silent)

/-- Helper Lemma H18: the objective monitor recognizes exactly `Ω_T`. -/
lemma helper_h18_objective_monitor
    (signature : TypeAlphabet) (initial : PactType) (progress : Finset ProcId)
    (play : ℕ → CompatibilityVertex) :
    RabinGame.Accepts (compatibilityGame signature initial progress) play ↔
      TypeWinningObjective initial progress
        (compatibilityPlayLog (compileType signature initial) play) := by
  sorry -- TODO(section7): unfold the Rabin monitor and play log.

/-- Helper Lemma H19: readiness matches outgoing automaton edges. -/
lemma helper_h19_readiness_matches_automaton_readiness
    {processType residual : PactType} {automaton : TypeAutomaton}
    {state : TypeAutomatonState} {env : TypeEnvironment}
    (correspondence : TypeAutomatonCorrespondence processType automaton)
    (hRelated : correspondence.relation residual state) :
    TypeReady env residual ↔
      ∃ label state', compiledTypeEdge automaton state env label state' := by
  sorry -- TODO(section7): use both directions of correspondence.stepIff.

/-- Helper Lemma H20: semantic strategy prefixes and compatibility-game plays
can be matched. -/
lemma helper_h20_matching_represented_prefixes_and_plays
    (signature : TypeAlphabet) (initial : PactType) (progress : Finset ProcId)
    (strategy : TypeStrategy) :
    ∃ gameStrategy : CompatibilityVertex → CompatibilityVertex, True := by
  sorry -- TODO(section7): construct the Player-0 strategy from `strategy`.

end

end Pact
