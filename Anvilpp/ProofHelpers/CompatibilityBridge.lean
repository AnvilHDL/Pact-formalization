import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MainHelpers
import Anvilpp.ProofHelpers.ObjectiveMonitor

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

/-- Helper Lemma H19: readiness matches outgoing automaton edges. -/
lemma helper_h19_readiness_matches_automaton_readiness
    {processType residual : PactType} {automaton : TypeAutomaton}
    {state : TypeAutomatonState} {env : TypeEnvironment}
    (correspondence : TypeAutomatonCorrespondence processType automaton)
    (hRelated : correspondence.relation residual state) :
    TypeReady env residual ↔
      ∃ label state', compiledTypeEdge automaton state env label state' := by
  constructor
  · rintro ⟨label, target, hStep⟩
    obtain ⟨offers, hDecorated⟩ := hStep.exists_decorated
    obtain ⟨state', hEdge, -⟩ := correspondence.forward hRelated hDecorated
    exact ⟨label, state', offers, hEdge⟩
  · rintro ⟨label, state', offers, hEdge⟩
    obtain ⟨residual', hDecorated, -⟩ := correspondence.backward hRelated hEdge
    exact ⟨label, residual', hDecorated.1⟩

end

end Pact
