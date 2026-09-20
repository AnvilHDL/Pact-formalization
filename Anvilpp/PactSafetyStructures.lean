import Anvilpp.PactTypes.Proofs.Automata.CompileTypeLemmas

namespace Pact

noncomputable section

open Classical

/-- A relation matching decorated type transitions and automaton edges in both directions. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  forward :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      DecoratedTypeTransition env residual label offers residual' →
      ∃ state',
        automaton.HasEdge state env label offers state' ∧
        relation residual' state'
  backward :
    ∀ {residual : PactType} {state state' : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      automaton.HasEdge state env label offers state' →
      ∃ residual',
        DecoratedTypeTransition env residual label offers residual' ∧
        relation residual' state'

/-- A finite automaton path, recording the environment and label of each edge. -/
inductive AutomatonPath (automaton : TypeAutomaton) (initial : TypeAutomatonState) :
    List (TypeEnvironment × TypeLabel) → TypeAutomatonState → Prop where
  | root : AutomatonPath automaton initial [] initial
  | step {entries : List (TypeEnvironment × TypeLabel)}
      {current next : TypeAutomatonState} {env : TypeEnvironment}
      {label : TypeLabel} {offers : TypeOfferSummary} :
      AutomatonPath automaton initial entries current →
      automaton.HasEdge current env label offers next →
      AutomatonPath automaton initial (entries ++ [(env, label)]) next

/-- `AutoReady(E,q)`: some decorated edge leaves `q` under `E`. -/
def AutoReady (automaton : TypeAutomaton) (env : TypeEnvironment)
    (state : TypeAutomatonState) : Prop :=
  ∃ label offers state', automaton.HasEdge state env label offers state'

/-- A process-state relation preserving steps and agreeing on readiness under erased environments. -/
structure ProcessAutomatonCorrespondence
    (process : Proc) (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : Proc → TypeAutomatonState → Prop
  initial : relation process automaton.initial
  matchStep :
    ∀ {p₀ p₁ : Proc} {state : TypeAutomatonState}
      {env : Environment} {label : Label},
      relation p₀ state →
      ProcessTransition env p₀ label p₁ →
      ∃ state' offers,
        automaton.HasEdge state (eraseEnvironment env) (eraseLabel label) offers state' ∧
        relation p₁ state'
  readyAgree :
    ∀ {p₀ : Proc} {state : TypeAutomatonState} {env : Environment},
      relation p₀ state →
      (AutoReady automaton (eraseEnvironment env) state ↔ ProcessReady env p₀)
