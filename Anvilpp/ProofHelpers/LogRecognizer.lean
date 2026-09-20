import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

/-- A deterministic finite-state automaton with Rabin acceptance. -/
structure FiniteRabinAutomaton (Letter : Type) : Type 1 where
  State : Type
  [finiteState : Fintype State]
  initial : State
  step : State → Letter → State
  pairs : List (Set State × Set State)

attribute [instance] FiniteRabinAutomaton.finiteState

/-- The state reached after reading the first `n` letters. -/
def FiniteRabinAutomaton.run {Letter : Type} (automaton : FiniteRabinAutomaton Letter)
    (word : ℕ → Letter) : ℕ → automaton.State
  | 0 => automaton.initial
  | n + 1 => automaton.step (automaton.run word n) (word n)

/-- Some Rabin pair has infinitely many good visits and finitely many bad visits. -/
def FiniteRabinAutomaton.Accepts {Letter : Type} (automaton : FiniteRabinAutomaton Letter)
    (word : ℕ → Letter) : Prop :=
  ∃ pair ∈ automaton.pairs,
    Set.Infinite {n | automaton.run word n ∈ pair.1} ∧
      ¬ Set.Infinite {n | automaton.run word n ∈ pair.2}

/-- Environment/label letters over a type's finite boundary alphabet. -/
abbrev TypeLogLetter (initial : PactType) :=
  {entry // entry ∈ initial.alphabet.localEnvironments ×ˢ initial.labels}

/-- Finite Rabin recognizability of the log objective over the boundary alphabet. -/
def OmegaRegular (initial : PactType) (progress : Finset ProcId) : Prop :=
  ∃ automaton : FiniteRabinAutomaton (TypeLogLetter initial),
    ∀ word, automaton.Accepts word ↔
      TypeWinningObjective initial progress (fun n => (word n).val)

end

end Pact
