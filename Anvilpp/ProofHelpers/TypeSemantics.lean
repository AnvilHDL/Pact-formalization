import Anvilpp.ProofHelpers.Process

namespace Pact

noncomputable section

open Classical

/-! ## Type logs, honesty, and the semantic compatibility objective
(`pacttypes.typ`, `pactcompat.typ`) -/

abbrev TypeLog := ℕ → TypeEnvironment × TypeLabel
abbrev TypeHistory := List (TypeEnvironment × TypeLabel × PactType)
abbrev TypeStrategy := TypeHistory → TypeEnvironment

/-- A valid finite type-execution prefix, mirroring `PrefixValid`. -/
inductive TypePrefixValid (initial : PactType) :
    List (TypeEnvironment × TypeLabel) → PactType → Prop where
  | root : TypePrefixValid initial [] initial
  | step {entries : List (TypeEnvironment × TypeLabel)} {current next : PactType}
      {env : TypeEnvironment} {label : TypeLabel} :
      TypePrefixValid initial entries current →
      TypeTransition env current label next →
      TypePrefixValid initial (entries ++ [(env, label)]) next

structure TypePrefix (initial : PactType) : Type where
  entries : List (TypeEnvironment × TypeLabel)
  residual : PactType
  valid : TypePrefixValid initial entries residual

/-- Ordinary infinite runs and absorbing failure completions under a type
strategy, mirroring `CompletedProcessLog`. The strategy consumes the flat
history `TypeHistory`, not the dependent prefix, so we track both alongside
each other. -/
def CompletedTypeLog
    (initial : PactType) (strategy : TypeStrategy) (log : TypeLog) : Prop :=
  ∃ prefixAt : ℕ → TypePrefix initial,
    prefixAt 0 = ⟨[], initial, .root⟩ ∧
    ∀ n,
      (((log n).1 = strategy
          ((prefixAt n).entries.map fun entry => (entry.1, entry.2, initial)) ∧
        (prefixAt n).entries ++ [log n] = (prefixAt (n + 1)).entries ∧
        TypeTransition (log n).1 (prefixAt n).residual (log n).2
          (prefixAt (n + 1)).residual)) ∨
      ((¬ ∃ label target, TypeTransition
          (strategy ((prefixAt n).entries.map
            fun entry => (entry.1, entry.2, initial)))
          (prefixAt n).residual label target) ∧
        log n =
          (strategy ((prefixAt n).entries.map
            fun entry => (entry.1, entry.2, initial)), TypeLabel.silent) ∧
        prefixAt (n + 1) = prefixAt n ∧
        ∀ m, n < m → log m = (TypeEnvironment.empty, TypeLabel.silent))

def typeAvailable (env : TypeEnvironment) : Finset BareMessage :=
  env.immediate ∪ env.future

def HonestTypeLog (log : TypeLog) : Prop :=
  ∀ index,
    (log index).2.isTock ∨
    typeAvailable (log (index + 1)).1 ⊆ (log index).1.future

def HonestTypeStrategy (initial : PactType) (strategy : TypeStrategy) : Prop :=
  ∀ log, CompletedTypeLog initial strategy log → HonestTypeLog log

mutual
  /-- Fair-choice identifiers occurring in a type, `cal(Eta)(τ)`. -/
  def typeFairIds : PactType → Finset BranchId
    | .message _ _ _ => ∅
    | .progress _ _ => ∅
    | .tock _ => ∅
    | .skip _ => ∅
    | .var _ _ => ∅
    | .choice _ left right => typeFairIds left ∪ typeFairIds right
    | .seq _ left right => typeFairIds left ∪ typeFairIds right
    | .par _ left right _ => typeFairIds left ∪ typeFairIds right
    | .recur _ _ body => typeFairIds body
    | .fairChoice _ bid left right =>
        {bid} ∪ typeFairIds left ∪ typeFairIds right
    | .xoffer _ elseType branches =>
        typeFairIds elseType ∪ typeBranchFairIds branches
    | .offer _ elseType branches =>
        typeFairIds elseType ∪ typeBranchFairIds branches
  termination_by processType => sizeOf processType

  /-- Fair-choice identifiers occurring in a type branch list. -/
  def typeBranchFairIds : List (BareMessage × PactType) → Finset BranchId
    | [] => ∅
    | branch :: rest => typeFairIds branch.2 ∪ typeBranchFairIds rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have : sizeOf branch.2 < sizeOf branch := by rcases branch; simp_wf; omega
       simp_wf; omega)
end

def TypeObservationOccursInfinitely
    (observation : TypeObservation) (log : TypeLog) : Prop :=
  Set.Infinite {index | (log index).2.contains observation}

def TypeTockOccursInfinitely (log : TypeLog) : Prop :=
  Set.Infinite {index | (log index).2 = TypeLabel.tock}

def FairTypeLog (initial : PactType) (log : TypeLog) : Prop :=
  ∀ bid ∈ typeFairIds initial,
    (TypeObservationOccursInfinitely (.fair bid true) log ↔
      TypeObservationOccursInfinitely (.fair bid false) log)

/-- The completed-log objective `Ω_T`. -/
def TypeWinningObjective
    (initial : PactType) (progress : Finset ProcId) (log : TypeLog) : Prop :=
  HonestTypeLog log ∧
  TypeTockOccursInfinitely log ∧
  (FairTypeLog initial log →
    ∀ pid ∈ progress,
      TypeObservationOccursInfinitely (.progress pid) log)

/-- Semantic compatibility (Theorem 4.2's right-hand side): some strategy
forces `Ω_T` on every completed log. -/
def SemanticTypeCompatible (initial : PactType) (progress : Finset ProcId) : Prop :=
  ∃ strategy : TypeStrategy,
    ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log

end

end Pact
