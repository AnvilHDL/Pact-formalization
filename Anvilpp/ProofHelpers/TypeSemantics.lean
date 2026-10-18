import Anvilpp.ProofHelpers.Process

namespace Pact

noncomputable section

open Classical

/-! ## Type logs, honesty, and the semantic compatibility objective
-/

abbrev TypeLog := ℕ → TypeEnvironment × TypeLabel
abbrev TypeHistory := List (TypeEnvironment × TypeLabel × PactType)
abbrev TypeStrategy := TypeHistory → TypeEnvironment

/-- A valid finite represented type-execution prefix, `hat(Pref)(Θ_0)`,
mirroring `PrefixValid`: each entry records the residual it reaches. -/
inductive TypePrefixValid (initial : PactType) :
    TypeHistory → PactType → Prop where
  | root : TypePrefixValid initial [] initial
  | step {entries : TypeHistory} {current next : PactType}
      {env : TypeEnvironment} {label : TypeLabel} :
      TypePrefixValid initial entries current →
      TypeTransition env current label next →
      TypePrefixValid initial (entries ++ [(env, label, next)]) next

structure TypePrefix (initial : PactType) : Type where
  entries : TypeHistory
  residual : PactType
  valid : TypePrefixValid initial entries residual

/-- The represented prefixes a type strategy generates, mirroring
`FollowsProcessStrategy`. -/
inductive FollowsTypeStrategy (initial : PactType) (strategy : TypeStrategy) :
    TypePrefix initial → Prop where
  | root : FollowsTypeStrategy initial strategy ⟨[], initial, .root⟩
  | step {history : TypePrefix initial} {label : TypeLabel} {next : PactType}
      (follows : FollowsTypeStrategy initial strategy history)
      (transition :
        TypeTransition (strategy history.entries) history.residual label next) :
      FollowsTypeStrategy initial strategy
        ⟨history.entries ++ [(strategy history.entries, label, next)], next,
          history.valid.step transition⟩

/-- One ordinary strategy step of a completed type log. -/
def OrdinaryTypeStep (initial : PactType) (strategy : TypeStrategy)
    (log : TypeLog) (prefixAt : ℕ → TypePrefix initial) (index : ℕ) : Prop :=
  (log index).1 = strategy (prefixAt index).entries ∧
    (prefixAt index).entries ++
        [((log index).1, (log index).2, (prefixAt (index + 1)).residual)] =
      (prefixAt (index + 1)).entries ∧
    TypeTransition (log index).1 (prefixAt index).residual (log index).2
      (prefixAt (index + 1)).residual

/-- Infinite strategy executions, including stuck prefixes completed by silent failure entries. -/
def CompletedTypeLog
    (initial : PactType) (strategy : TypeStrategy) (log : TypeLog) : Prop :=
  ∃ prefixAt : ℕ → TypePrefix initial,
    prefixAt 0 = ⟨[], initial, .root⟩ ∧
    ((∀ n, OrdinaryTypeStep initial strategy log prefixAt n) ∨
      ∃ stop,
        (∀ n, n < stop → OrdinaryTypeStep initial strategy log prefixAt n) ∧
        (¬ ∃ label target, TypeTransition (strategy (prefixAt stop).entries)
            (prefixAt stop).residual label target) ∧
        log stop = (strategy (prefixAt stop).entries, TypeLabel.silent) ∧
        ∀ m, stop < m → log m = (TypeEnvironment.empty, TypeLabel.silent))

def typeAvailable (env : TypeEnvironment) : Finset BareMessage :=
  env.immediate ∪ env.future

def HonestTypeLog (log : TypeLog) : Prop :=
  ∀ index,
    (log index).2.isTock ∨
    typeAvailable (log (index + 1)).1 ⊆ (log index).1.honestyRemainder (log index).2

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

/-- Some strategy enforces the honesty, clock, fairness, and progress objective on every completed log. -/
def SemanticTypeCompatible (initial : PactType) (progress : Finset ProcId) : Prop :=
  ∃ strategy : TypeStrategy,
    ∀ log, CompletedTypeLog initial strategy log →
      TypeWinningObjective initial progress log

end

end Pact
