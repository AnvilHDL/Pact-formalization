import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Forall2
import Anvilpp.PactSafetyStructures
import Anvilpp.ProofHelpers.Honesty
import Anvilpp.PactTypes.Proofs.Correspondence.TypeAutoRelCore
import Anvilpp.PactTypes.Proofs.Correspondence.CompileWFHelpers

namespace Pact

noncomputable section

open Classical

/-! ## Process strategies, safety, and liveness (`procSem.typ`, "Safety and
compatibility") -/

/-- A finite execution from `initial`, recording each environment, label, and target residual. -/
inductive PrefixValid (initial : Proc) :
    List (Environment × Label × Proc) → Proc → Prop where
  | root : PrefixValid initial [] initial
  | step {entries : List (Environment × Label × Proc)} {current next : Proc}
      {env : Environment} {label : Label} :
      PrefixValid initial entries current →
      ProcessTransition env current label next →
      PrefixValid initial (entries ++ [(env, label, next)]) next

structure ProcessPrefix (initial : Proc) : Type where
  entries : List (Environment × Label × Proc)
  residual : Proc
  valid : PrefixValid initial entries residual

/-- A history-sensitive open-system environment strategy, `S_Q`. -/
abbrev ProcessStrategy (initial : Proc) := ProcessPrefix initial → Environment

/-- The prefix is built by always taking the strategy-selected environment:
`S_Q ⊢ ρ_k →^{α_k} ρ_{k+1} iff S_Q(ρ_k) ⊢ Q_k →^{α_k} Q_{k+1}`. -/
inductive FollowsProcessStrategy {initial : Proc}
    (strategy : ProcessStrategy initial) : ProcessPrefix initial → Prop where
  | root : FollowsProcessStrategy strategy ⟨[], initial, .root⟩
  | step {history : ProcessPrefix initial} {label : Label} {next : Proc}
      (follows : FollowsProcessStrategy strategy history)
      (transition :
        ProcessTransition (strategy history) history.residual label next) :
      FollowsProcessStrategy strategy
        ⟨history.entries ++ [(strategy history, label, next)], next,
          history.valid.step transition⟩

/-- A completed infinite process log, including the failure completion. -/
abbrev ProcessLog := ℕ → Environment × Label

/-- Definition A.2: no transition is available under `env`. -/
def Stuck (env : Environment) (process : Proc) : Prop :=
  ¬ ∃ label target, ProcessTransition env process label target

/-- One ordinary strategy step of a completed log: the entry records the
strategy's environment and a genuine transition to the next residual. -/
def OrdinaryProcessStep {initial : Proc} (strategy : ProcessStrategy initial)
    (log : ProcessLog) (prefixAt : ℕ → ProcessPrefix initial) (index : ℕ) : Prop :=
  (log index).1 = strategy (prefixAt index) ∧
    (prefixAt index).entries ++
        [((log index).1, (log index).2, (prefixAt (index + 1)).residual)] =
      (prefixAt (index + 1)).entries ∧
    ProcessTransition (strategy (prefixAt index)) (prefixAt index).residual
      (log index).2 (prefixAt (index + 1)).residual

/-- Infinite strategy logs, including stuck prefixes followed by one failed entry
and an infinite empty-environment, silent-label suffix. -/
def CompletedProcessLog {initial : Proc}
    (strategy : ProcessStrategy initial) (log : ProcessLog) : Prop :=
  ∃ prefixAt : ℕ → ProcessPrefix initial,
    prefixAt 0 = ⟨[], initial, .root⟩ ∧
    (∀ n, FollowsProcessStrategy strategy (prefixAt n)) ∧
    ((∀ n, OrdinaryProcessStep strategy log prefixAt n) ∨
      ∃ stop,
        (∀ n, n < stop → OrdinaryProcessStep strategy log prefixAt n) ∧
        Stuck (strategy (prefixAt stop)) (prefixAt stop).residual ∧
        log stop = (strategy (prefixAt stop), Label.silent) ∧
        ∀ m, stop < m → log m = (Environment.empty, Label.silent))

/-- Between clocks, an environment retains only promises and unconsumed immediate offers. -/
def HonestProcessLog (log : ProcessLog) : Prop :=
  ∀ index,
    (log index).2.isTock ∨
    (log (index + 1)).1.available ⊆ (log index).1.honestyRemainder (log index).2

def HonestProcessStrategy {initial : Proc}
    (strategy : ProcessStrategy initial) : Prop :=
  ∀ log, CompletedProcessLog strategy log → HonestProcessLog log

/-- Definition A.3: no strategy-reachable residual is stuck. -/
def SyncCompatible {initial : Proc} (strategy : ProcessStrategy initial) : Prop :=
  ∀ historyPrefix,
    FollowsProcessStrategy strategy historyPrefix →
    ¬ Stuck (strategy historyPrefix) historyPrefix.residual

mutual
  /-- Fair-choice identifiers occurring in a process, `cal(Eta)(P)`. -/
  def processFairIds : Proc → Finset BranchId
    | .send _ _ _ p => processFairIds p
    | .recv _ _ _ p => processFairIds p
    | .var _ _ => ∅
    | .skip _ => ∅
    | .endp _ _ => ∅
    | .cycle _ => ∅
    | .par _ left right _ => processFairIds left ∪ processFairIds right
    | .seq _ left right => processFairIds left ∪ processFairIds right
    | .letp _ _ _ p => processFairIds p
    | .ifunfair _ _ left right => processFairIds left ∪ processFairIds right
    | .iffair _ bid _ left right =>
        {bid} ∪ processFairIds left ∪ processFairIds right
    | .xoffer _ elseProcess branches =>
        processFairIds elseProcess ∪ processBranchFairIds branches
    | .offer _ elseProcess branches =>
        processFairIds elseProcess ∪ processBranchFairIds branches
    | .recur _ _ body => processFairIds body
  termination_by process => sizeOf process

  /-- Fair-choice identifiers occurring in a branch list. -/
  def processBranchFairIds : List ChoiceBranch → Finset BranchId
    | [] => ∅
    | branch :: rest =>
        processFairIds (ChoiceBranch.continuation branch) ∪
          processBranchFairIds rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have := ChoiceBranch.continuation_sizeOf_lt branch; simp_wf; omega)
end

mutual
  /-- Progress identifiers occurring in a process, `cal(T)(P)`. -/
  def processProgressIds : Proc → Finset ProcId
    | .send _ _ _ p => processProgressIds p
    | .recv _ _ _ p => processProgressIds p
    | .var _ _ => ∅
    | .skip _ => ∅
    | .endp _ pid => {pid}
    | .cycle _ => ∅
    | .par _ left right _ => processProgressIds left ∪ processProgressIds right
    | .seq _ left right => processProgressIds left ∪ processProgressIds right
    | .letp _ _ _ p => processProgressIds p
    | .ifunfair _ _ left right =>
        processProgressIds left ∪ processProgressIds right
    | .iffair _ _ _ left right =>
        processProgressIds left ∪ processProgressIds right
    | .xoffer _ elseProcess branches =>
        processProgressIds elseProcess ∪ processBranchProgressIds branches
    | .offer _ elseProcess branches =>
        processProgressIds elseProcess ∪ processBranchProgressIds branches
    | .recur _ _ body => processProgressIds body
  termination_by process => sizeOf process

  /-- Progress identifiers occurring in a branch list. -/
  def processBranchProgressIds : List ChoiceBranch → Finset ProcId
    | [] => ∅
    | branch :: rest =>
        processProgressIds (ChoiceBranch.continuation branch) ∪
          processBranchProgressIds rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have := ChoiceBranch.continuation_sizeOf_lt branch; simp_wf; omega)
end

def ObservationOccursInfinitely
    (observation : Observation) (log : ProcessLog) : Prop :=
  Set.Infinite {index | (log index).2.contains observation}

def TockOccursInfinitely (log : ProcessLog) : Prop :=
  Set.Infinite {index | (log index).2 = Label.tock}

/-- Definition A.5: each fair branch takes both outcomes infinitely often together. -/
def FairProcessLog (initial : Proc) (log : ProcessLog) : Prop :=
  ∀ bid ∈ processFairIds initial,
    (ObservationOccursInfinitely (.fair bid true) log ↔
      ObservationOccursInfinitely (.fair bid false) log)

/-- Definition A.6: clock progress, plus marker progress on fair logs. -/
def Live {initial : Proc} (strategy : ProcessStrategy initial)
    (progress : Finset ProcId) : Prop :=
  ∀ log,
    CompletedProcessLog strategy log →
    TockOccursInfinitely log ∧
      (FairProcessLog initial log →
        ∀ pid ∈ progress,
          ObservationOccursInfinitely (.progress pid) log)

/-- `ProcJoin_{S,T}`: synchronization safety together with liveness. -/
def ProcJoin {initial : Proc} (strategy : ProcessStrategy initial)
    (progress : Finset ProcId) : Prop :=
  SyncCompatible strategy ∧ Live strategy progress

/-- `Compatible(Q_0,T)` (Definition 3.6/A.4): communication safety of a fixed
composition. -/
def ProcessCompatible (initial : Proc) (progress : Finset ProcId) : Prop :=
  ∃ strategy : ProcessStrategy initial,
    HonestProcessStrategy strategy ∧
    ProcJoin strategy progress

end

end Pact
