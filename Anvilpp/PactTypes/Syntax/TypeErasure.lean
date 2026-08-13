import Anvilpp.PactTypes.Syntax.PactTypeRegularity

/-!
# Erasure to the type-level observation/label/environment alphabet
-/

namespace Pact

noncomputable section

mutual
/-- Structural, data-oblivious abstraction `abs(P)`-/
  def inferProcess (process : Proc) : PactType :=
    match process with
    | Proc.send msg _ p =>
        .seq (.message msg .send) (inferProcess p)
    | Proc.recv msg _ p =>
        .seq (.message msg .recv) (inferProcess p)
    | Proc.var name => .var name
    | Proc.skip => .skip
    | Proc.endp pid => .progress pid
    | Proc.cycle => .tock
    | Proc.par left right interface =>
        .par (inferProcess left) (inferProcess right) interface
    | Proc.seq left right =>
        .seq (inferProcess left) (inferProcess right)
    | Proc.letp _ _ p => inferProcess p
    | Proc.ifunfair _ left right =>
        .choice (inferProcess left) (inferProcess right)
    | Proc.iffair bid _ left right =>
        .fairChoice bid (inferProcess left) (inferProcess right)
    | Proc.xoffer elseType branches =>
        .xoffer (inferProcess elseType) (branches.map inferBranch)
    | Proc.offer elseType branches =>
        .offer (inferProcess elseType) (branches.map inferBranch)
    | Proc.recur name body => .recur name (inferProcess body)

  /-- Erase a branch head and recursively abstract its continuation. -/
  def inferBranch : ChoiceBranch → BareMessage × PactType
    | .send msg _ process => ((msg, .send), inferProcess process)
    | .recv msg _ process => ((msg, .recv), inferProcess process)

end

inductive TypeObservation : Type where
  | message : MessageId → MessageDir → TypeObservation
  | resolved : MessageId → TypeObservation
  | fair : BranchId → Bool → TypeObservation
  | progress : ProcId → TypeObservation
  deriving DecidableEq

inductive TypeLabel : Type where
  | actions : Finset TypeObservation → TypeLabel
  | tock : TypeLabel
  deriving DecidableEq

namespace TypeLabel

  def silent : TypeLabel := .actions ∅

  def message (msg : MessageId) (dir : MessageDir) : TypeLabel :=
    .actions {TypeObservation.message msg dir}

  def fair (bid : BranchId) (taken : Bool) : TypeLabel :=
    .actions {TypeObservation.fair bid taken}

  def progress (pid : ProcId) : TypeLabel :=
    .actions {TypeObservation.progress pid}

  def isTock : TypeLabel → Prop
    | .tock => True
    | .actions _ => False

  def contains (label : TypeLabel) (obs : TypeObservation) : Prop :=
    match label with
    | .actions observations => obs ∈ observations
    | .tock => False

  def messageIdsWith (wanted : MessageDir)
      (observations : Finset TypeObservation) : Finset MessageId := by
    classical
    exact (observations.filter fun observation =>
      match observation with
      | .message _ dir => dir = wanted
      | _ => False).image fun observation =>
        match observation with
        | .message msg _ => msg
        | _ => ""

  def sends : TypeLabel → Finset MessageId
    | .actions observations => messageIdsWith .send observations
    | .tock => ∅

  def recvs : TypeLabel → Finset MessageId
    | .actions observations => messageIdsWith .recv observations
    | .tock => ∅

  /-- The erased synchronization predicate `Sync_I`. -/
  def Sync (interface : Interface) (left right : TypeLabel) : Prop :=
    interface ∩ left.sends = interface ∩ right.recvs ∧
    interface ∩ left.recvs = interface ∩ right.sends ∧
    (left.isTock ↔ right.isTock)

  def synced (interface : Interface) (left right : TypeLabel) : Finset MessageId :=
    (interface ∩ left.sends) ∪ (interface ∩ right.sends)

  def isRawSyncedMessage (syncedMessages : Finset MessageId) :
      TypeObservation → Bool
    | .message msg _ => msg ∈ syncedMessages
    | _ => false

  /-- The erased label combination `α₁ ∪_I α₂`. -/
  def combine (interface : Interface) : TypeLabel → TypeLabel → TypeLabel
    | .tock, .tock => .tock
    | .actions left, .actions right =>
        let syncedMessages := synced interface (.actions left) (.actions right)
        let boundary :=
          (left ∪ right).filter fun observation =>
            !(isRawSyncedMessage syncedMessages observation)
        .actions (boundary ∪ syncedMessages.image TypeObservation.resolved)
    | _, _ => silent

end TypeLabel

def eraseObservation : Observation → TypeObservation
  | .message msg dir _ => .message msg dir
  | .resolved msg => .resolved msg
  | .fair bid taken => .fair bid taken
  | .progress pid => .progress pid

/-- Payload erasure on process labels. -/
def eraseLabel : Label → TypeLabel
  | .actions observations => .actions (observations.image eraseObservation)
  | .tock => .tock

/-- A value-erased one-step environment. -/
structure TypeEnvironment : Type where
  immediate : Finset BareMessage
  future : Finset BareMessage
  clock : Bool
  deriving DecidableEq

namespace TypeEnvironment

  def empty : TypeEnvironment :=
    { immediate := ∅, future := ∅, clock := false }

  def tock : TypeEnvironment :=
    { immediate := ∅, future := ∅, clock := true }

  def WellFormed (env : TypeEnvironment) : Prop :=
    (env.clock = true → env.immediate = ∅ ∧ env.future = ∅) ∧
    (env.clock = false → env.immediate ∩ env.future = ∅)

  def hasNeed (env : TypeEnvironment) (action : BareMessage) : Prop :=
    (action.1, action.2.invert) ∈ env.immediate

end TypeEnvironment

/-- Erasure lifted to one-step environments. -/
def eraseEnvironment (env : Environment) : TypeEnvironment :=
  { immediate := env.bareImmediate
    future := env.future
    clock := env.clock }

end

end Pact
