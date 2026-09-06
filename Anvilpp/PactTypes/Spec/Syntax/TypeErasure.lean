import Anvilpp.PactTypes.Proofs.Syntax.PactTypeRegularityLemmas

/-!
# Erasure to the type-level observation/label/environment alphabet
-/

namespace Pact

noncomputable section

/-! ## Data-oblivious abstraction `abs(P)`

`abs((Ω,R)) = (Ω, abs_Ω(R))`: the written alphabet is read, never inferred.
A prefix and a local binding each become a sequence whose left operand is an
atomic type carrying the source alphabet. -/

mutual
  def inferProcess : Proc → PactType
    | Proc.send alphabet msg _ process =>
        .seq alphabet (.message alphabet msg .send) (inferProcess process)
    | Proc.recv alphabet msg _ process =>
        .seq alphabet (.message alphabet msg .recv) (inferProcess process)
    | Proc.var alphabet name => .var alphabet name
    | Proc.skip alphabet => .skip alphabet
    | Proc.endp alphabet pid => .progress alphabet pid
    | Proc.cycle alphabet => .tock alphabet
    | Proc.par alphabet left right interface =>
        .par alphabet (inferProcess left) (inferProcess right) interface
    | Proc.seq alphabet left right =>
        .seq alphabet (inferProcess left) (inferProcess right)
    | Proc.letp alphabet _ _ process =>
        .seq alphabet (.skip alphabet) (inferProcess process)
    | Proc.ifunfair alphabet _ left right =>
        .choice alphabet (inferProcess left) (inferProcess right)
    | Proc.iffair alphabet bid _ left right =>
        .fairChoice alphabet bid (inferProcess left) (inferProcess right)
    | Proc.xoffer alphabet elseProcess branches =>
        .xoffer alphabet (inferProcess elseProcess) (inferBranches branches)
    | Proc.offer alphabet elseProcess branches =>
        .offer alphabet (inferProcess elseProcess) (inferBranches branches)
    | Proc.recur alphabet name body =>
        .recur alphabet name (inferProcess body)
  termination_by process => sizeOf process

  /-- `abs_B(B)`: erase each branch head and abstract its continuation. -/
  def inferBranches : List ChoiceBranch → List (BareMessage × PactType)
    | [] => []
    | ChoiceBranch.send msg _ process :: rest =>
        ((msg, MessageDir.send), inferProcess process) :: inferBranches rest
    | ChoiceBranch.recv msg _ process :: rest =>
        ((msg, MessageDir.recv), inferProcess process) :: inferBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals (simp_wf; omega)
end

/-- `abs` of a single branch. -/
def inferBranch (branch : ChoiceBranch) : BareMessage × PactType :=
  (ChoiceBranch.action branch, inferProcess (ChoiceBranch.continuation branch))

/-- `Ω(abs(P)) = Ω(P)`: abstraction copies the written alphabet. -/
@[simp] theorem alphabet_inferProcess (process : Proc) :
    (inferProcess process).alphabet = process.alphabet := by
  cases process <;> simp [inferProcess, PactType.alphabet, Proc.alphabet]

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

/-- The complementary environment action needed to fire a type action. -/
def typeNeed (action : BareMessage) : BareMessage :=
  (action.1, action.2.invert)

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

  /-- Well-formedness of an environment offered to a type with fixed alphabet
  `alphabet`: both menus lie within the needs of the type's own actions. -/
  def WellFormed (env : TypeEnvironment) (alphabet : PactTypeAlphabet) : Prop :=
    (env.clock = true → env.immediate = ∅ ∧ env.future = ∅) ∧
    (env.clock = false → env.immediate ∩ env.future = ∅) ∧
    env.immediate ⊆ alphabet.actions.image typeNeed ∧
    env.future ⊆ alphabet.actions.image typeNeed

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
