import Anvilpp.PactTypes.Proofs.Syntax.PactTypeRegularityLemmas

/-!
# Erasure to the type-level observation/label/environment alphabet
-/

namespace Pact

noncomputable section

mutual
  /-- The syntactic type alphabet used by the process abstraction. -/
  def processAlphabet (process : Proc) : PactTypeAlphabet :=
    match process with
    | Proc.send msg _ process =>
        PactTypeAlphabet.union
          (PactTypeAlphabet.ofAction (msg, .send))
          (processAlphabet process)
    | Proc.recv msg _ process =>
        PactTypeAlphabet.union
          (PactTypeAlphabet.ofAction (msg, .recv))
          (processAlphabet process)
    | Proc.var _ | Proc.skip | Proc.cycle => PactTypeAlphabet.empty
    | Proc.endp _ => PactTypeAlphabet.empty
    | Proc.par left right interface =>
        PactTypeAlphabet.mergeHidden (processAlphabet left)
          (processAlphabet right) interface
    | Proc.seq left right | Proc.ifunfair _ left right =>
        PactTypeAlphabet.union (processAlphabet left) (processAlphabet right)
    | Proc.letp _ _ process => processAlphabet process
    | Proc.iffair _ _ left right =>
        PactTypeAlphabet.union (processAlphabet left) (processAlphabet right)
    | Proc.xoffer elseProcess branches | Proc.offer elseProcess branches =>
        PactTypeAlphabet.union (processAlphabet elseProcess)
          (branchesAlphabet branches)
    | Proc.recur _ body => processAlphabet body
  termination_by sizeOf process

  def branchAlphabet (branch : ChoiceBranch) : PactTypeAlphabet :=
    match branch with
    | .send msg _ process =>
        PactTypeAlphabet.union
          (PactTypeAlphabet.ofAction (msg, .send))
          (processAlphabet process)
    | .recv msg _ process =>
        PactTypeAlphabet.union
          (PactTypeAlphabet.ofAction (msg, .recv))
          (processAlphabet process)
  termination_by sizeOf branch

  def branchesAlphabet (branches : List ChoiceBranch) : PactTypeAlphabet :=
    match branches with
    | [] => PactTypeAlphabet.empty
    | branch :: rest =>
        PactTypeAlphabet.union (branchAlphabet branch) (branchesAlphabet rest)
  termination_by sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  /-- Structural, data-oblivious abstraction `abs(P)`, annotated with a fixed
  syntactic alphabet. -/
  def inferProcessWithAlphabet
      (alphabet : PactTypeAlphabet) (process : Proc) : PactType :=
    match process with
    | Proc.send msg _ process =>
        .seq alphabet (.message alphabet msg .send)
          (inferProcessWithAlphabet alphabet process)
    | Proc.recv msg _ process =>
        .seq alphabet (.message alphabet msg .recv)
          (inferProcessWithAlphabet alphabet process)
    | Proc.var name => .var alphabet name
    | Proc.skip => .skip alphabet
    | Proc.endp pid => .progress alphabet pid
    | Proc.cycle => .tock alphabet
    | Proc.par left right interface =>
        .par alphabet
          (inferProcessWithAlphabet (processAlphabet left) left)
          (inferProcessWithAlphabet (processAlphabet right) right)
          interface
    | Proc.seq left right =>
        .seq alphabet (inferProcessWithAlphabet alphabet left)
          (inferProcessWithAlphabet alphabet right)
    | Proc.letp _ _ process => inferProcessWithAlphabet alphabet process
    | Proc.ifunfair _ left right =>
        .choice alphabet (inferProcessWithAlphabet alphabet left)
          (inferProcessWithAlphabet alphabet right)
    | Proc.iffair bid _ left right =>
        .fairChoice alphabet bid (inferProcessWithAlphabet alphabet left)
          (inferProcessWithAlphabet alphabet right)
    | Proc.xoffer elseProcess branches =>
        .xoffer alphabet (inferProcessWithAlphabet alphabet elseProcess)
          (branches.map (inferBranchWithAlphabet alphabet))
    | Proc.offer elseProcess branches =>
        .offer alphabet (inferProcessWithAlphabet alphabet elseProcess)
          (branches.map (inferBranchWithAlphabet alphabet))
    | Proc.recur name body =>
        .recur alphabet name (inferProcessWithAlphabet alphabet body)
  termination_by sizeOf process

  /-- Erase a branch head and recursively abstract its continuation. -/
  def inferBranchWithAlphabet
      (alphabet : PactTypeAlphabet) (branch : ChoiceBranch) :
      BareMessage × PactType :=
    match branch with
    | .send msg _ process =>
        ((msg, .send), inferProcessWithAlphabet alphabet process)
    | .recv msg _ process =>
        ((msg, .recv), inferProcessWithAlphabet alphabet process)
  termination_by sizeOf branch
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Structural, data-oblivious abstraction `abs(P)`. -/
def inferProcess (process : Proc) : PactType :=
  inferProcessWithAlphabet (processAlphabet process) process

/-- Erase a branch head and recursively abstract its continuation. -/
def inferBranch (branch : ChoiceBranch) : BareMessage × PactType :=
  inferBranchWithAlphabet (branchAlphabet branch) branch

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
