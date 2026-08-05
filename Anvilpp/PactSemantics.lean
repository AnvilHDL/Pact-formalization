import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Anvilpp.Proc

namespace Pact

noncomputable section

/-- A finite synchronization interface. for P ||_I P -/
abbrev Interface := Finset MessageId

/-- A message identifier paired with its polarity. -/
abbrev BareMessage := MessageId × MessageDir

/-- Atomic observations that may occur together in a non-clock step. -/
inductive Observation : Type where
  | message : MessageId → MessageDir → Bool → Observation
  | resolved : MessageId → Observation
  | fair : BranchId → Bool → Observation
  | progress : ProcId → Observation
  deriving DecidableEq

/--
A Pact step label is either a set of simultaneous observations or the clock
tick
-/
inductive Label : Type where
  | actions : Finset Observation → Label
  | tock : Label
  deriving DecidableEq

namespace Label
  /-- ε-step -/
  def silent : Label := .actions ∅

  def message (msg : MessageId) (dir : MessageDir) (value : Bool) : Label :=
    .actions {Observation.message msg dir value}

  def resolved (msg : MessageId) : Label :=
    .actions {Observation.resolved msg}

  def fair (bid : BranchId) (taken : Bool) : Label :=
    .actions {Observation.fair bid taken}

  def progress (pid : ProcId) : Label :=
    .actions {Observation.progress pid}

  def isTock : Label → Prop
    | .tock => True
    | .actions _ => False

  def observations : Label → Finset Observation
    | .actions obs => obs
    | .tock => ∅

  private def messageIdsWith (wanted : MessageDir) (obs : Finset Observation) :
      Finset MessageId := by
    classical
    exact (obs.filter fun action =>
      match action with
      | .message _ dir _ => dir = wanted
      | _ => False).image fun action =>
        match action with
        | .message msg _ _ => msg
        | _ => ""

  /-- Boundary messages sent in a label. -/
  def sends : Label → Finset MessageId
    | .actions obs => messageIdsWith .send obs
    | .tock => ∅

  /-- Boundary messages received in a label. -/
  def recvs : Label → Finset MessageId
    | .actions obs => messageIdsWith .recv obs
    | .tock => ∅

  /-- `Sync_I` from the paper -/
  def Sync (interface : Interface) (left right : Label) : Prop :=
    interface ∩ left.sends = interface ∩ right.recvs ∧
    interface ∩ left.recvs = interface ∩ right.sends ∧
    (left.isTock ↔ right.isTock)

  def synced (interface : Interface) (left right : Label) : Finset MessageId :=
    (interface ∩ left.sends) ∪ (interface ∩ right.sends)

  private def isRawSyncedMessage (syncedMessages : Finset MessageId) :
      Observation → Bool
    | .message msg _ _ => msg ∈ syncedMessages
    | _ => false

  /--
  `α₁ ∪_I α₂`: hide raw interface messages and replace each synchronized
  exchange with a resolved-message observation.
  -/
  def combine (interface : Interface) : Label → Label → Label
    | .tock, .tock => .tock
    | .actions left, .actions right =>
        let syncedMessages :=
          synced interface (.actions left) (.actions right)
        let boundary :=
          (left ∪ right).filter fun obs =>
            !(isRawSyncedMessage syncedMessages obs)
        .actions (boundary ∪ syncedMessages.image Observation.resolved)
    | _, _ => silent

  def contains (label : Label) (obs : Observation) : Prop :=
    match label with
    | .actions observations => obs ∈ observations
    | .tock => False

end Label

/-! ## One-step environments -/

/-- An action offered by the environment to the process. -/
inductive Offer : Type where
  | send : MessageId → Bool → Offer
  | recv : MessageId → Offer
  deriving DecidableEq

namespace Offer

  def bare : Offer → BareMessage
    | .send msg _ => (msg, .send)
    | .recv msg => (msg, .recv)

  def messageId : Offer → MessageId
    | .send msg _ => msg
    | .recv msg => msg

end Offer

/--
The environment `(U,F)`.  `clock = true` represents the distinguished
immediate environment `{#}`; otherwise `immediate` is `U`.  Keeping the clock
flag separate makes it impossible to confuse a clock offer with a message.
-/
structure Environment : Type where
  immediate : Finset Offer
  future : Finset BareMessage
  clock : Bool
  deriving DecidableEq

namespace Environment

  def empty : Environment :=
    { immediate := ∅, future := ∅, clock := false }

  def tock : Environment :=
    { immediate := ∅, future := ∅, clock := true }

  def bareImmediate (env : Environment) : Finset BareMessage :=
    env.immediate.image Offer.bare

  /-- The well-formedness conditions on one-step environments. -/
  def WellFormed (env : Environment) : Prop :=
    (env.clock = true → env.immediate = ∅ ∧ env.future = ∅) ∧
    (env.clock = false → env.bareImmediate ∩ env.future = ∅)

  def hasRecv (env : Environment) (msg : MessageId) : Prop :=
    Offer.recv msg ∈ env.immediate

  def hasSend (env : Environment) (msg : MessageId) (value : Bool) : Prop :=
    Offer.send msg value ∈ env.immediate

  /-- Non-clock availability used by the honesty condition. -/
  def available (env : Environment) : Finset BareMessage :=
    env.bareImmediate ∪ env.future

end Environment

namespace ChoiceBranch

  /-- The complementary action that enables this branch. -/
  def need (branch : ChoiceBranch) : BareMessage :=
    (branch.getMessageId, branch.getDir.invert)

end ChoiceBranch

def branchNeeds (branches : List ChoiceBranch) : Finset BareMessage :=
  (branches.map ChoiceBranch.need).toFinset

/-- No branch need remains among the environment's future offers. -/
def Resolved (env : Environment) (branches : List ChoiceBranch) : Prop :=
  branchNeeds branches ∩ env.future = ∅

/-- No branch is enabled by an immediate environment offer. -/
def NoImmediateBranch (env : Environment) (branches : List ChoiceBranch) : Prop :=
  branchNeeds branches ∩ env.bareImmediate = ∅

/-- A branch need is present in the immediate environment. -/
def BranchEnabled (env : Environment) (branch : ChoiceBranch) : Prop :=
  ChoiceBranch.need branch ∈ env.bareImmediate

/-- Rewrite a conjunctive offer to parallel singleton exclusive offers. -/
def parallelBranches : List ChoiceBranch → Proc
  | [] => Proc.skip
  | [branch] => branch.toXOffer
  | branch :: rest => Proc.par branch.toXOffer (parallelBranches rest) ∅

/-! ## Sibling offers and local environments -/

/--
`Offers p α p' current future` is `Off(p,α,p')` from Appendix A.2.1.

Its syntax-directed definition is intentionally isolated as a proof obligation:
the paper's current/future-offer construction is mutually recursive with the
transition relation and the least fixed point `FutOff`.
-/
def Offers
    (process : Proc) (label : Label) (target : Proc)
    (current : Finset Offer) (future : Finset BareMessage) : Prop := by
  sorry

def restrictCurrent (interface : Interface) (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer => offer.messageId ∈ interface

def restrictFuture (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- `LocalEnv(E,I,sibling,α)` from Appendix A.2.1. -/
def LocalEnvironment
    (outer : Environment) (interface : Interface)
    (sibling : Proc) (label : Label) (localEnv : Environment) : Prop :=
  (outer.clock = true ∧ localEnv = Environment.tock) ∨
  (outer.clock = false ∧
    ∃ siblingTarget current future,
      Offers sibling label siblingTarget current future ∧
      localEnv.clock = false ∧
      localEnv.immediate = outer.immediate ∪ restrictCurrent interface current ∧
      localEnv.future =
        (outer.future ∪ restrictFuture interface future) \ localEnv.bareImmediate)

/-! ## Process transition system -/

/-- The updated local small-step judgment `E ⊢ P -α→ P'`. -/
@[aesop unsafe]
inductive ProcessTransition : Environment → Proc → Label → Proc → Prop where
  | send (env : Environment) (msg : MessageId) (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      env.hasRecv msg ∧
      Semantics.ExprEval expr value →
      --
      ProcessTransition env (Proc.send msg expr process) (Label.message msg .send value) process
  | send_wait (env : Environment) (msg : MessageId) (expr : Expr) (process : Proc) :
      env.WellFormed ∧
      ¬ env.hasRecv msg ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.send msg expr process)
      Label.silent
      (Proc.send msg expr process)
  | recv (env : Environment) (msg : MessageId) (var : String) (process : Proc)
      (value : Bool) :
      env.WellFormed ∧
      env.hasSend msg value →
      --
      ProcessTransition env (Proc.recv msg var process)
      (Label.message msg .recv value)
      (Semantics.procExprReplace process var value)
  | recv_wait (env : Environment) (msg : MessageId) (var : String) (process : Proc) :
      env.WellFormed ∧
      (∀ value, ¬ env.hasSend msg value) ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.recv msg var process)
      Label.silent
      (Proc.recv msg var process)
  | cycle (env : Environment) :
      env.WellFormed ∧ env.clock = true →
      --
      ProcessTransition env Proc.cycle
      Label.tock
      Proc.skip
  | cycle_wait (env : Environment) :
      env.WellFormed ∧ env.clock = false →
      --
      ProcessTransition env Proc.cycle
      Label.silent
      Proc.cycle
  | skip_seq (env : Environment) (process : Proc) :
      env.WellFormed →
      --
      ProcessTransition env (Proc.seq Proc.skip process)
      Label.silent
      process
  | skip (env : Environment) :
      env.WellFormed ∧
      env.clock = false ∧
      env.immediate = ∅ →
      --
      ProcessTransition env Proc.skip
      Label.silent
      Proc.skip
  | seq (env : Environment) (left left' right : Proc) (label : Label) :
      ProcessTransition env left
      label
      left' →
      --
      ProcessTransition env (Proc.seq left right)
      label
      (Proc.seq left' right)
  | letp (env : Environment) (var : String) (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      Semantics.ExprEval expr value →
      --
      ProcessTransition env (Proc.letp var expr process)
      Label.silent
      (Semantics.procExprReplace process var value)
  | if_true (env : Environment) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr true →
      --
      ProcessTransition env (Proc.ifunfair expr ifTrue ifFalse)
      Label.silent
      ifTrue
  | if_false (env : Environment) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr false →
      --
      ProcessTransition env (Proc.ifunfair expr ifTrue ifFalse)
      Label.silent
      ifFalse
  | fair_true (env : Environment) (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr true →
      --
      ProcessTransition env (Proc.iffair bid expr ifTrue ifFalse)
      (Label.fair bid true)
      ifTrue
  | fair_false (env : Environment) (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr false →
      --
      ProcessTransition env (Proc.iffair bid expr ifTrue ifFalse)
      (Label.fair bid false)
      ifFalse
  | progress (env : Environment) (pid : ProcId) :
      env.WellFormed →
      --
      ProcessTransition env (Proc.endp pid)
      (Label.progress pid)
      Proc.skip
  | recur (env : Environment) (var : String) (body : Proc) :
      env.WellFormed →
      --
      ProcessTransition env (Proc.recur var body)
      Label.silent
      (Semantics.procReplace body var (Proc.recur var body))
  | xoffer_send (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) (msg : MessageId) (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      ChoiceBranch.send msg expr process ∈ branches ∧
      env.hasRecv msg ∧
      Semantics.ExprEval expr value ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer elseProcess branches)
      (Label.message msg .send value)
      process
  | xoffer_recv (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) (msg : MessageId) (var : String) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      ChoiceBranch.recv msg var process ∈ branches ∧
      env.hasSend msg value ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer elseProcess branches)
      (Label.message msg .recv value)
      (Semantics.procExprReplace process var value)
  | xoffer_else (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer elseProcess branches)
      Label.silent
      elseProcess
  | xoffer_wait (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      ¬ Resolved env branches ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.xoffer elseProcess branches)
      Label.silent
      (Proc.xoffer elseProcess branches)
    -- To Do double check the offer case
  | offer_some (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) (enabled : ChoiceBranch) :
      env.WellFormed ∧
      enabled ∈ branches ∧
      BranchEnabled env enabled →
      --
      ProcessTransition env (Proc.offer elseProcess branches)
      Label.silent
      (parallelBranches branches)
  | offer_else (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.offer elseProcess branches)
      Label.silent
      elseProcess
  | offer_wait (env : Environment) (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      ¬ Resolved env branches ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.offer elseProcess branches)
      Label.silent
      (Proc.offer elseProcess branches)
  | par (outer leftEnv rightEnv : Environment) (interface : MsgIdSet) (left left' right right' : Proc) (leftLabel rightLabel : Label) :
      ProcessTransition leftEnv left leftLabel left' →
      ProcessTransition rightEnv right rightLabel right' →
      (outer.WellFormed ∧
        LocalEnvironment outer interface right rightLabel leftEnv ∧
        LocalEnvironment outer interface left leftLabel rightEnv ∧
        Label.Sync interface leftLabel rightLabel) →
      --
      ProcessTransition outer (Proc.par left right interface)
      (Label.combine interface leftLabel rightLabel)
      (Proc.par left' right' interface)
end

end Pact
