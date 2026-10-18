import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Anvilpp.Proc

namespace Pact

noncomputable section

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

  def messageIdsWith (wanted : MessageDir) (obs : Finset Observation) :
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

  /-- Synchronization on the interface `I`. -/
  def Sync (interface : Interface) (left right : Label) : Prop :=
    interface ∩ left.sends = interface ∩ right.recvs ∧
    interface ∩ left.recvs = interface ∩ right.sends ∧
    (left.isTock ↔ right.isTock)

  def synced (interface : Interface) (left right : Label) : Finset MessageId :=
    (interface ∩ left.sends) ∪ (interface ∩ right.sends)

  def isRawSyncedMessage (syncedMessages : Finset MessageId) :
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

  /-- `E ∈ Env_P`: the well-formedness conditions on one-step environments,
  including the blanket premise that the environment ranges over the
  complement of the process's written alphabet. -/
  def WellFormed (env : Environment) (alphabet : PactTypeAlphabet) : Prop :=
    (env.clock = true → env.immediate = ∅ ∧ env.future = ∅) ∧
    (env.clock = false → env.bareImmediate ∩ env.future = ∅) ∧
    env.bareImmediate ⊆ alphabet.actions.image bareNeed ∧
    env.future ⊆ alphabet.actions.image bareNeed

  def hasRecv (env : Environment) (msg : MessageId) : Prop :=
    Offer.recv msg ∈ env.immediate

  def hasSend (env : Environment) (msg : MessageId) (value : Bool) : Prop :=
    Offer.send msg value ∈ env.immediate

  /-- Non-clock availability used by the honesty condition. -/
  def available (env : Environment) : Finset BareMessage :=
    env.bareImmediate ∪ env.future

end Environment


/-! ## Offer heads and branch predicates -/

namespace ChoiceBranch

  /-- `Label(a)`: the concrete offer a branch head exposes.  A send retains
  its evaluated payload; a receive exposes only its demand. -/
  def offer (branch : ChoiceBranch) : Offer :=
    match branch with
    | ChoiceBranch.send msg expr _ =>
        Offer.send msg ((Semantics.exprEvalOpt expr).getD false)
    | ChoiceBranch.recv msg _ _ => Offer.recv msg

end ChoiceBranch

/-- `Need(B)`. -/
def branchNeeds (branches : List ChoiceBranch) : Finset BareMessage :=
  (branches.map ChoiceBranch.need).toFinset

/-- `Act_B` as bare actions. -/
def branchActions (branches : List ChoiceBranch) : Finset BareMessage :=
  (branches.map ChoiceBranch.action).toFinset

/-- `Act_B` as concrete offers. -/
def branchOfferSet (branches : List ChoiceBranch) : Finset Offer :=
  (branches.map ChoiceBranch.offer).toFinset

/-- Project concrete offers by their polarized message, retaining payloads. -/
def projectCurrent (alphabet : PactTypeAlphabet) (offers : Finset Offer) :
    Finset Offer :=
  offers.filter fun offer => offer.bare ∈ alphabet.actions

/-- `Resolved(E,B)`: no branch need remains among the future offers. -/
def Resolved (env : Environment) (branches : List ChoiceBranch) : Prop :=
  branchNeeds branches ∩ env.future = ∅

/-- No branch is enabled by an immediate environment offer. -/
def NoImmediateBranch (env : Environment) (branches : List ChoiceBranch) : Prop :=
  branchNeeds branches ∩ env.bareImmediate = ∅

/-- A branch need is present in the immediate environment. -/
def BranchEnabled (env : Environment) (branch : ChoiceBranch) : Prop :=
  ChoiceBranch.need branch ∈ env.bareImmediate

/-- Every branch head is declared by the written alphabet. -/
def BranchesDeclared (alphabet : PactTypeAlphabet)
    (branches : List ChoiceBranch) : Prop :=
  ∀ branch ∈ branches, ChoiceBranch.action branch ∈ alphabet.actions

/-- Boolean companion to `BranchesDeclared`, for the menu definitions. -/
def branchesDeclared (alphabet : PactTypeAlphabet)
    (branches : List ChoiceBranch) : Bool :=
  branches.all fun branch => decide (ChoiceBranch.action branch ∈ alphabet.actions)

/-- `W(E,B)`: branch actions the future environment still promises. -/
def waitingOffers (env : Environment) (branches : List ChoiceBranch) :
    Finset BareMessage :=
  env.future.image bareNeed ∩ branchActions branches

/-- The concrete witness set behind `W(E,B)`. -/
def waitingOfferSet (env : Environment) (branches : List ChoiceBranch) :
    Finset Offer :=
  ((branches.filter fun branch =>
      decide (ChoiceBranch.action branch ∈ waitingOffers env branches)).map
    ChoiceBranch.offer).toFinset

/-! ## Interface restriction and hiding -/

def restrictCurrent (interface : Interface) (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer => offer.messageId ∈ interface

def restrictFuture (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- `hide_I` on bare offers. -/
def hideProcOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

/-- `hide_I` on concrete offers. -/
def hideOfferSet (interface : Interface) (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer => offer.messageId ∉ interface

/-! ## Conjunctive commitment

`C^P_(B,a_j)`: the selected branch performs its head action; every other
branch becomes a singleton exclusive offer with a `skip` default. -/

def parallelProcessBranchesWithin (alphabet : PactTypeAlphabet) :
    List ChoiceBranch → Proc
  | [] => Proc.skip alphabet
  | [branch] => ChoiceBranch.toXOffer alphabet branch
  | branch :: rest =>
      Proc.par alphabet (ChoiceBranch.toXOffer alphabet branch)
        (parallelProcessBranchesWithin alphabet rest) ∅

/-- The committed form of the selected branch: it drops the synthetic
singleton offer and performs its head. -/
def selectedProcessBranchAt (alphabet : PactTypeAlphabet)
    (branch : ChoiceBranch) : Proc :=
  match branch with
  | ChoiceBranch.send msg expr process => Proc.send alphabet msg expr process
  | ChoiceBranch.recv msg varName process => Proc.recv alphabet msg varName process

def parallelProcessBranchesSelectingWithin (alphabet : PactTypeAlphabet)
    (selected : ChoiceBranch) : List ChoiceBranch → Proc
  | [] => Proc.skip alphabet
  | [branch] =>
      if branch = selected then selectedProcessBranchAt alphabet branch
      else ChoiceBranch.toXOffer alphabet branch
  | branch :: rest =>
      if branch = selected then
        Proc.par alphabet (selectedProcessBranchAt alphabet branch)
          (parallelProcessBranchesWithin alphabet rest) ∅
      else
        Proc.par alphabet (ChoiceBranch.toXOffer alphabet branch)
          (parallelProcessBranchesSelectingWithin alphabet selected rest) ∅

def parallelProcessBranchesSelecting (alphabet : PactTypeAlphabet)
    (selected : ChoiceBranch) : List ChoiceBranch → Proc
  | [] => Proc.skip PactTypeAlphabet.empty
  | branch :: rest =>
      parallelProcessBranchesSelectingWithin alphabet selected (branch :: rest)

/-! ## Optimistic completion

`canCompleteThisCycle(P)`. The test is independent of alphabet annotations. -/

mutual
  def Proc.CanCompleteBeforeTock : Proc → Bool
    | .send _ _ _ p | .recv _ _ _ p => Proc.CanCompleteBeforeTock p
    | .skip _ | .endp _ _ => true
    | .cycle _ | .var _ _ => false
    | .recur _ _ body => Proc.CanCompleteBeforeTock body
    | .par _ left right _ | .seq _ left right =>
        Proc.CanCompleteBeforeTock left && Proc.CanCompleteBeforeTock right
    | .letp _ _ _ p => Proc.CanCompleteBeforeTock p
    | .ifunfair _ _ left right | .iffair _ _ _ left right =>
        Proc.CanCompleteBeforeTock left || Proc.CanCompleteBeforeTock right
    | .xoffer _ elseProcess branches
    | .offer _ elseProcess branches =>
        Proc.CanCompleteBeforeTock elseProcess ||
          Proc.BranchCanCompleteBeforeTock branches
  termination_by process => sizeOf process

  def Proc.BranchCanCompleteBeforeTock : List ChoiceBranch → Bool
    | [] => false
    | branch :: rest =>
        Proc.CanCompleteBeforeTock (ChoiceBranch.continuation branch) ||
          Proc.BranchCanCompleteBeforeTock rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have hBranch := ChoiceBranch.continuation_sizeOf_lt branch
       simp_wf
       omega)
end

/-! ## Future-offer menu

`FutOff(P)`, with advertised heads projected to their written alphabet. -/

def procFutureOffersFuel : Nat → Proc → Finset BareMessage
  | 0, _ => ∅
  | fuel + 1, process =>
      match process with
      | Proc.send alphabet msg _ p =>
          ({(msg, MessageDir.send)} ∩ alphabet.actions) ∪
            procFutureOffersFuel fuel p
      | Proc.recv alphabet msg _ p =>
          ({(msg, MessageDir.recv)} ∩ alphabet.actions) ∪
            procFutureOffersFuel fuel p
      | Proc.var _ _ => ∅
      | Proc.skip _ => ∅
      | Proc.endp _ _ => ∅
      | Proc.cycle _ => ∅
      | Proc.recur _ _ body => procFutureOffersFuel fuel body
      | Proc.par _ left right interface =>
          hideProcOffers interface
            (procFutureOffersFuel fuel left ∪ procFutureOffersFuel fuel right)
      | Proc.seq _ left right =>
          if Proc.CanCompleteBeforeTock left then
            procFutureOffersFuel fuel left ∪ procFutureOffersFuel fuel right
          else procFutureOffersFuel fuel left
      | Proc.letp _ _ _ p' => procFutureOffersFuel fuel p'
      | Proc.ifunfair _ _ left right | Proc.iffair _ _ _ left right =>
          procFutureOffersFuel fuel left ∪ procFutureOffersFuel fuel right
      | Proc.xoffer alphabet elseProcess branches
      | Proc.offer alphabet elseProcess branches =>
          (branches.foldl (fun offers branch =>
              offers ∪ {ChoiceBranch.action branch} ∪
                procFutureOffersFuel fuel (ChoiceBranch.continuation branch))
              (procFutureOffersFuel fuel elseProcess)) ∩ alphabet.actions

/-- All message actions that may still be offered before the next clock. -/
def procFutureOffers (process : Proc) : Finset BareMessage :=
  procFutureOffersFuel (sizeOf process + 1) process

/-- `F_2` of the sequence offer clause: the right operand's menu, admitted
when the left operand passes the optimistic completion test at the source. -/
def procSequenceRightMenu (left right : Proc) : Finset BareMessage :=
  if Proc.CanCompleteBeforeTock left then procFutureOffers right else ∅

/-!
## Offer menu and local parallel environments

`Off(E,P,α,P')` and `LocalEnv(E,I,P_i,O_C,O_F)`, the concrete counterparts of
`TypeOffers` and `LocalTypeOfferEnvironment`, mirrored constructor for
constructor.  The local environment is indexed by the sibling's own offer
pair, which rules out justifying it by a different witness than the step uses.
-/

inductive LocalOfferEnvironment :
    Environment → Interface → Proc → Environment →
      Finset Offer → Finset BareMessage → Environment → Prop where
  | clock (outer : Environment) (interface : Interface)
      (localProc : Proc) (current : Finset Offer) (future : Finset BareMessage) :
      outer.clock = true →
      LocalOfferEnvironment outer interface localProc Environment.tock
        current future Environment.tock
  | ordinary (outer siblingEnv localEnv : Environment)
      (interface : Interface) (localProc : Proc)
      (current : Finset Offer) (future : Finset BareMessage) :
      outer.clock = false →
      siblingEnv.clock = false →
      localEnv.clock = false →
      localEnv.immediate =
        outer.immediate ∪ restrictCurrent interface current →
      localEnv.future =
        (outer.future ∪ restrictFuture interface future) \
          localEnv.bareImmediate →
      LocalOfferEnvironment outer interface localProc siblingEnv current
        future localEnv

@[aesop unsafe]
inductive Offers :
    Environment → Proc → Label → Proc →
      Finset Offer → Finset BareMessage → Prop where
  | send (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
      (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧ env.hasRecv msg ∧
        Semantics.ExprEval expr value →
      Offers env (Proc.send alphabet msg expr process)
        (Label.message msg .send value) process
        (projectCurrent alphabet {Offer.send msg value})
        (procFutureOffers process \ ({(msg, MessageDir.send)} ∩ alphabet.actions))
  | send_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧ ¬ env.hasRecv msg ∧ env.clock = false ∧
        Semantics.ExprEval expr value →
      Offers env (Proc.send alphabet msg expr process) Label.silent
        (Proc.send alphabet msg expr process)
        (projectCurrent alphabet {Offer.send msg value})
        (procFutureOffers (Proc.send alphabet msg expr process) \
          ({(msg, MessageDir.send)} ∩ alphabet.actions))
  | recv (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
      (varName : String) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧ env.hasSend msg value →
      Offers env (Proc.recv alphabet msg varName process)
        (Label.message msg .recv value)
        (Semantics.procExprReplace process varName value)
        (projectCurrent alphabet {Offer.recv msg})
        (procFutureOffers (Semantics.procExprReplace process varName value) \
          ({(msg, MessageDir.recv)} ∩ alphabet.actions))
  | recv_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (varName : String) (process : Proc) :
      env.WellFormed alphabet ∧ (∀ value, ¬ env.hasSend msg value) ∧
        env.clock = false →
      Offers env (Proc.recv alphabet msg varName process) Label.silent
        (Proc.recv alphabet msg varName process)
        (projectCurrent alphabet {Offer.recv msg})
        (procFutureOffers (Proc.recv alphabet msg varName process) \
          ({(msg, MessageDir.recv)} ∩ alphabet.actions))
  | cycle (env : Environment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧ env.clock = true →
      Offers env (Proc.cycle alphabet) Label.tock (Proc.skip alphabet) ∅ ∅
  | cycle_wait (env : Environment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧ env.clock = false →
      Offers env (Proc.cycle alphabet) Label.silent (Proc.cycle alphabet) ∅
        (procFutureOffers (Proc.cycle alphabet))
  | skip (env : Environment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧ env.clock = false →
      Offers env (Proc.skip alphabet) Label.silent (Proc.skip alphabet) ∅
        (procFutureOffers (Proc.skip alphabet))
  | progress (env : Environment) (alphabet : PactTypeAlphabet) (pid : ProcId) :
      env.WellFormed alphabet ∧ env.clock = false →
      Offers env (Proc.endp alphabet pid) (Label.progress pid)
        (Proc.skip alphabet) ∅ (procFutureOffers (Proc.skip alphabet))
  | letp (env : Environment) (alphabet : PactTypeAlphabet) (varName : String)
      (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        Semantics.ExprEval expr value →
      Offers env (Proc.letp alphabet varName expr process) Label.silent
        (Semantics.procExprReplace process varName value) ∅
        (procFutureOffers (Semantics.procExprReplace process varName value))
  | if_true (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
      (ifTrue ifFalse : Proc) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        Semantics.ExprEval expr true →
      Offers env (Proc.ifunfair alphabet expr ifTrue ifFalse) Label.silent
        ifTrue ∅
        (procFutureOffers (Proc.ifunfair alphabet expr ifTrue ifFalse))
  | if_false (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
      (ifTrue ifFalse : Proc) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        Semantics.ExprEval expr false →
      Offers env (Proc.ifunfair alphabet expr ifTrue ifFalse) Label.silent
        ifFalse ∅
        (procFutureOffers (Proc.ifunfair alphabet expr ifTrue ifFalse))
  | fair_true (env : Environment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        Semantics.ExprEval expr true →
      Offers env (Proc.iffair alphabet bid expr ifTrue ifFalse)
        (Label.fair bid true) ifTrue ∅
        (procFutureOffers (Proc.iffair alphabet bid expr ifTrue ifFalse))
  | fair_false (env : Environment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        Semantics.ExprEval expr false →
      Offers env (Proc.iffair alphabet bid expr ifTrue ifFalse)
        (Label.fair bid false) ifFalse ∅
        (procFutureOffers (Proc.iffair alphabet bid expr ifTrue ifFalse))
  | recur (env : Environment) (alphabet : PactTypeAlphabet) (varName : String)
      (body : Proc) :
      env.WellFormed alphabet ∧ env.clock = false →
      Offers env (Proc.recur alphabet varName body) Label.silent
        (Semantics.procReplace body varName (Proc.recur alphabet varName body)) ∅
        (procFutureOffers
          (Semantics.procReplace body varName (Proc.recur alphabet varName body)))
  | seq (env : Environment) (alphabet : PactTypeAlphabet)
      (left left' right : Proc) (label : Label)
      (current : Finset Offer) (childFuture : Finset BareMessage) :
      Offers env left label left' current childFuture →
      left' ≠ Proc.skip left'.alphabet →
      label ≠ Label.tock →
      Offers env (Proc.seq alphabet left right) label
        (Proc.seq alphabet left' right) current
        ((childFuture ∪ procSequenceRightMenu left right) \
          current.image Offer.bare)
  | seq_tock (env : Environment) (alphabet : PactTypeAlphabet)
      (left left' right : Proc)
      (current : Finset Offer) (childFuture : Finset BareMessage) :
      Offers env left Label.tock left' current childFuture →
      left' ≠ Proc.skip left'.alphabet →
      Offers env (Proc.seq alphabet left right) Label.tock
        (Proc.seq alphabet left' right) ∅ ∅
  | seq_fuse (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet)
      (left right : Proc) (label : Label)
      (current : Finset Offer) (childFuture : Finset BareMessage) :
      Offers env left label (Proc.skip skipAlphabet) current childFuture →
      label ≠ Label.tock →
      Offers env (Proc.seq alphabet left right) label right current
        ((childFuture ∪ procSequenceRightMenu left right) \
          current.image Offer.bare)
  | seq_fuse_tock (env : Environment)
      (alphabet skipAlphabet : PactTypeAlphabet) (left right : Proc)
      (current : Finset Offer) (childFuture : Finset BareMessage) :
      Offers env left Label.tock (Proc.skip skipAlphabet) current childFuture →
      Offers env (Proc.seq alphabet left right) Label.tock right ∅ ∅
  | xoffer_send (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) (msg : MessageId)
      (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧ ChoiceBranch.send msg expr process ∈ branches ∧
        env.hasRecv msg ∧ Semantics.ExprEval expr value ∧
        Resolved env branches →
      Offers env (Proc.xoffer alphabet elseProcess branches)
        (Label.message msg .send value) process {Offer.send msg value}
        (procFutureOffers (Proc.xoffer alphabet elseProcess branches) \
          branchActions branches)
  | xoffer_recv (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) (msg : MessageId)
      (varName : String) (process : Proc) (value : Bool) :
      env.WellFormed alphabet ∧
        ChoiceBranch.recv msg varName process ∈ branches ∧
        env.hasSend msg value ∧ Resolved env branches →
      Offers env (Proc.xoffer alphabet elseProcess branches)
        (Label.message msg .recv value)
        (Semantics.procExprReplace process varName value) {Offer.recv msg}
        (procFutureOffers (Proc.xoffer alphabet elseProcess branches) \
          branchActions branches)
  | xoffer_else (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        NoImmediateBranch env branches ∧ Resolved env branches →
      Offers env (Proc.xoffer alphabet elseProcess branches) Label.silent
        elseProcess (projectCurrent alphabet (branchOfferSet branches))
        (procFutureOffers (Proc.xoffer alphabet elseProcess branches) \
          branchActions branches)
  | xoffer_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed alphabet ∧ ¬ Resolved env branches ∧ env.clock = false →
      Offers env (Proc.xoffer alphabet elseProcess branches) Label.silent
        (Proc.xoffer alphabet elseProcess branches)
        (waitingOfferSet env branches)
        (procFutureOffers (Proc.xoffer alphabet elseProcess branches) \
          waitingOffers env branches)
  | offer_some (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch)
      (enabled : ChoiceBranch) :
      env.WellFormed alphabet ∧ enabled ∈ branches ∧ BranchEnabled env enabled →
      Offers env (Proc.offer alphabet elseProcess branches) Label.silent
        (parallelProcessBranchesSelecting alphabet enabled branches) ∅
        (procFutureOffers
          (parallelProcessBranchesSelecting alphabet enabled branches))
  | offer_else (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        NoImmediateBranch env branches ∧ Resolved env branches →
      Offers env (Proc.offer alphabet elseProcess branches) Label.silent
        elseProcess (projectCurrent alphabet (branchOfferSet branches))
        (procFutureOffers elseProcess \ (branchActions branches ∩ alphabet.actions))
  | offer_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed alphabet ∧ env.clock = false ∧
        NoImmediateBranch env branches ∧ ¬ Resolved env branches →
      Offers env (Proc.offer alphabet elseProcess branches) Label.silent
        (Proc.offer alphabet elseProcess branches)
        (projectCurrent alphabet (branchOfferSet branches))
        (procFutureOffers (Proc.offer alphabet elseProcess branches) \
          (branchActions branches ∩ alphabet.actions))
  | par (outer leftEnv rightEnv : Environment) (interface : Interface)
      (alphabet : PactTypeAlphabet)
      (left left' right right' : Proc) (leftLabel rightLabel : Label)
      (leftCurrent rightCurrent : Finset Offer)
      (leftFuture rightFuture : Finset BareMessage) :
      left ≠ Proc.skip left.alphabet →
      right ≠ Proc.skip right.alphabet →
      Offers leftEnv left leftLabel left' leftCurrent leftFuture →
      Offers rightEnv right rightLabel right' rightCurrent rightFuture →
      ¬ (left' = Proc.skip left'.alphabet ∧ right' = Proc.skip right'.alphabet) →
      LocalOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet ∧ Label.Sync interface leftLabel rightLabel →
      Offers outer (Proc.par alphabet left right interface)
        (Label.combine interface leftLabel rightLabel)
        (Proc.par alphabet left' right' interface)
        (hideOfferSet interface (leftCurrent ∪ rightCurrent))
        (if Label.combine interface leftLabel rightLabel = Label.tock
          then ∅
          else hideProcOffers interface (leftFuture ∪ rightFuture))
  | par_fuse (outer leftEnv rightEnv : Environment) (interface : Interface)
      (alphabet : PactTypeAlphabet) (left right : Proc)
      (leftLabel rightLabel : Label)
      (leftCurrent rightCurrent : Finset Offer)
      (leftFuture rightFuture : Finset BareMessage) :
      Offers leftEnv left leftLabel (Proc.skip left.alphabet)
        leftCurrent leftFuture →
      Offers rightEnv right rightLabel (Proc.skip right.alphabet)
        rightCurrent rightFuture →
      LocalOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet ∧ Label.Sync interface leftLabel rightLabel →
      Label.combine interface leftLabel rightLabel ≠ Label.tock →
      Offers outer (Proc.par alphabet left right interface)
        (Label.combine interface leftLabel rightLabel) (Proc.skip alphabet)
        (hideOfferSet interface (leftCurrent ∪ rightCurrent))
        (hideProcOffers interface (leftFuture ∪ rightFuture))
  | par_fuse_tock (outer leftEnv rightEnv : Environment)
      (interface : Interface) (alphabet : PactTypeAlphabet)
      (left right : Proc) (leftLabel rightLabel : Label)
      (leftCurrent rightCurrent : Finset Offer)
      (leftFuture rightFuture : Finset BareMessage) :
      Offers leftEnv left leftLabel (Proc.skip left.alphabet)
        leftCurrent leftFuture →
      Offers rightEnv right rightLabel (Proc.skip right.alphabet)
        rightCurrent rightFuture →
      LocalOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet ∧ Label.Sync interface leftLabel rightLabel →
      Label.combine interface leftLabel rightLabel = Label.tock →
      Offers outer (Proc.par alphabet left right interface)
        (Label.combine interface leftLabel rightLabel) (Proc.skip alphabet) ∅ ∅
  -- P-Par-Left: the left side is already `skip`, so only the right survives.
  -- The finished side still takes its silent `skip` step, both local
  -- environments are checked against the sibling's offers, and the labels
  -- synchronize.  `skip` cannot step under a clock environment, so survivor
  -- entry is non-clock and there is no separate tock clause.
  | left_complete (outer leftEnv rightEnv : Environment)
      (interface : Interface) (alphabet : PactTypeAlphabet)
      (left right right' : Proc) (rightLabel : Label)
      (leftCurrent rightCurrent : Finset Offer)
      (leftFuture rightFuture : Finset BareMessage) :
      left = Proc.skip left.alphabet →
      right ≠ Proc.skip right.alphabet →
      Offers leftEnv left Label.silent left leftCurrent leftFuture →
      Offers rightEnv right rightLabel right' rightCurrent rightFuture →
      right' ≠ Proc.skip right'.alphabet →
      LocalOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet →
      Label.Sync interface Label.silent rightLabel →
      Offers outer (Proc.par alphabet left right interface)
        rightLabel
        (Proc.reannotate alphabet right')
        (hideOfferSet interface rightCurrent)
        (hideProcOffers interface rightFuture)
  -- P-Par-Right: mirror of `left_complete`.
  | right_complete (outer leftEnv rightEnv : Environment)
      (interface : Interface) (alphabet : PactTypeAlphabet)
      (left left' right : Proc) (leftLabel : Label)
      (leftCurrent rightCurrent : Finset Offer)
      (leftFuture rightFuture : Finset BareMessage) :
      right = Proc.skip right.alphabet →
      left ≠ Proc.skip left.alphabet →
      Offers rightEnv right Label.silent right rightCurrent rightFuture →
      Offers leftEnv left leftLabel left' leftCurrent leftFuture →
      left' ≠ Proc.skip left'.alphabet →
      LocalOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet →
      Label.Sync interface leftLabel Label.silent →
      Offers outer (Proc.par alphabet left right interface)
        leftLabel
        (Proc.reannotate alphabet left')
        (hideOfferSet interface leftCurrent)
        (hideProcOffers interface leftFuture)

/-! ## Process transition system

`E ⊢ P →^α P'`: the offer judgement with its two offer sets forgotten. -/

def ProcessTransition (env : Environment) (source : Proc) (label : Label)
    (target : Proc) : Prop :=
  ∃ current future, Offers env source label target current future

/-- `Ready(E,P)`: some transition is available under `E`. -/
def ProcessReady (env : Environment) (process : Proc) : Prop :=
  ∃ label target, ProcessTransition env process label target

end

end Pact
