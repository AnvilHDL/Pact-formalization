import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Anvilpp.Proc

namespace Pact

noncomputable section

/-- A finite synchronization interface. for P ||_I P -/
abbrev Interface := Finset MessageId

/-- A message identifier paired with its polarity. -/
abbrev BareMessage := MessageId × MessageDir

/--
The message part of a process/type signature.

This is fixed by the surrounding system before either syntax tree is compiled;
in particular, it is deliberately not inferred by traversing a `Proc` or a
`PactType`.  `boundary` is polarized, while an interface contains message
identifiers because synchronization pairs the two polarities.
-/
structure MessageAlphabet : Type where
  boundary : Finset BareMessage
  interface : Interface
  deriving DecidableEq

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

namespace MessageAlphabet

  /-- Concrete environment offers complementary to the fixed process boundary. -/
  def processEnvironmentOffers (alphabet : MessageAlphabet) : Finset Offer :=
    alphabet.boundary.biUnion fun action =>
      match action.2 with
      | .send => {Offer.recv action.1}
      | .recv => {Offer.send action.1 false, Offer.send action.1 true}

  /-- Bare future offers admitted by the fixed process boundary. -/
  def processFutureOffers (alphabet : MessageAlphabet) : Finset BareMessage :=
    alphabet.processEnvironmentOffers.image Offer.bare

  /--
  The finite process-environment space generated from a fixed alphabet.
  Immediate and future offers are disjoint after value erasure; the clock
  environment is the distinguished additional possibility.
  -/
  def processEnvironments (alphabet : MessageAlphabet) : Finset Environment :=
    {Environment.tock} ∪
      alphabet.processEnvironmentOffers.powerset.biUnion fun immediate =>
        (alphabet.processFutureOffers \ immediate.image Offer.bare).powerset.image
          fun future =>
            { immediate := immediate, future := future, clock := false }

end MessageAlphabet

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
  | [] => Proc.skip PactTypeAlphabet.empty
  | [branch] => branch.toXOffer
  | branch :: rest =>
      Proc.par
        (PactTypeAlphabet.mergeHidden branch.toXOffer.alphabet
          (parallelBranches rest).alphabet ∅)
        branch.toXOffer (parallelBranches rest) ∅

/-! ## Sibling offers and local environments -/

/-- `ChoiceBranch.action`/`.continuation`/`.continuation_sizeOf_lt` now live
in `Proc.lean`, shared unqualified. -/

def branchActions (branches : List ChoiceBranch) : Finset BareMessage :=
  (branches.map ChoiceBranch.action).toFinset

def restrictCurrent (interface : Interface) (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer => offer.messageId ∈ interface

def restrictFuture (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Remove offers hidden by a parallel interface. -/
def hideProcOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

def hideOfferSet (interface : Interface) (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer => offer.messageId ∉ interface

/-- `Need` applied to a bare action: flip its polarity. -/
def bareNeed (action : BareMessage) : BareMessage := (action.1, action.2.invert)

/-- Restrict an outer environment's offers to the ones a local process could
actually need, mirroring `projectTypeEnvironmentOffers` on the type side. -/
def projectProcEnvironmentOffers (localProc : Proc)
    (offers : Finset Offer) : Finset Offer :=
  offers.filter fun offer =>
    offer.bare ∈ localProc.alphabet.actions.image bareNeed

/-- Restrict an outer environment's future offers the same way, for the bare
future set (already `Finset BareMessage`, no payload to filter on). -/
def projectProcEnvironmentFuture (localProc : Proc)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer ∈ localProc.alphabet.actions.image bareNeed

/-- Branch actions the future environment still promises to enable, as bare
messages: `W(E,B) = overline(Fut(E)) ∩ Act_B` from Appendix A.2.1/`pactcommons`. -/
def waitingOffers (env : Environment) (branches : List ChoiceBranch) :
    Finset BareMessage :=
  env.future.image bareNeed ∩ branchActions branches

/-- A concrete offer contributed by one branch: sends carry the branch's own
(closed) expression's value, receives carry none. -/
def branchOffer (branch : ChoiceBranch) : Offer :=
  match branch with
  | ChoiceBranch.send _ msg expr _ =>
      Offer.send msg ((Semantics.exprEvalOpt expr).getD false)
  | ChoiceBranch.recv _ msg _ _ => Offer.recv msg

/-- The concrete waiting-offer witness set exposed by an unresolved offer:
every branch whose bare action is still promised by the future environment,
each realized with its own (deterministic) value. -/
def waitingOfferSet (env : Environment) (branches : List ChoiceBranch) :
    Finset Offer :=
  ((branches.filter fun branch => ChoiceBranch.action branch ∈ waitingOffers env branches).map
    branchOffer).toFinset

/-! Whether a process may reach `skip` before its next mandatory clock,
mirroring `PactType.CanCompleteBeforeTock`. -/
mutual
  def Proc.CanCompleteBeforeTock : Proc → Bool
    | .send _ _ _ _ | .recv _ _ _ _ | .skip _ | .endp _ _ => true
    | .cycle _ | .var _ _ => false
    | .recur _ _ body => Proc.CanCompleteBeforeTock body
    | .par _ left right _ | .seq _ left right =>
        Proc.CanCompleteBeforeTock left && Proc.CanCompleteBeforeTock right
    | .letp _ _ _ p => Proc.CanCompleteBeforeTock p
    | .ifunfair _ _ left right | .iffair _ _ _ left right =>
        Proc.CanCompleteBeforeTock left || Proc.CanCompleteBeforeTock right
    | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
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
    | (have hBranch : sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
         cases branch <;> simp [ChoiceBranch.continuation] <;> omega
       simp_wf
       omega)
end

/-- Syntactic future-offer menu, bounded by the depth of the finite process
term.  Fuel-bounded (rather than plain structural recursion) because it must
also be applied to `recur`'s capture-avoiding unfolding, which need not be
structurally smaller than the original body. -/
def procFutureOffersFuel : Nat → Proc → Finset BareMessage
  | 0, _ => ∅
  | fuel + 1, process =>
      match process with
      | Proc.send _ msg _ _ => {(msg, .send)}
      | Proc.recv _ msg _ _ => {(msg, .recv)}
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
      | Proc.xoffer _ elseProcess branches | Proc.offer _ elseProcess branches =>
          branches.foldl (fun offers branch =>
            offers ∪ {ChoiceBranch.action branch} ∪
              procFutureOffersFuel fuel (ChoiceBranch.continuation branch))
            (procFutureOffersFuel fuel elseProcess)

/-- All message actions that may still be offered before the next clock. -/
def procFutureOffers (process : Proc) : Finset BareMessage :=
  procFutureOffersFuel (sizeOf process + 1) process

/-!
Environment-indexed current/future offers and the sibling-local environment
relation are mutually defined: parallel offers depend on the two local steps,
while each local environment depends on the sibling step's offers.  This is
`Off(E,P,α,P')` (Appendix A.2.1/`procSem.typ`), mirroring `TypeOffers` one
constructor at a time.
-/
mutual
  inductive Offers :
      Environment → Proc → Label → Proc →
        Finset Offer → Finset BareMessage → Prop where
    | send (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
        (expr : Expr) (process : Proc) (value : Bool) :
        env.WellFormed ∧ env.hasRecv msg ∧ Semantics.ExprEval expr value →
        Offers env (Proc.send alphabet msg expr process)
          (Label.message msg .send value)
          process {Offer.send msg value} (procFutureOffers process)
    | send_wait (env : Environment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (expr : Expr) (process : Proc) (value : Bool) :
        env.WellFormed ∧ ¬ env.hasRecv msg ∧ env.clock = false ∧
          Semantics.ExprEval expr value →
        Offers env (Proc.send alphabet msg expr process) Label.silent
          (Proc.send alphabet msg expr process) {Offer.send msg value}
          (procFutureOffers (Proc.send alphabet msg expr process) \
            {(msg, .send)})
    | recv (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
        (var : String) (process : Proc) (value : Bool) :
        env.WellFormed ∧ env.hasSend msg value →
        Offers env (Proc.recv alphabet msg var process)
          (Label.message msg .recv value)
          (Semantics.procExprReplace process var value) {Offer.recv msg}
          (procFutureOffers (Semantics.procExprReplace process var value))
    | recv_wait (env : Environment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (var : String) (process : Proc) :
        env.WellFormed ∧ (∀ value, ¬ env.hasSend msg value) ∧ env.clock = false →
        Offers env (Proc.recv alphabet msg var process) Label.silent
          (Proc.recv alphabet msg var process) {Offer.recv msg}
          (procFutureOffers (Proc.recv alphabet msg var process) \
            {(msg, .recv)})
    | cycle (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = true →
        Offers env (Proc.cycle alphabet) Label.tock (Proc.skip skipAlphabet)
          ∅ ∅
    | cycle_wait (env : Environment) (alphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = false →
        Offers env (Proc.cycle alphabet) Label.silent (Proc.cycle alphabet)
          ∅ ∅
    | skip (env : Environment) (alphabet : PactTypeAlphabet) :
        env.WellFormed ∧ env.clock = false →
        Offers env (Proc.skip alphabet) Label.silent (Proc.skip alphabet) ∅ ∅
    | progress (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet)
        (pid : ProcId) :
        env.WellFormed → env.clock = false →
        Offers env (Proc.endp alphabet pid) (Label.progress pid)
          (Proc.skip skipAlphabet) ∅ ∅
    | letp (env : Environment) (alphabet : PactTypeAlphabet) (var : String)
        (expr : Expr) (process : Proc) (value : Bool) :
        env.WellFormed ∧ Semantics.ExprEval expr value →
        Offers env (Proc.letp alphabet var expr process) Label.silent
          (Semantics.procExprReplace process var value) ∅
          (procFutureOffers (Semantics.procExprReplace process var value))
    | if_true (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
        (ifTrue ifFalse : Proc) :
        env.WellFormed ∧ Semantics.ExprEval expr true →
        Offers env (Proc.ifunfair alphabet expr ifTrue ifFalse) Label.silent
          ifTrue ∅ (procFutureOffers ifTrue)
    | if_false (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
        (ifTrue ifFalse : Proc) :
        env.WellFormed ∧ Semantics.ExprEval expr false →
        Offers env (Proc.ifunfair alphabet expr ifTrue ifFalse) Label.silent
          ifFalse ∅ (procFutureOffers ifFalse)
    | fair_true (env : Environment) (alphabet : PactTypeAlphabet)
        (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
        env.WellFormed ∧ Semantics.ExprEval expr true →
        Offers env (Proc.iffair alphabet bid expr ifTrue ifFalse)
          (Label.fair bid true) ifTrue ∅ (procFutureOffers ifTrue)
    | fair_false (env : Environment) (alphabet : PactTypeAlphabet)
        (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
        env.WellFormed ∧ Semantics.ExprEval expr false →
        Offers env (Proc.iffair alphabet bid expr ifTrue ifFalse)
          (Label.fair bid false) ifFalse ∅ (procFutureOffers ifFalse)
    | recur (env : Environment) (alphabet : PactTypeAlphabet) (var : String)
        (body : Proc) :
        env.WellFormed → env.clock = false →
        Offers env (Proc.recur alphabet var body) Label.silent
          (Semantics.procReplace body var (Proc.recur alphabet var body)) ∅
          (procFutureOffers
            (Semantics.procReplace body var (Proc.recur alphabet var body)))
    | seq (env : Environment) (alphabet : PactTypeAlphabet)
        (left left' right : Proc) (label : Label)
        (current : Finset Offer) (childFuture : Finset BareMessage) :
        Offers env left label left' current childFuture →
        left' ≠ Proc.skip left'.alphabet →
        Offers env (Proc.seq alphabet left right) label
          (Proc.seq alphabet left' right) current
          (procFutureOffers (Proc.seq alphabet left' right) \
            current.image Offer.bare)
    | seq_fuse (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet)
        (left right : Proc) (label : Label)
        (current : Finset Offer) (childFuture : Finset BareMessage) :
        Offers env left label (Proc.skip skipAlphabet) current childFuture →
        Offers env (Proc.seq alphabet left right) label right current
          (procFutureOffers right \ current.image Offer.bare)
    | xoffer_send (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch)
        (branchAlphabet : PactTypeAlphabet) (msg : MessageId) (expr : Expr)
        (process : Proc) (value : Bool) :
        env.WellFormed ∧
          ChoiceBranch.send branchAlphabet msg expr process ∈ branches ∧
          env.hasRecv msg ∧ Semantics.ExprEval expr value ∧
          Resolved env branches →
        Offers env (Proc.xoffer alphabet elseProcess branches)
          (Label.message msg .send value) process {Offer.send msg value}
          (procFutureOffers process)
    | xoffer_recv (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch)
        (branchAlphabet : PactTypeAlphabet) (msg : MessageId) (var : String)
        (process : Proc) (value : Bool) :
        env.WellFormed ∧
          ChoiceBranch.recv branchAlphabet msg var process ∈ branches ∧
          env.hasSend msg value ∧ Resolved env branches →
        Offers env (Proc.xoffer alphabet elseProcess branches)
          (Label.message msg .recv value)
          (Semantics.procExprReplace process var value) {Offer.recv msg}
          (procFutureOffers (Semantics.procExprReplace process var value))
    | xoffer_else (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch) :
        env.WellFormed ∧ NoImmediateBranch env branches ∧ Resolved env branches →
        Offers env (Proc.xoffer alphabet elseProcess branches) Label.silent
          elseProcess ∅ (procFutureOffers elseProcess)
    | xoffer_wait (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch) :
        env.WellFormed ∧ ¬ Resolved env branches ∧ env.clock = false →
        Offers env (Proc.xoffer alphabet elseProcess branches) Label.silent
          (Proc.xoffer alphabet elseProcess branches)
          (waitingOfferSet env branches)
          (procFutureOffers (Proc.xoffer alphabet elseProcess branches) \
            (waitingOfferSet env branches).image Offer.bare)
    | offer_some (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch)
        (enabled : ChoiceBranch) :
        env.WellFormed ∧ enabled ∈ branches ∧ BranchEnabled env enabled →
        Offers env (Proc.offer alphabet elseProcess branches) Label.silent
          (parallelBranches branches) ∅
          (procFutureOffers (parallelBranches branches))
    | offer_else (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch) :
        env.WellFormed ∧ NoImmediateBranch env branches ∧ Resolved env branches →
        Offers env (Proc.offer alphabet elseProcess branches) Label.silent
          elseProcess
          (branches.map branchOffer).toFinset (procFutureOffers elseProcess)
    | offer_wait (env : Environment) (alphabet : PactTypeAlphabet)
        (elseProcess : Proc) (branches : List ChoiceBranch) :
        env.WellFormed ∧ NoImmediateBranch env branches ∧
          ¬ Resolved env branches ∧ env.clock = false →
        Offers env (Proc.offer alphabet elseProcess branches) Label.silent
          (Proc.offer alphabet elseProcess branches)
          (waitingOfferSet env branches)
          (procFutureOffers (Proc.offer alphabet elseProcess branches) \
            (waitingOfferSet env branches).image Offer.bare)
    | par (outer leftEnv rightEnv : Environment) (interface : Interface)
        (left left' right right' : Proc) (leftLabel rightLabel : Label)
        (leftCurrent : Finset Offer) (leftFuture : Finset BareMessage)
        (rightCurrent : Finset Offer) (rightFuture : Finset BareMessage) :
        Offers leftEnv left leftLabel left' leftCurrent leftFuture →
        Offers rightEnv right rightLabel right' rightCurrent rightFuture →
        ¬ (left' = Proc.skip left'.alphabet ∧ right' = Proc.skip right'.alphabet) →
        LocalEnvironment outer interface left rightEnv right rightLabel leftEnv →
        LocalEnvironment outer interface right leftEnv left leftLabel rightEnv →
        outer.WellFormed ∧ Label.Sync interface leftLabel rightLabel →
        Offers outer
          (Proc.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
              interface) left right interface)
          (Label.combine interface leftLabel rightLabel)
          (Proc.par (PactTypeAlphabet.mergeHidden left'.alphabet
              right'.alphabet interface) left' right' interface)
          (hideOfferSet interface (leftCurrent ∪ rightCurrent))
          (hideProcOffers interface (leftFuture ∪ rightFuture))
    | par_fuse (outer leftEnv rightEnv : Environment) (interface : Interface)
        (left right : Proc) (leftLabel rightLabel : Label)
        (leftSkipAlphabet rightSkipAlphabet skipAlphabet : PactTypeAlphabet)
        (leftCurrent : Finset Offer) (leftFuture : Finset BareMessage)
        (rightCurrent : Finset Offer) (rightFuture : Finset BareMessage) :
        Offers leftEnv left leftLabel (Proc.skip leftSkipAlphabet) leftCurrent
          leftFuture →
        Offers rightEnv right rightLabel (Proc.skip rightSkipAlphabet)
          rightCurrent rightFuture →
        LocalEnvironment outer interface left rightEnv right rightLabel leftEnv →
        LocalEnvironment outer interface right leftEnv left leftLabel rightEnv →
        outer.WellFormed ∧ Label.Sync interface leftLabel rightLabel →
        Offers outer
          (Proc.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
              interface) left right interface)
          (Label.combine interface leftLabel rightLabel)
          (Proc.skip skipAlphabet)
          (hideOfferSet interface (leftCurrent ∪ rightCurrent))
          (hideProcOffers interface (leftFuture ∪ rightFuture))

  /-- `LocalEnv(E,I,siblingEnv,sibling,α)` from Appendix A.2.1: the local
  environment a component receives, built from the outer environment plus the
  sibling's own offers under its own (mutually determined) environment.

  Indexed by `localProc`, the process this local environment is *for*: the
  `ordinary` case restricts the outer environment's offers to `localProc`'s
  own actions before folding in the sibling's, mirroring
  `LocalTypeOfferEnvironment`'s `projectTypeEnvironmentOffers localType.alphabet`
  restriction on the type side. -/
  inductive LocalEnvironment :
      Environment → Interface → Proc → Environment → Proc → Label → Environment → Prop where
    | clock (outer : Environment) (interface : Interface) (localProc : Proc)
        (siblingEnv : Environment) (sibling : Proc) (label : Label) :
        outer.clock = true →
        LocalEnvironment outer interface localProc Environment.tock sibling label
          Environment.tock
    | ordinary (outer siblingEnv localEnv : Environment) (interface : Interface)
        (localProc sibling siblingTarget : Proc) (label : Label)
        (current : Finset Offer) (future : Finset BareMessage) :
        outer.clock = false →
        siblingEnv.clock = false →
        Offers siblingEnv sibling label siblingTarget current future →
        localEnv.clock = false →
        localEnv.immediate =
          projectProcEnvironmentOffers localProc outer.immediate ∪
            restrictCurrent interface current →
        localEnv.future =
          (projectProcEnvironmentFuture localProc outer.future ∪
            restrictFuture interface future) \ localEnv.bareImmediate →
        LocalEnvironment outer interface localProc siblingEnv sibling label localEnv
end

/-! ## Process transition system -/

/-- The updated local small-step judgment `E ⊢ P -α→ P'`. -/
@[aesop unsafe]
inductive ProcessTransition : Environment → Proc → Label → Proc → Prop where
  | send (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
      (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      env.hasRecv msg ∧
      Semantics.ExprEval expr value →
      --
      ProcessTransition env (Proc.send alphabet msg expr process)
      (Label.message msg .send value) process
  | send_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (expr : Expr) (process : Proc) :
      env.WellFormed ∧
      ¬ env.hasRecv msg ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.send alphabet msg expr process)
      Label.silent
      (Proc.send alphabet msg expr process)
  | recv (env : Environment) (alphabet : PactTypeAlphabet) (msg : MessageId)
      (var : String) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      env.hasSend msg value →
      --
      ProcessTransition env (Proc.recv alphabet msg var process)
      (Label.message msg .recv value)
      (Semantics.procExprReplace process var value)
  | recv_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (var : String) (process : Proc) :
      env.WellFormed ∧
      (∀ value, ¬ env.hasSend msg value) ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.recv alphabet msg var process)
      Label.silent
      (Proc.recv alphabet msg var process)
  | cycle (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet) :
      env.WellFormed ∧ env.clock = true →
      --
      ProcessTransition env (Proc.cycle alphabet)
      Label.tock
      (Proc.skip skipAlphabet)
  | cycle_wait (env : Environment) (alphabet : PactTypeAlphabet) :
      env.WellFormed ∧ env.clock = false →
      --
      ProcessTransition env (Proc.cycle alphabet)
      Label.silent
      (Proc.cycle alphabet)
  | skip (env : Environment) (alphabet : PactTypeAlphabet) :
      env.WellFormed ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.skip alphabet)
      Label.silent
      (Proc.skip alphabet)
  | seq (env : Environment) (alphabet : PactTypeAlphabet)
      (left left' right : Proc) (label : Label) :
      ProcessTransition env left
      label
      left' →
      left' ≠ Proc.skip left'.alphabet →
      --
      ProcessTransition env (Proc.seq alphabet left right)
      label
      (Proc.seq alphabet left' right)
  | seq_fuse (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet)
      (left right : Proc) (label : Label) :
      ProcessTransition env left label (Proc.skip skipAlphabet) →
      --
      ProcessTransition env (Proc.seq alphabet left right)
      label
      right
  | letp (env : Environment) (alphabet : PactTypeAlphabet) (var : String)
      (expr : Expr) (process : Proc) (value : Bool) :
      env.WellFormed ∧
      Semantics.ExprEval expr value →
      --
      ProcessTransition env (Proc.letp alphabet var expr process)
      Label.silent
      (Semantics.procExprReplace process var value)
  | if_true (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
      (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr true →
      --
      ProcessTransition env (Proc.ifunfair alphabet expr ifTrue ifFalse)
      Label.silent
      ifTrue
  | if_false (env : Environment) (alphabet : PactTypeAlphabet) (expr : Expr)
      (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr false →
      --
      ProcessTransition env (Proc.ifunfair alphabet expr ifTrue ifFalse)
      Label.silent
      ifFalse
  | fair_true (env : Environment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr true →
      --
      ProcessTransition env (Proc.iffair alphabet bid expr ifTrue ifFalse)
      (Label.fair bid true)
      ifTrue
  | fair_false (env : Environment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (expr : Expr) (ifTrue ifFalse : Proc) :
      env.WellFormed ∧
      Semantics.ExprEval expr false →
      --
      ProcessTransition env (Proc.iffair alphabet bid expr ifTrue ifFalse)
      (Label.fair bid false)
      ifFalse
  | progress (env : Environment) (alphabet skipAlphabet : PactTypeAlphabet)
      (pid : ProcId) :
      env.WellFormed →
      env.clock = false →
      --
      ProcessTransition env (Proc.endp alphabet pid)
      (Label.progress pid)
      (Proc.skip skipAlphabet)
  | recur (env : Environment) (alphabet : PactTypeAlphabet) (var : String)
      (body : Proc) :
      env.WellFormed →
      env.clock = false →
      --
      ProcessTransition env (Proc.recur alphabet var body)
      Label.silent
      (Semantics.procReplace body var (Proc.recur alphabet var body))
  | xoffer_send (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch)
      (branchAlphabet : PactTypeAlphabet) (msg : MessageId) (expr : Expr)
      (process : Proc) (value : Bool) :
      env.WellFormed ∧
      ChoiceBranch.send branchAlphabet msg expr process ∈ branches ∧
      env.hasRecv msg ∧
      Semantics.ExprEval expr value ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer alphabet elseProcess branches)
      (Label.message msg .send value)
      process
  | xoffer_recv (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch)
      (branchAlphabet : PactTypeAlphabet) (msg : MessageId) (var : String)
      (process : Proc) (value : Bool) :
      env.WellFormed ∧
      ChoiceBranch.recv branchAlphabet msg var process ∈ branches ∧
      env.hasSend msg value ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer alphabet elseProcess branches)
      (Label.message msg .recv value)
      (Semantics.procExprReplace process var value)
  | xoffer_else (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.xoffer alphabet elseProcess branches)
      Label.silent
      elseProcess
  | xoffer_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      ¬ Resolved env branches ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.xoffer alphabet elseProcess branches)
      Label.silent
      (Proc.xoffer alphabet elseProcess branches)
    -- To Do double check the offer case
  | offer_some (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch)
      (enabled : ChoiceBranch) :
      env.WellFormed ∧
      enabled ∈ branches ∧
      BranchEnabled env enabled →
      --
      ProcessTransition env (Proc.offer alphabet elseProcess branches)
      Label.silent
      (parallelBranches branches)
  | offer_else (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      Resolved env branches →
      --
      ProcessTransition env (Proc.offer alphabet elseProcess branches)
      Label.silent
      elseProcess
  | offer_wait (env : Environment) (alphabet : PactTypeAlphabet)
      (elseProcess : Proc) (branches : List ChoiceBranch) :
      env.WellFormed ∧
      NoImmediateBranch env branches ∧
      ¬ Resolved env branches ∧
      env.clock = false →
      --
      ProcessTransition env (Proc.offer alphabet elseProcess branches)
      Label.silent
      (Proc.offer alphabet elseProcess branches)
  | par (outer leftEnv rightEnv : Environment) (interface : MsgIdSet)
      (left left' right right' : Proc) (leftLabel rightLabel : Label) :
      ProcessTransition leftEnv left leftLabel left' →
      ProcessTransition rightEnv right rightLabel right' →
      ¬ (left' = Proc.skip left'.alphabet ∧ right' = Proc.skip right'.alphabet) →
      (outer.WellFormed ∧
        LocalEnvironment outer interface left rightEnv right rightLabel leftEnv ∧
        LocalEnvironment outer interface right leftEnv left leftLabel rightEnv ∧
        Label.Sync interface leftLabel rightLabel) →
      --
      ProcessTransition outer
      (Proc.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
          interface) left right interface)
      (Label.combine interface leftLabel rightLabel)
      (Proc.par (PactTypeAlphabet.mergeHidden left'.alphabet right'.alphabet
          interface) left' right' interface)
  | par_fuse (outer leftEnv rightEnv : Environment) (interface : MsgIdSet)
      (left right : Proc) (leftLabel rightLabel : Label)
      (leftSkipAlphabet rightSkipAlphabet skipAlphabet : PactTypeAlphabet) :
      ProcessTransition leftEnv left leftLabel (Proc.skip leftSkipAlphabet) →
      ProcessTransition rightEnv right rightLabel (Proc.skip rightSkipAlphabet) →
      (outer.WellFormed ∧
        LocalEnvironment outer interface left rightEnv right rightLabel leftEnv ∧
        LocalEnvironment outer interface right leftEnv left leftLabel rightEnv ∧
        Label.Sync interface leftLabel rightLabel) →
      --
      ProcessTransition outer
      (Proc.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
          interface) left right interface)
      (Label.combine interface leftLabel rightLabel)
      (Proc.skip skipAlphabet)
end

end Pact
