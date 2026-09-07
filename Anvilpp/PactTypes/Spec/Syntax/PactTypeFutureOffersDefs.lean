import Anvilpp.PactTypes.Proofs.Syntax.TypeFutureOffersFuelLemmas

namespace Pact

noncomputable section

/-- `F_2` of the sequence offer clause: the right operand's menu, admitted
when the left operand passes the optimistic completion test at the source. -/
def sequenceRightMenu (left right : PactType) : Finset BareMessage :=
  if left.CanCompleteDeclared then typeFutureOffers right else ∅

/-- Branch offers selected by the future part of this environment. -/
def typeWaitingOffers (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (env.future.image typeNeed) ∩ typeBranchActions branches

/-
Environment-indexed current/future offers and the sibling-local environment
relation are mutually defined: parallel offers depend on the two local steps,
while each local environment depends on the sibling step's offers.
-/

/-- Restrict a boundary environment menu to the actions visible to a type
with fixed alphabet `alphabet`.  Environments contain the complementary
polarities needed by type actions, so the projection uses `typeNeed`. -/
def projectTypeEnvironmentOffers
    (alphabet : PactTypeAlphabet) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun action => action ∈ alphabet.actions.image typeNeed

/-- The offer-indexed sibling-local environment relation used by the
decorated parallel rule.

Both children carry the complete outer boundary environment; the interface
contributions are supplied by the sibling's own offers.  The ordinary case is
indexed by the concrete sibling offer sets, which rules out justifying the
local environment by a different sibling offer witness than the step uses. -/
inductive LocalTypeOfferEnvironment :
    TypeEnvironment → Interface → PactType → TypeEnvironment →
      Finset BareMessage → Finset BareMessage → TypeEnvironment → Prop where
  | clock (outer : TypeEnvironment) (interface : Interface)
      (localType : PactType) (current future : Finset BareMessage) :
      outer.clock = true →
      LocalTypeOfferEnvironment outer interface localType TypeEnvironment.tock
        current future TypeEnvironment.tock
  | ordinary (outer siblingEnv localEnv : TypeEnvironment)
      (interface : Interface) (localType : PactType)
      (current future : Finset BareMessage) :
      outer.clock = false →
      siblingEnv.clock = false →
      localEnv.clock = false →
      localEnv.immediate =
        outer.immediate ∪ restrictTypeOffers interface current →
      localEnv.future =
        (outer.future ∪ restrictTypeOffers interface future) \
          localEnv.immediate →
      LocalTypeOfferEnvironment outer interface localType siblingEnv current
        future localEnv

mutual
  @[aesop unsafe]
  inductive TypeOffers :
      TypeEnvironment → PactType → TypeLabel → PactType →
        Finset BareMessage → Finset BareMessage → Prop where
    | action (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (dir : MessageDir) :
        env.WellFormed alphabet ∧ env.hasNeed (msg, dir) →
        TypeOffers env (.message alphabet msg dir) (TypeLabel.message msg dir)
          (.skip alphabet) ({(msg, dir)} ∩ alphabet.actions)
          (typeFutureOffers (.skip alphabet))
    | action_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (msg : MessageId) (dir : MessageDir) :
        env.WellFormed alphabet ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
        TypeOffers env (.message alphabet msg dir) TypeLabel.silent
          (.message alphabet msg dir) ({(msg, dir)} ∩ alphabet.actions)
          (typeFutureOffers (.message alphabet msg dir) \
            ({(msg, dir)} ∩ alphabet.actions))
    | choice_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left right : PactType) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.choice alphabet left right) TypeLabel.silent left
          ∅ (typeFutureOffers (.choice alphabet left right))
    | choice_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left right : PactType) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.choice alphabet left right) TypeLabel.silent right
          ∅ (typeFutureOffers (.choice alphabet left right))
    | fair_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (bid : BranchId)
        (left right : PactType) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.fairChoice alphabet bid left right)
          (TypeLabel.fair bid true) left ∅
          (typeFutureOffers (.fairChoice alphabet bid left right))
    | fair_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (bid : BranchId)
        (left right : PactType) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.fairChoice alphabet bid left right)
          (TypeLabel.fair bid false) right ∅
          (typeFutureOffers (.fairChoice alphabet bid left right))
    | cycle (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed alphabet ∧ env.clock = true →
        TypeOffers env (.tock alphabet) .tock (.skip alphabet) ∅ ∅
    | cycle_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.tock alphabet) TypeLabel.silent (.tock alphabet) ∅
          (typeFutureOffers (.tock alphabet))
    | skip (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.skip alphabet) TypeLabel.silent (.skip alphabet) ∅
          (typeFutureOffers (.skip alphabet))
    | progress (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (pid : ProcId) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.progress alphabet pid) (TypeLabel.progress pid)
          (.skip alphabet) ∅ (typeFutureOffers (.skip alphabet))
    | recur (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (name : String) (body : PactType) :
        env.WellFormed alphabet ∧ env.clock = false →
        TypeOffers env (.recur alphabet name body) TypeLabel.silent
          (body.replaceVar name (.recur alphabet name body)) ∅
          (typeFutureOffers (body.replaceVar name (.recur alphabet name body)))
    | seq (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left left' right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label left' current childFuture →
        left' ≠ .skip left'.alphabet →
        label ≠ TypeLabel.tock →
        TypeOffers env (.seq alphabet left right) label
          (.seq alphabet left' right) current
          ((childFuture ∪ sequenceRightMenu left right) \ current)
    | seq_tock (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (left left' right : PactType)
        (current childFuture : Finset BareMessage) :
        TypeOffers env left TypeLabel.tock left' current childFuture →
        left' ≠ .skip left'.alphabet →
        TypeOffers env (.seq alphabet left right) TypeLabel.tock
          (.seq alphabet left' right) ∅ ∅
    | seq_fuse (env : TypeEnvironment) (alphabet skipAlphabet : PactTypeAlphabet)
        (left right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label (.skip skipAlphabet) current childFuture →
        label ≠ TypeLabel.tock →
        TypeOffers env (.seq alphabet left right) label right current
          ((childFuture ∪ sequenceRightMenu left right) \ current)
    | seq_fuse_tock (env : TypeEnvironment) (alphabet skipAlphabet : PactTypeAlphabet)
        (left right : PactType)
        (current childFuture : Finset BareMessage) :
        TypeOffers env left TypeLabel.tock (.skip skipAlphabet) current childFuture →
        TypeOffers env (.seq alphabet left right) TypeLabel.tock right ∅ ∅
    | xoffer_branch (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (action : BareMessage) (processType : PactType) :
        env.WellFormed alphabet ∧
          (action, processType) ∈ branches ∧
          TypeBranchEnabled env (action, processType) ∧
          TypeResolved env branches →
        TypeOffers env (.xoffer alphabet elseType branches)
          (TypeLabel.message action.1 action.2) processType
          {action}
          (typeFutureOffers (.xoffer alphabet elseType branches) \
            typeBranchActions branches)
    | xoffer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed alphabet ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.xoffer alphabet elseType branches) TypeLabel.silent
          elseType ∅
          (typeFutureOffers (.xoffer alphabet elseType branches) \
            typeBranchActions branches)
    | xoffer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed alphabet ∧ ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.xoffer alphabet elseType branches) TypeLabel.silent
          (.xoffer alphabet elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.xoffer alphabet elseType branches) \
            typeWaitingOffers env branches)
    | offer_some (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (enabled : BareMessage × PactType) :
        env.WellFormed alphabet ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          (parallelTypeBranchesSelecting alphabet enabled branches) ∅
          (typeFutureOffers
            (parallelTypeBranchesSelecting alphabet enabled branches))
    | offer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed alphabet ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          elseType (typeBranchActions branches ∩ alphabet.actions)
          (typeFutureOffers elseType \ (typeBranchActions branches ∩ alphabet.actions))
    | offer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
        (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed alphabet ∧ env.clock = false ∧
          TypeNoImmediateBranch env branches ∧ ¬ TypeResolved env branches →
        TypeOffers env (.offer alphabet elseType branches) TypeLabel.silent
          (.offer alphabet elseType branches) (typeBranchActions branches ∩ alphabet.actions)
          (typeFutureOffers (.offer alphabet elseType branches) \
            (typeBranchActions branches ∩ alphabet.actions))
    | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (alphabet : PactTypeAlphabet)
        (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        left ≠ .skip left.alphabet →
        right ≠ .skip right.alphabet →
        TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
        ¬ (left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet) →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed alphabet ∧
          TypeLabel.Sync interface leftLabel rightLabel →
        TypeOffers outer (.par alphabet left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.par alphabet left' right' interface)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
            then ∅
            else hideTypeOffers interface (leftFuture ∪ rightFuture))
    | par_fuse (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (alphabet : PactTypeAlphabet)
        (left right : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel (.skip left.alphabet)
          leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel (.skip right.alphabet)
          rightCurrent rightFuture →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed alphabet ∧
          TypeLabel.Sync interface leftLabel rightLabel →
        TypeLabel.combine interface leftLabel rightLabel ≠ TypeLabel.tock →
        TypeOffers outer (.par alphabet left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.skip alphabet)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))
    | par_fuse_tock (outer leftEnv rightEnv : TypeEnvironment)
        (interface : Interface) (alphabet : PactTypeAlphabet)
        (left right : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel (.skip left.alphabet)
          leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel (.skip right.alphabet)
          rightCurrent rightFuture →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed alphabet ∧
          TypeLabel.Sync interface leftLabel rightLabel →
        TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock →
        TypeOffers outer (.par alphabet left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.skip alphabet)
          ∅ ∅
    -- T-Par-Left: the left side is already `skip`, so only the right survives.
    -- The finished side still takes its silent `skip` step, both local
    -- environments are checked against the sibling's offers, and the labels
    -- synchronize.  `skip` cannot step under a clock environment, so survivor
    -- entry is non-clock and there is no separate tock clause.
    | left_complete (outer leftEnv rightEnv : TypeEnvironment)
        (interface : Interface) (alphabet : PactTypeAlphabet)
        (left right right' : PactType) (rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        left = .skip left.alphabet →
        right ≠ .skip right.alphabet →
        TypeOffers leftEnv left TypeLabel.silent left leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
        right' ≠ .skip right'.alphabet →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed alphabet →
        TypeLabel.Sync interface TypeLabel.silent rightLabel →
        TypeOffers outer (.par alphabet left right interface)
          rightLabel
          (right'.reannotate alphabet)
          (hideTypeOffers interface rightCurrent)
          (hideTypeOffers interface rightFuture)
    -- T-Par-Right: mirror of `left_complete`; the right side is already `skip`.
    | right_complete (outer leftEnv rightEnv : TypeEnvironment)
        (interface : Interface) (alphabet : PactTypeAlphabet)
        (left left' right : PactType) (leftLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        right = .skip right.alphabet →
        left ≠ .skip left.alphabet →
        TypeOffers rightEnv right TypeLabel.silent right rightCurrent
          rightFuture →
        TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
        left' ≠ .skip left'.alphabet →
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv →
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv →
        outer.WellFormed alphabet →
        TypeLabel.Sync interface leftLabel TypeLabel.silent →
        TypeOffers outer (.par alphabet left right interface)
          leftLabel
          (left'.reannotate alphabet)
          (hideTypeOffers interface leftCurrent)
          (hideTypeOffers interface leftFuture)

end

end

end Pact
