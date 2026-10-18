import Anvilpp.PactTypes.Proofs.Syntax.PactTypeFutureOffersLemmas

namespace Pact

noncomputable section

/-! ## Type transition system -/

/-- The erased, environment-indexed type judgment `Eτ ⊢ τ -α→ τ'`.

Environment admissibility prevents undeclared heads from firing. Waiting and
offer resolution have no additional declaration premise; the decorated rules
project advertised actions to the source alphabet. -/
@[aesop unsafe]
inductive TypeTransition : TypeEnvironment → PactType → TypeLabel → PactType → Prop where
  | action (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (dir : MessageDir) :
      env.WellFormed alphabet ∧
      env.hasNeed (msg, dir) →
      --
      TypeTransition env (.message alphabet msg dir)
      (TypeLabel.message msg dir)
      (.skip alphabet)
  | action_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (dir : MessageDir) :
      env.WellFormed alphabet ∧
      ¬ env.hasNeed (msg, dir) ∧
      env.clock = false →
      --
      TypeTransition env (.message alphabet msg dir)
      TypeLabel.silent
      (.message alphabet msg dir)
  | choice_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (left right : PactType) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.choice alphabet left right)
      TypeLabel.silent
      left
  | choice_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (left right : PactType) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.choice alphabet left right)
      TypeLabel.silent
      right
  | fair_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (left right : PactType) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.fairChoice alphabet bid left right)
      (TypeLabel.fair bid true)
      left
  | fair_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (left right : PactType) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.fairChoice alphabet bid left right)
      (TypeLabel.fair bid false)
      right
  | cycle (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧
      env.clock = true →
      --
      TypeTransition env (.tock alphabet)
      .tock
      (.skip alphabet)
  | cycle_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧
      env.clock = false →
      --
      TypeTransition env (.tock alphabet)
      TypeLabel.silent
      (.tock alphabet)
  | skip (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed alphabet ∧
      env.clock = false →
      --
      TypeTransition env (.skip alphabet)
      TypeLabel.silent
      (.skip alphabet)
  | seq_fuse (env : TypeEnvironment) (alphabet skipAlphabet : PactTypeAlphabet)
      (left right : PactType) (label : TypeLabel) :
      TypeTransition env left label (.skip skipAlphabet) →
      --
      TypeTransition env (.seq alphabet left right)
      label
      right
  | progress (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (pid : ProcId) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.progress alphabet pid)
      (TypeLabel.progress pid)
      (.skip alphabet)
  | recur (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (var : String) (body : PactType) :
      env.WellFormed alphabet →
      env.clock = false →
      --
      TypeTransition env (.recur alphabet var body)
      TypeLabel.silent
      (body.replaceVar var (.recur alphabet var body))
  | seq (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (left left' right : PactType) (label : TypeLabel) :
      TypeTransition env left label left' →
      left' ≠ .skip left'.alphabet →
      --
      TypeTransition env (.seq alphabet left right)
      label
      (.seq alphabet left' right)
  | xoffer_branch (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (action : BareMessage) (processType : PactType) :
      env.WellFormed alphabet ∧
      (action, processType) ∈ branches ∧
      TypeBranchEnabled env (action, processType) ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer alphabet elseType branches)
      (TypeLabel.message action.1 action.2)
      processType
  | xoffer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed alphabet ∧
      env.clock = false ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer alphabet elseType branches)
      TypeLabel.silent
      elseType
  | xoffer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed alphabet ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.xoffer alphabet elseType branches)
      TypeLabel.silent
      (.xoffer alphabet elseType branches)
  | offer_some (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : Finset Nat) :
      env.WellFormed alphabet ∧
      enabled.Nonempty ∧
      typeEnabledBranches env branches = enabled →
      --
      TypeTransition env (.offer alphabet elseType branches)
      (typeBranchBatchLabel branches enabled)
      (parallelTypeBranchesFiring alphabet enabled branches)
  | offer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed alphabet ∧
      env.clock = false ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.offer alphabet elseType branches)
      TypeLabel.silent
      elseType
  | offer_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed alphabet ∧
      env.clock = false ∧
      TypeNoImmediateBranch env branches ∧
      ¬ TypeResolved env branches →
      --
      TypeTransition env (.offer alphabet elseType branches)
      TypeLabel.silent
      (.offer alphabet elseType branches)
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (alphabet : PactTypeAlphabet)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      left ≠ .skip left.alphabet →
      right ≠ .skip right.alphabet →
      TypeTransition leftEnv left leftLabel left' →
      TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
      TypeTransition rightEnv right rightLabel right' →
      TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
      ¬ (left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet) →
      (outer.WellFormed alphabet ∧
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv ∧
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par alphabet left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.par alphabet
        left' right' interface)
  | par_fuse (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (alphabet : PactTypeAlphabet)
      (left right : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      TypeTransition leftEnv left leftLabel (.skip left.alphabet) →
      TypeOffers leftEnv left leftLabel (.skip left.alphabet) leftCurrent
        leftFuture →
      TypeTransition rightEnv right rightLabel (.skip right.alphabet) →
      TypeOffers rightEnv right rightLabel (.skip right.alphabet) rightCurrent
        rightFuture →
      (outer.WellFormed alphabet ∧
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv ∧
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par alphabet left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.skip alphabet)
  -- T-Par-Left: the left side is already `skip`, so only the right survives.
  -- The finished side still takes its silent `skip` step, both local
  -- environments are checked against the sibling's offers, and the labels
  -- synchronize.  `skip` cannot step under a clock environment, so survivor
  -- entry is non-clock.
  | left_complete (outer leftEnv rightEnv : TypeEnvironment)
      (interface : Interface) (alphabet : PactTypeAlphabet)
      (left right right' : PactType) (rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      left = .skip left.alphabet →
      right ≠ .skip right.alphabet →
      TypeTransition leftEnv left TypeLabel.silent left →
      TypeOffers leftEnv left TypeLabel.silent left leftCurrent leftFuture →
      TypeTransition rightEnv right rightLabel right' →
      TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
      right' ≠ .skip right'.alphabet →
      LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet →
      TypeLabel.Sync interface TypeLabel.silent rightLabel →
      --
      TypeTransition outer (.par alphabet left right interface)
      rightLabel
      (right'.reannotate alphabet)
  -- T-Par-Right: mirror of `left_complete`; the right side is already `skip`.
  | right_complete (outer leftEnv rightEnv : TypeEnvironment)
      (interface : Interface) (alphabet : PactTypeAlphabet)
      (left left' right : PactType) (leftLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      right = .skip right.alphabet →
      left ≠ .skip left.alphabet →
      TypeTransition rightEnv right TypeLabel.silent right →
      TypeOffers rightEnv right TypeLabel.silent right rightCurrent
        rightFuture →
      TypeTransition leftEnv left leftLabel left' →
      TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
      left' ≠ .skip left'.alphabet →
      LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
        leftFuture rightEnv →
      outer.WellFormed alphabet →
      TypeLabel.Sync interface leftLabel TypeLabel.silent →
      --
      TypeTransition outer (.par alphabet left right interface)
      leftLabel
      (left'.reannotate alphabet)

structure TypeOfferSummary : Type where
  current : Finset BareMessage
  future : Finset BareMessage
  deriving DecidableEq

def DecoratedTypeTransition
    (env : TypeEnvironment) (source : PactType) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : PactType) : Prop :=
  TypeTransition env source label target ∧
  TypeOffers env source label target offers.current offers.future

/-- `Ready(E,R)`: `R` has at least one step under `E`. -/
def TypeReady (env : TypeEnvironment) (processType : PactType) : Prop :=
  ∃ label target, TypeTransition env processType label target

/-- An erased alternating simulation witnessing `P ⊧ τ`: it matches every
process resolution with a single erased type step, and reflects availability
from the type back to the process. -/
structure ConformanceWitness (process : Proc) (processType : PactType) : Type where
  relation : Proc → PactType → Prop
  initial : relation process processType
  readyReflect :
    ∀ {p₀ : Proc} {τ₀ : PactType} {env : Environment},
      relation p₀ τ₀ →
      TypeReady (eraseEnvironment env) τ₀ →
      ProcessReady env p₀
  matchStep :
    ∀ {p₀ p₁ : Proc} {τ₀ : PactType} {env : Environment} {label : Label},
      relation p₀ τ₀ →
      ProcessTransition env p₀ label p₁ →
      ∃ τ₁,
        TypeTransition (eraseEnvironment env) τ₀ (eraseLabel label) τ₁ ∧
        relation p₁ τ₁

/-- Process-type conformance, `P ⊧ τ` (Definition 4.1). -/
def Conforms (process : Proc) (processType : PactType) : Prop :=
  Nonempty (ConformanceWitness process processType)

/-- The precision preorder `precise ⊑ abstract`: an alternating simulation over
single decorated type steps, indexed by the same label and the same
current/future offer pair, with related pairs agreeing on whether they are
literally `skip`. -/
structure RefinementWitness (precise abstract : PactType) : Type where
  relation : PactType → PactType → Prop
  initial : relation precise abstract
  skipIff :
    ∀ {τ₀ τ₀' : PactType}, relation τ₀ τ₀' →
      ((∃ alphabet, τ₀ = .skip alphabet) ↔
        (∃ alphabet, τ₀' = .skip alphabet))
  availability :
    ∀ {τ₀ τ₀' τ₁' : PactType} {env : TypeEnvironment} {label : TypeLabel}
      {offers : TypeOfferSummary},
      relation τ₀ τ₀' →
      DecoratedTypeTransition env τ₀' label offers τ₁' →
      ∃ τ₁, DecoratedTypeTransition env τ₀ label offers τ₁
  response :
    ∀ {τ₀ τ₀' τ₁ : PactType} {env : TypeEnvironment} {label : TypeLabel}
      {offers : TypeOfferSummary},
      relation τ₀ τ₀' →
      DecoratedTypeTransition env τ₀ label offers τ₁ →
      ∃ τ₁',
        DecoratedTypeTransition env τ₀' label offers τ₁' ∧ relation τ₁ τ₁'

/-- `precise ⊑ abstract` (Definition 4.2). -/
def Refines (precise abstract : PactType) : Prop :=
  Nonempty (RefinementWitness precise abstract)

/-- Data-oblivious type checking (Definition 4.3). -/
def DataObliviousChecks (process : Proc) (claimed : PactType) : Prop :=
  Refines (inferProcess process) claimed

end

end Pact
