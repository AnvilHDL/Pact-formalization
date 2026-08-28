import Anvilpp.PactTypes.Syntax.PactTypeFutureOffers

/-!
# The operational type-transition judgment and conformance/refinement definitions
-/

namespace Pact

noncomputable section

/-! ## Type transition system -/

/-- The erased, environment-indexed type judgment `Eτ ⊢ τ -α→ τ'`. -/
@[aesop unsafe]
inductive TypeTransition : TypeEnvironment → PactType → TypeLabel → PactType → Prop where
  | action (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      env.hasNeed (msg, dir) →
      --
      TypeTransition env (.message alphabet msg dir)
      (TypeLabel.message msg dir)
      (.skip alphabet)
  | action_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      ¬ env.hasNeed (msg, dir) ∧
      env.clock = false →
      --
      TypeTransition env (.message alphabet msg dir)
      TypeLabel.silent
      (.message alphabet msg dir)
  | choice_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (left right : PactType) :
      env.WellFormed →
      env.clock = false →
      --
      TypeTransition env (.choice alphabet left right)
      TypeLabel.silent
      left
  | choice_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (left right : PactType) :
      env.WellFormed →
      env.clock = false →
      --
      TypeTransition env (.choice alphabet left right)
      TypeLabel.silent
      right
  | fair_left (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      env.clock = false →
      --
      TypeTransition env (.fairChoice alphabet bid left right)
      (TypeLabel.fair bid true)
      left
  | fair_right (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      env.clock = false →
      --
      TypeTransition env (.fairChoice alphabet bid left right)
      (TypeLabel.fair bid false)
      right
  | cycle (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed ∧
      env.clock = true →
      --
      TypeTransition env (.tock alphabet)
      .tock
      (.skip alphabet)
  | cycle_wait (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed ∧
      env.clock = false →
      --
      TypeTransition env (.tock alphabet)
      TypeLabel.silent
      (.tock alphabet)
  | skip (env : TypeEnvironment) (alphabet : PactTypeAlphabet) :
      env.WellFormed ∧
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
      env.WellFormed →
      env.clock = false →
      --
      TypeTransition env (.progress alphabet pid)
      (TypeLabel.progress pid)
      (.skip alphabet)
  | recur (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (var : String) (body : PactType) :
      env.WellFormed →
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
      env.WellFormed ∧
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
      env.WellFormed ∧
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
      env.WellFormed ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.xoffer alphabet elseType branches)
      TypeLabel.silent
      (.xoffer alphabet elseType branches)
  | offer_some (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : BareMessage × PactType) :
      env.WellFormed ∧
      enabled ∈ branches ∧
      TypeBranchEnabled env enabled →
      --
      TypeTransition env (.offer alphabet elseType branches)
      TypeLabel.silent
      (parallelTypeBranchesSelecting enabled branches)
  | offer_else (env : TypeEnvironment) (alphabet : PactTypeAlphabet)
      (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
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
      env.WellFormed ∧
      env.clock = false ∧
      TypeNoImmediateBranch env branches ∧
      ¬ TypeResolved env branches →
      --
      TypeTransition env (.offer alphabet elseType branches)
      TypeLabel.silent
      (.offer alphabet elseType branches)
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      TypeTransition leftEnv left leftLabel left' →
      TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
      TypeTransition rightEnv right rightLabel right' →
      TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
      ¬ (left' = .skip left'.alphabet ∧ right' = .skip right'.alphabet) →
      (outer.WellFormed ∧
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv ∧
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par (PactTypeAlphabet.mergeHidden left.alphabet
        right.alphabet interface) left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
        left' right' interface)
  | par_fuse (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left right : PactType) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      TypeTransition leftEnv left leftLabel (.skip left.alphabet) →
      TypeOffers leftEnv left leftLabel (.skip left.alphabet) leftCurrent
        leftFuture →
      TypeTransition rightEnv right rightLabel (.skip right.alphabet) →
      TypeOffers rightEnv right rightLabel (.skip right.alphabet) rightCurrent
        rightFuture →
      (outer.WellFormed ∧
        LocalTypeOfferEnvironment outer interface left rightEnv rightCurrent
          rightFuture leftEnv ∧
        LocalTypeOfferEnvironment outer interface right leftEnv leftCurrent
          leftFuture rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par (PactTypeAlphabet.mergeHidden left.alphabet
        right.alphabet interface) left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.skip (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet
        interface))

structure TypeOfferSummary : Type where
  current : Finset BareMessage
  future : Finset BareMessage
  deriving DecidableEq

def DecoratedTypeTransition
    (env : TypeEnvironment) (source : PactType) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : PactType) : Prop :=
  TypeTransition env source label target ∧
  TypeOffers env source label target offers.current offers.future

/-- Every semantic type step carries at least one environment-specific offer pair. -/
theorem TypeTransition.exists_typeOffers
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ current future, TypeOffers env source label target current future := by
  induction transition with
  | action env alphabet msg dir conditions =>
      exact ⟨{(msg, dir)}, typeFutureOffers (.skip alphabet),
        TypeOffers.action env alphabet msg dir conditions⟩
  | action_wait env alphabet msg dir conditions =>
      exact ⟨{(msg, dir)},
        typeFutureOffers (.message alphabet msg dir) \ {(msg, dir)},
        TypeOffers.action_wait env alphabet msg dir conditions⟩
  | choice_left env alphabet left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers left,
        TypeOffers.choice_left env alphabet left right ⟨hEnv, hClock⟩⟩
  | choice_right env alphabet left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers right,
        TypeOffers.choice_right env alphabet left right ⟨hEnv, hClock⟩⟩
  | fair_left env alphabet bid left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers left,
        TypeOffers.fair_left env alphabet bid left right ⟨hEnv, hClock⟩⟩
  | fair_right env alphabet bid left right hEnv hClock =>
      exact ⟨∅, typeFutureOffers right,
        TypeOffers.fair_right env alphabet bid left right ⟨hEnv, hClock⟩⟩
  | cycle env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.cycle env alphabet conditions⟩
  | cycle_wait env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.cycle_wait env alphabet conditions⟩
  | skip env alphabet conditions =>
      exact ⟨∅, ∅, TypeOffers.skip env alphabet conditions⟩
  | seq_fuse env alphabet skipAlphabet left right label _ ihLeft =>
      obtain ⟨current, childFuture, hOffers⟩ := ihLeft
      exact ⟨current, typeFutureOffers right \ current,
        TypeOffers.seq_fuse env alphabet skipAlphabet left right label current
          childFuture hOffers⟩
  | progress env alphabet pid hEnv hClock =>
      exact ⟨∅, ∅, TypeOffers.progress env alphabet pid ⟨hEnv, hClock⟩⟩
  | recur env alphabet name body hEnv hClock =>
      exact ⟨∅,
        typeFutureOffers (body.replaceVar name (.recur alphabet name body)),
        TypeOffers.recur env alphabet name body ⟨hEnv, hClock⟩⟩
  | seq env alphabet left left' right label _ hNotSkip ihLeft =>
      obtain ⟨current, childFuture, hOffers⟩ := ihLeft
      exact ⟨current, typeFutureOffers (.seq alphabet left' right) \ current,
        TypeOffers.seq env alphabet left left' right label current childFuture
          hOffers hNotSkip⟩
  | xoffer_branch env alphabet elseType branches action processType conditions =>
      exact ⟨{action}, typeFutureOffers processType,
        TypeOffers.xoffer_branch env alphabet elseType branches action
          processType conditions⟩
  | xoffer_else env alphabet elseType branches conditions =>
      exact ⟨∅, typeFutureOffers elseType,
        TypeOffers.xoffer_else env alphabet elseType branches conditions⟩
  | xoffer_wait env alphabet elseType branches conditions =>
      exact ⟨typeWaitingOffers env branches,
        typeFutureOffers (.xoffer alphabet elseType branches) \
          typeWaitingOffers env branches,
        TypeOffers.xoffer_wait env alphabet elseType branches conditions⟩
  | offer_some env alphabet elseType branches enabled conditions =>
      exact ⟨∅, typeFutureOffers (parallelTypeBranchesSelecting enabled branches),
        TypeOffers.offer_some env alphabet elseType branches enabled conditions⟩
  | offer_else env alphabet elseType branches conditions =>
      exact ⟨typeBranchActions branches, typeFutureOffers elseType,
        TypeOffers.offer_else env alphabet elseType branches conditions⟩
  | offer_wait env alphabet elseType branches conditions =>
      exact ⟨typeWaitingOffers env branches,
        typeFutureOffers (.offer alphabet elseType branches) \
          typeWaitingOffers env branches,
        TypeOffers.offer_wait env alphabet elseType branches conditions⟩
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture _ hLeftOffers
      _ hRightOffers hNotBothSkip conditions ihLeft ihRight =>
      exact ⟨hideTypeOffers interface (leftCurrent ∪ rightCurrent),
        hideTypeOffers interface (leftFuture ∪ rightFuture),
        TypeOffers.par outer leftEnv rightEnv interface left left' right right'
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers hNotBothSkip conditions.2.1
          conditions.2.2.1 ⟨conditions.1, conditions.2.2.2⟩⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture _ hLeftOffers _
      hRightOffers conditions ihLeft ihRight =>
      exact ⟨hideTypeOffers interface (leftCurrent ∪ rightCurrent),
        hideTypeOffers interface (leftFuture ∪ rightFuture),
        TypeOffers.par_fuse outer leftEnv rightEnv interface left right
          leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers conditions.2.1 conditions.2.2.1
          ⟨conditions.1, conditions.2.2.2⟩⟩

/-- Package a semantic step together with one of its offer pairs. -/
theorem TypeTransition.exists_decorated
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ offers, DecoratedTypeTransition env source label offers target := by
  obtain ⟨current, future, hOffers⟩ := transition.exists_typeOffers
  exact ⟨{ current := current, future := future }, transition, hOffers⟩

/-- A semantic type step preserves the fixed syntactic alphabet of an
admissible source type.  The transition rules are intentionally not cluttered
with these equalities; they are recovered from `AlphabetWellFormed`. -/
theorem TypeTransition.preserves_alphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hSource : source.AlphabetWellFormed)
    (transition : TypeTransition env source label target) :
    target.alphabet = source.alphabet := by
  induction transition with
  | action env alphabet msg dir conditions =>
      simp [PactType.alphabet]
  | action_wait env alphabet msg dir conditions =>
      simp [PactType.alphabet]
  | choice_left env alphabet left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | choice_right env alphabet left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | fair_left env alphabet bid left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | fair_right env alphabet bid left right hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.2.1
  | cycle env alphabet conditions =>
      simp [PactType.alphabet]
  | cycle_wait env alphabet conditions =>
      simp [PactType.alphabet]
  | skip env alphabet conditions =>
      simp [PactType.alphabet]
  | seq_fuse env alphabet skipAlphabet left right label childTransition ihLeft =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.2.1
  | progress env alphabet pid hEnv hClock =>
      simp [PactType.alphabet]
  | recur env alphabet name body hEnv hClock =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hBody : body.alphabet = alphabet := hSource.2.1
      have hReplacement :
          (PactType.recur alphabet name body).alphabet = body.alphabet := by
        simpa [PactType.alphabet] using hBody.symm
      have hReplace :=
        PactType.replaceVar_alphabet_eq_of_replacement body name hReplacement
      change (body.replaceVar name (PactType.recur alphabet name body)).alphabet =
        alphabet
      exact hReplace.trans hBody
  | seq env alphabet left left' right label childTransition hNotSkip ihLeft =>
      simp [PactType.alphabet]
  | xoffer_branch env alphabet elseType branches action processType conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hBranch :
          processType.alphabet = alphabet :=
        PactType.branch_alphabet_eq_of_mem hSource.2.2.2 conditions.2.1
      simpa [PactType.alphabet] using hBranch
  | xoffer_else env alphabet elseType branches conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | xoffer_wait env alphabet elseType branches conditions =>
      simp [PactType.alphabet]
  | offer_some env alphabet elseType branches enabled conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      have hSelected :
          (parallelTypeBranchesSelecting enabled branches).alphabet =
            alphabet :=
        parallelTypeBranchesSelecting_alphabet_eq_of_mem conditions.2.1
          hSource.2.2.2
      simpa [PactType.alphabet] using hSelected
  | offer_else env alphabet elseType branches conditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using hSource.2.1
  | offer_wait env alphabet elseType branches conditions =>
      simp [PactType.alphabet]
  | par outer leftEnv rightEnv interface left left' right right' leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture leftTransition
      hLeftOffers rightTransition hRightOffers hNotBothSkip conditions ihLeft
      ihRight =>
      simp [PactType.alphabet]
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture leftTransition
      hLeftOffers rightTransition hRightOffers conditions ihLeft ihRight =>
      simp [PactType.alphabet]

theorem DecoratedTypeTransition.preserves_alphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hSource : source.AlphabetWellFormed)
    (transition : DecoratedTypeTransition env source label offers target) :
    target.alphabet = source.alphabet :=
  TypeTransition.preserves_alphabet hSource transition.1

/-- `Ready(E,R)`: `R` has at least one step under `E`. -/
def TypeReady (env : TypeEnvironment) (processType : PactType) : Prop :=
  ∃ label target, TypeTransition env processType label target

/-- `Ready(E,P)` at the process level. -/
def ProcessReady (env : Environment) (process : Proc) : Prop :=
  ∃ label target, ProcessTransition env process label target

/--
An erased alternating simulation witnessing `P ⊧ τ` (`pactformalappendix.typ`,
"Erasure"). Besides matching every process resolution with a single erased
type step (not a weak, epsilon-padded one), it reflects availability from the
type to the process: a winning environment choice transferred from a type
strategy must not become stuck merely by being realized concretely.
-/
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

/--
The precision preorder `precise ⊑ abstract` (Definition 4.2), an alternating
simulation over single *decorated* type steps: the response and availability
clauses are indexed by the same label and the same current/future offer pair
`(O_C,O_F)` on both sides (the offer-polarity condition needed for the
parallel-composition congruence, `pactformalappendix.typ`/`pactproofs.typ`
Lemma 4.7), and a related pair agrees on whether it is literally `skip`.
-/
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
