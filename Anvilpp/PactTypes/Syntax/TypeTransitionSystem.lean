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
  | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      env.hasNeed (msg, dir) →
      --
      TypeTransition env (.message msg dir)
      (TypeLabel.message msg dir)
      .skip
  | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      ¬ env.hasNeed (msg, dir) ∧
      env.clock = false →
      --
      TypeTransition env (.message msg dir)
      TypeLabel.silent
      (.message msg dir)
  | choice_left (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.choice left right)
      TypeLabel.silent
      left
  | choice_right (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.choice left right)
      TypeLabel.silent
      right
  | fair_left (env : TypeEnvironment) (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.fairChoice bid left right)
      (TypeLabel.fair bid true)
      left
  | fair_right (env : TypeEnvironment) (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.fairChoice bid left right)
      (TypeLabel.fair bid false)
      right
  | cycle (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = true →
      --
      TypeTransition env .tock
      .tock
      .skip
  | cycle_wait (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = false →
      --
      TypeTransition env .tock
      TypeLabel.silent
      .tock
  | skip (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = false →
      --
      TypeTransition env .skip
      TypeLabel.silent
      .skip
  | seq_fuse (env : TypeEnvironment) (left right : PactType) (label : TypeLabel) :
      TypeTransition env left label .skip →
      --
      TypeTransition env (.seq left right)
      label
      right
  | progress (env : TypeEnvironment) (pid : ProcId) :
      env.WellFormed →
      --
      TypeTransition env (.progress pid)
      (TypeLabel.progress pid)
      .skip
  | recur (env : TypeEnvironment) (var : String) (body : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.recur var body)
      TypeLabel.silent
      (body.replaceVar var (.recur var body))
  | seq (env : TypeEnvironment) (left left' right : PactType) (label : TypeLabel) :
      TypeTransition env left label left' →
      left' ≠ .skip →
      --
      TypeTransition env (.seq left right)
      label
      (.seq left' right)
  | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (action : BareMessage) (processType : PactType) :
      env.WellFormed ∧
      (action, processType) ∈ branches ∧
      TypeBranchEnabled env (action, processType) ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer elseType branches)
      (TypeLabel.message action.1 action.2)
      processType
  | xoffer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer elseType branches)
      TypeLabel.silent
      elseType
  | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.xoffer elseType branches)
      TypeLabel.silent
      (.xoffer elseType branches)
  | offer_some (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : BareMessage × PactType) :
      env.WellFormed ∧
      enabled ∈ branches ∧
      TypeBranchEnabled env enabled →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      (parallelTypeBranchesSelecting enabled branches)
  | offer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      elseType
  | offer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      (.offer elseType branches)
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel) :
      TypeTransition leftEnv left leftLabel left' →
      TypeTransition rightEnv right rightLabel right' →
      ¬ (left' = .skip ∧ right' = .skip) →
      (outer.WellFormed ∧
        LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv ∧
        LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.par left' right' interface)
  | par_fuse (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left right : PactType) (leftLabel rightLabel : TypeLabel) :
      TypeTransition leftEnv left leftLabel .skip →
      TypeTransition rightEnv right rightLabel .skip →
      (outer.WellFormed ∧
        LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv ∧
        LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      .skip

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
  | xoffer_branch env elseType branches action processType conditions =>
      exact ⟨{action}, typeFutureOffers processType,
        TypeOffers.xoffer_branch env elseType branches action processType conditions⟩
  | _ => aesop

/-- Package a semantic step together with one of its offer pairs. -/
theorem TypeTransition.exists_decorated
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ offers, DecoratedTypeTransition env source label offers target := by
  obtain ⟨current, future, hOffers⟩ := transition.exists_typeOffers
  exact ⟨{ current := current, future := future }, transition, hOffers⟩

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
    ∀ {τ₀ τ₀' : PactType}, relation τ₀ τ₀' → (τ₀ = .skip ↔ τ₀' = .skip)
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
