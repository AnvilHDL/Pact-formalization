import Anvilpp.PactTypes.Syntax.PactTypeShapeLemmas

/-!
Live equivalence: two residuals with the same control skeleton whose alphabet
annotations differ only on actions their bodies no longer use.
-/

namespace Pact

noncomputable section

namespace PactTypeAlphabet

/-- Two alphabets agree on every action the given set records as still used. -/
def AgreeOn (left right : PactTypeAlphabet) (used : Finset BareMessage) : Prop :=
  ∀ action ∈ used, (action ∈ left.actions ↔ action ∈ right.actions)

theorem AgreeOn.refl (alphabet : PactTypeAlphabet) (used : Finset BareMessage) :
    AgreeOn alphabet alphabet used := fun _ _ => Iff.rfl

theorem AgreeOn.symm {left right : PactTypeAlphabet} {used : Finset BareMessage}
    (h : AgreeOn left right used) : AgreeOn right left used :=
  fun action hAction => (h action hAction).symm

theorem AgreeOn.trans {a b c : PactTypeAlphabet} {used : Finset BareMessage}
    (hab : AgreeOn a b used) (hbc : AgreeOn b c used) : AgreeOn a c used :=
  fun action hAction => (hab action hAction).trans (hbc action hAction)

theorem AgreeOn.mono {a b : PactTypeAlphabet} {used smaller : Finset BareMessage}
    (h : AgreeOn a b used) (hSub : smaller ⊆ used) : AgreeOn a b smaller :=
  fun action hAction => h action (hSub hAction)

end PactTypeAlphabet

namespace TypeEnvironment

/-- Two environments an residual cannot tell apart: they agree on the needs of
every action it still uses, and on the clock.  This is the formal content of the
paper's "no child rule or offer menu observes those actions". -/
def AgreeOnNeeds (env env' : TypeEnvironment) (used : Finset BareMessage) :
    Prop :=
  env.clock = env'.clock ∧
    (∀ action ∈ used, (typeNeed action ∈ env.immediate ↔
      typeNeed action ∈ env'.immediate)) ∧
    (∀ action ∈ used, (typeNeed action ∈ env.future ↔
      typeNeed action ∈ env'.future))

theorem AgreeOnNeeds.refl (env : TypeEnvironment) (used : Finset BareMessage) :
    AgreeOnNeeds env env used :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem AgreeOnNeeds.symm {env env' : TypeEnvironment}
    {used : Finset BareMessage} (h : AgreeOnNeeds env env' used) :
    AgreeOnNeeds env' env used :=
  ⟨h.1.symm, fun a ha => (h.2.1 a ha).symm, fun a ha => (h.2.2 a ha).symm⟩

theorem AgreeOnNeeds.mono {env env' : TypeEnvironment}
    {used smaller : Finset BareMessage} (h : AgreeOnNeeds env env' used)
    (hSub : smaller ⊆ used) : AgreeOnNeeds env env' smaller :=
  ⟨h.1, fun a ha => h.2.1 a (hSub ha), fun a ha => h.2.2 a (hSub ha)⟩

theorem AgreeOnNeeds.hasNeed {env env' : TypeEnvironment}
    {used : Finset BareMessage} (h : AgreeOnNeeds env env' used)
    {action : BareMessage} (hAction : action ∈ used) :
    env.hasNeed action ↔ env'.hasNeed action :=
  h.2.1 action hAction

end TypeEnvironment


namespace PactType

mutual

/-- The structural half of live equivalence: the same control skeleton, with
each pair of corresponding annotations agreeing on the actions that subterm
still uses. -/
def LiveEqBody : PactType → PactType → Prop
  | .message a m d, .message b m' d' =>
      m = m' ∧ d = d' ∧ PactTypeAlphabet.AgreeOn a b {(m, d)}
  | .progress _ p, .progress _ p' => p = p'
  | .tock _, .tock _ => True
  | .skip _, .skip _ => True
  | .var _ n, .var _ n' => n = n'
  | .choice a l r, .choice b l' r' =>
      PactTypeAlphabet.AgreeOn a b (MessageActions (.choice a l r)) ∧
        LiveEqBody l l' ∧ LiveEqBody r r'
  | .seq a l r, .seq b l' r' =>
      PactTypeAlphabet.AgreeOn a b (MessageActions (.seq a l r)) ∧
        LiveEqBody l l' ∧ LiveEqBody r r'
  | .fairChoice a bid l r, .fairChoice b bid' l' r' =>
      bid = bid' ∧
        PactTypeAlphabet.AgreeOn a b (MessageActions (.fairChoice a bid l r)) ∧
        LiveEqBody l l' ∧ LiveEqBody r r'
  | .par a l r i, .par b l' r' i' =>
      i = i' ∧ PactTypeAlphabet.AgreeOn a b (MessageActions (.par a l r i)) ∧
        LiveEqBody l l' ∧ LiveEqBody r r'
  | .recur a n body, .recur b n' body' =>
      n = n' ∧ PactTypeAlphabet.AgreeOn a b (MessageActions body) ∧
        LiveEqBody body body'
  | .xoffer a e bs, .xoffer b e' bs' =>
      PactTypeAlphabet.AgreeOn a b (MessageActions (.xoffer a e bs)) ∧
        LiveEqBody e e' ∧ LiveEqBranches bs bs'
  | .offer a e bs, .offer b e' bs' =>
      PactTypeAlphabet.AgreeOn a b (MessageActions (.offer a e bs)) ∧
        LiveEqBody e e' ∧ LiveEqBranches bs bs'
  | _, _ => False
  termination_by rho theta => sizeOf rho

/-- Branch lists are live-equivalent pointwise, with the same heads. -/
def LiveEqBranches :
    List (BareMessage × PactType) → List (BareMessage × PactType) → Prop
  | [], [] => True
  | (action, body) :: rest, (action', body') :: rest' =>
      action = action' ∧ LiveEqBody body body' ∧ LiveEqBranches rest rest'
  | _, _ => False
  termination_by branches _ => sizeOf branches
end

/-- Live equivalence: the structural condition plus equal outer alphabets, so
the two residuals range over the same environments. -/
def LiveEq (rho theta : PactType) : Prop :=
  rho.alphabet = theta.alphabet ∧ LiveEqBody rho theta

end PactType

end

end Pact
