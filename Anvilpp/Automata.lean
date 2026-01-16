import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

/-- Abstract versions of transition labels for automata. -/
inductive AbstractTransLabel : Type where
  | ε : AbstractTransLabel
  | tock : AbstractTransLabel
  | message : MessageId → AbstractTransLabel
  | branchTrue : BranchId → AbstractTransLabel
  | branchFalse : BranchId → AbstractTransLabel
  | dollar : ProcId → AbstractTransLabel

namespace AbstractTransLabel
  def isNonsync : AbstractTransLabel → Bool
    | ε => true
    | tock => false
    | message _ => false
    | branchTrue _ => true
    | branchFalse _ => true
    | dollar _ => true

  def fromConcrete : TransLabel → AbstractTransLabel
    | TransLabel.ε => AbstractTransLabel.ε
    | TransLabel.tock => AbstractTransLabel.tock
    | TransLabel.message msg _ => AbstractTransLabel.message msg
    | TransLabel.branchTrue bid => AbstractTransLabel.branchTrue bid
    | TransLabel.branchFalse bid => AbstractTransLabel.branchFalse bid
    | TransLabel.dollar pid => AbstractTransLabel.dollar pid
end AbstractTransLabel

inductive ProcTyNonInstant : ProcTy → Prop where
  | cycle :
    ProcTyNonInstant ProcTy.cycle
  | choice (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₁ →
    ProcTyNonInstant τ₂ →
    ProcTyNonInstant (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₁ →
    ProcTyNonInstant τ₂ →
    ProcTyNonInstant (ProcTy.choice_fair bid τ₁ τ₂)
  | seq_left (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₁ →
    ProcTyNonInstant (ProcTy.seq τ₁ τ₂)
  | seq_right (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₂ →
    ProcTyNonInstant (ProcTy.seq τ₁ τ₂)
  | par_left (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₁ →
    ProcTyNonInstant (ProcTy.par τ₁ τ₂)
  | par_right (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant τ₂ →
    ProcTyNonInstant (ProcTy.par τ₁ τ₂)
  -- | xoffer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
  --   ProcTyNonInstant τ_else →
  --   (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant ty) →
  --   ProcTyNonInstant (ProcTy.xoffer τ_else branch_tys)
  -- | offer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
  --   ProcTyNonInstant τ_else →
  --   (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant ty) →
  --   ProcTyNonInstant (ProcTy.offer τ_else branch_tys)
  | recur (x : String) (τ : ProcTy) :
    ProcTyNonInstant τ →
    ProcTyNonInstant (ProcTy.recur x τ)

inductive ProcTyNonInstantMsg : ProcTy → MessageId → Prop where
  | cycle (msg : MessageId) :
    ProcTyNonInstantMsg ProcTy.cycle msg
  | choice (τ₁ τ₂ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ₁ msg →
    ProcTyNonInstantMsg τ₂ msg →
    ProcTyNonInstantMsg (ProcTy.choice τ₁ τ₂) msg
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ₁ msg →
    ProcTyNonInstantMsg τ₂ msg →
    ProcTyNonInstantMsg (ProcTy.choice_fair bid τ₁ τ₂) msg
  | seq_left (τ₁ τ₂ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ₁ msg →
    ProcTyNonInstant τ₁ →
    ProcTyNonInstantMsg (ProcTy.seq τ₁ τ₂) msg
  | seq_right (τ₁ τ₂ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ₁ msg →
    ProcTyNonInstantMsg τ₂ msg →
    ProcTyNonInstantMsg (ProcTy.seq τ₁ τ₂) msg
  | par (τ₁ τ₂ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ₁ msg →
    ProcTyNonInstantMsg τ₂ msg →
    ProcTyNonInstantMsg (ProcTy.par τ₁ τ₂) msg
  -- | xoffer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (msg : MessageId) :
  --   ProcTyNonInstantMsg τ_else msg →
  --   (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg ty msg) →
  --   (∀ m ty, (m, ty) ∈ branch_tys → m.messageId ≠ msg) →
  --   ProcTyNonInstantMsg (ProcTy.xoffer τ_else branch_tys) msg
  -- | offer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (msg : MessageId) :
  --   ProcTyNonInstantMsg τ_else msg →
  --   (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg ty msg) →
  --   (∀ m ty, (m, ty) ∈ branch_tys → m.messageId ≠ msg) →
  --   ProcTyNonInstantMsg (ProcTy.offer τ_else branch_tys) msg
  | recur (x : String) (τ : ProcTy) (msg : MessageId) :
    ProcTyNonInstantMsg τ msg →
    ProcTyNonInstantMsg (ProcTy.recur x τ) msg
  | skip (msg : MessageId) :
    ProcTyNonInstantMsg ProcTy.skip msg
  | send (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.send msg') msg
  | recv (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.recv msg') msg

inductive ProcTyTransition : Finset MessageId → ProcTy → AbstractTransLabel → ProcTy → Prop where
  | message_send ex_msg (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.send msg) (AbstractTransLabel.message msg) τ
  | message_recv ex_msg (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.recv msg) (AbstractTransLabel.message msg) τ
  | par_left ex_msg (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ProcTyTransition ex_msg τ₁ lbl τ₁' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂)
  | par_right ex_msg (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ProcTyTransition ex_msg τ₂ lbl τ₂' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁ τ₂')
  | par_tock ex_msg (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg τ₁ AbstractTransLabel.tock τ₁ →
    ProcTyTransition ex_msg τ₂ AbstractTransLabel.tock τ₂ →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) AbstractTransLabel.tock (ProcTy.par τ₁ τ₂)
  | par_skip_left ex_msg (τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.par ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | par_skip_right ex_msg (τ₁ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.par τ₁ ProcTy.skip) AbstractTransLabel.ε τ₁
  | seq_step ex_msg (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyTransition ex_msg τ₁ lbl τ₁' →
    ProcTyTransition ex_msg (ProcTy.seq τ₁ τ₂) lbl (ProcTy.seq τ₁' τ₂)
  | seq_done ex_msg (τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.seq ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | choice_left ex_msg (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.choice τ₁ τ₂) AbstractTransLabel.ε τ₁
  | choice_right ex_msg (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.choice τ₁ τ₂) AbstractTransLabel.ε τ₂
  | choice_fair_left ex_msg (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.branchTrue bid) τ₁
  | choice_fair_right ex_msg (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.branchFalse bid) τ₂
  | recur_unfold ex_msg (x : String) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.recur x τ) AbstractTransLabel.ε (τ.replaceVar x (ProcTy.recur x τ))
  -- | xoffer_else ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
  --   (∀ m ty, (m, ty) ∈ branch_tys →
  --     m.messageId ∈ ex_msg) →
  --   ProcTyTransition ex_msg (ProcTy.xoffer τ_else branch_tys) AbstractTransLabel.ε τ_else
  -- | offer_else ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
  --   (∀ m ty, (m, ty) ∈ branch_tys →
  --     m.messageId ∈ ex_msg) →
  --   ProcTyTransition ex_msg (ProcTy.offer τ_else branch_tys) AbstractTransLabel.ε τ_else
  -- | xoffer_branch ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy))
  --     (me : MessageExch) (ty : ProcTy) :
  --   (me, ty) ∈ branch_tys →
  --   ProcTyTransition ex_msg (ProcTy.xoffer τ_else branch_tys)
  --     (AbstractTransLabel.message me.messageId) ty
  -- | offer_branch ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy))
  --     (me : MessageExch) (ty : ProcTy) :
  --   (me, ty) ∈ branch_tys →
  --   ProcTyTransition ex_msg (ProcTy.offer τ_else branch_tys)
  --     (AbstractTransLabel.message me.messageId) ty

inductive ProcTyCompTransition : ProcTyComposition → AbstractTransLabel → ProcTyComposition → Prop where
  | nonsync (ex_msg : Finset MessageId) (τ τ' : ProcTy) (τs : ProcTyComposition) (lbl : AbstractTransLabel) :
    lbl.isNonsync →
    ProcTyTransition ex_msg τ lbl τ' →
    (∀ msg ∈ ex_msg, ProcTyNonInstantMsg τ msg) →
    ProcTyCompTransition (τs + {τ}) lbl (τs + {τ'})
  | message (τ₁ τ₂ τ'₁ τ'₂ : ProcTy) (τs : ProcTyComposition) (msg : MessageId) :
    ProcTyTransition ∅ τ₁ (AbstractTransLabel.message msg) τ'₁ →
    ProcTyTransition ∅ τ₂ (AbstractTransLabel.message msg) τ'₂ →
    ProcTyCompTransition (τs + {τ₁, τ₂}) (AbstractTransLabel.message msg) (τs + {τ'₁, τ'₂})
  | tock (τs τs' : ProcTyComposition) :
    Multiset.Rel (fun τ τ' => ProcTyTransition ∅ τ AbstractTransLabel.tock τ') τs τs' →
    ProcTyCompTransition τs AbstractTransLabel.tock τs'

inductive ProcTyReachable : ProcTy → ProcTy → Prop where
  | base (τ : ProcTy) :
    ProcTyReachable τ τ
  | step (τ₁ τ₂ τ₃ : ProcTy) (ex_msg : Finset MessageId) (lbl : AbstractTransLabel) :
    ProcTyTransition ex_msg τ₁ lbl τ₂ →
    ProcTyReachable τ₂ τ₃ →
    ProcTyReachable τ₁ τ₃

inductive ProcTyCompReachable : ProcTyComposition → ProcTyComposition → Prop where
  | base (τs : ProcTyComposition) :
    ProcTyCompReachable τs τs
  | step (τs₁ τs₂ τs₃ : ProcTyComposition) (lbl : AbstractTransLabel) :
    ProcTyCompTransition τs₁ lbl τs₂ →
    ProcTyCompReachable τs₂ τs₃ →
    ProcTyCompReachable τs₁ τs₃
