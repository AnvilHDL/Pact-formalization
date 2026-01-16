import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

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

inductive ProcTyNonInstantMsg : ProcTy → (MessageId × MessageDir) → Prop where
  | cycle (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg ProcTy.cycle mx
  | choice (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ₁ mx →
    ProcTyNonInstantMsg τ₂ mx →
    ProcTyNonInstantMsg (ProcTy.choice τ₁ τ₂) mx
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ₁ mx →
    ProcTyNonInstantMsg τ₂ mx →
    ProcTyNonInstantMsg (ProcTy.choice_fair bid τ₁ τ₂) mx
  | seq_left (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ₁ mx →
    ProcTyNonInstant τ₁ →
    ProcTyNonInstantMsg (ProcTy.seq τ₁ τ₂) mx
  | seq_right (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ₁ mx →
    ProcTyNonInstantMsg τ₂ mx →
    ProcTyNonInstantMsg (ProcTy.seq τ₁ τ₂) mx
  | par (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ₁ mx →
    ProcTyNonInstantMsg τ₂ mx →
    ProcTyNonInstantMsg (ProcTy.par τ₁ τ₂) mx
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
  | recur (x : String) (τ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg τ mx →
    ProcTyNonInstantMsg (ProcTy.recur x τ) mx
  | skip (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg ProcTy.skip mx
  | send (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.send)
  | send_opposite (msg msg' : MessageId) :
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.recv)
  | recv (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.recv)
  | recv_opposite (msg msg' : MessageId) :
    ProcTyNonInstantMsg (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.send)

inductive ProcTyTransition : Finset (MessageId × MessageDir) → ProcTy → AbstractTransLabel → ProcTy → Prop where
  | message_send ex_msg (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.send msg) (AbstractTransLabel.message msg MessageDir.send) τ
  | message_recv ex_msg (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.recv msg) (AbstractTransLabel.message msg MessageDir.recv) τ
  | par_left ex_msg ex_msg' (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ex_msg' ⊆ ex_msg →
    (∀ mx ∈ ex_msg', ProcTyNonInstantMsg τ₂ mx) →
    ProcTyTransition ex_msg τ₁ lbl τ₁' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂)
  | par_right ex_msg ex_msg' (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ex_msg' ⊆ ex_msg →
    (∀ mx ∈ ex_msg', ProcTyNonInstantMsg τ₁ mx) →
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
  | par_message ex_msg ex_msg₁ ex_msg₂ (τ₁ τ₂ τ'₁ τ'₂ : ProcTy) (msg : MessageId) (d₁ d₂ : MessageDir) :
    MessageDir.dual d₁ d₂ →
    ex_msg₁ ⊆ ex_msg →
    ex_msg₂ ⊆ ex_msg →
    (∀ mx ∈ ex_msg₂, ProcTyNonInstantMsg τ₁ mx) →
    (∀ mx ∈ ex_msg₁, ProcTyNonInstantMsg τ₂ mx) →
    ProcTyTransition ∅ τ₁ (AbstractTransLabel.message msg d₁) τ'₁ →
    ProcTyTransition ∅ τ₂ (AbstractTransLabel.message msg d₂) τ'₂ →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) (AbstractTransLabel.message msg MessageDir.complete) (ProcTy.par τ'₁ τ'₂)
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

def ProcTyCompTransition (τ₁ : ProcTyComposition) (lbl : AbstractTransLabel) (τ₂ : ProcTyComposition) : Prop :=
  lbl.isComplete ∧
  ∃ ex_msg : Finset (MessageId × MessageDir),
    ProcTyTransition ex_msg τ₁ lbl τ₂

inductive ProcTyReachable : ProcTy → ProcTy → Prop where
  | base (τ : ProcTy) :
    ProcTyReachable τ τ
  | step (τ₁ τ₂ τ₃ : ProcTy) (ex_msg : Finset (MessageId × MessageDir)) (lbl : AbstractTransLabel) :
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
