import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing

def branch_to_xoffer_ty (br : MessageExch × ProcTy) : ProcTy := ProcTy.xoffer ProcTy.skip [br]

@[aesop unsafe]
inductive ProcTyTransition : ProcTy → AbstractTransLabel → ProcTy → Prop where
  | tock :
    ProcTyTransition ProcTy.cycle (AbstractTransLabel.ac Action.tock) ProcTy.skip
  | message_send (msg : MessageId) :
    ProcTyTransition (ProcTy.message $ MessageExch.send msg) (AbstractTransLabel.message msg MessageDir.send) ProcTy.skip
  | message_recv (msg : MessageId) :
    ProcTyTransition (ProcTy.message $ MessageExch.recv msg) (AbstractTransLabel.message msg MessageDir.recv) ProcTy.skip
  | par_left (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ac Action.tock →
    ¬ lbl.isEx →
    ProcTyTransition τ₁ lbl τ₁' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂)
  | par_right (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ac Action.tock →
    ¬ lbl.isEx →
    ProcTyTransition τ₂ lbl τ₂' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁ τ₂')
  | par_left_ex (ex_msg : Finset (MessageId × MessageDir)) (τ₁ τ₁' τ₂ : ProcTy) :
    (∀ mx ∈ ex_msg, ProcTyNonInstantMsg ∅ ∅ τ₂ mx) →
    ProcTyTransition τ₁ (AbstractTransLabel.ex ex_msg) τ₁' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ex ex_msg) (ProcTy.par τ₁' τ₂)
  | par_right_ex (ex_msg : Finset (MessageId × MessageDir)) (τ₁ τ₂ τ₂' : ProcTy) :
    (∀ mx ∈ ex_msg, ProcTyNonInstantMsg ∅ ∅ τ₁ mx) →
    ProcTyTransition τ₂ (AbstractTransLabel.ex ex_msg) τ₂' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ex ex_msg) (ProcTy.par τ₁ τ₂')
  | par_tock (τ₁ τ₂ τ₁' τ₂' : ProcTy) :
    ProcTyTransition τ₁ (AbstractTransLabel.ac Action.tock) τ₁' →
    ProcTyTransition τ₂ (AbstractTransLabel.ac Action.tock) τ₂' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac Action.tock) (ProcTy.par τ₁' τ₂')
  | par_skip_left (τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.par ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | par_skip_right (τ₁ : ProcTy) :
    ProcTyTransition (ProcTy.par τ₁ ProcTy.skip) AbstractTransLabel.ε τ₁
  | par_message (τ₁ τ₂ τ'₁ τ'₂ : ProcTy) (msg : MessageId) (d₁ d₂ : MessageDir) :
    MessageDir.dual d₁ d₂ →
    ProcTyTransition τ₁ (AbstractTransLabel.message msg d₁) τ'₁ →
    ProcTyTransition τ₂ (AbstractTransLabel.message msg d₂) τ'₂ →
    ProcTyTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac $ Action.fullMessage msg) (ProcTy.par τ'₁ τ'₂)
  | seq_step (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyTransition τ₁ lbl τ₁' →
    ProcTyTransition (ProcTy.seq τ₁ τ₂) lbl (ProcTy.seq τ₁' τ₂)
  | seq_done (τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.seq ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | choice_left (τ₁ τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.choice τ₁ τ₂) AbstractTransLabel.ε τ₁
  | choice_right (τ₁ τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.choice τ₁ τ₂) AbstractTransLabel.ε τ₂
  | choice_fair_left (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.ac $ Action.branchTrue bid) τ₁
  | choice_fair_right (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.ac $ Action.branchFalse bid) τ₂
  | recur_unfold (x : String) (τ : ProcTy) :
    ProcTyTransition (ProcTy.recur x τ) AbstractTransLabel.ε (τ.replaceVar x (ProcTy.recur x τ))
  | xoffer_else (ex_msg : Finset (MessageId × MessageDir)) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    (∀ m ty, (m, ty) ∈ branch_tys →
      (m.messageId, m.direction.invert) ∈ ex_msg) →
    ProcTyTransition (ProcTy.xoffer τ_else branch_tys) (AbstractTransLabel.ex ex_msg) τ_else
  | offer_else (ex_msg : Finset (MessageId × MessageDir)) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    (∀ m ty, (m, ty) ∈ branch_tys →
      (m.messageId, m.direction.invert) ∈ ex_msg) →
    ProcTyTransition (ProcTy.offer τ_else branch_tys) (AbstractTransLabel.ex ex_msg) τ_else
  | xoffer_branch (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy))
      (me : MessageExch) (ty : ProcTy) :
    (me, ty) ∈ branch_tys →
    ProcTyTransition (ProcTy.xoffer τ_else branch_tys)
      (AbstractTransLabel.message me.messageId me.direction) ty
  | offer_branch (τ_else : ProcTy)
                        (branch_tys : List (MessageExch × ProcTy))
                        (idx : ℕ)
                        (branch_tys' : List ProcTy)
      (me : MessageExch) (ty ty' : ProcTy) :
    branch_tys' = branch_tys.map branch_to_xoffer_ty →
    ty' = List.foldl (fun acc e => ProcTy.par acc e) ProcTy.skip (ty::branch_tys') →
    idx < branch_tys.length + 1 →
    ProcTyTransition (ProcTy.offer τ_else $ branch_tys.insertIdx ↑idx (me, ty))
      (AbstractTransLabel.message me.messageId me.direction) ty'

@[aesop unsafe]
inductive ProcTyCompElim : ProcTyComposition → ProcTyComposition → Prop where
  | refl (τs : ProcTyComposition) :
    ProcTyCompElim τs τs
  | eps_elim (τs τs' τs'' : ProcTyComposition) :
    ProcTyTransition τs AbstractTransLabel.ε τs' →
    ProcTyCompElim τs' τs'' →
    ProcTyCompElim τs τs''
inductive ProcTyCompElimStep : ℕ → ProcTyComposition → ProcTyComposition → Prop where
  | zero (τs : ProcTyComposition) :
    ProcTyCompElimStep 0 τs τs
  | succ (n : ℕ) (τs τs' τs'' : ProcTyComposition) :
    ProcTyTransition τs AbstractTransLabel.ε τs' →
    ProcTyCompElimStep n τs' τs'' →
    ProcTyCompElimStep (n + 1) τs τs''

@[reducible]
def ProcTyIncompTransition (τ₁ : ProcTy) (lbl : AbstractTransLabel) (τ₂ : ProcTy) :=
  ∃ τ₁', ProcTyTransition τ₁' lbl τ₂ ∧
               ProcTyCompElim τ₁ τ₁'

@[reducible]
def ProcTyCompTransition (τ₁ : ProcTy) (α : Action) (τ₂ : ProcTy) :=
  ProcTyIncompTransition τ₁ (AbstractTransLabel.ac α) τ₂
