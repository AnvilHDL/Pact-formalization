import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

inductive ProcTyNonInstant : Finset String → ProcTy → Prop where
  | cycle (Γ : Finset String) :
    ProcTyNonInstant Γ ProcTy.cycle
  | choice (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.choice_fair bid τ₁ τ₂)
  | seq_left (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ (ProcTy.seq τ₁ τ₂)
  | seq_right (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.seq τ₁ τ₂)
  | par_left (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ (ProcTy.par τ₁ τ₂)
  | par_right (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.par τ₁ τ₂)
  | xoffer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    ProcTyNonInstant Γ τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant Γ ty) →
    ProcTyNonInstant Γ (ProcTy.xoffer τ_else branch_tys)
  | offer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    ProcTyNonInstant Γ τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant Γ ty) →
    ProcTyNonInstant Γ (ProcTy.offer τ_else branch_tys)
  | var (Γ : Finset String) (x : String) :
    x ∈ Γ →
    ProcTyNonInstant Γ (ProcTy.var x)
  | recur (Γ : Finset String) (x : String) (τ : ProcTy) :
    ProcTyNonInstant (Γ ∪ {x}) τ →
    ProcTyNonInstant Γ (ProcTy.recur x τ)

inductive ProcTyNonInstantMsg : Finset String → Finset String → ProcTy → (MessageId × MessageDir) → Prop where
  | cycle (Γₙ Γₘ : Finset String) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ ProcTy.cycle mx
  | choice (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.choice τ₁ τ₂) mx
  | choice_fair (bid : BranchId) (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.choice_fair bid τ₁ τ₂) mx
  | seq_left (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstant Γₙ τ₁ →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.seq τ₁ τ₂) mx
  | seq_right (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.seq τ₁ τ₂) mx
  | par (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.par τ₁ τ₂) mx
  | xoffer (Γₙ Γₘ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ_else mx →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg Γₙ Γₘ ty mx) →
    (∀ m ty, (m, ty) ∈ branch_tys → m.toPair ≠ mx) →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.xoffer τ_else branch_tys) mx
  | offer (Γₙ Γₘ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ_else mx →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg Γₙ Γₘ ty mx) →
    (∀ m ty, (m, ty) ∈ branch_tys → m.toPair ≠ mx) →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.offer τ_else branch_tys) mx
  | var (Γₙ Γₘ : Finset String) (x : String) (mx : MessageId × MessageDir) :
    x ∈ Γₘ →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.var x) mx
  | recur_instant (Γₙ Γₘ : Finset String) (x : String) (τ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstant Γₙ (ProcTy.recur x τ) →
    ProcTyNonInstantMsg (Γₙ ∪ {x}) (Γₘ ∪ {x}) τ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.recur x τ) mx
  | recur_noninstant (Γₙ Γₘ : Finset String) (x : String) (τ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg (Γₙ \ {x}) (Γₘ ∪ {x}) τ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.recur x τ) mx
  | skip (Γₙ Γₘ : Finset String) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ ProcTy.skip mx
  | send (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.send)
  | send_opposite (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.recv)
  | recv (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.recv)
  | recv_opposite (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.send)


def branch_to_xoffer_ty (br : MessageExch × ProcTy) : ProcTy := ProcTy.xoffer ProcTy.skip [br]

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
    -- TODO: this can be simplified
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

inductive ProcTyCompElim : ProcTyComposition → ProcTyComposition → Prop where
  | refl (τs : ProcTyComposition) :
    ProcTyCompElim τs τs
  | eps_elim (τs τs' τs'' : ProcTyComposition) :
    ProcTyTransition τs AbstractTransLabel.ε τs' →
    ProcTyCompElim τs' τs'' →
    ProcTyCompElim τs τs''

-- same as ProcTyCompElim but with a step count
inductive ProcTyCompElimStep : ℕ → ProcTyComposition → ProcTyComposition → Prop where
  | zero (τs : ProcTyComposition) :
    ProcTyCompElimStep 0 τs τs
  | succ (n : ℕ) (τs τs' τs'' : ProcTyComposition) :
    ProcTyTransition τs AbstractTransLabel.ε τs' →
    ProcTyCompElimStep n τs' τs'' →
    ProcTyCompElimStep (n + 1) τs τs''

lemma procty_comp_elim_step_iff :
      ∀ (τs τs' : ProcTyComposition),
        (∃ n, ProcTyCompElimStep n τs τs') ↔
        ProcTyCompElim τs τs' := by sorry -- trivial

@[reducible]
def ProcTyIncompTransition (τ₁ : ProcTy) (lbl : AbstractTransLabel) (τ₂ : ProcTy) :=
  ∃ τ₁', ProcTyTransition τ₁' lbl τ₂ ∧
               ProcTyCompElim τ₁ τ₁'

@[reducible]
def ProcTyCompTransition (τ₁ : ProcTy) (α : Action) (τ₂ : ProcTy) :=
  ProcTyIncompTransition τ₁ (AbstractTransLabel.ac α) τ₂
