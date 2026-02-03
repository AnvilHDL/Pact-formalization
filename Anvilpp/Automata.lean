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

inductive ProcTyTransition : Finset (MessageId × MessageDir) → ProcTy → AbstractTransLabel → ProcTy → Prop where
  | tock ex_msg :
    ProcTyTransition ex_msg ProcTy.cycle (AbstractTransLabel.ac Action.tock) ProcTy.skip
  | message_send ex_msg (msg : MessageId) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.send msg) (AbstractTransLabel.message msg MessageDir.send) ProcTy.skip
  | message_recv ex_msg (msg : MessageId) :
    ProcTyTransition ex_msg (ProcTy.message $ MessageExch.recv msg) (AbstractTransLabel.message msg MessageDir.recv) ProcTy.skip
  | par_left ex_msg ex_msg' (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ac Action.tock →
    ex_msg' ⊆ ex_msg →
    (∀ mx ∈ ex_msg', ProcTyNonInstantMsg ∅ ∅ τ₂ mx) →
    ProcTyTransition ex_msg' τ₁ lbl τ₁' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂)
  | par_right ex_msg ex_msg' (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ac Action.tock →
    ex_msg' ⊆ ex_msg →
    (∀ mx ∈ ex_msg', ProcTyNonInstantMsg ∅ ∅ τ₁ mx) →
    ProcTyTransition ex_msg' τ₂ lbl τ₂' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁ τ₂')
  | par_tock ex_msg (τ₁ τ₂ τ₁' τ₂' : ProcTy) :
    ProcTyTransition ex_msg τ₁ (AbstractTransLabel.ac Action.tock) τ₁' →
    ProcTyTransition ex_msg τ₂ (AbstractTransLabel.ac Action.tock) τ₂' →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac Action.tock) (ProcTy.par τ₁' τ₂')
  | par_skip_left ex_msg (τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.par ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | par_skip_right ex_msg (τ₁ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.par τ₁ ProcTy.skip) AbstractTransLabel.ε τ₁
  | par_message ex_msg ex_msg₁ ex_msg₂ (τ₁ τ₂ τ'₁ τ'₂ : ProcTy) (msg : MessageId) (d₁ d₂ : MessageDir) :
    -- TODO: this can be simplified
    MessageDir.dual d₁ d₂ →
    ex_msg₁ ⊆ ex_msg →
    ex_msg₂ ⊆ ex_msg →
    (∀ mx ∈ ex_msg₂, ProcTyNonInstantMsg ∅ ∅ τ₁ mx) →
    (∀ mx ∈ ex_msg₁, ProcTyNonInstantMsg ∅ ∅ τ₂ mx) →
    ProcTyTransition ex_msg₁ τ₁ (AbstractTransLabel.message msg d₁) τ'₁ →
    ProcTyTransition ex_msg₂ τ₂ (AbstractTransLabel.message msg d₂) τ'₂ →
    ProcTyTransition ex_msg (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac $ Action.fullMessage msg) (ProcTy.par τ'₁ τ'₂)
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
    ProcTyTransition ex_msg (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.ac $ Action.branchTrue bid) τ₁
  | choice_fair_right ex_msg (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.ac $ Action.branchFalse bid) τ₂
  | recur_unfold ex_msg (x : String) (τ : ProcTy) :
    ProcTyTransition ex_msg (ProcTy.recur x τ) AbstractTransLabel.ε (τ.replaceVar x (ProcTy.recur x τ))
  | xoffer_else ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    (∀ m ty, (m, ty) ∈ branch_tys →
      (m.messageId, m.direction.invert) ∈ ex_msg) →
    ProcTyTransition ex_msg (ProcTy.xoffer τ_else branch_tys) AbstractTransLabel.ε τ_else
  | offer_else ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    (∀ m ty, (m, ty) ∈ branch_tys →
      (m.messageId, m.direction.invert) ∈ ex_msg) →
    ProcTyTransition ex_msg (ProcTy.offer τ_else branch_tys) AbstractTransLabel.ε τ_else
  | xoffer_branch ex_msg (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy))
      (me : MessageExch) (ty : ProcTy) :
    (me, ty) ∈ branch_tys →
    ProcTyTransition ex_msg (ProcTy.xoffer τ_else branch_tys)
      (AbstractTransLabel.message me.messageId me.direction) ty
  | offer_branch ex_msg (τ_else : ProcTy)
                        (branch_tys : List (MessageExch × ProcTy))
                        (idx : ℕ)
                        (branch_tys' : List ProcTy)
      (me : MessageExch) (ty ty' : ProcTy) :
    branch_tys' = branch_tys.map branch_to_xoffer_ty →
    ty' = List.foldl (fun acc e => ProcTy.par acc e) ProcTy.skip (ty::branch_tys') →
    idx < branch_tys.length + 1 →
    ProcTyTransition ex_msg (ProcTy.offer τ_else $ branch_tys.insertIdx ↑idx (me, ty))
      (AbstractTransLabel.message me.messageId me.direction) ty'
  | eps_elim₁ ex_msg (τ τ' τ'' : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyTransition ex_msg τ AbstractTransLabel.ε τ' →
    ProcTyTransition ex_msg τ' lbl τ'' →
    ProcTyTransition ex_msg τ lbl τ''
  | eps_elim₂ ex_msg (τ τ' τ'' : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyTransition ex_msg τ lbl τ' →
    ProcTyTransition ex_msg τ' AbstractTransLabel.ε τ'' →
    ProcTyTransition ex_msg τ lbl τ''

def ProcTyCompTransition (τ₁ : ProcTyComposition) (α : Action) (τ₂ : ProcTyComposition) : Prop :=
  ∃ ex_msg : Finset (MessageId × MessageDir),
    ProcTyTransition ex_msg τ₁ (AbstractTransLabel.ac α) τ₂

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
  | step (τs₁ τs₂ τs₃ : ProcTyComposition) (α : Action) :
    ProcTyCompTransition τs₁ α τs₂ →
    ProcTyCompReachable τs₂ τs₃ →
    ProcTyCompReachable τs₁ τs₃

lemma procty_trans_preserved_under_extended_exmsg :
      ∀ (ex_msg ex_msg' : Finset (MessageId × MessageDir)) (τ₁ τ₂ : ProcTy) (lbl : AbstractTransLabel),
        ex_msg ⊆ ex_msg' →
        ProcTyTransition ex_msg τ₁ lbl τ₂ →
        ProcTyTransition ex_msg' τ₁ lbl τ₂ := by
  intro ex_msg ex_msg' τ₁ τ₂ lbl H_subset H_transition
  revert H_subset
  induction H_transition
  case tock =>
    intro H_subset
    apply ProcTyTransition.tock
  case message_send ex_msg msg =>
    intro H_subset
    apply ProcTyTransition.message_send
  case message_recv ex_msg msg =>
    intro H_subset
    apply ProcTyTransition.message_recv
  case par_left ex_msg ex_msg' τ₁ τ₁' τ₂ lbl H_neq H_subset H_non_instant H_transition IH =>
    intro H_subset_total
    apply ProcTyTransition.par_left
    . exact H_neq
    . sorry
    all_goals sorry
  all_goals sorry
