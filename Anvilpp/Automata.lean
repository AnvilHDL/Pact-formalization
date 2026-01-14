import Anvilpp.Base
import Anvilpp.Types

/-- Abstract versions of transition labels for automata. -/
inductive AbstractTransLabel : Type where
  | ε : AbstractTransLabel
  | tock : AbstractTransLabel
  | message : MessageId → AbstractTransLabel
  | branchTrue : BranchId → AbstractTransLabel
  | branchFalse : BranchId → AbstractTransLabel
  | dollar : ProcId → AbstractTransLabel

-- structure ProcAutomaton (S : Type) where
--   states : Finset S
--   transitions : Finset (S × AbstractTransLabel × S)
--   initial : S
--   exit : S

-- inductive ProcAutomatonTranslation (S : Type) : Proc → ProcAutomaton S → Prop where

inductive ProcTyTransition : ProcTy → AbstractTransLabel → ProcTy → Prop where
  | message_send (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition (ProcTy.message $ MessageExch.send msg) (AbstractTransLabel.message msg) τ
  | message_recv (msg : MessageId) (τ : ProcTy) :
    ProcTyTransition (ProcTy.message $ MessageExch.recv msg) (AbstractTransLabel.message msg) τ
  | par_left (τ₁ τ₁' τ₂ : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ProcTyTransition τ₁ lbl τ₁' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂)
  | par_right (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.tock →
    ProcTyTransition τ₂ lbl τ₂' →
    ProcTyTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁ τ₂')
  | par_tock (τ₁ τ₂ : ProcTy) :
    ProcTyTransition τ₁ AbstractTransLabel.tock τ₁ →
    ProcTyTransition τ₂ AbstractTransLabel.tock τ₂ →
    ProcTyTransition (ProcTy.par τ₁ τ₂) AbstractTransLabel.tock (ProcTy.par τ₁ τ₂)
  | par_skip_left (τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.par ProcTy.skip τ₂) AbstractTransLabel.ε τ₂
  | par_skip_right (τ₁ : ProcTy) :
    ProcTyTransition (ProcTy.par τ₁ ProcTy.skip) AbstractTransLabel.ε τ₁
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
    ProcTyTransition (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.branchTrue bid) τ₁
  | choice_fair_right (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    ProcTyTransition (ProcTy.choice_fair bid τ₁ τ₂) (AbstractTransLabel.branchFalse bid) τ₂
  | recur_unfold (x : String) (τ : ProcTy) :
    ProcTyTransition (ProcTy.recur x τ) AbstractTransLabel.ε (τ.replaceVar x (ProcTy.recur x τ))
