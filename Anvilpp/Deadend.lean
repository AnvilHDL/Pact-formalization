import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Zip
import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers


lemma type_preserves_deadends_single : ∀ (p : Proc) (τ τ' : ProcTy) (lbl : AbstractTransLabel),
    CompositionTyJudgement p τ →
    lbl ≠ AbstractTransLabel.ε →
    ProcTyTransition τ lbl τ' →
    ∃ p' lbl',
      lbl = AbstractTransLabel.fromConcrete lbl' ∧
        Semantics.IncompReduces p lbl' p' := by

  intro p τ τ' lbl H_typing H_not_ε H_transition
  revert τ' lbl
  unfold CompositionTyJudgement at H_typing
  generalize H_ctx : ProcTyContext.empty = ctx at H_typing
  induction H_typing <;>  intro τ' lbl H_not_ε H_trans
  case cycle ctx' =>
    cases H_trans
    exists Proc.skip, TransLabel.ac Action.tock
    constructor
    . simp
    . unfold Semantics.IncompReduces
      exists Proc.cycle
      constructor
      . apply Semantics.Reduces.tock
      . apply Semantics.CompElim.refl
  case par ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_trans
    case par_left τ₁' H_not_tock H_not_ex H_trans₁ =>
      have H_p₁' := H_ind₁ H_ctx τ₁' lbl H_not_ε H_trans₁
      have ⟨p₁', lbl', H_lbl', H_reduces⟩ := H_p₁'
      exists (Proc.par p₁' p₂), lbl'
      constructor
      . exact H_lbl'
      . apply Semantics.IncompReduces.par_non_ex_left
        . have H_lbl_nonex : lbl.isEx ↔ lbl'.isEx := by
            rewrite [H_lbl']
            apply label_abstraction_preserves_ex
          rewrite [← H_lbl_nonex]
          exact H_not_ex
        . exact H_reduces
    case par_right τ₂' H_not_tock H_not_ex H_trans₂ =>
      have H_p₂' := H_ind₂ H_ctx τ₂' lbl H_not_ε H_trans₂
      have ⟨p₂', lbl', H_lbl', H_reduces⟩ := H_p₂'
      exists (Proc.par p₁ p₂'), lbl'
      constructor
      . exact H_lbl'
      . apply Semantics.IncompReduces.par_non_ex_right
        . have H_lbl_nonex : lbl.isEx ↔ lbl'.isEx := by
            rewrite [H_lbl']
            apply label_abstraction_preserves_ex
          rewrite [← H_lbl_nonex]
          exact H_not_ex
        . exact H_reduces
    case par_left_ex ex_msg τ₁' H_trans H_m =>
      have H_p₁' := H_ind₁ H_ctx τ₁' (AbstractTransLabel.ex ex_msg) H_not_ε H_trans
      have ⟨p₁', lbl', H_lbl', H_reduces⟩ := H_p₁'
      exists (Proc.par p₁' p₂), lbl'
      constructor
      . exact H_lbl'
      . have H_m' : ∀ mx ∈ ex_msg, Semantics.NonInstantMessage ∅ ∅ p₂ mx := by
          intro mx H_mx
          apply non_instant_msg_preservation (p := p₂) (τ := τ₂)
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₂
          . exact H_m mx H_mx
        unfold AbstractTransLabel.fromConcrete at H_lbl'
        have H_lbl_ex' : lbl' = TransLabel.ex ex_msg := by
          cases lbl' <;> (simp at H_lbl'; try contradiction)
          rename_i ex_msg'
          rewrite [H_lbl']
          rfl
        rewrite [H_lbl_ex']
        apply Semantics.IncompReduces.par_ex_left
        . rewrite [← H_lbl_ex']
          exact H_reduces
        . exact H_m'
    case par_right_ex ex_msg τ₂' H_m H_trans =>
      have H_p₂' := H_ind₂ H_ctx τ₂' (AbstractTransLabel.ex ex_msg) H_not_ε H_trans
      have ⟨p₂', lbl', H_lbl', H_reduces⟩ := H_p₂'
      exists (Proc.par p₁ p₂'), lbl'
      constructor
      . exact H_lbl'
      . have H_m' : ∀ mx ∈ ex_msg, Semantics.NonInstantMessage ∅ ∅ p₁ mx := by
          intro mx H_mx
          apply non_instant_msg_preservation (p := p₁) (τ := τ₁)
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₁
          . exact H_m mx H_mx
        unfold AbstractTransLabel.fromConcrete at H_lbl'
        have H_lbl_ex' : lbl' = TransLabel.ex ex_msg := by
          cases lbl' <;> (simp at H_lbl'; try contradiction)
          rename_i ex_msg'
          rewrite [H_lbl']
          rfl
        rewrite [H_lbl_ex']
        apply Semantics.IncompReduces.par_ex_right
        . rewrite [← H_lbl_ex']
          exact H_reduces
        . exact H_m'
    case par_skip_left =>
      simp at H_not_ε
    case par_skip_right =>
      simp at H_not_ε
    case par_tock τ₁' τ₂' H_trans₁ H_trans₂ =>
      have H_p₁' := H_ind₁ H_ctx τ₁' (AbstractTransLabel.ac Action.tock) H_not_ε H_trans₁
      have ⟨p₁', lbl₁', H_lbl₁', H_reduces₁⟩ := H_p₁'
      have H_p₂' := H_ind₂ H_ctx τ₂' (AbstractTransLabel.ac Action.tock) H_not_ε H_trans₂
      have ⟨p₂', lbl₂', H_lbl₂', H_reduces₂⟩ := H_p₂'
      exists (Proc.par p₁' p₂'), (TransLabel.ac Action.tock)
      constructor
      . simp
      . apply Semantics.IncompReduces.par_tock
        . have H_lbl₁_tock : lbl₁' = TransLabel.ac Action.tock := by
            cases lbl₁' <;> (simp at H_lbl₁'; try contradiction)
            rewrite [H_lbl₁']
            rfl
          rewrite [← H_lbl₁_tock]
          exact H_reduces₁
        . have H_lbl₂_tock : lbl₂' = TransLabel.ac Action.tock := by
            cases lbl₂' <;> (simp at H_lbl₂'; try contradiction)
            rewrite [H_lbl₂']
            rfl
          rewrite [← H_lbl₂_tock]
          exact H_reduces₂
    case par_message τ₁' τ₂' msg d₁ d₂ H_dual H_trans₁ H_trans₂ =>
      have H_p₁' := H_ind₁ H_ctx τ₁' (AbstractTransLabel.message msg d₁) (by simp) H_trans₁
      have ⟨p₁', lbl₁', H_lbl₁', H_reduces₁⟩ := H_p₁'
      have H_p₂' := H_ind₂ H_ctx τ₂' (AbstractTransLabel.message msg d₂) (by simp) H_trans₂
      have ⟨p₂', lbl₂', H_lbl₂', H_reduces₂⟩ := H_p₂'
      exists (Proc.par p₁' p₂'), (TransLabel.ac $ Action.fullMessage msg)
      constructor
      . simp
      . have H_lbl₁_msg : ∃ v₁, lbl₁' = TransLabel.message msg d₁ v₁ := by
          cases lbl₁' <;> (simp at H_lbl₁'; try contradiction)
          rename_i v₁
          exists v₁
          rewrite [H_lbl₁'.1]
          rewrite [H_lbl₁'.2]
          rfl
        have H_lbl₂_msg : ∃ v₂, lbl₂' = TransLabel.message msg d₂ v₂ := by
          cases lbl₂' <;> (simp at H_lbl₂'; try contradiction)
          rename_i v₂
          exists v₂
          rewrite [H_lbl₂'.1]
          rewrite [H_lbl₂'.2]
          rfl
        have ⟨v₁, H_lbl₁_msg⟩ := H_lbl₁_msg
        have ⟨v₂, H_lbl₂_msg⟩ := H_lbl₂_msg
        apply Semantics.IncompReduces.par_message (v₁ := v₁) (v₂ := v₂) (d₁ := d₁) (d₂ := d₂)
        . exact H_dual
        . rewrite [← H_lbl₁_msg]
          exact H_reduces₁
        . rewrite [← H_lbl₂_msg]
          exact H_reduces₂
  case var ctx' x H_x =>
    cases H_trans
  case skip ctx' =>
    cases H_trans
  case recur =>
    cases H_trans
    simp at H_not_ε
  case subtype ctx' p' τ₁ τ₂ H_typing H_sub H_ind =>
    clear p τ ctx
    have H_τ₁'' := sub_preserves_behaviour τ₁ τ₂ τ' lbl H_sub H_trans
    have ⟨τ₁'', H_τ₁''⟩ := H_τ₁''
    exact H_ind H_ctx τ₁'' lbl H_not_ε H_τ₁''.1
  all_goals sorry -- FIXME: complete

-- If the type can transition through ε in any way at all, at least one of
-- them can be matched by the process.
lemma type_keeps_elim : ∀ (p : Proc) (τ τ' : ProcTy),
    CompositionTyJudgement p τ →
    ProcTyTransition τ AbstractTransLabel.ε τ' →
    ∃ τ'' p'', ProcTyTransition τ AbstractTransLabel.ε τ'' ∧
       Semantics.CompElim p p'' ∧ CompositionTyJudgement p'' τ'' := by

    intro p τ τ' H_typing H_transition
    revert τ'
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> intro τ' H_transition
    case cycle ctx' =>
      cases H_transition
    case par ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      cases H_transition
      case par_left τ₁' H_not_ε H_non_ex H_trans =>
        have H_p₁' := H_ind₁ H_ctx τ₁' H_trans
        have ⟨τ₁'', p₁'', H_trans₁, H_elim₁, H_typing₁'⟩ := H_p₁'
        exists (ProcTy.par τ₁'' τ₂), (Proc.par p₁'' p₂)
        constructor
        . apply ProcTyTransition.par_left
          . exact H_not_ε
          . exact H_non_ex
          . exact H_trans₁
        . constructor
          . sorry -- trivial
          . apply ProcTyJudgement.par
            . exact H_typing₁'
            . rewrite [H_ctx]
              exact H_typing₂
      case par_right τ₂' H_not_ε H_non_ex H_trans =>
        sorry -- symmetrical
      case par_skip_left =>
        exists τ₂, p₂
        constructor
        . apply ProcTyTransition.par_skip_left
        . constructor
          . sorry -- trivial
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₂
      case par_skip_right =>
        sorry -- symmetrical
    case choice ctx' e p₁ p₂ τ₁ τ₂ H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      have H_eval : ∃ v, e ↓ v := by
        apply welltyped_expr_evaluates_to_something
        rewrite [← H_ctx] at H_e_typing
        unfold ProcTyContext.empty at H_e_typing
        simp at H_e_typing
        exact H_e_typing
      have ⟨v, H_eval⟩ := H_eval
      cases v
      case true =>
        exists τ₁, p₁
        constructor
        . apply ProcTyTransition.choice_left
        . constructor
          . apply Semantics.CompElim.eps_elim (p' := p₁)
            . apply Semantics.Reduces.ifunfair_true <;> trivial
            . apply Semantics.CompElim.refl
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₁
      case false =>
        exists τ₂, p₂
        constructor
        . apply ProcTyTransition.choice_right
        . constructor
          . apply Semantics.CompElim.eps_elim (p' := p₂)
            . apply Semantics.Reduces.ifunfair_false <;> trivial
            . apply Semantics.CompElim.refl
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₂
    case subtype ctx' p' τ₁ τ₂ H_typing H_sub H_ind =>
      sorry -- FIXME: prove it
    all_goals sorry

lemma type_preserves_deadend_elim : ∀ (P : ProcTy → Prop) (p : Proc) (τ : ProcTy),
    CompositionTyJudgement p τ →
    (∃ n, ∀ τ', ¬ ProcTyCompElimStep n τ τ') →
    (∀ τ', ProcTyCompElim τ τ' → (∃ τ'', ProcTyCompElim τ' τ'' ∧ P τ'')) →
    (∃ p' τ', CompositionTyJudgement p' τ' ∧ ProcTyCompElim τ τ' ∧ Semantics.CompElim p p' ∧ P τ') := by
    -- (∃ τ', ProcTyCompElim τ τ' ∧ (∀ α τ'', ProcTyCompTransition τ' α τ'' → ∃ p'', Semantics.CompReduces p α p'')) := by

    sorry -- FIXME: prove it (low priority)

theorem type_preserves_deadends : ∀ (p : Proc) (τ : ProcTy),
    CompositionTyJudgement p τ →
    (¬ ∃ p' α, Semantics.CompReduces p α p') →
    (
      (∀ n, ∃ τ', ProcTyCompElimStep n τ τ') ∨
      (∃ τ', ProcTyCompElim τ τ' ∧ (¬ ∃ τ'' α, ProcTyCompTransition τ' α τ''))
    )
     := by
  intro p τ H_typing H_deadend
  by_contra H_contra
  push_neg at H_contra
  have H_contra_final :  ∃ p' τ',
    CompositionTyJudgement p' τ' ∧
      ProcTyCompElim τ τ' ∧ Semantics.CompElim p p' ∧ ∃ τ'' α, ProcTyTransition τ' (AbstractTransLabel.ac α) τ'' := by
    have ⟨H_contra₁, H_contra₂⟩ := H_contra
    apply type_preserves_deadend_elim
    . exact H_typing
    . exact H_contra₁
    . intro τ' H_contra'
      have H := H_contra₂ τ' H_contra'
      unfold ProcTyCompTransition ProcTyIncompTransition at H
      have ⟨τ'', α, τₘ, H_τ''⟩ := H
      exists τₘ
      constructor
      . exact H_τ''.2
      . exists τ'', α
        exact H_τ''.1
  have ⟨p', τ', H_prop, H_elim, H_comp_elim, τ'', α, H_trans⟩ := H_contra_final
  have H_p'' := type_preserves_deadends_single p' τ' τ'' (AbstractTransLabel.ac α) H_prop (by simp) H_trans
  have ⟨p'', lbl', H_lbl', H_reduces⟩ := H_p''
  cases lbl' <;> simp at H_lbl'; try contradiction
  rewrite [← H_lbl'] at H_reduces
  have H_contra' : ∃ p' α, Semantics.CompReduces p α p' := by
    exists p'', α
    unfold Semantics.CompReduces
    apply Semantics.IncompReduces.extend_l (p₁' := p')
    . exact H_comp_elim
    . exact H_reduces
  contradiction
