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

lemma type_emulates_proc_ε : ∀ (p p' : Semantics.ProcComp)
                             (τ : ProcTyComposition),
    CompositionTyJudgement p τ →
    Semantics.Reduces p TransLabel.ε p' →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyCompElim τ τ' := by

    intro p p' τ H_typing H_reduces
    revert H_reduces p'
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> intro p' H_reduces
    case par =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case par_left H_reduces =>
        rename_i p₁' H_noninstant H_noneps
        have H_ind₁ := H_ind₁ H_ctx p₁' H_reduces
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.par τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . apply ProcTyCompElim.elim_par
          . exact H_ind₁.2
          . apply ProcTyCompElim.refl
      case par_right H_reduces =>
        rename_i p₂' H_noninstant H_noneps
        have H_ind₂ := H_ind₂ H_ctx p₂' H_reduces
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁ τ₂')
        constructor
        . apply ProcTyJudgement.par
          . rewrite [H_ctx]
            exact H_typing₁
          . exact H_ind₂.1
        . apply ProcTyCompElim.elim_par
          . apply ProcTyCompElim.refl
          . exact H_ind₂.2
      case par_skip_left =>
        exists τ₂
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₂
        . apply ProcTyCompElim.elim_right (τ₂ := ProcTy.skip.par τ₂)
          . have H_τ₁ : ProcTyCompElim τ₁ ProcTy.skip := by
              apply ProcTyIncompTransition.skip_typing_implies_skip_elim
              rewrite [H_ctx]
              exact H_typing₁
            apply ProcTyCompElim.elim_par
            . exact H_τ₁
            . apply ProcTyCompElim.refl
          . apply ProcTyTransition.par_skip_left
      case par_skip_right =>
        exists τ₁
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₁
        . apply ProcTyCompElim.elim_right (τ₂ := τ₁.par ProcTy.skip)
          . have H_τ₂ : ProcTyCompElim τ₂ ProcTy.skip := by
              apply ProcTyIncompTransition.skip_typing_implies_skip_elim
              rewrite [H_ctx]
              exact H_typing₂
            apply ProcTyCompElim.elim_par
            . apply ProcTyCompElim.refl
            . exact H_τ₂
          . apply ProcTyTransition.par_skip_right
    case recur =>
      rename_i ctx' pid body τ_body H_typing_body H_ind
      cases H_reduces
      sorry
    case seq =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case seq_step p₁' H_red =>
        have H_ind₁ := H_ind₁ H_ctx p₁' H_red
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.seq τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.seq
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . apply ProcTyCompElim.elim_seq_step
          exact H_ind₁.2
      case seq_skip =>
        exists τ₂
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₂
        . apply ProcTyCompElim.elim_seq_skip (τ₂' := τ₂)
          . have H_τ₁ : ProcTyCompElim τ₁ ProcTy.skip := by
              apply ProcTyIncompTransition.skip_typing_implies_skip_elim
              rewrite [H_ctx]
              exact H_typing₁
            exact H_τ₁
          . apply ProcTyCompElim.refl
    case var =>
      rename_i ctx' x H_x
      cases H_reduces
    case subtype =>
      rename_i ctx' p'' τ₁ τ₂ H_typing H_subtype H_ind
      revert H_ctx
      sorry
    all_goals sorry


lemma type_emulates_proc_multi_ε : ∀ (p p' : Semantics.ProcComp) (τ : ProcTy),
    CompositionTyJudgement p τ →
    Semantics.CompElim p p' →
    ∃ τ', CompositionTyJudgement p' τ' ∧ ProcTyCompElim τ τ' := by

  intro p p' τ H_typing H_elim
  revert τ
  induction H_elim <;> intro τ H_typing
  case refl p₁ =>
    exists τ
    constructor
    . exact H_typing
    . apply ProcTyCompElim.refl
  case eps_elim p₁ p₁' p₁'' H_red H_elim H_ind =>
    have H_τ' : ∃ τ', CompositionTyJudgement p₁' τ' ∧ ProcTyCompElim τ τ' := by
      apply type_emulates_proc_ε (p := p₁) (p' := p₁')
      . exact H_typing
      . exact H_red
    have ⟨τ', H_τ'⟩ := H_τ'
    have ⟨τ'', H_τ''⟩ := H_ind τ' H_τ'.1
    exists τ''
    constructor
    . exact H_τ''.1
    . apply ProcTyCompElim.elim_transitivity (τ₂ := τ')
      . exact H_τ'.2
      . exact H_τ''.2

lemma label_abstraction_preserves_ex : ∀ {lbl : TransLabel},
    (AbstractTransLabel.fromConcrete lbl).isEx ↔ lbl.isEx := by
  intro lbl
  unfold AbstractTransLabel.isEx
  unfold AbstractTransLabel.fromConcrete
  unfold TransLabel.isEx
  simp
  cases lbl <;> simp

lemma type_emulates_proc_label : ∀ (p p' : Semantics.ProcComp)
                                (τ : ProcTyComposition) (lbl : TransLabel),
    CompositionTyJudgement p τ →
    Semantics.Reduces p lbl p' →
    lbl ≠ TransLabel.ε →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyIncompTransition τ (AbstractTransLabel.fromConcrete lbl) τ' := by

    intro p p' τ lbl H_typing H_reduces H_not_ε
    revert H_reduces p' lbl
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> intro p' lbl H_reduces H_not_ε
    case seq =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case seq_step p₁' H_red =>
        have H_ind₁ := H_ind₁ H_ctx p₁' lbl H_red H_not_ε
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.seq τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.seq
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . apply ProcTyIncompTransition.reduces_seq
          exact H_ind₁.2
      case seq_skip =>
        simp at H_not_ε
    case par =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case par_tock =>
        rename_i p₁' p₂' H_red₁ H_red₂
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.ac Action.tock) H_red₁ (by simp)
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.ac Action.tock) H_red₂ (by simp)
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . exact H_ind₂.1
        . apply ProcTyIncompTransition.reduces_par_tock
          . exact H_ind₁.2
          . exact H_ind₂.2
      case par_left p₁' H_lbl H_nonex H_red =>
        have H_ind₁ := H_ind₁ H_ctx p₁' lbl H_red H_not_ε
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.par τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . apply ProcTyIncompTransition.reduces_par_left
          . rewrite [label_abstraction_preserves_ex (lbl := lbl)]
            exact H_nonex
          . exact H_ind₁.2
          . apply ProcTyCompElim.refl
      case par_right p₂' H_lbl H_nonex H_red =>
        sorry -- completely symmetrical
      case par_left_ex ex_msg p₁' H_red H_m =>
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.ex ex_msg) H_red H_not_ε
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.par τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . sorry -- FIXME: prove separately
      case par_right_ex ex_msg p₂' H_m H_red =>
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.ex ex_msg) H_red H_not_ε
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁ τ₂')
        constructor
        . apply ProcTyJudgement.par
          . rewrite [H_ctx]
            exact H_typing₁
          . exact H_ind₂.1
        . sorry -- FIXME: prove separately
      case par_skip_left =>
        simp at H_not_ε
      case par_skip_right =>
        simp at H_not_ε
      case par_message msg dir dir' b p₁' p₂' H_dual H_red₁ H_red₂ =>
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.message msg dir b) H_red₁ (by simp)
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.message msg dir' b) H_red₂ (by simp)
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . exact H_ind₂.1
        . sorry -- FIXME: prove separately
    case recur ctx' x p_body τ_body H_body_typing H_ind =>
      cases H_reduces
      simp at H_not_ε
    case var ctx' x H_x =>
      cases H_reduces
    case subtype ctx' p₀ τ₁ τ₂ H_typing₁ H_sub H_ind =>
      have H_ind₁ := H_ind H_ctx p' lbl H_reduces H_not_ε
      have ⟨τ₁', H_ind₁⟩ := H_ind₁
      sorry -- FIXME: prove separately

    all_goals sorry

lemma process_refines_type_incomp : ∀ (p p' : Proc) (τ : ProcTy) (lbl : TransLabel),
    CompositionTyJudgement p τ →
    lbl ≠ TransLabel.ε →
    Semantics.IncompReduces p lbl p' →
    ∃ τ', CompositionTyJudgement p' τ'
      ∧ ProcTyIncompTransition τ (AbstractTransLabel.fromConcrete lbl) τ' := by

  intro p p' τ lbl H_typing H_not_ε H_reduces
  unfold Semantics.IncompReduces at H_reduces
  have ⟨p₁, H_reduces⟩ := H_reduces
  have H_mid_τ : ∃ τ₁, CompositionTyJudgement p₁ τ₁ ∧ ProcTyCompElim τ τ₁ := by
    apply type_emulates_proc_multi_ε (p := p) (p' := p₁)
    . exact H_typing
    . exact H_reduces.2
  have ⟨τ', H_τ'⟩ := H_mid_τ
  have H_end_τ : ∃ τ'', CompositionTyJudgement p' τ''
    ∧ ProcTyIncompTransition τ' (AbstractTransLabel.fromConcrete lbl) τ'' := by
    apply type_emulates_proc_label (p := p₁) (p' := p')
    . exact H_τ'.1
    . exact H_reduces.1
    . exact H_not_ε
  have ⟨τ'', H_τ''⟩ := H_end_τ
  exists τ''
  constructor
  . exact H_τ''.1
  . apply ProcTyIncompTransition.reduces_extend_l (τ₁ := τ')
    . exact H_τ''.2
    . exact H_τ'.2

-- TODO: may need to consider the ex labels
theorem process_refines_type : ∀ (p p' : Proc) (τ : ProcTy) (α : Action),
    CompositionTyJudgement p τ →
    Semantics.CompReduces p α p' →
    ∃ τ', CompositionTyJudgement p' τ'
      ∧ ProcTyCompTransition τ α τ' := by

  intro p p' τ α H_typing H_reduces
  unfold ProcTyCompTransition
  have H_lbl : AbstractTransLabel.ac α = AbstractTransLabel.fromConcrete (TransLabel.ac α) := by
    simp
  rewrite [H_lbl]
  apply process_refines_type_incomp (p := p) (p' := p') <;> try trivial
  simp

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
      sorry -- symmetrical
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
    case par_right_ex ex_msg τ₂' H_trans H_m =>
      sorry -- symmetrical
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
    sorry
  all_goals sorry
