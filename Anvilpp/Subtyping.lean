import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers

lemma par_symm_trans_congr : ∀ (τ₁ τ₂ τ : ProcTy) (lbl : AbstractTransLabel),
    ProcTyTransition (ProcTy.par τ₁ τ₂) lbl τ →
    ∃ τ', ProcTyTransition (ProcTy.par τ₂ τ₁) lbl τ' ∧ ProcTyCongr τ τ' := by

  intro τ₁ τ₂ τ lbl H_trans
  cases H_trans <;> try trivial
  case par_left τ₁' H_not_ε H_non_ex H_trans =>
    exists (ProcTy.par τ₂ τ₁')
    constructor
    . aesop
    . apply ProcTyCongr.par_comm
  case par_right τ₂' H_not_ε H_non_ex H_trans =>
    exists (ProcTy.par τ₂' τ₁)
    constructor
    . aesop
    . apply ProcTyCongr.par_comm
  case par_left_ex ex_msg τ₁' H_trans H_mx =>
    exists (ProcTy.par τ₂ τ₁')
    constructor
    . aesop
    . apply ProcTyCongr.par_comm
  case par_right_ex ex_msg τ₂' H_trans H_mx =>
    exists (ProcTy.par τ₂' τ₁)
    constructor
    . aesop
    . apply ProcTyCongr.par_comm
  case par_tock τ₁' τ₂' H_trans₁ H_trans₂ =>
    exists (ProcTy.par τ₂' τ₁')
    constructor
    . aesop
    . apply ProcTyCongr.par_comm
  case par_skip_left =>
    exists τ₂
    constructor
    . aesop
    . apply ProcTyCongr.refl
  case par_skip_right =>
    exists τ₁
    constructor
    . aesop
    . apply ProcTyCongr.refl
  case par_message τ₁'' τ₂'' msg' d₁ d₂ H_dir H_trans₁ H_trans₂ =>
    exists (ProcTy.par τ₂'' τ₁'')
    constructor
    . apply ProcTyTransition.par_message (d₁ := d₂) (d₂ := d₁)
      . rewrite [MessageDir.dual_symm]
        exact H_dir
      . exact H_trans₂
      . exact H_trans₁
    . apply ProcTyCongr.par_comm

namespace ProcTyCongr
  lemma congr_preserves_behaviour (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ →
      ((∀ τ₁' lbl, ProcTyTransition τ₁ lbl τ₁' → ∃ τ₂', ProcTyTransition τ₂ lbl τ₂' ∧ ProcTyCongr τ₁' τ₂')
        ∧
        (∀ τ₂' lbl, ProcTyTransition τ₂ lbl τ₂' → ∃ τ₁', ProcTyTransition τ₁ lbl τ₁' ∧ ProcTyCongr τ₁' τ₂')
      ) := by
    intro H_congr
    induction H_congr
    case refl τ' =>
      constructor
      . intro τ₁' lbl H_trans
        exists τ₁'
        constructor
        . exact H_trans
        . apply ProcTyCongr.refl
      . intro τ₂' lbl H_trans
        exists τ₂'
        constructor
        . exact H_trans
        . apply ProcTyCongr.refl
    case symm τ' τ₁'' H_congr H_ind =>
      constructor
      . intro τ₁' lbl H_trans
        have H_ind' := H_ind.2 τ₁' lbl H_trans
        have ⟨τ₂', H_trans', H_congr'⟩ := H_ind'
        exists τ₂'
        constructor
        . exact H_trans'
        . apply ProcTyCongr.symm
          exact H_congr'
      . intro τ₂' lbl H_trans
        have H_ind' := H_ind.1 τ₂' lbl H_trans
        have ⟨τ₁', H_trans', H_congr'⟩ := H_ind'
        exists τ₁'
        constructor
        . exact H_trans'
        . apply ProcTyCongr.symm
          exact H_congr'
    case trans τ' τ₁'' τ₃ H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
      constructor
      . intro τ₁' lbl H_trans
        have H_ind₁' := H_ind₁.1 τ₁' lbl H_trans
        have ⟨τ₂', H_trans₂, H_congr₂'⟩ := H_ind₁'
        have H_ind₂' := H_ind₂.1 τ₂' lbl H_trans₂
        have ⟨τ₃', H_trans₃, H_congr₃'⟩ := H_ind₂'
        exists τ₃'
        constructor
        . exact H_trans₃
        . apply ProcTyCongr.trans <;> assumption
      . intro τ₃' lbl H_trans
        have H_ind₁' := H_ind₂.2 τ₃' lbl H_trans
        have ⟨τ₂', H_trans₂, H_congr₂'⟩ := H_ind₁'
        have H_ind₂' := H_ind₁.2 τ₂' lbl H_trans₂
        have ⟨τ₁', H_trans₁, H_congr₁'⟩ := H_ind₂'
        exists τ₁'
        constructor
        . exact H_trans₁
        . apply ProcTyCongr.trans <;> assumption
    case par_comm τ' τ'' =>
      constructor
      . intro τ₁' lbl H_trans
        apply par_symm_trans_congr
        exact H_trans
      . intro τ₂' lbl H_trans
        have H := par_symm_trans_congr τ'' τ' τ₂' lbl H_trans
        have ⟨τ₂'', H⟩ := H
        exists τ₂''
        constructor
        . exact H.1
        . apply ProcTyCongr.symm
          exact H.2

  lemma congr_of_skip_is_skip (τ₁ τ₂ : ProcTy) :
    (ProcTyCongr τ₁ τ₂) → (τ₁ = ProcTy.skip ↔ τ₂ = ProcTy.skip) := by
      intro H_congr
      generalize H_skip : ProcTy.skip = τ at H_congr
      induction H_congr
      case refl =>
        rfl
      case symm τ₁ τ₂ H_congr =>
        symm
        exact H_congr
      case trans τ₁' τ₂' τ₃ H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
        rewrite [H_ind₁]
        rewrite [H_ind₂]
        rfl
      case par_comm τ₁' τ₂' =>
        rewrite [← H_skip]
        simp

  lemma congr_preserves_elim_to_skip : ∀ (τ₁ τ₂ : ProcTy),
      ProcTyCongr τ₁ τ₂ →
      ProcTyCompElim τ₁ ProcTy.skip → ProcTyCompElim τ₂ ProcTy.skip := by
    intro τ₁ τ₂ H_congr H_elim
    generalize H_skip : ProcTy.skip = τ₂' at H_elim
    revert τ₂ H_skip
    induction H_elim
    case refl τ' =>
      intro τ₂ H_congr H_skip
      have H_τ₂ : τ₂ = ProcTy.skip := by
        rewrite [← congr_of_skip_is_skip (τ₁ := τ') (τ₂ := τ₂)]
        . symm
          exact H_skip
        . exact H_congr
      rewrite [H_τ₂]
      rewrite [← H_skip]
      apply ProcTyCompElim.refl
    case eps_elim τs τs' τs'' H_trans H_elim H_ind =>
      intro τ₂ H_congr H_skip
      have ⟨τ₂'', H_τ₂''⟩ :=
        (congr_preserves_behaviour τs τ₂ H_congr).left τs' AbstractTransLabel.ε H_trans
      have H' := H_ind τ₂'' H_τ₂''.2 H_skip
      apply ProcTyCompElim.eps_elim (τs' := τ₂'')
      . exact H_τ₂''.1
      . exact H'

end ProcTyCongr

-- Being eliminated to another type while keeping being a supertype of a given type
inductive ProcTyCompElimWithSub : ProcTy → ProcTy → ProcTy → Prop where
  | base (τ₁ τ₂ : ProcTy) :
    ProcTySub τ₂ τ₁ →
    ProcTyCompElimWithSub τ₁ τ₁ τ₂
  | step (τ₁ τ₁' τₑ τ₂ : ProcTy) :
    ProcTySub τ₂ τ₁ →
    ProcTyTransition τ₁ AbstractTransLabel.ε τ₁' →
    ProcTyCompElimWithSub τ₁' τₑ τ₂ →
    ProcTyCompElimWithSub τ₁ τₑ τ₂

lemma procty_comp_elim_with_sub_implies_comp_elim : ∀ (τ₁ τ₂ τ₃ : ProcTy),
    ProcTyCompElimWithSub τ₁ τ₂ τ₃ →
    ProcTyCompElim τ₁ τ₂ := by sorry -- trivial

namespace ProcTySub
  lemma subtype_refinement_elim_single (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyTransition τ₁ AbstractTransLabel.ε τ₁' →
    ∃ τ₂', ProcTyTransition τ₂ AbstractTransLabel.ε τ₂' ∧ (ProcTySub τ₁ τ₂' ∨ ProcTySub τ₁' τ₂') := by

    intro H_sub H_trans
    revert H_trans τ₁'
    induction H_sub
    case congr τ₁'' τ₂'' H_congr =>
      intro τ₁' H_trans
      have H := (ProcTyCongr.congr_preserves_behaviour τ₁'' τ₂'' H_congr).left τ₁' AbstractTransLabel.ε H_trans
      have ⟨τ₂', H_trans₂, H_congr'⟩ := H
      exists τ₂'
      constructor
      . exact H_trans₂
      . right
        apply ProcTySub.congr
        exact H_congr'
    case choice_relax τ₁'' τ₂'' =>
      intro τ₁' H_trans
      exists τ₁''
      constructor
      . aesop
      . left
        apply ProcTySub.congr
        apply ProcTyCongr.refl
    case trans τ₁'' τ₂'' τ₃'' H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
      intro τ₁' H_trans
      have H_ind₁' := H_ind₁ τ₁' H_trans
      have ⟨τ₂''', H_trans₂, H_sub₂'⟩ := H_ind₁'
      have H_ind₂' := H_ind₂ τ₂''' H_trans₂
      have ⟨τ₃''', H_trans₃, H_sub₃'⟩ := H_ind₂'
      exists τ₃'''
      constructor
      . exact H_trans₃
      . cases H_sub₃' <;> cases H_sub₂'
        . left
          apply ProcTySub.trans (τ₂ := τ₂'') <;> assumption
        . left
          apply ProcTySub.trans (τ₂ := τ₂'') <;> assumption
        . left
          apply ProcTySub.trans (τ₂ := τ₂''') <;> assumption
        . right
          apply ProcTySub.trans (τ₂ := τ₂''') <;> assumption

  lemma sub_preserves_behaviour (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ε →
    ProcTySub τ₁ τ₂ → ProcTyTransition τ₂ lbl τ₂' →
    ∃ τ₁'', ProcTyTransition τ₁ lbl τ₁'' ∧ ProcTySub τ₁'' τ₂' := by

    intro H_not_ε H_sub H_trans
    revert H_not_ε τ₂'
    induction H_sub <;> intro τ₂' H_not_ε H_trans
    case congr τ₁'' τ₂'' H_congr =>
      have ⟨τ₁', H_τ₁'⟩ :=
        (ProcTyCongr.congr_preserves_behaviour τ₁'' τ₂'' H_congr).right τ₂' lbl H_trans
      exists τ₁'
      constructor
      . exact H_τ₁'.1
      . apply ProcTySub.congr
        exact H_τ₁'.2
    case choice_relax τ₁'' τ₂'' =>
      have H := ProcTySub.choice_relax τ₁'' τ₂''
      cases H_trans <;> simp at H_not_ε
    case trans τ₁'' τ₂'' τ₃'' H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
      have H_ind₂' := H_ind₂ τ₂' H_not_ε H_trans
      have ⟨τ₂''', H_trans₂, H_sub₂'⟩ := H_ind₂'
      have H_ind₁' := H_ind₁ τ₂''' H_not_ε H_trans₂
      have ⟨τ₁'', H_trans₁, H_sub₁'⟩ := H_ind₁'
      exists τ₁''
      constructor
      . exact H_trans₁
      . apply ProcTySub.trans (τ₂ := τ₂''')
          <;> assumption

  set_option maxHeartbeats 5000000

  lemma sub_preserves_behaviour_elim (τ₁ τ₂ τ₂' : ProcTy) :
    ProcTySub τ₁ τ₂ → ProcTyTransition τ₂ AbstractTransLabel.ε τ₂' →
    ∃ τ₂'', (
      ProcTyTransition τ₂ AbstractTransLabel.ε τ₂'' ∧
      ∃ τ₁', (τ₁' = τ₁ ∨ ProcTyTransition τ₁ AbstractTransLabel.ε τ₁') ∧ ProcTySub τ₁' τ₂'') := by
    intro H_sub
    revert τ₂'
    induction H_sub <;> intro τ₂' H_trans
    case congr τ₁'' τ₂'' H_congr =>
      have H := (ProcTyCongr.congr_preserves_behaviour τ₁'' τ₂'' H_congr).right τ₂' AbstractTransLabel.ε H_trans
      have ⟨τ₁', H_trans₁, H_congr'⟩ := H
      exists τ₂'
      constructor
      . exact H_trans
      . exists τ₁'
        constructor
        . right
          exact H_trans₁
        . apply ProcTySub.congr
          exact H_congr'
    case choice_relax τ₁'' τ₂'' =>
      have H := ProcTySub.choice_relax τ₁'' τ₂''
      cases H_trans <;>
      (
        exists τ₁''
        constructor
        . apply ProcTyTransition.choice_left
        . exists τ₁''
          constructor
          . left
            rfl
          . apply ProcTySub.congr
            apply ProcTyCongr.refl
      )
    case trans τ₁'' τ₂'' τ₃'' H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
      have H_ind₂' := H_ind₂ τ₂' H_trans
      have ⟨τ₃''', H_trans₃, τ₂''', H_eq₂, H_sub₂'⟩ := H_ind₂'
      cases H_eq₂
      case inl H_eq₂' =>
        exists τ₃'''
        constructor
        . exact H_trans₃
        . exists τ₁''
          constructor
          . left
            rfl
          . apply ProcTySub.trans (τ₂ := τ₂'')
            . exact H_sub₁
            . rewrite [← H_eq₂']
              exact H_sub₂'
      case inr H_sub₂' =>
        have H_ind₁' := H_ind₁ τ₂''' H_sub₂'
        have ⟨τ₂'''', H_trans₂, τ₁''', H_eq₁', H_sub₁'⟩ := H_ind₁'
        have H := subtype_refinement_elim_single τ₂'' τ₂'''' τ₃'' H_sub₂ H_trans₂
        have ⟨τ₃'''', H_trans₃', H_sub₃'⟩ := H
        exists τ₃''''
        constructor
        . exact H_trans₃'
        . cases H_eq₁'
          case inl H_eq₁' =>
            exists τ₁''
            constructor
            . left
              rfl
            . cases H_sub₃'
              case inr H_sub₃' =>
                apply ProcTySub.trans (τ₂ := τ₂'''')
                . rewrite [← H_eq₁']
                  exact H_sub₁'
                . exact H_sub₃'
              case inl H_sub₃' =>
                apply ProcTySub.trans (τ₂ := τ₂'')
                . exact H_sub₁
                . exact H_sub₃'
          case inr H_sub₁' =>
            cases H_sub₃'
            case inl H_sub₃' =>
              exists τ₁''
              constructor
              . left
                rfl
              . apply ProcTySub.trans (τ₂ := τ₂'')
                . exact H_sub₁
                . exact H_sub₃'
            case inr H_sub₃' =>
              exists τ₁'''
              constructor
              . right
                exact H_sub₁'
              . apply ProcTySub.trans (τ₂ := τ₂'''')
                . rename_i H'
                  exact H'
                . exact H_sub₃'

  lemma elim_sub_implies_sub_head (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTyCompElimWithSub τ₁ τ₁' τ₂ →
    ProcTySub τ₂ τ₁ := by
    intro H_elim
    induction H_elim <;> aesop


  lemma subtype_preserves_elim_sub : ∀ (τ₁ τ₁' τ₂ τ₂' : ProcTy),
    ProcTyCompElimWithSub τ₁ τ₁' τ₂' →
    ProcTySub τ₂ τ₂' →
    ProcTyCompElimWithSub τ₁ τ₁' τ₂ := by
    intro τ₁ τ₁' τ₂ τ₂' H_elim H_sub
    induction H_elim
    case base τ₁ τ₂' H_sub' =>
      apply ProcTyCompElimWithSub.base
      apply ProcTySub.trans (τ₂ := τ₂')
      . apply ProcTySub.trans (τ₂ := τ₂)
        . apply ProcTySub.congr
          apply ProcTyCongr.refl
        . exact H_sub
      . exact H_sub'
    case step τ₁ τ₁' τₑ τ₂ H_sub H_trans H_elim H_ind =>
      apply ProcTyCompElimWithSub.step
      . apply ProcTySub.trans (τ₂ := τ₂)
        . exact H_sub
        . assumption
      . exact H_trans
      . apply H_ind
        exact H_sub

  lemma subtype_refinement_elim_multi (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyCompElim τ₁ τ₁' →
    ∃ τ₂', ProcTyCompElim τ₂ τ₂' ∧ ProcTySub τ₁' τ₂' := by

    intro H_sub
    revert τ₁'
    induction H_sub
    case congr τ₁ τ₂ H_congr =>
      intro τ₁' H_elim
      revert τ₂
      induction H_elim
      case refl τ' =>
        intro τ₂ H_congr
        exists τ₂
        constructor
        . apply ProcTyCompElim.refl
        . apply ProcTySub.congr
          exact H_congr
      case eps_elim τs τs' τs'' H_trans H_elim H_ind =>
        intro τ₂ H_congr
        have H := (ProcTyCongr.congr_preserves_behaviour τs τ₂ H_congr).left τs' AbstractTransLabel.ε H_trans
        have ⟨τ₂', H_trans₂, H_congr'⟩ := H
        have H_ind' := H_ind τ₂' H_congr'
        have ⟨τ₂'', H_elim'', H_congr''⟩ := H_ind'
        exists τ₂''
        constructor
        . apply ProcTyCompElim.eps_elim (τs' := τ₂')
          . exact H_trans₂
          . exact H_elim''
        . exact H_congr''
    case choice_relax τ₁ τ₂ =>
      intro τ₁' H_elim
      exists τ₁'
      constructor
      . aesop
      . apply ProcTySub.congr
        apply ProcTyCongr.refl
    case trans τ₁ τ₂ τ₃ H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
      intro τ₁' H_elim
      have ⟨τ₂', H_elim₂, H_sub₂'⟩ := H_ind₁ τ₁' H_elim
      have ⟨τ₃', H_elim₃, H_sub₃'⟩ := H_ind₂ τ₂' H_elim₂
      exists τ₃'
      constructor
      . exact H_elim₃
      . apply ProcTySub.trans (τ₂ := τ₂')
          <;> assumption

  lemma congr_preserves_guarded : ∀ (τ₁ τ₂ : ProcTy),
      ProcTyCongr τ₁ τ₂ →
      (ProcTyGuarded ∅ ∅ τ₂ ↔ ProcTyGuarded ∅ ∅ τ₁) := by

    intro τ₁ τ₂ H_congr
    induction H_congr
    case refl τ' =>
      constructor
      . intro H_guarded
        exact H_guarded
      . intro H_guarded
        exact H_guarded
    case symm τ₁' τ₂' H_congr =>
      symm
      exact H_congr
    case trans τ₁' τ₂' τ₃ H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
      rewrite [H_ind₂]
      exact H_ind₁
    case par_comm τ₁' τ₂' =>
      constructor <;> (
        intro H_guarded
        cases H_guarded
        aesop
      )

  lemma subtype_preserves_guarded : ∀ (τ₁ τ₂ : ProcTy),
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyGuarded ∅ ∅ τ₁ := by

    intro τ₁ τ₂ H_sub H_guarded
    induction H_sub
    case congr τ₁' τ₂' H_congr =>
      apply (congr_preserves_guarded τ₁' τ₂' H_congr).mp
      exact H_guarded
    case choice_relax τ₁' τ₂' =>
      cases H_guarded
      assumption
    case trans τ₁' τ₂' τ₃ H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
      apply H_ind₁
      apply H_ind₂
      exact H_guarded

  lemma subtype_refinement_label : ∀ (τ₁ τ₁' τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyTransition τ₁ lbl τ₁' →
      ∃ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' ∧ ProcTyGuarded ∅ ∅ τ₂' ∧ ProcTySub τ₁' τ₂' := by sorry -- FIXME: prove

  lemma congr_refinement_label_multi : ∀ (τ₁ τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTyCongr τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      (
        ∀ τ₁', ProcTyIncompTransition τ₁ lbl τ₁' →
        ∃ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' ∧ ProcTyGuarded ∅ ∅ τ₂' ∧ ProcTyCongr τ₁' τ₂'
      )
        ∧
      (
        ∀ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' →
        ∃ τ₁', ProcTyIncompTransition τ₁ lbl τ₁' ∧ ProcTyGuarded ∅ ∅ τ₁' ∧ ProcTyCongr τ₁' τ₂'
      ) := by
    intro τ₁ τ₂ lbl H_not_ε H_congr H_guarded
    revert lbl
    induction H_congr
    case refl τ' =>
      intro lbl H_not_ε
      constructor
      . intro τ₁' H_trans
        exists τ₁'
        constructor
        . exact H_trans
        . constructor
          . apply ProcTyGuarded.incomp_trans_preserves_guarded (τ₁ := τ') (lbl := lbl) <;> assumption
          . apply ProcTyCongr.refl
      . intro τ₂' H_trans
        exists τ₂'
        constructor
        . exact H_trans
        . constructor
          . apply ProcTyGuarded.incomp_trans_preserves_guarded (τ₁ := τ') (lbl := lbl) <;> assumption
          . apply ProcTyCongr.refl
    case symm τ₁' τ₂' H_congr H_ind =>
      intro lbl H_not_ε
      have H_guarded₂ : ProcTyGuarded ∅ ∅ τ₂' := by
        apply (congr_preserves_guarded τ₁' τ₂' H_congr).mpr
        exact H_guarded
      have H_ind' := H_ind H_guarded₂ lbl H_not_ε
      constructor
      . intro τ₁' H_trans
        have H_ind'' := H_ind'.2 τ₁' H_trans
        have ⟨τ₂', H_trans', H_congr'⟩ := H_ind''
        exists τ₂'
        constructor
        . exact H_trans'
        . constructor
          . exact H_congr'.1
          . apply ProcTyCongr.symm
            exact H_congr'.2
      . intro τ₂' H_trans
        have H_ind'' := H_ind'.1 τ₂' H_trans
        have ⟨τ₁', H_trans', H_congr'⟩ := H_ind''
        exists τ₁'
        constructor
        . exact H_trans'
        . constructor
          . exact H_congr'.1
          . apply ProcTyCongr.symm
            exact H_congr'.2
    case trans τ₁' τ₂' τ₃ H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
      intro lbl H_not_ε
      have H_ind₂' := H_ind₂ H_guarded lbl H_not_ε
      have H_guarded₂ := (congr_preserves_guarded τ₂' τ₃ H_congr₂).mp H_guarded
      have H_ind₁' := H_ind₁ H_guarded₂ lbl H_not_ε
      constructor
      . intro τ₁ H_trans
        have H_ind₁'' := H_ind₁'.1 τ₁ H_trans
        have ⟨τ₂', H_trans', H_congr'⟩ := H_ind₁''
        have H_ind₂'' := H_ind₂'.1 τ₂' H_trans'
        have ⟨τ₃', H_trans'', H_congr''⟩ := H_ind₂''
        exists τ₃'
        constructor
        . exact H_trans''
        . constructor
          . exact H_congr''.1
          . apply ProcTyCongr.trans (τ₂ := τ₂')
            . exact H_congr'.2
            . exact H_congr''.2
      . intro τ₃ H_trans
        have H_ind₂'' := H_ind₂'.2 τ₃ H_trans
        have ⟨τ₂', H_trans', H_congr''⟩ := H_ind₂''
        have H_ind₁'' := H_ind₁'.2 τ₂' H_trans'
        have ⟨τ₁', H_trans'', H_congr'⟩ := H_ind₁''
        exists τ₁'
        constructor
        . exact H_trans''
        . constructor
          . exact H_congr'.1
          . apply ProcTyCongr.trans (τ₂ := τ₂')
            . exact H_congr'.2
            . exact H_congr''.2
    case par_comm τ₁' τ₂' =>
      intro lbl H_not_ε
      constructor
      . intro τ₁' H_trans
        have ⟨τ₀, H_trans, H_elim⟩ := H_trans
        rename_i τ' H_trans
        sorry -- FIXME: prove
      . sorry




  lemma subtype_refinement_label_multi : ∀ (τ₁ τ₁' τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyIncompTransition τ₁ lbl τ₁' →
      ∃ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' ∧ ProcTyGuarded ∅ ∅ τ₂' ∧ ProcTySub τ₁' τ₂' := by

    intro τ₁ τ₁' τ₂ lbl H_not_ε H_sub
    revert lbl τ₁'
    induction H_sub
    all_goals sorry -- FIXME: prove


  lemma sub_of_skip_is_skip (τ : ProcTy) :
    ProcTySub τ ProcTy.skip → τ = ProcTy.skip := by
      intro H_sub
      generalize H_skip : ProcTy.skip = τ at H_sub
      induction H_sub
      case congr τ₁ τ₂ H_congr =>
        rewrite [← H_skip]
        rewrite [ProcTyCongr.congr_of_skip_is_skip τ₁ τ₂ H_congr]
        symm
        exact H_skip
      case choice_relax τ₁ τ₂ =>
        cases H_skip
      case trans τ₁ τ₂ τ₃ H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
        have H_ind₂' := H_ind₂ H_skip
        have H_ind₁' := H_ind₁ (by rewrite [H_ind₂']; grind)
        grind

end ProcTySub
