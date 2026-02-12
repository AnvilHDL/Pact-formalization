import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers

lemma subtype_preserves_reduction : ∀ (τ₁ τ₂ τ₁' : ProcTy)
        (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTyTransition τ₁ lbl τ₂ →
      ProcTySub τ₁ τ₁' →
      (∃ τ₂', ProcTyTransition τ₁' lbl τ₂' ∧ ProcTySub τ₂ τ₂') := by sorry

namespace ProcTyCongr
  lemma congr_preserves_behaviour (τ₁ τ₂ τ₁' : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyCongr τ₁ τ₂ → ProcTyTransition τ₁ lbl τ₁' → ∃ τ₂', ProcTyTransition τ₂ lbl τ₂' ∧ ProcTyCongr τ₁' τ₂' := by sorry -- FIXME: prove

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
  lemma sub_preserves_behaviour (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    lbl ≠ AbstractTransLabel.ε →
    ProcTySub τ₁ τ₂ → ProcTyTransition τ₂ lbl τ₂' →
    ∃ τ₁'', ProcTyTransition τ₁ lbl τ₁'' ∧ ProcTySub τ₁'' τ₂' := by sorry -- FIXME: prove

  lemma sub_preserves_behaviour_elim (τ₁ τ₂ τ₂' : ProcTy) :
    ProcTySub τ₁ τ₂ → ProcTyTransition τ₂ AbstractTransLabel.ε τ₂' →
    ∃ τ₂'', (
      ProcTyTransition τ₂ AbstractTransLabel.ε τ₂'' ∧
      ∃ τ₁', (τ₁' = τ₁ ∨ ProcTyTransition τ₁ AbstractTransLabel.ε τ₁') ∧ ProcTySub τ₁' τ₂'') := by sorry -- FIXME: prove

  lemma subtype_refinement_elim (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyTransition τ₁ AbstractTransLabel.ε τ₁' →
    ∃ τ₂', ProcTyCompElim τ₂ τ₂' ∧ ProcTySub τ₁' τ₂' := by sorry -- FIXME: prove

  lemma subtype_refinement_elim_strong (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyTransition τ₁ AbstractTransLabel.ε τ₁' →
    ∃ τ₂' τ₂'', ProcTyCompElimWithSub τ₂ τ₂' τ₁
      ∧ ProcTyTransition τ₂' AbstractTransLabel.ε τ₂'' ∧ ProcTySub τ₁' τ₂'' := by sorry -- FIXME: prove

  lemma subtype_refinement_elim_single (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyTransition τ₁ AbstractTransLabel.ε τ₁' →
    ∃ τ₂', ProcTyTransition τ₂ AbstractTransLabel.ε τ₂' ∧ (ProcTySub τ₁ τ₂' ∨ ProcTySub τ₁' τ₂') := by sorry -- FIXME: prove

  lemma subtype_refinement_elim_multi (τ₁ τ₁' τ₂ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTyCompElim τ₁ τ₁' →
    ∃ τ₂', ProcTyCompElim τ₂ τ₂' ∧ ProcTySub τ₁' τ₂' := by

    intro H_sub
    revert τ₁'
    induction H_sub
    case congr τ₁ τ₂ H_congr =>
      sorry
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

  lemma subtype_preserves_guarded : ∀ (τ₁ τ₂ : ProcTy),
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyGuarded ∅ ∅ τ₁ := by sorry -- FIXME: prove

  lemma subtype_refinement_label_strong : ∀ (τ₁ τ₁' τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyTransition τ₁ lbl τ₁' →
      ∃ τ₂' τ₂'', ProcTyCompElimWithSub τ₂ τ₂' τ₁ ∧ ProcTyTransition τ₂' lbl τ₂'' ∧ ProcTySub τ₁' τ₂'' := by sorry -- FIXME: prove

  lemma subtype_refinement_label : ∀ (τ₁ τ₁' τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyTransition τ₁ lbl τ₁' →
      ∃ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' ∧ ProcTyGuarded ∅ ∅ τ₂' ∧ ProcTySub τ₁' τ₂' := by sorry -- FIXME: prove

  lemma subtype_refinement_label_multi : ∀ (τ₁ τ₁' τ₂ : ProcTy)
      (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTySub τ₁ τ₂ →
      ProcTyGuarded ∅ ∅ τ₂ →
      ProcTyIncompTransition τ₁ lbl τ₁' →
      ∃ τ₂', ProcTyIncompTransition τ₂ lbl τ₂' ∧ ProcTyGuarded ∅ ∅ τ₂' ∧ ProcTySub τ₁' τ₂' := by sorry -- FIXME: prove

end ProcTySub
