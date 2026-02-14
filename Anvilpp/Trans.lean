import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers
import Anvilpp.Subtyping


namespace ProcTyIncompTransition
  lemma skip_typing_implies_skip_elim_rev :
        ∀ {p : Semantics.ProcComp},
          ProcTyJudgement ProcTyContext.empty p ProcTy.skip →
          p = Proc.skip := by
    intro p H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    generalize H_skip : ProcTy.skip = τ at H_typing
    induction H_typing <;> try (cases H_skip; done)
    case skip =>
      rfl
    case subtype =>
      rename_i p' τ₁ τ₂ H_typing H_sub H_ind
      rewrite [← H_skip] at H_sub
      apply H_ind
      . exact H_ctx
      . symm
        apply ProcTySub.sub_of_skip_is_skip
        exact H_sub

  lemma skip_typing_implies_skip_elim :
        ∀ {τ : ProcTy},
          ProcTyJudgement ProcTyContext.empty Proc.skip τ →
          ProcTyCompElim τ ProcTy.skip := by
    intro τ H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    generalize H_skip : Proc.skip = p at H_typing
    induction H_typing <;> try (cases H_skip; done)
    case skip =>
      apply ProcTyCompElim.refl
    case subtype =>
      rename_i ctx' p' τ₁ τ₂ H_typing H_sub H_ind
      have H_ind' := H_ind H_ctx H_skip
      clear H_ind
      induction H_sub
      case congr τ₁ τ₂ H_congr =>
        apply ProcTyCongr.congr_preserves_elim_to_skip (τ₁ := τ₁) <;> assumption
      case choice_relax τ₁' τ₂' =>
        apply ProcTyCompElim.eps_elim (τs' := τ₁')
        . aesop
        . exact H_ind'
      case trans τ₁'' τ₂'' τ₃'' H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
        have H_ind₁' := H_ind₁ H_typing H_ind'
        have H_typing₂ : ProcTyJudgement ctx' p' τ₂'' := by
          apply ProcTyJudgement.subtype (τ₁ := τ₁'')
          . exact H_typing
          . exact H_sub₁
        have H_ind₂' := H_ind₂ H_typing₂ H_ind₁'
        exact H_ind₂'
end ProcTyIncompTransition
