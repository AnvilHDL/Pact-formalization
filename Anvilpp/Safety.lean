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
        . apply ProcTyCompElim.eps_elim (τs' := ProcTy.par τ₁' τ₂)
          . apply ProcTyTransition.par_left <;> try trivial
            . simp
            . sorry -- FIXME: prove separately
            all_goals sorry
          sorry
      all_goals sorry
    all_goals sorry

lemma type_emulates_proc_label : ∀ (p p' : Semantics.ProcComp)
                                (τ : ProcTyComposition) (lbl : TransLabel),
    CompositionTyJudgement p τ →
    Semantics.Reduces p lbl p' →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyIncompTransition τ (AbstractTransLabel.fromConcrete lbl) τ' := by

    intro p p' τ lbl H_typing H_reduces
    revert H_reduces p' lbl
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> intro p' lbl H_reduces
    case par =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case par_tock =>
        rename_i p₁' p₂' H_red₁ H_red₂
        sorry
      all_goals sorry
    all_goals sorry
