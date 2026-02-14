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

end ProcTyIncompTransition
