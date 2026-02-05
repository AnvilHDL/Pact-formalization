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


macro "induction_prep" H_p:ident p'':ident H_ctx:ident ctx:ident p:term " at " H_typing:ident : tactic =>
  `(tactic| (
    generalize $H_p : $p = $p''
    rewrite [$(Lean.mkIdent H_p.getId):term] at ($(Lean.mkIdent H_typing.getId):term)
    unfold CompositionTyJudgement at $(Lean.mkIdent H_typing.getId):term
    generalize $H_ctx : ProcTyContext.empty = $ctx
    rewrite [$(Lean.mkIdent H_ctx.getId):term] at $(Lean.mkIdent H_typing.getId):term
    -- revert $H_p $H_ctx
    induction $(Lean.mkIdent H_typing.getId):term
    all_goals (try { intro H; cases H }; try contradiction)
    ))

-- TODO: the most important proof
/-
  Issues:
  - Need to ensure that if process is a deadend, then type is also a deadend (i.e., no deadend is removed by typing)
    - Equivalently, if type is not a deadend, then process is also not a deadend
  - Maybe need to ignore ε transitions
  - Variable binding (the induction principle might need to consider this)
-/
lemma type_emulates_proc : ∀ (p p' : Semantics.ProcComp)
                             (τ : ProcTyComposition) (lbl : TransLabel) (ex_msg : Finset (MessageId × MessageDir)),
    lbl ≠ TransLabel.ε →
    CompositionTyJudgement p τ →
    Semantics.IncompReduces ex_msg p lbl p' →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyIncompTransition ex_msg τ (AbstractTransLabel.fromConcrete lbl) τ' := by

    intro p p' τ lbl ex_msg H_not_eps H_typing H_reduces
    revert H_not_eps H_reduces p'
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx
    rewrite [H_ctx] at H_typing
    induction H_typing <;> intro p' H_not_eps H_reduces <;>
    unfold Semantics.IncompReduces at H_reduces <;>
    have ⟨p₁', H_reduces⟩ := H_reduces <;>
    have ⟨H_red, H_elim⟩ := H_reduces
    case cycle =>
      have H_p : p₁' = Proc.cycle := by
        generalize H_cycle : Proc.cycle = p₁ at H_elim
        rewrite [← H_cycle]
        -- revert H_cycle
        induction H_elim
        . symm
          exact H_cycle
        . rename_i Hr H_elim H_ind
          have H_ind := H_ind H_reduces H_red
          rewrite [← H_cycle] at Hr
          cases Hr
      rewrite [H_p] at H_red
      cases H_red
      exists ProcTy.skip
      constructor
      . apply ProcTyJudgement.skip
      . unfold ProcTyIncompTransition
        exists ProcTy.cycle
        constructor
        . apply ProcTyTransition.tock
        . apply ProcTyCompElim.refl
    case dollar =>
      rename ProcId => pid
      have H_p : p₁' = Proc.endp pid := by
        generalize H_dollar : Proc.endp pid = p₁ at H_elim
        rewrite [← H_dollar]
        -- revert H_dollar
        induction H_elim
        . symm
          exact H_dollar
        . rename_i Hr H_elim H_ind
          have H_ind := H_ind H_reduces H_red
          rewrite [← H_dollar] at Hr
          cases Hr
      rewrite [H_p] at H_red
      cases H_red
    case skip =>
      have H_p : p₁' = Proc.skip := by
        generalize H_skip : Proc.skip = p₁ at H_elim
        rewrite [← H_skip]
        -- revert H_skip
        induction H_elim
        . symm
          exact H_skip
        . rename_i Hr H_elim H_ind
          have H_ind := H_ind H_reduces H_red
          rewrite [← H_skip] at Hr
          cases Hr
      rewrite [H_p] at H_red
      cases H_red
    case message_send =>
      rename MessageId => msg
      rename Expr => e
      have H_p : p₁' = Proc.send msg e := by
        generalize H_send : Proc.send msg e = p₁ at H_elim
        rewrite [← H_send]
        induction H_elim
        . symm
          exact H_send
        . rename_i Hr H_elim H_ind
          have H_ind := H_ind H_reduces H_red
          rewrite [← H_send] at Hr
          cases Hr
      rewrite [H_p] at H_red
      cases H_red
      exists ProcTy.skip
      constructor
      . apply ProcTyJudgement.skip
      . unfold ProcTyIncompTransition
        exists ProcTy.message $ MessageExch.send msg
        constructor
        . apply ProcTyTransition.message_send
        . apply ProcTyCompElim.refl
    case message_recv =>
      rename_i ctx' msg x p_body τ_body H_typing H_ind _
      have H_p : p₁' = Proc.recv msg x p_body := Semantics.CompElim.comp_elim_preserves_recv H_elim
      rewrite [H_p] at H_red
      cases H_red <;> sorry
      -- have H_elim_c := Semantics.CompElim.seq_elim H_reduces
      -- -- different cases of seq elim
      -- cases H_elim_c <;> rename_i H_elim_c
      -- . have ⟨p₁'', H_elim_c⟩ := H_elim_c
      --   have H_p₁'' : p₁'' = Proc.skip := Semantics.CompElim.comp_elim_preserves_skip H_elim_c.1
      --   rewrite [H_p₁''] at H_elim_c
      --   rewrite [H_elim_c.2]
      --   exists (ProcTy.seq ProcTy.skip τ_body)
      --   constructor
      --   . apply ProcTyJudgement.seq
      --     . apply ProcTyJudgement.skip
      --     . sorry -- trivial
      --   . unfold ProcTyIncompTransition
      --     exists (ProcTy.message $ MessageExch.recv msg).seq τ_body, ProcTy.skip.seq τ_body
      --     constructor
      --     . apply ProcTyTransition.seq_step
      --       apply ProcTyTransition.message_recv
      --     . constructor
      --       . apply ProcTyCompElim.refl
      --       . apply ProcTyCompElim.refl
      -- . -- now this case the induction principles seem off
    case seq =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ H_reduces'
      have H_elim := Semantics.CompElim.seq_elim H_elim
      cases H_elim
      case inl H_elim =>
        have ⟨pₑ, H_elim⟩ := H_elim
        rewrite [H_elim.2] at H_red
        cases H_red
        case seq_step p₁'' H_red =>
          sorry
        case seq_skip =>
          contradiction
      case inr H_elim =>
        have H_p₂_red : Semantics.IncompReduces ex_msg p₂ lbl p' := by
          unfold Semantics.IncompReduces
          exists p₁'
          constructor
          . exact H_red
          . exact H_elim.2
        have H_ind₂ := H_ind₂ H_ctx p' H_not_eps H_p₂_red
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists τ₂'
        constructor
        . exact H_ind₂.1
        . rewrite [← H_ctx] at H_typing₁
          have H_elim_seg₁ := Semantics.CompElim.elim_preserves_typing (ex_msg := ex_msg) H_elim.1 H_typing₁
          have ⟨τ₁', H_elim_seg₁⟩ := H_elim_seg₁
          have H_elim_seg₂ : ProcTyCompElim ex_msg τ₁ ProcTy.skip := by
            apply ProcTyCompElim.elim_transitivity (τ₂ := τ₁')
            . exact H_elim_seg₁.1
            . apply ProcTyIncompTransition.skip_typing_implies_skip_elim
              exact H_elim_seg₁.2
          apply ProcTyIncompTransition.reduces_seq_skip
          . exact H_elim_seg₂
          . exact H_ind₂.2
    case par =>
      clear τ p ctx
      rename_i ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ _
      have H_elim_par := Semantics.CompElim.par_elim H_elim
      cases H_elim_par
      case inl H_elim_par =>
        have ⟨p₁ₘ, p₂ₘ, H_elim_f₁, H_elim_f₂, H_p₁⟩ := H_elim_par
        rewrite [H_p₁] at H_red
        cases H_red <;> try trivial
        case par_left H_red =>
          rename Proc => p₁ₘ'
          rename _ ⊆ _ => H_ex_msg
          rename Finset _ => ex_msg'
          have H_p₁_red_relax : Semantics.Reduces ex_msg p₁ₘ lbl p₁ₘ' := by
            apply Semantics.Reduces.enlarge_ex_msg_preserves_reduces
            . exact H_ex_msg
            . assumption
          have H_ind₁ := H_ind₁ H_ctx p₁ₘ' H_not_eps (by exists p₁ₘ)
          have ⟨τ₁', H_ind₁⟩ := H_ind₁
          rewrite [← H_ctx] at H_typing₂
          have H_p₂_typing := Semantics.CompElim.elim_preserves_typing H_elim_f₂ H_typing₂
          have ⟨τ₂', H_p₂_typing⟩ := H_p₂_typing
          exists (ProcTy.par τ₁' τ₂')
          constructor
          . apply ProcTyJudgement.par
            . exact H_ind₁.1
            . exact H_p₂_typing.2
          . apply ProcTyIncompTransition.reduces_par_left
            . exact H_ind₁.2
            . exact H_p₂_typing.1
        case par_right =>
          -- completely symmetrical
          rename Proc => p₂ₘ'
          rename _ ⊆ _ => H_ex_msg
          rename Finset _ => ex_msg'
          have H_p₂_red_relax : Semantics.Reduces ex_msg p₂ₘ lbl p₂ₘ' := by
            apply Semantics.Reduces.enlarge_ex_msg_preserves_reduces
            . exact H_ex_msg
            . assumption
          have H_ind₂ := H_ind₂ H_ctx p₂ₘ' H_not_eps (by exists p₂ₘ)
          have ⟨τ₂', H_ind₂⟩ := H_ind₂
          rewrite [← H_ctx] at H_typing₁
          have H_p₁_typing := Semantics.CompElim.elim_preserves_typing H_elim_f₁ H_typing₁
          have ⟨τ₁', H_p₁_typing⟩ := H_p₁_typing
          exists (ProcTy.par τ₁' τ₂')
          constructor
          . apply ProcTyJudgement.par
            . exact H_p₁_typing.2
            . exact H_ind₂.1
          . apply ProcTyIncompTransition.reduces_par_right
            . exact H_p₁_typing.1
            . exact H_ind₂.2
        case par_tock =>
          rename_i p₁'' p₂'' H_red₁ H_red₂ _
          sorry
        case par_message =>
          sorry
      case inr H_elim_par =>
        sorry

    all_goals sorry


    -- induction H_reduces <;> intro τ H_not_eps H_typing
    -- case tock ex_msg' =>
    --   induction_prep H_p p'' H_ctx ctx Proc.cycle at H_typing
    --   all_goals sorry
      -- . rename ProcTyContext => ctx'
      --   exists ProcTy.skip
      --   constructor
      --   . apply ProcTyJudgement.skip
      --   . unfold AbstractTransLabel.fromConcrete
      --     simp
      --     apply ProcTyTransition.tock
      -- . rename_i p'' τ₁ τ₂ H_typing H_sub H_ih
      --   have ⟨τ', H_ind⟩ := H_ih H_p
      --   have ⟨τ₂', H_ty⟩ := subtype_preserves_reduction ex_msg' τ₁ τ' τ₂
      --     (AbstractTransLabel.fromConcrete (TransLabel.ac Action.tock))
      --     (by simp) H_ind.2 H_sub
      --   exists τ₂'
      --   constructor
      --   . apply ProcTyJudgement.subtype (τ₁ := τ')
      --     . exact H_ind.1
      --     . exact H_ty.2
      --   . exact H_ty.1
    -- case seq_skip =>
    --   rename Proc => p₂
    --   induction_prep H_p p'' H_ctx ctx (Proc.skip.seq p₂) at H_typing
    -- case seq_step =>
    --   rename_i ex_msg' p₁ p₁' p₂ c H_red H_ind
    --   induction_prep H_p p'' H_ctx ctx (Proc.seq p₁ p₂) at H_typing
    --   . intro H_eq H_empt
    --     rename ProcTyContext => ctx'
    --     rename_i H_ind₁ H_ind₂
    --     have H_ind := H_ind₁
    -- all_goals sorry
    -- case seq_step =>
    --   intro τ H_not_eps H_typing
    --   rename_i H_ind
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   rename TransLabel => α
    --   rename Finset _ => ex_msg'
    --   rename_i H_red
    --   have H_ind' := H_ind τ₁ H_not_eps H_typing₁
    --   have ⟨τ₁', H_ind'⟩ := H_ind'
    --   exists ProcTy.seq τ₁' τ₂
    --   constructor
    --   . apply ProcTyJudgement.seq
    --     . exact H_ind'.1
    --     . exact H_typing₂
    --   . apply ProcTyTransition.seq_step
    --     exact H_ind'.2
    -- case send =>
    --   intro τ H_not_eps H_typing
    --   exists ProcTy.skip
    --   constructor
    --   . apply ProcTyJudgement.skip
    --   . unfold AbstractTransLabel.fromConcrete
    --     simp
    --     cases H_typing
    --     apply ProcTyTransition.message_send

    -- case recv =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i msg x p b τ' H_typing_body
    --   exists ProcTy.seq ProcTy.skip τ'
    --   constructor
    --   . apply ProcTyJudgement.seq
    --     . apply ProcTyJudgement.skip
    --     . sorry -- FIXME: prove separately
    --   . unfold AbstractTransLabel.fromConcrete
    --     simp
    --     apply ProcTyTransition.seq_step
    --     apply ProcTyTransition.message_recv
    --     -- apply ProcTyTransition.message_recv
    -- case par_skip_left =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   exists τ₂
    -- case par_skip_right =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   exists τ₁
    -- case par_left =>
    --   intro τ H_not_eps H_typing
    --   rename_i H_red₁ H_ind
    --   rename Finset _ => ex_msg'
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   have ⟨τ₁', H_ind'⟩ := H_ind τ₁ H_not_eps H_typing₁
    --   exists ProcTy.par τ₁' τ₂
    --   constructor
    --   . apply ProcTyJudgement.par
    --     . exact H_ind'.1
    --     . exact H_typing₂
    --   . apply ProcTyTransition.par_left
    --     all_goals sorry
    -- case par_right => -- symmetrical
    --   intro τ H_not_eps H_typing
    --   rename_i H_red₂ H_ind
    --   rename Finset _ => ex_msg'
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   have ⟨τ₂', H_ind'⟩ := H_ind τ₂ H_not_eps H_typing₂
    --   exists ProcTy.par τ₁ τ₂'
    --   constructor
    --   . apply ProcTyJudgement.par
    --     . exact H_typing₁
    --     . exact H_ind'.1
    --   . apply ProcTyTransition.par_right
    --     all_goals sorry
    -- case par_tock =>
    --   intro τ H_not_eps H_typing
    --   rename_i ex_msg' p₁ p₂ p₁' p₂' H_red₁ H_red₂ H_ind₁ H_ind₂
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂
    --   have ⟨τ₁', H_ind₁'⟩ := H_ind₁ τ₁ H_not_eps H_typing₁
    --   have ⟨τ₂', H_ind₂'⟩ := H_ind₂ τ₂ H_not_eps H_typing₂
    --   exists ProcTy.par τ₁' τ₂'
    --   constructor
    --   . apply ProcTyJudgement.par
    --     . exact H_ind₁'.1
    --     . exact H_ind₂'.1
    --   . apply ProcTyTransition.par_tock
    --     . apply procty_trans_preserved_under_extended_exmsg ex_msg'
    --       . trivial
    --       . exact H_ind₁'.2
    --     . apply procty_trans_preserved_under_extended_exmsg ex_msg'
    --       . trivial
    --       . exact H_ind₂'.2
    -- case recur_unfold =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename String => X
    --   rename ProcTy => τ
    --   exists τ.replaceVar X (ProcTy.recur X τ)
    -- case ifunfair_true =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
    --   exists τ₁
    -- case ifunfair_false =>
    --   -- symmetrical
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
    --   exists τ₂
    -- case iffair_true =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
    --   exists τ₁
    --   constructor
    --   . exact H_typing₁
    --   . apply ProcTyTransition.choice_fair_left
    -- case iffair_false =>
    --   -- symmetrical
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
    --   exists τ₂
    --   constructor
    --   . exact H_typing₂
    --   . apply ProcTyTransition.choice_fair_right
    -- case par_message =>
    --   intro τ H_not_eps H_typing
    --   rename_i H_sub₁ H_sub₂ H_nim₁ H_nim₂ H_red₁ H_red₂ H_ih₁ H_ih₂
    --   rename MessageId => msg
    --   rename_i ex_msg' ex_msg₁ ex_msg₂ dir dir' b p₁ p₁' p₂ p₂' H_dual
    --   cases H_typing
    --   rename_i τ₁ τ₂ H_typing₁ H_typing₂

    --   have ⟨τ₁', H_ih₁'⟩ := H_ih₁ τ₁ (by simp) H_typing₁
    --   have ⟨τ₂', H_ih₂'⟩ := H_ih₂ τ₂ (by simp) H_typing₂
    --   exists ProcTy.par τ₁' τ₂'
    --   constructor
    --   . apply ProcTyJudgement.par
    --     . exact H_ih₁'.1
    --     . exact H_ih₂'.1
    --   . apply ProcTyTransition.par_message (ex_msg₁ := ex_msg₁) (ex_msg₂ := ex_msg₂) <;> try trivial
    --     . intro mx H_mx
    --       apply (non_instant_msg_preservation p₁ τ₁ H_typing₁ mx).mp
    --       apply H_nim₁
    --       assumption
    --     . intro mx H_mx
    --       apply (non_instant_msg_preservation p₂ τ₂ H_typing₂ mx).mp
    --       apply H_nim₂
    --       assumption
    --     . exact H_ih₁'.2
    --     . exact H_ih₂'.2
    -- case xoffer_branch_else ex_msg' p_else branches H_mx =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename ProcTy => τ_else
    --   exists τ_else
    -- case offer_branch_else ex_msg' p_else branches H_mx =>
    --   -- similar to above
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename ProcTy => τ_else
    --   exists τ_else
    -- case xoffer_branch_send ex_msg' msg e p_else p_send br b br_send H_eval =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename ProcTy => τ_else
    --   rename ProcTyJudgement _ _ _ => H_typing
    --   rename_i H_len H_br_expr H_br_typing
    --   rename List (MessageExch × ProcTy) => br_tys
    --   have H_exists_br_ty : ∃ br_ty, (ChoiceBranch.send msg e p_send, br_ty) ∈ List.zip br br_tys := by
    --     apply Trivia.zip_list_exists br br_tys (ChoiceBranch.send msg e p_send)
    --     . aesop
    --     . assumption
    --   have ⟨br_ty, H_br_ty⟩ := H_exists_br_ty
    --   have H_br_typing' := H_br_typing (ChoiceBranch.send msg e p_send) br_ty H_br_ty
    --   cases H_br_typing'
    --   rename_i τ_br H_expr_ty H_br_typing'
    --   exists τ_br
    --   constructor
    --   . exact H_br_typing'
    --   . unfold AbstractTransLabel.fromConcrete
    --     simp
    --     apply ProcTyTransition.xoffer_branch (me := MessageExch.send msg)
    --     exact (List.of_mem_zip H_br_ty).2
    -- case xoffer_branch_recv ex_msg' var p_else branches msg p_br b H_br =>
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename ProcTy => τ_else
    --   rename ProcTyJudgement _ _ _ => H_typing
    --   rename_i H_len H_br_expr H_br_typing
    --   rename List (MessageExch × ProcTy) => br_tys
    --   have H_exists_br_ty : ∃ br_ty, (ChoiceBranch.recv msg var p_br, br_ty) ∈ List.zip branches br_tys := by
    --     apply Trivia.zip_list_exists branches br_tys (ChoiceBranch.recv msg var p_br)
    --     . aesop
    --     . assumption
    --   have ⟨br_ty, H_br_ty⟩ := H_exists_br_ty
    --   have H_br_typing' := H_br_typing (ChoiceBranch.recv msg var p_br) br_ty H_br_ty
    --   cases H_br_typing'
    --   rename_i τ_br H_br_typing'
    --   exists τ_br
    --   constructor
    --   . sorry -- FIXME: prove separately
    --   . unfold AbstractTransLabel.fromConcrete
    --     simp
    --     sorry
    --     -- apply ProcTyTransition.xoffer_branch (me := MessageExch.recv msg)
    --     -- exact (List.of_mem_zip H_br_ty).2
    -- -- NOW BELOW IS THE TRICKIEST PART
    -- case offer_branch_send ex_msg' msg p_else p_br branches idx
    --                        branches_proc p_o e b H_eval H_branches H_p H_idx =>
    --     intro τ H_not_eps H_typing
    --     cases H_typing
    --     rename ProcTy => τ_else
    --     rename ProcTyJudgement _ _ _ => H_typing
    --     rename_i H_len H_br_expr H_br_typing
    --     rename List (MessageExch × ProcTy) => br_tys
    --     have H_len' : branches.length = branches_proc.length := by
    --       aesop
    --     have H_len'' : branches.length + 1 = br_tys.length := by
    --       rewrite [← H_len]
    --       rewrite [List.length_insertIdx_of_le_length]
    --       . rfl
    --       . apply Nat.lt_add_one_iff.mp
    --         exact H_idx
    --     have H_br_ty : ∃ br_ty, (ChoiceBranch.send msg e p_br, br_ty) ∈ (List.zip $ branches.insertIdx idx (ChoiceBranch.send msg e p_br)) br_tys := by
    --       apply Trivia.zip_list_exists
    --       . rewrite [H_len]
    --         simp
    --       . apply Trivia.list_insert_idx
    --         apply Nat.lt_add_one_iff.mp
    --         exact H_idx
    --     have ⟨br_ty, H_br_ty⟩ := H_br_ty
    --     have H_br_ty_1 : br_ty.1 = MessageExch.send msg := by sorry -- TRIVIAL
    --     exists (br_ty.2::(br_tys.map branch_to_xoffer_ty).eraseIdx idx).foldl (fun acc e => ProcTy.par acc e) ProcTy.skip
    --     constructor
    --     . rewrite [H_p]
    --       rewrite [H_branches]
    --       apply par_list_ty
    --       . simp
    --         rewrite [List.length_eraseIdx_of_lt]
    --         . simp
    --           rewrite [← H_len'']
    --           rfl
    --         . simp
    --           rewrite [← H_len'']
    --           exact H_idx
    --       . intro p τ H_x
    --         simp at H_x
    --         cases H_x
    --         . rename_i H_x
    --           rewrite [H_x.1]
    --           rewrite [H_x.2]
    --           sorry -- TRIVIAL
    --         . sorry -- FIXME: prove separately about membership with insertIdx
    --           -- can use List.subset_insertIdx, List.eraseIdx_subset
    --     . have H_br_tys : br_tys = (br_tys.eraseIdx idx).insertIdx idx br_ty := by
    --         sorry -- trivial
    --       rewrite [H_br_tys]
    --       have H_br_ty' : br_ty = (br_ty.1, br_ty.2) := by rfl
    --       rewrite [H_br_ty']
    --       rewrite [H_br_ty_1]
    --       unfold AbstractTransLabel.fromConcrete
    --       simp
    --       have H_msg : msg = (MessageExch.send msg).messageId := by rfl
    --       have H_msg_dir : MessageDir.send = (MessageExch.send msg).direction := by rfl
    --       conv in AbstractTransLabel.message _ _ =>
    --         rewrite [H_msg, H_msg_dir]
    --       apply ProcTyTransition.offer_branch (me := MessageExch.send msg) (ty := br_ty.2) (ex_msg := ex_msg') (idx := idx) <;> try trivial
    --       . simp
    --         sorry -- trivial
    --       . have H_br_tys_len : (br_tys.eraseIdx idx).length = br_tys.length - 1 := by
    --           sorry -- trivial
    --         rewrite [H_br_tys_len]
    --         rewrite [← H_len'']
    --         simp
    --         exact H_idx
    -- case offer_branch_recv ex_msg' var p_br p_else branches idx msg b branches' p' H_branches H_p H_idx =>
    --   -- largely the same as for send
    --   intro τ H_not_eps H_typing
    --   cases H_typing
    --   rename ProcTy => τ_else
    --   rename ProcTyJudgement _ _ _ => H_typing
    --   rename_i H_len H_br_expr H_br_typing
    --   rename List (MessageExch × ProcTy) => br_tys
    --   have H_len' : branches.length = branches'.length := by
    --     aesop
    --   have H_len'' : branches.length + 1 = br_tys.length := by
    --     rewrite [← H_len]
    --     rewrite [List.length_insertIdx_of_le_length]
    --     . rfl
    --     . apply Nat.lt_add_one_iff.mp
    --       exact H_idx
    --   have H_br_ty : ∃ br_ty, (ChoiceBranch.recv msg var p_br, br_ty) ∈ (List.zip $ branches.insertIdx idx (ChoiceBranch.recv msg var p_br)) br_tys := by
    --     apply Trivia.zip_list_exists
    --     . rewrite [H_len]
    --       simp
    --     . apply Trivia.list_insert_idx
    --       apply Nat.lt_add_one_iff.mp
    --       exact H_idx
    --   have ⟨br_ty, H_br_ty⟩ := H_br_ty
    --   have H_br_ty_1 : br_ty.1 = MessageExch.recv msg := by sorry -- TRIVIAL
    --   exists (br_ty.2::(br_tys.map branch_to_xoffer_ty).eraseIdx idx).foldl (fun acc e => ProcTy.par acc e) ProcTy.skip
    --   constructor
    --   . rewrite [H_p]
    --     rewrite [H_branches]
    --     apply par_list_ty
    --     . simp
    --       rewrite [List.length_eraseIdx_of_lt]
    --       . simp
    --         rewrite [← H_len'']
    --         rfl
    --       . simp
    --         rewrite [← H_len'']
    --         exact H_idx
    --     . intro p τ H_x
    --       simp at H_x
    --       cases H_x
    --       . rename_i H_x
    --         rewrite [H_x.1]
    --         rewrite [H_x.2]
    --         sorry -- TRIVIAL
    --       . sorry -- FIXME: prove separately about membership with insertIdx
    --         -- can use List.subset_insertIdx, List.eraseIdx_subset
    --   . have H_br_tys : br_tys = (br_tys.eraseIdx idx).insertIdx idx br_ty := by
    --       sorry -- trivial
    --     rewrite [H_br_tys]
    --     have H_br_ty' : br_ty = (br_ty.1, br_ty.2) := by rfl
    --     rewrite [H_br_ty']
    --     rewrite [H_br_ty_1]
    --     unfold AbstractTransLabel.fromConcrete
    --     simp
    --     have H_msg : msg = (MessageExch.recv msg).messageId := by rfl
    --     have H_msg_dir : MessageDir.recv = (MessageExch.recv msg).direction := by rfl
    --     conv in AbstractTransLabel.message _ _ =>
    --       rewrite [H_msg, H_msg_dir]
    --     apply ProcTyTransition.offer_branch (me := MessageExch.recv msg) (ty := br_ty.2) (ex_msg := ex_msg') (idx := idx) <;> try trivial
    --     . simp
    --       sorry -- trivial
    --     . have H_br_tys_len : (br_tys.eraseIdx idx).length = br_tys.length - 1 := by
    --         sorry -- trivial
    --       rewrite [H_br_tys_len]
    --       rewrite [← H_len'']
    --       simp
    --       exact H_idx
    -- all_goals sorry

-- lemma deadend_preserved_by_typing :
--   ∀ (p : Semantics.ProcComp) (τ τ' : ProcTyComposition) (α : Action),
--     CompositionTyJudgement p τ →
--     ProcTyCompTransition τ α τ' →
--     ∃ (p' : Semantics.ProcComp) (α' : Action),
--       Semantics.CompReduces p α' p' := by

--     intro p τ τ' l H_typing
--     revert p τ' l
--     induction τ using ProcTy.ind
--     all_goals sorry
    -- case H_skip =>
    --   intro p τ' l H_typing ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --   cases H_typing
    --   cases H_trans
    -- case H_cycle =>
    --   intro p τ' l H_typing ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --   cases H_typing
    --   exists Proc.skip, TransLabel.tock
    --   unfold Semantics.CompReduces
    --   exists ∅
    --   constructor
    --   . apply Semantics.Reduces.tock
    --   . aesop
    -- case H_dollar pid =>
    --   intro p τ' l H_typing ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --   cases H_typing
    --   exists Proc.skip, TransLabel.dollar pid
    -- case H_message msg =>
    --   intro p τ' l H_typing ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --   cases H_typing
    --   rename MessageId => msg
    --   rename Proc => p
    --   rename Expr => e
    --   cases H_trans
    --   unfold AbstractTransLabel.isComplete at H_complete
    --   simp at H_complete
    -- case H_seq τ₁ τ₂ H_ih₁ H_ih₂ =>
    --   intro p τ' l H_typing ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --   cases H_typing
    --   . rename_i msg x p H_typing
    --     cases H_trans
    --     rename_i τ₁' H_trans
    --     cases H_trans
    --     cases H_complete
    --   . rename_i p₁ p₂ H_typing₁ H_typing₂
    --     cases H_trans
    --     . rename_i τ₁' H_trans
    --       have ⟨p₁', α₁, ⟨ex_msg₁, H_red₁⟩⟩ := H_ih₁ p₁ τ₁' l H_typing₁ ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
    --       unfold Semantics.CompReduces
    --       exists Proc.seq p₁' p₂, α₁, ex_msg₁
    --       constructor
    --       . apply Semantics.Reduces.seq_step
    --         exact H_red₁.1
    --       . exact H_red₁.2
    --     . cases H_typing₁
    --       unfold Semantics.CompReduces
    --       exists p₂, TransLabel.ε, ∅
    --       constructor
    --       . apply Semantics.Reduces.seq_skip
    --       . trivial

    -- all_goals sorry
