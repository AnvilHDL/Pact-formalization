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

-- TODO: the most important proof
/-
  Issues:
  - Need to ensure that if process is a deadend, then type is also a deadend (i.e., no deadend is removed by typing)
    - Equivalently, if type is not a deadend, then process is also not a deadend
  - Maybe need to ignore ε transitions
-/
lemma type_emulates_proc : ∀ (p p' : Semantics.ProcComp)
                             (τ : ProcTyComposition) (c_lbl : TransLabel) (ex_msg : Finset (MessageId × MessageDir)),
    CompositionTyJudgement p τ →
    Semantics.Reduces ex_msg p c_lbl p' →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyTransition ex_msg τ (AbstractTransLabel.fromConcrete c_lbl) τ' := by

    intro p p' τ c_lbl ex_msg H_typing H_reduces
    revert H_typing τ
    induction H_reduces -- using Semantics.Reduces.ind
    case tock ex_msg' =>
      intro τ H_typing
      cases H_typing
      exists ProcTy.skip
      constructor
      . unfold CompositionTyJudgement
        apply ProcTyJudgement.skip
      . unfold AbstractTransLabel.fromConcrete
        simp
        constructor
    case seq_skip =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        cases H_typing₁
        apply ProcTyTransition.seq_done
    case seq_step =>
      intro τ H_typing
      rename_i H_ind
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      rename TransLabel => α
      rename Finset _ => ex_msg'
      rename_i H_red
      have H_ind' := H_ind τ₁ H_typing₁
      have ⟨τ₁', H_ind'⟩ := H_ind'
      exists ProcTy.seq τ₁' τ₂
      constructor
      . apply ProcTyJudgement.seq
        . exact H_ind'.1
        . exact H_typing₂
      . apply ProcTyTransition.seq_step
        exact H_ind'.2
    case send =>
      intro τ H_typing
      exists ProcTy.skip
      constructor
      . apply ProcTyJudgement.skip
      . unfold AbstractTransLabel.fromConcrete
        simp
        cases H_typing
        apply ProcTyTransition.message_send
    case recv =>
      intro τ H_typing
      cases H_typing
      rename_i msg x p b τ' H_typing_body
      exists ProcTy.seq ProcTy.skip τ'
      constructor
      . sorry -- FIXME: prove separately
      . sorry-- FIXME: something subtle is wrong in the definition
    case par_skip_left =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        cases H_typing₁
        apply ProcTyTransition.par_skip_left
    case par_skip_right =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      exists τ₁
      constructor
      . exact H_typing₁
      . unfold AbstractTransLabel.fromConcrete
        simp
        cases H_typing₂
        apply ProcTyTransition.par_skip_right
    case par_left =>
      intro τ H_typing
      rename_i H_red₁ H_ind
      rename Finset _ => ex_msg'
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₁', H_ind'⟩ := H_ind τ₁ H_typing₁
      exists ProcTy.par τ₁' τ₂
      constructor
      . apply ProcTyJudgement.par
        . exact H_ind'.1
        . exact H_typing₂
      . apply ProcTyTransition.par_left
        all_goals sorry
    case par_right => -- symmetrical
      intro τ H_typing
      rename_i H_red₂ H_ind
      rename Finset _ => ex_msg'
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₂', H_ind'⟩ := H_ind τ₂ H_typing₂
      exists ProcTy.par τ₁ τ₂'
      constructor
      . apply ProcTyJudgement.par
        . exact H_typing₁
        . exact H_ind'.1
      . apply ProcTyTransition.par_right
        all_goals sorry
    case par_tock =>
      intro τ H_typing
      rename_i ex_msg' p₁ p₂ p₁' p₂' H_red₁ H_red₂ H_ind₁ H_ind₂
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₁', H_ind₁'⟩ := H_ind₁ τ₁ H_typing₁
      have ⟨τ₂', H_ind₂'⟩ := H_ind₂ τ₂ H_typing₂
      exists ProcTy.par τ₁' τ₂'
      constructor
      . apply ProcTyJudgement.par
        . exact H_ind₁'.1
        . exact H_ind₂'.1
      . apply ProcTyTransition.par_tock
        . apply procty_trans_preserved_under_extended_exmsg ex_msg'
          . trivial
          . exact H_ind₁'.2
        . apply procty_trans_preserved_under_extended_exmsg ex_msg'
          . trivial
          . exact H_ind₂'.2
    case recur_unfold =>
      intro τ H_typing
      cases H_typing
      rename String => X
      rename ProcTy => τ
      exists τ.replaceVar X (ProcTy.recur X τ)
      unfold CompositionTyJudgement
      constructor
      . rename Proc => p_body
        apply recursion_unfolding_preserved p_body τ
        assumption
      . apply ProcTyTransition.recur_unfold
    case ifunfair_true =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₁
      constructor
      . exact H_typing₁
      . apply ProcTyTransition.choice_left
    case ifunfair_false =>
      -- symmetrical
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . apply ProcTyTransition.choice_right
    case iffair_true =>
      intro τ H_typing
      cases H_typing
      rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₁
      constructor
      . exact H_typing₁
      . apply ProcTyTransition.choice_fair_left
    case iffair_false =>
      -- symmetrical
      intro τ H_typing
      cases H_typing
      rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . apply ProcTyTransition.choice_fair_right
    case par_message =>
      intro τ H_typing
      rename_i H_sub₁ H_sub₂ H_nim₁ H_nim₂ H_red₁ H_red₂ H_ih₁ H_ih₂
      rename MessageId => msg
      rename_i ex_msg' ex_msg₁ ex_msg₂ dir dir' b p₁ p₁' p₂ p₂' H_dual
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₁', H_ih₁'⟩ := H_ih₁ τ₁ H_typing₁
      have ⟨τ₂', H_ih₂'⟩ := H_ih₂ τ₂ H_typing₂
      exists ProcTy.par τ₁' τ₂'
      constructor
      . apply ProcTyJudgement.par
        . exact H_ih₁'.1
        . exact H_ih₂'.1
      . apply ProcTyTransition.par_message (ex_msg₁ := ex_msg₁) (ex_msg₂ := ex_msg₂) <;> try trivial
        . intro mx H_mx
          apply (non_instant_msg_preservation p₁ τ₁ H_typing₁ mx).mp
          apply H_nim₁
          assumption
        . intro mx H_mx
          apply (non_instant_msg_preservation p₂ τ₂ H_typing₂ mx).mp
          apply H_nim₂
          assumption
        . exact H_ih₁'.2
        . exact H_ih₂'.2
    case xoffer_branch_else ex_msg' p_else branches H_mx =>
      intro τ H_typing
      cases H_typing
      rename ProcTy => τ_else
      exists τ_else
      constructor
      . assumption
      . apply ProcTyTransition.xoffer_else
        sorry -- FIXME: prove separately
    case offer_branch_else ex_msg' p_else branches H_mx =>
      -- similar to above
      intro τ H_typing
      cases H_typing
      rename ProcTy => τ_else
      exists τ_else
      constructor
      . assumption
      . apply ProcTyTransition.offer_else
        sorry -- FIXME: prove separately
    case xoffer_branch_send ex_msg' msg e p_else p_send br b br_send H_eval =>
      intro τ H_typing
      cases H_typing
      rename ProcTy => τ_else
      rename ProcTyJudgement _ _ _ => H_typing
      rename_i H_len H_br_expr H_br_typing
      rename List (MessageExch × ProcTy) => br_tys
      have H_exists_br_ty : ∃ br_ty, (ChoiceBranch.send msg e p_send, br_ty) ∈ List.zip br br_tys := by
        apply Trivia.zip_list_exists br br_tys (ChoiceBranch.send msg e p_send)
        . aesop
        . assumption
      have ⟨br_ty, H_br_ty⟩ := H_exists_br_ty
      have H_br_typing' := H_br_typing (ChoiceBranch.send msg e p_send) br_ty H_br_ty
      cases H_br_typing'
      rename_i τ_br H_expr_ty H_br_typing'
      exists τ_br
      constructor
      . exact H_br_typing'
      . unfold AbstractTransLabel.fromConcrete
        simp
        apply ProcTyTransition.xoffer_branch (me := MessageExch.send msg)
        exact (List.of_mem_zip H_br_ty).2
    case xoffer_branch_recv ex_msg' var p_else branches msg p_br b H_br =>
      intro τ H_typing
      cases H_typing
      rename ProcTy => τ_else
      rename ProcTyJudgement _ _ _ => H_typing
      rename_i H_len H_br_expr H_br_typing
      rename List (MessageExch × ProcTy) => br_tys
      have H_exists_br_ty : ∃ br_ty, (ChoiceBranch.recv msg var p_br, br_ty) ∈ List.zip branches br_tys := by
        apply Trivia.zip_list_exists branches br_tys (ChoiceBranch.recv msg var p_br)
        . aesop
        . assumption
      have ⟨br_ty, H_br_ty⟩ := H_exists_br_ty
      have H_br_typing' := H_br_typing (ChoiceBranch.recv msg var p_br) br_ty H_br_ty
      cases H_br_typing'
      rename_i τ_br H_br_typing'
      exists τ_br
      constructor
      . sorry -- FIXME: prove separately
      . unfold AbstractTransLabel.fromConcrete
        simp
        sorry
        -- apply ProcTyTransition.xoffer_branch (me := MessageExch.recv msg)
        -- exact (List.of_mem_zip H_br_ty).2
    -- NOW BELOW IS THE TRICKIEST PART
    case offer_branch_send ex_msg' msg p_else p_br branches idx
                           branches_proc p_o e b H_eval H_branches H_p H_idx =>
        intro τ H_typing
        cases H_typing
        rename ProcTy => τ_else
        rename ProcTyJudgement _ _ _ => H_typing
        rename_i H_len H_br_expr H_br_typing
        rename List (MessageExch × ProcTy) => br_tys
        have H_len' : branches.length = branches_proc.length := by
          aesop
        have H_len'' : branches.length + 1 = br_tys.length := by
          rewrite [← H_len]
          rewrite [List.length_insertIdx_of_le_length]
          . rfl
          . apply Nat.lt_add_one_iff.mp
            exact H_idx
        have H_br_ty : ∃ br_ty, (ChoiceBranch.send msg e p_br, br_ty) ∈ (List.zip $ branches.insertIdx idx (ChoiceBranch.send msg e p_br)) br_tys := by
          apply Trivia.zip_list_exists
          . rewrite [H_len]
            simp
          . apply Trivia.list_insert_idx
            apply Nat.lt_add_one_iff.mp
            exact H_idx
        have ⟨br_ty, H_br_ty⟩ := H_br_ty
        have H_br_ty_1 : br_ty.1 = MessageExch.send msg := by sorry -- TRIVIAL
        exists (br_ty.2::(br_tys.map branch_to_xoffer_ty).eraseIdx idx).foldl (fun acc e => ProcTy.par acc e) ProcTy.skip
        constructor
        . rewrite [H_p]
          rewrite [H_branches]
          apply par_list_ty
          . simp
            rewrite [List.length_eraseIdx_of_lt]
            . simp
              rewrite [← H_len'']
              rfl
            . simp
              rewrite [← H_len'']
              exact H_idx
          . intro p τ H_x
            simp at H_x
            cases H_x
            . rename_i H_x
              rewrite [H_x.1]
              rewrite [H_x.2]
              sorry -- TRIVIAL
            . sorry -- FIXME: prove separately about membership with insertIdx
              -- can use List.subset_insertIdx, List.eraseIdx_subset
        . have H_br_tys : br_tys = (br_tys.eraseIdx idx).insertIdx idx br_ty := by
            sorry -- trivial
          rewrite [H_br_tys]
          have H_br_ty' : br_ty = (br_ty.1, br_ty.2) := by rfl
          rewrite [H_br_ty']
          rewrite [H_br_ty_1]
          unfold AbstractTransLabel.fromConcrete
          simp
          have H_msg : msg = (MessageExch.send msg).messageId := by rfl
          have H_msg_dir : MessageDir.send = (MessageExch.send msg).direction := by rfl
          conv in AbstractTransLabel.message _ _ =>
            rewrite [H_msg, H_msg_dir]
          apply ProcTyTransition.offer_branch (me := MessageExch.send msg) (ty := br_ty.2) (ex_msg := ex_msg') (idx := idx) <;> try trivial
          . simp
            sorry -- trivial
          . have H_br_tys_len : (br_tys.eraseIdx idx).length = br_tys.length - 1 := by
              sorry -- trivial
            rewrite [H_br_tys_len]
            rewrite [← H_len'']
            simp
            exact H_idx
    case offer_branch_recv ex_msg' var p_br p_else branches idx msg b branches' p' H_branches H_p H_idx =>
      -- largely the same as for send
      intro τ H_typing
      cases H_typing
      rename ProcTy => τ_else
      rename ProcTyJudgement _ _ _ => H_typing
      rename_i H_len H_br_expr H_br_typing
      rename List (MessageExch × ProcTy) => br_tys
      have H_len' : branches.length = branches'.length := by
        aesop
      have H_len'' : branches.length + 1 = br_tys.length := by
        rewrite [← H_len]
        rewrite [List.length_insertIdx_of_le_length]
        . rfl
        . apply Nat.lt_add_one_iff.mp
          exact H_idx
      have H_br_ty : ∃ br_ty, (ChoiceBranch.recv msg var p_br, br_ty) ∈ (List.zip $ branches.insertIdx idx (ChoiceBranch.recv msg var p_br)) br_tys := by
        apply Trivia.zip_list_exists
        . rewrite [H_len]
          simp
        . apply Trivia.list_insert_idx
          apply Nat.lt_add_one_iff.mp
          exact H_idx
      have ⟨br_ty, H_br_ty⟩ := H_br_ty
      have H_br_ty_1 : br_ty.1 = MessageExch.recv msg := by sorry -- TRIVIAL
      exists (br_ty.2::(br_tys.map branch_to_xoffer_ty).eraseIdx idx).foldl (fun acc e => ProcTy.par acc e) ProcTy.skip
      constructor
      . rewrite [H_p]
        rewrite [H_branches]
        apply par_list_ty
        . simp
          rewrite [List.length_eraseIdx_of_lt]
          . simp
            rewrite [← H_len'']
            rfl
          . simp
            rewrite [← H_len'']
            exact H_idx
        . intro p τ H_x
          simp at H_x
          cases H_x
          . rename_i H_x
            rewrite [H_x.1]
            rewrite [H_x.2]
            sorry -- TRIVIAL
          . sorry -- FIXME: prove separately about membership with insertIdx
            -- can use List.subset_insertIdx, List.eraseIdx_subset
      . have H_br_tys : br_tys = (br_tys.eraseIdx idx).insertIdx idx br_ty := by
          sorry -- trivial
        rewrite [H_br_tys]
        have H_br_ty' : br_ty = (br_ty.1, br_ty.2) := by rfl
        rewrite [H_br_ty']
        rewrite [H_br_ty_1]
        unfold AbstractTransLabel.fromConcrete
        simp
        have H_msg : msg = (MessageExch.recv msg).messageId := by rfl
        have H_msg_dir : MessageDir.recv = (MessageExch.recv msg).direction := by rfl
        conv in AbstractTransLabel.message _ _ =>
          rewrite [H_msg, H_msg_dir]
        apply ProcTyTransition.offer_branch (me := MessageExch.recv msg) (ty := br_ty.2) (ex_msg := ex_msg') (idx := idx) <;> try trivial
        . simp
          sorry -- trivial
        . have H_br_tys_len : (br_tys.eraseIdx idx).length = br_tys.length - 1 := by
            sorry -- trivial
          rewrite [H_br_tys_len]
          rewrite [← H_len'']
          simp
          exact H_idx
    all_goals sorry

lemma deadend_preserved_by_typing :
  ∀ (p : Semantics.ProcComp) (τ τ' : ProcTyComposition) (α : Action),
    CompositionTyJudgement p τ →
    ProcTyCompTransition τ α τ' →
    ∃ (p' : Semantics.ProcComp) (α' : Action),
      Semantics.CompReduces p α' p' := by

    intro p τ τ' l H_typing
    revert p τ' l
    induction τ using ProcTy.ind
    all_goals sorry
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

    all_goals sorry
