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
import Anvilpp.Subtyping
import Anvilpp.Trans

lemma type_preserves_deadends_single : ∀ (p : Proc) (τ τ' : ProcTy) (lbl : AbstractTransLabel),
    CompositionTyJudgement p τ →
    lbl ≠ AbstractTransLabel.ε →
    ProcTyTransition τ lbl τ' →
    ∃ p' lbl',
      AbstractTransLabel.Related lbl lbl' ∧
        Semantics.IncompReduces p lbl' p' := by

  intro p τ τ' lbl H_typing H_not_ε H_transition
  revert τ' lbl
  unfold CompositionTyJudgement at H_typing
  generalize H_ctx : ProcTyContext.empty = ctx at H_typing
  induction H_typing <;> (intro τ' lbl H_not_ε H_trans; try (cases H_trans; done))
  case cycle ctx' =>
    cases H_trans
    exists Proc.skip, TransLabel.ac Action.tock
    constructor
    . simp [AbstractTransLabel.Related]
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
            apply AbstractTransLabel.Related.is_ex_preserved
            exact H_lbl'
          rewrite [← H_lbl_nonex]
          exact H_not_ex
        . by_contra H_tock
          rewrite [H_tock] at H_lbl'
          simp [AbstractTransLabel.Related] at H_lbl'
          have H' : lbl = AbstractTransLabel.ac Action.tock := by
            cases lbl <;> (simp at H_lbl'; try contradiction)
            rewrite [H_lbl']
            rfl
          contradiction
        . exact H_reduces
    case par_right τ₂' H_not_tock H_not_ex H_trans₂ =>
      have H_p₂' := H_ind₂ H_ctx τ₂' lbl H_not_ε H_trans₂
      have ⟨p₂', lbl', H_lbl', H_reduces⟩ := H_p₂'
      exists (Proc.par p₁ p₂'), lbl'
      constructor
      . exact H_lbl'
      . apply Semantics.IncompReduces.par_non_ex_right
        . have H_lbl_nonex : lbl.isEx ↔ lbl'.isEx := by
            apply AbstractTransLabel.Related.is_ex_preserved
            exact H_lbl'
          rewrite [← H_lbl_nonex]
          exact H_not_ex
        . by_contra H_tock
          rewrite [H_tock] at H_lbl'
          simp [AbstractTransLabel.Related] at H_lbl'
          have H' : lbl = AbstractTransLabel.ac Action.tock := by
            cases lbl <;> (simp at H_lbl'; try contradiction)
            rewrite [H_lbl']
            rfl
          contradiction
        . exact H_reduces
    case par_left_ex ex_msg τ₁' H_trans H_m =>
      have H_p₁' := H_ind₁ H_ctx τ₁' (AbstractTransLabel.ex ex_msg) H_not_ε H_trans
      have ⟨p₁', lbl', H_lbl', H_reduces⟩ := H_p₁'
      exists (Proc.par p₁' p₂), lbl'
      constructor
      . exact H_lbl'
      . have H_m' : ∀ mx ∈ ex_msg, Semantics.NonInstantMessage ∅ ∅ p₂ mx := by
          intro mx H_mx
          apply non_instant_msg_preservation (p := p₂) (τ := τ₂) (ctx := ctx')
          . exact H_typing₂
          . exact H_m mx H_mx
        have H_lbl_ex' : lbl' = TransLabel.ex ex_msg := by
          cases lbl' <;> (simp [AbstractTransLabel.Related] at H_lbl'; try contradiction)
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
          apply non_instant_msg_preservation (p := p₁) (τ := τ₁) (ctx := ctx')
          . exact H_typing₁
          . exact H_m mx H_mx
        have H_lbl_ex' : lbl' = TransLabel.ex ex_msg := by
          cases lbl' <;> (simp [AbstractTransLabel.Related] at H_lbl'; try contradiction)
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
            cases lbl₁' <;> (simp [AbstractTransLabel.Related] at H_lbl₁'; try contradiction)
            rewrite [H_lbl₁']
            rfl
          rewrite [← H_lbl₁_tock]
          exact H_reduces₁
        . have H_lbl₂_tock : lbl₂' = TransLabel.ac Action.tock := by
            cases lbl₂' <;> (simp [AbstractTransLabel.Related] at H_lbl₂'; try contradiction)
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
          cases lbl₁' <;> (simp [AbstractTransLabel.Related] at H_lbl₁'; try contradiction)
          rename_i v₁
          exists v₁
          rewrite [H_lbl₁'.1]
          rewrite [H_lbl₁'.2]
          rfl
        have H_lbl₂_msg : ∃ v₂, lbl₂' = TransLabel.message msg d₂ v₂ := by
          cases lbl₂' <;> (simp [AbstractTransLabel.Related] at H_lbl₂'; try contradiction)
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
  case recur =>
    cases H_trans
    simp at H_not_ε
  case message_send ctx' msg e H_typing =>
    cases H_trans
    rewrite [← H_ctx] at H_typing
    unfold ProcTyContext.empty at H_typing
    simp at H_typing
    have H_e_eval : ∃ v, e ↓ v := by
      apply welltyped_expr_evaluates_to_something
      exact H_typing
    have ⟨v, H_eval⟩ := H_e_eval
    exists Proc.skip, (TransLabel.message msg MessageDir.send v)
    constructor
    . simp [AbstractTransLabel.Related]
    . exists Proc.send msg e
      constructor <;> aesop
  case message_recv ctx' msg x p' τ' H_typing H_ind =>
    cases H_trans
    rename_i τ₁' H_trans
    cases H_trans
    exists Proc.skip.seq (Semantics.procExprReplace p' x true), (TransLabel.message msg MessageDir.recv true)
    constructor
    . simp [AbstractTransLabel.Related]
    . exists Proc.recv msg x p'
      constructor <;> aesop
  case seq ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_trans
    case seq_step τ₁' H_trans =>
      have H_p₁' := H_ind₁ H_ctx τ₁' lbl H_not_ε H_trans
      have ⟨p₁', lbl', H_lbl', H_reduces⟩ := H_p₁'
      exists (Proc.seq p₁' p₂), lbl'
      constructor
      . exact H_lbl'
      . apply Semantics.IncompReduces.seq_reduces
        exact H_reduces
    case seq_done =>
      simp at H_not_ε
  case choice ctx' e p₁ p₂ τ₁ τ₂ H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_trans <;> simp at H_not_ε
  case choice_fair ctx' e p₁ p₂ τ₁ τ₂ b H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    have H_e_eval : ∃ v, e ↓ v := by
      apply welltyped_expr_evaluates_to_something
      rewrite [← H_ctx] at H_e_typing
      unfold ProcTyContext.empty at H_e_typing
      simp at H_e_typing
      exact H_e_typing
    obtain ⟨v, H_eval⟩ := H_e_eval
    cases H_trans
    case choice_fair_left =>
      cases v
      case true =>
        exact ⟨p₁, TransLabel.ac (Action.branchTrue b),
               by simp [AbstractTransLabel.Related],
               Proc.iffair b e p₁ p₂,
               Semantics.Reduces.iffair_true b e p₁ p₂ true H_eval rfl,
               Semantics.CompElim.refl _⟩
      case false =>
        exact ⟨p₂, TransLabel.ac (Action.branchFalse b),
               by simp [AbstractTransLabel.Related],
               Proc.iffair b e p₁ p₂,
               Semantics.Reduces.iffair_false b e p₁ p₂ false H_eval rfl,
               Semantics.CompElim.refl _⟩
    case choice_fair_right =>
      cases v
      case false =>
        exact ⟨p₂, TransLabel.ac (Action.branchFalse b),
               by simp [AbstractTransLabel.Related],
               Proc.iffair b e p₁ p₂,
               Semantics.Reduces.iffair_false b e p₁ p₂ false H_eval rfl,
               Semantics.CompElim.refl _⟩
      case true =>
        exact ⟨p₁, TransLabel.ac (Action.branchTrue b),
               by simp [AbstractTransLabel.Related],
               Proc.iffair b e p₁ p₂,
               Semantics.Reduces.iffair_true b e p₁ p₂ true H_eval rfl,
               Semantics.CompElim.refl _⟩
  case xoffer ctx' p_else branches τ_else branch_tys
      H_len H_send_expr H_send_ty H_send_typing H_recv_ty H_recv_typing H_else_typing
      H_ind_send H_ind_recv H_ind_else =>
    have mem_left_of_zip : ∀ {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β},
        (x, y) ∈ l₁.zip l₂ → x ∈ l₁ := by
      intro α β x y l₁
      induction l₁ with
      | nil =>
        intro l₂ h
        simp at h
      | cons hd tl ih =>
        intro l₂ h
        cases l₂ with
        | nil => simp at h
        | cons hd₂ tl₂ =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl rfl
          · exact Or.inr (ih h)
    have mem_right_of_zip : ∀ {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β},
        (x, y) ∈ l₁.zip l₂ → y ∈ l₂ := by
      intro α β x y l₁
      induction l₁ with
      | nil =>
        intro l₂ h
        simp at h
      | cons hd tl ih =>
        intro l₂ h
        cases l₂ with
        | nil => simp at h
        | cons hd₂ tl₂ =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl rfl
          · exact Or.inr (ih h)
    cases H_trans
    case xoffer_else =>
      rename_i ex_msg H_ex
      exists p_else, (TransLabel.ex ex_msg)
      constructor
      · simp [AbstractTransLabel.Related]
      · refine ⟨Proc.xoffer p_else branches, ?_, Semantics.CompElim.refl _⟩
        apply Semantics.Reduces.xoffer_branch_else
        intro mx H_mx
        simp only [List.mem_map] at H_mx
        obtain ⟨br, H_br_mem, H_mx_eq⟩ := H_mx
        have H_le : branches.length ≤ branch_tys.length := by
          simp [H_len]
        obtain ⟨br_ty, H_zip_right⟩ := Trivia.zip_list_exists branches branch_tys br H_le H_br_mem
        have H_zip : (br, br_ty) ∈ branches.zip branch_tys := H_zip_right
        have H_brty_mem : br_ty ∈ branch_tys := mem_right_of_zip H_zip
        cases br with
        | send msg e p_br =>
          have H_me : br_ty.1 = MessageExch.send msg :=
            H_send_ty msg e p_br br_ty H_zip
          have H_ex' : (br_ty.1.messageId, br_ty.1.direction.invert) ∈ ex_msg :=
            H_ex br_ty.1 br_ty.2 H_brty_mem
          subst mx
          simpa [ChoiceBranch.getMessage, H_me] using H_ex'
        | recv msg var p_br =>
          have H_me : br_ty.1 = MessageExch.recv msg :=
            H_recv_ty msg var p_br br_ty H_zip
          have H_ex' : (br_ty.1.messageId, br_ty.1.direction.invert) ∈ ex_msg :=
            H_ex br_ty.1 br_ty.2 H_brty_mem
          subst mx
          simpa [ChoiceBranch.getMessage, H_me] using H_ex'
    case xoffer_branch =>
      rename_i me H_mem
      have H_le : branch_tys.length ≤ branches.length := by
        simp [H_len]
      obtain ⟨br, H_zip_r⟩ := Trivia.zip_list_exists branch_tys branches (me, τ') H_le H_mem
      have H_zip : (br, (me, τ')) ∈ branches.zip branch_tys :=
        Trivia.zip_flip branch_tys branches (me, τ') br H_zip_r
      cases br with
      | send msg e p_br =>
        have H_me : me = MessageExch.send msg := by
          simpa using H_send_ty msg e p_br (me, τ') H_zip
        have H_expr : ExprTyJudgement ∅ e := by
          have H_expr' := H_send_expr msg e p_br (me, τ') H_zip
          rw [← H_ctx] at H_expr'
          simpa [ProcTyContext.empty] using H_expr'
        obtain ⟨b, H_eval⟩ := welltyped_expr_evaluates_to_something e H_expr
        exists p_br, (TransLabel.message msg MessageDir.send b)
        constructor
        · cases H_me
          exact ⟨rfl, rfl⟩
        · refine ⟨Proc.xoffer p_else branches, ?_, Semantics.CompElim.refl _⟩
          apply Semantics.Reduces.xoffer_branch_send
          · exact mem_left_of_zip H_zip
          · exact H_eval
      | recv msg var p_br =>
        have H_me : me = MessageExch.recv msg := by
          simpa using H_recv_ty msg var p_br (me, τ') H_zip
        exists (Semantics.procExprReplace p_br var true), (TransLabel.message msg MessageDir.recv true)
        constructor
        · cases H_me
          exact ⟨rfl, rfl⟩
        · refine ⟨Proc.xoffer p_else branches, ?_, Semantics.CompElim.refl _⟩
          apply Semantics.Reduces.xoffer_branch_recv
          exact mem_left_of_zip H_zip
  case offer ctx' p_else branches τ_else branch_tys
      H_len H_send_expr H_send_ty H_send_typing H_recv_ty H_recv_typing H_else_typing
      H_ind_send H_ind_recv H_ind_else =>
    have mem_left_of_zip : ∀ {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β},
        (x, y) ∈ l₁.zip l₂ → x ∈ l₁ := by
      intro α β x y l₁
      induction l₁ with
      | nil =>
        intro l₂ h
        simp at h
      | cons hd tl ih =>
        intro l₂ h
        cases l₂ with
        | nil => simp at h
        | cons hd₂ tl₂ =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl rfl
          · exact Or.inr (ih h)
    have mem_right_of_zip : ∀ {α β : Type} {x : α} {y : β} {l₁ : List α} {l₂ : List β},
        (x, y) ∈ l₁.zip l₂ → y ∈ l₂ := by
      intro α β x y l₁
      induction l₁ with
      | nil =>
        intro l₂ h
        simp at h
      | cons hd tl ih =>
        intro l₂ h
        cases l₂ with
        | nil => simp at h
        | cons hd₂ tl₂ =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
          rcases h with ⟨rfl, rfl⟩ | h
          · exact Or.inl rfl
          · exact Or.inr (ih h)
    cases H_trans
    case offer_else =>
      rename_i ex_msg H_ex
      exists p_else, (TransLabel.ex ex_msg)
      constructor
      · simp [AbstractTransLabel.Related]
      · refine ⟨Proc.offer p_else branches, ?_, Semantics.CompElim.refl _⟩
        apply Semantics.Reduces.offer_branch_else
        intro mx H_mx
        simp only [List.mem_map] at H_mx
        obtain ⟨br, H_br_mem, H_mx_eq⟩ := H_mx
        have H_le : branches.length ≤ branch_tys.length := by
          simp [H_len]
        obtain ⟨br_ty, H_zip_right⟩ := Trivia.zip_list_exists branches branch_tys br H_le H_br_mem
        have H_zip : (br, br_ty) ∈ branches.zip branch_tys := H_zip_right
        have H_brty_mem : br_ty ∈ branch_tys := mem_right_of_zip H_zip
        cases br with
        | send msg e p_br =>
          have H_me : br_ty.1 = MessageExch.send msg :=
            H_send_ty msg e p_br br_ty H_zip
          have H_ex' : (br_ty.1.messageId, br_ty.1.direction.invert) ∈ ex_msg :=
            H_ex br_ty.1 br_ty.2 H_brty_mem
          subst mx
          simpa [ChoiceBranch.getMessage, H_me] using H_ex'
        | recv msg var p_br =>
          have H_me : br_ty.1 = MessageExch.recv msg :=
            H_recv_ty msg var p_br br_ty H_zip
          have H_ex' : (br_ty.1.messageId, br_ty.1.direction.invert) ∈ ex_msg :=
            H_ex br_ty.1 br_ty.2 H_brty_mem
          subst mx
          simpa [ChoiceBranch.getMessage, H_me] using H_ex'
    case offer_branch =>
      rename_i branch_tys idx branch_tys' me ty H_brtys_eq H_idx H_ty'_eq
      have H_me_mem : (me, ty) ∈ branch_tys.insertIdx idx (me, ty) :=
        Trivia.list_insert_idx branch_tys idx (me, ty) (Nat.lt_succ_iff.mp H_idx)
      have H_le : (branch_tys.insertIdx idx (me, ty)).length ≤ branches.length := by
        simp [H_len]
      obtain ⟨br, H_zip_r⟩ :=
        Trivia.zip_list_exists (branch_tys.insertIdx idx (me, ty)) branches (me, ty) H_le H_me_mem
      have H_zip : (br, (me, ty)) ∈ branches.zip (branch_tys.insertIdx idx (me, ty)) :=
        Trivia.zip_flip (branch_tys.insertIdx idx (me, ty)) branches (me, ty) br H_zip_r
      have H_br_mem : br ∈ branches := mem_left_of_zip H_zip
      obtain ⟨idx', H_idx'_lt, H_idx'_eq⟩ := List.mem_iff_getElem.mp H_br_mem
      have H_idx'_ins : idx' < (branches.eraseIdx idx').length + 1 := by
        have H_len_erase : (branches.eraseIdx idx').length = branches.length - 1 := by
          simpa [H_idx'_lt] using (List.length_eraseIdx (l := branches) (i := idx'))
        rw [H_len_erase]
        omega
      cases br with
      | send msg e p_br =>
        have H_me : me = MessageExch.send msg := by
          simpa using H_send_ty msg e p_br (me, ty) H_zip
        have H_expr : ExprTyJudgement ∅ e := by
          have H_expr' := H_send_expr msg e p_br (me, ty) H_zip
          rw [← H_ctx] at H_expr'
          simpa [ProcTyContext.empty] using H_expr'
        obtain ⟨b, H_eval⟩ := welltyped_expr_evaluates_to_something e H_expr
        let p_out := List.foldl (fun acc br => Proc.par acc br) Proc.skip
          (p_br :: (branches.eraseIdx idx').map ChoiceBranch.toXOffer)
        exists p_out, (TransLabel.message msg MessageDir.send b)
        constructor
        · cases H_me
          exact ⟨rfl, rfl⟩
        · refine ⟨Proc.offer p_else branches, ?_, Semantics.CompElim.refl _⟩
          have H_red : Semantics.Reduces
              (Proc.offer p_else ((branches.eraseIdx idx').insertIdx idx' (ChoiceBranch.send msg e p_br)))
              (TransLabel.message msg MessageDir.send b) p_out := by
            apply Semantics.Reduces.offer_branch_send
            · exact H_eval
            · rfl
            · rfl
            · exact H_idx'_ins
          have H_ins : (branches.eraseIdx idx').insertIdx idx' (ChoiceBranch.send msg e p_br) = branches := by
            simpa [H_idx'_eq] using (List.insertIdx_eraseIdx_getElem (l := branches) (n := idx') H_idx'_lt)
          simpa [H_ins] using H_red
      | recv msg var p_br =>
        have H_me : me = MessageExch.recv msg := by
          simpa using H_recv_ty msg var p_br (me, ty) H_zip
        let p_out := List.foldl (fun acc br => Proc.par acc br) Proc.skip
          ((Semantics.procExprReplace p_br var true) :: (branches.eraseIdx idx').map ChoiceBranch.toXOffer)
        exists p_out, (TransLabel.message msg MessageDir.recv true)
        constructor
        · cases H_me
          exact ⟨rfl, rfl⟩
        · refine ⟨Proc.offer p_else branches, ?_, Semantics.CompElim.refl _⟩
          have H_red : Semantics.Reduces
              (Proc.offer p_else ((branches.eraseIdx idx').insertIdx idx' (ChoiceBranch.recv msg var p_br)))
              (TransLabel.message msg MessageDir.recv true) p_out := by
            apply Semantics.Reduces.offer_branch_recv
            · rfl
            · rfl
            · exact H_idx'_ins
          have H_ins : (branches.eraseIdx idx').insertIdx idx' (ChoiceBranch.recv msg var p_br) = branches := by
            simpa [H_idx'_eq] using (List.insertIdx_eraseIdx_getElem (l := branches) (n := idx') H_idx'_lt)
          simpa [H_ins] using H_red
  case subtype ctx' p' τ₁ τ₂ H_typing H_sub H_ind =>
    clear p τ ctx
    have H_τ₁'' := ProcTySub.sub_preserves_behaviour τ₁ τ₂ τ' lbl H_not_ε H_sub H_trans
    have ⟨τ₁'', ⟨H_trans', H_sub'⟩⟩ := H_τ₁''
    aesop

set_option maxHeartbeats 5000000

-- If the type can transition through ε in any way at all, at least one of
-- them can be matched by the process.
lemma type_keeps_elim : ∀ (p : Proc) (τ τ' : ProcTy),
    CompositionTyJudgement p τ →
    ProcTyGuardedClosed τ →
    ProcTyTransition τ AbstractTransLabel.ε τ' →
    ∃ τ'' p'', ProcTyTransition τ AbstractTransLabel.ε τ'' ∧
       (p'' = p ∨ Semantics.Reduces p TransLabel.ε p'') ∧ CompositionTyJudgement p'' τ'' := by

    intro p τ τ' H_typing H_guarded H_transition
    revert τ' H_guarded
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> (intro τ' H_guarded H_transition; try (cases H_transition; done))
    case par ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      cases H_transition
      case par_left τ₁' H_not_ε H_non_ex H_trans =>
        have H_p₁' := H_ind₁ H_ctx τ₁' H_guarded₁ H_trans
        have ⟨τ₁'', p₁'', H_trans₁, H_elim₁, H_typing₁'⟩ := H_p₁'
        exists (ProcTy.par τ₁'' τ₂), (Proc.par p₁'' p₂)
        constructor
        . apply ProcTyTransition.par_left
          . exact H_not_ε
          . exact H_non_ex
          . exact H_trans₁
        . constructor
          . cases H_elim₁
            . rename_i h
              left
              rewrite [h]
              rfl
            . aesop
          . apply ProcTyJudgement.par
            . exact H_typing₁'
            . rewrite [H_ctx]
              exact H_typing₂
      case par_right τ₂' H_not_ε H_non_ex H_trans =>
        have H_p₂' := H_ind₂ H_ctx τ₂' H_guarded₂ H_trans
        have ⟨τ₂'', p₂'', H_trans₂, H_elim₂, H_typing₂'⟩ := H_p₂'
        exists (ProcTy.par τ₁ τ₂''), (Proc.par p₁ p₂'')
        constructor
        . apply ProcTyTransition.par_right
          . exact H_not_ε
          . exact H_non_ex
          . exact H_trans₂
        . constructor
          . cases H_elim₂
            . rename_i h
              left
              rewrite [h]
              rfl
            . aesop
          . apply ProcTyJudgement.par
            . rewrite [H_ctx]
              exact H_typing₁
            . exact H_typing₂'
      case par_skip_left =>
        exists τ₂, p₂
        constructor
        . apply ProcTyTransition.par_skip_left
        . constructor
          . cases H_typing₁
            case skip =>
              right
              aesop
            case subtype τ₁ H_typing H_sub =>
              have H_τ₁_skip : τ₁ = ProcTy.skip := by
                apply ProcTySub.sub_of_skip_is_skip
                exact H_sub
              rewrite [H_τ₁_skip] at H_typing
              have H_p₁_skip : p₁ = Proc.skip := by
                apply ProcTyIncompTransition.skip_typing_implies_skip_elim_rev
                rewrite [H_ctx]
                exact H_typing
              right
              rewrite [H_p₁_skip]
              aesop
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₂
      case par_skip_right =>
        exists τ₁, p₁
        constructor
        . apply ProcTyTransition.par_skip_right
        . constructor
          . cases H_typing₂
            case skip =>
              right
              aesop
            case subtype τ₂ H_typing H_sub =>
              have H_τ₂_skip : τ₂ = ProcTy.skip := by
                apply ProcTySub.sub_of_skip_is_skip
                exact H_sub
              rewrite [H_τ₂_skip] at H_typing
              have H_p₂_skip : p₂ = Proc.skip := by
                apply ProcTyIncompTransition.skip_typing_implies_skip_elim_rev
                rewrite [H_ctx]
                exact H_typing
              right
              rewrite [H_p₂_skip]
              aesop
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₁
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
          . right
            aesop
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₁
      case false =>
        exists τ₂, p₂
        constructor
        . apply ProcTyTransition.choice_right
        . constructor
          . right
            aesop
          . unfold CompositionTyJudgement
            rewrite [H_ctx]
            exact H_typing₂
    case message_recv =>
      cases H_transition
      rename_i H_trans
      cases H_trans
    case seq ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      cases H_guarded <;> (
        rename_i H_guarded₁ H_guarded₂
        cases H_transition
        case seq_step τ₁' H_trans =>
          have H_p₁' := H_ind₁ H_ctx τ₁' H_guarded₁ H_trans
          have ⟨τ₁'', p₁'', H_trans₁, H_elim₁, H_typing₁'⟩ := H_p₁'
          exists (ProcTy.seq τ₁'' τ₂), (Proc.seq p₁'' p₂)
          constructor
          . apply ProcTyTransition.seq_step
            exact H_trans₁
          . constructor
            . cases H_elim₁
              . rename_i h
                left
                rewrite [h]
                rfl
              . aesop
            . apply ProcTyJudgement.seq
              . exact H_typing₁'
              . rewrite [H_ctx]
                exact H_typing₂
        case seq_done =>
          exists τ₂, p₂
          (
            try
              constructor
              . apply ProcTyTransition.seq_done
              . constructor
                . right
                  have H_p₁ : p₁ = Proc.skip := by
                    apply ProcTyIncompTransition.skip_typing_implies_skip_elim_rev
                    rewrite [H_ctx]
                    exact H_typing₁
                  rewrite [H_p₁]
                  aesop
                . unfold CompositionTyJudgement
                  rewrite [H_ctx]
                  exact H_typing₂
          )
      )
    case recur ctx' x p_body τ_body H_typing H_ind =>
      cases H_transition
      exists τ_body.replaceVar x (ProcTy.recur x τ_body), Semantics.procReplace p_body x (Proc.recur x p_body)
      constructor
      . aesop
      . constructor
        . right
          aesop
        . apply recursion_unfolding_preserved
          . rewrite [H_ctx]
            exact H_typing
          . apply ProcTyJudgement.recur
            rewrite [H_ctx]
            exact H_typing
    case subtype ctx' p' τ₁ τ₂ H_typing H_sub H_ind =>
      clear p τ ctx
      have H₂ := ProcTySub.sub_preserves_behaviour_elim τ₁ τ₂ τ' H_sub H_transition
      have ⟨τ₂'', ⟨H_elim₂, H_congr⟩⟩ := H₂
      have ⟨τ₁'', H_τ₁, H_sub'⟩ := H_congr
      cases H_τ₁
      case inl H =>
        exists τ₂'', p'
        constructor
        . exact H_elim₂
        . constructor
          . left
            rfl
          . apply ProcTyJudgement.subtype (τ₁ := τ₁'')
            . rewrite [H]
              rewrite [H_ctx]
              exact H_typing
            . exact H_sub'
      case inr H =>
        have H_guarded₁ : ProcTyGuardedClosed τ₁ := by
          apply ProcTySub.subtype_preserves_guarded (τ₁ := τ₁) (τ₂ := τ₂) <;> assumption
        have H_ind := H_ind H_ctx τ₁'' H_guarded₁ H
        have ⟨τ₁''', p'', H_trans₁, H_elim₁, H_typing₁'⟩ := H_ind
        have H_τ₂'' : ∃ τ₂', ProcTyTransition τ₂ AbstractTransLabel.ε τ₂' ∧ (ProcTySub τ₁ τ₂' ∨ ProcTySub τ₁''' τ₂') := by
          apply ProcTySub.subtype_refinement_elim_single
          . exact H_sub
          . exact H_trans₁
        have ⟨τ₂', ⟨H_trans₂, H_sub''⟩⟩ := H_τ₂''
        cases H_sub''
        case inl H_sub₂ =>
          exists τ₂', p'
          constructor
          . exact H_trans₂
          . constructor
            . left
              rfl
            . apply ProcTyJudgement.subtype (τ₁ := τ₁)
              . rewrite [H_ctx]
                exact H_typing
              . exact H_sub₂
        case inr H_sub₂ =>
          exists τ₂', p''
          constructor
          . exact H_trans₂
          . constructor
            . exact H_elim₁
            . apply ProcTyJudgement.subtype (τ₁ := τ₁''')
              . exact H_typing₁'
              . exact H_sub₂

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
  cases lbl' <;> simp [AbstractTransLabel.Related] at H_lbl'; try contradiction
  rename Action => α'
  have H_contra' : ∃ p' α, Semantics.CompReduces p α p' := by
    exists p'', α'
    unfold Semantics.CompReduces
    apply Semantics.IncompReduces.extend_l (p₁' := p')
    . exact H_comp_elim
    . exact H_reduces
  contradiction
