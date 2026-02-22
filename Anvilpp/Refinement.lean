import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Zip
import Mathlib.Data.List.Forall2
import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata
import Anvilpp.Helpers
import Anvilpp.Subtyping
import Anvilpp.Trans

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
    induction H_typing <;> (intro p' H_reduces; try contradiction)
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
      exists ProcTy.replaceVar τ_body pid (ProcTy.recur pid τ_body)
      constructor
      . apply recursion_unfolding_preserved
        . rewrite [H_ctx]
          exact H_typing_body
        . apply ProcTyJudgement.recur
          rewrite [H_ctx]
          exact H_typing_body
      . apply ProcTyCompElim.eps_elim (τs' := τ_body.replaceVar pid (ProcTy.recur pid τ_body))
        . apply ProcTyTransition.recur_unfold
        . apply ProcTyCompElim.refl
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
    case choice ctx' e p₁ p₂ τ₁ τ₂ H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      clear p τ ctx
      cases H_reduces
      case ifunfair_true v H_v H_eval =>
        exists τ₁
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₁
        . apply ProcTyCompElim.eps_elim (τs' := τ₁)
          . apply ProcTyTransition.choice_left
          . apply ProcTyCompElim.refl
      case ifunfair_false v H_v H_eval =>
        exists τ₂
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₂
        . apply ProcTyCompElim.eps_elim (τs' := τ₂)
          . apply ProcTyTransition.choice_right
          . apply ProcTyCompElim.refl
    case subtype =>
      rename_i ctx' p'' τ₁ τ₂ H_typing H_subtype H_ind
      clear p τ ctx
      have H_ind := H_ind H_ctx p' H_reduces
      have ⟨τ₁', H_ind'⟩ := H_ind
      have H_τ₂' : ∃ τ₂', ProcTyCompElim τ₂ τ₂' ∧ ProcTySub τ₁' τ₂' := by
        apply ProcTySub.subtype_refinement_elim_multi
        . exact H_subtype
        . exact H_ind'.2
      have ⟨τ₂', H_τ₂'⟩ := H_τ₂'
      exists τ₂'
      constructor
      . apply ProcTyJudgement.subtype (τ₁ := τ₁')
        . exact H_ind'.1
        . exact H_τ₂'.2
      . exact H_τ₂'.1

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

private lemma insertIdx_eq_take_drop {T : Type} : ∀ (l : List T) (i : Nat) (a : T),
    i ≤ l.length → l.insertIdx i a = l.take i ++ a :: l.drop i := by
  intro l
  induction l with
  | nil =>
    intro i a h; cases i with
    | zero => rfl
    | succ n => grind
  | cons x xs ih =>
    intro i a h; cases i with
    | zero => simp [List.insertIdx]
    | succ n =>
      simp only [List.insertIdx, List.modifyTailIdx_succ_cons, List.take_succ_cons,
                 List.drop_succ_cons, List.cons_append]
      exact congrArg (x :: ·) (ih n a (by simp at h; omega))

private lemma list_append_cons_insertIdx_eq {T : Type} : ∀ (l₁ : List T) (e : T) (l₂ : List T),
    l₁ ++ e :: l₂ = (l₁ ++ l₂).insertIdx l₁.length e := by
  intro l₁; induction l₁ with
  | nil => intros; rfl
  | cons x xs ih =>
    intro e l₂
    show x :: (xs ++ e :: l₂) = x :: (xs ++ l₂).insertIdx xs.length e
    exact congrArg (x :: ·) (ih e l₂)

private lemma zip_append_of_length {T U : Type} : ∀ (l₁ l₂ : List T) (m₁ m₂ : List U),
    l₁.length = m₁.length → (l₁ ++ l₂).zip (m₁ ++ m₂) = l₁.zip m₁ ++ l₂.zip m₂ := by
  intro l₁; induction l₁ with
  | nil => intro l₂ m₁ m₂ H; cases m₁ with | nil => rfl | cons h t => simp at H
  | cons x xs ih =>
    intro l₂ m₁ m₂ H; cases m₁ with
    | nil => simp at H
    | cons y ys =>
      simp only [List.cons_append, List.zip_cons_cons]
      exact congrArg _ (ih l₂ ys m₂ (by simp at H; exact H))

private lemma toXOffer_typing'
    {ctx : ProcTyContext} {branches : List ChoiceBranch} {branch_tys : List (MessageExch × ProcTy)}
    (H_send_expr : ∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys → ExprTyJudgement ctx.exprVars e)
    (H_send_ty : ∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.send m)
    (H_send_typing : ∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys → ProcTyJudgement ctx p br_ty.2)
    (H_recv_ty : ∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.recv m)
    (H_recv_typing : ∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys → ProcTyJudgement (ctx.extendExprVar x) p br_ty.2)
    (br : ChoiceBranch) (me : MessageExch) (ty : ProcTy)
    (H_mem : (br, (me, ty)) ∈ branches.zip branch_tys) :
    ProcTyJudgement ctx br.toXOffer (branch_to_xoffer_ty (me, ty)) := by
  simp only [ChoiceBranch.toXOffer, branch_to_xoffer_ty]
  cases br with
  | send m₀ e₀ p₀ =>
    have H_me : me = MessageExch.send m₀ := by have := H_send_ty m₀ e₀ p₀ (me, ty) H_mem; simp at this; exact this
    have H_e₀ := H_send_expr m₀ e₀ p₀ (me, ty) H_mem
    have H_p₀ : ProcTyJudgement ctx p₀ ty := by have := H_send_typing m₀ e₀ p₀ (me, ty) H_mem; simp at this; exact this
    subst H_me
    apply ProcTyJudgement.xoffer <;> [rfl; skip; skip; skip; skip; skip; exact ProcTyJudgement.skip _]
    · intro m e p br_ty H; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at H; obtain ⟨rfl, -, -, rfl⟩ := H; exact H_e₀
    · intro m e p br_ty H; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at H; obtain ⟨rfl, -, -, rfl⟩ := H; rfl
    · intro m e p br_ty H; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at H; obtain ⟨rfl, -, -, rfl⟩ := H; simpa using H_p₀
    · intro m v p br_ty H; simp at H
    · intro m v p br_ty H; simp at H
  | recv m₀ v₀ p₀ =>
    have H_me : me = MessageExch.recv m₀ := by have := H_recv_ty m₀ v₀ p₀ (me, ty) H_mem; simp at this; exact this
    have H_p₀ : ProcTyJudgement (ctx.extendExprVar v₀) p₀ ty := by have := H_recv_typing m₀ v₀ p₀ (me, ty) H_mem; simp at this; exact this
    subst H_me
    apply ProcTyJudgement.xoffer <;> [rfl; skip; skip; skip; skip; skip; exact ProcTyJudgement.skip _]
    · intro m e p br_ty H; simp at H
    · intro m e p br_ty H; simp at H
    · intro m e p br_ty H; simp at H
    · intro m v p br_ty H; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at H; obtain ⟨rfl, -, -, rfl⟩ := H; rfl
    · intro m v p br_ty H; simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at H; obtain ⟨rfl, -, -, rfl⟩ := H; simpa using H_p₀

private lemma branch_to_xoffer_ty_guarded (me : MessageExch) (ty : ProcTy)
    (H_guarded : ProcTyGuardedClosed ty) : ProcTyGuardedClosed (branch_to_xoffer_ty (me, ty)) := by
  simp only [branch_to_xoffer_ty]
  apply ProcTyGuarded.xoffer <;> [exact ProcTyGuarded.skip _ _ _; skip]
  intro m τ H_mem; simp only [List.mem_singleton] at H_mem; obtain ⟨-, rfl⟩ := H_mem; exact H_guarded

private lemma foldl_par_typing' {ctx : ProcTyContext} : ∀ (ps : List Proc) (τs : List ProcTy),
    List.Forall₂ (ProcTyJudgement ctx) ps τs → ∀ p₀ τ₀, ProcTyJudgement ctx p₀ τ₀ →
    ProcTyJudgement ctx (List.foldl (fun acc p => Proc.par acc p) p₀ ps)
      (List.foldl (fun acc τ => ProcTy.par acc τ) τ₀ τs) := by
  intro ps τs H_all; induction H_all with
  | nil => exact fun _ _ h => h
  | @cons p τ rest_p rest_τ H_head H_tail ih =>
    intro p₀ τ₀ H₀; simp only [List.foldl_cons]
    exact ih _ _ (ProcTyJudgement.par _ _ _ _ _ H₀ H_head)

private lemma foldl_par_guarded' : ∀ (τs : List ProcTy), (∀ τ ∈ τs, ProcTyGuardedClosed τ) →
    ∀ τ₀, ProcTyGuardedClosed τ₀ →
    ProcTyGuardedClosed (List.foldl (fun acc τ => ProcTy.par acc τ) τ₀ τs) := by
  intro τs; induction τs with
  | nil => exact fun _ _ h => h
  | cons τ₁ rest ih =>
    intro H_all τ₀ H₀; simp only [List.foldl_cons]
    apply ih (fun τ hm => H_all τ (List.mem_cons_of_mem _ hm))
    apply ProcTyGuarded.par
    . exact H₀
    . apply H_all
      grind

private lemma ex_cond_of_branches
    {branches : List ChoiceBranch} {branch_tys : List (MessageExch × ProcTy)}
    {ex_msg : Finset (MessageId × MessageDir)}
    (H_send_ty : ∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.send m)
    (H_recv_ty : ∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys → br_ty.1 = MessageExch.recv m)
    (H_len : branches.length = branch_tys.length)
    (H_ex_cond : ∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg) :
    ∀ m ty, (m, ty) ∈ branch_tys → (m.messageId, m.direction.invert) ∈ ex_msg := by
  intro m ty H_mem
  obtain ⟨br, H_zip'⟩ := Trivia.zip_list_exists branch_tys branches (m, ty) H_len.symm.le H_mem
  have H_zip : (br, (m, ty)) ∈ branches.zip branch_tys := Trivia.zip_flip _ _ _ _ H_zip'
  have H_br_mem : br ∈ branches := (List.of_mem_zip H_zip).1
  cases br with
  | send msg' e' p' =>
    have H_m : m = MessageExch.send msg' := by have := H_send_ty msg' e' p' (m, ty) H_zip; simp at this; exact this
    subst H_m
    have := @H_ex_cond (msg', MessageDir.send) (by simp only [List.mem_map]; exact ⟨_, H_br_mem, rfl⟩)
    simpa [MessageExch.messageId, MessageExch.direction, MessageDir.invert] using this
  | recv msg' var' p' =>
    have H_m : m = MessageExch.recv msg' := by have := H_recv_ty msg' var' p' (m, ty) H_zip; simp at this; exact this
    subst H_m
    have := @H_ex_cond (msg', MessageDir.recv) (by simp only [List.mem_map]; exact ⟨_, H_br_mem, rfl⟩)
    simpa [MessageExch.messageId, MessageExch.direction, MessageDir.invert] using this

set_option maxHeartbeats 20000000

lemma type_emulates_proc_label : ∀ (p p' : Semantics.ProcComp)
                                (τ : ProcTyComposition) (lbl : TransLabel),
    CompositionTyJudgement p τ →
    ProcTyGuardedClosed τ →
    Semantics.Reduces p lbl p' →
    lbl ≠ TransLabel.ε →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyGuardedClosed τ' ∧
      ProcTyIncompTransition τ (AbstractTransLabel.fromConcrete lbl) τ' := by

    intro p p' τ lbl H_typing H_guarded H_reduces H_not_ε
    revert H_guarded H_reduces p' lbl
    unfold CompositionTyJudgement at H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    induction H_typing <;> intro p' lbl H_guarded H_reduces H_not_ε <;> try (cases H_reduces; done)
    case seq =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_reduces
      case seq_step p₁' H_red =>
        cases H_guarded <;> (
          rename_i H_guarded₁ H_guarded₂
          have H_ind₁ := H_ind₁ H_ctx p₁' lbl H_guarded₁ H_red H_not_ε
          have ⟨τ₁', H_ind₁⟩ := H_ind₁
          exists (ProcTy.seq τ₁' τ₂)
          constructor
          . apply ProcTyJudgement.seq
            . exact H_ind₁.1
            . rewrite [H_ctx]
              exact H_typing₂
          . constructor
            . aesop
            . apply ProcTyIncompTransition.reduces_seq
              exact H_ind₁.2.2
        )
      case seq_skip =>
        simp at H_not_ε
    case par =>
      rename_i ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      cases H_reduces
      case par_tock =>
        rename_i p₁' p₂' H_red₁ H_red₂
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.ac Action.tock) H_guarded₁ H_red₁ (by simp)
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.ac Action.tock) H_guarded₂ H_red₂ (by simp)
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . exact H_ind₂.1
        . constructor
          . aesop
          . apply ProcTyIncompTransition.reduces_par_tock
            . exact H_ind₁.2.2
            . exact H_ind₂.2.2
      case par_left p₁' H_lbl H_nonex H_red =>
        have H_ind₁ := H_ind₁ H_ctx p₁' lbl H_guarded₁ H_red H_not_ε
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        exists (ProcTy.par τ₁' τ₂)
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . rewrite [H_ctx]
            exact H_typing₂
        . constructor
          . aesop
          . apply ProcTyIncompTransition.reduces_par_left
            . rewrite [label_abstraction_preserves_ex (lbl := lbl)]
              exact H_nonex
            . by_contra H_tock
              unfold AbstractTransLabel.fromConcrete at H_tock
              cases lbl <;> simp at H_tock
              simp at H_lbl
              contradiction
            . exact H_ind₁.2.2
            . apply ProcTyCompElim.refl
      case par_right p₂' H_lbl H_nonex H_red =>
        have H_ind₂ := H_ind₂ H_ctx p₂' lbl H_guarded₂ H_red H_not_ε
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁ τ₂')
        constructor
        . apply ProcTyJudgement.par
          . rewrite [H_ctx]
            exact H_typing₁
          . exact H_ind₂.1
        . constructor
          . aesop
          . apply ProcTyIncompTransition.reduces_par_right
            . rewrite [label_abstraction_preserves_ex (lbl := lbl)]
              exact H_nonex
            . by_contra H_tock
              unfold AbstractTransLabel.fromConcrete at H_tock
              cases lbl <;> simp at H_tock
              simp at H_lbl
              contradiction
            . apply ProcTyCompElim.refl
            . exact H_ind₂.2.2
      case par_left_ex ex_msg p₁' H_red H_m =>
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.ex ex_msg) H_guarded₁ H_red H_not_ε
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        have H_τ₂' : ∃ τ₂', ProcTyCompElim τ₂ τ₂' ∧ CompositionTyJudgement p₂ τ₂' ∧ (
          ∀ mx, Semantics.NonInstantMessage ∅ ∅ p₂ mx → ProcTyNonInstantMsg ∅ ∅ τ₂' mx
        ) := by
          exists τ₂
          constructor
          . aesop
          . constructor
            . unfold CompositionTyJudgement
              rewrite [H_ctx]
              exact H_typing₂
            . intro mx H_noninstmsg
              apply ProcTyGuarded.guarded_preserves_non_instant_msg <;> assumption
        have ⟨τ₂', H_τ₂'⟩ := H_τ₂'
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . exact H_τ₂'.2.1
        . constructor
          . apply ProcTyGuarded.par
            . apply ProcTyGuarded.incomp_trans_preserves_guarded (τ₁ := τ₁) (lbl := AbstractTransLabel.ex ex_msg)
              . exact H_guarded₁
              . unfold AbstractTransLabel.fromConcrete at H_ind₁
                simp at H_ind₁
                exact H_ind₁.2.2
            . apply ProcTyGuarded.elim_preserves_guarded (τ₁ := τ₂)
              . exact H_guarded₂
              . exact H_τ₂'.1
          . apply ProcTyIncompTransition.reduces_extend_l (τ₁ := ProcTy.par τ₁ τ₂')
            . apply ProcTyIncompTransition.reduces_par_ex_left
              . unfold AbstractTransLabel.fromConcrete at H_ind₁
                simp at H_ind₁
                exact H_ind₁.2.2
              . intro mx H_mx
                apply H_τ₂'.2.2
                apply H_m
                exact H_mx
            . apply ProcTyCompElim.elim_par
              . apply ProcTyCompElim.refl
              . exact H_τ₂'.1
      case par_right_ex ex_msg p₂' H_m H_red =>
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.ex ex_msg) H_guarded₂ H_red H_not_ε
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        have H_τ₁' : ∃ τ₁', ProcTyCompElim τ₁ τ₁' ∧ CompositionTyJudgement p₁ τ₁' ∧ (
          ∀ mx, Semantics.NonInstantMessage ∅ ∅ p₁ mx → ProcTyNonInstantMsg ∅ ∅ τ₁' mx
        ) := by
          exists τ₁
          constructor
          . aesop
          . constructor
            . unfold CompositionTyJudgement
              rewrite [H_ctx]
              exact H_typing₁
            . intro mx H_noninstmsg
              apply ProcTyGuarded.guarded_preserves_non_instant_msg <;> assumption
        have ⟨τ₁', H_τ₁'⟩ := H_τ₁'
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_τ₁'.2.1
          . exact H_ind₂.1
        . constructor
          . apply ProcTyGuarded.par
            . apply ProcTyGuarded.elim_preserves_guarded (τ₁ := τ₁)
              . exact H_guarded₁
              . exact H_τ₁'.1
            . apply ProcTyGuarded.incomp_trans_preserves_guarded (τ₁ := τ₂) (lbl := AbstractTransLabel.ex ex_msg)
              . exact H_guarded₂
              . unfold AbstractTransLabel.fromConcrete at H_ind₂
                simp at H_ind₂
                exact H_ind₂.2.2
          . apply ProcTyIncompTransition.reduces_extend_l (τ₁ := ProcTy.par τ₁' τ₂)
            . apply ProcTyIncompTransition.reduces_par_ex_right
              . unfold AbstractTransLabel.fromConcrete at H_ind₂
                simp at H_ind₂
                exact H_ind₂.2.2
              . intro mx H_mx
                apply H_τ₁'.2.2
                apply H_m
                exact H_mx
            . apply ProcTyCompElim.elim_par
              . exact H_τ₁'.1
              . apply ProcTyCompElim.refl
      case par_skip_left =>
        simp at H_not_ε
      case par_skip_right =>
        simp at H_not_ε
      case par_message msg dir dir' b p₁' p₂' H_dual H_red₁ H_red₂ =>
        have H_ind₁ := H_ind₁ H_ctx p₁' (TransLabel.message msg dir b) H_guarded₁ H_red₁ (by simp)
        have ⟨τ₁', H_ind₁⟩ := H_ind₁
        have H_ind₂ := H_ind₂ H_ctx p₂' (TransLabel.message msg dir' b) H_guarded₂ H_red₂ (by simp)
        have ⟨τ₂', H_ind₂⟩ := H_ind₂
        exists (ProcTy.par τ₁' τ₂')
        constructor
        . apply ProcTyJudgement.par
          . exact H_ind₁.1
          . exact H_ind₂.1
        . constructor
          . aesop
          . apply ProcTyIncompTransition.reduces_par_message (τ₁ := τ₁) (τ₂ := τ₂)
            . exact H_dual
            . exact H_ind₁.2.2
            . exact H_ind₂.2.2
    case cycle =>
      rename_i ctx'
      cases H_reduces
      exists ProcTy.skip
      constructor
      . unfold CompositionTyJudgement
        rewrite [H_ctx]
        apply ProcTyJudgement.skip
      . constructor
        . aesop
        . exists ProcTy.cycle
          constructor <;> aesop
    case message_send ctx' msg p'' H_typing =>
      clear p τ ctx
      cases H_reduces
      exists ProcTy.skip
      constructor
      . unfold CompositionTyJudgement
        rewrite [H_ctx]
        apply ProcTyJudgement.skip
      . constructor
        . aesop
        . exists (ProcTy.message $ MessageExch.send msg)
          constructor <;> aesop
    case message_recv ctx' msg x p'' τ_body H_typing_body H_ind =>
      clear p τ ctx
      cases H_reduces
      rename_i v
      exists ProcTy.seq ProcTy.skip τ_body
      constructor
      . apply ProcTyJudgement.seq
        . aesop
        . apply val_replacement_preserves_typing (ctx := ProcTyContext.empty)
          rewrite [H_ctx]
          exact H_typing_body
      . constructor
        . cases H_guarded <;> aesop
        . exists ((ProcTy.message (MessageExch.recv msg)).seq τ_body)
          constructor
          . aesop
          . apply ProcTyCompElim.refl
    case choice ctx' e p₁ p₂ τ₁ τ₂ H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      clear p τ ctx
      cases H_reduces <;> simp at H_not_ε
    case choice_fair ctx' e p₁ p₂ τ₁ τ₂ bid H_e_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      clear p τ ctx
      cases H_reduces
      case iffair_true v H_v H_eval =>
        exists τ₁
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₁
        . constructor
          . cases H_guarded
            assumption
          . exists (ProcTy.choice_fair bid τ₁ τ₂)
            constructor
            . apply ProcTyTransition.choice_fair_left
            . apply ProcTyCompElim.refl
      case iffair_false v H_v H_eval =>
        exists τ₂
        constructor
        . unfold CompositionTyJudgement
          rewrite [H_ctx]
          exact H_typing₂
        . constructor
          . cases H_guarded
            assumption
          . exists (ProcTy.choice_fair bid τ₁ τ₂)
            constructor
            . apply ProcTyTransition.choice_fair_right
            . apply ProcTyCompElim.refl
    case subtype ctx' p₀ τ₁ τ₂ H_typing₁ H_sub H_ind =>
      have H_guarded₁ : ProcTyGuardedClosed τ₁ := by
        apply ProcTySub.subtype_preserves_guarded
        . exact H_sub
        . exact H_guarded
      have H_ind := H_ind H_ctx p' lbl H_guarded₁ H_reduces H_not_ε
      have ⟨τ₁', H_ind⟩ := H_ind
      have H_τ₂' : ∃ τ₂', ProcTyIncompTransition τ₂ (AbstractTransLabel.fromConcrete lbl) τ₂' ∧ ProcTyGuardedClosed τ₂' ∧ ProcTySub τ₁' τ₂' := by
        apply ProcTySub.subtype_refinement_label_multi (τ₁ := τ₁) (lbl := AbstractTransLabel.fromConcrete lbl) <;> try assumption
        . unfold AbstractTransLabel.fromConcrete
          cases lbl <;> simp
          simp at H_not_ε
        . exact H_ind.2.2
      have ⟨τ₂', H_τ₂'⟩ := H_τ₂'
      exists τ₂'
      constructor
      . apply ProcTyJudgement.subtype (τ₁ := τ₁')
        . exact H_ind.1
        . exact H_τ₂'.2.2
      . constructor
        . exact H_τ₂'.2.1
        . exact H_τ₂'.1
    case recur ctx' x p'' τ' H_typing H_ind=>
      cases H_reduces
      simp at H_not_ε
    case offer => sorry
    case xoffer => sorry -- TODO: to prove

lemma process_refines_type_incomp : ∀ (p p' : Proc) (τ : ProcTy) (lbl : TransLabel),
    CompositionTyJudgement p τ →
    ProcTyGuardedClosed τ →
    lbl ≠ TransLabel.ε →
    Semantics.IncompReduces p lbl p' →
    ∃ τ', CompositionTyJudgement p' τ'
      ∧ ProcTyGuardedClosed τ'
      ∧ ProcTyIncompTransition τ (AbstractTransLabel.fromConcrete lbl) τ' := by

  intro p p' τ lbl H_typing H_guarded H_not_ε H_reduces
  unfold Semantics.IncompReduces at H_reduces
  have ⟨p₁, H_reduces⟩ := H_reduces
  have H_mid_τ : ∃ τ₁, CompositionTyJudgement p₁ τ₁ ∧ ProcTyCompElim τ τ₁ := by
    apply type_emulates_proc_multi_ε (p := p) (p' := p₁)
    . exact H_typing
    . exact H_reduces.2
  have ⟨τ', H_τ'⟩ := H_mid_τ
  have H_end_τ : ∃ τ'', CompositionTyJudgement p' τ''
    ∧ ProcTyGuardedClosed τ''
    ∧ ProcTyIncompTransition τ' (AbstractTransLabel.fromConcrete lbl) τ'' := by
    apply type_emulates_proc_label (p := p₁) (p' := p')
    . exact H_τ'.1
    . apply ProcTyGuarded.elim_preserves_guarded (τ₁ := τ)
      . exact H_guarded
      . exact H_τ'.2
    . exact H_reduces.1
    . exact H_not_ε
  have ⟨τ'', H_τ''⟩ := H_end_τ
  exists τ''
  constructor
  . exact H_τ''.1
  . constructor
    . exact H_τ''.2.1
    . apply ProcTyIncompTransition.reduces_extend_l (τ₁ := τ')
      . exact H_τ''.2.2
      . exact H_τ'.2

-- TODO: may need to consider the ex labels
theorem process_refines_type : ∀ (p p' : Proc) (τ : ProcTy) (α : Action),
    CompositionTyJudgement p τ →
    ProcTyGuardedClosed τ →
    Semantics.CompReduces p α p' →
    ∃ τ', CompositionTyJudgement p' τ'
      ∧ ProcTyGuardedClosed τ'
      ∧ ProcTyCompTransition τ α τ' := by

  intro p p' τ α H_typing H_guarded H_reduces
  unfold ProcTyCompTransition
  have H_lbl : AbstractTransLabel.ac α = AbstractTransLabel.fromConcrete (TransLabel.ac α) := by
    simp
  rewrite [H_lbl]
  apply process_refines_type_incomp (p := p) (p' := p') <;> try trivial
  simp
