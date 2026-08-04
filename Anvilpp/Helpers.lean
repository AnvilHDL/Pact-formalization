/-
  Here we include the helper lemmas needed for safety proofs.
-/
import Anvilpp.Proc
import Anvilpp.Types
import Anvilpp.Typing
import Anvilpp.Automata

namespace Trivia
  /-
    These lemmas are trivial.
  -/

  lemma zip_list_exists : ∀ {T U : Type} (l₁ : List T) (l₂ : List U) (v₁ : T),
      l₁.length ≤ l₂.length → v₁ ∈ l₁ → ∃ v₂, (v₁, v₂) ∈ List.zip l₁ l₂ := by
    intro T U l₁
    induction l₁ with
    | nil => simp
    | cons h t ih =>
      intro l₂ v₁ H_len H_mem
      cases l₂ with
      | nil => simp at H_len
      | cons h₂ t₂ =>
        simp only [List.length_cons, Nat.succ_le_succ_iff] at H_len
        simp only [List.zip_cons_cons, List.mem_cons] at H_mem ⊢
        rcases H_mem with rfl | hmem
        · exact ⟨h₂, Or.inl rfl⟩
        · obtain ⟨v₂, hv₂⟩ := ih t₂ v₁ H_len hmem
          exact ⟨v₂, Or.inr hv₂⟩

  lemma zip_list_split₂ : ∀ {T U : Type} (ll₁ rl₁ : List T) (e₁ : T) (ll₂ rl₂ : List U) (e₂ : U),
      ll₁.length = ll₂.length → rl₁.length = rl₂.length →
      (ll₁ ++ e₁ :: rl₁).zip (ll₂ ++ e₂ :: rl₂) = List.zip ll₁ ll₂ ++ [(e₁, e₂)] ++ List.zip rl₁ rl₂ := by
    intro T U ll₁
    induction ll₁ with
    | nil =>
      intro rl₁ e₁ ll₂ rl₂ e₂ H_len _
      cases ll₂ with
      | nil => simp
      | cons => simp at H_len
    | cons h t ih =>
      intro rl₁ e₁ ll₂ rl₂ e₂ H_len H_rlen
      cases ll₂ with
      | nil => simp at H_len
      | cons h₂ t₂ =>
        simp only [List.length_cons, Nat.succ_inj] at H_len
        simp only [List.cons_append, List.zip_cons_cons]
        rw [ih rl₁ e₁ t₂ rl₂ e₂ H_len H_rlen]

  lemma list_insert_idx : ∀ {T : Type} (l : List T) (idx : ℕ) (v : T),
      idx ≤ l.length →
        v ∈ l.insertIdx idx v := by
    intro T l idx v
    induction idx generalizing l with
    | zero => simp
    | succ n ih =>
      cases l with
      | nil => simp
      | cons h t =>
        intro H
        simp only [List.length_cons, Nat.succ_le_succ_iff] at H
        simp only [List.insertIdx_succ_cons, List.mem_cons]
        exact Or.inr (ih t H)

  lemma zip_flip {T U : Type} : ∀ (l1 : List T) (l2 : List U) (a : T) (b : U),
      (a, b) ∈ l1.zip l2 → (b, a) ∈ l2.zip l1 := by
    intro l1; induction l1 with
    | nil => simp
    | cons x xs ih =>
      intro l2; cases l2 with
      | nil => simp
      | cons y ys =>
        intro a b h
        simp [List.mem_cons] at h ⊢
        cases h with
        | inl h => left; exact ⟨h.2, h.1⟩
        | inr h => right; exact ih _ _ _ h
end Trivia

lemma larger_context_preserves_noninst (τ : ProcTy) (Γ Γ' : Finset String) :
    Γ ⊆ Γ' →
    ProcTyNonInstant Γ τ →
    ProcTyNonInstant Γ' τ := by
  intro H_subset H_noninst
  induction H_noninst generalizing Γ' with
  | cycle Γ => exact ProcTyNonInstant.cycle Γ'
  | choice Γ τ1 τ2 H1 H2 IH1 IH2 =>
    exact ProcTyNonInstant.choice Γ' τ1 τ2 (IH1 Γ' H_subset) (IH2 Γ' H_subset)
  | choice_fair bid Γ τ1 τ2 H1 H2 IH1 IH2 =>
    exact ProcTyNonInstant.choice_fair bid Γ' τ1 τ2 (IH1 Γ' H_subset) (IH2 Γ' H_subset)
  | seq_left Γ τ1 τ2 H IH =>
    exact ProcTyNonInstant.seq_left Γ' τ1 τ2 (IH Γ' H_subset)
  | seq_right Γ τ1 τ2 H IH =>
    exact ProcTyNonInstant.seq_right Γ' τ1 τ2 (IH Γ' H_subset)
  | par_left Γ τ1 τ2 H IH =>
    exact ProcTyNonInstant.par_left Γ' τ1 τ2 (IH Γ' H_subset)
  | par_right Γ τ1 τ2 H IH =>
    exact ProcTyNonInstant.par_right Γ' τ1 τ2 (IH Γ' H_subset)
  | xoffer Γ τ_else branch_tys H_else H_br IH_else IH_br =>
    exact ProcTyNonInstant.xoffer Γ' τ_else branch_tys
      (IH_else Γ' H_subset)
      (fun m ty H_in => IH_br m ty H_in Γ' H_subset)
  | offer Γ τ_else branch_tys H_else H_br IH_else IH_br =>
    exact ProcTyNonInstant.offer Γ' τ_else branch_tys
      (IH_else Γ' H_subset)
      (fun m ty H_in => IH_br m ty H_in Γ' H_subset)
  | var Γ x Hx =>
    exact ProcTyNonInstant.var Γ' x (Finset.mem_of_subset H_subset Hx)
  | recur Γ x body Hrec IH =>
    have H_union : (Γ ∪ {x}) ⊆ (Γ' ∪ {x}) := by grind
    exact ProcTyNonInstant.recur Γ' x body (IH (Γ' ∪ {x}) H_union)

lemma congr_non_instant_preservation (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ → ∀ Γ, (ProcTyNonInstant Γ τ₂ ↔ ProcTyNonInstant Γ τ₁) := by
    intro H_congr
    induction H_congr with
    | refl τ => intro Γ; exact Iff.rfl
    | symm τ₁' τ₂' H_congr H_ind =>
      intro Γ
      exact (H_ind Γ).symm
    | trans τ₁' τ₂' τ₃' H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
      intro Γ
      exact Iff.trans (H_ind₂ Γ) (H_ind₁ Γ)
    | par_comm τ₁' τ₂' =>
      intro Γ
      constructor <;> (
        intro H_noninst
        cases H_noninst with
        | par_left Γ'' α β H => exact ProcTyNonInstant.par_right _ _ _ H
        | par_right Γ'' α β H => exact ProcTyNonInstant.par_left _ _ _ H
      )

lemma subtype_non_instant_preservation (τ₁ τ₂ : ProcTy) :
      ProcTySub τ₁ τ₂ → ∀ Γ, (ProcTyNonInstant Γ τ₂ → ProcTyNonInstant Γ τ₁) := by
    intro H_sub
    induction H_sub
    case congr τ₁' τ₂' H_congr =>
      intro Γ
      apply (congr_non_instant_preservation τ₁' τ₂' H_congr Γ).mp
    case choice_relax τ₁' τ₂' H_mx H_mx_msg =>
      intro Γ H_noninst
      cases H_noninst
      aesop
    case trans => aesop

lemma subtype_non_instant_preservation_rev (τ₁ τ₂ : ProcTy) :
      ProcTySub τ₁ τ₂ → ∀ Γ, (ProcTyNonInstant Γ τ₁ → ProcTyNonInstant Γ τ₂) := by
    intro H_sub
    induction H_sub
    case congr τ₁' τ₂' H_congr =>
      intro Γ
      apply (congr_non_instant_preservation τ₁' τ₂' H_congr Γ).mpr
    case choice_relax τ₁' τ₂' H_mx H_mx_msg =>
      intro Γ H_noninst
      apply ProcTyNonInstant.choice
      · exact H_noninst
      · exact larger_context_preserves_noninst τ₂' ∅ Γ (Finset.empty_subset Γ) H_mx
    case trans => aesop

lemma congr_non_instant_msg_preservation (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ → ∀ Γₙ Γₘ mx, (ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx ↔ ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx) := by

    intro H_congr
    induction H_congr
    case refl | symm | trans => aesop
    case par_comm τ₁' τ₂' =>
      intro Γₙ Γₘ mx
      constructor <;> (
        intro H_noninst_msg
        cases H_noninst_msg
        aesop
      )

lemma subtype_non_instant_msg_preservation (τ₁ τ₂ : ProcTy) :
      ProcTySub τ₁ τ₂ → ∀ Γₙ Γₘ mx, (ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx → ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx) := by

    intro H_sub
    induction H_sub
    case congr τ₁' τ₂' H_congr =>
      intro Γₙ Γₘ mx
      apply (congr_non_instant_msg_preservation τ₁' τ₂' H_congr Γₙ Γₘ mx).mp
    case choice_relax τ₁' τ₂' H_mx =>
      intro Γₙ Γₘ mx H_noninst_msg
      cases H_noninst_msg
      aesop
    case trans => aesop

lemma larger_context_preserves_noninst_msg (τ : ProcTy) (Γₙ Γₘ Γₙ' Γₘ' : Finset String) (mx : MessageId × MessageDir) :
    Γₙ ⊆ Γₙ' →
    Γₘ ⊆ Γₘ' →
    ProcTyNonInstantMsg Γₙ Γₘ τ mx →
    ProcTyNonInstantMsg Γₙ' Γₘ' τ mx := by

    intro Hₙ_subset Hₘ_subset H_noninst_msg
    revert Hₙ_subset Hₘ_subset Γₙ' Γₘ'
    induction H_noninst_msg
    case cycle | skip | dollar | choice | choice_fair | par | var
        | send | recv | send_opposite | recv_opposite => aesop
    case seq_left Γₙ Γₘ τ₁ τ₂ mx H_noninstmsg H_noninst H_ind =>
      intro Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.seq_left
      . apply H_ind
        exact Hₙ_subset
        exact Hₘ_subset
      . apply larger_context_preserves_noninst (Γ := Γₙ)
        exact Hₙ_subset
        exact H_noninst
    case seq_right Γₙ Γₘ τ₁ τ₂ mx H_noninstmsg₁ H_noninstmsg₂ H_ind₁ H_ind₂ =>
      intro Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.seq_right
      . apply H_ind₁
        exact Hₙ_subset
        exact Hₘ_subset
      . apply H_ind₂
        exact Hₙ_subset
        exact Hₘ_subset
    case recur_instant Γₙ' Γₘ' x τ' mx H_noninst H_noninstmsg H_ind =>
      intro Γₙ'' Γₘ'' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.recur_instant
      . apply ProcTyNonInstant.recur
        cases H_noninst
        apply larger_context_preserves_noninst (Γ := Γₙ' ∪ {x})
        . grind
        . assumption
      . apply H_ind <;> grind
    case recur_noninstant Γₙ' Γₘ' x τ' mx H_noninstmsg H_ind =>
      intro Γₙ'' Γₘ'' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.recur_noninstant
      apply H_ind <;> grind
    case xoffer =>
      rename_i Γₙ'' Γₘ'' τ_else branch_tys mx' H_else H_branch H_neq H_ind_else H_ind_branch
      intro Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.xoffer
      · exact H_ind_else Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      · intro m ty H_mem; exact H_ind_branch m ty H_mem Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      · exact H_neq
    case offer =>
      rename_i Γₙ'' Γₘ'' τ_else branch_tys mx' H_else H_branch H_neq H_ind_else H_ind_branch
      intro Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      apply ProcTyNonInstantMsg.offer
      · exact H_ind_else Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      · intro m ty H_mem; exact H_ind_branch m ty H_mem Γₙ' Γₘ' Hₙ_subset Hₘ_subset
      · exact H_neq

lemma subtype_non_instant_msg_preservation_rev (τ₁ τ₂ : ProcTy) :
      ProcTySub τ₁ τ₂ → ∀ Γₙ Γₘ mx, (ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx → ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx) := by

    intro H_sub
    induction H_sub
    case congr τ₁' τ₂' H_congr =>
      intro Γₙ Γₘ mx
      apply (congr_non_instant_msg_preservation τ₁' τ₂' H_congr Γₙ Γₘ mx).mpr
    case choice_relax τ₁' τ₂' H_mx =>
      intro Γₙ Γₘ mx H_noninst_msg
      apply ProcTyNonInstantMsg.choice
      . exact H_noninst_msg
      . apply larger_context_preserves_noninst_msg (Γₙ := ∅) (Γₘ := ∅)
        . grind
        . grind
        . apply H_mx
    case trans => aesop


lemma procty_double_extend_does_nothing : ∀ (ctx : ProcTyContext) (x : String),
    ctx.extendProcVar x = (ctx.extendProcVar x).extendProcVar x := by
  intro ctx x
  unfold ProcTyContext.extendProcVar
  grind

@[aesop unsafe]
lemma larger_context_preserves_expr_typing :
      ∀ (e : Expr) (ctx ctx' : Finset String),
      ctx ⊆ ctx' →
      ExprTyJudgement ctx e →
      ExprTyJudgement ctx' e := by
  intro e ctx ctx' H_subset H_typing
  revert ctx'
  induction H_typing
  case var x H_ctx =>
    intro ctx' H_subset
    apply ExprTyJudgement.var
    grind
  case val b =>
    intro ctx' H_subset
    apply ExprTyJudgement.val
  case add e₁ e₂ bop H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    intro ctx' H_subset
    apply ExprTyJudgement.add
    . apply H_ind₁
      exact H_subset
    . apply H_ind₂
      exact H_subset

private lemma mem_replaceBranches_inv
    {branch_tys : List (MessageExch × ProcTy)} {x : String} {τ' : ProcTy}
    {m : MessageExch} {ty : ProcTy}
    (h : (m, ty) ∈ ProcTy.replaceBranches branch_tys x τ') :
    ∃ ty₀, (m, ty₀) ∈ branch_tys ∧ ty = ty₀.replaceVar x τ' := by
  induction branch_tys with
  | nil =>
      simp [ProcTy.replaceBranches] at h
  | cons br rest ih =>
      cases br with
      | mk me tyh =>
          simp [ProcTy.replaceBranches] at h
          rcases h with h | h
          · have hmty : m = me ∧ ty = tyh.replaceVar x τ' := by
              simpa [Prod.mk.injEq] using h
            rcases hmty with ⟨hm, hty⟩
            subst hm
            exact ⟨tyh, List.mem_cons.mpr (Or.inl rfl), hty⟩
          · obtain ⟨ty₀, hmem, hty⟩ := ih h
            exact ⟨ty₀, List.mem_cons.mpr (Or.inr hmem), hty⟩

lemma replace_preserves_noninst (x : String) (τ τ' : ProcTy) (Γ : Finset String) :
    (x ∈ Γ → ProcTyNonInstant ∅ τ') →
    ProcTyNonInstant Γ τ → ProcTyNonInstant Γ (τ.replaceVar x τ') := by

  revert x τ' Γ
  induction τ using ProcTy.ind
  case H_cycle | H_dollar | H_skip | H_message =>
    unfold ProcTy.replaceVar
    aesop
  case H_recur x' body H_ind =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    by_cases h : x = x'
    case pos =>
      aesop
    case neg =>
      simp [h]
      cases H_noninst₂
      rename_i H_noninst₂
      have H_ind := H_ind x τ' (Γ ∪ {x'}) (
        by
          -- x ∈ Γ
          intro H_x
          simp [h] at H_x
          apply H_noninst₁
          exact H_x
      ) H_noninst₂
      aesop
  case H_var x =>
    intro x' τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    rename_i H_noninst₂
    by_cases h : x' = x
    case pos =>
      simp [h]
      apply larger_context_preserves_noninst (Γ := ∅)
      . grind
      . apply H_noninst₁
        rewrite [h]
        exact H_noninst₂
    case neg =>
      simp [h]
      aesop
  case H_choice τ₁ τ₂ H_ind₁ H_ind₂ =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    rename_i H_noninst₁' H_noninst₂'
    have H_ind₁ := H_ind₁ x τ' Γ H_noninst₁ H_noninst₁'
    have H_ind₂ := H_ind₂ x τ' Γ H_noninst₁ H_noninst₂'
    aesop
  case H_choice_fair τ₁ τ₂ b H_ind₁ H_ind₂ =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    rename_i H_noninst₁' H_noninst₂'
    have H_ind₁ := H_ind₁ x τ' Γ H_noninst₁ H_noninst₁'
    have H_ind₂ := H_ind₂ x τ' Γ H_noninst₁ H_noninst₂'
    aesop
  case H_par τ₁ τ₂ H_ind₁ H_ind₂ =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    case par_left H_noninst₂ =>
      have H_ind₁ := H_ind₁ x τ' Γ H_noninst₁ H_noninst₂
      aesop
    case par_right H_noninst₂ =>
      have H_ind₂ := H_ind₂ x τ' Γ H_noninst₁ H_noninst₂
      aesop
  case H_seq τ₁ τ₂ H_ind₁ H_ind₂ =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    case seq_left H_noninst₂ =>
      have H_ind₁ := H_ind₁ x τ' Γ H_noninst₁ H_noninst₂
      aesop
    case seq_right H_noninst₂ =>
      have H_ind₂ := H_ind₂ x τ' Γ H_noninst₁ H_noninst₂
      aesop
  case H_xoffer τ_else branch_tys H_ind_else H_ind_branch =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    case xoffer H_else H_branch =>
      apply ProcTyNonInstant.xoffer
      · exact H_ind_else x τ' Γ H_noninst₁ H_else
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x) (τ' := τ') H_mem
        rw [H_eq]
        exact H_ind_branch m ty₀ H_mem₀ x τ' Γ H_noninst₁ (H_branch m ty₀ H_mem₀)
  case H_offer τ_else branch_tys H_ind_else H_ind_branch =>
    intro x τ' Γ H_noninst₁ H_noninst₂
    unfold ProcTy.replaceVar
    cases H_noninst₂
    case offer H_else H_branch =>
      apply ProcTyNonInstant.offer
      · exact H_ind_else x τ' Γ H_noninst₁ H_else
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x) (τ' := τ') H_mem
        rw [H_eq]
        exact H_ind_branch m ty₀ H_mem₀ x τ' Γ H_noninst₁ (H_branch m ty₀ H_mem₀)

lemma replace_preserves_noninst_msg (x : String) (τ τ' : ProcTy) (Γₙ Γₘ : Finset String) (mx : MessageId × MessageDir) :
    (x ∈ Γₙ → ProcTyNonInstant ∅ τ') →
    (x ∈ Γₘ → ProcTyNonInstantMsg ∅ ∅ τ' mx) →
    ProcTyNonInstantMsg Γₙ Γₘ τ mx → ProcTyNonInstantMsg Γₙ Γₘ (τ.replaceVar x τ') mx := by

    intro H_x' H_x H_noninst_msg
    revert H_x' H_x τ' x
    induction H_noninst_msg
    case cycle | skip | choice | choice_fair | dollar | send | send_opposite | recv | recv_opposite | par =>
      unfold ProcTy.replaceVar
      aesop
    case var Γₙ' Γₘ' x mx' H_mx =>
      intro x' τ' H_noninst H_noninst_msg
      unfold ProcTy.replaceVar
      by_cases h : x' = x
      case pos =>
        simp [h]
        apply larger_context_preserves_noninst_msg (Γₙ := ∅) (Γₘ := ∅)
        . grind
        . grind
        . apply H_noninst_msg
          rewrite [h]
          exact H_mx
      case neg =>
        simp [h]
        aesop
    case seq_left Γₙ' Γₘ' τ₁' τ₂' mx' H_noninstmsg H_noninst H_ind =>
      intro x' τ' H_noninst' H_noninstmsg'
      unfold ProcTy.replaceVar
      apply ProcTyNonInstantMsg.seq_left
      . apply H_ind
        . exact H_noninst'
        . exact H_noninstmsg'
      . apply replace_preserves_noninst
        . exact H_noninst'
        . aesop
    case seq_right Γₙ' Γₘ' τ₁' τ₂' mx' H_noninstmsg₁ H_noninstmsg₂ H_ind₁ H_ind₂ =>
      intro x' τ' H_noninst' H_noninstmsg'
      unfold ProcTy.replaceVar
      apply ProcTyNonInstantMsg.seq_right
      . apply H_ind₁
        . exact H_noninst'
        . exact H_noninstmsg'
      . apply H_ind₂
        . exact H_noninst'
        . exact H_noninstmsg'
    case recur_instant Γₙ' Γₘ' x' τ'' mx' H_noninst H_noninstmsg H_ind =>
      intro x'' τ' H_noninst' H_noninstmsg'
      unfold ProcTy.replaceVar
      by_cases h : x'' = x'
      case pos =>
        simp [h]
        apply ProcTyNonInstantMsg.recur_instant
        . apply ProcTyNonInstant.recur
          cases H_noninst
          apply larger_context_preserves_noninst (Γ := Γₙ' ∪ {x'})
          . grind
          . assumption
        . exact H_noninstmsg
      case neg =>
        simp [h]
        apply ProcTyNonInstantMsg.recur_instant
        . apply ProcTyNonInstant.recur
          cases H_noninst
          apply larger_context_preserves_noninst (Γ := Γₙ' ∪ {x'})
          . grind
          . apply replace_preserves_noninst
            . simp [h]
              exact H_noninst'
            . assumption
        . apply H_ind
          . simp [h]
            exact H_noninst'
          . simp [h]
            exact H_noninstmsg'
    case recur_noninstant Γₙ' Γₘ' x' τ'' mx' H_noninstmsg H_ind =>
      intro x'' τ' H_noninst' H_noninstmsg'
      unfold ProcTy.replaceVar
      by_cases h : x'' = x'
      case pos =>
        simp [h]
        apply ProcTyNonInstantMsg.recur_noninstant
        . exact H_noninstmsg
      case neg =>
        simp [h]
        apply ProcTyNonInstantMsg.recur_noninstant
        apply H_ind
        . simp [h]
          exact H_noninst'
        . simp [h]
          exact H_noninstmsg'
    case xoffer Γₙ' Γₘ' τ_else branch_tys mx' H_else H_branch H_neq H_ind_else H_ind_branch =>
      intro x' τ'' H_noninst' H_noninstmsg'
      simp only [ProcTy.replaceVar]
      apply ProcTyNonInstantMsg.xoffer
      · exact H_ind_else x' τ'' H_noninst' H_noninstmsg'
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x') (τ' := τ'') H_mem
        rw [H_eq]
        exact H_ind_branch m ty₀ H_mem₀ x' τ'' H_noninst' H_noninstmsg'
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, _⟩ := mem_replaceBranches_inv (x := x') (τ' := τ'') H_mem
        exact H_neq m ty₀ H_mem₀
    case offer Γₙ' Γₘ' τ_else branch_tys mx' H_else H_branch H_neq H_ind_else H_ind_branch =>
      intro x' τ'' H_noninst' H_noninstmsg'
      simp only [ProcTy.replaceVar]
      apply ProcTyNonInstantMsg.offer
      · exact H_ind_else x' τ'' H_noninst' H_noninstmsg'
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x') (τ' := τ'') H_mem
        rw [H_eq]
        exact H_ind_branch m ty₀ H_mem₀ x' τ'' H_noninst' H_noninstmsg'
      · intro m ty H_mem
        obtain ⟨ty₀, H_mem₀, _⟩ := mem_replaceBranches_inv (x := x') (τ' := τ'') H_mem
        exact H_neq m ty₀ H_mem₀


lemma subtyping_replace_procty_preserved :
      ∀ (τ' τ₁ τ₂ : ProcTy) (x : String),
        ProcTySub τ₁ τ₂ →
        ProcTySub (τ₁.replaceVar x τ') (τ₂.replaceVar x τ') := by

  intro τ' τ₁ τ₂ x H_sub
  induction H_sub
  case congr τ₁' τ₂' H_congr =>
    apply ProcTySub.congr
    induction H_congr
    case a.refl =>
      apply ProcTyCongr.refl
    case a.symm τ₁'' τ₂'' H_congr' =>
      apply ProcTyCongr.symm
      exact H_congr'
    case a.trans τ₁'' τ₂'' τ₃'' H_congr₁ H_congr₂ =>
      apply ProcTyCongr.trans
      . exact H_congr₁
      . exact H_congr₂
    case a.par_comm τ₁'' τ₂'' =>
      unfold ProcTy.replaceVar
      apply ProcTyCongr.par_comm
  case choice_relax τ₁' τ₂' H_noninst H_mx =>
    conv =>
      arg 2
      unfold ProcTy.replaceVar
    apply ProcTySub.choice_relax
    . apply replace_preserves_noninst
      . grind
      . exact H_noninst
    . intro mx
      apply replace_preserves_noninst_msg
      . grind
      . grind
      . apply H_mx
  case trans τ₁' τ₂' τ₃' H_sub₁ H_sub₂ H_ind₁ H_ind₂ =>
    apply ProcTySub.trans (τ₂ := τ₂'.replaceVar x τ')
    . exact H_ind₁
    . exact H_ind₂

private lemma replaceBranches_length (branch_tys : List (MessageExch × ProcTy))
    (x : String) (τ' : ProcTy) :
    (ProcTy.replaceBranches branch_tys x τ').length = branch_tys.length := by
  induction branch_tys with
  | nil => simp [ProcTy.replaceBranches]
  | cons br rest ih =>
      cases br
      simp [ProcTy.replaceBranches, ih]

private lemma replaceBranches_eq_map (branch_tys : List (MessageExch × ProcTy))
    (x : String) (τ' : ProcTy) :
    ProcTy.replaceBranches branch_tys x τ' =
      branch_tys.map (fun br_ty => ProcTy.replaceBranchVar br_ty x τ') := by
  induction branch_tys with
  | nil => simp [ProcTy.replaceBranches]
  | cons br rest ih =>
      cases br
      simp [ProcTy.replaceBranches, ProcTy.replaceBranchVar, ih]

private lemma mem_zip_of_map {α β γ δ : Type} (f : α → γ) (g : β → δ)
    {l₁ : List α} {l₂ : List β} {a' : γ} {b' : δ}
    (h : (a', b') ∈ (l₁.map f).zip (l₂.map g)) :
    ∃ a b, (a, b) ∈ l₁.zip l₂ ∧ f a = a' ∧ g b = b' := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a₀ as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b₀ bs =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨a₀, b₀, List.mem_cons.mpr (Or.inl rfl), rfl, rfl⟩
      · obtain ⟨a, b, hmem, hfa, hgb⟩ := ih h
        exact ⟨a, b, List.mem_cons.mpr (Or.inr hmem), hfa, hgb⟩

lemma val_replacement_preserves_expr_typing :
      ∀ (ctx : ExprTyContext) (e : Expr) (x : String) (v : Bool),
        ExprTyJudgement (ctx ∪ {x}) e →
        ExprTyJudgement ctx (Semantics.exprReplace e x v) := by
  intro ctx e x v H_typing
  induction H_typing
  case var y H_ctx =>
    unfold Semantics.exprReplace
    by_cases h : x = y
    case pos =>
      rewrite [h]
      simp
      apply ExprTyJudgement.val
    case neg =>
      simp [h]
      apply ExprTyJudgement.var
      grind
  case val b =>
    unfold Semantics.exprReplace
    apply ExprTyJudgement.val
  case add e1 e2 bop H_typing1 H_typing2 H_ind1 H_ind2 =>
    unfold Semantics.exprReplace
    apply ExprTyJudgement.add
    . exact H_ind1
    . exact H_ind2

namespace ProcTyCompElim
  lemma elim_transitivity :
        ∀ {τ₁ τ₂ τ₃ : ProcTy},
          ProcTyCompElim τ₁ τ₂ →
          ProcTyCompElim τ₂ τ₃ →
          ProcTyCompElim τ₁ τ₃ := by
    intro τ₁ τ₂ τ₃ H_elim₁ H_elim₂
    induction H_elim₁
    case refl τ' =>
      exact H_elim₂
    case eps_elim τ' τ'' τ''' H_transition H_elim H_ind =>
      have H_elim' := H_ind H_elim₂
      apply ProcTyCompElim.eps_elim
      . exact H_transition
      . exact H_elim'

  lemma elim_right :
    ∀ {τ₁ τ₂ τ₃ : ProcTy},
      ProcTyCompElim τ₁ τ₂ →
      ProcTyTransition τ₂ AbstractTransLabel.ε τ₃ →
      ProcTyCompElim τ₁ τ₃ := by
    intro τ₁ τ₂ τ₃ H_elim H_transition
    have H_elim' := H_elim
    induction H_elim
    case refl τ' =>
      apply ProcTyCompElim.eps_elim
      . exact H_transition
      . apply ProcTyCompElim.refl
    case eps_elim τ' τ'' τ''' H_transition' H_elim'' H_ind =>
      apply ProcTyCompElim.eps_elim
      . exact H_transition'
      . apply H_ind
        . exact H_transition
        . exact H_elim''

  lemma elim_par :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy},
          ProcTyCompElim τ₁ τ₁' →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyCompElim (ProcTy.par τ₁ τ₂) (ProcTy.par τ₁' τ₂') := by
    intro τ₁ τ₁' τ₂ τ₂' H_elim₁ H_elim₂
    induction H_elim₁
    case refl τ₁'' =>
      induction H_elim₂
      case refl τ₂'' =>
        apply ProcTyCompElim.refl
      case eps_elim τ₂'' τ₂''' τ₂'''' H_transition H_elim H_ind =>
        apply ProcTyCompElim.eps_elim
        . apply ProcTyTransition.par_right (τ₂' := τ₂''')
          . simp
          . simp
          . exact H_transition
        . apply H_ind
    case eps_elim τ₁'' τ₁''' τ₁'''' H_transition H_elim H_ind =>
      apply ProcTyCompElim.eps_elim
      . apply ProcTyTransition.par_left (τ₁' := τ₁''')
        . simp
        . simp
        . exact H_transition
      . apply H_ind

  lemma elim_seq_step :
        ∀ {τ₁ τ₁' τ₂ : ProcTy},
          ProcTyCompElim τ₁ τ₁' →
          ProcTyCompElim (ProcTy.seq τ₁ τ₂) (ProcTy.seq τ₁' τ₂) := by
    intro τ₁ τ₁' τ₂ H_elim
    induction H_elim
    case refl τ₁'' =>
      apply ProcTyCompElim.refl
    case eps_elim τ₁'' τ₁''' τ₁'''' H_transition H_elim H_ind =>
      apply ProcTyCompElim.eps_elim
      . apply ProcTyTransition.seq_step (τ₁' := τ₁''')
        exact H_transition
      . exact H_ind

  lemma elim_seq_skip :
        ∀ {τ₁ τ₂ τ₂' : ProcTy},
          ProcTyCompElim τ₁ ProcTy.skip →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyCompElim (ProcTy.seq τ₁ τ₂) τ₂' := by
    intro τ₁ τ₂ τ₂' H_elim₁ H_elim₂
    generalize H_skip : ProcTy.skip = τ₁ at H_elim₁
    induction H_elim₁
    case refl τ₁'' =>
      rewrite [← H_skip]
      apply ProcTyCompElim.eps_elim (τs' := τ₂) <;> aesop
    case eps_elim τ₁'' τ₁''' τ₁'''' H_transition H_elim H_ind =>
      have H_ind' := H_ind H_skip
      have H_elim' : ProcTyCompElim (ProcTy.seq τ₁'' τ₂) (ProcTy.seq τ₁''' τ₂) := by
        aesop
      apply ProcTyCompElim.eps_elim (τs' := ProcTy.seq τ₁''' τ₂) <;> aesop
end ProcTyCompElim



namespace ProcTyIncompTransition
  lemma reduces_seq :
        ∀ {τ₁ τ₂ τ₁' : ProcTy} {lbl : AbstractTransLabel},
          ProcTyIncompTransition τ₁ lbl τ₁' →
          ProcTyIncompTransition (ProcTy.seq τ₁ τ₂) lbl (ProcTy.seq τ₁' τ₂) := by
    intro τ₁ τ₂ τ₁' lbl H_transition
    have ⟨τ₁'', H_τ₁', H_elim₁⟩ := H_transition
    exists τ₁''.seq τ₂
    constructor
    . apply ProcTyTransition.seq_step
      exact H_τ₁'
    . apply ProcTyCompElim.elim_seq_step
      exact H_elim₁

  lemma reduces_seq_skip :
        ∀ {τ₁ τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ProcTyCompElim τ₁ ProcTy.skip →
          ProcTyIncompTransition τ₂ lbl τ₂' →
          ProcTyIncompTransition (ProcTy.seq τ₁ τ₂) lbl τ₂' := by
    intro τ₁ τ₂ τ₂' lbl H_elim₁ H_transition
    have ⟨τ₂'', H_τ₂', H_elim₂⟩ := H_transition
    exists τ₂''
    constructor
    . exact H_τ₂'
    . apply ProcTyCompElim.elim_seq_skip
      . exact H_elim₁
      . exact H_elim₂

  lemma reduces_par_left :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ¬ lbl.isEx →
          lbl ≠ AbstractTransLabel.ac Action.tock →
          ProcTyIncompTransition τ₁ lbl τ₁' →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂') := by
    intro τ₁ τ₁' τ₂ τ₂' lbl H_non_ex H_not_tock H_transition H_elim
    have ⟨τ₁'', H_τ₁', H_elim₁⟩ := H_transition
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁''.par τ₂') := by
      apply ProcTyCompElim.elim_par
      . exact H_elim₁
      . exact H_elim
    exists τ₁''.par τ₂'
    constructor
    . aesop
    . exact H_τ'

  lemma reduces_par_right :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ¬ lbl.isEx →
          lbl ≠ AbstractTransLabel.ac Action.tock →
          ProcTyCompElim τ₁ τ₁' →
          ProcTyIncompTransition τ₂ lbl τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂') := by
    intro τ₁ τ₁' τ₂ τ₂' lbl H_non_ex H_not_tock H_elim H_transition
    have ⟨τ₂'', H_τ₂', H_elim₂⟩ := H_transition
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁'.par τ₂'') := by
      apply ProcTyCompElim.elim_par
      . exact H_elim
      . exact H_elim₂
    exists τ₁'.par τ₂''
    constructor
    . aesop
    . exact H_τ'

  lemma reduces_par_tock :
        ∀ {τ₁ τ₂ τ₁' τ₂' : ProcTy},
          ProcTyIncompTransition τ₁ (AbstractTransLabel.ac Action.tock) τ₁' →
          ProcTyIncompTransition τ₂ (AbstractTransLabel.ac Action.tock) τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac Action.tock) (ProcTy.par τ₁' τ₂') := by
    intro τ₁ τ₂ τ₁' τ₂' H_transition₁ H_transition₂
    have ⟨τ₁'', H_τ₁', H_elim₁⟩ := H_transition₁
    have ⟨τ₂'', H_τ₂', H_elim₂⟩ := H_transition₂
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁''.par τ₂'') := by
      apply ProcTyCompElim.elim_par
      . exact H_elim₁
      . exact H_elim₂
    exists τ₁''.par τ₂''
    constructor
    . apply ProcTyTransition.par_tock
      . exact H_τ₁'
      . exact H_τ₂'
    . exact H_τ'

  lemma reduces_par_ex_left :
        ∀ {τ₁ τ₁' τ₂ : ProcTy} {ex_msg : Finset (MessageId × MessageDir)},
          ProcTyIncompTransition τ₁ (AbstractTransLabel.ex ex_msg) τ₁' →
          (∀ mx ∈ ex_msg,
            ProcTyNonInstantMsg ∅ ∅ τ₂ mx) →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ex ex_msg) (ProcTy.par τ₁' τ₂) := by
    intro τ₁ τ₁' τ₂ ex_msg H_transition H_noninst_msg
    have ⟨τ₁'', H_τ₁'⟩ := H_transition
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁''.par τ₂) := by
      apply ProcTyCompElim.elim_par
      . exact H_τ₁'.2
      . apply ProcTyCompElim.refl
    exists τ₁''.par τ₂
    constructor
    . apply ProcTyTransition.par_left_ex
      . exact H_noninst_msg
      . exact H_τ₁'.1
    . exact H_τ'

  lemma reduces_par_ex_right :
        ∀ {τ₁ τ₂ τ₂' : ProcTy} {ex_msg : Finset (MessageId × MessageDir)},
          ProcTyIncompTransition τ₂ (AbstractTransLabel.ex ex_msg) τ₂' →
          (∀ mx ∈ ex_msg,
            ProcTyNonInstantMsg ∅ ∅ τ₁ mx) →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ex ex_msg) (ProcTy.par τ₁ τ₂') := by
    intro τ₁ τ₂ τ₂' ex_msg H_transition H_noninst_msg
    have ⟨τ₂'', H_τ₂'⟩ := H_transition
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁.par τ₂'') := by
      apply ProcTyCompElim.elim_par
      . apply ProcTyCompElim.refl
      . exact H_τ₂'.2
    exists τ₁.par τ₂''
    constructor
    . apply ProcTyTransition.par_right_ex
      . exact H_noninst_msg
      . exact H_τ₂'.1
    . exact H_τ'

  lemma reduces_par_message :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {msg : MessageId} {d₁ d₂ : MessageDir},
          MessageDir.dual d₁ d₂ →
          ProcTyIncompTransition τ₁ (AbstractTransLabel.message msg d₁) τ₁' →
          ProcTyIncompTransition τ₂ (AbstractTransLabel.message msg d₂) τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac $ Action.fullMessage msg) (ProcTy.par τ₁' τ₂') := by
    intro τ₁ τ₁' τ₂ τ₂' msg d₁ d₂ H_dual H_trans₁ H_trans₂
    have ⟨τ₁'', H_τ₁'⟩ := H_trans₁
    have ⟨τ₂'', H_τ₂'⟩ := H_trans₂
    have H_τ' : ProcTyCompElim (τ₁.par τ₂) (τ₁''.par τ₂'') := by
      apply ProcTyCompElim.elim_par
      . exact H_τ₁'.2
      . exact H_τ₂'.2
    exists τ₁''.par τ₂''
    constructor
    . apply ProcTyTransition.par_message
      . exact H_dual
      . exact H_τ₁'.1
      . exact H_τ₂'.1
    . exact H_τ'

  lemma reduces_extend_l :
        ∀ {τ₁' τ₁ τ₂ : ProcTy} {lbl : AbstractTransLabel},
          ProcTyIncompTransition τ₁ lbl τ₂ →
          ProcTyCompElim τ₁' τ₁ →
          ProcTyIncompTransition τ₁' lbl τ₂ := by
    intro τ₁' τ₁ τ₂ lbl H_transition H_elim
    have ⟨τ₁'', H_τ₂', H_elim'⟩ := H_transition
    exists τ₁''
    constructor
    . exact H_τ₂'
    . apply ProcTyCompElim.elim_transitivity
      . exact H_elim
      . exact H_elim'

end ProcTyIncompTransition

lemma label_abstraction_preserves_ε : ∀ {lbl : TransLabel},
    (AbstractTransLabel.fromConcrete lbl) = AbstractTransLabel.ε ↔ lbl = TransLabel.ε := by
  intro lbl
  unfold AbstractTransLabel.fromConcrete
  cases lbl <;> simp

lemma label_abstraction_preserves_ex : ∀ {lbl : TransLabel},
    (AbstractTransLabel.fromConcrete lbl).isEx ↔ lbl.isEx := by
  intro lbl
  unfold AbstractTransLabel.isEx
  unfold AbstractTransLabel.fromConcrete
  unfold TransLabel.isEx
  simp
  cases lbl <;> simp

lemma welltyped_expr_evaluates_to_something : ∀ (e : Expr),
  ExprTyJudgement ∅ e →
  ∃ v, e ↓ v := by
  intro e H_typing
  induction H_typing
  case var x H_x =>
    simp at H_x
  case val v₀ =>
    exists v₀
    apply Semantics.ExprEval.literal
  case add e₁ e₂ bop H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    have ⟨v₁, H_v₁⟩ := H_ind₁
    have ⟨v₂, H_v₂⟩ := H_ind₂
    exists valEval v₁ v₂ bop
    apply Semantics.ExprEval.bin <;> assumption

namespace ProcTyGuarded
  lemma larger_context_preserves_guarded
        (τ : ProcTy) (Γₙ Γₙ' Γₘ Γₒ Γₘ' Γₒ' : Finset String) :
        Γₙ ⊆ Γₙ' →
        Γₘ ⊆ Γₘ' →
        Γₒ ⊆ Γₒ' →
        ProcTyGuarded Γₙ Γₘ Γₒ τ →
        ProcTyGuarded Γₙ' Γₘ' Γₒ' τ := by
    intro H_n H_m H_o H_guarded
    induction H_guarded generalizing Γₙ' Γₘ' Γₒ'
    case message_recv | message_send | cycle | skip | dollar => aesop
    case var => aesop
    case seq_instant ih1 ih2 => aesop
    case par ih1 ih2 => aesop
    case choice ih1 ih2 => aesop
    case choice_fair ih1 ih2 => aesop
    case xoffer Γₙ'' Γₘ'' Γₒ'' τ_else branch_tys H_else H_branches H_ind_else H_ind_branches =>
      apply ProcTyGuarded.xoffer
      · exact H_ind_else Γₙ' Γₘ' Γₒ' H_n H_m H_o
      · intro m ty H_mem; exact H_ind_branches m ty H_mem Γₙ' Γₘ' Γₒ' H_n H_m H_o
    case offer Γₙ'' Γₘ'' Γₒ'' τ_else branch_tys H_else H_branches H_ind_else H_ind_branches =>
      apply ProcTyGuarded.offer
      · exact H_ind_else Γₙ' Γₘ' Γₒ' H_n H_m H_o
      · intro m ty H_mem; exact H_ind_branches m ty H_mem Γₙ' Γₘ' Γₒ' H_n H_m H_o
    case seq_noninstant Γₙ'' Γₘ'' Γₒ'' τ₁ τ₂ H_noninst H_g1 H_g2 H_ind1 H_ind2 =>
      apply ProcTyGuarded.seq_noninstant
      · exact larger_context_preserves_noninst _ _ _ H_n H_noninst
      · exact H_ind1 Γₙ' Γₘ' Γₒ' H_n H_m H_o
      · exact H_ind2 Γₙ' Γₘ' Γₘ' H_n H_m H_m
    case recur Γₙ'' Γₘ'' Γₒ'' x body H_g H_ind =>
      apply ProcTyGuarded.recur
      have H_n' : (Γₙ'' \ {x}) ⊆ (Γₙ' \ {x}) := by
        intro z hz
        simp at hz ⊢
        exact ⟨H_n hz.1, hz.2⟩
      exact H_ind (Γₙ' \ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x}) H_n' (by grind) (by grind)
    case recur_noninst Γₙ'' Γₘ'' Γₒ'' x body H_noninst H_g H_ind =>
      apply ProcTyGuarded.recur_noninst
      · exact larger_context_preserves_noninst _ _ _ H_n H_noninst
      · exact H_ind (Γₙ' ∪ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x}) (by grind) (by grind) (by grind)

  lemma recur_extend_context_preserves_guarded
    (x : String) (τ : ProcTy) (Γₙ Γₘ Γₒ : Finset String) :
    ProcTyGuarded Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (ProcTy.recur x τ) →
    ProcTyGuarded Γₙ Γₘ Γₒ (ProcTy.recur x τ) := by
      intro H_guarded
      have H_m : Γₘ ∪ {x} ∪ {x} = Γₘ ∪ {x} := by grind
      have H_o : (Γₒ ∪ {x}) \ {x} = Γₒ \ {x} := by grind
      cases H_guarded <;> (
        rename_i H_guarded
        rewrite [H_m, H_o] at H_guarded
        aesop
      )

  lemma replace_preserves_guarded_gen :
        ∀ (x : String) (τ τ' : ProcTy) (Γₙ Γₘ Γₒ : Finset String),
          Γₒ ⊆ Γₘ →
          (x ∈ Γₙ → ProcTyNonInstant ∅ τ') →
          ProcTyGuarded Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) τ →
          ProcTyGuarded ∅ ∅ ∅ τ' →
          ProcTyGuarded Γₙ Γₘ Γₒ (τ.replaceVar x τ') := by

    intro x τ
    revert x
    induction τ using ProcTy.ind
    case H_recur x' body H_ind =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      by_cases h : x = x'
      case pos =>
        rewrite [h]
        simp
        rewrite [← h] at H_guarded₁
        have H_guarded₁' : ProcTyGuarded Γₙ Γₘ Γₒ (ProcTy.recur x body) := by
          apply recur_extend_context_preserves_guarded
          apply larger_context_preserves_guarded (Γₙ := Γₙ) (Γₘ := Γₘ ∪ {x}) (Γₒ := Γₒ ∪ {x}) <;> grind
        cases H_guarded₁
        case recur H_guarded₁ =>
          aesop
        case recur_noninst H_non_inst H_guarded₁ =>
          aesop
      case neg =>
        simp [h]
        have H_m : Γₘ ∪ {x'} ∪ {x} = Γₘ ∪ {x} ∪ {x'} := by grind
        have H_o : (Γₒ \ {x'}) ∪ {x} = (Γₒ ∪ {x}) \ {x'} := by grind
        cases H_guarded₁
        case recur H_guarded₁ =>
          have H_noninst_x' : x ∈ (Γₙ \ {x'}) → ProcTyNonInstant ∅ τ' := by
            intro Hx
            have : x ∈ Γₙ := by
              simp at Hx
              exact Hx.1
            exact H_noninst_x this
          have H_ind' := H_ind x τ' (Γₙ \ {x'}) (Γₘ ∪ {x'}) (Γₒ \ {x'}) (by grind) (by exact H_noninst_x') (
            by
              rewrite [H_m, H_o]
              exact H_guarded₁
          ) H_guarded₂
          apply ProcTyGuarded.recur
          simpa [ProcTy.replaceVar, h] using H_ind'
        case recur_noninst H_non_inst H_guarded₁ =>
          have H_non_inst' : ProcTyNonInstant Γₙ ((ProcTy.recur x' body).replaceVar x τ') := by
            apply replace_preserves_noninst (Γ := Γₙ)
            . exact H_noninst_x
            . exact H_non_inst
          have H_noninst_x' : x ∈ (Γₙ ∪ {x'}) → ProcTyNonInstant ∅ τ' := by
            intro Hx
            have : x ∈ Γₙ := by
              simp at Hx
              cases Hx with
              | inl hmem => exact hmem
              | inr heq => contradiction
            exact H_noninst_x this
          have H_ind' := H_ind x τ' (Γₙ ∪ {x'}) (Γₘ ∪ {x'}) (Γₒ \ {x'}) (by grind) (by exact H_noninst_x') (
            by
              rewrite [H_m, H_o]
              exact H_guarded₁
          ) H_guarded₂
          apply ProcTyGuarded.recur_noninst
          . simpa [ProcTy.replaceVar, h] using H_non_inst'
          . exact H_ind'
    case H_var x =>
      intro x' τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      rename_i H_x
      by_cases h : x' = x
      case pos =>
        simp [h]
        apply larger_context_preserves_guarded (Γₙ := ∅) (Γₘ := ∅) (Γₒ := ∅) <;> grind
      case neg =>
        simp [h]
        aesop
    case H_cycle | H_skip | H_dollar =>
      unfold ProcTy.replaceVar
      aesop
    case H_choice τ₁ τ₂ H_ind₁ H_ind₂ =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case choice H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        aesop
    case H_choice_fair τ₁ τ₂ b H_ind₁ H_ind₂ =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case choice_fair H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        aesop
    case H_par τ₁ τ₂ H_ind₁ H_ind₂ =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case par H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₙ (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        aesop
    case H_seq τ₁ τ₂ H_ind₁ H_ind₂ =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case seq_instant H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₙ Γₘ Γₒ (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₙ Γₘ Γₒ (by grind) (by exact H_noninst_x) (by grind) H_guarded₂
        aesop
      case seq_noninstant H_noninst H_guarded_l H_guarded_r =>
        have H_ind₁' := H_ind₁ x τ' Γₙ Γₘ Γₒ (by grind) (by exact H_noninst_x) (by exact H_guarded_l) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₙ Γₘ Γₘ (by grind) (by exact H_noninst_x) (
          by exact H_guarded_r
        ) H_guarded₂
        apply ProcTyGuarded.seq_noninstant
        . apply replace_preserves_noninst (Γ := Γₙ)
          . exact H_noninst_x
          . exact H_noninst
        . exact H_ind₁'
        . exact H_ind₂'
    case H_message msg =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁ <;> aesop
    case H_xoffer τ_else branch_tys H_ind_else H_ind_branch =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case xoffer H_else H_branches =>
        apply ProcTyGuarded.xoffer
        · exact H_ind_else x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_else H_guarded₂
        · intro m ty H_mem
          obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x) (τ' := τ') H_mem
          rw [H_eq]
          exact H_ind_branch m ty₀ H_mem₀ x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x
            (H_branches m ty₀ H_mem₀) H_guarded₂
    case H_offer τ_else branch_tys H_ind_else H_ind_branch =>
      intro x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case offer H_else H_branches =>
        apply ProcTyGuarded.offer
        · exact H_ind_else x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x H_else H_guarded₂
        · intro m ty H_mem
          obtain ⟨ty₀, H_mem₀, H_eq⟩ := mem_replaceBranches_inv (x := x) (τ' := τ') H_mem
          rw [H_eq]
          exact H_ind_branch m ty₀ H_mem₀ x τ' Γₙ Γₘ Γₒ H_subset H_noninst_x
            (H_branches m ty₀ H_mem₀) H_guarded₂

  lemma replace_preserves_guarded :
        ∀ (x : String) (τ τ' : ProcTy) (Γₘ Γₒ : Finset String),
          Γₒ ⊆ Γₘ →
          ProcTyGuarded ∅ (Γₘ ∪ {x}) (Γₒ ∪ {x}) τ →
          ProcTyGuarded ∅ ∅ ∅ τ' →
          ProcTyGuarded ∅ Γₘ Γₒ (τ.replaceVar x τ') := by
    intro x τ τ' Γₘ Γₒ H_subset H_guarded H_guarded'
    apply replace_preserves_guarded_gen x τ τ' ∅ Γₘ Γₒ
    · exact H_subset
    · intro Hx
      simp at Hx
    · exact H_guarded
    · exact H_guarded'


  lemma noninst_preserved_under_guarded_intersection :
    ∀ (τ : ProcTy) (Γₙ Γₘ Γₒ : Finset String),
      ProcTyNonInstant Γₙ τ →
      ProcTyGuarded Γₙ Γₘ Γₒ τ →
      ProcTyNonInstant (Γₙ ∩ (Γₘ ∪ Γₒ)) τ := by
    intro τ Γₙ Γₘ Γₒ H_noninst
    revert Γₘ Γₒ
    induction H_noninst
    case cycle => aesop
    case var Γ' x H_x =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      rename_i H_x'
      apply ProcTyNonInstant.var
      grind
    case recur Γ' x τ H_noninst H_ind =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case recur H_guarded₁ H_guarded₂ =>
        have H_ind' := H_ind (Γₘ ∪ {x}) (Γₒ \ {x})
          (
            by
              apply larger_context_preserves_guarded (Γₙ := Γ' \ {x}) (Γₘ := Γₘ ∪ {x}) (Γₒ := Γₒ \ {x}) <;> grind
          )
        simp at H_ind'
        have H : ((Γ' ∪ {x}) ∩ (Γₘ ∪ ({x} ∪ Γₒ))) = (Γ' ∩ (Γₘ ∪ Γₒ)) ∪ {x} := by grind
        rewrite [H] at H_ind'
        apply ProcTyNonInstant.recur
        exact H_ind'
      case recur_noninst H_noninst' H_guard' =>
        have H_ind' := H_ind (Γₘ ∪ {x}) (Γₒ \ {x})
          (
            by
              apply larger_context_preserves_guarded (Γₙ := Γ' ∪ {x}) (Γₘ := Γₘ ∪ {x}) (Γₒ := Γₒ \ {x}) <;> grind
          )
        simp at H_ind'
        have H : ((Γ' ∪ {x}) ∩ (Γₘ ∪ ({x} ∪ Γₒ))) = (Γ' ∩ (Γₘ ∪ Γₒ)) ∪ {x} := by grind
        rewrite [H] at H_ind'
        apply ProcTyNonInstant.recur
        exact H_ind'
    case par_left Γ' τ₁ τ₂ H_noninst H_ind =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case par H_guarded₁ H_guarded₂ =>
        have H_ind' := H_ind Γₘ Γₒ H_guarded₁
        apply ProcTyNonInstant.par_left
        exact H_ind'
    case par_right Γ' τ₁ τ₂ H_noninst H_ind =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case par H_guarded₁ H_guarded₂ =>
        have H_ind' := H_ind Γₘ Γₒ H_guarded₂
        apply ProcTyNonInstant.par_right
        exact H_ind'
    case choice Γ' τ₁ τ₂ H_noninst₁ H_noninst₂ H_ind₁ H_ind₂ =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case choice H_guarded₁ H_guarded₂ =>
        apply ProcTyNonInstant.choice
        · exact H_ind₁ Γₘ Γₒ H_guarded₁
        · exact H_ind₂ Γₘ Γₒ H_guarded₂
    case choice_fair bid Γ' τ₁ τ₂ H_noninst₁ H_noninst₂ H_ind₁ H_ind₂ =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case choice_fair H_guarded₁ H_guarded₂ =>
        apply ProcTyNonInstant.choice_fair
        · exact H_ind₁ Γₘ Γₒ H_guarded₁
        · exact H_ind₂ Γₘ Γₒ H_guarded₂
    case seq_left Γ' τ₁ τ₂ H_noninst H_ind =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case seq_instant H_guarded₁ H_guarded₂ =>
        apply ProcTyNonInstant.seq_left
        exact H_ind Γₘ Γₒ H_guarded₁
      case seq_noninstant H_noninst' H_guarded₁ H_guarded₂ =>
        apply ProcTyNonInstant.seq_left
        exact H_ind Γₘ Γₒ H_guarded₁
    case seq_right Γ' τ₁ τ₂ H_noninst H_ind =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case seq_instant H_guarded₁ H_guarded₂ =>
        apply ProcTyNonInstant.seq_right
        exact H_ind Γₘ Γₒ H_guarded₂
      case seq_noninstant H_noninst' H_guarded₁ H_guarded₂ =>
        have H_guarded₂' : ProcTyGuarded Γ' Γₘ (Γₘ ∪ Γₒ) τ₂ := by
          apply larger_context_preserves_guarded (Γₙ := Γ') (Γₘ := Γₘ) (Γₒ := Γₘ)
          · grind
          · grind
          · grind
          · exact H_guarded₂
        have H_ind' := H_ind Γₘ (Γₘ ∪ Γₒ) H_guarded₂'
        apply ProcTyNonInstant.seq_right
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_idempotent] using H_ind'
    case xoffer Γ' τ_else branch_tys H_noninst_else H_noninst_branches H_ih_else H_ih_branches =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case xoffer H_guarded_else H_guarded_branches =>
        apply ProcTyNonInstant.xoffer
        · exact H_ih_else Γₘ Γₒ H_guarded_else
        · intro m ty H_mem
          exact H_ih_branches m ty H_mem Γₘ Γₒ (H_guarded_branches m ty H_mem)
    case offer Γ' τ_else branch_tys H_noninst_else H_noninst_branches H_ih_else H_ih_branches =>
      intro Γₘ Γₒ H_guarded
      cases H_guarded
      case offer H_guarded_else H_guarded_branches =>
        apply ProcTyNonInstant.offer
        · exact H_ih_else Γₘ Γₒ H_guarded_else
        · intro m ty H_mem
          exact H_ih_branches m ty H_mem Γₘ Γₒ (H_guarded_branches m ty H_mem)


  lemma guarded_intersect_noninst_context :
    ∀ (τ : ProcTy) (Γₙ Γₘ Γₒ : Finset String),
      ProcTyGuarded Γₙ Γₘ Γₒ τ →
      ProcTyGuarded (Γₙ ∩ (Γₘ ∪ Γₒ)) Γₘ Γₒ τ := by
    intro τ Γₙ Γₘ Γₒ H_guarded
    induction H_guarded
    case message_recv | message_send | cycle | skip | dollar
        | var | seq_instant | par | choice | choice_fair => aesop
    case seq_noninstant Γₙ' Γₘ' Γₒ' τ₁ τ₂ H_noninst H_guarded₁ H_guarded₂ H_ind₁ H_ind₂ =>
      apply ProcTyGuarded.seq_noninstant
      . apply noninst_preserved_under_guarded_intersection
        . exact H_noninst
        . exact H_guarded₁
      . exact H_ind₁
      . apply larger_context_preserves_guarded (Γₙ := Γₙ' ∩ (Γₘ' ∪ Γₘ')) (Γₘ := Γₘ') (Γₒ := Γₘ') <;> grind
    case recur Γₙ' Γₘ' Γₒ' x body H_guarded_body H_ind =>
      apply ProcTyGuarded.recur
      have H_body :
          ProcTyGuarded ((Γₙ' ∩ (Γₘ' ∪ Γₒ')) \ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x}) body := by
        apply larger_context_preserves_guarded body
          ((Γₙ' \ {x}) ∩ (Γₘ' ∪ {x} ∪ (Γₒ' \ {x}))) ((Γₙ' ∩ (Γₘ' ∪ Γₒ')) \ {x})
          (Γₘ' ∪ {x}) (Γₒ' \ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x})
        · intro z hz; grind
        · intro z hz; exact hz
        · intro z hz; exact hz
        · exact H_ind
      exact H_body
    case recur_noninst Γₙ' Γₘ' Γₒ' x body H_noninst H_guarded_body H_ind =>
      apply ProcTyGuarded.recur_noninst
      · exact noninst_preserved_under_guarded_intersection
          (τ := ProcTy.recur x body)
          (Γₙ := Γₙ') (Γₘ := Γₘ') (Γₒ := Γₒ')
          H_noninst
          (ProcTyGuarded.recur_noninst Γₙ' Γₘ' Γₒ' x body H_noninst H_guarded_body)
      · have H_body :
            ProcTyGuarded ((Γₙ' ∩ (Γₘ' ∪ Γₒ')) ∪ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x}) body := by
          apply larger_context_preserves_guarded body
            ((Γₙ' ∪ {x}) ∩ (Γₘ' ∪ {x} ∪ (Γₒ' \ {x}))) ((Γₙ' ∩ (Γₘ' ∪ Γₒ')) ∪ {x})
            (Γₘ' ∪ {x}) (Γₒ' \ {x}) (Γₘ' ∪ {x}) (Γₒ' \ {x})
          · intro z hz; grind
          · intro z hz; exact hz
          · intro z hz; exact hz
          · exact H_ind
        exact H_body
    case xoffer Γₙ' Γₘ' Γₒ' τ_else branch_tys H_else H_branches H_ind_else H_ind_branches =>
      apply ProcTyGuarded.xoffer
      · exact H_ind_else
      · intro m ty H_mem
        exact H_ind_branches m ty H_mem
    case offer Γₙ' Γₘ' Γₒ' τ_else branch_tys H_else H_branches H_ind_else H_ind_branches =>
      apply ProcTyGuarded.offer
      · exact H_ind_else
      · intro m ty H_mem
        exact H_ind_branches m ty H_mem

  lemma trans_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy} {lbl : AbstractTransLabel},
          ProcTyGuardedClosed τ₁ →
          ProcTyTransition τ₁ lbl τ₂ →
          ProcTyGuardedClosed τ₂ := by
    intro τ₁ τ₂ lbl H_guarded H_transition
    induction H_transition
    case tock | message_send | message_recv =>
      aesop
    case par_left τ₁ τ₁' τ₂ lbl H_lbl H_non_ex H_trans H_ind =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind' := H_ind H_guarded₁
      apply ProcTyGuarded.par <;> assumption
    case par_right τ₁ τ₂ τ₂' lbl H_lbl H_non_ex H_trans H_ind =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind' := H_ind H_guarded₂
      apply ProcTyGuarded.par <;> assumption
    case par_tock τ₁ τ₂ τ₁' τ₂' H_trans₁ H_trans₂ H_ind₁ H_ind₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind₁' := H_ind₁ H_guarded₁
      have H_ind₂' := H_ind₂ H_guarded₂
      apply ProcTyGuarded.par <;> assumption
    case par_left_ex ex_msg τ₁ τ₁' τ₂' H_mx H_trans₁ H_ind =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind' := H_ind H_guarded₁
      apply ProcTyGuarded.par <;> assumption
    case par_right_ex ex_msg τ₁ τ₂ τ₂' H_mx H_trans₂ H_ind =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind' := H_ind H_guarded₂
      apply ProcTyGuarded.par <;> assumption
    case par_message τ₁ τ₂ τ₁' τ₂' msg d₁ d₂ H_dual H_trans₁ H_trans₂ H_ind₁ H_ind₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      have H_ind₁' := H_ind₁ H_guarded₁
      have H_ind₂' := H_ind₂ H_guarded₂
      apply ProcTyGuarded.par <;> assumption
    case par_skip_left τ₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₂
    case par_skip_right τ₁ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₁
    case seq_step τ₁ τ₁' τ₂ lbl H_trans₁ H_ind =>
      cases H_guarded <;> aesop
    case seq_done =>
      cases H_guarded <;> aesop
    case choice_left τ₁ τ₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₁
    case choice_right τ₁ τ₂ =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₂
    case choice_fair_left τ₁ τ₂ b =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₁
    case choice_fair_right τ₁ τ₂ b =>
      cases H_guarded
      rename_i H_guarded₁ H_guarded₂
      exact H_guarded₂
    case recur_unfold x τ =>
      cases H_guarded
      · rename_i H_g
        apply replace_preserves_guarded
        · grind
        · have H_g' : ProcTyGuarded ∅ (∅ ∪ {x}) (∅ ∪ {x}) τ := by
            have H_g0 : ProcTyGuarded ∅ (∅ ∪ {x}) (∅ \ {x}) τ := by
              simpa using H_g
            exact larger_context_preserves_guarded τ
              ∅ ∅ (∅ ∪ {x}) (∅ \ {x}) (∅ ∪ {x}) (∅ ∪ {x})
              (by aesop)
              (by aesop)
              (by aesop)
              H_g0
          exact H_g'
        · aesop
      · rename_i H_non_inst H_g
        have H_gx : ProcTyGuarded {x} ({x}) ({x}) τ := by
          exact larger_context_preserves_guarded τ
            ({x}) ({x}) ({x}) (∅) ({x}) ({x})
            (by grind)
            (by grind)
            (by grind)
            H_g
        have H_rep_x : ProcTyGuarded ({x}) ∅ ∅ (τ.replaceVar x (ProcTy.recur x τ)) := by
          apply replace_preserves_guarded_gen
            (x := x) (τ := τ) (τ' := ProcTy.recur x τ)
            (Γₙ := ({x})) (Γₘ := ∅) (Γₒ := ∅)
          · grind
          · intro _
            exact H_non_inst
          · simpa using H_gx
          · exact ProcTyGuarded.recur_noninst ∅ ∅ ∅ x τ H_non_inst H_g
        have H_closed : ProcTyGuarded ∅ ∅ ∅ (τ.replaceVar x (ProcTy.recur x τ)) := by
          simpa using (guarded_intersect_noninst_context
            (τ := τ.replaceVar x (ProcTy.recur x τ))
            (Γₙ := ({x})) (Γₘ := ∅) (Γₒ := ∅)
            H_rep_x)
        exact H_closed
    case xoffer_else ex_msg τ_else branch_tys _H_cond =>
      cases H_guarded
      rename_i H_else _H_branches
      exact H_else
    case offer_else ex_msg τ_else branch_tys _H_cond =>
      cases H_guarded
      rename_i H_else _H_branches
      exact H_else
    case xoffer_branch τ_else branch_tys me ty H_mem =>
      cases H_guarded
      rename_i _H_else H_branches
      exact H_branches me ty H_mem
    case offer_branch τ_else branch_tys idx branch_tys' me ty ty' H_brtys_eq H_ty'_eq H_idx =>
      cases H_guarded
      rename_i _H_else H_branches
      subst H_brtys_eq; subst H_ty'_eq
      have H_ty_g : ProcTyGuardedClosed ty :=
        H_branches me ty (Trivia.list_insert_idx branch_tys ↑idx (me, ty) (Nat.lt_succ_iff.mp H_idx))
      have mem_ins : ∀ {α : Type} (l : List α) (n : ℕ) (v x : α),
          x ∈ l → x ∈ l.insertIdx n v := by
        intro α l; induction l with
        | nil => intro n v x H_mem; simp at H_mem
        | cons h t ih =>
          intro n v x H_mem
          cases n with
          | zero => exact List.mem_cons_of_mem _ H_mem
          | succ m =>
            simp only [List.insertIdx]
            exact List.mem_cons.mpr ((List.mem_cons.mp H_mem).imp_right (ih m v x))
      suffices h_foldl : ∀ (τs : List ProcTy), (∀ τ ∈ τs, ProcTyGuardedClosed τ) →
          ∀ τ₀, ProcTyGuardedClosed τ₀ →
          ProcTyGuardedClosed (List.foldl (fun acc τ => ProcTy.par acc τ) τ₀ τs) by
        apply h_foldl
        · intro τ H_mem_τ
          simp only [List.mem_cons] at H_mem_τ
          rcases H_mem_τ with (rfl | H_mem_τ)
          · exact H_ty_g
          · obtain ⟨⟨m_i, ty_i⟩, H_mem_i, H_eq⟩ := List.mem_map.mp H_mem_τ
            rw [← H_eq]
            have H_ti_g : ProcTyGuardedClosed ty_i :=
              H_branches m_i ty_i (mem_ins branch_tys ↑idx (me, ty) (m_i, ty_i) H_mem_i)
            simp only [branch_to_xoffer_ty]
            exact ProcTyGuarded.xoffer ∅ ∅ ∅ ProcTy.skip [(m_i, ty_i)]
              (ProcTyGuarded.skip ∅ ∅ ∅)
              (fun m t H_in => by
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at H_in
                obtain ⟨rfl, rfl⟩ := H_in
                exact H_ti_g)
        · exact ProcTyGuarded.skip ∅ ∅ ∅
      intro τs; induction τs with
      | nil => exact fun _ _ h => h
      | cons τ₁ rest ih =>
        intro H_all τ₀ H₀
        simp only [List.foldl_cons]
        apply ih (fun τ hm => H_all τ (List.mem_cons_of_mem _ hm))
        exact ProcTyGuarded.par ∅ ∅ ∅ τ₀ τ₁ H₀ (H_all τ₁ (List.mem_cons.mpr (Or.inl rfl)))

  lemma elim_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy},
          ProcTyGuardedClosed τ₁ →
          ProcTyCompElim τ₁ τ₂ →
          ProcTyGuardedClosed τ₂ := by
    intro τ₁ τ₂ H_guarded H_elim
    induction H_elim
    case refl τ' =>
      exact H_guarded
    case eps_elim τ' τ'' τ''' H_transition H_elim H_ind =>
      apply H_ind
      apply trans_preserves_guarded (τ₁ := τ') (lbl := AbstractTransLabel.ε)
      . exact H_guarded
      . exact H_transition

  lemma incomp_trans_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy} {lbl : AbstractTransLabel},
          ProcTyGuardedClosed τ₁ →
          ProcTyIncompTransition τ₁ lbl τ₂ →
          ProcTyGuardedClosed τ₂ := by
    intro τ₁ τ₂ lbl H_guarded H_transition
    have ⟨τ', H_trans, H_elim⟩ := H_transition
    apply trans_preserves_guarded (τ₁ := τ') (lbl := lbl)
    . apply elim_preserves_guarded (τ₁ := τ₁)
      . exact H_guarded
      . exact H_elim
    . exact H_trans

end ProcTyGuarded
