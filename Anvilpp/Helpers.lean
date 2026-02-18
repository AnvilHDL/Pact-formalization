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
      l₁.length ≤ l₂.length → v₁ ∈ l₁ → ∃ v₂, (v₁, v₂) ∈ List.zip l₁ l₂ := by sorry -- obvious

  lemma zip_list_split : ∀ {T U : Type} (ll₁ rl₁ : List T) (e₁ : T) (l₂ : List U),
      (ll₁ ++ e₁ :: rl₁).length = l₂.length →
      ∃ (ll₂ rl₂ : List U) (e₂ : U),
        l₂ = ll₂ ++ e₂ :: rl₂ ∧ (ll₁ ++ e₁ :: rl₁).zip l₂ = List.zip ll₁ ll₂ ++ [(e₁, e₂)] ++ List.zip rl₁ rl₂
          ∧ ll₁.length = ll₂.length ∧ rl₁.length = rl₂.length := by sorry -- obvious

  lemma zip_list_split₂ : ∀ {T U : Type} (ll₁ rl₁ : List T) (e₁ : T) (ll₂ rl₂ : List U) (e₂ : U),
      ll₁.length = ll₂.length → rl₁.length = rl₂.length →
      (ll₁ ++ e₁ :: rl₁).zip (ll₂ ++ e₂ :: rl₂) = List.zip ll₁ ll₂ ++ [(e₁, e₂)] ++ List.zip rl₁ rl₂ := by sorry -- obvious

  lemma list_insert_idx : ∀ {T : Type} (l : List T) (idx : ℕ) (v : T),
      idx ≤ l.length →
        v ∈ l.insertIdx idx v := by sorry -- obvious
end Trivia

/-- A type variable is absent from a process type. -/
inductive AbsentIn : String → ProcTy → Prop where
  | var (x x' : String) :
    x ≠ x' →
    AbsentIn x (ProcTy.var x')
  | message (x : String) (me : MessageExch) :
    AbsentIn x (ProcTy.message me)
  | cycle (x : String) :
    AbsentIn x ProcTy.cycle
  | skip (x : String) :
    AbsentIn x ProcTy.skip
  | dollar (x : String) (pid : ProcId) :
    AbsentIn x (ProcTy.dollar pid)
  | choice (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.choice τ₁ τ₂)
  | choice_fair (x : String) (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.choice_fair bid τ₁ τ₂)
  | par (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.par τ₁ τ₂)
  | seq (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AbsentIn x τ₂ →
    AbsentIn x (ProcTy.seq τ₁ τ₂)
  | xoffer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AbsentIn x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AbsentIn x ty) →
    AbsentIn x (ProcTy.xoffer τ_else branch_tys)
  | offer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AbsentIn x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AbsentIn x ty) →
    AbsentIn x (ProcTy.offer τ_else branch_tys)
  | recur (x x' : String) (body : ProcTy) :
    x ≠ x' →
    AbsentIn x body →
    AbsentIn x (ProcTy.recur x' body)

/-- A type variable appears only at tail locations or is absent. -/
inductive AtTail : String → ProcTy → Prop where
  -- For par we only allow absence
  | absent (x : String) (τ : ProcTy) :
    AbsentIn x τ →
    AtTail x τ
  | seq (x : String) (τ₁ τ₂ : ProcTy) :
    AbsentIn x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.seq τ₁ τ₂)
  | choice (x : String) (τ₁ τ₂ : ProcTy) :
    AtTail x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.choice τ₁ τ₂)
  | choice_fair (x : String) (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    AtTail x τ₁ →
    AtTail x τ₂ →
    AtTail x (ProcTy.choice_fair bid τ₁ τ₂)
  | xoffer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AtTail x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AtTail x ty) →
    AtTail x (ProcTy.xoffer τ_else branch_tys)
  | offer (x : String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    AtTail x τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → AtTail x ty) →
    AtTail x (ProcTy.offer τ_else branch_tys)
  | recur (x x' : String) (body : ProcTy) :
    x ≠ x' →
    AtTail x body →
    AtTail x (ProcTy.recur x' body)

lemma non_instant_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (Γ : Finset String),
        ProcTyJudgement ctx p τ → (ProcTyNonInstant Γ τ ↔ Semantics.NonInstantReducible Γ p) := by

    sorry -- trivial

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

lemma larger_context_preserves_noninst (τ : ProcTy) (Γ Γ' : Finset String) :
    Γ ⊆ Γ' →
    ProcTyNonInstant Γ τ →
    ProcTyNonInstant Γ' τ := by sorry -- trivial

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
    case xoffer => sorry -- low priority
    case offer => sorry -- low priority

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

lemma non_instant_msg_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext),
        ProcTyJudgement ctx p τ → ∀ mx Γₙ Γₘ, (ProcTyNonInstantMsg Γₙ Γₘ τ mx → Semantics.NonInstantMessage Γₙ Γₘ p mx) := by
  intro p τ ctx H_typing
  -- generalize H_ctx : ProcTyContext.empty = ctx at H_typing
  induction H_typing <;> (intro mx Γₙ Γₘ H_noninst_msg)
  case cycle ctx => aesop
  case dollar ctx pid => aesop
  case skip ctx => aesop
  case message_send =>
    cases H_noninst_msg <;> aesop
  case message_recv ctx msg x p τ H_typing H_ind =>
    cases H_noninst_msg
    case seq_left H_noninst H_noninst_msg =>
      cases H_noninst
    case seq_right H_noninst H_noninst_msg =>
      have H_ind' := H_ind mx Γₙ Γₘ H_noninst_msg
      cases H_noninst <;> aesop
  case par ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case seq ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    case seq_left H_noninst H_noninst_msg =>
      have H_ind₁' := H_ind₁ mx Γₙ Γₘ H_noninst_msg
      have H_noninst₁ : Semantics.NonInstantReducible Γₙ p₁ := by
        rewrite [← non_instant_preservation p₁ τ₁ (Γ := Γₙ) (ctx := ctx)]
        all_goals assumption
      aesop
    case seq_right H_noninst_msg₁ H_noninst_msg₂ =>
      have H_ind₁' := H_ind₁ mx Γₙ Γₘ H_noninst_msg₁
      have H_ind₂' := H_ind₂ mx Γₙ Γₘ H_noninst_msg₂
      aesop
  case choice ctx e p₁ p₂ τ₁ τ₂ H_expr_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case choice_fair ctx e p₁ p₂ τ₁ τ₂ b H_expr_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case var ctx x =>
    cases H_noninst_msg
    aesop
  case recur ctx x body τ_body H_typing H_ind =>
    cases H_noninst_msg
    case recur_instant H_noninst H_noninst_msg =>
      cases H_noninst
      have H_ind' := H_ind mx (Γₙ ∪ {x}) (Γₘ ∪ {x}) H_noninst_msg
      apply Semantics.NonInstantMessage.recur_instant
      . rewrite [← non_instant_preservation (Γ := Γₙ) (τ := ProcTy.recur x τ_body)]  <;> try assumption
        . apply ProcTyNonInstant.recur
          assumption
        . apply ProcTyJudgement.recur
          exact H_typing
      . exact H_ind'
    case recur_noninstant H_noninst_msg =>
      apply Semantics.NonInstantMessage.recur_noninstant
      apply H_ind
      exact H_noninst_msg
  case subtype ctx p τ₁ τ₂ H_typing H_sub H_ind =>
    apply H_ind
    apply subtype_non_instant_msg_preservation (τ₂ := τ₂) <;> assumption
  case xoffer => sorry -- low priority
  case offer => sorry -- low priority

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

lemma larger_context_preserves_typing :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx ctx' : ProcTyContext),
      ctx.procVars ⊆ ctx'.procVars →
      ctx.exprVars ⊆ ctx'.exprVars →
      ProcTyJudgement ctx p τ →
      ProcTyJudgement ctx' p τ := by

  intro p τ ctx ctx' H_proc_subset H_expr_subset H_typing
  revert ctx'
  induction H_typing
  case cycle | dollar | skip | message_send | seq | par | choice | choice_fair | var => aesop
  case recur ctx x body τ_body H_typing H_ind =>
    intro ctx' H_proc_subset H_expr_subset
    apply ProcTyJudgement.recur
    apply H_ind
    . unfold ProcTyContext.extendProcVar
      grind
    . unfold ProcTyContext.extendProcVar
      grind
  case message_recv ctx msg x p τ H_typing H_ind =>
    intro ctx' H_proc_subset H_expr_subset
    apply ProcTyJudgement.message_recv
    apply H_ind
    . unfold ProcTyContext.extendExprVar
      grind
    . unfold ProcTyContext.extendExprVar
      grind
  case subtype ctx p τ₁ τ₂ H_typing H_sub H_ind =>
    intro ctx' H_proc_subset H_expr_subset
    apply ProcTyJudgement.subtype (τ₁ := τ₁)
    . apply H_ind
      exact H_proc_subset
      exact H_expr_subset
    . exact H_sub
  case xoffer => sorry
  case offer => sorry -- low priority

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
  case H_xoffer => sorry -- low prority
  case H_offer => sorry -- low priority

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
    case xoffer => sorry -- low priority
    case offer => sorry -- low priority


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

lemma recursion_unfolding_preserved :
      ∀ (p p' : Semantics.ProcComp) (τ τ' : ProcTyComposition) (ctx : ProcTyContext) (x : String),
        ProcTyJudgement (ctx.extendProcVar x) p τ →
        ProcTyJudgement ctx p' τ' →
        ProcTyJudgement ctx (Semantics.procReplace p x p') (τ.replaceVar x τ') := by

  intro p p' τ τ' ctx x H_typing H_typing'
  generalize H_ctx : ctx.extendProcVar x = ctx' at H_typing
  revert x ctx τ' p'
  induction H_typing <;> (intro p' τ' ctx x H_typing' H_ctx; unfold Semantics.procReplace ProcTy.replaceVar)
  case cycle | dollar | skip | message_send | seq | par | choice | choice_fair =>
    aesop
  case var ctx'' x' H_x =>
    by_cases h : x' = x
    case pos =>
      rewrite [h]
      simp
      rewrite [← H_ctx] at H_x
      aesop
    case neg =>
      simp [h]
      rewrite [← H_ctx] at H_x
      unfold ProcTyContext.extendProcVar at H_x
      simp at H_x
      cases H_x
      case inr H_x => grind
      case inl H_x => aesop
  case recur ctx'' x' p_body τ_body H_typing_body H_ind =>
    by_cases h : x' = x
    case pos =>
      simp [h]
      apply ProcTyJudgement.recur
      rewrite [h] at H_typing_body
      rewrite [← H_ctx] at H_typing_body
      rewrite [← procty_double_extend_does_nothing] at H_typing_body
      exact H_typing_body
    case neg =>
      have H : x ≠ x' := by grind
      simp [H, h]
      apply ProcTyJudgement.recur
      apply H_ind
      . apply larger_context_preserves_typing (ctx := ctx)
        . unfold ProcTyContext.extendProcVar
          grind
        . unfold ProcTyContext.extendProcVar
          grind
        . exact H_typing'
      . rewrite [← H_ctx]
        unfold ProcTyContext.extendProcVar
        grind
  case message_recv ctx'' msg x' p'' τ'' H_typing H_ind =>
    conv =>
      arg 3
      arg 1
      unfold ProcTy.replaceVar
    apply ProcTyJudgement.message_recv
    apply H_ind
    . apply larger_context_preserves_typing (ctx := ctx)
      . unfold ProcTyContext.extendExprVar
        grind
      . unfold ProcTyContext.extendExprVar
        grind
      . exact H_typing'
    . rewrite [← H_ctx]
      unfold ProcTyContext.extendExprVar ProcTyContext.extendProcVar
      grind
  case subtype ctx'' p'' τ₁'' τ₂'' H_typing H_sub H_ind =>
    have H_ind' := H_ind p' τ' ctx x H_typing' H_ctx
    have H_sub' : ProcTySub (τ₁''.replaceVar x τ') (τ₂''.replaceVar x τ') := by
      apply subtyping_replace_procty_preserved
      exact H_sub
    have H : ProcTyJudgement ctx (Semantics.procReplace p'' x p') (τ₂''.replaceVar x τ') := by
      apply ProcTyJudgement.subtype
      . exact H_ind'
      . exact H_sub'
    unfold Semantics.procReplace at H
    unfold ProcTy.replaceVar at H
    exact H
  case xoffer => sorry
  case offer => sorry -- low priority

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


lemma val_replacement_preserves_typing :
      ∀ (ctx : ProcTyContext) (p : Semantics.ProcComp) (τ : ProcTyComposition) (x : String) (v : Bool),
        ProcTyJudgement (ctx.extendExprVar x) p τ →
        ProcTyJudgement ctx (Semantics.procExprReplace p x v) τ := by
  intro ctx p τ x v H_typing
  generalize H_ctx : ctx.extendExprVar x = ctx' at H_typing
  revert ctx
  induction H_typing <;> intro ctx''' H_ctx
  case cycle ctx' =>
    unfold Semantics.procExprReplace
    aesop
  case dollar ctx' pid =>
    unfold Semantics.procExprReplace
    aesop
  case skip ctx' =>
    unfold Semantics.procExprReplace
    aesop
  case message_send ctx'' msg e H_ind =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.message_send
    apply val_replacement_preserves_expr_typing
    rewrite [← H_ctx] at H_ind
    unfold ProcTyContext.extendExprVar at H_ind
    simp at H_ind
    exact H_ind
  case message_recv ctx'' msg x' p τ H_typing H_ind =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.message_recv
    . rewrite [← H_ctx] at H_ind
      unfold ProcTyContext.extendExprVar at H_ind
      simp at H_ind
      by_cases h : x = x'
      case pos =>
        rewrite [h]
        simp
        rewrite [← H_ctx] at H_typing
        rewrite [h] at H_typing
        unfold ProcTyContext.extendExprVar at H_typing
        simp at H_typing
        unfold ProcTyContext.extendExprVar
        exact H_typing
      case neg =>
        simp [h]
        rewrite [← H_ctx] at H_typing
        apply H_ind
        . unfold ProcTyContext.extendExprVar
          simp
        . unfold ProcTyContext.extendExprVar
          grind
  case par ctx' p1 p2 τ1 τ2 H_typing1 H_typing2 H_ind1 H_ind2 =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.par
    . rewrite [← H_ctx] at H_ind1
      apply H_ind1
      unfold ProcTyContext.extendExprVar
      simp
    . rewrite [← H_ctx] at H_ind2
      apply H_ind2
      unfold ProcTyContext.extendExprVar
      simp
  case seq ctx' p1 p2 τ1 τ2 H_typing1 H_typing2 H_ind1 H_ind2 =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.seq
    . rewrite [← H_ctx] at H_ind1
      apply H_ind1
      unfold ProcTyContext.extendExprVar
      simp
    . rewrite [← H_ctx] at H_ind2
      apply H_ind2
      unfold ProcTyContext.extendExprVar
      simp
  case choice ctx' e p1 p2 τ1 τ2 H_expr_typing H_typing1 H_typing2 H_ind1 H_ind2 =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.choice
    . apply val_replacement_preserves_expr_typing
      rewrite [← H_ctx] at H_expr_typing
      unfold ProcTyContext.extendExprVar at H_expr_typing
      simp at H_expr_typing
      exact H_expr_typing
    . rewrite [← H_ctx] at H_ind1
      apply H_ind1
      unfold ProcTyContext.extendExprVar
      simp
    . rewrite [← H_ctx] at H_ind2
      apply H_ind2
      unfold ProcTyContext.extendExprVar
      simp
  case choice_fair ctx' e p1 p2 τ1 τ2 b H_expr_typing H_typing1 H_typing2 H_ind1 H_ind2 =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.choice_fair
    . apply val_replacement_preserves_expr_typing
      rewrite [← H_ctx] at H_expr_typing
      unfold ProcTyContext.extendExprVar at H_expr_typing
      simp at H_expr_typing
      exact H_expr_typing
    . rewrite [← H_ctx] at H_ind1
      apply H_ind1
      unfold ProcTyContext.extendExprVar
      simp
    . rewrite [← H_ctx] at H_ind2
      apply H_ind2
      unfold ProcTyContext.extendExprVar
      simp
  case var ctx' x' =>
    unfold Semantics.procExprReplace
    aesop
  case recur ctx' x' body τ_body H_typing H_ind =>
    unfold Semantics.procExprReplace
    apply ProcTyJudgement.recur
    rewrite [← H_ctx] at H_ind
    apply H_ind
    unfold ProcTyContext.extendExprVar
    unfold ProcTyContext.extendProcVar
    simp
  case subtype ctx' p τ₁ τ₂ H_typing H_sub H_ind =>
    apply ProcTyJudgement.subtype (τ₁ := τ₁)
    . apply H_ind
      exact H_ctx
    . exact H_sub
  case xoffer => sorry -- low priority
  case offer => sorry -- low priority


lemma par_list_ty : ∀ (procs : List Proc) (tys : List ProcTy),
    (H_len : procs.length = tys.length) →
    (∀ p τ, (p, τ) ∈ List.zip procs tys → ProcTyJudgement ProcTyContext.empty p τ) →
    ProcTyJudgement ProcTyContext.empty (procs.foldl (fun acc p => Proc.par acc p) Proc.skip) (tys.foldl (fun acc τ => ProcTy.par acc τ) ProcTy.skip) :=
      by sorry -- obvious


namespace Semantics.CompElim
  lemma comp_elim_preseves_skip : ∀ {p : Semantics.ProcComp},
                                  CompElim Proc.skip p → p = Proc.skip := by
    intro p H_elim
    generalize H_skip : Proc.skip = p at H_elim
    induction H_elim
    case refl =>
      rfl
    case eps_elim =>
      rename Reduces _ _ _ => H_reduces
      rewrite [← H_skip] at H_reduces
      cases H_reduces

  lemma comp_elim_preserves_recv : ∀ {msg : MessageId}
      {x : String} {p p' : Semantics.ProcComp},
        CompElim (Proc.recv msg x p) p' →
        p' = Proc.recv msg x p := by
    intro msg x p p' H_elim
    generalize H_recv : Proc.recv msg x p = p' at H_elim
    induction H_elim
    case refl =>
      rfl
    case eps_elim =>
      rename Reduces _ _ _ => H_reduces
      rewrite [← H_recv] at H_reduces
      cases H_reduces

  lemma comp_elim_preserves_send : ∀ {msg : MessageId} {e : Expr}
      {p : Semantics.ProcComp},
        CompElim (Proc.send msg e) p →
        p = Proc.send msg e := by
    intro msg e p H_elim
    generalize H_send : Proc.send msg e = p at H_elim
    induction H_elim
    case refl =>
      rfl
    case eps_elim =>
      rename Reduces _ _ _ => H_reduces
      rewrite [← H_send] at H_reduces
      cases H_reduces

  lemma comp_elim_seq_step : ∀ {p₁ p₁' p₂ : Semantics.ProcComp},
      CompElim p₁ p₁' →
      CompElim (Proc.seq p₁ p₂) (Proc.seq p₁' p₂) := by
    intro p₁ p₁' p₂ H_elim
    induction H_elim
    case refl =>
      apply CompElim.refl
    case eps_elim p p' p'' H_red H_elim H_elim' =>
      apply CompElim.eps_elim (p' := Proc.seq p' p₂)
      . aesop
      . exact H_elim'

end Semantics.CompElim

namespace Semantics.IncompReduces
  lemma reduces_implies_incomp_reduces :
        ∀ {p₁ p₂ : Semantics.ProcComp} {lbl : TransLabel},
          Semantics.Reduces p₁ lbl p₂ →
          Semantics.IncompReduces p₁ lbl p₂ := by
    intro p₁ p₂ lbl H_reduces
    unfold IncompReduces
    exists p₁
    constructor
    . exact H_reduces
    . apply Semantics.CompElim.refl

  lemma seq_reduces :
    ∀ {p₁ p₁' p₂ : Semantics.ProcComp} {lbl : TransLabel},
      Semantics.IncompReduces p₁ lbl p₁' →
      Semantics.IncompReduces (Proc.seq p₁ p₂) lbl (Proc.seq p₁' p₂) := by
      intro p₁ p₁' p₂ lbl H_incomp_reduces
      unfold IncompReduces at H_incomp_reduces
      have ⟨p₁'', H_incomp_reduces'⟩ := H_incomp_reduces
      exists (Proc.seq p₁'' p₂)
      constructor
      . aesop
      . apply CompElim.comp_elim_seq_step
        exact H_incomp_reduces'.2

  lemma par_non_ex_left :
    ∀ {p₁ p₁' p₂ : Semantics.ProcComp} {lbl : TransLabel},
      ¬ lbl.isEx →
      lbl ≠ TransLabel.ac Action.tock →
      Semantics.IncompReduces p₁ lbl p₁' →
      Semantics.IncompReduces (Proc.par p₁ p₂) lbl (Proc.par p₁' p₂) := by
      intro p₁ p₁' p₂ lbl H_non_ex H_not_tock H_incomp_reduces
      unfold IncompReduces at H_incomp_reduces
      have ⟨p₁'', H_incomp_reduces'⟩ := H_incomp_reduces
      exists (Proc.par p₁'' p₂)
      constructor
      . aesop
      . sorry -- trivial

  lemma par_non_ex_right :
    ∀ {p₁ p₂ p₂' : Semantics.ProcComp} {lbl : TransLabel},
      ¬ lbl.isEx →
      lbl ≠ TransLabel.ac Action.tock →
      Semantics.IncompReduces p₂ lbl p₂' →
      Semantics.IncompReduces (Proc.par p₁ p₂) lbl (Proc.par p₁ p₂') := by
      intro p₁ p₂ p₂' lbl H_non_ex H_not_tock H_incomp_reduces
      unfold IncompReduces at H_incomp_reduces
      have ⟨p₂'', H_incomp_reduces'⟩ := H_incomp_reduces
      exists (Proc.par p₁ p₂'')
      constructor
      . aesop
      . sorry -- trivial

  lemma par_ex_left :
    ∀ {p₁ p₁' p₂ : Semantics.ProcComp} {ex_msg : Finset (MessageId × MessageDir)},
      Semantics.IncompReduces p₁ (TransLabel.ex ex_msg) p₁' →
      (∀ mx ∈ ex_msg,
        Semantics.NonInstantMessage ∅ ∅ p₂ mx) →
      Semantics.IncompReduces (Proc.par p₁ p₂) (TransLabel.ex ex_msg) (Proc.par p₁' p₂) := by
      sorry -- trivial

  lemma par_ex_right :
    ∀ {p₁ p₂ p₂' : Semantics.ProcComp} {ex_msg : Finset (MessageId × MessageDir)},
      Semantics.IncompReduces p₂ (TransLabel.ex ex_msg) p₂' →
      (∀ mx ∈ ex_msg,
        Semantics.NonInstantMessage ∅ ∅ p₁ mx) →
      Semantics.IncompReduces (Proc.par p₁ p₂) (TransLabel.ex ex_msg) (Proc.par p₁ p₂') := by
      sorry -- trivial

  lemma par_tock :
    ∀ {p₁ p₁' p₂ p₂' : Semantics.ProcComp},
      Semantics.IncompReduces p₁ (TransLabel.ac Action.tock) p₁' →
      Semantics.IncompReduces p₂ (TransLabel.ac Action.tock) p₂' →
      Semantics.IncompReduces (Proc.par p₁ p₂) (TransLabel.ac Action.tock) (Proc.par p₁' p₂') := by
      sorry -- trivial

  lemma par_message :
    ∀ {p₁ p₁' p₂ p₂' : Semantics.ProcComp} {msg : MessageId} {d₁ d₂ : MessageDir} {v₁ v₂ : Bool},
      MessageDir.dual d₁ d₂ →
      -- note that we weaken the condition on the values as if the receiver side can receive at all, it can receive any value
      Semantics.IncompReduces p₁ (TransLabel.message msg d₁ v₁) p₁' →
      Semantics.IncompReduces p₂ (TransLabel.message msg d₂ v₂) p₂' →
      Semantics.IncompReduces (Proc.par p₁ p₂) (TransLabel.ac $ Action.fullMessage msg) (Proc.par p₁' p₂') := by
        sorry -- trivial

  lemma extend_l :
        ∀ {p₁ p₁' p₂ : Semantics.ProcComp} {lbl : TransLabel},
          Semantics.CompElim p₁ p₁' →
          Semantics.IncompReduces p₁' lbl p₂ →
          Semantics.IncompReduces p₁ lbl p₂ := by sorry -- trivial
end Semantics.IncompReduces

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
        Γₘ \ Γₙ ⊆ Γₘ' \ Γₙ' →
        Γₘ ⊆ Γₘ' →
        Γₒ ⊆ Γₒ' →
        ProcTyGuarded Γₙ Γₘ Γₒ τ →
        ProcTyGuarded Γₙ' Γₘ' Γₒ' τ := by sorry -- trivial

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

  lemma replace_preserves_guarded :
        ∀ (x : String) (τ τ' : ProcTy) (Γₘ Γₒ : Finset String),
          Γₒ ⊆ Γₘ →
          ProcTyGuarded ∅ (Γₘ ∪ {x}) (Γₒ ∪ {x}) τ →
          ProcTyGuarded ∅ ∅ ∅ τ' →
          ProcTyGuarded ∅ Γₘ Γₒ (τ.replaceVar x τ') := by

    intro x τ
    revert x
    induction τ using ProcTy.ind
    case H_recur x' body H_ind =>
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      by_cases h : x = x'
      case pos =>
        rewrite [h]
        simp
        rewrite [← h] at H_guarded₁
        have H_guarded₁' : ProcTyGuarded ∅ Γₘ Γₒ (ProcTy.recur x body) := by
          apply recur_extend_context_preserves_guarded
          apply larger_context_preserves_guarded (Γₙ := ∅) (Γₘ := Γₘ ∪ {x}) (Γₒ := Γₒ ∪ {x}) <;> grind
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
          have H_ind' := H_ind x τ' (Γₘ ∪ {x'}) (Γₒ \ {x'}) (by grind) (
            by
              rewrite [H_m, H_o]
              exact H_guarded₁
          ) H_guarded₂
          aesop
        case recur_noninst H_non_inst H_guarded₁ =>
          have H_ind' := H_ind x τ' (Γₘ ∪ {x'}) (Γₒ \ {x'}) (by grind) (
            by
              rewrite [H_m, H_o]
              apply larger_context_preserves_guarded (Γₙ := ∅ ∪ {x'}) (Γₘ := (Γₘ ∪ {x} ∪ {x'})) (Γₒ := ((Γₒ ∪ {x}) \ {x'})) <;> grind
          ) H_guarded₂
          aesop
    case H_var x =>
      intro x' τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
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
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case choice H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        aesop
    case H_choice_fair τ₁ τ₂ b H_ind₁ H_ind₂ =>
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case choice_fair H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        aesop
    case H_par τ₁ τ₂ H_ind₁ H_ind₂ =>
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case par H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' (Γₘ ∪ {x}) (Γₒ ∪ {x}) (by grind) (by grind) H_guarded₂
        aesop
    case H_seq τ₁ τ₂ H_ind₁ H_ind₂ =>
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁
      case seq_instant H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₘ Γₒ (by grind) (by grind) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₘ Γₒ (by grind) (by grind) H_guarded₂
        aesop
      case seq_noninstant H_guarded' H_guarded₁ =>
        have H_ind₁' := H_ind₁ x τ' Γₘ Γₒ (by grind) (by aesop) H_guarded₂
        have H_ind₂' := H_ind₂ x τ' Γₘ Γₘ (by grind) (
          by exact H_guarded₁
        ) H_guarded₂
        apply ProcTyGuarded.seq_noninstant
        . apply replace_preserves_noninst (Γ := ∅) <;> grind
        . exact H_ind₁'
        . exact H_ind₂'
    case H_message msg =>
      intro x τ' Γₘ Γₒ H_subset H_guarded₁ H_guarded₂
      unfold ProcTy.replaceVar
      cases H_guarded₁ <;> aesop
    case H_xoffer => sorry -- low priority
    case H_offer => sorry -- low priority

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
      apply replace_preserves_guarded
      . grind
      . cases H_guarded
        . apply larger_context_preserves_guarded (Γₙ := ∅) (Γₘ := ∅ ∪ {x}) (Γₒ := ∅ \ {x}) <;> grind
        . apply larger_context_preserves_guarded (Γₙ := ∅ ∪ {x}) (Γₘ := ∅ ∪ {x}) (Γₒ := ∅ \ {x}) <;> grind
      . aesop
    case xoffer_else => sorry -- low priority
    case offer_else => sorry
    case xoffer_branch => sorry
    case offer_branch => sorry

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

  lemma guarded_preserves_non_instant_msg :
    ∀ (ctx : ProcTyContext) (p : Semantics.ProcComp) (τ : ProcTyComposition)
      (mx : MessageId × MessageDir) (Γₙ Γₘ : Finset String),
      ProcTyJudgement ctx p τ →
      -- ProcTyGuardedClosed τ →
      Semantics.NonInstantMessage Γₙ Γₘ p mx →
      ProcTyNonInstantMsg Γₙ Γₘ τ mx := by
    intro ctx p τ mx Γₙ Γₘ H_judgement
    revert mx Γₙ Γₘ
    induction H_judgement
    case cycle | skip | dollar => aesop
    case choice ctx' p₁ p₂ τ₁ τ₂ H_typing_e H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      intro mx Γₙ Γₘ H_noninst
      -- rename_i H_guarded₁ H_guarded₂
      cases H_noninst
      apply ProcTyNonInstantMsg.choice
      . apply H_ind₁; assumption
      . apply H_ind₂; assumption
    case choice_fair ctx' p₁ p₂ τ₁ τ₂ b H_typing_e H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      intro mx Γₙ Γₘ H_noninst
      -- cases H_guarded
      -- rename_i H_guarded₁ H_guarded₂
      cases H_noninst
      apply ProcTyNonInstantMsg.choice_fair
      . apply H_ind₁; assumption
      . apply H_ind₂; assumption
    case par ctx' p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      intro mx Γₙ Γₘ H_noninst
      -- cases H_guarded
      -- rename_i H_guarded₁ H_guarded₂
      cases H_noninst
      apply ProcTyNonInstantMsg.par
      . apply H_ind₁; assumption
      . apply H_ind₂; assumption
    case message_send ctx msg e H_typing_e =>
      intro mx Γₙ Γₘ H_noninst
      -- cases H_guarded
      cases H_noninst
      . apply ProcTyNonInstantMsg.send
        grind
      . apply ProcTyNonInstantMsg.send_opposite
    case message_recv ctx msg x p' τ' H_typing H_ind =>
      intro mx Γₙ Γₘ H_noninst
      -- cases H_guarded
      cases H_noninst
      . apply ProcTyNonInstantMsg.seq_right
        apply ProcTyNonInstantMsg.recv
        . grind
        . apply H_ind; assumption
      . apply ProcTyNonInstantMsg.seq_right
        apply ProcTyNonInstantMsg.recv_opposite
        apply H_ind; assumption
    case recur ctx x p' τ' H_typing H_ind =>
      intro mx Γₙ Γₘ H_noninst
      cases H_noninst
      case recur_instant H_noninst H_noninstmsg =>
        apply ProcTyNonInstantMsg.recur_instant
        . have H : ProcTyJudgement ctx (Proc.recur x p') (ProcTy.recur x τ') := by
            aesop
          apply (non_instant_preservation (Proc.recur x p') (ProcTy.recur x τ') ctx Γₙ H).mpr
          exact H_noninst
        . apply H_ind
          exact H_noninstmsg
      case recur_noninstant H_noninst H_noninstmsg =>
        apply ProcTyNonInstantMsg.recur_noninstant
        . have H : ProcTyJudgement ctx (Proc.recur x p') (ProcTy.recur x τ') := by
            aesop
          apply H_ind
          exact H_noninstmsg
    case seq ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
      intro mx Γₙ Γₘ H_noninst
      cases H_noninst
      case seq H_noninst₁ H_noninst₂ =>
        apply ProcTyNonInstantMsg.seq_right
        . apply H_ind₁
          assumption
        . apply H_ind₂
          assumption
      case seq_noninst H_noninst H_noninstmsg =>
        apply ProcTyNonInstantMsg.seq_left
        . apply H_ind₁
          assumption
        . apply (non_instant_preservation p₁ τ₁ ctx Γₙ H_typing₁).mpr
          exact H_noninst
    case var cx' x H_x =>
      intro mx Γₙ Γₘ H_noninst
      cases H_noninst
      apply ProcTyNonInstantMsg.var
      grind
    case subtype ctx p τ₁ τ₂ H_typing H_subtype H_ind =>
      intro mx Γₙ Γₘ H_noninst
      apply subtype_non_instant_msg_preservation_rev (τ₁ := τ₁)
      . exact H_subtype
      . apply H_ind
        assumption
    case offer => sorry
    case xoffer => sorry -- low priority

end ProcTyGuarded
