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


/-- Well-formed process types. All recursion variables appear only at tail locations. -/
inductive WellformedTy : ProcTy → Prop where
  | message (me : MessageExch) :
    WellformedTy (ProcTy.message me)
  | cycle :
    WellformedTy ProcTy.cycle
  | skip :
    WellformedTy ProcTy.skip
  | dollar (pid : ProcId) :
    WellformedTy (ProcTy.dollar pid)
  | choice (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.choice_fair bid τ₁ τ₂)
  | par (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.par τ₁ τ₂)
  | seq (τ₁ τ₂ : ProcTy) :
    WellformedTy τ₁ →
    WellformedTy τ₂ →
    WellformedTy (ProcTy.seq τ₁ τ₂)
  | xoffer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    WellformedTy τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → WellformedTy ty) →
    WellformedTy (ProcTy.xoffer τ_else branch_tys)
  | offer (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    WellformedTy τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → WellformedTy ty) →
    WellformedTy (ProcTy.offer τ_else branch_tys)
  | var (x : String) :
    WellformedTy (ProcTy.var x)
  | recur (x : String) (body : ProcTy) :
    WellformedTy body →
    AtTail x body →
    WellformedTy (ProcTy.recur x body)

lemma non_instant_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (Γ : Finset String),
        ctx.procVars = ∅ → ProcTyJudgement ctx p τ → ProcTyNonInstant Γ τ → Semantics.NonInstantReducible Γ p := by

    sorry

lemma non_instant_msg_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext),
        ctx.procVars = ∅ → ProcTyJudgement ctx p τ → ∀ mx Γₙ Γₘ, (ProcTyNonInstantMsg Γₙ Γₘ τ mx → Semantics.NonInstantMessage Γₙ Γₘ p mx) := by
  intro p τ ctx H_ctx H_typing
  -- generalize H_ctx : ProcTyContext.empty = ctx at H_typing
  revert H_ctx
  induction H_typing <;> (intro H_ctx' mx Γₙ Γₘ H_noninst_msg)
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
      have H_ind' := H_ind H_ctx' mx Γₙ Γₘ H_noninst_msg
      cases H_noninst <;> aesop
  case par ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case seq ctx p₁ p₂ τ₁ τ₂ H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    case seq_left H_noninst H_noninst_msg =>
      have H_ind₁' := H_ind₁ H_ctx' mx Γₙ Γₘ H_noninst_msg
      have H_noninst₁ : Semantics.NonInstantReducible Γₙ p₁ := by
        apply non_instant_preservation (ctx := ctx) <;> assumption
      aesop
    case seq_right H_noninst_msg₁ H_noninst_msg₂ =>
      have H_ind₁' := H_ind₁ H_ctx' mx Γₙ Γₘ H_noninst_msg₁
      have H_ind₂' := H_ind₂ H_ctx' mx Γₙ Γₘ H_noninst_msg₂
      aesop
  case choice ctx e p₁ p₂ τ₁ τ₂ H_expr_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case choice_fair ctx e p₁ p₂ τ₁ τ₂ b H_expr_typing H_typing₁ H_typing₂ H_ind₁ H_ind₂ =>
    cases H_noninst_msg
    aesop
  case var ctx x =>
    aesop
  case recur ctx x body τ_body H_typing H_ind =>
    cases H_noninst_msg
    case recur_instant H_noninst H_noninst_msg =>
      sorry
    sorry
  all_goals sorry -- FIXME: complete

lemma recursion_unfolding_preserved :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (x : String),
        ProcTyJudgement (ctx.extendProcVar x) p τ →
        ProcTyJudgement ctx (Semantics.procReplace p x (Proc.recur x p)) (τ.replaceVar x $ ProcTy.recur x τ) := by

  sorry -- FIXME: prove


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
      Semantics.IncompReduces (Proc.seq p₁ p₂) lbl (Proc.seq p₁' p₂) := by sorry -- trivial

  lemma par_non_ex_left :
    ∀ {p₁ p₁' p₂ : Semantics.ProcComp} {lbl : TransLabel},
      ¬ lbl.isEx →
      Semantics.IncompReduces p₁ lbl p₁' →
      Semantics.IncompReduces (Proc.par p₁ p₂) lbl (Proc.par p₁' p₂) := by
      sorry -- trivial

  lemma par_non_ex_right :
    ∀ {p₁ p₂ p₂' : Semantics.ProcComp} {lbl : TransLabel},
      ¬ lbl.isEx →
      Semantics.IncompReduces p₂ lbl p₂' →
      Semantics.IncompReduces (Proc.par p₁ p₂) lbl (Proc.par p₁ p₂') := by
      sorry -- trivial

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
    sorry -- trivial

  lemma elim_right :
    ∀ {τ₁ τ₂ τ₃ : ProcTy},
      ProcTyCompElim τ₁ τ₂ →
      ProcTyTransition τ₂ AbstractTransLabel.ε τ₃ →
      ProcTyCompElim τ₁ τ₃ := by
    sorry -- trivial

  lemma elim_par :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy},
          ProcTyCompElim τ₁ τ₁' →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyCompElim (ProcTy.par τ₁ τ₂) (ProcTy.par τ₁' τ₂') := by
    sorry -- trivial

  lemma elim_seq_step :
        ∀ {τ₁ τ₁' τ₂ : ProcTy},
          ProcTyCompElim τ₁ τ₁' →
          ProcTyCompElim (ProcTy.seq τ₁ τ₂) (ProcTy.seq τ₁' τ₂) := by
    sorry -- trivial

  lemma elim_seq_skip :
        ∀ {τ₁ τ₂ τ₂' : ProcTy},
          ProcTyCompElim τ₁ ProcTy.skip →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyCompElim (ProcTy.seq τ₁ τ₂) τ₂' := by
    sorry -- trivial

end ProcTyCompElim



namespace ProcTyIncompTransition
  lemma reduces_seq :
        ∀ {τ₁ τ₂ τ₁' : ProcTy} {lbl : AbstractTransLabel},
          ProcTyIncompTransition τ₁ lbl τ₁' →
          ProcTyIncompTransition (ProcTy.seq τ₁ τ₂) lbl (ProcTy.seq τ₁' τ₂) := by
    sorry -- trivial

  lemma reduces_seq_skip :
        ∀ {τ₁ τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ProcTyCompElim τ₁ ProcTy.skip →
          ProcTyIncompTransition τ₂ lbl τ₂' →
          ProcTyIncompTransition (ProcTy.seq τ₁ τ₂) lbl τ₂' := by
    sorry -- trivial

  lemma reduces_par_left :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ¬ lbl.isEx →
          ProcTyIncompTransition τ₁ lbl τ₁' →
          ProcTyCompElim τ₂ τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂') := by
    sorry -- trivial

  lemma reduces_par_right :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {lbl : AbstractTransLabel},
          ¬ lbl.isEx →
          ProcTyCompElim τ₁ τ₁' →
          ProcTyIncompTransition τ₂ lbl τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) lbl (ProcTy.par τ₁' τ₂') := by
    sorry -- trivial

  lemma reduces_par_tock :
        ∀ {τ₁ τ₂ τ₁' τ₂' : ProcTy},
          ProcTyIncompTransition τ₁ (AbstractTransLabel.ac Action.tock) τ₁' →
          ProcTyIncompTransition τ₂ (AbstractTransLabel.ac Action.tock) τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac Action.tock) (ProcTy.par τ₁' τ₂') := by
    sorry -- trivial

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
    sorry --trivial

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
      induction H_sub
      case congr τ₁ τ₂ H_congr =>
        sorry -- FIXME: prove separately
      all_goals sorry

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
  lemma trans_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy} {lbl : AbstractTransLabel},
          ProcTyGuarded ∅ ∅ τ₁ →
          ProcTyTransition τ₁ lbl τ₂ →
          ProcTyGuarded ∅ ∅ τ₂ := by
    intro τ₁ τ₂ lbl H_guarded H_transition
    induction H_transition
    all_goals sorry -- FIXME: prove

  lemma elim_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy},
          ProcTyGuarded ∅ ∅ τ₁ →
          ProcTyCompElim τ₁ τ₂ →
          ProcTyGuarded ∅ ∅ τ₂ := by
    sorry -- trivial

  lemma incomp_trans_preserves_guarded :
        ∀ {τ₁ τ₂ : ProcTy} {lbl : AbstractTransLabel},
          ProcTyGuarded ∅ ∅ τ₁ →
          ProcTyIncompTransition τ₁ lbl τ₂ →
          ProcTyGuarded ∅ ∅ τ₂ := by
    sorry -- FIXME: prove

  lemma guarded_preserves_non_instant_msg :
       ∀ {p : Semantics.ProcComp} {τ : ProcTyComposition},
          CompositionTyJudgement p τ →
          ProcTyGuarded ∅ ∅ τ →
          ∃ τ', ProcTyCompElim τ τ' ∧
            CompositionTyJudgement p τ' ∧
            (
              ∀ mx,
              Semantics.NonInstantMessage ∅ ∅ p mx →
              ProcTyNonInstantMsg ∅ ∅ τ' mx
            ) := by sorry -- FIXME: prove
end ProcTyGuarded
