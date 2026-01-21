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

lemma non_instant_red_preservation :
      ∀ (ctx : ProcTyContext) (p: Semantics.ProcComp) (τ : ProcTyComposition),
        ProcTyJudgement ctx p τ →
        (Semantics.NonInstantReducible p ↔ ProcTyNonInstant τ) := by

  intro ctx p τ
  revert p ctx
  induction τ using ProcTy.ind
  case H_cycle =>
    intro ctx p H_typing
    constructor
    . intro H_non_instant
      apply ProcTyNonInstant.cycle
    . intro H_non_instant
      cases H_typing
      apply Semantics.NonInstantReducible.cycle
  case H_skip =>
    intro ctx p H_typing
    cases H_typing
    constructor
    . intro H_non_instant
      cases H_non_instant
    . intro H_non_instant
      cases H_non_instant
  case H_message =>
    intro ctx p H_typing
    cases H_typing
    constructor
    . intro H_non_instant
      cases H_non_instant
    . intro H_non_instant
      cases H_non_instant
  case H_choice τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro ctx p H_typing
    cases H_typing
    rename_i e p₁ p₂ H_expr_ty H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply ProcTyNonInstant.choice
      . have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mp H_non_instant₁
      . have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply Semantics.NonInstantReducible.ifunfair
      . have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mpr H_non_instant₁
      . have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mpr H_non_instant₂
  case H_choice_fair bid τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro ctx p H_typing
    cases H_typing
    rename_i e p₁ p₂ H_expr_ty H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply ProcTyNonInstant.choice_fair bid
      . have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mp H_non_instant₁
      . have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply Semantics.NonInstantReducible.iffair bid
      . have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mpr H_non_instant₁
      . have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mpr H_non_instant₂
  case H_par τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro ctx p H_typing
    cases H_typing
    rename_i p₁ p₂ H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      . rename_i H_non_instant₁
        apply ProcTyNonInstant.par_left
        have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mp H_non_instant₁
      . rename_i H_non_instant₂
        apply ProcTyNonInstant.par_right
        have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      . rename_i H_non_instant₁
        apply Semantics.NonInstantReducible.par_left
        have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
        exact H_ih₁'.mpr H_non_instant₁
      . rename_i H_non_instant₂
        apply Semantics.NonInstantReducible.par_right
        have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
        exact H_ih₂'.mpr H_non_instant₂
  case H_seq τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro ctx p H_typing
    cases H_typing
    . rename_i msg x p H_typing
      constructor
      . intro H_non_instant
        apply ProcTyNonInstant.seq_right
        have H_ih₂' := H_ih₂ (ctx.extendExprVar x) p H_typing
        cases H_non_instant
        rename_i H_ih
        exact H_ih₂'.mp H_ih
      . intro H_non_instant
        apply Semantics.NonInstantReducible.recv
        cases H_non_instant
        . rename_i H_ih
          cases H_ih
        . rename_i H_ih
          have H_ih₂' := H_ih₂ (ctx.extendExprVar x) p H_typing
          exact H_ih₂'.mpr H_ih
    . rename_i p₁ p₂ H_typing₁ H_typing₂
      constructor
      . intro H_non_instant
        cases H_non_instant
        . rename_i H_non_instant₁
          apply ProcTyNonInstant.seq_left
          have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
          exact H_ih₁'.mp H_non_instant₁
        . rename_i H_non_instant₂
          apply ProcTyNonInstant.seq_right
          have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
          exact H_ih₂'.mp H_non_instant₂
      . intro H_non_instant
        cases H_non_instant
        . rename_i H_non_instant₁
          apply Semantics.NonInstantReducible.seq_left
          have H_ih₁' := H_ih₁ ctx p₁ H_typing₁
          exact H_ih₁'.mpr H_non_instant₁
        . rename_i H_non_instant₂
          apply Semantics.NonInstantReducible.seq_right
          have H_ih₂' := H_ih₂ ctx p₂ H_typing₂
          exact H_ih₂'.mpr H_non_instant₂
  case H_dollar =>
    intro ctx p H_typing
    cases H_typing
    constructor
    . intro H_non_instant
      cases H_non_instant
    . intro H_non_instant
      cases H_non_instant
  case H_var x =>
    intro ctx p H_typing
    cases H_typing
    constructor
    . intro H_non_instant
      cases H_non_instant
    . intro H_non_instant
      cases H_non_instant
  case H_recur x body H_ih =>
    intro ctx p H_typing
    cases H_typing
    rename_i p_body H_typing_body
    constructor
    . intro H_non_instant
      apply ProcTyNonInstant.recur x body
      have H_ih' := H_ih (ctx.extendProcVar x) p_body H_typing_body
      cases H_non_instant
      rename_i H_ih
      exact H_ih'.mp H_ih
    . intro H_non_instant
      apply Semantics.NonInstantReducible.recur x
      have H_ih' := H_ih (ctx.extendProcVar x) p_body H_typing_body
      cases H_non_instant
      rename_i H_ih
      exact H_ih'.mpr H_ih
  case H_xoffer =>
    intro ctx p H_typing
    cases H_typing -- TODO: would need to complete once we add xoffer back
    sorry
  case H_offer =>
    intro ctx p H_typing
    cases H_typing -- TODO: would need to complete once we add offer back
    sorry


lemma non_instant_msg_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition),
        CompositionTyJudgement p τ → ∀ mx, (Semantics.NonInstantMessage p mx ↔ ProcTyNonInstantMsg τ mx) := by

  intro p τ mx
  revert p
  induction τ using ProcTy.ind
  case H_cycle =>
    intro p H_typing mx
    constructor
    . intro H_non_instant
      apply ProcTyNonInstantMsg.cycle
    . intro H_non_instant
      cases H_typing
      apply Semantics.NonInstantMessage.cycle
  case H_skip =>
    intro p H_typing mx
    cases H_typing
    constructor
    . intro H_non_instant
      apply ProcTyNonInstantMsg.skip
    . intro H_non_instant
      apply Semantics.NonInstantMessage.skip
  case H_choice τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro p H_typing mx
    cases H_typing
    rename_i e p₁ p₂ H_expr_ty H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply ProcTyNonInstantMsg.choice
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mp H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply Semantics.NonInstantMessage.ifunfair
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mpr H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mpr H_non_instant₂
  case H_choice_fair bid τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro p H_typing mx
    cases H_typing
    rename_i e p₁ p₂ H_expr_ty H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply ProcTyNonInstantMsg.choice_fair bid
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mp H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply Semantics.NonInstantMessage.iffair bid
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mpr H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mpr H_non_instant₂
  case H_par τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro p H_typing mx
    cases H_typing
    rename_i p₁ p₂ H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply ProcTyNonInstantMsg.par
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mp H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mp H_non_instant₂
    . intro H_non_instant
      cases H_non_instant
      rename_i H_non_instant₁ H_non_instant₂
      apply Semantics.NonInstantMessage.par
      . have H_ih₁' := H_ih₁ p₁ H_typing₁ mx
        exact H_ih₁'.mpr H_non_instant₁
      . have H_ih₂' := H_ih₂ p₂ H_typing₂ mx
        exact H_ih₂'.mpr H_non_instant₂
  case H_seq τ₁ τ₂ H_ih₁ H_ih₂ =>
    intro p H_typing mx
    cases H_typing
    rename_i p₁ p₂ H_typing₁ H_typing₂
    constructor
    . intro H_non_instant
      sorry
    all_goals sorry
  all_goals sorry -- FIXME: complete


lemma recursion_unfolding_preserved :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (x : String),
        ProcTyJudgement (ctx.extendProcVar x) p τ →
        ProcTyJudgement ctx (Semantics.procReplace p x (Proc.recur x p)) (τ.replaceVar x $ ProcTy.recur x τ) := by

  sorry

lemma par_list_ty : ∀ (procs : List Proc) (tys : List ProcTy),
    (H_len : procs.length = tys.length) →
    (∀ p τ, (p, τ) ∈ List.zip procs tys → ProcTyJudgement ProcTyContext.empty p τ) →
    ProcTyJudgement ProcTyContext.empty (procs.foldl (fun acc p => Proc.par acc p) Proc.skip) (tys.foldl (fun acc τ => ProcTy.par acc τ) ProcTy.skip) :=
      by sorry -- obvious
