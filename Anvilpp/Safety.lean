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

lemma par_list_ty : ∀ (procs : List Proc) (tys : List ProcTy),
    (H_len : procs.length = tys.length) →
    (∀ p τ, (p, τ) ∈ List.zip procs tys → ProcTyJudgement ProcTyContext.empty p τ) →
    ProcTyJudgement ProcTyContext.empty (procs.foldl (fun acc p => Proc.par acc p) Proc.skip) (tys.foldl (fun acc τ => ProcTy.par acc τ) ProcTy.skip) :=
      by sorry -- obvious

lemma list_insert_idx : ∀ {T : Type} (l : List T) (idx : ℕ) (v : T),
    idx ≤ l.length →
      v ∈ l.insertIdx idx v := by sorry -- obvious


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
        . rewrite [← AbstractTransLabel.fromConcrete_nontock]
          assumption
        . assumption
        . rename Proc => p₂
          intro mx H_mx
          rewrite [← non_instant_msg_preservation p₂ τ₂ H_typing₂ mx]
          revert H_mx mx
          assumption
        . exact H_ind'.2
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
        . rewrite [← AbstractTransLabel.fromConcrete_nontock]
          assumption
        . assumption
        . rename_i p₁ _ _ _ _ _ _
          intro mx H_mx
          rewrite [← non_instant_msg_preservation p₁ τ₁ H_typing₁ mx]
          revert H_mx mx
          assumption
        . exact H_ind'.2
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
        apply zip_list_exists br br_tys (ChoiceBranch.send msg e p_send)
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
        apply zip_list_exists branches br_tys (ChoiceBranch.recv msg var p_br)
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
        apply ProcTyTransition.xoffer_branch (me := MessageExch.recv msg)
        exact (List.of_mem_zip H_br_ty).2
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
          apply zip_list_exists
          . rewrite [H_len]
            simp
          . apply list_insert_idx
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
        apply zip_list_exists
        . rewrite [H_len]
          simp
        . apply list_insert_idx
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

lemma deadend_preserved_by_typing :
  ∀ (p : Semantics.ProcComp) (τ τ' : ProcTyComposition) (l : AbstractTransLabel),
    CompositionTyJudgement p τ →
    ProcTyCompTransition τ l τ' →
    ∃ (p' : Semantics.ProcComp) (α : TransLabel),
      Semantics.CompReduces p α p' := by

    intro p τ τ' l H_typing
    induction τ using ProcTy.ind
    case H_skip =>
      cases H_typing
      intro ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
      cases H_trans
    case H_cycle =>
      cases H_typing
      intro ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
      exists Proc.skip, TransLabel.tock
      unfold Semantics.CompReduces
      exists ∅
      constructor
      . apply Semantics.Reduces.tock
      . aesop
    case H_dollar pid =>
      cases H_typing
      intro ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
      exists Proc.skip, TransLabel.dollar pid
    case H_message msg =>
      cases H_typing
      intro ⟨H_complete, ⟨ex_msg, H_trans⟩⟩
      rename MessageId => msg
      rename Proc => p
      rename Expr => e
      cases H_trans
      unfold AbstractTransLabel.isComplete at H_complete
      simp at H_complete
    all_goals sorry


def reachableTySet (Γ : String → Option ProcTy) (τ : ProcTy) : Finset ProcTy :=
  match τ with
  | .message x => {ProcTy.message x, ProcTy.skip}
  | .cycle => {ProcTy.cycle, ProcTy.skip}
  | .skip => {ProcTy.skip}
  | .dollar pid => {ProcTy.dollar pid, ProcTy.skip}
  | .seq τ₁ τ₂ =>
      let set₁ := reachableTySet Γ τ₁
      let set₂ := reachableTySet Γ τ₂
      set₁.image (fun τ'₁ => ProcTy.seq τ'₁ τ₂) ∪ set₂
  | .choice τ₁ τ₂ =>
      (reachableTySet Γ τ₁) ∪ (reachableTySet Γ τ₂)
  | .choice_fair bid τ₁ τ₂ =>
      (reachableTySet Γ τ₁) ∪ (reachableTySet Γ τ₂)
  | .par τ₁ τ₂ =>
      let set₁ := reachableTySet Γ τ₁
      let set₂ := reachableTySet Γ τ₂
      (set₁ ×ˢ set₂).image (fun (τ'₁, τ'₂) => ProcTy.par τ'₁ τ'₂) ∪ {ProcTy.skip}
  -- FIXME: check if this is correct
  | .xoffer τ_else branch_tys =>
      let set_else := reachableTySet Γ τ_else
      let set_branches :=
        branch_tys.foldl (fun acc (_, ty) => acc ∪ reachableTySet Γ ty) ∅
      set_else ∪ set_branches ∪ {ProcTy.skip}
  | .offer τ_else branch_tys =>
      let set_else := reachableTySet Γ τ_else
      let set_branches :=
        branch_tys.foldl (fun acc (_, ty) => acc ∪ reachableTySet Γ ty) ∅
      set_else ∪ set_branches ∪ {ProcTy.skip}
  | .var x => (
    match Γ x with
    | some τ' => {τ'}
    | none => {τ}
  )
  | .recur x body =>
    {τ} ∪ (reachableTySet (fun x' => if x' = x then τ else Γ x') body)
decreasing_by
  all_goals sorry


/-
  Now we actually prove that this finite set includes all reachable types.
  TODO: do we need further assumptions, e.g., all variables are bound?
-/

lemma reachable_types_in_set :
  ∀ (τ τ' : ProcTy), ProcTyReachable τ τ' → τ' ∈ reachableTySet (fun _ => none) τ := sorry
