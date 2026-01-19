import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
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
  case H_offer =>
    intro ctx p H_typing
    cases H_typing -- TODO: would need to complete once we add offer back


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

-- TODO: the most important proof
/-
  Issues:
  - Need to ensure that if process is a deadend, then type is also a deadend (i.e., no deadend is removed by typing)
    - Equivalently, if type is not a deadend, then process is also not a deadend
  - Maybe need to ignore ε transitions
-/
lemma type_emulates_proc : ∀ (p p' : Semantics.ProcComp)
                             (τ : ProcTyComposition) (c_lbl : TransLabel),
    CompositionTyJudgement p τ →
    Semantics.CompReduces p c_lbl p' →
    ∃ τ',
      CompositionTyJudgement p' τ' ∧
      ProcTyCompTransition τ (AbstractTransLabel.fromConcrete c_lbl) τ' := by
    intro p p' τ c_lbl H_typing H_reduces
    revert H_typing τ
    unfold Semantics.CompReduces at H_reduces
    have ⟨ex_msg, ⟨H_reduces, H_complete⟩⟩ := H_reduces
    induction H_reduces
    case tock ex_msg' =>
      intro τ H_typing
      cases H_typing
      exists ProcTy.skip
      constructor
      . unfold CompositionTyJudgement
        apply ProcTyJudgement.skip
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . exists ∅
          apply ProcTyTransition.tock
    case seq_skip =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
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
      have H_ind' := H_ind ⟨ex_msg', ⟨H_red, H_complete⟩⟩ H_complete τ₁ H_typing₁
      have ⟨τ₁', H_ind'⟩ := H_ind'
      exists ProcTy.seq τ₁' τ₂
      constructor
      . apply ProcTyJudgement.seq
        . exact H_ind'.1
        . exact H_typing₂
      . unfold ProcTyCompTransition
        constructor
        . rewrite [AbstractTransLabel.fromConcrete_isComplete]
          assumption
        . unfold ProcTyCompTransition at H_ind'
          have ⟨ex_msg'', H_transition⟩ := H_ind'.2.2
          exists ex_msg''
          apply ProcTyTransition.seq_step
          exact H_transition
    case send =>
      intro τ H_typing
      exists ProcTy.skip
    case recv =>
      intro τ H_typing
      exists ProcTy.skip
    case par_skip_left =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
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
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
          cases H_typing₂
          apply ProcTyTransition.par_skip_right
    case par_left =>
      intro τ H_typing
      rename_i H_red₁ H_ind
      rename Finset _ => ex_msg'
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₁', H_ind'⟩ := H_ind ⟨ex_msg', ⟨H_red₁, H_complete⟩⟩ H_complete τ₁ H_typing₁
      exists ProcTy.par τ₁' τ₂
      constructor
      . apply ProcTyJudgement.par
        . exact H_ind'.1
        . exact H_typing₂
      . unfold ProcTyCompTransition
        constructor
        . rewrite [AbstractTransLabel.fromConcrete_isComplete]
          assumption
        . unfold ProcTyCompTransition at H_ind'
          have ⟨ex_msg'', H_transition⟩ := H_ind'.2.2
          exists ex_msg''
          apply ProcTyTransition.par_left (ex_msg' := ex_msg' ∩ ex_msg'')
          . rename_i H_not_tock _ _
            rename TransLabel => α
            apply (AbstractTransLabel.fromConcrete_nontock α).mp
            exact H_not_tock
          . simp
          . rename Proc => p₂
            have H_msg : ∀ (mx : MessageId × MessageDir), Semantics.NonInstantMessage p₂ mx ↔ ProcTyNonInstantMsg τ₂ mx :=
              non_instant_msg_preservation p₂ τ₂ H_typing₂
            rename_i H_non_instant
            intro mx H_mx
            apply (H_msg mx).mp
            apply H_non_instant
            aesop
          . exact H_transition
    case par_right => -- symmetrical
      intro τ H_typing
      rename_i H_red₂ H_ind
      rename Finset _ => ex_msg'
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      have ⟨τ₂', H_ind'⟩ := H_ind ⟨ex_msg', ⟨H_red₂, H_complete⟩⟩ H_complete τ₂ H_typing₂
      exists ProcTy.par τ₁ τ₂'
      constructor
      . apply ProcTyJudgement.par
        . exact H_typing₁
        . exact H_ind'.1
      . unfold ProcTyCompTransition
        constructor
        . rewrite [AbstractTransLabel.fromConcrete_isComplete]
          assumption
        . unfold ProcTyCompTransition at H_ind'
          have ⟨ex_msg'', H_transition⟩ := H_ind'.2.2
          exists ex_msg''
          apply ProcTyTransition.par_right (ex_msg' := ex_msg' ∩ ex_msg'')
          . rename_i H_not_tock _ _
            rename TransLabel => α
            apply (AbstractTransLabel.fromConcrete_nontock α).mp
            exact H_not_tock
          . simp
          . rename_i p₁ _ _ _ _ _ _
            have H_msg : ∀ (mx : MessageId × MessageDir), Semantics.NonInstantMessage p₁ mx ↔ ProcTyNonInstantMsg τ₁ mx :=
              non_instant_msg_preservation p₁ τ₁ H_typing₁
            rename_i H_non_instant
            intro mx H_mx
            apply (H_msg mx).mp
            apply H_non_instant
            aesop
          . exact H_transition
    case par_tock => sorry
    case recur_unfold =>
      intro τ H_typing
      cases H_typing
      rename String => X
      rename ProcTy => τ
      exists τ.replaceVar X (ProcTy.recur X τ)
      unfold CompositionTyJudgement
      constructor
      . sorry -- FIXME: prove this separately in a lemma
      . unfold ProcTyCompTransition
        constructor
        . rewrite [AbstractTransLabel.fromConcrete_isComplete]
          aesop
        . exists ∅
          apply ProcTyTransition.recur_unfold
    case ifunfair_true =>
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₁
      constructor
      . exact H_typing₁
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
          apply ProcTyTransition.choice_left
    case ifunfair_false =>
      -- symmetrical
      intro τ H_typing
      cases H_typing
      rename_i τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
          apply ProcTyTransition.choice_right
    case iffair_true =>
      intro τ H_typing
      cases H_typing
      rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₁
      constructor
      . exact H_typing₁
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
          apply ProcTyTransition.choice_fair_left
    case iffair_false =>
      -- symmetrical
      intro τ H_typing
      cases H_typing
      rename_i bid τ₁ τ₂ ctx H_typing₁ H_typing₂
      exists τ₂
      constructor
      . exact H_typing₂
      . unfold AbstractTransLabel.fromConcrete
        simp
        unfold ProcTyCompTransition
        constructor
        . aesop
        . have ⟨ex_msg'', H_red⟩ := H_reduces
          exists ex_msg''
          apply ProcTyTransition.choice_fair_right
    case par_message =>
      intro τ H_typing
      rename_i H_sub₁ H_sub₂ H_nim₁ H_nim₂ H_red₁ H_red₂ H_ih₁ H_ih₂
      rename MessageId => msg
      rename_i ex_msg₁ ex_msg₂ dir dir' b p₁ p₁' p₂ p₂' H_dual
      cases H_typing
      rename_i τ₁ τ₂ H_typing₁ H_typing₂
      unfold TransLabel.isComplete at H_complete
      simp at H_complete
      rewrite [H_complete] at H_dual
      unfold MessageDir.dual at H_dual
      simp at H_dual
      -- have ⟨τ₁', H_ih₁'⟩ := H_ih₁ ⟨ex_msg₁, ⟨H_red₁, H_complete⟩⟩ H_complete τ₁ H_typing₁


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
