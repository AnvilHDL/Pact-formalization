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

lemma non_instant_msg_preservation :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition),
        CompositionTyJudgement p τ → ∀ mx, (ProcTyNonInstantMsg ∅ ∅ τ mx → Semantics.NonInstantMessage ∅ ∅ p mx) := by sorry
      -- FIXME: prove

lemma recursion_unfolding_preserved :
      ∀ (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (x : String),
        ProcTyJudgement (ctx.extendProcVar x) p τ →
        ProcTyJudgement ctx (Semantics.procReplace p x (Proc.recur x p)) (τ.replaceVar x $ ProcTy.recur x τ) := by

  sorry -- FIXME: prove

lemma val_replacement_preserves_typing :
      ∀ (ctx : ProcTyContext) (p : Semantics.ProcComp) (τ : ProcTyComposition) (ctx : ProcTyContext) (x : String) (v : Bool),
        ProcTyJudgement (ctx.extendExprVar x) p τ →
        ProcTyJudgement ctx (Semantics.procExprReplace p x v) τ := by
  sorry -- FIXME: prove

lemma par_list_ty : ∀ (procs : List Proc) (tys : List ProcTy),
    (H_len : procs.length = tys.length) →
    (∀ p τ, (p, τ) ∈ List.zip procs tys → ProcTyJudgement ProcTyContext.empty p τ) →
    ProcTyJudgement ProcTyContext.empty (procs.foldl (fun acc p => Proc.par acc p) Proc.skip) (tys.foldl (fun acc τ => ProcTy.par acc τ) ProcTy.skip) :=
      by sorry -- obvious


lemma subtype_preserves_reduction : ∀ (τ₁ τ₂ τ₁' : ProcTy)
        (lbl : AbstractTransLabel),
      lbl ≠ AbstractTransLabel.ε →
      ProcTyTransition τ₁ lbl τ₂ →
      ProcTySub τ₁ τ₁' →
      (∃ τ₂', ProcTyTransition τ₁' lbl τ₂' ∧ ProcTySub τ₂ τ₂') := by sorry

namespace ProcTyCongr
  lemma congr_preserves_behaviour (τ₁ τ₂ τ₁' : ProcTy) (lbl : AbstractTransLabel) :
    ProcTyCongr τ₁ τ₂ → ProcTyTransition τ₁ lbl τ₁' → ∃ τ₂', ProcTyTransition τ₂ lbl τ₂' ∧ ProcTyCongr τ₁' τ₂' := by sorry -- FIXME: prove

  lemma congr_of_skip_is_skip (τ₁ τ₂ : ProcTy) :
    (ProcTyCongr τ₁ τ₂) → (τ₁ = ProcTy.skip ↔ τ₂ = ProcTy.skip) := by
      intro H_congr
      generalize H_skip : ProcTy.skip = τ at H_congr
      induction H_congr
      case refl =>
        rfl
      case symm τ₁ τ₂ H_congr =>
        symm
        exact H_congr
      case trans τ₁' τ₂' τ₃ H_congr₁ H_congr₂ H_ind₁ H_ind₂ =>
        rewrite [H_ind₁]
        rewrite [H_ind₂]
        rfl
      case par_comm τ₁' τ₂' =>
        rewrite [← H_skip]
        simp

end ProcTyCongr

namespace ProcTySub
  lemma sub_preserves_behaviour (τ₁ τ₂ τ₂' : ProcTy) (lbl : AbstractTransLabel) :
    ProcTySub τ₁ τ₂ → ProcTyTransition τ₂ lbl τ₂' → ∃ τ₁', ProcTyTransition τ₁ lbl τ₁' ∧ ProcTySub τ₁' τ₂' := by sorry -- FIXME: prove

  lemma sub_of_skip_is_skip (τ : ProcTy) :
    ProcTySub τ ProcTy.skip → τ = ProcTy.skip := by
      intro H_sub
      generalize H_skip : ProcTy.skip = τ at H_sub
      induction H_sub
      case congr τ₁ τ₂ H_congr =>
        rewrite [← H_skip]
        sorry
      case choice_relax τ₁ τ₂ =>
        sorry
      case trans => sorry -- FIXME: prove
end ProcTySub

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

  lemma seq_elim : ∀ {p₁ p₂ p' : Semantics.ProcComp},
      CompElim (Proc.seq p₁ p₂) p' →
      (∃ p₁', CompElim p₁ p₁' ∧ p' = Proc.seq p₁' p₂) ∨
      (CompElim p₁ Proc.skip ∧ CompElim p₂ p') := by
    intro p₁ p₂ p' H_elim
    sorry -- FIXME: prove this

  lemma par_elim : ∀ {p₁ p₂ p' : Semantics.ProcComp},
      CompElim (Proc.par p₁ p₂) p' →
      (∃ p₁' p₂', CompElim p₁ p₁' ∧ CompElim p₂ p₂' ∧ p' = Proc.par p₁' p₂') ∨
      (CompElim p₁ Proc.skip ∧ CompElim p₂ Proc.skip ∧ p' = Proc.skip) := by
    intro p₁ p₂ p' H_elim
    sorry -- FIXME: prove this

  lemma par_elim_fwd : ∀ {p₁ p₂ p₁' p₂' : Semantics.ProcComp},
      CompElim p₁ p₁' →
      CompElim p₂ p₂' →
      CompElim (Proc.par p₁ p₂) (Proc.par p₁' p₂') := by sorry -- trivial

  lemma par_elim_fwd_skip_l : ∀ {p₁ p₂ p₂' : Semantics.ProcComp},
      CompElim p₁ Proc.skip →
      CompElim p₂ p₂' →
      CompElim (Proc.par p₁ p₂) p₂' := by
    sorry -- trivial

  lemma par_elim_fwd_skip_r : ∀ {p₁ p₁' p₂ : Semantics.ProcComp},
      CompElim p₁ p₁' →
      CompElim p₂ Proc.skip →
      CompElim (Proc.par p₁ p₂) p₁' := by
    sorry -- trivial


  lemma seq_elim_fwd_r : ∀ {p₁ p₂ p₂' : Semantics.ProcComp},
      CompElim p₁ Proc.skip →
      CompElim p₂ p₂' →
      CompElim (Proc.seq p₁ p₂) p₂' := by
    sorry -- FIXME: prove this

  lemma elim_preserves_typing :
        ∀ {p p' : Semantics.ProcComp} {τ : ProcTyComposition},
          Semantics.CompElim p p' →
          CompositionTyJudgement p τ →
          ∃ τ', ProcTyCompElim τ τ' ∧ CompositionTyJudgement p' τ' := by sorry -- FIXME: prove this
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
    sorry -- FIXME: prove

  lemma reduces_par_ex_right :
        ∀ {τ₁ τ₂ τ₂' : ProcTy} {ex_msg : Finset (MessageId × MessageDir)},
          ProcTyIncompTransition τ₂ (AbstractTransLabel.ex ex_msg) τ₂' →
          (∀ mx ∈ ex_msg,
            ProcTyNonInstantMsg ∅ ∅ τ₁ mx) →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ex ex_msg) (ProcTy.par τ₁ τ₂') := by
    sorry -- FIXME: prove

  lemma reduces_par_message :
        ∀ {τ₁ τ₁' τ₂ τ₂' : ProcTy} {msg : MessageId} {d₁ d₂ : MessageDir},
          MessageDir.dual d₁ d₂ →
          ProcTyIncompTransition τ₁ (AbstractTransLabel.message msg d₁) τ₁' →
          ProcTyIncompTransition τ₂ (AbstractTransLabel.message msg d₂) τ₂' →
          ProcTyIncompTransition (ProcTy.par τ₁ τ₂) (AbstractTransLabel.ac $ Action.fullMessage msg) (ProcTy.par τ₁' τ₂') := by
    sorry -- FIXME: prove

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
    sorry -- FIXME: prove this

  lemma skip_typing_implies_skip_elim_rev :
        ∀ {p : Semantics.ProcComp},
          ProcTyJudgement ProcTyContext.empty p ProcTy.skip →
          p = Proc.skip := by
    intro p H_typing
    generalize H_ctx : ProcTyContext.empty = ctx at H_typing
    generalize H_skip : ProcTy.skip = τ at H_typing
    induction H_typing <;> try (cases H_skip; done)
    case skip =>
      rfl
    case subtype =>
      rename_i p' τ₁ τ₂ H_typing H_sub H_ind
      rewrite [← H_skip] at H_sub
      apply H_ind
      . exact H_ctx
      . symm
        apply ProcTySub.sub_of_skip_is_skip
        exact H_sub
end ProcTyIncompTransition

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
    sorry -- FIXME: prove

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
