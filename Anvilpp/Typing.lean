import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

@[aesop unsafe]
inductive ProcTyNonInstant : Finset String → ProcTy → Prop where
  | cycle (Γ : Finset String) :
    ProcTyNonInstant Γ ProcTy.cycle
  | choice (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.choice τ₁ τ₂)
  | choice_fair (bid : BranchId) (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.choice_fair bid τ₁ τ₂)
  | seq_left (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ (ProcTy.seq τ₁ τ₂)
  | seq_right (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.seq τ₁ τ₂)
  | par_left (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₁ →
    ProcTyNonInstant Γ (ProcTy.par τ₁ τ₂)
  | par_right (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
    ProcTyNonInstant Γ τ₂ →
    ProcTyNonInstant Γ (ProcTy.par τ₁ τ₂)
  | xoffer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    ProcTyNonInstant Γ τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant Γ ty) →
    ProcTyNonInstant Γ (ProcTy.xoffer τ_else branch_tys)
  | offer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
    ProcTyNonInstant Γ τ_else →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstant Γ ty) →
    ProcTyNonInstant Γ (ProcTy.offer τ_else branch_tys)
  | var (Γ : Finset String) (x : String) :
    x ∈ Γ →
    ProcTyNonInstant Γ (ProcTy.var x)
  | recur (Γ : Finset String) (x : String) (τ : ProcTy) :
    ProcTyNonInstant (Γ ∪ {x}) τ →
    ProcTyNonInstant Γ (ProcTy.recur x τ)

@[aesop unsafe]
inductive ProcTyNonInstantMsg : Finset String → Finset String → ProcTy → (MessageId × MessageDir) → Prop where
  | cycle (Γₙ Γₘ : Finset String) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ ProcTy.cycle mx
  | choice (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.choice τ₁ τ₂) mx
  | choice_fair (bid : BranchId) (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.choice_fair bid τ₁ τ₂) mx
  | seq_left (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstant Γₙ τ₁ →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.seq τ₁ τ₂) mx
  | seq_right (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.seq τ₁ τ₂) mx
  | par (Γₙ Γₘ : Finset String) (τ₁ τ₂ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ₁ mx →
    ProcTyNonInstantMsg Γₙ Γₘ τ₂ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.par τ₁ τ₂) mx
  | xoffer (Γₙ Γₘ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ_else mx →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg Γₙ Γₘ ty mx) →
    (∀ m ty, (m, ty) ∈ branch_tys → m.toPair ≠ mx) →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.xoffer τ_else branch_tys) mx
  | offer (Γₙ Γₘ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ τ_else mx →
    (∀ m ty, (m, ty) ∈ branch_tys → ProcTyNonInstantMsg Γₙ Γₘ ty mx) →
    (∀ m ty, (m, ty) ∈ branch_tys → m.toPair ≠ mx) →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.offer τ_else branch_tys) mx
  | var (Γₙ Γₘ : Finset String) (x : String) (mx : MessageId × MessageDir) :
    x ∈ Γₘ →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.var x) mx
  | recur_instant (Γₙ Γₘ : Finset String) (x : String) (τ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstant Γₙ (ProcTy.recur x τ) →
    ProcTyNonInstantMsg (Γₙ ∪ {x}) (Γₘ ∪ {x}) τ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.recur x τ) mx
  | recur_noninstant (Γₙ Γₘ : Finset String) (x : String) (τ : ProcTy) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg (Γₙ \ {x}) (Γₘ ∪ {x}) τ mx →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.recur x τ) mx
  | skip (Γₙ Γₘ : Finset String) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ ProcTy.skip mx
  | dollar (Γₙ Γₘ : Finset String) (pid : ProcId) (mx : MessageId × MessageDir) :
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.dollar pid) mx
  | send (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.send)
  | send_opposite (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.send msg') (msg, MessageDir.recv)
  | recv (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    msg ≠ msg' →
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.recv)
  | recv_opposite (Γₙ Γₘ : Finset String) (msg msg' : MessageId) :
    ProcTyNonInstantMsg Γₙ Γₘ (ProcTy.message $ MessageExch.recv msg') (msg, MessageDir.send)



abbrev ExprTyContext := Finset String

structure ProcTyContext where
  -- procVars : String → Option ProcTy
  procVars : Finset String
  exprVars : ExprTyContext

namespace ProcTyContext
  def empty : ProcTyContext :=
    { procVars := ∅, exprVars := ∅ }

  -- def extendProcVar (ctx : ProcTyContext) (x : String) (ty : ProcTy) : ProcTyContext :=
  --   { ctx with procVars := fun y => if y = x then some ty else ctx.procVars y }

  def extendProcVar (ctx : ProcTyContext) (x : String) : ProcTyContext :=
    { ctx with procVars := ctx.procVars ∪ {x} }

  def extendExprVar (ctx : ProcTyContext) (x : String) : ProcTyContext :=
    { ctx with exprVars := ctx.exprVars ∪ {x} }
end ProcTyContext

inductive ExprTyJudgement : ExprTyContext → Expr → Prop where
  | var (ctx : ExprTyContext) (x : String) :
    x ∈ ctx →
    ExprTyJudgement ctx (Expr.var x)
  | val (ctx : ExprTyContext) (n : Bool) :
    ExprTyJudgement ctx (Expr.val n)
  | add (ctx : ExprTyContext) (e1 e2 : Expr) (bop : BOp) :
    ExprTyJudgement ctx e1 →
    ExprTyJudgement ctx e2 →
    ExprTyJudgement ctx (Expr.bin e1 bop e2)

inductive ProcTyCongr : ProcTy → ProcTy → Prop where
  | refl (τ : ProcTy) :
    ProcTyCongr τ τ
  | symm (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ →
    ProcTyCongr τ₂ τ₁
  | trans (τ₁ τ₂ τ₃ : ProcTy) :
    ProcTyCongr τ₁ τ₂ →
    ProcTyCongr τ₂ τ₃ →
    ProcTyCongr τ₁ τ₃
  | par_comm (τ₁ τ₂ : ProcTy) :
    ProcTyCongr (ProcTy.par τ₁ τ₂) (ProcTy.par τ₂ τ₁)
    -- TODO: these are tricky, consider adding these later
  -- | seq_skip (τ : ProcTy) :
  --   ProcTyCongr (ProcTy.seq ProcTy.skip τ) τ
  -- | choice_lift_right (τ₁ τ₂ τ' : ProcTy) :
  --   ProcTyCongr (ProcTy.choice (ProcTy.seq τ₁ τ') (ProcTy.seq τ₂ τ')) (ProcTy.seq (ProcTy.choice τ₁ τ₂) τ')
  -- | choice_lift_left (τ₁ τ₂ τ' : ProcTy) :
  --   ProcTyCongr (ProcTy.choice (ProcTy.seq τ' τ₁) (ProcTy.seq τ' τ₂)) (ProcTy.seq τ' (ProcTy.choice τ₁ τ₂))

/-- Subtyping -/
inductive ProcTySub : ProcTy → ProcTy → Prop where
  | congr (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ →
    ProcTySub τ₁ τ₂
  | choice_relax (τ₁ τ₂ : ProcTy) :
    (ProcTyNonInstant ∅ τ₂) →
    (∀ mx, ProcTyNonInstantMsg ∅ ∅ τ₂ mx) →
    ProcTySub τ₁ (ProcTy.choice τ₁ τ₂) -- FIXME: this requires that τ₂ does not include potentially instant messages
  | trans (τ₁ τ₂ τ₃ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTySub τ₂ τ₃ →
    ProcTySub τ₁ τ₃

  @[aesop unsafe]
  inductive ProcTyJudgement : ProcTyContext → Proc → ProcTy → Prop where
    | cycle (ctx : ProcTyContext) :
      ProcTyJudgement ctx Proc.cycle ProcTy.cycle
    | dollar (ctx : ProcTyContext) (pid : ProcId) :
      ProcTyJudgement ctx (Proc.endp pid) (ProcTy.dollar pid)
    | skip (ctx : ProcTyContext) :
      ProcTyJudgement ctx Proc.skip ProcTy.skip
    | message_send (ctx : ProcTyContext) (msg : MessageId) (e : Expr) :
      ExprTyJudgement ctx.exprVars e →
      ProcTyJudgement ctx (Proc.send msg e) (ProcTy.message $ MessageExch.send msg)
    | message_recv (ctx : ProcTyContext) (msg : MessageId) (x : String) (p : Proc) (τ : ProcTy) :
      ProcTyJudgement (ctx.extendExprVar x) p τ →
      ProcTyJudgement ctx (Proc.recv msg x p) (ProcTy.seq (ProcTy.message $ MessageExch.recv msg) τ)
    | par (ctx : ProcTyContext) (p₁ p₂ : Proc) (τ₁ τ₂ : ProcTy) :
      ProcTyJudgement ctx p₁ τ₁ →
      ProcTyJudgement ctx p₂ τ₂ →
      ProcTyJudgement ctx (Proc.par p₁ p₂) (ProcTy.par τ₁ τ₂)
    | seq (ctx : ProcTyContext) (p₁ p₂ : Proc) (τ₁ τ₂ : ProcTy) :
      ProcTyJudgement ctx p₁ τ₁ →
      ProcTyJudgement ctx p₂ τ₂ →
      ProcTyJudgement ctx (Proc.seq p₁ p₂) (ProcTy.seq τ₁ τ₂)
    | choice (ctx : ProcTyContext) (e : Expr) (p₁ p₂ : Proc) (τ₁ τ₂ : ProcTy) :
      ExprTyJudgement ctx.exprVars e →
      ProcTyJudgement ctx p₁ τ₁ →
      ProcTyJudgement ctx p₂ τ₂ →
      ProcTyJudgement ctx (Proc.ifunfair e p₁ p₂) (ProcTy.choice τ₁ τ₂)
    | choice_fair (ctx : ProcTyContext) (e : Expr) (p₁ p₂ : Proc) (τ₁ τ₂ : ProcTy) (b : BranchId) :
      ExprTyJudgement ctx.exprVars e →
      ProcTyJudgement ctx p₁ τ₁ →
      ProcTyJudgement ctx p₂ τ₂ →
      ProcTyJudgement ctx (Proc.iffair b e p₁ p₂) (ProcTy.choice_fair b τ₁ τ₂)
    | xoffer (ctx : ProcTyContext) (p_else : Proc) (branches : List ChoiceBranch)
        (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
      branches.length = branch_tys.length →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
          ExprTyJudgement ctx.exprVars e) →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
          br_ty.1 = MessageExch.send m) →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
        ProcTyJudgement ctx p br_ty.2) →
      (∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys →
        br_ty.1 = MessageExch.recv m) →
      (∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys →
        ProcTyJudgement (ctx.extendExprVar x) p br_ty.2) →
      ProcTyJudgement ctx p_else τ_else →
      ProcTyJudgement ctx (Proc.xoffer p_else branches) (ProcTy.xoffer τ_else branch_tys)
    | offer (ctx : ProcTyContext) (p_else : Proc) (branches : List ChoiceBranch)
        (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
      branches.length = branch_tys.length →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
          ExprTyJudgement ctx.exprVars e) →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
          br_ty.1 = MessageExch.send m) →
      (∀ m e p br_ty, (ChoiceBranch.send m e p, br_ty) ∈ branches.zip branch_tys →
        ProcTyJudgement ctx p br_ty.2) →
      (∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys →
        br_ty.1 = MessageExch.recv m) →
      (∀ m x p br_ty, (ChoiceBranch.recv m x p, br_ty) ∈ branches.zip branch_tys →
        ProcTyJudgement (ctx.extendExprVar x) p br_ty.2) →
      ProcTyJudgement ctx p_else τ_else →
      ProcTyJudgement ctx (Proc.offer p_else branches) (ProcTy.offer τ_else branch_tys)
    | var (ctx : ProcTyContext) (x : String) :
      -- ctx.procVars x = some τ →
      x ∈ ctx.procVars →
      ProcTyJudgement ctx (Proc.var x) (ProcTy.var x)
    | recur (ctx : ProcTyContext) (x : String) (p : Proc) (τ : ProcTy) :
      ProcTyJudgement (ctx.extendProcVar x) p τ →
      ProcTyJudgement ctx (Proc.recur x p) (ProcTy.recur x τ)
    | subtype (ctx : ProcTyContext) (p : Proc) (τ₁ τ₂ : ProcTy) :
      ProcTyJudgement ctx p τ₁ →
      ProcTySub τ₁ τ₂ →
      ProcTyJudgement ctx p τ₂

@[reducible]
def CompositionTyJudgement := ProcTyJudgement ProcTyContext.empty
