import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

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
    -- FIXME: these are tricky
  -- | seq_skip (τ : ProcTy) :
  --   ProcTyCongr (ProcTy.seq ProcTy.skip τ) τ
  -- | choice_lift_right (τ₁ τ₂ τ' : ProcTy) :
  --   ProcTyCongr (ProcTy.choice (ProcTy.seq τ₁ τ') (ProcTy.seq τ₂ τ')) (ProcTy.seq (ProcTy.choice τ₁ τ₂) τ')
  -- | choice_lift_left (τ₁ τ₂ τ' : ProcTy) :
  --   ProcTyCongr (ProcTy.choice (ProcTy.seq τ' τ₁) (ProcTy.seq τ' τ₂)) (ProcTy.seq τ' (ProcTy.choice τ₁ τ₂))
  -- TODO: add more

/-- Subtyping -/
inductive ProcTySub : ProcTy → ProcTy → Prop where
  | congr (τ₁ τ₂ : ProcTy) :
    ProcTyCongr τ₁ τ₂ →
    ProcTySub τ₁ τ₂
  | choice_relax (τ₁ τ₂ : ProcTy) :
    ProcTySub τ₁ (ProcTy.choice τ₁ τ₂)
  | trans (τ₁ τ₂ τ₃ : ProcTy) :
    ProcTySub τ₁ τ₂ →
    ProcTySub τ₂ τ₃ →
    ProcTySub τ₁ τ₃

  @[aesop safe [constructors, cases]]
  inductive ProcTyJudgement : ProcTyContext → Proc → ProcTy → Prop where
    | cycle (ctx : ProcTyContext) :
      ProcTyJudgement ctx Proc.cycle ProcTy.cycle
    | dollar (ctx : ProcTyContext) (pid : ProcId) :
      ProcTyJudgement ctx (Proc.endp pid) (ProcTy.dollar pid)
    | skip (ctx : ProcTyContext) :
      ProcTyJudgement ctx Proc.skip ProcTy.skip
    | message_send (ctx : ProcTyContext) (msg : MessageId) (p : Proc) (e : Expr) :
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
