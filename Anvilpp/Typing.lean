import Anvilpp.Base
import Anvilpp.Proc
import Anvilpp.Types

abbrev ExprTyContext := Finset String

structure ProcTyContext where
  procVars : String → Option ProcTy
  exprVars : ExprTyContext

namespace ProcTyContext
  def empty : ProcTyContext :=
    { procVars := fun _ => none, exprVars := ∅ }

  def extendProcVar (ctx : ProcTyContext) (x : String) (ty : ProcTy) : ProcTyContext :=
    { ctx with procVars := fun y => if y = x then some ty else ctx.procVars y }

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
  | xoffer (ctx : ProcTyContext) (p_else : Proc) (branches : List ChoiceBranch) (τ_else : ProcTy) :
    (∀ m e p, ChoiceBranch.send m e p ∈ branches → ExprTyJudgement ctx.exprVars e) →
    ProcTyJudgement ctx p_else τ_else →
    ProcTyJudgement ctx (Proc.xoffer p_else branches) (ProcTy.xoffer τ_else []) -- FIXME: fill in branches
  | offer (ctx : ProcTyContext) (p_else : Proc) (branches : List ChoiceBranch) (τ_else : ProcTy) :
    (∀ m e p, ChoiceBranch.send m e p ∈ branches → ExprTyJudgement ctx.exprVars e) →
    ProcTyJudgement ctx p_else τ_else →
    ProcTyJudgement ctx (Proc.offer p_else branches) (ProcTy.offer τ_else []) -- FIXME: fill in branches
  | var (ctx : ProcTyContext) (x : String) (τ : ProcTy) :
    ctx.procVars x = some τ →
    ProcTyJudgement ctx (Proc.var x) τ
  | recur (ctx : ProcTyContext) (x : String) (p : Proc) (τ : ProcTy) :
    ProcTyJudgement (ctx.extendProcVar x τ) p τ →
    ProcTyJudgement ctx (Proc.recur x p) τ
