import Mathlib.Data.Finset.Basic
import Anvilpp.Base

inductive MessageExch : Type where
  | send : MessageId → MessageExch
  | recv : MessageId → MessageExch
deriving DecidableEq

namespace MessageExch
  def messageId : MessageExch → MessageId
    | send msg => msg
    | recv msg => msg
end MessageExch

/-- Process type. -/
inductive ProcTy : Type where
  | message : MessageExch → ProcTy
  | cycle : ProcTy
  | skip : ProcTy
  | dollar : ProcId → ProcTy
  | choice : ProcTy → ProcTy → ProcTy
  | choice_fair : BranchId → ProcTy → ProcTy → ProcTy
  | par : ProcTy → ProcTy → ProcTy
  | seq : ProcTy → ProcTy → ProcTy
  -- | xoffer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  -- | offer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | var : String → ProcTy
  | recur : String → ProcTy → ProcTy

-- FIXME: Lean cannot automatically derive DecidableEq for this yet
instance : DecidableEq ProcTy := by sorry

namespace ProcTy
  mutual
    def replaceBranchVar (branch_tys : MessageExch × ProcTy) (x : String) (τ' : ProcTy) :
        MessageExch × ProcTy :=
      (branch_tys.1, branch_tys.2.replaceVar x τ')

    /-- Replace occurrences of a process type variable with another process type. -/
    def replaceVar (τ : ProcTy) (x : String) (τ' : ProcTy) : ProcTy :=
      match τ with
      | message me => ProcTy.message me
      | cycle => ProcTy.cycle
      | skip => ProcTy.skip
      | dollar pid => ProcTy.dollar pid
      | choice τ₁ τ₂ => ProcTy.choice (replaceVar τ₁ x τ') (replaceVar τ₂ x τ')
      | choice_fair bid τ₁ τ₂ =>
          ProcTy.choice_fair bid (replaceVar τ₁ x τ') (replaceVar τ₂ x τ')
      | par τ₁ τ₂ => ProcTy.par (replaceVar τ₁ x τ') (replaceVar τ₂ x τ')
      | seq τ₁ τ₂ => ProcTy.seq (replaceVar τ₁ x τ') (replaceVar τ₂ x τ')
      -- | xoffer τ_else branch_tys =>
      --     ProcTy.xoffer (replaceVar τ_else x τ')
      --       (List.map (fun (me, ty) => (me, replaceVar ty x τ')) branch_tys)
      -- | offer τ_else branch_tys =>
      --     ProcTy.offer (replaceVar τ_else x τ')
      --       (List.map (fun (me, ty) => (me, replaceVar ty x τ')) branch_tys)
      | var y => if x = y then τ' else ProcTy.var y
      | recur y body =>
          if x = y then ProcTy.recur y body
          else ProcTy.recur y (replaceVar body x τ')
    decreasing_by  -- FIXME: prove termination
      all_goals sorry
  end
end ProcTy

abbrev ProcTyComposition := ProcTy
