import Mathlib.Data.Finset.Basic
import Anvilpp.Base
import Anvilpp.Proc

inductive MessageExch : Type where
  | send : MessageId → MessageExch
  | recv : MessageId → MessageExch
deriving DecidableEq

namespace MessageExch
  def messageId : MessageExch → MessageId
    | send msg => msg
    | recv msg => msg

  def direction : MessageExch → MessageDir
    | send _ => MessageDir.send
    | recv _ => MessageDir.recv

  def toPair (me : MessageExch) : MessageId × MessageDir :=
    (me.messageId, me.direction)
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
  | xoffer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | offer : ProcTy → List (MessageExch × ProcTy) → ProcTy
  | var : String → ProcTy
  | recur : String → ProcTy → ProcTy

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
      | xoffer τ_else branch_tys =>
          ProcTy.xoffer (replaceVar τ_else x τ')
            (List.map (fun (me, ty) => (me, replaceVar ty x τ')) branch_tys)
      | offer τ_else branch_tys =>
          ProcTy.offer (replaceVar τ_else x τ')
            (List.map (fun (me, ty) => (me, replaceVar ty x τ')) branch_tys)
      | var y => if x = y then τ' else ProcTy.var y
      | recur y body =>
          if x = y then ProcTy.recur y body
          else ProcTy.recur y (replaceVar body x τ')
    decreasing_by  -- FIXME: prove termination
      all_goals sorry
  end

  -- TODO: see if this is actually useful
  theorem ind {C : ProcTy → Prop}
      (H_message : ∀ me, C (ProcTy.message me))
      (H_cycle : C ProcTy.cycle)
      (H_skip : C ProcTy.skip)
      (H_dollar : ∀ pid, C (ProcTy.dollar pid))
      (H_choice : ∀ τ₁ τ₂, C τ₁ → C τ₂ → C (ProcTy.choice τ₁ τ₂))
      (H_choice_fair : ∀ bid τ₁ τ₂, C τ₁ → C τ₂ → C (ProcTy.choice_fair bid τ₁ τ₂))
      (H_par : ∀ τ₁ τ₂, C τ₁ → C τ₂ → C (ProcTy.par τ₁ τ₂))
      (H_seq : ∀ τ₁ τ₂, C τ₁ → C τ₂ → C (ProcTy.seq τ₁ τ₂))
      (H_xoffer : ∀ τ_else branch_tys,
          C τ_else →
          (∀ me ty, (me, ty) ∈ branch_tys → C ty) →
          C (ProcTy.xoffer τ_else branch_tys))
      (H_offer : ∀ τ_else branch_tys,
          C τ_else →
          (∀ me ty, (me, ty) ∈ branch_tys → C ty) →
          C (ProcTy.offer τ_else branch_tys))
      (H_var : ∀ x, C (ProcTy.var x))
      (H_recur : ∀ x body, C body → C (ProcTy.recur x body)) :
      ∀ τ, C τ := sorry

  /-- Well-formedness of process types.
      This says that the type only includes tail recursions. -/
  inductive Wellformed : Finset String → ProcTy → Prop where
    | var (Γ : Finset String) (x : String) :
        x ∈ Γ → Wellformed Γ (ProcTy.var x)
    | cycle (Γ : Finset String) :
        Wellformed Γ ProcTy.cycle
    | skip (Γ : Finset String) :
        Wellformed Γ ProcTy.skip
    | message (Γ : Finset String) (me : MessageExch) :
        Wellformed Γ (ProcTy.message me)
    | dollar (Γ : Finset String) (pid : ProcId) :
        Wellformed Γ (ProcTy.dollar pid)
    | seq (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
        Wellformed ∅ τ₁ → Wellformed Γ τ₂ → Wellformed Γ (ProcTy.seq τ₁ τ₂)
    | par (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
        Wellformed ∅ τ₁ → Wellformed ∅ τ₂ → Wellformed Γ (ProcTy.par τ₁ τ₂)
    | recur (Γ : Finset String) (x : String) (body : ProcTy) :
        Wellformed (Γ ∪ {x}) body → Wellformed Γ (ProcTy.recur x body)
    | choice (Γ : Finset String) (τ₁ τ₂ : ProcTy) :
        Wellformed Γ τ₁ → Wellformed Γ τ₂ → Wellformed Γ (ProcTy.choice τ₁ τ₂)
    | choice_fair (Γ : Finset String) (bid : BranchId) (τ₁ τ₂ : ProcTy) :
        Wellformed Γ τ₁ → Wellformed Γ τ₂ →
        Wellformed Γ (ProcTy.choice_fair bid τ₁ τ₂)
    | xoffer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
        Wellformed Γ τ_else →
        (∀ me ty, (me, ty) ∈ branch_tys → Wellformed Γ ty) →
        Wellformed Γ (ProcTy.xoffer τ_else branch_tys)
    | offer (Γ : Finset String) (τ_else : ProcTy) (branch_tys : List (MessageExch × ProcTy)) :
        Wellformed Γ τ_else →
        (∀ me ty, (me, ty) ∈ branch_tys → Wellformed ∅ ty) →
        Wellformed Γ (ProcTy.offer τ_else branch_tys)
end ProcTy

abbrev ProcTyComposition := ProcTy
