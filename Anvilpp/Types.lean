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
    private lemma sizeOf_snd_lt_of_mem {branch_tys : List (MessageExch × ProcTy)}
            {me : MessageExch} {ty : ProcTy} :
            (me, ty) ∈ branch_tys → sizeOf ty < sizeOf branch_tys := by
        intro hmem
        have hpair : sizeOf (me, ty) < sizeOf branch_tys := List.sizeOf_lt_of_mem hmem
        have hty : sizeOf ty < sizeOf (me, ty) := by
            simp
            omega
        exact Nat.lt_trans hty hpair

    mutual
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
                    ProcTy.xoffer (replaceVar τ_else x τ') (replaceBranches branch_tys x τ')
            | offer τ_else branch_tys =>
                    ProcTy.offer (replaceVar τ_else x τ') (replaceBranches branch_tys x τ')
            | var y => if x = y then τ' else ProcTy.var y
            | recur y body =>
                    if x = y then ProcTy.recur y body
                    else ProcTy.recur y (replaceVar body x τ')
        termination_by sizeOf τ

        def replaceBranches (branch_tys : List (MessageExch × ProcTy)) (x : String) (τ' : ProcTy) :
                List (MessageExch × ProcTy) :=
            match branch_tys with
            | [] => []
            | (me, ty) :: rest => (me, replaceVar ty x τ') :: replaceBranches rest x τ'
        termination_by sizeOf branch_tys
    decreasing_by
        all_goals
            simp_wf
            omega
    end

    def replaceBranchVar (branch_tys : MessageExch × ProcTy) (x : String) (τ' : ProcTy) :
            MessageExch × ProcTy :=
        (branch_tys.1, branch_tys.2.replaceVar x τ')

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
            ∀ τ, C τ := by
        let rec go (τ : ProcTy) : C τ := by
            match τ with
            | message me => exact H_message me
            | cycle => exact H_cycle
            | skip => exact H_skip
            | dollar pid => exact H_dollar pid
            | choice τ₁ τ₂ => exact H_choice τ₁ τ₂ (go τ₁) (go τ₂)
            | choice_fair bid τ₁ τ₂ => exact H_choice_fair bid τ₁ τ₂ (go τ₁) (go τ₂)
            | par τ₁ τ₂ => exact H_par τ₁ τ₂ (go τ₁) (go τ₂)
            | seq τ₁ τ₂ => exact H_seq τ₁ τ₂ (go τ₁) (go τ₂)
            | xoffer τ_else branch_tys =>
                exact H_xoffer τ_else branch_tys (go τ_else) (fun _ ty hmem => go ty)
            | offer τ_else branch_tys =>
                exact H_offer τ_else branch_tys (go τ_else) (fun _ ty hmem => go ty)
            | var x => exact H_var x
            | recur x body => exact H_recur x body (go body)
        termination_by sizeOf τ
        decreasing_by
            all_goals
                simp_wf
                first
                | omega
                |
                    have hty : sizeOf ty < sizeOf branch_tys := sizeOf_snd_lt_of_mem (branch_tys := branch_tys) hmem
                    omega
        intro τ
        exact go τ

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
