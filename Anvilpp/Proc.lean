import Mathlib.Data.Finset.Basic

abbrev MessageId := String
abbrev BranchId := Nat
abbrev ProcId := Nat

/-- Binary operators. -/
inductive BOp : Type where
  | and
  | or

/-- Anvil++ expressions. -/
inductive Expr : Type where
  | var : String → Expr
  | val : Bool → Expr
  | bin : Expr → BOp → Expr → Expr

def valEval (v₁ v₂ : Bool) (bop : BOp) :=
  match bop with
  | .and => v₁ && v₂
  | .or => v₁ || v₂

mutual
  /-- A branch in `offer` or `xoffer`. -/
  inductive ChoiceBranch : Type where
    | send : MessageId → Expr → Proc → ChoiceBranch
    | recv : MessageId → String → Proc → ChoiceBranch

  inductive Proc : Type where
    | send : MessageId → Expr → Proc
    | recv : MessageId → String → Proc → Proc
    | var : String → Proc
    | skip : Proc
    | endp : ProcId → Proc
    | cycle : Proc
    | par : Proc → Proc → Proc
    | seq : Proc → Proc → Proc
    -- | letin : String → Expr → Proc → Proc
    | ifunfair : Expr → Proc → Proc → Proc
    | iffair : BranchId → Expr → Proc → Proc → Proc
    | xoffer : Proc → List ChoiceBranch → Proc
    | offer : Proc → List ChoiceBranch → Proc
    /-- Recursion -/
    | recur : String → Proc → Proc
end

namespace ChoiceBranch
  def getMessageId : ChoiceBranch → MessageId
    | send msg _ _ => msg
    | recv msg _ _ => msg
end ChoiceBranch

inductive TransLabel : Type where
  | ε : TransLabel
  | tock : TransLabel
  | message : MessageId → Bool → TransLabel
  | branchTrue : BranchId → TransLabel
  | branchFalse : BranchId → TransLabel
  | dollar : ProcId → TransLabel

namespace Semantics
  inductive ExprEval : Expr → Bool → Prop where
    | literal (b : Bool) : ExprEval (Expr.val b) b
    | bin (e₁ e₂ : Expr) (b₁ b₂ : Bool) (bop : BOp) :
      ExprEval e₁ b₁ → ExprEval e₂ b₂ → ExprEval (Expr.bin e₁ bop e₂) (valEval b₁ b₂ bop)

  infix:80 " ↓ " => ExprEval

  example : (Expr.val true) ↓ true := ExprEval.literal true

  def exprReplace (e : Expr) (x : String) (v : Bool) : Expr :=
    match e with
    | Expr.var y => if x = y then Expr.val v else e
    | Expr.val _ => e
    | Expr.bin e₁ bop e₂ =>
      Expr.bin (exprReplace e₁ x v) bop (exprReplace e₂ x v)

  mutual
    def choiceBranchExprReplace (br : ChoiceBranch) (x : String) (v : Bool) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg (exprReplace e x v) (procExprReplace p x v)
      | ChoiceBranch.recv msg var p =>
        let p' := if x = var then p else procExprReplace p x v
        ChoiceBranch.recv msg var p'

    def procExprReplace (p : Proc) (x : String) (v : Bool) : Proc :=
      match p with
      | Proc.send msg e => Proc.send msg (exprReplace e x v)
      | Proc.recv msg var p' =>
        let p'' := if x = var then p' else procExprReplace p' x v
        Proc.recv msg var p''
      | Proc.var _ => p
      | Proc.skip => p
      | Proc.endp _ => p
      | Proc.cycle => p
      | Proc.par p₁ p₂ => Proc.par (procExprReplace p₁ x v) (procExprReplace p₂ x v)
      | Proc.seq p₁ p₂ => Proc.seq (procExprReplace p₁ x v) (procExprReplace p₂ x v)
      | Proc.ifunfair e p₁ p₂ =>
        Proc.ifunfair (exprReplace e x v) (procExprReplace p₁ x v) (procExprReplace p₂ x v)
      | Proc.iffair bid e p₁ p₂ =>
        Proc.iffair bid (exprReplace e x v) (procExprReplace p₁ x v) (procExprReplace p₂ x v)
      | Proc.xoffer p' branches =>
        Proc.xoffer (procExprReplace p' x v)
          (branches.map fun br => choiceBranchExprReplace br x v)
      | Proc.offer p' branches =>
        Proc.offer (procExprReplace p' x v)
          (branches.map fun br => choiceBranchExprReplace br x v)
      | Proc.recur f p' => Proc.recur f (procExprReplace p' x v)
  end

  mutual
    def choiceBranchProcReplace (br : ChoiceBranch) (f : String) (p_body : Proc) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg e (procReplace p f p_body)
      | ChoiceBranch.recv msg var p =>
        ChoiceBranch.recv msg var (procReplace p f p_body)

    def procReplace (p : Proc) (f : String) (p_body : Proc) : Proc :=
      match p with
      | Proc.var x => if x = f then p_body else p
      | Proc.send msg e => Proc.send msg e
      | Proc.recv msg var p' => Proc.recv msg var (procReplace p' f p_body)
      | Proc.skip => p
      | Proc.endp _ => p
      | Proc.cycle => p
      | Proc.par p₁ p₂ => Proc.par (procReplace p₁ f p_body) (procReplace p₂ f p_body)
      | Proc.seq p₁ p₂ => Proc.seq (procReplace p₁ f p_body) (procReplace p₂ f p_body)
      | Proc.ifunfair e p₁ p₂ =>
        Proc.ifunfair e (procReplace p₁ f p_body) (procReplace p₂ f p_body)
      | Proc.iffair bid e p₁ p₂ =>
        Proc.iffair bid e (procReplace p₁ f p_body) (procReplace p₂ f p_body)
      | Proc.xoffer p' branches =>
        Proc.xoffer (procReplace p' f p_body) (branches.map fun br => choiceBranchProcReplace br f p_body)
      | Proc.offer p' branches =>
        Proc.offer (procReplace p' f p_body) (branches.map fun br => choiceBranchProcReplace br f p_body)
      | Proc.recur g p' =>
        if g = f then Proc.recur g p' else Proc.recur g (procReplace p' f p_body)
  end


  inductive Reduces : Finset MessageId → Proc → TransLabel → Proc → Prop where
    | send ex_msg (msg : MessageId) (e : Expr) (p : Proc) (b : Bool) :
      e ↓ b →
      Reduces ex_msg (Proc.send msg e) (TransLabel.message msg b) p
    | recv ex_msg (msg : MessageId) (var : String) (p : Proc) (b : Bool) :
      Reduces ex_msg (Proc.recv msg var p) (TransLabel.message msg b) (procExprReplace p var b)
    | seq_step ex_msg (p₁ p₁' p₂ : Proc) (α : TransLabel) :
      Reduces ex_msg p₁ α p₁' →
      Reduces ex_msg (Proc.seq p₁ p₂) α (Proc.seq p₁' p₂)
    | seq_skip ex_msg (p₂ : Proc) :
      Reduces ex_msg (Proc.seq Proc.skip p₂) TransLabel.ε p₂
    | ifunfair_true ex_msg (e : Expr) (p₁ p₂ : Proc) (b : Bool) :
      e ↓ b →
      b = true →
      Reduces ex_msg (Proc.ifunfair e p₁ p₂) TransLabel.ε p₁
    | ifunfair_false ex_msg (e : Expr) (p₁ p₂ : Proc) (b : Bool) :
      e ↓ b →
      b = false →
      Reduces ex_msg (Proc.ifunfair e p₁ p₂) TransLabel.ε p₂
    | iffair_true ex_msg (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (b : Bool) :
      e ↓ b →
      b = true →
      Reduces ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.branchTrue bid) p₁
    | iffair_false ex_msg (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (b : Bool) :
      e ↓ b →
      b = false →
      Reduces ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.branchFalse bid) p₂
    | par_left ex_msg (p₁ p₁' p₂ : Proc) (α : TransLabel) :
      α ≠ TransLabel.tock →
      Reduces ex_msg p₁ α p₁' →
      Reduces ex_msg (Proc.par p₁ p₂) α (Proc.par p₁' p₂)
    | par_right ex_msg (p₁ p₂ p₂' : Proc) (α : TransLabel) :
      α ≠ TransLabel.tock →
      Reduces ex_msg p₂ α p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) α (Proc.par p₁ p₂')
    | par_tock ex_msg (p₁ p₂ p₁' p₂' : Proc) :
      Reduces ex_msg p₁ TransLabel.tock p₁' →
      Reduces ex_msg p₂ TransLabel.tock p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) TransLabel.tock (Proc.par p₁' p₂')
    | xoffer_branch_recv ex_msg (var : String) (p_else : Proc) (branches : List ChoiceBranch)
                         (msg : MessageId) (p' : Proc) (b : Bool) :
      ChoiceBranch.recv msg var p' ∈ branches →
      Reduces ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg b) (procExprReplace p' var b)
    | xoffer_branch_send ex_msg (msg : MessageId) (e : Expr) (p_else p' : Proc)
                         (branches : List ChoiceBranch) (b : Bool) :
      ChoiceBranch.send msg e p' ∈ branches →
      e ↓ b →
      Reduces ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg b) p'
    | xoffer_branch_else ex_msg (p_else : Proc) (branches : List ChoiceBranch) :
      ex_msg ∩ (branches.map ChoiceBranch.getMessageId).toFinset = ∅ →
      Reduces ex_msg (Proc.xoffer p_else branches) TransLabel.ε p_else
    | offer_branch_recv ex_msg (var : String) (p_else : Proc) (branches : List ChoiceBranch)
                         (msg : MessageId) (b : Bool) :
      -- let p' := List.foldl (fun acc br =>
      --     let p_branch :=
      --       match br with
      --       | ChoiceBranch.recv m v p'' =>
      --         if m = msg then procExprReplace p'' v b else Proc.xoffer Proc.skip [br]
      --       | _ => Proc.xoffer Proc.skip [br]
      --     Proc.par acc p_branch
      --   ) Proc.skip branches
      ChoiceBranch.recv msg var p' ∈ branches →
      Reduces ex_msg (Proc.offer p_else branches) (TransLabel.message msg b) p'
    | offer_branch_send ex_msg (msg : MessageId) (p_else p' : Proc)
                         (branches : List ChoiceBranch) (e : Expr) (b : Bool) :
      -- let p' := List.foldl (fun acc br =>
      --     let p_branch :=
      --       match br with
      --       | ChoiceBranch.send m e' p'' =>
      --         if m = msg then p'' else Proc.xoffer Proc.skip [br]
      --       | _ => Proc.xoffer Proc.skip [br]
      --     Proc.par acc p_branch
      --   ) Proc.skip branches
      ChoiceBranch.send msg e p' ∈ branches →
      Reduces ex_msg (Proc.offer p_else branches) (TransLabel.message msg b) p'
    | offer_branch_else ex_msg (p_else : Proc) (branches : List ChoiceBranch) :
      ex_msg ∩ (branches.map ChoiceBranch.getMessageId).toFinset = ∅ →
      Reduces ex_msg (Proc.offer p_else branches) TransLabel.ε p_else
    | recur_unfold ex_msg (f : String) (p_body : Proc) :
      Reduces ex_msg (Proc.recur f p_body) TransLabel.ε (procReplace p_body f $ Proc.recur f p_body)

end Semantics
