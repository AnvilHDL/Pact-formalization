import Anvilpp.Base

/-! ## Expression syntax -/

/-- Binary operators. -/
inductive BOp : Type where
  | and
  | or

/-- Anvil++ expressions. -/
inductive Expr : Type where
  | var : String → Expr
  | val : Bool → Expr
  | bin : Expr → BOp → Expr → Expr

/-- Evaluate a binary boolean operator on two concrete boolean values. -/
def valEval (v₁ v₂ : Bool) (bop : BOp) :=
  match bop with
  | .and => v₁ && v₂
  | .or => v₁ || v₂


/-! ## Process syntax -/


inductive MessageDir : Type where
  | send : MessageDir
  | recv : MessageDir
  deriving DecidableEq

namespace MessageDir
  /-- Flip direction between send and recv. -/
  def invert (dir : MessageDir) : MessageDir :=
    match dir with
    | send => recv
    | recv => send
end MessageDir

mutual
  /-- A branch in `offer` or `xoffer`. -/
  inductive ChoiceBranch : Type where
    | send : MessageId → Expr → Proc → ChoiceBranch
    | recv : MessageId → String → Proc → ChoiceBranch

  inductive Proc : Type where
    | send : MessageId → Expr → Proc → Proc
    | recv : MessageId → String → Proc → Proc
    | var : String → Proc
    | skip : Proc
    | endp : ProcId → Proc
    | cycle : Proc
    | par : Proc → Proc → MsgIdSet → Proc
    | seq : Proc → Proc → Proc
    | letp : String → Expr → Proc → Proc
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

  def getDir : ChoiceBranch → MessageDir
    | send _ _ _ => MessageDir.send
    | recv _ _ _ => MessageDir.recv

  def toXOffer (br : ChoiceBranch) := Proc.xoffer Proc.skip [br]
end ChoiceBranch


/-! ## Operational semantics -/


namespace Semantics
  /-! ### Expression evaluation and substitution -/

  inductive ExprEval : Expr → Bool → Prop where
    | literal (b : Bool) : ExprEval (Expr.val b) b
    | bin (e₁ e₂ : Expr) (b₁ b₂ : Bool) (bop : BOp) :
      ExprEval e₁ b₁ → ExprEval e₂ b₂ → ExprEval (Expr.bin e₁ bop e₂) (valEval b₁ b₂ bop)

  infix:80 " ↓ " => ExprEval

  example : (Expr.val true) ↓ true := ExprEval.literal true

  /-- Computable companion to `ExprEval`.  Agrees with it on every closed
  expression; a free variable (which `ExprEval` never assigns a value to)
  simply yields `none`. -/
  def exprEvalOpt : Expr → Option Bool
    | Expr.var _ => none
    | Expr.val b => some b
    | Expr.bin e₁ bop e₂ =>
        match exprEvalOpt e₁, exprEvalOpt e₂ with
        | some b₁, some b₂ => some (valEval b₁ b₂ bop)
        | _, _ => none

  def exprReplace (e : Expr) (x : String) (v : Bool) : Expr :=
    match e with
    | Expr.var y => if x = y then Expr.val v else e
    | Expr.val _ => e
    | Expr.bin e₁ bop e₂ =>
      Expr.bin (exprReplace e₁ x v) bop (exprReplace e₂ x v)

  mutual
    /-- Capture-avoiding replacement of an expression variable inside a choice branch. -/
    def choiceBranchExprReplace (br : ChoiceBranch) (x : String) (v : Bool) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg (exprReplace e x v) (procExprReplace p x v)
      | ChoiceBranch.recv msg var p =>
        let p' := if x = var then p else procExprReplace p x v
        ChoiceBranch.recv msg var p'

    /-- Replace expression variable occurrences inside a branch list. -/
    def choiceBranchesExprReplace
        (branches : List ChoiceBranch) (x : String) (v : Bool) : List ChoiceBranch :=
      match branches with
      | [] => []
      | br :: rest =>
          choiceBranchExprReplace br x v :: choiceBranchesExprReplace rest x v

    /-- Capture-avoiding replacement of an expression variable inside a
    process.  `recv` and `letp` bind a data variable of their own: a nested
    occurrence of `x` under that binder refers to the inner binding, so the
    body is left untouched exactly when the binder shadows `x`. Recursion
    binders (`recur`, `var`) live in a separate namespace from data variables
    and are always traversed. -/
    def procExprReplace (p : Proc) (x : String) (v : Bool) : Proc :=
      match p with
      | Proc.send msg e p' =>
          Proc.send msg (exprReplace e x v) (procExprReplace p' x v)
      | Proc.recv msg var p' =>
          Proc.recv msg var (if x = var then p' else procExprReplace p' x v)
      | Proc.var name => Proc.var name
      | Proc.skip => Proc.skip
      | Proc.endp pid => Proc.endp pid
      | Proc.cycle => Proc.cycle
      | Proc.par left right interface =>
          Proc.par (procExprReplace left x v) (procExprReplace right x v) interface
      | Proc.seq left right =>
          Proc.seq (procExprReplace left x v) (procExprReplace right x v)
      | Proc.letp var e p' =>
          Proc.letp var (exprReplace e x v)
            (if x = var then p' else procExprReplace p' x v)
      | Proc.ifunfair e left right =>
          Proc.ifunfair (exprReplace e x v) (procExprReplace left x v)
            (procExprReplace right x v)
      | Proc.iffair bid e left right =>
          Proc.iffair bid (exprReplace e x v) (procExprReplace left x v)
            (procExprReplace right x v)
      | Proc.xoffer elseProcess branches =>
          Proc.xoffer (procExprReplace elseProcess x v)
            (choiceBranchesExprReplace branches x v)
      | Proc.offer elseProcess branches =>
          Proc.offer (procExprReplace elseProcess x v)
            (choiceBranchesExprReplace branches x v)
      | Proc.recur name body => Proc.recur name (procExprReplace body x v)
  end

  mutual
    /-- Replace recursive process variable occurrences inside a choice branch. -/
    def choiceBranchProcReplace (br : ChoiceBranch) (f : String) (p_body : Proc) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg e (procReplace p f p_body)
      | ChoiceBranch.recv msg var p =>
        ChoiceBranch.recv msg var (procReplace p f p_body)

    /-- Replace recursive process variable occurrences inside a branch list. -/
    def choiceBranchesProcReplace
        (branches : List ChoiceBranch) (f : String) (p_body : Proc) : List ChoiceBranch :=
      match branches with
      | [] => []
      | br :: rest =>
          choiceBranchProcReplace br f p_body :: choiceBranchesProcReplace rest f p_body

    /-- Unfold-style replacement for recursion variables.  `recv`/`letp`
    binders are data variables, a disjoint namespace from process-recursion
    variables, so they are always traversed; a `recur` binder shadows `f`
    exactly when it reuses the same name. -/
    def procReplace (p : Proc) (f : String) (p_body : Proc) : Proc :=
      match p with
      | Proc.send msg e p' => Proc.send msg e (procReplace p' f p_body)
      | Proc.recv msg var p' => Proc.recv msg var (procReplace p' f p_body)
      | Proc.var name => if f = name then p_body else Proc.var name
      | Proc.skip => Proc.skip
      | Proc.endp pid => Proc.endp pid
      | Proc.cycle => Proc.cycle
      | Proc.par left right interface =>
          Proc.par (procReplace left f p_body) (procReplace right f p_body) interface
      | Proc.seq left right =>
          Proc.seq (procReplace left f p_body) (procReplace right f p_body)
      | Proc.letp var e p' => Proc.letp var e (procReplace p' f p_body)
      | Proc.ifunfair e left right =>
          Proc.ifunfair e (procReplace left f p_body) (procReplace right f p_body)
      | Proc.iffair bid e left right =>
          Proc.iffair bid e (procReplace left f p_body) (procReplace right f p_body)
      | Proc.xoffer elseProcess branches =>
          Proc.xoffer (procReplace elseProcess f p_body)
            (choiceBranchesProcReplace branches f p_body)
      | Proc.offer elseProcess branches =>
          Proc.offer (procReplace elseProcess f p_body)
            (choiceBranchesProcReplace branches f p_body)
      | Proc.recur name body =>
          if f = name then Proc.recur name body
          else Proc.recur name (procReplace body f p_body)
  end
end Semantics

/-! ## Well-formedness -/

/-- Every `Expr.var` occurrence is included in the ambient bound-data-variable
list. -/
def Expr.AllVariablesBound (bound : List String) : Expr → Prop
  | Expr.var name => name ∈ bound
  | Expr.val _ => True
  | Expr.bin left _ right =>
      Expr.AllVariablesBound bound left ∧ Expr.AllVariablesBound bound right

mutual
  /-- Every `Proc.var` (recursion) and `Expr.var` (data) occurrence is
  included in its respective ambient bound list. `recur` extends the
  process-variable context; `recv`/`letp` extend the data-variable context. -/
  def Proc.AllVariablesBound (procVars dataVars : List String) : Proc → Prop
    | Proc.send _ expr p =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars p
    | Proc.recv _ varName p =>
        Proc.AllVariablesBound procVars (varName :: dataVars) p
    | Proc.var name => name ∈ procVars
    | Proc.skip => True
    | Proc.endp _ => True
    | Proc.cycle => True
    | Proc.par left right _ =>
        Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.seq left right =>
        Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.letp varName expr p =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars (varName :: dataVars) p
    | Proc.ifunfair expr left right =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.iffair _ expr left right =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.xoffer elseProcess branches =>
        Proc.AllVariablesBound procVars dataVars elseProcess ∧
          Proc.AllBranchVariablesBound procVars dataVars branches
    | Proc.offer elseProcess branches =>
        Proc.AllVariablesBound procVars dataVars elseProcess ∧
          Proc.AllBranchVariablesBound procVars dataVars branches
    | Proc.recur name body =>
        Proc.AllVariablesBound (name :: procVars) dataVars body

  def Proc.AllBranchVariablesBound
      (procVars dataVars : List String) : List ChoiceBranch → Prop
    | [] => True
    | ChoiceBranch.send _ expr p :: rest =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
    | ChoiceBranch.recv _ varName p :: rest =>
        Proc.AllVariablesBound procVars (varName :: dataVars) p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
end

/-- Every process- and data-variable in `P` is bound. -/
def WFProc (process : Proc) : Prop := Proc.AllVariablesBound [] [] process
