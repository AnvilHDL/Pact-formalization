import Mathlib.Data.Finset.Basic
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


/-! ## Process syntax and actions -/


inductive MessageDir : Type where
  | send : MessageDir
  | recv : MessageDir
  deriving DecidableEq

namespace MessageDir
  /-- `true` when directions are opposite and can synchronize. -/
  def dual : MessageDir → MessageDir → Bool
    | send, recv => true
    | recv, send => true
    | _, _ => false

  lemma dual_symm : ∀ (d₁ d₂ : MessageDir), dual d₁ d₂ = dual d₂ d₁ := by
    intros d₁ d₂
    cases d₁ <;> cases d₂ <;> rfl

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
    | send : MessageId → Expr → Proc
    | recv : MessageId → String → Proc → Proc
    | var : String → Proc
    | skip : Proc
    | endp : ProcId → Proc
    | cycle : Proc
    | par : Proc → Proc → MsgIdSet -> Proc
    | seq : Proc → Proc → Proc
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

  def getProc : ChoiceBranch → Proc
    | send _ _ p => p
    | recv _ _ p => p

  def getDir : ChoiceBranch → MessageDir
    | send _ _ _ => MessageDir.send
    | recv _ _ _ => MessageDir.recv

  def getMessage (br : ChoiceBranch) : MessageId × MessageDir :=
    (br.getMessageId, br.getDir)

  def toXOffer (br : ChoiceBranch) := Proc.xoffer Proc.skip [br]
end ChoiceBranch

/-! ## Transition labels -/

/-- Runtime actions emitted by visible process transitions. -/
inductive Action : Type where
  | tock : Action
  | fullMessage : MessageId → Action
  | branchTrue : BranchId → Action
  | branchFalse : BranchId → Action
  | dollar : ProcId → Action

inductive TransLabel : Type where
  | ac : Action → TransLabel
  | ε : TransLabel
  | ex : Finset (MessageId × MessageDir) → TransLabel
  | message : MessageId → MessageDir → Bool → TransLabel

namespace TransLabel
  /-- `true` exactly for exclusion labels. -/
  @[reducible]
  def isEx : TransLabel → Bool
    | TransLabel.ex _ => true
    | _ => false
end TransLabel

/-- Abstract versions of transition labels for automata. -/
inductive AbstractTransLabel : Type where
  | ac : Action → AbstractTransLabel
  | ε : AbstractTransLabel
  | ex : Finset (MessageId × MessageDir) → AbstractTransLabel
  | message : MessageId → MessageDir → AbstractTransLabel

namespace AbstractTransLabel
  /-- Forget concrete payload booleans from concrete transition labels. -/
  @[reducible]
  def fromConcrete : TransLabel → AbstractTransLabel
    | TransLabel.ac act => AbstractTransLabel.ac act
    | TransLabel.ε => AbstractTransLabel.ε
    | TransLabel.ex ex_msgs => AbstractTransLabel.ex ex_msgs
    | TransLabel.message msg dir _ => AbstractTransLabel.message msg dir

  /-- Compatibility relation between abstract and concrete labels. -/
  @[reducible]
  def Related (α : AbstractTransLabel) (c : TransLabel) : Prop :=
    match α, c with
    | AbstractTransLabel.ac act, TransLabel.ac act' =>
      match act, act' with
      | Action.branchTrue bid, Action.branchFalse bid' => bid = bid'
      | Action.branchFalse bid, Action.branchTrue bid' => bid = bid'
      | _, _ => act = act'
    | AbstractTransLabel.ε, TransLabel.ε => True
    | AbstractTransLabel.ex ex_msgs, TransLabel.ex ex_msgs' => ex_msgs = ex_msgs'
    | AbstractTransLabel.message msg dir, TransLabel.message msg' dir' _ =>
      msg = msg' ∧ dir = dir'
    | _, _ => False

  /-- `true` exactly for exclusion labels. -/
  @[reducible]
  def isEx : AbstractTransLabel → Bool
    | AbstractTransLabel.ex _ => true
    | _ => false

  namespace Related
    lemma is_ex_preserved (α : AbstractTransLabel) (c : TransLabel) :
        AbstractTransLabel.Related α c → (α.isEx ↔ c.isEx) := by
      intro H_related
      cases α <;> cases c <;> simp [AbstractTransLabel.Related, AbstractTransLabel.isEx, TransLabel.isEx] at H_related ⊢
  end Related
end AbstractTransLabel


/-! ## Operational semantics -/


namespace Semantics
  /-! ### Expression evaluation and substitution -/

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
    /-- Capture-avoiding replacement of an expression variable inside a choice branch. -/
    def choiceBranchExprReplace (br : ChoiceBranch) (x : String) (v : Bool) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg (exprReplace e x v) (procExprReplace p x v)
      | ChoiceBranch.recv msg var p =>
        let p' := if x = var then p else procExprReplace p x v
        ChoiceBranch.recv msg var p'

    /-- Capture-avoiding replacement of an expression variable inside a process. -/
    def procExprReplace (p : Proc) (x : String) (v : Bool) : Proc :=
      sorry
  end

  mutual
    /-- Replace recursive process variable occurrences inside a choice branch. -/
    def choiceBranchProcReplace (br : ChoiceBranch) (f : String) (p_body : Proc) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send msg e p =>
        ChoiceBranch.send msg e (procReplace p f p_body)
      | ChoiceBranch.recv msg var p =>
        ChoiceBranch.recv msg var (procReplace p f p_body)

    /-- Unfold-style replacement for recursion variables. -/
    def procReplace (p : Proc) (f : String) (p_body : Proc) : Proc :=
    sorry
  end

  abbrev ProcComp := Proc
end Semantics
