import Mathlib.Data.Finset.Basic
import Anvilpp.Base

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


inductive MessageDir : Type where
  | send : MessageDir
  | recv : MessageDir
  deriving DecidableEq

namespace MessageDir
  def dual : MessageDir → MessageDir → Bool
    | send, recv => true
    | recv, send => true
    | _, _ => false

  def invert (dir : MessageDir) : MessageDir :=
    match dir with
    | send => recv
    | recv => send
end MessageDir

inductive Action : Type where
  | tock : Action
  | fullMessage : MessageId → Action
  | branchTrue : BranchId → Action
  | branchFalse : BranchId → Action
  | dollar : ProcId → Action

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

inductive TransLabel : Type where
  | ac : Action → TransLabel
  | ε : TransLabel
  | message : MessageId → MessageDir → Bool → TransLabel

/-- Abstract versions of transition labels for automata. -/
inductive AbstractTransLabel : Type where
  | ac : Action → AbstractTransLabel
  | ε : AbstractTransLabel
  | message : MessageId → MessageDir → AbstractTransLabel

namespace AbstractTransLabel
  @[reducible]
  def fromConcrete : TransLabel → AbstractTransLabel
    | TransLabel.ac act => AbstractTransLabel.ac act
    | TransLabel.ε => AbstractTransLabel.ε
    | TransLabel.message msg dir _ => AbstractTransLabel.message msg dir
end AbstractTransLabel


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

  inductive NonInstantReducible : Finset String → Proc → Prop where
    | cycle (Γ : Finset String) : NonInstantReducible Γ Proc.cycle
    | par_left (Γ : Finset String) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₁ →
      NonInstantReducible Γ (Proc.par p₁ p₂)
    | par_right (Γ : Finset String) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₂ →
      NonInstantReducible Γ (Proc.par p₁ p₂)
    | seq_left (Γ : Finset String) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₁ →
      NonInstantReducible Γ (Proc.seq p₁ p₂)
    | seq_right (Γ : Finset String) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₂ →
      NonInstantReducible Γ (Proc.seq p₁ p₂)
    | xoffer (Γ : Finset String) (p_else : Proc) (branches : List ChoiceBranch) :
      NonInstantReducible Γ p_else →
      ∀ br ∈ branches, NonInstantReducible Γ (ChoiceBranch.getProc br) →
      NonInstantReducible Γ (Proc.xoffer p_else branches)
    | offer (Γ : Finset String) (p_else : Proc) (branches : List ChoiceBranch) :
      NonInstantReducible Γ p_else →
      ∀ br ∈ branches, NonInstantReducible Γ (ChoiceBranch.getProc br) →
      NonInstantReducible Γ (Proc.offer p_else branches)
    | ifunfair (Γ : Finset String) (e : Expr) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₁ →
      NonInstantReducible Γ p₂ →
      NonInstantReducible Γ (Proc.ifunfair e p₁ p₂)
    | iffair (Γ : Finset String) (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) :
      NonInstantReducible Γ p₁ →
      NonInstantReducible Γ p₂ →
      NonInstantReducible Γ (Proc.iffair bid e p₁ p₂)
    | var (Γ : Finset String) (x : String) :
      x ∈ Γ →
      NonInstantReducible Γ (Proc.var x)
    | recur (Γ : Finset String) (f : String) (p_body : Proc) :
      NonInstantReducible (Γ ∪ {f}) p_body →
      NonInstantReducible Γ (Proc.recur f p_body)
    | recv (Γ : Finset String) (msg : MessageId) (var : String) (p : Proc) :
      NonInstantReducible Γ p →
      NonInstantReducible Γ (Proc.recv msg var p)

  inductive NonInstantMessage : Finset String → Finset String → Proc → (MessageId × MessageDir) → Prop where
    | recv (Γ₁ Γ₂ : Finset String) (msg m : MessageId) (var : String) (p : Proc) :
      msg ≠ m →
      NonInstantMessage Γ₁ Γ₂ p (m, MessageDir.recv) →
      NonInstantMessage Γ₁ Γ₂ (Proc.recv msg var p) (m, MessageDir.recv)
    | recv_opposite (Γ₁ Γ₂ : Finset String) (msg m : MessageId) (var : String) (p : Proc) :
      NonInstantMessage Γ₁ Γ₂ p (m, MessageDir.send) →
      NonInstantMessage Γ₁ Γ₂ (Proc.recv msg var p) (m, MessageDir.send)
    | send (Γ₁ Γ₂ : Finset String) (msg m : MessageId) (e : Expr) :
      msg ≠ m →
      NonInstantMessage Γ₁ Γ₂ (Proc.send msg e) (m, MessageDir.send)
    | send_opposite (Γ₁ Γ₂ : Finset String) (msg m : MessageId) (e : Expr) :
      NonInstantMessage Γ₁ Γ₂ (Proc.send msg e) (m, MessageDir.recv)
    | cycle (Γ₁ Γ₂ : Finset String) (m : MessageId) (d : MessageDir) :
      NonInstantMessage Γ₁ Γ₂ Proc.cycle (m, d)
    | skip (Γ₁ Γ₂ : Finset String) (m : MessageId) (d : MessageDir) :
      NonInstantMessage Γ₁ Γ₂ Proc.skip (m, d)
    | par (Γ₁ Γ₂ : Finset String) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p₁ mx →
      NonInstantMessage Γ₁ Γ₂ p₂ mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.par p₁ p₂) mx
    | seq (Γ₁ Γ₂ : Finset String) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p₁ mx →
      NonInstantMessage Γ₁ Γ₂ p₂ mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.seq p₁ p₂) mx
    | seq_noninst (Γ₁ Γ₂ : Finset String) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p₁ mx →
      NonInstantReducible Γ₁ p₁ →
      NonInstantMessage Γ₁ Γ₂ (Proc.seq p₁ p₂) mx
    | xoffer (Γ₁ Γ₂ : Finset String) (p_else : Proc) (branches : List ChoiceBranch) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p_else mx →
      (∀ br ∈ branches, NonInstantMessage Γ₁ Γ₂ br.getProc mx) →
      (∀ br ∈ branches, br.getMessage ≠ mx) →
      NonInstantMessage Γ₁ Γ₂ (Proc.xoffer p_else branches) mx
    | offer (Γ₁ Γ₂ : Finset String) (p_else : Proc) (branches : List ChoiceBranch) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p_else mx →
      (∀ br ∈ branches, NonInstantMessage Γ₁ Γ₂ br.getProc mx) →
      (∀ br ∈ branches, br.getMessage ≠ mx) →
      NonInstantMessage Γ₁ Γ₂ (Proc.offer p_else branches) mx
    | ifunfair (Γ₁ Γ₂ : Finset String) (e : Expr) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p₁ mx →
      NonInstantMessage Γ₁ Γ₂ p₂ mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.ifunfair e p₁ p₂) mx
    | iffair (Γ₁ Γ₂ : Finset String) (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage Γ₁ Γ₂ p₁ mx →
      NonInstantMessage Γ₁ Γ₂ p₂ mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.iffair bid e p₁ p₂) mx
    | var (Γ₁ Γ₂ : Finset String) (x : String) (mx : MessageId × MessageDir) :
      x ∈ Γ₂ →
      NonInstantMessage Γ₁ Γ₂ (Proc.var x) mx
    | recur_instant (Γ₁ Γ₂ : Finset String) (f : String) (p_body : Proc) (mx : MessageId × MessageDir) :
      NonInstantReducible Γ₁ (Proc.recur f p_body) →
      NonInstantMessage (Γ₁ ∪ {f}) (Γ₂ ∪ {f}) p_body mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.recur f p_body) mx
    | recur_noninstant (Γ₁ Γ₂ : Finset String) (f : String) (p_body : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage (Γ₁ \ {f}) (Γ₂ ∪ {f}) p_body mx →
      NonInstantMessage Γ₁ Γ₂ (Proc.recur f p_body) mx



  inductive Reduces : Finset (MessageId × MessageDir) → Proc → TransLabel → Proc → Prop where
    | tock ex_msg :
      Reduces ex_msg Proc.cycle (TransLabel.ac Action.tock) Proc.skip
    | send ex_msg (msg : MessageId) (e : Expr) (b : Bool) :
      e ↓ b →
      Reduces ex_msg (Proc.send msg e) (TransLabel.message msg MessageDir.send b) Proc.skip
    | recv ex_msg (msg : MessageId) (var : String) (p : Proc) (b : Bool) :
      Reduces ex_msg (Proc.recv msg var p) (TransLabel.message msg MessageDir.recv b)
        $ Proc.seq Proc.skip (procExprReplace p var b)
    | seq_step ex_msg (p₁ p₁' p₂ : Proc) (c : TransLabel) :
      Reduces ex_msg p₁ c p₁' →
      Reduces ex_msg (Proc.seq p₁ p₂) c (Proc.seq p₁' p₂)
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
      Reduces ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.ac $ Action.branchTrue bid) p₁
    | iffair_false ex_msg (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (b : Bool) :
      e ↓ b →
      b = false →
      Reduces ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.ac $ Action.branchFalse bid) p₂
    | par_left ex_msg ex_msg' (p₁ p₁' p₂ : Proc) (c : TransLabel) :
      c ≠ (TransLabel.ac Action.tock) →
      ex_msg' ⊆ ex_msg →
      (∀ mx ∈ ex_msg', NonInstantMessage ∅ ∅ p₂ mx) →
      Reduces ex_msg' p₁ c p₁' →
      Reduces ex_msg (Proc.par p₁ p₂) c (Proc.par p₁' p₂)
    | par_right ex_msg ex_msg' (p₁ p₂ p₂' : Proc) (c : TransLabel) :
      c ≠ (TransLabel.ac Action.tock) →
      ex_msg' ⊆ ex_msg →
      (∀ mx ∈ ex_msg', NonInstantMessage ∅ ∅ p₁ mx) →
      Reduces ex_msg' p₂ c p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) c (Proc.par p₁ p₂')
    | par_tock ex_msg (p₁ p₂ p₁' p₂' : Proc) :
      Reduces ex_msg p₁ (TransLabel.ac Action.tock) p₁' →
      Reduces ex_msg p₂ (TransLabel.ac Action.tock) p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) (TransLabel.ac Action.tock) (Proc.par p₁' p₂')
    | par_skip_right ex_msg (p₁ : Proc) :
      Reduces ex_msg (Proc.par p₁ Proc.skip) TransLabel.ε p₁
    | par_skip_left ex_msg (p₂ : Proc) :
      Reduces ex_msg (Proc.par Proc.skip p₂) TransLabel.ε p₂
    | par_message ex_msg ex_msg₁ ex_msg₂ (msg : MessageId) (dir dir' : MessageDir) (b : Bool)
                      (p₁ p₁' p₂ p₂' : Proc) :
      MessageDir.dual dir dir' →
      ex_msg₁ ⊆ ex_msg →
      ex_msg₂ ⊆ ex_msg →
      (∀ mx ∈ ex_msg₂, NonInstantMessage ∅ ∅ p₁ mx) →
      (∀ mx ∈ ex_msg₁, NonInstantMessage ∅ ∅ p₂ mx) →
      Reduces ex_msg₁ p₁ (TransLabel.message msg dir b) p₁' →
      Reduces ex_msg₂ p₂ (TransLabel.message msg dir' b) p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) (TransLabel.ac $ Action.fullMessage msg) (Proc.par p₁' p₂')
    | xoffer_branch_recv ex_msg (var : String) (p_else : Proc) (branches : List ChoiceBranch)
                         (msg : MessageId) (p' : Proc) (b : Bool) :
      ChoiceBranch.recv msg var p' ∈ branches →
      Reduces ex_msg (Proc.xoffer p_else branches) (TransLabel.ac $ Action.fullMessage msg) (procExprReplace p' var b)
    | xoffer_branch_send ex_msg (msg : MessageId) (e : Expr) (p_else p' : Proc)
                         (branches : List ChoiceBranch) (b : Bool) :
      ChoiceBranch.send msg e p' ∈ branches →
      e ↓ b →
      Reduces ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg MessageDir.send b) p'
    | xoffer_branch_else ex_msg (p_else : Proc) (branches : List ChoiceBranch) :
      (∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg) →
      Reduces ex_msg (Proc.xoffer p_else branches) TransLabel.ε p_else
    | offer_branch_recv ex_msg (var : String) (p_branch p_else : Proc) (branches : List ChoiceBranch) (idx : ℕ)
                         (msg : MessageId) (b : Bool) (branches' : List Proc) (p' : Proc) :
      branches' = branches.map ChoiceBranch.toXOffer →
      p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip ((procExprReplace p_branch var b)::branches') →
      idx < branches.length + 1 →
      Reduces ex_msg (Proc.offer p_else $ branches.insertIdx idx (ChoiceBranch.recv msg var p_branch)) (TransLabel.message msg MessageDir.recv b) p'
    | offer_branch_send ex_msg (msg : MessageId) (p_else p_branch : Proc)
                         (branches : List ChoiceBranch) (idx : ℕ) (branches' : List Proc) (p' : Proc) (e : Expr) (b : Bool) :
      e ↓ b →
      branches' = branches.map ChoiceBranch.toXOffer →
      p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip (p_branch::branches') →
      idx < branches.length + 1 →
      Reduces ex_msg (Proc.offer p_else $ branches.insertIdx idx (ChoiceBranch.send msg e p_branch)) (TransLabel.message msg MessageDir.send b) p'
    | offer_branch_else ex_msg (p_else : Proc) (branches : List ChoiceBranch) :
      (∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg) →
      Reduces ex_msg (Proc.offer p_else branches) TransLabel.ε p_else
    | recur_unfold ex_msg (f : String) (p_body : Proc) :
      Reduces ex_msg (Proc.recur f p_body) TransLabel.ε (procReplace p_body f $ Proc.recur f p_body)

  abbrev ProcComp := Proc
  -- def CompReduces (c₁ : ProcComp) (α : Action) (c₂ : ProcComp) : Prop :=
  --   ∃ ex_msg : Finset (MessageId × MessageDir), Reduces ex_msg c₁ (TransLabel.ac α) c₂
  inductive CompElim : Finset (MessageId × MessageDir) → Proc → Proc → Prop where
    | refl ex_msg (p : Proc) :
      CompElim ex_msg p p
    | eps_elim ex_msg (p p' p'' : Proc) :
      Reduces ex_msg p TransLabel.ε p' →
      CompElim ex_msg p' p'' →
      CompElim ex_msg p p''

  @[reducible]
  def IncompReduces (ex_msg : Finset (MessageId × MessageDir)) (p₁ : Proc) (lbl : TransLabel) (p₂ : Proc) : Prop :=
    ∃ p₁' p₂' : Proc, Reduces ex_msg p₁' lbl p₂' ∧ CompElim ex_msg p₁ p₁' ∧ CompElim ex_msg p₂' p₂

  @[reducible]
  def CompReduces (ex_msg : Finset (MessageId × MessageDir)) (p₁ : Proc) (α : Action) (p₂ : Proc) : Prop :=
    IncompReduces ex_msg p₁ (TransLabel.ac α) p₂
end Semantics
