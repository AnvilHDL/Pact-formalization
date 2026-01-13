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

  def toXOffer (br : ChoiceBranch) := Proc.xoffer Proc.skip [br]
end ChoiceBranch

inductive TransLabel : Type where
  | ε : TransLabel
  | tock : TransLabel
  | message : MessageId → Bool → TransLabel
  | branchTrue : BranchId → TransLabel
  | branchFalse : BranchId → TransLabel
  | dollar : ProcId → TransLabel

namespace TransLabel
  def isAsync (α : TransLabel) : Bool :=
    match α with
    | ε | branchTrue _
    | branchFalse _ | dollar _ => false
    | tock | message _ _ => true
end TransLabel

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
    | par_skip_right ex_msg (p₁ : Proc) :
      Reduces ex_msg (Proc.par p₁ Proc.skip) TransLabel.ε p₁
    | par_skip_left ex_msg (p₂ : Proc) :
      Reduces ex_msg (Proc.par Proc.skip p₂) TransLabel.ε p₂
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
    | offer_branch_recv ex_msg (var : String) (p_branch p_else : Proc) (branches : List ChoiceBranch)
                         (msg : MessageId) (b : Bool) (lbranches rbranches : List ChoiceBranch) :
      branches = lbranches ++ (ChoiceBranch.recv msg var p_branch) :: rbranches →
      branches' = lbranches.map ChoiceBranch.toXOffer ++ (procExprReplace p_branch var b) :: rbranches.map ChoiceBranch.toXOffer →
      p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip branches' →
      Reduces ex_msg (Proc.offer p_else branches) (TransLabel.message msg b) p'
    | offer_branch_send ex_msg (msg : MessageId) (p_else p_branch : Proc)
                         (lbranches rbranches : List ChoiceBranch) (e : Expr) (b : Bool) :
      e ↓ b →
      branches = lbranches ++ (ChoiceBranch.send msg e p') :: rbranches →
      branches' = lbranches.map ChoiceBranch.toXOffer ++ p_branch :: rbranches.map ChoiceBranch.toXOffer →
      p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip branches' →
      Reduces ex_msg (Proc.offer p_else branches) (TransLabel.message msg b) p'
    | offer_branch_else ex_msg (p_else : Proc) (branches : List ChoiceBranch) :
      ex_msg ∩ (branches.map ChoiceBranch.getMessageId).toFinset = ∅ →
      Reduces ex_msg (Proc.offer p_else branches) TransLabel.ε p_else
    | recur_unfold ex_msg (f : String) (p_body : Proc) :
      Reduces ex_msg (Proc.recur f p_body) TransLabel.ε (procReplace p_body f $ Proc.recur f p_body)

  inductive NonInstantReducible : Proc → Prop where
    | cycle : NonInstantReducible Proc.cycle
    | par_left (p₁ p₂ : Proc) :
      NonInstantReducible p₁ →
      NonInstantReducible (Proc.par p₁ p₂)
    | par_right (p₁ p₂ : Proc) :
      NonInstantReducible p₂ →
      NonInstantReducible (Proc.par p₁ p₂)
    | seq_left (p₁ p₂ : Proc) :
      NonInstantReducible p₁ →
      NonInstantReducible (Proc.seq p₁ p₂)
    | seq_right (p₁ p₂ : Proc) :
      NonInstantReducible p₂ →
      NonInstantReducible (Proc.seq p₁ p₂)
    | xoffer (p_else : Proc) (branches : List ChoiceBranch) :
      NonInstantReducible p_else →
      ∀ br ∈ branches, NonInstantReducible (ChoiceBranch.getProc br) →
      NonInstantReducible (Proc.xoffer p_else branches)
    | offer (p_else : Proc) (branches : List ChoiceBranch) :
      NonInstantReducible p_else →
      ∀ br ∈ branches, NonInstantReducible (ChoiceBranch.getProc br) →
      NonInstantReducible (Proc.offer p_else branches)
    | ifunfair (e : Expr) (p₁ p₂ : Proc) :
      NonInstantReducible p₁ →
      NonInstantReducible p₂ →
      NonInstantReducible (Proc.ifunfair e p₁ p₂)
    | iffair (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) :
      NonInstantReducible p₁ →
      NonInstantReducible p₂ →
      NonInstantReducible (Proc.iffair bid e p₁ p₂)
    | recur (f : String) (p_body : Proc) :
      NonInstantReducible p_body →
      NonInstantReducible (Proc.recur f p_body)

  inductive NonInstantMessage : Proc → MessageId → Prop where
    | recv (msg m : MessageId) (var : String) (p : Proc) :
      msg ≠ m →
      NonInstantMessage p m →
      NonInstantMessage (Proc.recv msg var p) m
    | send (msg m : MessageId) (e : Expr) :
      msg ≠ m →
      NonInstantMessage (Proc.send msg e) m
    | cycle (m : MessageId) :
      NonInstantMessage Proc.cycle m
    | skip (m : MessageId) :
      NonInstantMessage Proc.skip m
    | par (p₁ p₂ : Proc) (m : MessageId) :
      NonInstantMessage p₁ m →
      NonInstantMessage p₂ m →
      NonInstantMessage (Proc.par p₁ p₂) m
    | seq (p₁ p₂ : Proc) (m : MessageId) :
      NonInstantMessage p₁ m →
      NonInstantMessage p₂ m →
      NonInstantMessage (Proc.seq p₁ p₂) m
    | seq_noninst (p₁ p₂ : Proc) (m : MessageId) :
      NonInstantMessage p₁ m →
      NonInstantReducible p₁ →
      NonInstantMessage (Proc.seq p₁ p₂) m
    | xoffer (p_else : Proc) (branches : List ChoiceBranch) (m : MessageId) :
      NonInstantMessage p_else m →
      (∀ br ∈ branches, NonInstantMessage br.getProc m) →
      (∀ br ∈ branches, br.getMessageId ≠ m) →
      NonInstantMessage (Proc.xoffer p_else branches) m
    | offer (p_else : Proc) (branches : List ChoiceBranch) (m : MessageId) :
      NonInstantMessage p_else m →
      (∀ br ∈ branches, NonInstantMessage br.getProc m) →
      (∀ br ∈ branches, br.getMessageId ≠ m) →
      NonInstantMessage (Proc.offer p_else branches) m
    | ifunfair (e : Expr) (p₁ p₂ : Proc) (m : MessageId) :
      NonInstantMessage p₁ m →
      NonInstantMessage p₂ m →
      NonInstantMessage (Proc.ifunfair e p₁ p₂) m
    | iffair (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (m : MessageId) :
      NonInstantMessage p₁ m →
      NonInstantMessage p₂ m →
      NonInstantMessage (Proc.iffair bid e p₁ p₂) m
    | recur (f : String) (p_body : Proc) (m : MessageId) :
      NonInstantMessage p_body m →
      NonInstantMessage (Proc.recur f p_body) m


  -- TODO: we probably don't need these now
  def instantReducible (p : Proc) : Bool :=
    match p with
    | .skip => true
    | .cycle => false
    | .par p₁ p₂ => instantReducible p₁ && instantReducible p₂
    | .seq p₁ p₂ => instantReducible p₁ && instantReducible p₂
    | .send _ _ => true
    | .recv _ _ p' => instantReducible p'
    | .ifunfair _ p₁ p₂
    | .iffair _ _ p₁ p₂ => instantReducible p₁ || instantReducible p₂
    | .xoffer p_else branches
    | .offer p_else branches => instantReducible p_else
      || branches.any (fun br => instantReducible (ChoiceBranch.getProc br))
    | .var _ => true
    | .endp _ => true
    | .recur _ p_body => instantReducible p_body
  termination_by 0
  decreasing_by
    all_goals sorry -- FIXME: prove that this is terminating

  def awaitSet (p : Proc) : Finset MessageId :=
    match p with
    | .cycle | .skip | .endp _ => ∅
    | .recv msg _ p' => {msg} ∪ awaitSet p'
    | .send msg _ => {msg}
    | .par p₁ p₂ => awaitSet p₁ ∪ awaitSet p₂
    | .seq p₁ p₂ =>
      if instantReducible p₁ then awaitSet p₁ ∪ awaitSet p₂ else awaitSet p₁
    | .xoffer p_else branches
    | .offer p_else branches =>
      awaitSet p_else ∪
      branches.foldl (fun acc br => acc ∪ {ChoiceBranch.getMessageId br} ∪ awaitSet (ChoiceBranch.getProc br)) ∅
    | .var _ => ∅ -- FIXME: not correct
    | .ifunfair _ p₁ p₂
    | .iffair _ _ p₁ p₂ => awaitSet p₁ ∪ awaitSet p₂
    | .recur _ p_body => awaitSet p_body
  termination_by 0
  decreasing_by
    all_goals sorry -- FIXME: prove that this is terminating


  abbrev ProcComp := Multiset Proc
  inductive CompReduces : ProcComp → TransLabel → ProcComp → Prop where
    | nonsync_step (ex_msg : Finset MessageId) (p : Proc) (p' : Proc) (α : TransLabel) (rest : ProcComp) :
      (∀ po ∈ rest, ∀ m ∈ ex_msg, NonInstantMessage po m) →
      Reduces ex_msg p α p' → ¬α.isAsync →
      CompReduces (Multiset.cons p rest) α (Multiset.cons p' rest)
    | msg_step (ex_msg₁ ex_msg₂ : Finset MessageId) (p₁ p₁' p₂ p₂' : Proc) (msg : MessageId) (b : Bool) (rest : ProcComp) :
      Reduces ex_msg₁ p₁ (TransLabel.message msg b) p₁' →
      Reduces ex_msg₂ p₂ (TransLabel.message msg b) p₂' →
      CompReduces (Multiset.cons p₁ (Multiset.cons p₂ rest)) (TransLabel.message msg b)
        (Multiset.cons p₁' (Multiset.cons p₂' rest))
    | tock_step (c c' : ProcComp) :
      Multiset.Rel (fun p₁ p₂ => Reduces ∅ p₁ TransLabel.tock p₂) c c' →
      CompReduces c TransLabel.tock c'
end Semantics
