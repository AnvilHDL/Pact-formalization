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
  | complete : MessageDir
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
    | complete => complete
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
  | ε : TransLabel
  | tock : TransLabel
  | message : MessageId → MessageDir → Bool → TransLabel
  | branchTrue : BranchId → TransLabel
  | branchFalse : BranchId → TransLabel
  | dollar : ProcId → TransLabel

namespace TransLabel
  def isComplete (α : TransLabel) : Bool :=
    match α with
    | TransLabel.message _ dir _ => dir = MessageDir.complete
    | _ => true
end TransLabel

/-- Abstract versions of transition labels for automata. -/
inductive AbstractTransLabel : Type where
  | ε : AbstractTransLabel
  | tock : AbstractTransLabel
  | message : MessageId → MessageDir → AbstractTransLabel
  | branchTrue : BranchId → AbstractTransLabel
  | branchFalse : BranchId → AbstractTransLabel
  | dollar : ProcId → AbstractTransLabel

namespace AbstractTransLabel
  def fromConcrete : TransLabel → AbstractTransLabel
    | TransLabel.ε => AbstractTransLabel.ε
    | TransLabel.tock => AbstractTransLabel.tock
    | TransLabel.message msg dir _ => AbstractTransLabel.message msg dir
    | TransLabel.branchTrue bid => AbstractTransLabel.branchTrue bid
    | TransLabel.branchFalse bid => AbstractTransLabel.branchFalse bid
    | TransLabel.dollar pid => AbstractTransLabel.dollar pid

  def isComplete (α : AbstractTransLabel) : Bool :=
    match α with
    | AbstractTransLabel.message _ dir => dir = MessageDir.complete
    | _ => true

  lemma fromConcrete_isComplete (α : TransLabel) :
      AbstractTransLabel.isComplete (fromConcrete α) = TransLabel.isComplete α := by
    cases α
    case ε => rfl
    case tock => rfl
    case message msg dir b => rfl
    case branchTrue bid => rfl
    case branchFalse bid => rfl
    case dollar pid => rfl

  lemma fromConcrete_nontock (α : TransLabel) :
      α ≠ TransLabel.tock ↔ fromConcrete α ≠ AbstractTransLabel.tock := by
    constructor
    . intro H_neq
      cases α
      case tock => contradiction
      all_goals { intro H_eq; contradiction }
    . intro H_neq
      cases α
      case tock => contradiction
      all_goals { intro H_eq; contradiction }

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
    | recv (msg : MessageId) (var : String) (p : Proc) :
      NonInstantReducible p →
      NonInstantReducible (Proc.recv msg var p)

  inductive NonInstantMessage : Proc → (MessageId × MessageDir) → Prop where
    | recv (msg m : MessageId) (var : String) (p : Proc) :
      msg ≠ m →
      NonInstantMessage p (m, MessageDir.recv) →
      NonInstantMessage (Proc.recv msg var p) (m, MessageDir.recv)
    | recv_opposite (msg m : MessageId) (var : String) (p : Proc) :
      NonInstantMessage p (m, MessageDir.send) →
      NonInstantMessage (Proc.recv msg var p) (m, MessageDir.send)
    | send (msg m : MessageId) (e : Expr) :
      msg ≠ m →
      NonInstantMessage (Proc.send msg e) (m, MessageDir.send)
    | send_opposite (msg m : MessageId) (e : Expr) :
      NonInstantMessage (Proc.send msg e) (m, MessageDir.recv)
    | cycle (m : MessageId) (d : MessageDir) :
      NonInstantMessage Proc.cycle (m, d)
    | skip (m : MessageId) (d : MessageDir) :
      NonInstantMessage Proc.skip (m, d)
    | par (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p₁ mx →
      NonInstantMessage p₂ mx →
      NonInstantMessage (Proc.par p₁ p₂) mx
    | seq (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p₁ mx →
      NonInstantMessage p₂ mx →
      NonInstantMessage (Proc.seq p₁ p₂) mx
    | seq_noninst (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p₁ mx →
      NonInstantReducible p₁ →
      NonInstantMessage (Proc.seq p₁ p₂) mx
    | xoffer (p_else : Proc) (branches : List ChoiceBranch) (mx : MessageId × MessageDir) :
      NonInstantMessage p_else mx →
      (∀ br ∈ branches, NonInstantMessage br.getProc mx) →
      (∀ br ∈ branches, br.getMessage ≠ mx) →
      NonInstantMessage (Proc.xoffer p_else branches) mx
    | offer (p_else : Proc) (branches : List ChoiceBranch) (mx : MessageId × MessageDir) :
      NonInstantMessage p_else mx →
      (∀ br ∈ branches, NonInstantMessage br.getProc mx) →
      (∀ br ∈ branches, br.getMessage ≠ mx) →
      NonInstantMessage (Proc.offer p_else branches) mx
    | ifunfair (e : Expr) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p₁ mx →
      NonInstantMessage p₂ mx →
      NonInstantMessage (Proc.ifunfair e p₁ p₂) mx
    | iffair (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p₁ mx →
      NonInstantMessage p₂ mx →
      NonInstantMessage (Proc.iffair bid e p₁ p₂) mx
    | recur (f : String) (p_body : Proc) (mx : MessageId × MessageDir) :
      NonInstantMessage p_body mx →
      NonInstantMessage (Proc.recur f p_body) mx



  inductive Reduces : Finset (MessageId × MessageDir) → Proc → TransLabel → Proc → Prop where
    | tock ex_msg :
      Reduces ex_msg Proc.cycle TransLabel.tock Proc.skip
    | send ex_msg (msg : MessageId) (e : Expr) (b : Bool) :
      e ↓ b →
      Reduces ex_msg (Proc.send msg e) (TransLabel.message msg MessageDir.send b) Proc.skip
    | recv ex_msg (msg : MessageId) (var : String) (p : Proc) (b : Bool) :
      Reduces ex_msg (Proc.recv msg var p) (TransLabel.message msg MessageDir.recv b)
        $ Proc.seq Proc.skip (procExprReplace p var b)
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
    | par_left ex_msg ex_msg' (p₁ p₁' p₂ : Proc) (α : TransLabel) :
      α ≠ TransLabel.tock →
      ex_msg' ⊆ ex_msg →
      (∀ mx ∈ ex_msg', NonInstantMessage p₂ mx) →
      Reduces ex_msg' p₁ α p₁' →
      Reduces ex_msg (Proc.par p₁ p₂) α (Proc.par p₁' p₂)
    | par_right ex_msg ex_msg' (p₁ p₂ p₂' : Proc) (α : TransLabel) :
      α ≠ TransLabel.tock →
      ex_msg' ⊆ ex_msg →
      (∀ mx ∈ ex_msg', NonInstantMessage p₁ mx) →
      Reduces ex_msg' p₂ α p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) α (Proc.par p₁ p₂')
    | par_tock ex_msg (p₁ p₂ p₁' p₂' : Proc) :
      Reduces ex_msg p₁ TransLabel.tock p₁' →
      Reduces ex_msg p₂ TransLabel.tock p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) TransLabel.tock (Proc.par p₁' p₂')
    | par_skip_right ex_msg (p₁ : Proc) :
      Reduces ex_msg (Proc.par p₁ Proc.skip) TransLabel.ε p₁
    | par_skip_left ex_msg (p₂ : Proc) :
      Reduces ex_msg (Proc.par Proc.skip p₂) TransLabel.ε p₂
    | par_message ex_msg ex_msg₁ ex_msg₂ (msg : MessageId) (dir dir' : MessageDir) (b : Bool)
                      (p₁ p₁' p₂ p₂' : Proc) :
      MessageDir.dual dir dir' →
      ex_msg₁ ⊆ ex_msg →
      ex_msg₂ ⊆ ex_msg →
      (∀ mx ∈ ex_msg₂, NonInstantMessage p₁ mx) →
      (∀ mx ∈ ex_msg₁, NonInstantMessage p₂ mx) →
      Reduces ex_msg₁ p₁ (TransLabel.message msg dir b) p₁' →
      Reduces ex_msg₂ p₂ (TransLabel.message msg dir' b) p₂' →
      Reduces ex_msg (Proc.par p₁ p₂) (TransLabel.message msg MessageDir.complete b) (Proc.par p₁' p₂')
    | xoffer_branch_recv ex_msg (var : String) (p_else : Proc) (branches : List ChoiceBranch)
                         (msg : MessageId) (p' : Proc) (b : Bool) :
      ChoiceBranch.recv msg var p' ∈ branches →
      Reduces ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg MessageDir.recv b) (procExprReplace p' var b)
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

  -- namespace Reduces
  --   #check rec -- the default induction principle is not strong enough

  --   set_option autoImplicit false

    -- TODO: check if this is actually needed
    /-- Custom induction principle. -/
    -- lemma ind {P : (ex_msg : Finset (MessageId × MessageDir)) → (p : Proc) → (α : TransLabel) → (p' : Proc) → Reduces ex_msg p α p' → Prop}
    --   (tock : ∀ ex_msg,
    --     P ex_msg Proc.cycle TransLabel.tock Proc.skip (Reduces.tock ex_msg))
    --   (send : ∀ ex_msg (msg : MessageId) (e : Expr) (b : Bool),
    --     (H_eval : e ↓ b) →
    --     P ex_msg (Proc.send msg e) (TransLabel.message msg MessageDir.send b) Proc.skip
    --       (Reduces.send ex_msg msg e b H_eval))
    --   (recv : ∀ ex_msg (msg : MessageId) (var : String) (p : Proc) (b : Bool),
    --     P ex_msg (Proc.recv msg var p) (TransLabel.message msg MessageDir.recv b)
    --       (Proc.seq Proc.skip (procExprReplace p var b))
    --       (Reduces.recv ex_msg msg var p b))
    --   (seq_step : ∀ ex_msg (p₁ p₁' p₂ : Proc) (α : TransLabel)
    --                     (H_red : Reduces ex_msg p₁ α p₁'),
    --     (H_ind : P ex_msg p₁ α p₁' H_red) →
    --     P ex_msg (Proc.seq p₁ p₂) α (Proc.seq p₁' p₂)
    --       (Reduces.seq_step ex_msg p₁ p₁' p₂ α H_red))
    --   (seq_skip : ∀ ex_msg (p₂ : Proc),
    --     P ex_msg (Proc.seq Proc.skip p₂) TransLabel.ε p₂
    --       (Reduces.seq_skip ex_msg p₂))
    --   (ifunfair_true : ∀ ex_msg (e : Expr) (p₁ p₂ : Proc) (b : Bool)
    --                            (H_eval : e ↓ b) (H_bool : b = true),
    --     P ex_msg (Proc.ifunfair e p₁ p₂) TransLabel.ε p₁
    --       (Reduces.ifunfair_true ex_msg e p₁ p₂ b H_eval H_bool))
    --   (ifunfair_false : ∀ ex_msg (e : Expr) (p₁ p₂ : Proc) (b : Bool)
    --                             (H_eval : e ↓ b) (H_bool : b = false),
    --     P ex_msg (Proc.ifunfair e p₁ p₂) TransLabel.ε p₂
    --       (Reduces.ifunfair_false ex_msg e p₁ p₂ b H_eval H_bool))
    --   (iffair_true : ∀ ex_msg (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (b : Bool)
    --                           (H_eval : e ↓ b) (H_bool : b = true),
    --     P ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.branchTrue bid) p₁
    --       (Reduces.iffair_true ex_msg bid e p₁ p₂ b H_eval H_bool))
    --   (iffair_false : ∀ ex_msg (bid : BranchId) (e : Expr) (p₁ p₂ : Proc) (b : Bool)
    --                            (H_eval : e ↓ b) (H_bool : b = false),
    --     P ex_msg (Proc.iffair bid e p₁ p₂) (TransLabel.branchFalse bid) p₂
    --       (Reduces.iffair_false ex_msg bid e p₁ p₂ b H_eval H_bool))
    --   (par_left : ∀ ex_msg ex_msg' (p₁ p₁' p₂ : Proc) (α : TransLabel)
    --                      (H_neq : α ≠ TransLabel.tock)
    --                      (H_subset : ex_msg' ⊆ ex_msg)
    --                      (H_noninst : ∀ mx ∈ ex_msg', NonInstantMessage p₂ mx)
    --                      (H_red : Reduces ex_msg' p₁ α p₁'),
    --     (H_ind : P ex_msg' p₁ α p₁' H_red) →
    --     P ex_msg (Proc.par p₁ p₂) α (Proc.par p₁' p₂)
    --       (Reduces.par_left ex_msg ex_msg' p₁ p₁' p₂ α H_neq H_subset H_noninst H_red))
    --   (par_right : ∀ ex_msg ex_msg' (p₁ p₂ p₂' : Proc) (α : TransLabel)
    --                       (H_neq : α ≠ TransLabel.tock)
    --                       (H_subset : ex_msg' ⊆ ex_msg)
    --                       (H_noninst : ∀ mx ∈ ex_msg', NonInstantMessage p₁ mx)
    --                       (H_red : Reduces ex_msg' p₂ α p₂'),
    --     (H_ind : P ex_msg' p₂ α p₂' H_red) →
    --     P ex_msg (Proc.par p₁ p₂) α (Proc.par p₁ p₂')
    --       (Reduces.par_right ex_msg ex_msg' p₁ p₂ p₂' α H_neq H_subset H_noninst H_red))
    --   (par_tock : ∀ ex_msg (p₁ p₂ p₁' p₂' : Proc)
    --                      (H_red₁ : Reduces ex_msg p₁ TransLabel.tock p₁')
    --                      (H_red₂ : Reduces ex_msg p₂ TransLabel.tock p₂'),
    --     (H_ind₁ : P ex_msg p₁ TransLabel.tock p₁' H_red₁) →
    --     (H_ind₂ : P ex_msg p₂ TransLabel.tock p₂' H_red₂) →
    --     P ex_msg (Proc.par p₁ p₂) TransLabel.tock (Proc.par p₁' p₂')
    --       (Reduces.par_tock ex_msg p₁ p₂ p₁' p₂' H_red₁ H_red₂))
    --   (par_skip_right : ∀ ex_msg (p₁ : Proc),
    --     P ex_msg (Proc.par p₁ Proc.skip) TransLabel.ε p₁
    --       (Reduces.par_skip_right ex_msg p₁))
    --   (par_skip_left : ∀ ex_msg (p₂ : Proc),
    --     P ex_msg (Proc.par Proc.skip p₂) TransLabel.ε p₂
    --       (Reduces.par_skip_left ex_msg p₂))
    --   (par_message : ∀ ex_msg ex_msg₁ ex_msg₂ (msg : MessageId) (dir dir' : MessageDir) (b : Bool)
    --                        (p₁ p₁' p₂ p₂' : Proc)
    --                        (H_dual : MessageDir.dual dir dir')
    --                        (H_subset₁ : ex_msg₁ ⊆ ex_msg)
    --                        (H_subset₂ : ex_msg₂ ⊆ ex_msg)
    --                        (H_noninst₁ : ∀ mx ∈ ex_msg₂, NonInstantMessage p₁ mx)
    --                        (H_noninst₂ : ∀ mx ∈ ex_msg₁, NonInstantMessage p₂ mx)
    --                        (H_red₁ : Reduces ex_msg₁ p₁ (TransLabel.message msg dir b) p₁')
    --                        (H_red₂ : Reduces ex_msg₂ p₂ (TransLabel.message msg dir' b) p₂'),
    --     (H_ind₁ : P ex_msg₁ p₁ (TransLabel.message msg dir b) p₁' H_red₁) →
    --     (H_ind₂ : P ex_msg₂ p₂ (TransLabel.message msg dir' b) p₂' H_red₂) →
    --     P ex_msg (Proc.par p₁ p₂) (TransLabel.message msg MessageDir.complete b) (Proc.par p₁' p₂')
    --       (Reduces.par_message ex_msg ex_msg₁ ex_msg₂ msg dir dir' b p₁ p₁' p₂ p₂' H_dual H_subset₁ H_subset₂ H_noninst₁ H_noninst₂ H_red₁ H_red₂))
    --   (xoffer_branch_recv : ∀ ex_msg (var : String) (p_else : Proc) (branches : List ChoiceBranch)
    --                                (msg : MessageId) (p' : Proc) (b : Bool)
    --                                (H_in : ChoiceBranch.recv msg var p' ∈ branches),
    --     P ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg MessageDir.recv b) (procExprReplace p' var b)
    --       (Reduces.xoffer_branch_recv ex_msg var p_else branches msg p' b H_in))
    --   (xoffer_branch_send : ∀ ex_msg (msg : MessageId) (e : Expr) (p_else p' : Proc)
    --                                (branches : List ChoiceBranch) (b : Bool)
    --                                (H_in : ChoiceBranch.send msg e p' ∈ branches)
    --                                (H_eval : e ↓ b),
    --     P ex_msg (Proc.xoffer p_else branches) (TransLabel.message msg MessageDir.send b) p'
    --       (Reduces.xoffer_branch_send ex_msg msg e p_else p' branches b H_in H_eval))
    --   (xoffer_branch_else : ∀ ex_msg (p_else : Proc) (branches : List ChoiceBranch)
    --                                (H_cond : ∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg),
    --     P ex_msg (Proc.xoffer p_else branches) TransLabel.ε p_else
    --       (Reduces.xoffer_branch_else ex_msg p_else branches H_cond))
    --   (offer_branch_recv : ∀ ex_msg (var : String) (p_branch p_else : Proc) (branches : List ChoiceBranch)
    --                                (msg : MessageId) (b : Bool)
    --                                (lbranches rbranches : List ChoiceBranch)
    --                                (branches' : List Proc)
    --                                (p' : Proc)
    --                                (H_eq₁ : branches = lbranches ++ (ChoiceBranch.recv msg var p_branch) :: rbranches)
    --                                (H_eq₂ : branches' = lbranches.map ChoiceBranch.toXOffer ++ (procExprReplace p_branch var b) :: rbranches.map ChoiceBranch.toXOffer)
    --                                (H_eq₃ : p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip branches'),
    --     P ex_msg (Proc.offer p_else branches) (TransLabel.message msg MessageDir.recv b) p'
    --       (Reduces.offer_branch_recv ex_msg var p_branch p_else branches msg b lbranches rbranches branches' p' H_eq₁ H_eq₂ H_eq₃))
    --   (offer_branch_send : ∀ ex_msg (msg : MessageId) (p_else p_branch : Proc)
    --                                (branches lbranches rbranches : List ChoiceBranch)
    --                                (branches' : List Proc)
    --                                (p' : Proc)
    --                                (e : Expr) (b : Bool)
    --                                (H_eval : e ↓ b)
    --                                (H_eq₁ : branches = lbranches ++ (ChoiceBranch.send msg e p') :: rbranches)
    --                                (H_eq₂ : branches' = lbranches.map ChoiceBranch.toXOffer ++ p_branch :: rbranches.map ChoiceBranch.toXOffer)
    --                                (H_eq₃ : p' = List.foldl (fun acc br => Proc.par acc br) Proc.skip branches'),
    --     P ex_msg (Proc.offer p_else branches) (TransLabel.message msg MessageDir.send b) p'
    --       (Reduces.offer_branch_send ex_msg msg p_else p_branch branches lbranches rbranches branches' p' e b H_eval H_eq₁ H_eq₂ H_eq₃))
    --   (offer_branch_else : ∀ ex_msg (p_else : Proc) (branches : List ChoiceBranch)
    --                                (H_cond : ∀ mx ∈ branches.map ChoiceBranch.getMessage, (mx.1, mx.2.invert) ∈ ex_msg),
    --     P ex_msg (Proc.offer p_else branches) TransLabel.ε p_else
    --       (Reduces.offer_branch_else ex_msg p_else branches H_cond))
    --   (recur_unfold : ∀ ex_msg (f : String) (p_body : Proc),
    --     P ex_msg (Proc.recur f p_body) TransLabel.ε (procReplace p_body f $ Proc.recur f p_body)
    --       (Reduces.recur_unfold ex_msg f p_body))

    --     : ∀ {ex_msg p α p'} (H_red : Reduces ex_msg p α p'), P ex_msg p α p' H_red := by sorry

  -- end Reduces

  abbrev ProcComp := Proc
  def CompReduces (c₁ : ProcComp) (α : TransLabel) (c₂ : ProcComp) : Prop :=
    ∃ ex_msg : Finset (MessageId × MessageDir), Reduces ex_msg c₁ α c₂ ∧ α.isComplete

end Semantics
