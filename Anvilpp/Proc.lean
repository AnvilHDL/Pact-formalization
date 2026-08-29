import Mathlib.Data.Finset.Image
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

/-- A finite synchronization interface, for `P ||_I P`. -/
abbrev Interface := Finset MessageId

/-- A message identifier paired with its polarity. -/
abbrev BareMessage := MessageId × MessageDir

/-- The fixed alphabet attached to one syntax node, shared by `Proc` and
`PactType`. -/
structure PactTypeAlphabet : Type where
  actions : Finset BareMessage
  progress : Finset ProcId
  fair : Finset BranchId
  deriving DecidableEq

instance : SizeOf PactTypeAlphabet := ⟨fun _ => 0⟩

namespace PactTypeAlphabet

  def messageIds (alphabet : PactTypeAlphabet) : Finset MessageId :=
    alphabet.actions.image Prod.fst

  def OnePolarity (alphabet : PactTypeAlphabet) : Prop :=
    ∀ msg, ¬ ((msg, MessageDir.send) ∈ alphabet.actions ∧
      (msg, MessageDir.recv) ∈ alphabet.actions)

  def WellFormed (alphabet : PactTypeAlphabet) : Prop :=
    alphabet.OnePolarity

  def empty : PactTypeAlphabet :=
    { actions := ∅
      progress := ∅
      fair := ∅ }

  def ofAction (action : BareMessage) : PactTypeAlphabet :=
    { actions := {action}
      progress := ∅
      fair := ∅ }

  def ofProgress (pid : ProcId) : PactTypeAlphabet :=
    { actions := ∅
      progress := {pid}
      fair := ∅ }

  def ofFair (bid : BranchId) : PactTypeAlphabet :=
    { actions := ∅
      progress := ∅
      fair := {bid} }

  def union (left right : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := left.actions ∪ right.actions
      progress := left.progress ∪ right.progress
      fair := left.fair ∪ right.fair }

  def hideInterface (alphabet : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions := alphabet.actions.filter fun action => action.1 ∉ interface
      progress := alphabet.progress
      fair := alphabet.fair }

  def mergeHidden (left right : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions :=
        (left.actions ∪ right.actions).filter fun action =>
          action.1 ∉ interface
      progress := left.progress ∪ right.progress
      fair := left.fair ∪ right.fair }

  @[simp] theorem mergeHidden_self_empty (alphabet : PactTypeAlphabet) :
      mergeHidden alphabet alphabet ∅ = alphabet := by
    cases alphabet
    simp [mergeHidden]

  def ComplementaryOn
      (left right : PactTypeAlphabet) (interface : Interface) : Prop :=
    ∀ msg ∈ interface,
      (((msg, MessageDir.send) ∈ left.actions ∧
          (msg, MessageDir.recv) ∈ right.actions) ∨
        ((msg, MessageDir.recv) ∈ left.actions ∧
          (msg, MessageDir.send) ∈ right.actions))

  /-- Outside the synchronizing interface, the two parallel children own
  disjoint message names.  This is stated on message ids, not polarized
  actions, because `(m, send)` and `(m, recv)` are different actions but still
  refer to the same boundary message name. -/
  def BoundaryMessageIdsDisjoint
      (left right : PactTypeAlphabet) (interface : Interface) : Prop :=
    Disjoint (left.messageIds \ interface) (right.messageIds \ interface)

  /-- Compatibility of the fixed alphabets at a parallel node.

  The parent alphabet is the union of the two child alphabets with the
  interface messages hidden.  The children may overlap only on the interface
  message ids, and on those ids they must use complementary polarities.  Away
  from the interface, boundary message ids are disjoint.  Concrete polarized
  actions, progress ids, and fair-choice ids are also disjoint. -/
  structure ParallelCompatible
      (parent left right : PactTypeAlphabet) (interface : Interface) : Prop where
    parent_eq : parent = mergeHidden left right interface
    shared_messageIds : left.messageIds ∩ right.messageIds = interface
    boundary_messageIds_disjoint :
      BoundaryMessageIdsDisjoint left right interface
    actions_disjoint : Disjoint left.actions right.actions
    complementary : ComplementaryOn left right interface
    progress_disjoint : Disjoint left.progress right.progress
    fair_disjoint : Disjoint left.fair right.fair

end PactTypeAlphabet

mutual
  /-- A branch in `offer` or `xoffer`. -/
  inductive ChoiceBranch : Type where
    | send : PactTypeAlphabet → MessageId → Expr → Proc → ChoiceBranch
    | recv : PactTypeAlphabet → MessageId → String → Proc → ChoiceBranch

  /-- The process grammar, annotated with the fixed alphabet chosen for each
  subterm, mirroring `PactType`. -/
  inductive Proc : Type where
    | send : PactTypeAlphabet → MessageId → Expr → Proc → Proc
    | recv : PactTypeAlphabet → MessageId → String → Proc → Proc
    | var : PactTypeAlphabet → String → Proc
    | skip : PactTypeAlphabet → Proc
    | endp : PactTypeAlphabet → ProcId → Proc
    | cycle : PactTypeAlphabet → Proc
    | par : PactTypeAlphabet → Proc → Proc → MsgIdSet → Proc
    | seq : PactTypeAlphabet → Proc → Proc → Proc
    | letp : PactTypeAlphabet → String → Expr → Proc → Proc
    | ifunfair : PactTypeAlphabet → Expr → Proc → Proc → Proc
    | iffair : PactTypeAlphabet → BranchId → Expr → Proc → Proc → Proc
    | xoffer : PactTypeAlphabet → Proc → List ChoiceBranch → Proc
    | offer : PactTypeAlphabet → Proc → List ChoiceBranch → Proc
    /-- Recursion -/
    | recur : PactTypeAlphabet → String → Proc → Proc
end

namespace ChoiceBranch
  def getMessageId : ChoiceBranch → MessageId
    | send _ msg _ _ => msg
    | recv _ msg _ _ => msg

  def getDir : ChoiceBranch → MessageDir
    | send .. => MessageDir.send
    | recv .. => MessageDir.recv

  def alphabet : ChoiceBranch → PactTypeAlphabet
    | send alphabet _ _ _ => alphabet
    | recv alphabet _ _ _ => alphabet

  /-- The branch's continuation process. -/
  def continuation : ChoiceBranch → Proc
    | send _ _ _ p => p
    | recv _ _ _ p => p

  /-- The branch's own polarized action. -/
  def action (branch : ChoiceBranch) : BareMessage :=
    (branch.getMessageId, branch.getDir)

  theorem continuation_sizeOf_lt (branch : ChoiceBranch) :
      sizeOf branch.continuation < sizeOf branch := by
    cases branch <;> simp [continuation] <;> omega

  def toXOffer (br : ChoiceBranch) :=
    Proc.xoffer br.alphabet (Proc.skip br.alphabet) [br]
end ChoiceBranch

namespace Proc
  def alphabet : Proc → PactTypeAlphabet
    | send alphabet .. => alphabet
    | recv alphabet .. => alphabet
    | var alphabet _ => alphabet
    | skip alphabet => alphabet
    | endp alphabet _ => alphabet
    | cycle alphabet => alphabet
    | par alphabet .. => alphabet
    | seq alphabet .. => alphabet
    | letp alphabet .. => alphabet
    | ifunfair alphabet .. => alphabet
    | iffair alphabet .. => alphabet
    | xoffer alphabet .. => alphabet
    | offer alphabet .. => alphabet
    | recur alphabet .. => alphabet

  mutual
    /-- The fixed alphabet discipline for process syntax, mirroring
    `PactType.AlphabetWellFormed`: every constructor's alphabet is
    well-formed, non-parallel children share the parent's alphabet, and a
    `par` node's children compose via `ParallelCompatible`. -/
    def AlphabetWellFormed : Proc → Prop
      | .send alphabet msg _ p =>
          alphabet.WellFormed ∧ (msg, MessageDir.send) ∈ alphabet.actions ∧
            p.alphabet = alphabet ∧ AlphabetWellFormed p
      | .recv alphabet msg _ p =>
          alphabet.WellFormed ∧ (msg, MessageDir.recv) ∈ alphabet.actions ∧
            p.alphabet = alphabet ∧ AlphabetWellFormed p
      | .var alphabet _ | .skip alphabet | .cycle alphabet =>
          alphabet.WellFormed
      | .endp alphabet pid =>
          alphabet.WellFormed ∧ pid ∈ alphabet.progress
      | .seq alphabet left right =>
          alphabet.WellFormed ∧
            left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .letp alphabet _ _ p =>
          alphabet.WellFormed ∧ p.alphabet = alphabet ∧ AlphabetWellFormed p
      | .ifunfair alphabet _ left right =>
          alphabet.WellFormed ∧
            left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .iffair alphabet bid _ left right =>
          alphabet.WellFormed ∧ bid ∈ alphabet.fair ∧
            left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .recur alphabet _ body =>
          alphabet.WellFormed ∧ body.alphabet = alphabet ∧
            AlphabetWellFormed body
      | .par alphabet left right interface =>
          alphabet.WellFormed ∧
            PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
              right.alphabet interface ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .xoffer alphabet elseProcess branches
      | .offer alphabet elseProcess branches =>
          alphabet.WellFormed ∧ elseProcess.alphabet = alphabet ∧
            AlphabetWellFormed elseProcess ∧
            BranchesAlphabetWellFormed alphabet branches
    termination_by process => sizeOf process

    def BranchesAlphabetWellFormed
        (alphabet : PactTypeAlphabet) : List ChoiceBranch → Prop
      | [] => True
      | ChoiceBranch.send branchAlphabet msg _ p :: rest =>
          branchAlphabet = alphabet ∧ (msg, MessageDir.send) ∈ alphabet.actions ∧
            p.alphabet = alphabet ∧ AlphabetWellFormed p ∧
            BranchesAlphabetWellFormed alphabet rest
      | ChoiceBranch.recv branchAlphabet msg _ p :: rest =>
          branchAlphabet = alphabet ∧ (msg, MessageDir.recv) ∈ alphabet.actions ∧
            p.alphabet = alphabet ∧ AlphabetWellFormed p ∧
            BranchesAlphabetWellFormed alphabet rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end
end Proc


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
      | ChoiceBranch.send alphabet msg e p =>
        ChoiceBranch.send alphabet msg (exprReplace e x v) (procExprReplace p x v)
      | ChoiceBranch.recv alphabet msg var p =>
        let p' := if x = var then p else procExprReplace p x v
        ChoiceBranch.recv alphabet msg var p'

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
      | Proc.send alphabet msg e p' =>
          Proc.send alphabet msg (exprReplace e x v) (procExprReplace p' x v)
      | Proc.recv alphabet msg var p' =>
          Proc.recv alphabet msg var
            (if x = var then p' else procExprReplace p' x v)
      | Proc.var alphabet name => Proc.var alphabet name
      | Proc.skip alphabet => Proc.skip alphabet
      | Proc.endp alphabet pid => Proc.endp alphabet pid
      | Proc.cycle alphabet => Proc.cycle alphabet
      | Proc.par alphabet left right interface =>
          Proc.par alphabet (procExprReplace left x v) (procExprReplace right x v)
            interface
      | Proc.seq alphabet left right =>
          Proc.seq alphabet (procExprReplace left x v) (procExprReplace right x v)
      | Proc.letp alphabet var e p' =>
          Proc.letp alphabet var (exprReplace e x v)
            (if x = var then p' else procExprReplace p' x v)
      | Proc.ifunfair alphabet e left right =>
          Proc.ifunfair alphabet (exprReplace e x v) (procExprReplace left x v)
            (procExprReplace right x v)
      | Proc.iffair alphabet bid e left right =>
          Proc.iffair alphabet bid (exprReplace e x v) (procExprReplace left x v)
            (procExprReplace right x v)
      | Proc.xoffer alphabet elseProcess branches =>
          Proc.xoffer alphabet (procExprReplace elseProcess x v)
            (choiceBranchesExprReplace branches x v)
      | Proc.offer alphabet elseProcess branches =>
          Proc.offer alphabet (procExprReplace elseProcess x v)
            (choiceBranchesExprReplace branches x v)
      | Proc.recur alphabet name body =>
          Proc.recur alphabet name (procExprReplace body x v)
  end

  mutual
    /-- Replace recursive process variable occurrences inside a choice branch. -/
    def choiceBranchProcReplace (br : ChoiceBranch) (f : String) (p_body : Proc) : ChoiceBranch :=
      match br with
      | ChoiceBranch.send alphabet msg e p =>
        ChoiceBranch.send alphabet msg e (procReplace p f p_body)
      | ChoiceBranch.recv alphabet msg var p =>
        ChoiceBranch.recv alphabet msg var (procReplace p f p_body)

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
      | Proc.send alphabet msg e p' =>
          Proc.send alphabet msg e (procReplace p' f p_body)
      | Proc.recv alphabet msg var p' =>
          Proc.recv alphabet msg var (procReplace p' f p_body)
      | Proc.var alphabet name => if f = name then p_body else Proc.var alphabet name
      | Proc.skip alphabet => Proc.skip alphabet
      | Proc.endp alphabet pid => Proc.endp alphabet pid
      | Proc.cycle alphabet => Proc.cycle alphabet
      | Proc.par alphabet left right interface =>
          Proc.par alphabet (procReplace left f p_body) (procReplace right f p_body)
            interface
      | Proc.seq alphabet left right =>
          Proc.seq alphabet (procReplace left f p_body) (procReplace right f p_body)
      | Proc.letp alphabet var e p' =>
          Proc.letp alphabet var e (procReplace p' f p_body)
      | Proc.ifunfair alphabet e left right =>
          Proc.ifunfair alphabet e (procReplace left f p_body) (procReplace right f p_body)
      | Proc.iffair alphabet bid e left right =>
          Proc.iffair alphabet bid e (procReplace left f p_body)
            (procReplace right f p_body)
      | Proc.xoffer alphabet elseProcess branches =>
          Proc.xoffer alphabet (procReplace elseProcess f p_body)
            (choiceBranchesProcReplace branches f p_body)
      | Proc.offer alphabet elseProcess branches =>
          Proc.offer alphabet (procReplace elseProcess f p_body)
            (choiceBranchesProcReplace branches f p_body)
      | Proc.recur alphabet name body =>
          if f = name then Proc.recur alphabet name body
          else Proc.recur alphabet name (procReplace body f p_body)
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
    | Proc.send _ _ expr p =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars p
    | Proc.recv _ _ varName p =>
        Proc.AllVariablesBound procVars (varName :: dataVars) p
    | Proc.var _ name => name ∈ procVars
    | Proc.skip _ => True
    | Proc.endp _ _ => True
    | Proc.cycle _ => True
    | Proc.par _ left right _ =>
        Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.seq _ left right =>
        Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.letp _ varName expr p =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars (varName :: dataVars) p
    | Proc.ifunfair _ expr left right =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.iffair _ _ expr left right =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars left ∧
          Proc.AllVariablesBound procVars dataVars right
    | Proc.xoffer _ elseProcess branches =>
        Proc.AllVariablesBound procVars dataVars elseProcess ∧
          Proc.AllBranchVariablesBound procVars dataVars branches
    | Proc.offer _ elseProcess branches =>
        Proc.AllVariablesBound procVars dataVars elseProcess ∧
          Proc.AllBranchVariablesBound procVars dataVars branches
    | Proc.recur _ name body =>
        Proc.AllVariablesBound (name :: procVars) dataVars body

  def Proc.AllBranchVariablesBound
      (procVars dataVars : List String) : List ChoiceBranch → Prop
    | [] => True
    | ChoiceBranch.send _ _ expr p :: rest =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
    | ChoiceBranch.recv _ _ varName p :: rest =>
        Proc.AllVariablesBound procVars (varName :: dataVars) p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
end

/-- `WFProc(P)`: every process- and data-variable in `P` is bound.  The
expression language is untyped booleans throughout, so "every expression is
well typed" (the other conjunct of the paper's `WFProc`) is vacuous. -/
def WFProc (process : Proc) : Prop := Proc.AllVariablesBound [] [] process
