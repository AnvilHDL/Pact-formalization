import Anvilpp.Alphabet

open Pact

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


/-! ## Process syntax

Signed processes `P = (Ω,R)`: every node carries its written alphabet, in the
same per-constructor encoding used by `PactType`. -/


mutual
  /-- A branch in `offer` or `xoffer`. -/
  inductive ChoiceBranch : Type where
    | send : MessageId → Expr → Proc → ChoiceBranch
    | recv : MessageId → String → Proc → ChoiceBranch

  inductive Proc : Type where
    | send : PactTypeAlphabet → MessageId → Expr → Proc → Proc
    | recv : PactTypeAlphabet → MessageId → String → Proc → Proc
    | var : PactTypeAlphabet → String → Proc
    | skip : PactTypeAlphabet → Proc
    | endp : PactTypeAlphabet → ProcId → Proc
    | cycle : PactTypeAlphabet → Proc
    | par : PactTypeAlphabet → Proc → Proc → Interface → Proc
    | seq : PactTypeAlphabet → Proc → Proc → Proc
    | letp : PactTypeAlphabet → String → Expr → Proc → Proc
    | ifunfair : PactTypeAlphabet → Expr → Proc → Proc → Proc
    | iffair : PactTypeAlphabet → BranchId → Expr → Proc → Proc → Proc
    | xoffer : PactTypeAlphabet → Proc → List ChoiceBranch → Proc
    | offer : PactTypeAlphabet → Proc → List ChoiceBranch → Proc
    /-- Recursion -/
    | recur : PactTypeAlphabet → String → Proc → Proc
end

/-- Recursive branch lists prevent the stock deriving handler from closing. -/
noncomputable instance instDecidableEqProc : DecidableEq Proc :=
  Classical.decEq Proc

noncomputable instance instDecidableEqChoiceBranch : DecidableEq ChoiceBranch :=
  Classical.decEq ChoiceBranch

namespace Proc

  /-- `Ω(P)`, the written alphabet of a signed process. -/
  def alphabet : Proc → PactTypeAlphabet
    | .send alphabet _ _ _ => alphabet
    | .recv alphabet _ _ _ => alphabet
    | .var alphabet _ => alphabet
    | .skip alphabet => alphabet
    | .endp alphabet _ => alphabet
    | .cycle alphabet => alphabet
    | .par alphabet _ _ _ => alphabet
    | .seq alphabet _ _ => alphabet
    | .letp alphabet _ _ _ => alphabet
    | .ifunfair alphabet _ _ _ => alphabet
    | .iffair alphabet _ _ _ _ => alphabet
    | .xoffer alphabet _ _ => alphabet
    | .offer alphabet _ _ => alphabet
    | .recur alphabet _ _ => alphabet

end Proc

namespace ChoiceBranch
  def getMessageId : ChoiceBranch → MessageId
    | send msg _ _ => msg
    | recv msg _ _ => msg

  def getDir : ChoiceBranch → MessageDir
    | send _ _ _ => MessageDir.send
    | recv _ _ _ => MessageDir.recv

  def continuation : ChoiceBranch → Proc
    | send _ _ p => p
    | recv _ _ p => p

  theorem continuation_sizeOf_lt (branch : ChoiceBranch) :
      sizeOf (continuation branch) < sizeOf branch := by
    cases branch <;> simp [continuation] <;> omega

  /-- `Msg(a)`: the branch head as a polarized action. -/
  def action (branch : ChoiceBranch) : BareMessage :=
    (branch.getMessageId, branch.getDir)

  /-- `Need(a)`: the complementary action that enables this branch. -/
  def need (branch : ChoiceBranch) : BareMessage := bareNeed branch.action

  /-- The singleton exclusive offer a non-selected branch becomes on
  conjunctive commitment. -/
  def toXOffer (alphabet : PactTypeAlphabet) (br : ChoiceBranch) : Proc :=
    Proc.xoffer alphabet (Proc.skip alphabet) [br]

end ChoiceBranch


/-! ## Re-signing

`P[Ω']` from the paper.  A parallel node applies `Π_I` to each child, so a
child retains its interface actions and receives the complete incoming
alphabet. -/

mutual
  def Proc.reannotate (alphabet : PactTypeAlphabet) : Proc → Proc
    | .send _ msg expr p => .send alphabet msg expr (Proc.reannotate alphabet p)
    | .recv _ msg varName p => .recv alphabet msg varName (Proc.reannotate alphabet p)
    | .var _ name => .var alphabet name
    | .skip _ => .skip alphabet
    | .endp _ pid => .endp alphabet pid
    | .cycle _ => .cycle alphabet
    | .par _ left right interface =>
        let leftAlphabet :=
          PactTypeAlphabet.projectParallel alphabet left.alphabet interface
        let rightAlphabet :=
          PactTypeAlphabet.projectParallel alphabet right.alphabet interface
        .par alphabet (Proc.reannotate leftAlphabet left)
          (Proc.reannotate rightAlphabet right) interface
    | .seq _ left right =>
        .seq alphabet (Proc.reannotate alphabet left)
          (Proc.reannotate alphabet right)
    | .letp _ varName expr p =>
        .letp alphabet varName expr (Proc.reannotate alphabet p)
    | .ifunfair _ expr left right =>
        .ifunfair alphabet expr (Proc.reannotate alphabet left)
          (Proc.reannotate alphabet right)
    | .iffair _ bid expr left right =>
        .iffair alphabet bid expr (Proc.reannotate alphabet left)
          (Proc.reannotate alphabet right)
    | .xoffer _ elseProcess branches =>
        .xoffer alphabet (Proc.reannotate alphabet elseProcess)
          (Proc.reannotateBranches alphabet branches)
    | .offer _ elseProcess branches =>
        .offer alphabet (Proc.reannotate alphabet elseProcess)
          (Proc.reannotateBranches alphabet branches)
    | .recur _ name body =>
        .recur alphabet name (Proc.reannotate alphabet body)
  termination_by process => sizeOf process

  def Proc.reannotateBranches (alphabet : PactTypeAlphabet) :
      List ChoiceBranch → List ChoiceBranch
    | [] => []
    | ChoiceBranch.send msg expr p :: rest =>
        ChoiceBranch.send msg expr (Proc.reannotate alphabet p) ::
          Proc.reannotateBranches alphabet rest
    | ChoiceBranch.recv msg varName p :: rest =>
        ChoiceBranch.recv msg varName (Proc.reannotate alphabet p) ::
          Proc.reannotateBranches alphabet rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals (simp_wf; omega)
end

@[simp] theorem Proc.alphabet_reannotate (alphabet : PactTypeAlphabet)
    (process : Proc) : (Proc.reannotate alphabet process).alphabet = alphabet := by
  cases process <;> simp [Proc.reannotate, Proc.alphabet]


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
    and are always traversed.  Written alphabets are never changed. -/
    def procExprReplace (p : Proc) (x : String) (v : Bool) : Proc :=
      match p with
      | Proc.send alphabet msg e p' =>
          Proc.send alphabet msg (exprReplace e x v) (procExprReplace p' x v)
      | Proc.recv alphabet msg var p' =>
          Proc.recv alphabet msg var (if x = var then p' else procExprReplace p' x v)
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

/-! ## Alphabet well-formedness for signed processes

`AlphaWF_P(P)`: `MsgWF` at every node, the constructor-specific alphabet
clause, and `ParCompat_I` at a parallel node. -/

mutual
  def Proc.AlphabetWellFormed : Proc → Prop
    | .send alphabet _ _ p =>
        alphabet.WellFormed ∧ p.alphabet = alphabet ∧
          Proc.AlphabetWellFormed p
    | .recv alphabet _ _ p =>
        alphabet.WellFormed ∧ p.alphabet = alphabet ∧
          Proc.AlphabetWellFormed p
    | .var alphabet _ | .skip alphabet | .cycle alphabet =>
        alphabet.WellFormed
    | .endp alphabet _ => alphabet.WellFormed
    | .letp alphabet _ _ p =>
        alphabet.WellFormed ∧ p.alphabet = alphabet ∧
          Proc.AlphabetWellFormed p
    | .seq alphabet left right =>
        alphabet.WellFormed ∧
          left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
          Proc.AlphabetWellFormed left ∧ Proc.AlphabetWellFormed right
    | .ifunfair alphabet _ left right =>
        alphabet.WellFormed ∧
          left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
          Proc.AlphabetWellFormed left ∧ Proc.AlphabetWellFormed right
    | .iffair alphabet _ _ left right =>
        alphabet.WellFormed ∧
          left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
          Proc.AlphabetWellFormed left ∧ Proc.AlphabetWellFormed right
    | .recur alphabet _ body =>
        alphabet.WellFormed ∧ body.alphabet = alphabet ∧
          Proc.AlphabetWellFormed body
    | .par alphabet left right interface =>
        alphabet.WellFormed ∧
          PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
            right.alphabet interface ∧
          Proc.AlphabetWellFormed left ∧ Proc.AlphabetWellFormed right
    | .xoffer alphabet elseProcess branches =>
        alphabet.WellFormed ∧ elseProcess.alphabet = alphabet ∧
          Proc.AlphabetWellFormed elseProcess ∧
          Proc.BranchesAlphabetWellFormed alphabet branches
    | .offer alphabet elseProcess branches =>
        alphabet.WellFormed ∧ elseProcess.alphabet = alphabet ∧
          Proc.AlphabetWellFormed elseProcess ∧
          Proc.BranchesAlphabetWellFormed alphabet branches
  termination_by process => sizeOf process

  /-- `conjunctCompatible(Ω,B)` and the exclusive-offer clause coincide: every
  branch carries the surrounding alphabet. -/
  def Proc.BranchesAlphabetWellFormed
      (alphabet : PactTypeAlphabet) : List ChoiceBranch → Prop
    | [] => True
    | branch :: rest =>
        (ChoiceBranch.continuation branch).alphabet = alphabet ∧
          Proc.AlphabetWellFormed (ChoiceBranch.continuation branch) ∧
          Proc.BranchesAlphabetWellFormed alphabet rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    first
    | (simp_wf; omega)
    | (have hBranch := ChoiceBranch.continuation_sizeOf_lt branch
       simp_wf
       omega)
end

/-! ## Variable binding -/

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
    | ChoiceBranch.send _ expr p :: rest =>
        Expr.AllVariablesBound dataVars expr ∧
          Proc.AllVariablesBound procVars dataVars p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
    | ChoiceBranch.recv _ varName p :: rest =>
        Proc.AllVariablesBound procVars (varName :: dataVars) p ∧
          Proc.AllBranchVariablesBound procVars dataVars rest
end

/-- `DataWF(P)`: every process- and data-variable in `P` is bound. -/
def DataWFProc (process : Proc) : Prop := Proc.AllVariablesBound [] [] process
