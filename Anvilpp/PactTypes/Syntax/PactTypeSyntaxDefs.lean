import Mathlib.Data.Finset.Image
import Anvilpp.PactSemantics

namespace Pact

noncomputable section

/-- The fixed alphabet attached to one type node.

`actions` stores the polarized message actions owned by this type.  The
unpolarized message names are derived from `actions`.
-/
structure PactTypeAlphabet : Type where
  actions : Finset BareMessage
  deriving DecidableEq

instance : SizeOf PactTypeAlphabet := ⟨fun _ => 0⟩

namespace PactTypeAlphabet

  def OnePolarity (alphabet : PactTypeAlphabet) : Prop :=
    ∀ msg, ¬ ((msg, MessageDir.send) ∈ alphabet.actions ∧
      (msg, MessageDir.recv) ∈ alphabet.actions)

  def WellFormed (alphabet : PactTypeAlphabet) : Prop :=
    alphabet.OnePolarity

  def empty : PactTypeAlphabet :=
    { actions := ∅ }

  def ofAction (action : BareMessage) : PactTypeAlphabet :=
    { actions := {action} }

  def union (left right : PactTypeAlphabet) : PactTypeAlphabet :=
    { actions := left.actions ∪ right.actions }

  def hideInterface (alphabet : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions := alphabet.actions.filter fun action => action.1 ∉ interface }

  def mergeHidden (left right : PactTypeAlphabet)
      (interface : Interface) : PactTypeAlphabet :=
    { actions :=
        (left.actions ∪ right.actions).filter fun action =>
          action.1 ∉ interface }


  def ComplementaryOn
      (left right : PactTypeAlphabet) (interface : Interface) : Prop :=
    ∀ msg ∈ interface,
      (((msg, MessageDir.send) ∈ left.actions ∧
          (msg, MessageDir.recv) ∈ right.actions) ∨
        ((msg, MessageDir.recv) ∈ left.actions ∧
          (msg, MessageDir.send) ∈ right.actions))

end PactTypeAlphabet

/-- The type grammar, annotated with the fixed alphabet chosen for each
subterm. -/
inductive PactType : Type where
  | message : PactTypeAlphabet → MessageId → MessageDir → PactType
  | progress : PactTypeAlphabet → ProcId → PactType
  | tock : PactTypeAlphabet → PactType
  | skip : PactTypeAlphabet → PactType
  | choice : PactTypeAlphabet → PactType → PactType → PactType
  | seq : PactTypeAlphabet → PactType → PactType → PactType
  | par : PactTypeAlphabet → PactType → PactType → Interface → PactType
  | var : PactTypeAlphabet → String → PactType
  | recur : PactTypeAlphabet → String → PactType → PactType
  | fairChoice : PactTypeAlphabet → BranchId → PactType → PactType → PactType
  | xoffer : PactTypeAlphabet → PactType → List (BareMessage × PactType) →
      PactType
  | offer : PactTypeAlphabet → PactType → List (BareMessage × PactType) →
      PactType

/-- Recursive branch lists prevent the stock deriving handler from closing. -/
noncomputable instance instDecidableEqPactType : DecidableEq PactType :=
  Classical.decEq PactType

namespace PactType

  def alphabet : PactType → PactTypeAlphabet
    | .message alphabet _ _ => alphabet
    | .progress alphabet _ => alphabet
    | .tock alphabet => alphabet
    | .skip alphabet => alphabet
    | .choice alphabet _ _ => alphabet
    | .seq alphabet _ _ => alphabet
    | .par alphabet _ _ _ => alphabet
    | .var alphabet _ => alphabet
    | .recur alphabet _ _ => alphabet
    | .fairChoice alphabet _ _ _ => alphabet
    | .xoffer alphabet _ _ => alphabet
    | .offer alphabet _ _ => alphabet

  def recurSelf (name : String) (body : PactType) : PactType :=
    .recur body.alphabet name body

  /-! Actions a type can perform.  Needed here so a conjunctive-offer branch
  can be given the alphabet its siblings do not own. -/
  mutual
    def MessageActions : PactType → Finset BareMessage
      | .message _ msg dir => {(msg, dir)}
      | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => MessageActions body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          MessageActions left ∪ MessageActions right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          MessageActions elseType ∪ BranchMessageActions branches
    termination_by processType => sizeOf processType

    def BranchMessageActions : List (BareMessage × PactType) → Finset BareMessage
      | [] => ∅
      | (action, processType) :: rest =>
          {action} ∪ MessageActions processType ∪ BranchMessageActions rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

end PactType

namespace PactTypeAlphabet

  /-- Compatibility of the fixed alphabets at a parallel node.

  On interface ids the two children use complementary polarities.  The parent
  declares each child's non-interface actions together with the actions the
  sibling body actually performs — one equation from each side. -/
  structure ParallelCompatible
      (parent left right : PactTypeAlphabet)
      (leftType rightType : PactType) (interface : Interface) : Prop where
    complementary : ComplementaryOn left right interface
    parent_left : parent.actions =
      (hideInterface left interface).actions ∪ PactType.MessageActions rightType
    parent_right : parent.actions =
      (hideInterface right interface).actions ∪ PactType.MessageActions leftType

end PactTypeAlphabet

namespace PactType

  /-- Actions declared by the branch alphabets of an offer. -/
  def branchAlphabetActions : List (BareMessage × PactType) → Finset BareMessage
    | [] => ∅
    | (_, processType) :: rest =>
        processType.alphabet.actions ∪ branchAlphabetActions rest

  mutual
    /-- The fixed alphabet discipline for type syntax.

    Every constructor carries an alphabet.  For all non-parallel constructors,
    every immediate type child carries the same alphabet.  A parallel node is
    the one constructor that composes two different child alphabets; their
    shared message ids are exactly the interface, and those shared actions are
    owned in complementary polarities.
    -/
    def AlphabetWellFormed : PactType → Prop
      | .message alphabet _ _ =>
          alphabet.WellFormed
      | .progress alphabet _ =>
          alphabet.WellFormed
      | .tock alphabet | .skip alphabet | .var alphabet _ =>
          alphabet.WellFormed
      | .choice alphabet left right | .seq alphabet left right =>
          alphabet.WellFormed ∧
            left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .fairChoice alphabet _ left right =>
          alphabet.WellFormed ∧
            left.alphabet = alphabet ∧ right.alphabet = alphabet ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .recur alphabet _ body =>
          alphabet.WellFormed ∧ body.alphabet = alphabet ∧
            AlphabetWellFormed body
      | .par alphabet left right interface =>
          alphabet.WellFormed ∧
            PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
              right.alphabet left right interface ∧
            AlphabetWellFormed left ∧ AlphabetWellFormed right
      | .xoffer alphabet elseType branches =>
          alphabet.WellFormed ∧ elseType.alphabet = alphabet ∧
            AlphabetWellFormed elseType ∧
            BranchesAlphabetWellFormed alphabet branches
      | .offer alphabet elseType branches =>
          alphabet.WellFormed ∧ elseType.alphabet = alphabet ∧
            AlphabetWellFormed elseType ∧
            OfferBranchesWellFormed alphabet ∅ branches
    termination_by processType => sizeOf processType

    def BranchesAlphabetWellFormed
        (alphabet : PactTypeAlphabet) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
            processType.alphabet = alphabet ∧
            AlphabetWellFormed processType ∧
            BranchesAlphabetWellFormed alphabet rest
    termination_by branches => sizeOf branches

    /-- A conjunctive offer expands into a parallel product, so each branch
    carries the offer's actions minus everything its siblings own.  `seen`
    collects the branches already passed, `rest` those still to come. -/
    def OfferBranchesWellFormed
        (alphabet : PactTypeAlphabet) (seen : Finset BareMessage) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (action, processType) :: rest =>
            processType.alphabet.actions =
              alphabet.actions \ (seen ∪ BranchMessageActions rest) ∧
            AlphabetWellFormed processType ∧
            OfferBranchesWellFormed alphabet
              (seen ∪ ({action} ∪ MessageActions processType)) rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega

  end

  mutual
    /-- Capture-avoiding replacement of a recursive type variable. -/
    def replaceVar (processType : PactType) (var : String)
        (replacement : PactType) : PactType :=
      match processType with
      | .message alphabet msg dir => .message alphabet msg dir
      | .progress alphabet pid => .progress alphabet pid
      | .tock alphabet => .tock alphabet
      | .skip alphabet => .skip alphabet
      | .choice alphabet left right =>
          .choice alphabet (replaceVar left var replacement)
            (replaceVar right var replacement)
      | .seq alphabet left right =>
          .seq alphabet (replaceVar left var replacement)
            (replaceVar right var replacement)
      | .par alphabet left right interface =>
          .par alphabet (replaceVar left var replacement)
            (replaceVar right var replacement) interface
      | .var alphabet other => if var = other then replacement else .var alphabet other
      | .recur alphabet other body =>
          if var = other then .recur alphabet other body
          else .recur alphabet other (replaceVar body var replacement)
      | .fairChoice alphabet bid left right =>
          .fairChoice alphabet bid (replaceVar left var replacement)
            (replaceVar right var replacement)
      | .xoffer alphabet elseType branches =>
          .xoffer alphabet (replaceVar elseType var replacement)
            (replaceBranches branches var replacement)
      | .offer alphabet elseType branches =>
          .offer alphabet (replaceVar elseType var replacement)
            (replaceBranches branches var replacement)
    termination_by sizeOf processType

    def replaceBranches (branches : List (BareMessage × PactType))
        (var : String) (replacement : PactType) :
        List (BareMessage × PactType) :=
      match branches with
      | [] => []
      | (action, processType) :: rest =>
          (action, replaceVar processType var replacement) ::
            replaceBranches rest var replacement
    termination_by sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- Names in `forbidden` are never used by a recursion binder anywhere in
  the syntax.  Unlike `BinderHygienic`, the set is not extended while
  descending: this is the exact capture-avoidance invariant for substituting
  a term whose free variables are contained in `forbidden`. -/
  mutual
    def BinderFreshFor (forbidden : List String) : PactType → Prop
      | .recur _ name body =>
          name ∉ forbidden ∧ BinderFreshFor forbidden body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          BinderFreshFor forbidden left ∧ BinderFreshFor forbidden right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          BinderFreshFor forbidden elseType ∧
            BinderFreshForBranches forbidden branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    termination_by processType => sizeOf processType

    def BinderFreshForBranches (forbidden : List String) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          BinderFreshFor forbidden processType ∧
            BinderFreshForBranches forbidden rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-!
  ### Closed, clock-guarded recursive types

  `MustTockBeforeCompletion` is a conservative structural guarantee: every
  completing branch of the term crosses a clock.  It is used only to propagate
  a clock guard from the left of a sequence into its right continuation.
  Parallel requires both children to carry that guarantee, matching the fact
  that a clock step must synchronize.
  -/
  mutual
    def MustTockBeforeCompletion : PactType → Prop
      | .tock _ => True
      | .seq _ left right =>
          MustTockBeforeCompletion left ∨ MustTockBeforeCompletion right
      | .choice _ left right | .fairChoice _ _ left right |
          .par _ left right _ =>
          MustTockBeforeCompletion left ∧ MustTockBeforeCompletion right
      | .recur _ _ body => MustTockBeforeCompletion body
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          MustTockBeforeCompletion elseType ∧
            BranchesMustTockBeforeCompletion branches
      | .message _ _ _ | .progress _ _ | .skip _ | .var _ _ => False
    termination_by processType => sizeOf processType

    def BranchesMustTockBeforeCompletion :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          MustTockBeforeCompletion processType ∧
            BranchesMustTockBeforeCompletion rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-! Every free occurrence of `name` is reached only after a clock step. -/
  mutual
    def GuardedOccurrences (name : String) (guarded : Prop) :
        PactType → Prop
      | .var _ other => other = name → guarded
      | .seq _ left right =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name
              (guarded ∨ MustTockBeforeCompletion left) right
      | .choice _ left right | .fairChoice _ _ left right |
          .par _ left right _ =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name guarded right
      | .recur _ other body =>
          if other = name then True else GuardedOccurrences name guarded body
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          GuardedOccurrences name guarded elseType ∧
            GuardedBranchOccurrences name guarded branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ => True
    termination_by processType => sizeOf processType

    def GuardedBranchOccurrences (name : String) (guarded : Prop) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          GuardedOccurrences name guarded processType ∧
            GuardedBranchOccurrences name guarded rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-! All recursion variables are bound by an enclosing `recur`. -/
  mutual
    def AllVariablesBound (bound : List String) : PactType → Prop
      | .var _ name => name ∈ bound
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          AllVariablesBound bound left ∧ AllVariablesBound bound right
      | .recur _ name body => AllVariablesBound (name :: bound) body
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          AllVariablesBound bound elseType ∧
            AllBranchVariablesBound bound branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ => True
    termination_by processType => sizeOf processType

    def AllBranchVariablesBound (bound : List String) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          AllVariablesBound bound processType ∧
            AllBranchVariablesBound bound rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-!
  ### Lexical recursion-binder hygiene

  `replaceVar` stops at a binder of the substituted name.  To make textual
  unfolding coincide with the constructor graph without quotienting types by
  alpha-equivalence, a nested binder must therefore not reuse the name of an
  enclosing binder.  Sibling binders may still use the same name: neither is
  in the lexical scope of the other.
  -/
  mutual
    def BinderHygienic (bound : List String) : PactType → Prop
      | .recur _ name body =>
          name ∉ bound ∧ BinderHygienic (name :: bound) body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          BinderHygienic bound left ∧ BinderHygienic bound right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          BinderHygienic bound elseType ∧
            BinderHygienicBranches bound branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    termination_by processType => sizeOf processType

    def BinderHygienicBranches (bound : List String) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          BinderHygienic bound processType ∧
            BinderHygienicBranches bound rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

end PactType

end

end Pact
