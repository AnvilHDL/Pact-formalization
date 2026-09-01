import Mathlib.Data.Finset.Image
import Anvilpp.PactSemantics

/-!
# PactType: the type grammar, capture-avoiding substitution, binder freshness/hygiene
-/

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

  theorem branch_alphabet_eq_of_mem
      {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType}
      (hBranches : BranchesAlphabetWellFormed alphabet branches)
      (hMem : branch ∈ branches) :
      branch.2.alphabet = alphabet := by
    induction branches with
    | nil =>
        cases hMem
    | cons head tail ih =>
        rcases head with ⟨action, processType⟩
        simp only [BranchesAlphabetWellFormed] at hBranches
        simp only [List.mem_cons] at hMem
        rcases hMem with hHead | hTail
        · cases hHead
          exact hBranches.1
        · exact ih hBranches.2.2 hTail

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

  theorem replaceVar_alphabet_eq_of_replacement
      (processType : PactType) (name : String) {replacement : PactType}
      (hReplacement : replacement.alphabet = processType.alphabet) :
      (processType.replaceVar name replacement).alphabet =
        processType.alphabet := by
    cases processType with
    | var alphabet other =>
        by_cases hName : name = other
        · subst other
          simpa [replaceVar, PactType.alphabet] using hReplacement
        · simp [replaceVar, PactType.alphabet, hName]
    | recur alphabet other body =>
        by_cases hName : name = other <;>
          simp [replaceVar, PactType.alphabet, hName]
    | message alphabet msg dir => simp [replaceVar, PactType.alphabet]
    | progress alphabet pid => simp [replaceVar, PactType.alphabet]
    | tock alphabet => simp [replaceVar, PactType.alphabet]
    | skip alphabet => simp [replaceVar, PactType.alphabet]
    | choice alphabet left right => simp [replaceVar, PactType.alphabet]
    | seq alphabet left right => simp [replaceVar, PactType.alphabet]
    | par alphabet left right interface =>
        simp [replaceVar, PactType.alphabet]
    | fairChoice alphabet bid left right =>
        simp [replaceVar, PactType.alphabet]
    | xoffer alphabet elseType branches =>
        simp [replaceVar, PactType.alphabet]
    | offer alphabet elseType branches =>
        simp [replaceVar, PactType.alphabet]

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

  mutual
    /-- Replacing a variable by its recursion binder never shrinks the type. -/
    theorem sizeOf_le_replaceVar_recur (processType : PactType)
        (name : String) (body : PactType) :
        sizeOf processType ≤
          sizeOf (processType.replaceVar name (recurSelf name body)) := by
      cases processType with
      | message alphabet msg dir => simp [replaceVar]
      | progress alphabet pid => simp [replaceVar]
      | tock alphabet => simp [replaceVar]
      | skip alphabet => simp [replaceVar]
      | var alphabet other =>
          by_cases hName : name = other
          · subst other
            simp [replaceVar, recurSelf]
          · simp [replaceVar, recurSelf, hName]
      | recur alphabet other nestedBody =>
          by_cases hName : name = other
          · simp [replaceVar, recurSelf, hName]
          · simp [replaceVar, hName]
            have hBody := sizeOf_le_replaceVar_recur nestedBody name body
            omega
      | choice alphabet left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | fairChoice alphabet bid left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | seq alphabet left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | par alphabet left right interface =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp [replaceVar]
          omega
      | xoffer alphabet elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          omega
      | offer alphabet elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          omega
    termination_by sizeOf processType

    theorem sizeOf_le_replaceBranches_recur
        (branches : List (BareMessage × PactType))
        (name : String) (body : PactType) :
        sizeOf branches ≤
          sizeOf (replaceBranches branches name (recurSelf name body)) := by
      cases branches with
      | nil => simp [replaceBranches]
      | cons branch rest =>
          rcases branch with ⟨action, branchType⟩
          have hBranch := sizeOf_le_replaceVar_recur branchType name body
          have hRest := sizeOf_le_replaceBranches_recur rest name body
          simp [replaceBranches]
          omega
    termination_by sizeOf branches
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

  /-- Enlarging the set of names regarded as bound preserves closedness. -/
  theorem allVariablesBound_mono
      {smaller larger : List String}
      (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
      ∀ processType,
        AllVariablesBound smaller processType →
          AllVariablesBound larger processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType smaller larger with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            AllBranchVariablesBound smaller branches →
              AllBranchVariablesBound larger branches := by
          intro branches hBranchesSize h
          induction branches with
          | nil => simp [AllBranchVariablesBound]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [AllBranchVariablesBound] at h ⊢
              have hBranchSize : sizeOf branchType < n := by
                have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                  simp_wf
                  omega
                have hHead : sizeOf (action, branchType) <
                    sizeOf ((action, branchType) :: rest) := by
                  simp_wf
                  omega
                omega
              have hRestSize : sizeOf rest < n := by
                have hRest : sizeOf rest <
                    sizeOf ((action, branchType) :: rest) := by
                  simp_wf
                  omega
                omega
              exact ⟨ih (sizeOf branchType) hBranchSize hSubset branchType
                  rfl h.1, restIH hRestSize h.2⟩
        cases processType with
        | message alphabet msg dir => simp [AllVariablesBound]
        | progress alphabet pid => simp [AllVariablesBound]
        | tock alphabet => simp [AllVariablesBound]
        | skip alphabet => simp [AllVariablesBound]
        | var alphabet name => simpa [AllVariablesBound] using hSubset name
        | recur alphabet name body =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize
              (by
                intro other hMem
                simp only [List.mem_cons] at hMem ⊢
                exact hMem.elim Or.inl (fun h => Or.inr (hSubset other h)))
              body rfl h
        | choice alphabet left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | fairChoice alphabet bid left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | seq alphabet left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | par alphabet left right interface =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | xoffer alphabet elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer alphabet elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩

end PactType

end

end Pact
