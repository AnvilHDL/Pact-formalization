import Mathlib.Data.Finset.Image
import Anvilpp.PactSemantics

/-!
# Pact type syntax and operational semantics
-/

namespace Pact

noncomputable section

/-! ## Type syntax and erasure -/

/-- The type grammar from Section 4.1. -/
inductive PactType : Type where
  | message : MessageId → MessageDir → PactType
  | progress : ProcId → PactType
  | tock : PactType
  | skip : PactType
  | choice : PactType → PactType → PactType
  | seq : PactType → PactType → PactType
  | par : PactType → PactType → Interface → PactType
  | var : String → PactType
  | recur : String → PactType → PactType
  | fairChoice : BranchId → PactType → PactType → PactType
  | xoffer : PactType → List (BareMessage × PactType) → PactType
  | offer : PactType → List (BareMessage × PactType) → PactType

/-- Recursive branch lists prevent the stock deriving handler from closing. -/
noncomputable instance instDecidableEqPactType : DecidableEq PactType :=
  Classical.decEq PactType

namespace PactType

  mutual
    /-- Capture-avoiding replacement of a recursive type variable. -/
    def replaceVar (processType : PactType) (var : String)
        (replacement : PactType) : PactType :=
      match processType with
      | .message msg dir => .message msg dir
      | .progress pid => .progress pid
      | .tock => .tock
      | .skip => .skip
      | .choice left right =>
          .choice (replaceVar left var replacement) (replaceVar right var replacement)
      | .seq left right =>
          .seq (replaceVar left var replacement) (replaceVar right var replacement)
      | .par left right interface =>
          .par (replaceVar left var replacement) (replaceVar right var replacement) interface
      | .var other => if var = other then replacement else .var other
      | .recur other body =>
          if var = other then .recur other body
          else .recur other (replaceVar body var replacement)
      | .fairChoice bid left right =>
          .fairChoice bid
            (replaceVar left var replacement) (replaceVar right var replacement)
      | .xoffer elseType branches =>
          .xoffer (replaceVar elseType var replacement)
            (replaceBranches branches var replacement)
      | .offer elseType branches =>
          .offer (replaceVar elseType var replacement)
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
      | .recur name body =>
          name ∉ forbidden ∧ BinderFreshFor forbidden body
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          BinderFreshFor forbidden left ∧ BinderFreshFor forbidden right
      | .xoffer elseType branches | .offer elseType branches =>
          BinderFreshFor forbidden elseType ∧
            BinderFreshForBranches forbidden branches
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
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
          sizeOf (processType.replaceVar name (.recur name body)) := by
      cases processType with
      | message msg dir => simp [replaceVar]
      | progress pid => simp [replaceVar]
      | tock => simp [replaceVar]
      | skip => simp [replaceVar]
      | var other =>
          by_cases hName : name = other
          · subst other
            simp [replaceVar]
          · simp [replaceVar, hName]
      | recur other nestedBody =>
          by_cases hName : name = other
          · simp [replaceVar, hName]
          · simp only [replaceVar, hName]
            have hBody := sizeOf_le_replaceVar_recur nestedBody name body
            simpa using Nat.add_le_add_left hBody (1 + sizeOf other)
      | choice left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp only [replaceVar]
          change 1 + sizeOf left + sizeOf right ≤
            1 + sizeOf (left.replaceVar name (.recur name body)) +
              sizeOf (right.replaceVar name (.recur name body))
          omega
      | fairChoice bid left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp only [replaceVar]
          change 1 + bid + sizeOf left + sizeOf right ≤
            1 + bid + sizeOf (left.replaceVar name (.recur name body)) +
              sizeOf (right.replaceVar name (.recur name body))
          simpa only [Nat.add_assoc] using
            Nat.add_le_add_left (Nat.add_le_add hLeft hRight) (1 + bid)
      | seq left right =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp only [replaceVar]
          change 1 + sizeOf left + sizeOf right ≤
            1 + sizeOf (left.replaceVar name (.recur name body)) +
              sizeOf (right.replaceVar name (.recur name body))
          omega
      | par left right interface =>
          have hLeft := sizeOf_le_replaceVar_recur left name body
          have hRight := sizeOf_le_replaceVar_recur right name body
          simp only [replaceVar]
          change 1 + sizeOf left + sizeOf right + sizeOf interface ≤
            1 + sizeOf (left.replaceVar name (.recur name body)) +
              sizeOf (right.replaceVar name (.recur name body)) +
                sizeOf interface
          omega
      | xoffer elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          simpa only [Nat.add_assoc] using
            Nat.add_le_add_left (Nat.add_le_add hElse hBranches) 1
      | offer elseType branches =>
          have hElse := sizeOf_le_replaceVar_recur elseType name body
          have hBranches := sizeOf_le_replaceBranches_recur branches name body
          simp [replaceVar]
          simpa only [Nat.add_assoc] using
            Nat.add_le_add_left (Nat.add_le_add hElse hBranches) 1
    termination_by sizeOf processType

    theorem sizeOf_le_replaceBranches_recur
        (branches : List (BareMessage × PactType))
        (name : String) (body : PactType) :
        sizeOf branches ≤
          sizeOf (replaceBranches branches name (.recur name body)) := by
      cases branches with
      | nil => simp [replaceBranches]
      | cons branch rest =>
          rcases branch with ⟨action, branchType⟩
          have hBranch := sizeOf_le_replaceVar_recur branchType name body
          have hRest := sizeOf_le_replaceBranches_recur rest name body
          simp only [replaceBranches]
          change 1 + (1 + sizeOf action + sizeOf branchType) + sizeOf rest ≤
            1 + (1 + sizeOf action +
              sizeOf (branchType.replaceVar name (.recur name body))) +
                sizeOf (replaceBranches rest name (.recur name body))
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
      | .tock => True
      | .seq left right =>
          MustTockBeforeCompletion left ∨ MustTockBeforeCompletion right
      | .choice left right | .fairChoice _ left right |
          .par left right _ =>
          MustTockBeforeCompletion left ∧ MustTockBeforeCompletion right
      | .recur _ body => MustTockBeforeCompletion body
      | .xoffer elseType branches | .offer elseType branches =>
          MustTockBeforeCompletion elseType ∧
            BranchesMustTockBeforeCompletion branches
      | .message _ _ | .progress _ | .skip | .var _ => False
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
      | .var other => other = name → guarded
      | .seq left right =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name
              (guarded ∨ MustTockBeforeCompletion left) right
      | .choice left right | .fairChoice _ left right |
          .par left right _ =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name guarded right
      | .recur other body =>
          if other = name then True else GuardedOccurrences name guarded body
      | .xoffer elseType branches | .offer elseType branches =>
          GuardedOccurrences name guarded elseType ∧
            GuardedBranchOccurrences name guarded branches
      | .message _ _ | .progress _ | .tock | .skip => True
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
      | .var name => name ∈ bound
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          AllVariablesBound bound left ∧ AllVariablesBound bound right
      | .recur name body => AllVariablesBound (name :: bound) body
      | .xoffer elseType branches | .offer elseType branches =>
          AllVariablesBound bound elseType ∧
            AllBranchVariablesBound bound branches
      | .message _ _ | .progress _ | .tock | .skip => True
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
      | .recur name body =>
          name ∉ bound ∧ BinderHygienic (name :: bound) body
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          BinderHygienic bound left ∧ BinderHygienic bound right
      | .xoffer elseType branches | .offer elseType branches =>
          BinderHygienic bound elseType ∧
            BinderHygienicBranches bound branches
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
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

  /- Binder hygiene is contravariant in the list of already-active names:
  removing active names only weakens the freshness obligations. -/
  theorem binderHygienic_mono
      {smaller larger : List String}
      (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
      ∀ processType,
        BinderHygienic larger processType →
          BinderHygienic smaller processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType smaller larger with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            BinderHygienicBranches larger branches →
              BinderHygienicBranches smaller branches := by
          intro branches hBranchesSize h
          induction branches with
          | nil => simp [BinderHygienicBranches]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [BinderHygienicBranches] at h ⊢
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
                  rfl h.1,
                restIH hRestSize h.2⟩
        cases processType with
        | message msg dir => simp [BinderHygienic]
        | progress pid => simp [BinderHygienic]
        | tock => simp [BinderHygienic]
        | skip => simp [BinderHygienic]
        | var name => simp [BinderHygienic]
        | recur name body =>
            intro h
            simp only [BinderHygienic] at h ⊢
            refine ⟨fun hMem => h.1 (hSubset name hMem), ?_⟩
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize
              (by
                intro other hMem
                simp only [List.mem_cons] at hMem ⊢
                exact hMem.elim Or.inl (fun h => Or.inr (hSubset other h)))
              body rfl h.2
        | choice left right =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | fairChoice bid left right =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | seq left right =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | par left right interface =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | xoffer elseType branches =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer elseType branches =>
            intro h
            simp only [BinderHygienic] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩

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
        | message msg dir => simp [AllVariablesBound]
        | progress pid => simp [AllVariablesBound]
        | tock => simp [AllVariablesBound]
        | skip => simp [AllVariablesBound]
        | var name => simpa [AllVariablesBound] using hSubset name
        | recur name body =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize
              (by
                intro other hMem
                simp only [List.mem_cons] at hMem ⊢
                exact hMem.elim Or.inl (fun h => Or.inr (hSubset other h)))
              body rfl h
        | choice left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | fairChoice bid left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | seq left right =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | par left right interface =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize hSubset left rfl h.1,
              ih (sizeOf right) hRightSize hSubset right rfl h.2⟩
        | xoffer elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer elseType branches =>
            intro h
            simp only [AllVariablesBound] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize hSubset elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩

  theorem binderHygienic_binderFreshFor (bound : List String) :
      ∀ processType,
        BinderHygienic bound processType → BinderFreshFor bound processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType bound with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            BinderHygienicBranches bound branches →
              BinderFreshForBranches bound branches := by
          intro branches hBranchesSize h
          induction branches with
          | nil => simp [BinderFreshForBranches]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [BinderHygienicBranches, BinderFreshForBranches] at h ⊢
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
              exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                  h.1, restIH hRestSize h.2⟩
        cases processType with
        | message msg dir => simp [BinderFreshFor]
        | progress pid => simp [BinderFreshFor]
        | tock => simp [BinderFreshFor]
        | skip => simp [BinderFreshFor]
        | var name => simp [BinderFreshFor]
        | recur name body =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            refine ⟨h.1, ?_⟩
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ih (sizeOf body) hBodySize bound body rfl
              (PactType.binderHygienic_mono
                (by intro x hx; exact List.mem_cons_of_mem name hx) body h.2)
        | choice left right =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl h.1,
              ih (sizeOf right) hRightSize bound right rfl h.2⟩
        | fairChoice bid left right =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl h.1,
              ih (sizeOf right) hRightSize bound right rfl h.2⟩
        | seq left right =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl h.1,
              ih (sizeOf right) hRightSize bound right rfl h.2⟩
        | par left right interface =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl h.1,
              ih (sizeOf right) hRightSize bound right rfl h.2⟩
        | xoffer elseType branches =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer elseType branches =>
            intro h
            simp only [BinderHygienic, BinderFreshFor] at h ⊢
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
  /-! Every recursive backedge in a type is protected by a prior clock. -/
  mutual
    def ClockGuarded : PactType → Prop
      | .recur name body =>
          GuardedOccurrences name False body ∧ ClockGuarded body
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          ClockGuarded left ∧ ClockGuarded right
      | .xoffer elseType branches | .offer elseType branches =>
          ClockGuarded elseType ∧ ClockGuardedBranches branches
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
    termination_by processType => sizeOf processType

    def ClockGuardedBranches : List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          ClockGuarded processType ∧ ClockGuardedBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-!
  ### Tail-regular recursion

  The constructor automaton represents a recursive call by a backedge to the
  binder's body entry.  This is sound exactly when taking that call does not
  retain a surrounding control context.  A call in the left of a sequence
  would retain the right continuation; a call below parallel would retain its
  sibling; and a call in a conjunctive-offer branch would retain the generated
  product of the other branches.  Those are therefore non-tail positions.

  Choices and exclusive offers discard their constructor when selecting a
  continuation, and the right side of a sequence is entered only after the
  sequence constructor has been discarded, so they preserve tail position.
  -/
  mutual
    def TailOccurrences (name : String) (tail : Prop) : PactType → Prop
      | .var other => other = name → tail
      | .seq left right =>
          TailOccurrences name False left ∧
            TailOccurrences name tail right
      | .par left right _ =>
          TailOccurrences name False left ∧
            TailOccurrences name False right
      | .choice left right | .fairChoice _ left right =>
          TailOccurrences name tail left ∧
            TailOccurrences name tail right
      | .recur other body =>
          if other = name then True else TailOccurrences name tail body
      | .xoffer elseType branches =>
          TailOccurrences name tail elseType ∧
            TailBranchOccurrences name tail branches
      | .offer elseType branches =>
          TailOccurrences name tail elseType ∧
            TailBranchOccurrences name False branches
      | .message _ _ | .progress _ | .tock | .skip => True
    termination_by processType => sizeOf processType

    def TailBranchOccurrences (name : String) (tail : Prop) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          TailOccurrences name tail processType ∧
            TailBranchOccurrences name tail rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- Every binder is used only in tail positions, and every nested binder has
  the same property.  This is the finite-control part of regularity. -/
  mutual
    def TailRecursive : PactType → Prop
      | .recur name body =>
          TailOccurrences name True body ∧ TailRecursive body
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          TailRecursive left ∧ TailRecursive right
      | .xoffer elseType branches | .offer elseType branches =>
          TailRecursive elseType ∧ TailRecursiveBranches branches
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
    termination_by processType => sizeOf processType

    def TailRecursiveBranches : List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          TailRecursive processType ∧ TailRecursiveBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-!
  ### Per-cycle message linearity

  `PrefixMessageIds` collects messages that may occur before the first clock;
  `SuffixMessageIds` collects messages that may occur after the last clock on
  a completing path.  Their disjointness at sequence and recursion boundaries
  rules out two exchanges of the same message identifier in one clock cycle.
  -/
  mutual
    def CanCompleteBeforeTock : PactType → Bool
      | .message _ _ | .progress _ | .skip => true
      | .tock | .var _ => false
      | .recur _ body => CanCompleteBeforeTock body
      | .choice left right | .fairChoice _ left right =>
          CanCompleteBeforeTock left || CanCompleteBeforeTock right
      | .seq left right | .par left right _ =>
          CanCompleteBeforeTock left && CanCompleteBeforeTock right
      | .xoffer elseType branches | .offer elseType branches =>
          CanCompleteBeforeTock elseType ||
            BranchCanCompleteBeforeTock branches
    termination_by processType => sizeOf processType

    def BranchCanCompleteBeforeTock :
        List (BareMessage × PactType) → Bool
      | [] => false
      | (_, processType) :: rest =>
          CanCompleteBeforeTock processType ||
            BranchCanCompleteBeforeTock rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def PrefixMessageIds : PactType → Finset MessageId
      | .message msg _ => {msg}
      | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => PrefixMessageIds body
      | .choice left right | .fairChoice _ left right |
          .par left right _ =>
          PrefixMessageIds left ∪ PrefixMessageIds right
      | .seq left right =>
          PrefixMessageIds left ∪
            if CanCompleteBeforeTock left then PrefixMessageIds right else ∅
      | .xoffer elseType branches | .offer elseType branches =>
          PrefixMessageIds elseType ∪ BranchPrefixMessageIds branches
    termination_by processType => sizeOf processType

    def BranchPrefixMessageIds :
        List (BareMessage × PactType) → Finset MessageId
      | [] => ∅
      | (action, processType) :: rest =>
          {action.1} ∪ PrefixMessageIds processType ∪
            BranchPrefixMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def SuffixMessageIds : PactType → Finset MessageId
      | .message msg _ => {msg}
      | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => SuffixMessageIds body
      | .choice left right | .fairChoice _ left right |
          .par left right _ =>
          SuffixMessageIds left ∪ SuffixMessageIds right
      | .seq left right =>
          SuffixMessageIds right ∪
            if CanCompleteBeforeTock right then SuffixMessageIds left else ∅
      | .xoffer elseType branches | .offer elseType branches =>
          SuffixMessageIds elseType ∪ BranchSuffixMessageIds branches
    termination_by processType => sizeOf processType

    def BranchSuffixMessageIds :
        List (BareMessage × PactType) → Finset MessageId
      | [] => ∅
      | (action, processType) :: rest =>
          SuffixMessageIds processType ∪
            (if CanCompleteBeforeTock processType then {action.1} else ∅) ∪
            BranchSuffixMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def SameCycleMessageLinear : PactType → Prop
      | .seq left right =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right ∧
            Disjoint (SuffixMessageIds left) (PrefixMessageIds right)
      | .recur _ body =>
          SameCycleMessageLinear body ∧
            Disjoint (SuffixMessageIds body) (PrefixMessageIds body)
      | .choice left right | .fairChoice _ left right |
          .par left right _ =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right
      | .xoffer elseType branches | .offer elseType branches =>
          SameCycleMessageLinear elseType ∧
            SameCycleMessageLinearBranches branches
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
    termination_by processType => sizeOf processType

    def SameCycleMessageLinearBranches :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (action, processType) :: rest =>
          SameCycleMessageLinear processType ∧
            action.1 ∉ PrefixMessageIds processType ∧
            SameCycleMessageLinearBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- All synchronization interfaces occurring below a type.  This is used by
  the compositional proof only; it does not alter operational future offers. -/
  mutual
    def ParallelInterfaces : PactType → Finset MessageId
      | .message _ _ | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => ParallelInterfaces body
      | .choice left right | .seq left right | .fairChoice _ left right =>
          ParallelInterfaces left ∪ ParallelInterfaces right
      | .par left right interface =>
          interface ∪ ParallelInterfaces left ∪ ParallelInterfaces right
      | .xoffer elseType branches | .offer elseType branches =>
          ParallelInterfaces elseType ∪ ParallelBranchInterfaces branches
    termination_by processType => sizeOf processType

    def ParallelBranchInterfaces :
        List (BareMessage × PactType) → Finset MessageId
      | [] => ∅
      | (_, processType) :: rest =>
          ParallelInterfaces processType ∪ ParallelBranchInterfaces rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- A parallel binder may not reuse an interface owned by an ancestor or a
  descendant binder.  Sibling products may still use the same identifier. -/
  mutual
    def InterfaceScoped : PactType → Prop
      | .message _ _ | .progress _ | .tock | .skip | .var _ => True
      | .recur _ body => InterfaceScoped body
      | .choice left right | .seq left right | .fairChoice _ left right =>
          InterfaceScoped left ∧ InterfaceScoped right
      | .par left right interface =>
          Disjoint interface
              (ParallelInterfaces left ∪ ParallelInterfaces right) ∧
            InterfaceScoped left ∧ InterfaceScoped right
      | .xoffer elseType branches | .offer elseType branches =>
          InterfaceScoped elseType ∧ InterfaceScopedBranches branches
    termination_by processType => sizeOf processType

    def InterfaceScopedBranches :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          InterfaceScoped processType ∧ InterfaceScopedBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  theorem parallel_interface_subset_parallelInterfaces
      (left right : PactType) (interface : Interface) :
      interface ⊆ ParallelInterfaces (.par left right interface) := by
    simp [ParallelInterfaces]

  theorem sameCycleMessageLinear_rejects_repeat
      (msg : MessageId) (first second : MessageDir) :
      ¬ SameCycleMessageLinear
        (.seq (.message msg first) (.message msg second)) := by
    simp [SameCycleMessageLinear, SuffixMessageIds, PrefixMessageIds]

  theorem sameCycleMessageLinear_allows_distinct
      (first second : MessageId) (firstDir secondDir : MessageDir)
      (hDistinct : first ≠ second) :
      SameCycleMessageLinear
        (.seq (.message first firstDir) (.message second secondDir)) := by
    have hReverse : second ≠ first := Ne.symm hDistinct
    simp [SameCycleMessageLinear, SuffixMessageIds, PrefixMessageIds,
      hReverse]

  theorem sameCycleMessageLinear_clock_resets
      (msg : MessageId) (first second : MessageDir) :
      SameCycleMessageLinear
        (.seq (.message msg first) (.seq .tock (.message msg second))) := by
    simp [SameCycleMessageLinear, SuffixMessageIds, PrefixMessageIds,
      CanCompleteBeforeTock]

  theorem sameCycleMessageLinear_rejects_repeated_offer_head
      (msg : MessageId) (dir : MessageDir) :
      ¬ SameCycleMessageLinear
        (.xoffer .skip [((msg, dir), .message msg dir)]) := by
    simp [SameCycleMessageLinear, SameCycleMessageLinearBranches,
      PrefixMessageIds]

  theorem clockGuarded_accepts_cycle_delay (name : String) :
      ClockGuarded (.recur name (.seq .tock (.var name))) := by
    simp [ClockGuarded, GuardedOccurrences, MustTockBeforeCompletion]

  theorem clockGuarded_rejects_message_only_delay
      (name : String) (msg : MessageId) (dir : MessageDir) :
      ¬ ClockGuarded
        (.recur name (.seq (.message msg dir) (.var name))) := by
    simp [ClockGuarded, GuardedOccurrences, MustTockBeforeCompletion]

  theorem tailRecursive_accepts_cycle_loop (name : String) :
      TailRecursive (.recur name (.seq .tock (.var name))) := by
    simp [TailRecursive, TailOccurrences]

  theorem tailRecursive_rejects_retained_sequence
      (name msg : String) (dir : MessageDir) :
      ¬ TailRecursive
        (.recur name (.seq (.seq .tock (.var name)) (.message msg dir))) := by
    simp [TailRecursive, TailOccurrences]

  theorem tailRecursive_rejects_parallel_call (name : String) :
      ¬ TailRecursive
        (.recur name (.par (.seq .tock (.var name)) .tock ∅)) := by
    simp [TailRecursive, TailOccurrences]

  /-- The guarded recursive shape used to audit future resolution through a
  parallel product satisfies closure, clock guarding, and per-cycle message
  linearity.  It motivates the separate tail-recursion condition: those three
  properties alone do not justify resolving a child's recursion-dependent
  futures before the enclosing binder installs its back-edge. -/
  theorem guarded_parallel_future_audit_is_regular :
      let leftBody : PactType :=
        .seq (.message "a" .send) (.seq .tock (.var "x"))
      let processType : PactType :=
        .recur "x" (.par leftBody .tock ∅)
      processType.AllVariablesBound [] ∧ processType.ClockGuarded ∧
        processType.SameCycleMessageLinear := by
    simp [AllVariablesBound, ClockGuarded, GuardedOccurrences,
      MustTockBeforeCompletion, SameCycleMessageLinear, SuffixMessageIds,
      PrefixMessageIds, CanCompleteBeforeTock]

end PactType

mutual
/-- Structural, data-oblivious abstraction `abs(P)`-/
  def inferProcess (process : Proc) : PactType :=
    match process with
    | Proc.send msg _ p =>
        .seq (.message msg .send) (inferProcess p)
    | Proc.recv msg _ p =>
        .seq (.message msg .recv) (inferProcess p)
    | Proc.var name => .var name
    | Proc.skip => .skip
    | Proc.endp pid => .progress pid
    | Proc.cycle => .tock
    | Proc.par left right interface =>
        .par (inferProcess left) (inferProcess right) interface
    | Proc.seq left right =>
        .seq (inferProcess left) (inferProcess right)
    | Proc.letp _ _ p => inferProcess p
    | Proc.ifunfair _ left right =>
        .choice (inferProcess left) (inferProcess right)
    | Proc.iffair bid _ left right =>
        .fairChoice bid (inferProcess left) (inferProcess right)
    | Proc.xoffer elseType branches =>
        .xoffer (inferProcess elseType) (branches.map inferBranch)
    | Proc.offer elseType branches =>
        .offer (inferProcess elseType) (branches.map inferBranch)
    | Proc.recur name body => .recur name (inferProcess body)

  /-- Erase a branch head and recursively abstract its continuation. -/
  def inferBranch : ChoiceBranch → BareMessage × PactType
    | .send msg _ process => ((msg, .send), inferProcess process)
    | .recv msg _ process => ((msg, .recv), inferProcess process)

end

inductive TypeObservation : Type where
  | message : MessageId → MessageDir → TypeObservation
  | resolved : MessageId → TypeObservation
  | fair : BranchId → Bool → TypeObservation
  | progress : ProcId → TypeObservation
  deriving DecidableEq

inductive TypeLabel : Type where
  | actions : Finset TypeObservation → TypeLabel
  | tock : TypeLabel
  deriving DecidableEq

namespace TypeLabel

  def silent : TypeLabel := .actions ∅

  def message (msg : MessageId) (dir : MessageDir) : TypeLabel :=
    .actions {TypeObservation.message msg dir}

  def fair (bid : BranchId) (taken : Bool) : TypeLabel :=
    .actions {TypeObservation.fair bid taken}

  def progress (pid : ProcId) : TypeLabel :=
    .actions {TypeObservation.progress pid}

  def isTock : TypeLabel → Prop
    | .tock => True
    | .actions _ => False

  def contains (label : TypeLabel) (obs : TypeObservation) : Prop :=
    match label with
    | .actions observations => obs ∈ observations
    | .tock => False

  def messageIdsWith (wanted : MessageDir)
      (observations : Finset TypeObservation) : Finset MessageId := by
    classical
    exact (observations.filter fun observation =>
      match observation with
      | .message _ dir => dir = wanted
      | _ => False).image fun observation =>
        match observation with
        | .message msg _ => msg
        | _ => ""

  def sends : TypeLabel → Finset MessageId
    | .actions observations => messageIdsWith .send observations
    | .tock => ∅

  def recvs : TypeLabel → Finset MessageId
    | .actions observations => messageIdsWith .recv observations
    | .tock => ∅

  /-- The erased synchronization predicate `Sync_I`. -/
  def Sync (interface : Interface) (left right : TypeLabel) : Prop :=
    interface ∩ left.sends = interface ∩ right.recvs ∧
    interface ∩ left.recvs = interface ∩ right.sends ∧
    (left.isTock ↔ right.isTock)

  def synced (interface : Interface) (left right : TypeLabel) : Finset MessageId :=
    (interface ∩ left.sends) ∪ (interface ∩ right.sends)

  def isRawSyncedMessage (syncedMessages : Finset MessageId) :
      TypeObservation → Bool
    | .message msg _ => msg ∈ syncedMessages
    | _ => false

  /-- The erased label combination `α₁ ∪_I α₂`. -/
  def combine (interface : Interface) : TypeLabel → TypeLabel → TypeLabel
    | .tock, .tock => .tock
    | .actions left, .actions right =>
        let syncedMessages := synced interface (.actions left) (.actions right)
        let boundary :=
          (left ∪ right).filter fun observation =>
            !(isRawSyncedMessage syncedMessages observation)
        .actions (boundary ∪ syncedMessages.image TypeObservation.resolved)
    | _, _ => silent

end TypeLabel

def eraseObservation : Observation → TypeObservation
  | .message msg dir _ => .message msg dir
  | .resolved msg => .resolved msg
  | .fair bid taken => .fair bid taken
  | .progress pid => .progress pid

/-- Payload erasure on process labels. -/
def eraseLabel : Label → TypeLabel
  | .actions observations => .actions (observations.image eraseObservation)
  | .tock => .tock

/-- A value-erased one-step environment. -/
structure TypeEnvironment : Type where
  immediate : Finset BareMessage
  future : Finset BareMessage
  clock : Bool
  deriving DecidableEq

namespace TypeEnvironment

  def empty : TypeEnvironment :=
    { immediate := ∅, future := ∅, clock := false }

  def tock : TypeEnvironment :=
    { immediate := ∅, future := ∅, clock := true }

  def WellFormed (env : TypeEnvironment) : Prop :=
    (env.clock = true → env.immediate = ∅ ∧ env.future = ∅) ∧
    (env.clock = false → env.immediate ∩ env.future = ∅)

  def hasNeed (env : TypeEnvironment) (action : BareMessage) : Prop :=
    (action.1, action.2.invert) ∈ env.immediate

end TypeEnvironment

/-- Erasure lifted to one-step environments. -/
def eraseEnvironment (env : Environment) : TypeEnvironment :=
  { immediate := env.bareImmediate
    future := env.future
    clock := env.clock }

/-! ## Type dynamics and semantic correspondence -/

/-- The complementary environment action needed to fire a type action. -/
def typeNeed (action : BareMessage) : BareMessage :=
  (action.1, action.2.invert)

def typeBranchNeeds (branches : List (BareMessage × PactType)) :
    Finset BareMessage :=
  (branches.map fun branch => typeNeed branch.1).toFinset

def TypeResolved (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.future = ∅

def TypeNoImmediateBranch (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Prop :=
  typeBranchNeeds branches ∩ env.immediate = ∅

def TypeBranchEnabled (env : TypeEnvironment)
    (branch : BareMessage × PactType) : Prop :=
  typeNeed branch.1 ∈ env.immediate

def singletonTypeXOffer (branch : BareMessage × PactType) : PactType :=
  .xoffer .skip [branch]

/-- A selected conjunctive-offer branch has no synthetic else alternative:
its head action is now mandatory, followed by its continuation. -/
def selectedTypeBranch (branch : BareMessage × PactType) : PactType :=
  .seq (.message branch.1.1 branch.1.2) branch.2

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers. -/
def parallelTypeBranches : List (BareMessage × PactType) → PactType
  | [] => .skip
  | [branch] => singletonTypeXOffer branch
  | branch :: rest =>
      .par (singletonTypeXOffer branch) (parallelTypeBranches rest) ∅

/-- Post-process the singleton-`xoffer` product after `selected` witnesses that
the conjunctive offer fired.  Exactly that singleton loses its synthetic
`skip` else-arm; all other singleton offers are retained.  Consequently the
single outcome in which every singleton selects else is absent. -/
def parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    List (BareMessage × PactType) → PactType
  | [] => .skip
  | [branch] =>
      if branch = selected then selectedTypeBranch branch
      else singletonTypeXOffer branch
  | branch :: rest =>
      if branch = selected then
        .par (selectedTypeBranch branch) (parallelTypeBranches rest) ∅
      else
        .par (singletonTypeXOffer branch)
          (parallelTypeBranchesSelecting selected rest) ∅

@[simp] theorem parallelTypeBranchesSelecting_singleton_self
    (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting branch [branch] =
      selectedTypeBranch branch := by
  simp [parallelTypeBranchesSelecting]

/-- Even duplicate branches force only one occurrence: the second singleton
retains its synthetic else arm. -/
@[simp] theorem parallelTypeBranchesSelecting_duplicate_pair
    (branch : BareMessage × PactType) :
    parallelTypeBranchesSelecting branch [branch, branch] =
      .par (selectedTypeBranch branch) (singletonTypeXOffer branch) ∅ := by
  simp [parallelTypeBranchesSelecting, parallelTypeBranches]

/-- Actions appearing at the heads of an offer's branches. -/
def typeBranchActions
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (branches.map Prod.fst).toFinset

/-- Keep only offers whose message identifier belongs to `interface`. -/
def restrictTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Remove offers hidden by a parallel interface. -/
def hideTypeOffers (interface : Interface) (offers : Finset BareMessage) :
    Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

/--
Whether a type may complete before the next clock.  Fuel bounds recursive
unfolding; a variable stops the search, which is exact for guarded recursion
when computing the offers visible before the next guard.
-/
private def typeCanCompleteThisCycleFuel : Nat → PactType → Bool
  | 0, _ => false
  | fuel + 1, processType =>
      match processType with
      | .message _ _ | .progress _ | .skip => true
      | .tock | .var _ => false
      | .recur _ body => typeCanCompleteThisCycleFuel fuel body
      | .choice left right | .fairChoice _ left right =>
          typeCanCompleteThisCycleFuel fuel left ||
            typeCanCompleteThisCycleFuel fuel right
      | .seq left right =>
          typeCanCompleteThisCycleFuel fuel left &&
            typeCanCompleteThisCycleFuel fuel right
      | .par left right _ =>
          typeCanCompleteThisCycleFuel fuel left &&
            typeCanCompleteThisCycleFuel fuel right
      | .xoffer elseType branches | .offer elseType branches =>
          typeCanCompleteThisCycleFuel fuel elseType ||
            branches.any fun branch =>
              typeCanCompleteThisCycleFuel fuel branch.2

/-- Once the fuel covers the finite syntax tree, one more unit cannot change
same-cycle completion. -/
private theorem typeCanCompleteThisCycleFuel_succ_stable :
    ∀ fuel processType, sizeOf processType ≤ fuel →
      typeCanCompleteThisCycleFuel (fuel + 1) processType =
        typeCanCompleteThisCycleFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hSize
      cases processType <;> simp at hSize
  | succ fuel ih =>
      intro processType hSize
      cases processType with
      | message msg dir => rfl
      | progress pid => rfl
      | tock => rfl
      | skip => rfl
      | var name => rfl
      | recur name body =>
          change typeCanCompleteThisCycleFuel (fuel + 1) body =
            typeCanCompleteThisCycleFuel fuel body
          apply ih
          have hBody : sizeOf body < sizeOf (PactType.recur name body) := by
            simp_wf
            omega
          omega
      | choice left right =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left ||
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right)
          rw [ih left (by
              have : sizeOf left < sizeOf (PactType.choice left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right < sizeOf (PactType.choice left right) := by
                simp_wf
                omega
              omega)]
      | fairChoice bid left right =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left ||
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf
                omega
              omega)]
      | seq left right =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left &&
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left &&
              typeCanCompleteThisCycleFuel fuel right)
          rw [ih left (by
              have : sizeOf left < sizeOf (PactType.seq left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right < sizeOf (PactType.seq left right) := by
                simp_wf
                omega
              omega)]
      | par left right interface =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) left &&
              typeCanCompleteThisCycleFuel (fuel + 1) right) =
            (typeCanCompleteThisCycleFuel fuel left &&
              typeCanCompleteThisCycleFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.par left right interface) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.par left right interface) := by
                simp_wf
                omega
              omega)]
      | xoffer elseType branches =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel (fuel + 1) branch.2)) =
            (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2))
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer elseType branches) := by
              simp_wf
              omega
            omega)]
          congr 1
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.xoffer elseType branches) := by
              simp_wf
              omega
            omega
          induction branches with
          | nil => rfl
          | cons branch rest restIH =>
              simp only [List.any_cons]
              rw [ih branch.2 (hEvery branch (by simp))]
              rw [restIH (by
                have : sizeOf (PactType.xoffer elseType rest) <
                    sizeOf (PactType.xoffer elseType (branch :: rest)) := by
                  simp_wf
                  omega
                omega) (by
                intro other hOther
                exact hEvery other (by simp [hOther]))]
      | offer elseType branches =>
          change (typeCanCompleteThisCycleFuel (fuel + 1) elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel (fuel + 1) branch.2)) =
            (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2))
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer elseType branches) := by
              simp_wf
              omega
            omega)]
          congr 1
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.offer elseType branches) := by
              simp_wf
              omega
            omega
          induction branches with
          | nil => rfl
          | cons branch rest restIH =>
              simp only [List.any_cons]
              rw [ih branch.2 (hEvery branch (by simp))]
              rw [restIH (by
                have : sizeOf (PactType.offer elseType rest) <
                    sizeOf (PactType.offer elseType (branch :: rest)) := by
                  simp_wf
                  omega
                omega) (by
                intro other hOther
                exact hEvery other (by simp [hOther]))]

/-- Once fuel covers the finite syntax tree, the bounded completion analysis
agrees with the public structural predicate. -/
private theorem typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock :
    ∀ fuel processType, sizeOf processType < fuel →
      typeCanCompleteThisCycleFuel fuel processType =
        processType.CanCompleteBeforeTock := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hSize
      omega
  | succ fuel ih =>
      intro processType hSize
      cases processType with
      | message msg dir =>
          simp [typeCanCompleteThisCycleFuel, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [typeCanCompleteThisCycleFuel, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [typeCanCompleteThisCycleFuel, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [typeCanCompleteThisCycleFuel, PactType.CanCompleteBeforeTock]
      | var name =>
          simp [typeCanCompleteThisCycleFuel, PactType.CanCompleteBeforeTock]
      | recur name body =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          apply ih
          have hProper : sizeOf body <
              sizeOf (PactType.recur name body) := by
            simp_wf
            omega
          omega
      | choice left right =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih left (by
              have : sizeOf left < sizeOf (PactType.choice left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right < sizeOf (PactType.choice left right) := by
                simp_wf; omega
              omega)]
      | fairChoice bid left right =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf; omega
              omega)]
      | seq left right =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih left (by
              have : sizeOf left < sizeOf (PactType.seq left right) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right < sizeOf (PactType.seq left right) := by
                simp_wf; omega
              omega)]
      | par left right interface =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.par left right interface) := by
                simp_wf; omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.par left right interface) := by
                simp_wf; omega
              omega)]
      | xoffer elseType branches =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer elseType branches) := by
              simp_wf; omega
            omega)]
          congr 1
          induction branches with
          | nil => simp [PactType.BranchCanCompleteBeforeTock]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [List.any_cons, PactType.BranchCanCompleteBeforeTock]
              rw [ih branchType (by
                have : sizeOf branchType < sizeOf
                    (PactType.xoffer elseType ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
              rw [restIH (by
                have : sizeOf (PactType.xoffer elseType rest) < sizeOf
                    (PactType.xoffer elseType ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
      | offer elseType branches =>
          simp only [typeCanCompleteThisCycleFuel,
            PactType.CanCompleteBeforeTock]
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer elseType branches) := by
              simp_wf; omega
            omega)]
          congr 1
          induction branches with
          | nil => simp [PactType.BranchCanCompleteBeforeTock]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [List.any_cons, PactType.BranchCanCompleteBeforeTock]
              rw [ih branchType (by
                have : sizeOf branchType < sizeOf
                    (PactType.offer elseType ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]
              rw [restIH (by
                have : sizeOf (PactType.offer elseType rest) < sizeOf
                    (PactType.offer elseType ((action, branchType) :: rest)) := by
                  simp_wf; omega
                omega)]

/- A structurally mandatory clock prevents same-cycle completion. -/
private theorem mustTock_cannotCompleteThisCycleFuel
      (processType : PactType)
      (hTock : processType.MustTockBeforeCompletion) (fuel : Nat) :
      typeCanCompleteThisCycleFuel fuel processType = false := by
    cases fuel with
    | zero => rfl
    | succ fuel =>
        cases processType with
        | message msg dir => simp [PactType.MustTockBeforeCompletion] at hTock
        | progress pid => simp [PactType.MustTockBeforeCompletion] at hTock
        | tock => rfl
        | skip => simp [PactType.MustTockBeforeCompletion] at hTock
        | var name => simp [PactType.MustTockBeforeCompletion] at hTock
        | recur name body =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            exact mustTock_cannotCompleteThisCycleFuel body hTock fuel
        | choice left right =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with ⟨hLeft, hRight⟩
            change (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right) = false
            rw [mustTock_cannotCompleteThisCycleFuel left hLeft fuel,
              mustTock_cannotCompleteThisCycleFuel right hRight fuel]
            simp
        | fairChoice bid left right =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with ⟨hLeft, hRight⟩
            change (typeCanCompleteThisCycleFuel fuel left ||
              typeCanCompleteThisCycleFuel fuel right) = false
            rw [mustTock_cannotCompleteThisCycleFuel left hLeft fuel,
              mustTock_cannotCompleteThisCycleFuel right hRight fuel]
            simp
        | seq left right =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with hLeft | hRight
            · change (typeCanCompleteThisCycleFuel fuel left &&
                typeCanCompleteThisCycleFuel fuel right) = false
              rw [mustTock_cannotCompleteThisCycleFuel left hLeft fuel]
              simp
            · change (typeCanCompleteThisCycleFuel fuel left &&
                typeCanCompleteThisCycleFuel fuel right) = false
              rw [mustTock_cannotCompleteThisCycleFuel right hRight fuel]
              simp
        | par left right interface =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with ⟨hLeft, _⟩
            change (typeCanCompleteThisCycleFuel fuel left &&
              typeCanCompleteThisCycleFuel fuel right) = false
            rw [mustTock_cannotCompleteThisCycleFuel left hLeft fuel]
            simp
        | xoffer elseType branches =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with ⟨hElse, hBranches⟩
            have hNoBranches :
                branches.any (fun branch =>
                  typeCanCompleteThisCycleFuel fuel branch.2) = false := by
              induction branches with
              | nil => rfl
              | cons branch rest ih =>
                  rcases branch with ⟨action, branchType⟩
                  simp only [PactType.BranchesMustTockBeforeCompletion]
                    at hBranches
                  rcases hBranches with ⟨hBranch, hRest⟩
                  change (typeCanCompleteThisCycleFuel fuel branchType ||
                    rest.any (fun branch =>
                      typeCanCompleteThisCycleFuel fuel branch.2)) = false
                  rw [mustTock_cannotCompleteThisCycleFuel branchType
                    hBranch fuel, ih hRest]
                  simp
            change (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2)) = false
            rw [mustTock_cannotCompleteThisCycleFuel elseType hElse fuel,
              hNoBranches]
            simp
        | offer elseType branches =>
            simp only [PactType.MustTockBeforeCompletion] at hTock
            rcases hTock with ⟨hElse, hBranches⟩
            have hNoBranches :
                branches.any (fun branch =>
                  typeCanCompleteThisCycleFuel fuel branch.2) = false := by
              induction branches with
              | nil => rfl
              | cons branch rest ih =>
                  rcases branch with ⟨action, branchType⟩
                  simp only [PactType.BranchesMustTockBeforeCompletion]
                    at hBranches
                  rcases hBranches with ⟨hBranch, hRest⟩
                  change (typeCanCompleteThisCycleFuel fuel branchType ||
                    rest.any (fun branch =>
                      typeCanCompleteThisCycleFuel fuel branch.2)) = false
                  rw [mustTock_cannotCompleteThisCycleFuel branchType
                    hBranch fuel, ih hRest]
                  simp
            change (typeCanCompleteThisCycleFuel fuel elseType ||
              branches.any (fun branch =>
                typeCanCompleteThisCycleFuel fuel branch.2)) = false
            rw [mustTock_cannotCompleteThisCycleFuel elseType hElse fuel,
              hNoBranches]
            simp
termination_by fuel
decreasing_by
  all_goals
    omega

/-- Replacing a variable hidden behind a clock does not change completion
within the current cycle. -/
private theorem guardedOccurrences_replace_canCompleteThisCycleFuel
    (name : String) (replacement processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) (fuel : Nat) :
    typeCanCompleteThisCycleFuel fuel
        (processType.replaceVar name replacement) =
      typeCanCompleteThisCycleFuel fuel processType := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, typeCanCompleteThisCycleFuel]
      | progress pid =>
          simp [PactType.replaceVar, typeCanCompleteThisCycleFuel]
      | tock => simp [PactType.replaceVar, typeCanCompleteThisCycleFuel]
      | skip => simp [PactType.replaceVar, typeCanCompleteThisCycleFuel]
      | var other =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          have hNe : name ≠ other := by
            intro h
            exact hGuarded h.symm
          simp [PactType.replaceVar, hNe]
      | recur other body =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          by_cases hName : other = name
          · have hTarget : name = other := hName.symm
            simp [PactType.replaceVar, hTarget]
          · simp only [hName, ↓reduceIte] at hGuarded
            have hTarget : name ≠ other := by
              intro h
              exact hName h.symm
            simp only [PactType.replaceVar, hTarget,
              typeCanCompleteThisCycleFuel]
            exact guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement body hGuarded fuel
      | choice left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement right hRight fuel]
      | fairChoice bid left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement right hRight fuel]
      | par left right interface =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement right hRight fuel]
      | seq left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
            name replacement left hLeft fuel]
          by_cases hTock : left.MustTockBeforeCompletion
          · rw [mustTock_cannotCompleteThisCycleFuel left hTock fuel]
            simp
          · simp only [hTock, or_false] at hRight
            rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement right hRight fuel]
      | xoffer elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hBranchesEq :
              (PactType.replaceBranches branches name replacement).any
                  (fun branch =>
                    typeCanCompleteThisCycleFuel fuel branch.2) =
                branches.any (fun branch =>
                  typeCanCompleteThisCycleFuel fuel branch.2) := by
            induction branches with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.any_cons]
                rw [guardedOccurrences_replace_canCompleteThisCycleFuel
                    name replacement branchType hBranch fuel,
                  ih hRest]
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement elseType hElse fuel,
            hBranchesEq]
      | offer elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hBranchesEq :
              (PactType.replaceBranches branches name replacement).any
                  (fun branch =>
                    typeCanCompleteThisCycleFuel fuel branch.2) =
                branches.any (fun branch =>
                  typeCanCompleteThisCycleFuel fuel branch.2) := by
            induction branches with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.any_cons]
                rw [guardedOccurrences_replace_canCompleteThisCycleFuel
                    name replacement branchType hBranch fuel,
                  ih hRest]
          simp only [PactType.replaceVar, typeCanCompleteThisCycleFuel]
          rw [guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement elseType hElse fuel,
            hBranchesEq]
termination_by fuel
decreasing_by
  all_goals
    omega

/-- Syntactic future-offer menu, bounded by the depth of the finite type term. -/
def typeFutureOffersFuel : Nat → PactType → Finset BareMessage
  | 0, _ => ∅
  | fuel + 1, processType =>
      match processType with
      | .message msg dir => {(msg, dir)}
      | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => typeFutureOffersFuel fuel body
      | .choice left right | .fairChoice _ left right =>
          typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right
      | .seq left right =>
          let leftOffers := typeFutureOffersFuel fuel left
          if typeCanCompleteThisCycleFuel fuel left then
            leftOffers ∪ typeFutureOffersFuel fuel right
          else leftOffers
      | .par left right interface =>
          hideTypeOffers interface
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
      | .xoffer elseType branches | .offer elseType branches =>
          branches.foldl (fun offers branch =>
            offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
            (typeFutureOffersFuel fuel elseType)

/-- Once fuel covers the finite syntax tree, one more unit cannot expose a new
same-cycle future offer. -/
private theorem typeFutureOffersFuel_succ_stable :
    ∀ fuel processType, sizeOf processType ≤ fuel →
      typeFutureOffersFuel (fuel + 1) processType =
        typeFutureOffersFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hSize
      cases processType <;> simp at hSize
  | succ fuel ih =>
      intro processType hSize
      cases processType with
      | message msg dir => rfl
      | progress pid => rfl
      | tock => rfl
      | skip => rfl
      | var name => rfl
      | recur name body =>
          change typeFutureOffersFuel (fuel + 1) body =
            typeFutureOffersFuel fuel body
          apply ih
          have : sizeOf body < sizeOf (PactType.recur name body) := by
            simp_wf
            omega
          omega
      | choice left right =>
          change (typeFutureOffersFuel (fuel + 1) left ∪
              typeFutureOffersFuel (fuel + 1) right) =
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left < sizeOf (PactType.choice left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right < sizeOf (PactType.choice left right) := by
                simp_wf
                omega
              omega)]
      | fairChoice bid left right =>
          change (typeFutureOffersFuel (fuel + 1) left ∪
              typeFutureOffersFuel (fuel + 1) right) =
            (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.fairChoice bid left right) := by
                simp_wf
                omega
              omega)]
      | seq left right =>
          have hLeft : sizeOf left ≤ fuel := by
            have : sizeOf left < sizeOf (PactType.seq left right) := by
              simp_wf
              omega
            omega
          have hRight : sizeOf right ≤ fuel := by
            have : sizeOf right < sizeOf (PactType.seq left right) := by
              simp_wf
              omega
            omega
          change (if typeCanCompleteThisCycleFuel (fuel + 1) left then
              typeFutureOffersFuel (fuel + 1) left ∪
                typeFutureOffersFuel (fuel + 1) right
            else typeFutureOffersFuel (fuel + 1) left) =
            (if typeCanCompleteThisCycleFuel fuel left then
              typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right
            else typeFutureOffersFuel fuel left)
          rw [typeCanCompleteThisCycleFuel_succ_stable fuel left hLeft,
            ih left hLeft, ih right hRight]
      | par left right interface =>
          change hideTypeOffers interface
              (typeFutureOffersFuel (fuel + 1) left ∪
                typeFutureOffersFuel (fuel + 1) right) =
            hideTypeOffers interface
              (typeFutureOffersFuel fuel left ∪ typeFutureOffersFuel fuel right)
          rw [ih left (by
              have : sizeOf left <
                  sizeOf (PactType.par left right interface) := by
                simp_wf
                omega
              omega),
            ih right (by
              have : sizeOf right <
                  sizeOf (PactType.par left right interface) := by
                simp_wf
                omega
              omega)]
      | xoffer elseType branches =>
          change branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪
                typeFutureOffersFuel (fuel + 1) branch.2)
              (typeFutureOffersFuel (fuel + 1) elseType) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
              (typeFutureOffersFuel fuel elseType)
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.xoffer elseType branches) := by
              simp_wf
              omega
            omega)]
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.xoffer elseType branches) := by
              simp_wf
              omega
            omega
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2) initial =
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel fuel branch.2) initial := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro initial hSubset
                simp only [List.foldl_cons]
                rw [ih branch.2 (hEvery branch (hSubset branch (by simp)))]
                apply tailIH
                intro other hOther
                exact hSubset other (by simp [hOther])
          exact hFold branches _ (by simp)
      | offer elseType branches =>
          change branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪
                typeFutureOffersFuel (fuel + 1) branch.2)
              (typeFutureOffersFuel (fuel + 1) elseType) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
              (typeFutureOffersFuel fuel elseType)
          rw [ih elseType (by
            have : sizeOf elseType <
                sizeOf (PactType.offer elseType branches) := by
              simp_wf
              omega
            omega)]
          have hEvery : ∀ branch ∈ branches, sizeOf branch.2 ≤ fuel := by
            intro branch hBranch
            have hPair := List.sizeOf_lt_of_mem hBranch
            have hComponent : sizeOf branch.2 < sizeOf branch := by
              rcases branch
              simp_wf
              omega
            have hList : sizeOf branches <
                sizeOf (PactType.offer elseType branches) := by
              simp_wf
              omega
            omega
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel (fuel + 1) branch.2) initial =
              rest.foldl (fun offers branch =>
                offers ∪ {branch.1} ∪
                  typeFutureOffersFuel fuel branch.2) initial := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro initial hSubset
                simp only [List.foldl_cons]
                rw [ih branch.2 (hEvery branch (hSubset branch (by simp)))]
                apply tailIH
                intro other hOther
                exact hSubset other (by simp [hOther])
          exact hFold branches _ (by simp)

private theorem typeFutureOffersFuel_add_stable
    (processType : PactType) (fuel extra : Nat)
    (hFuel : sizeOf processType ≤ fuel) :
    typeFutureOffersFuel (fuel + extra) processType =
      typeFutureOffersFuel fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        typeFutureOffersFuel_succ_stable (fuel + extra) processType (by omega),
        ih]

/-- A clock-guarded substitution cannot expose a new offer before the next
clock. -/
private theorem guardedOccurrences_replace_typeFutureOffersFuel
    (name : String) (replacement processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) (fuel : Nat) :
    typeFutureOffersFuel fuel (processType.replaceVar name replacement) =
      typeFutureOffersFuel fuel processType := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases processType with
      | message msg dir => simp [PactType.replaceVar, typeFutureOffersFuel]
      | progress pid => simp [PactType.replaceVar, typeFutureOffersFuel]
      | tock => simp [PactType.replaceVar, typeFutureOffersFuel]
      | skip => simp [PactType.replaceVar, typeFutureOffersFuel]
      | var other =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          have hNe : name ≠ other := by
            intro h
            exact hGuarded h.symm
          simp [PactType.replaceVar, typeFutureOffersFuel, hNe]
      | recur other body =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          by_cases hName : other = name
          · have hTarget : name = other := hName.symm
            simp [PactType.replaceVar, typeFutureOffersFuel, hTarget]
          · simp only [hName, ↓reduceIte] at hGuarded
            have hTarget : name ≠ other := by
              intro h
              exact hName h.symm
            simp only [PactType.replaceVar, typeFutureOffersFuel, hTarget]
            exact guardedOccurrences_replace_typeFutureOffersFuel
              name replacement body hGuarded fuel
      | choice left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | fairChoice bid left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | par left right interface =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | seq left right =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hLeft, hRight⟩
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement left hLeft fuel,
            guardedOccurrences_replace_canCompleteThisCycleFuel
              name replacement left hLeft fuel]
          by_cases hTock : left.MustTockBeforeCompletion
          · rw [mustTock_cannotCompleteThisCycleFuel left hTock fuel]
            simp
          · simp only [hTock, or_false] at hRight
            rw [guardedOccurrences_replace_typeFutureOffersFuel
              name replacement right hRight fuel]
      | xoffer elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hFold : ∀ initial,
              (PactType.replaceBranches branches name replacement).foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial =
                branches.foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial := by
            intro initial
            induction branches generalizing initial with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.foldl_cons]
                rw [guardedOccurrences_replace_typeFutureOffersFuel
                  name replacement branchType hBranch fuel]
                exact ih hRest _
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
            name replacement elseType hElse fuel]
          exact hFold _
      | offer elseType branches =>
          simp only [PactType.GuardedOccurrences] at hGuarded
          rcases hGuarded with ⟨hElse, hBranches⟩
          have hFold : ∀ initial,
              (PactType.replaceBranches branches name replacement).foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial =
                branches.foldl
                  (fun offers branch => offers ∪ {branch.1} ∪
                    typeFutureOffersFuel fuel branch.2) initial := by
            intro initial
            induction branches generalizing initial with
            | nil => simp [PactType.replaceBranches]
            | cons branch rest ih =>
                rcases branch with ⟨action, branchType⟩
                simp only [PactType.GuardedBranchOccurrences] at hBranches
                rcases hBranches with ⟨hBranch, hRest⟩
                simp only [PactType.replaceBranches, List.foldl_cons]
                rw [guardedOccurrences_replace_typeFutureOffersFuel
                  name replacement branchType hBranch fuel]
                exact ih hRest _
          simp only [PactType.replaceVar, typeFutureOffersFuel]
          rw [guardedOccurrences_replace_typeFutureOffersFuel
            name replacement elseType hElse fuel]
          exact hFold _
termination_by fuel
decreasing_by
  all_goals
    omega

/-- All message actions that may still be offered before the next clock. -/
def typeFutureOffers (processType : PactType) : Finset BareMessage :=
  typeFutureOffersFuel (sizeOf processType + 1) processType

/-- Any fuel budget covering the syntax computes the same public future menu. -/
theorem typeFutureOffersFuel_eq_typeFutureOffers
    (processType : PactType) (fuel : Nat)
    (hFuel : sizeOf processType + 1 ≤ fuel) :
    typeFutureOffersFuel fuel processType = typeFutureOffers processType := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  unfold typeFutureOffers
  exact typeFutureOffersFuel_add_stable processType
    (sizeOf processType + 1) extra (by omega)

mutual
  /-- `CanCompleteBeforeTock`, but every occurrence of `.var name` contributes
  `value` instead of the unconditional `false` used by `CanCompleteBeforeTock`
  itself.  Respects the same capture-avoiding shadowing as `replaceVar`: a
  nested `.recur name _` binder stops the substitution view of its own body,
  matching `replaceVar`'s `if var = other then .recur other body else ...`
  clause. -/
  def PactType.canCompleteBeforeTockSubst
      (name : String) (value : Bool) : PactType → Bool
    | .message _ _ | .progress _ | .skip => true
    | .tock => false
    | .var other => if name = other then value else false
    | .recur other body =>
        if name = other then PactType.CanCompleteBeforeTock body
        else canCompleteBeforeTockSubst name value body
    | .choice left right | .fairChoice _ left right =>
        canCompleteBeforeTockSubst name value left ||
          canCompleteBeforeTockSubst name value right
    | .seq left right | .par left right _ =>
        canCompleteBeforeTockSubst name value left &&
          canCompleteBeforeTockSubst name value right
    | .xoffer elseType branches | .offer elseType branches =>
        canCompleteBeforeTockSubst name value elseType ||
          branchCanCompleteBeforeTockSubst name value branches
  termination_by processType => sizeOf processType

  def PactType.branchCanCompleteBeforeTockSubst
      (name : String) (value : Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        canCompleteBeforeTockSubst name value processType ||
          branchCanCompleteBeforeTockSubst name value rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  /-- Optimistic completion under a finite-control interpretation of the free
  recursion variables.  Entering a binder shadows its own name with the
  ordinary (unfolded-call-free) value `false`; an installed backedge is
  represented separately by updating that name to the binder's completion
  value when its body is analysed. -/
  def PactType.completionEval (valuation : String → Bool) : PactType → Bool
    | .message _ _ | .progress _ | .skip => true
    | .tock => false
    | .var name => valuation name
    | .recur name body => completionEval (Function.update valuation name false) body
    | .choice left right | .fairChoice _ left right =>
        completionEval valuation left || completionEval valuation right
    | .seq left right | .par left right _ =>
        completionEval valuation left && completionEval valuation right
    | .xoffer elseType branches | .offer elseType branches =>
        completionEval valuation elseType ||
          branchCompletionEval valuation branches
  termination_by processType => sizeOf processType

  def PactType.branchCompletionEval (valuation : String → Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        completionEval valuation processType || branchCompletionEval valuation rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Completion evaluation depends only on the values of variables declared
free in the supplied binding context. -/
theorem PactType.completionEval_congr_of_allVariablesBound
    (bound : List String) (left right : String → Bool)
    (hAgree : ∀ name ∈ bound, left name = right name) :
    ∀ processType : PactType,
      PactType.AllVariablesBound bound processType →
        completionEval left processType = completionEval right processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound left right with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
            branchCompletionEval left branches =
              branchCompletionEval right branches := by
        intro branches hBranchesSize hBound
        induction branches with
        | nil => simp [branchCompletionEval]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hBound
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
            simp only [branchCompletionEval]
            rw [ih (sizeOf branchType) hBranchSize bound left right hAgree
                branchType rfl hBound.1,
              restIH hRestSize hBound.2]
      cases processType with
      | message msg dir => simp [completionEval]
      | progress pid => simp [completionEval]
      | tock => simp [completionEval]
      | skip => simp [completionEval]
      | var name =>
          intro hBound
          simpa [completionEval] using
            hAgree name (by simpa [PactType.AllVariablesBound] using hBound)
      | recur name body =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval]
          exact ih (sizeOf body) hBodySize (name :: bound)
            (Function.update left name false)
            (Function.update right name false)
            (by
              intro other hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with rfl | hMem
              · simp
              · by_cases hEq : other = name
                · subst other
                  simp
                · simpa [Function.update, hEq] using hAgree other hMem)
            body rfl hBound
      | choice leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | fairChoice bid leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | seq leftType rightType =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | par leftType rightType interface =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftSize : sizeOf leftType < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf rightType < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf leftType) hLeftSize bound left right hAgree leftType rfl
              hBound.1,
            ih (sizeOf rightType) hRightSize bound left right hAgree rightType
              rfl hBound.2]
      | xoffer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf elseType) hElseSize bound left right hAgree elseType rfl
              hBound.1,
            hBranches branches hBranchesSize hBound.2]
      | offer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval,
            ih (sizeOf elseType) hElseSize bound left right hAgree elseType rfl
              hBound.1,
            hBranches branches hBranchesSize hBound.2]

/-- Hygienic substitution is interpreted by updating the completion
valuation.  Every name outside `active` is already interpreted as `false`, so
a nested binder fresh for `active` does not change the replacement's value;
the replacement itself need not be closed. -/
theorem PactType.completionEval_replaceVar_of_hygienic
    (active : List String) (valuation : String → Bool) (name : String)
    (replacement : PactType)
    (hSupported : ∀ other, other ∉ active → valuation other = false) :
    ∀ processType : PactType,
      processType.BinderFreshFor (name :: active) →
        completionEval valuation (processType.replaceVar name replacement) =
          completionEval
            (Function.update valuation name
              (completionEval valuation replacement)) processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active valuation with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: active) branches →
          branchCompletionEval valuation
              (PactType.replaceBranches branches name replacement) =
            branchCompletionEval
              (Function.update valuation name
                (completionEval valuation replacement)) branches := by
        intro branches hBranchesSize hHygienic
        induction branches with
        | nil => simp [PactType.replaceBranches, branchCompletionEval]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches] at hHygienic
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
            simp only [PactType.replaceBranches, branchCompletionEval]
            rw [ih (sizeOf branchType) hBranchSize active valuation hSupported
                branchType rfl hHygienic.1,
              restIH hRestSize hHygienic.2]
      cases processType with
      | message msg dir => simp [PactType.replaceVar, completionEval]
      | progress pid => simp [PactType.replaceVar, completionEval]
      | tock => simp [PactType.replaceVar, completionEval]
      | skip => simp [PactType.replaceVar, completionEval]
      | var other =>
          intro _
          by_cases hEq : name = other
          · subst other
            simp [PactType.replaceVar, completionEval]
          · simp [PactType.replaceVar, completionEval, hEq, Ne.symm hEq]
      | recur other body =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hOtherName : other ≠ name := by
            intro hEq
            subst other
            exact hHygienic.1 (by simp)
          have hOtherActive : other ∉ active := by
            intro hMem
            exact hHygienic.1 (by simp [hMem])
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          have hSupported' : ∀ x, x ∉ active →
              Function.update valuation other false x = false := by
            intro x hx
            by_cases hEq : x = other
            · subst x
              simp
            · simpa [Function.update, hEq] using hSupported x hx
          have hReplacementEval :
              completionEval (Function.update valuation other false)
                  replacement = completionEval valuation replacement := by
            have hValuation : Function.update valuation other false =
                valuation := by
              funext x
              by_cases hEq : x = other
              · subst x
                simp [hSupported other hOtherActive]
              · simp [Function.update, hEq]
            rw [hValuation]
          simp only [PactType.replaceVar, if_neg hOtherName.symm,
            completionEval]
          rw [ih (sizeOf body) hBodySize active
              (Function.update valuation other false) hSupported' body rfl
                hHygienic.2,
            hReplacementEval]
          exact congrArg (fun f => completionEval f body)
            (Function.update_comm hOtherName.symm
              (completionEval valuation replacement) false valuation).symm
      | choice left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | fairChoice bid left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | seq left right =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | par left right interface =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf left) hLeftSize active valuation hSupported
              left rfl hHygienic.1,
            ih (sizeOf right) hRightSize active valuation hSupported
              right rfl hHygienic.2]
      | xoffer elseType branches =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf elseType) hElseSize active valuation hSupported
              elseType rfl hHygienic.1,
            hBranches branches hBranchesSize hHygienic.2]
      | offer elseType branches =>
          intro hHygienic
          simp only [PactType.BinderFreshFor] at hHygienic
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.replaceVar, completionEval,
            ih (sizeOf elseType) hElseSize active valuation hSupported
              elseType rfl hHygienic.1,
            hBranches branches hBranchesSize hHygienic.2]

/-- Substituting an `active`-closed replacement for `name` closes that name in
the result. -/
theorem PactType.replaceVar_allVariablesBound
    (active : List String) (name : String) (replacement : PactType)
    (hReplacement : replacement.AllVariablesBound active) :
    ∀ processType : PactType,
      processType.AllVariablesBound (name :: active) →
        (processType.replaceVar name replacement).AllVariablesBound active := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound (name :: active) branches →
            PactType.AllBranchVariablesBound active
              (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hBound
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound,
              PactType.replaceBranches] at hBound ⊢
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
            exact ⟨ih (sizeOf branchType) hBranchSize active hReplacement
                branchType rfl hBound.1, restIH hRestSize hBound.2⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | progress pid => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | tock => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | skip => simp [PactType.replaceVar, PactType.AllVariablesBound]
      | var other =>
          intro hBound
          by_cases hEq : name = other
          · subst other
            simpa [PactType.replaceVar] using hReplacement
          · have hMem : other ∈ active := by
              simp only [PactType.AllVariablesBound, List.mem_cons] at hBound
              exact hBound.resolve_left (Ne.symm hEq)
            simpa [PactType.replaceVar, PactType.AllVariablesBound, hEq,
              Ne.symm hEq] using hMem
      | recur other body =>
          intro hBound
          simp only [PactType.AllVariablesBound] at hBound ⊢
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hEq : name = other
          · subst other
            simp [PactType.replaceVar, PactType.AllVariablesBound]
            exact PactType.allVariablesBound_mono
              (smaller := name :: name :: active)
              (larger := name :: active)
              (by
                intro x hx
                simp only [List.mem_cons] at hx ⊢
                rcases hx with rfl | rfl | hx
                · exact Or.inl rfl
                · exact Or.inl rfl
                · exact Or.inr hx)
              body hBound
          · simp only [PactType.replaceVar, if_neg hEq,
              PactType.AllVariablesBound]
            have hReordered :
                body.AllVariablesBound (name :: other :: active) := by
              exact PactType.allVariablesBound_mono
                (smaller := other :: name :: active)
                (larger := name :: other :: active)
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx ⊢
                  rcases hx with rfl | rfl | hx
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr hx))
                body hBound
            have hReplacement' :
                replacement.AllVariablesBound (other :: active) :=
              PactType.allVariablesBound_mono
                (by intro x hx; exact List.mem_cons_of_mem other hx)
                replacement hReplacement
            exact ih (sizeOf body) hBodySize (other :: active) hReplacement'
              body rfl hReordered
      | choice left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | fairChoice bid left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | seq left right =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | par left right interface =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar]
            at hBound ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hBound.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hBound.2⟩
      | xoffer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar,
            PactType.replaceBranches] at hBound ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hBound.1, hBranches branches hBranchesSize hBound.2⟩
      | offer elseType branches =>
          intro hBound
          simp only [PactType.AllVariablesBound, PactType.replaceVar,
            PactType.replaceBranches] at hBound ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hBound.1, hBranches branches hBranchesSize hBound.2⟩

/-- Capture-freshness is preserved by substituting a replacement which is
fresh for the active names. -/
theorem PactType.replaceVar_binderFreshFor
    (active : List String) (name : String) (replacement : PactType)
    (hReplacement : replacement.BinderFreshFor active) :
    ∀ processType : PactType,
      processType.BinderFreshFor (name :: active) →
        (processType.replaceVar name replacement).BinderFreshFor active := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType active with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BinderFreshForBranches (name :: active) branches →
            PactType.BinderFreshForBranches active
              (PactType.replaceBranches branches name replacement) := by
        intro branches hBranchesSize hFresh
        induction branches with
        | nil => simp [PactType.replaceBranches,
            PactType.BinderFreshForBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderFreshForBranches,
              PactType.replaceBranches] at hFresh ⊢
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
            exact ⟨ih (sizeOf branchType) hBranchSize active hReplacement
                branchType rfl hFresh.1, restIH hRestSize hFresh.2⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | progress pid => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | tock => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | skip => simp [PactType.replaceVar, PactType.BinderFreshFor]
      | var other =>
          intro _
          by_cases hEq : name = other
          · subst other
            simpa [PactType.replaceVar] using hReplacement
          · simp [PactType.replaceVar, PactType.BinderFreshFor, hEq,
              Ne.symm hEq]
      | recur other body =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hOtherName : other ≠ name := by
            intro hEq
            subst other
            exact hFresh.1 (by simp)
          have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, if_neg hOtherName.symm,
            PactType.BinderFreshFor]
          exact ⟨fun hMem => hFresh.1 (by simp [hMem]),
            ih (sizeOf body) hBodySize active hReplacement body rfl hFresh.2⟩
      | choice left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | fairChoice bid left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | seq left right =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | par left right interface =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf left) hLeftSize active hReplacement left rfl hFresh.1,
            ih (sizeOf right) hRightSize active hReplacement right rfl hFresh.2⟩
      | xoffer elseType branches =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar] at hFresh ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hFresh.1, hBranches branches hBranchesSize hFresh.2⟩
      | offer elseType branches =>
          intro hFresh
          simp only [PactType.BinderFreshFor, PactType.replaceVar,
            PactType.replaceBranches] at hFresh ⊢
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          exact ⟨ih (sizeOf elseType) hElseSize active hReplacement elseType
              rfl hFresh.1, hBranches branches hBranchesSize hFresh.2⟩

mutual
  /-- `typeFutureOffers`, parameterized by the interpretation of one free
  variable. A matching `.var name` contributes `replacementFuture`, while a
  sequence consults the matching parametric completion analysis. This is the
  syntax-side invariant used after an enclosing recursion binder installs its
  backedges. -/
  def PactType.futureOffersSubst
      (name : String) (replacementCompleting : Bool)
      (replacementFuture : Finset BareMessage) : PactType →
        Finset BareMessage
    | .message msg dir => {(msg, dir)}
    | .progress _ | .tock | .skip => ∅
    | .var other => if name = other then replacementFuture else ∅
    | .recur other body =>
        if name = other then typeFutureOffers body
        else futureOffersSubst name replacementCompleting replacementFuture body
    | .choice left right | .fairChoice _ left right =>
        futureOffersSubst name replacementCompleting replacementFuture left ∪
          futureOffersSubst name replacementCompleting replacementFuture right
    | .seq left right =>
        let leftFuture :=
          futureOffersSubst name replacementCompleting replacementFuture left
        if canCompleteBeforeTockSubst name replacementCompleting left then
          leftFuture ∪
            futureOffersSubst name replacementCompleting replacementFuture right
        else leftFuture
    | .par left right interface =>
        hideTypeOffers interface
          (futureOffersSubst name replacementCompleting replacementFuture left ∪
            futureOffersSubst name replacementCompleting replacementFuture right)
    | .xoffer elseType branches | .offer elseType branches =>
        futureOffersSubst name replacementCompleting replacementFuture elseType ∪
          branchFutureOffersSubst name replacementCompleting replacementFuture
            branches
  termination_by processType => sizeOf processType

  /-- Branch-list component of `futureOffersSubst`: every branch contributes
  its head action and the parametric future of its continuation. -/
  def PactType.branchFutureOffersSubst
      (name : String) (replacementCompleting : Bool)
      (replacementFuture : Finset BareMessage) :
      List (BareMessage × PactType) → Finset BareMessage
    | [] => ∅
    | (action, processType) :: rest =>
        {action} ∪
          futureOffersSubst name replacementCompleting replacementFuture
            processType ∪
          branchFutureOffersSubst name replacementCompleting replacementFuture
            rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Unconditional substitution equation for `CanCompleteBeforeTock`: no
`GuardedOccurrences` hypothesis is needed, because `CanCompleteBeforeTock`
never unfolds a `.recur` node more than once (it reads `body`'s own
completion directly, per its `.recur _ body => CanCompleteBeforeTock body`
clause) and `replaceVar` only ever substitutes literal `.var name` leaves. -/
theorem PactType.replaceVar_canCompleteBeforeTock
    (name : String) (replacement processType : PactType) :
    (processType.replaceVar name replacement).CanCompleteBeforeTock =
      canCompleteBeforeTockSubst name replacement.CanCompleteBeforeTock
        processType := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | progress pid =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | tock =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | skip =>
          simp [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst]
      | var other =>
          by_cases hName : name = other
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst]
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, Ne.symm hName]
      | recur other body =>
          by_cases hName : name = other
          · simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp [PactType.replaceVar, hName, PactType.CanCompleteBeforeTock,
              canCompleteBeforeTockSubst, ih (sizeOf body) hBodySize body rfl]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : PactType.BranchCanCompleteBeforeTock
              (PactType.replaceBranches branches name replacement) =
              branchCanCompleteBeforeTockSubst name
                replacement.CanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil => simp [PactType.replaceBranches,
                PactType.BranchCanCompleteBeforeTock,
                branchCanCompleteBeforeTockSubst]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hMem := List.sizeOf_lt_of_mem
                    (List.mem_cons_self (a := branch) (l := rest))
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.replaceBranches PactType.BranchCanCompleteBeforeTock
                  branchCanCompleteBeforeTockSubst
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf elseType) hElseSize
              elseType rfl, hBranches]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : PactType.BranchCanCompleteBeforeTock
              (PactType.replaceBranches branches name replacement) =
              branchCanCompleteBeforeTockSubst name
                replacement.CanCompleteBeforeTock branches := by
            clear hElseSize hSize
            induction branches with
            | nil => simp [PactType.replaceBranches,
                PactType.BranchCanCompleteBeforeTock,
                branchCanCompleteBeforeTockSubst]
            | cons branch rest ihRest =>
                have hBranchSize : sizeOf branch.2 < n := by
                  have hMem := List.sizeOf_lt_of_mem
                    (List.mem_cons_self (a := branch) (l := rest))
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                have hRestSize : sizeOf rest < n := by
                  have hHead : sizeOf rest < sizeOf (branch :: rest) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.replaceBranches PactType.BranchCanCompleteBeforeTock
                  branchCanCompleteBeforeTockSubst
                rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
                  ihRest hRestSize]
          simp only [PactType.replaceVar, PactType.CanCompleteBeforeTock,
            canCompleteBeforeTockSubst, ih (sizeOf elseType) hElseSize
              elseType rfl, hBranches]

/-- Substituting any value at `.var name` can only make same-cycle completion
easier, since `CanCompleteBeforeTock` scores a bare variable as `false` and
both `||` and `&&` are monotone.  This is the direction needed to place a
fragment's own `completing` states into the substituted completion set. -/
theorem PactType.canCompleteBeforeTock_le_subst
    (name : String) (value : Bool) (processType : PactType)
    (hComplete : processType.CanCompleteBeforeTock = true) :
    canCompleteBeforeTockSubst name value processType = true := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir => simp [canCompleteBeforeTockSubst]
      | progress pid => simp [canCompleteBeforeTockSubst]
      | skip => simp [canCompleteBeforeTockSubst]
      | tock => simp [PactType.CanCompleteBeforeTock] at hComplete
      | var other => simp [PactType.CanCompleteBeforeTock] at hComplete
      | recur other body =>
          by_cases hName : name = other
          · subst hName
            simp only [canCompleteBeforeTockSubst, if_pos rfl]
            simpa [PactType.CanCompleteBeforeTock] using hComplete
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp only [canCompleteBeforeTockSubst, hName, if_false]
            exact ih (sizeOf body) hBodySize body
              (by simpa [PactType.CanCompleteBeforeTock] using hComplete) rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left hLeft rfl)
          · exact Or.inr (ih (sizeOf right) hRightSize right hRight rfl)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.and_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.and_eq_true]
          exact ⟨ih (sizeOf left) hLeftSize left hComplete.1 rfl,
            ih (sizeOf right) hRightSize right hComplete.2 rfl⟩
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.BranchCanCompleteBeforeTock rest = true →
              branchCanCompleteBeforeTockSubst name value rest = true := by
            intro rest
            induction rest with
            | nil => intro _ hNil
                     simp [PactType.BranchCanCompleteBeforeTock] at hNil
            | cons branch tail ihTail =>
                intro hRestSize hCons
                have hBranchSize : sizeOf branch.2 < n := by
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                have hTailSize : sizeOf tail < n := by
                  have hHead : sizeOf tail < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.BranchCanCompleteBeforeTock at hCons
                unfold branchCanCompleteBeforeTockSubst
                simp only [Bool.or_eq_true] at hCons ⊢
                rcases hCons with hHead | hTail
                · exact Or.inl (ih (sizeOf branch.2) hBranchSize branch.2
                    hHead rfl)
                · exact Or.inr (ihTail hTailSize hTail)
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hElse | hBranch
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType hElse rfl)
          · exact Or.inr (hBranches branches hBranchesSize hBranch)
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranches : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.BranchCanCompleteBeforeTock rest = true →
              branchCanCompleteBeforeTockSubst name value rest = true := by
            intro rest
            induction rest with
            | nil => intro _ hNil
                     simp [PactType.BranchCanCompleteBeforeTock] at hNil
            | cons branch tail ihTail =>
                intro hRestSize hCons
                have hBranchSize : sizeOf branch.2 < n := by
                  have hPair : sizeOf branch.2 < sizeOf branch := by
                    obtain ⟨action, processType⟩ := branch
                    simp_wf
                    omega
                  have hHead : sizeOf branch < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                have hTailSize : sizeOf tail < n := by
                  have hHead : sizeOf tail < sizeOf (branch :: tail) := by
                    simp_wf
                    omega
                  omega
                unfold PactType.BranchCanCompleteBeforeTock at hCons
                unfold branchCanCompleteBeforeTockSubst
                simp only [Bool.or_eq_true] at hCons ⊢
                rcases hCons with hHead | hTail
                · exact Or.inl (ih (sizeOf branch.2) hBranchSize branch.2
                    hHead rfl)
                · exact Or.inr (ihTail hTailSize hTail)
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.CanCompleteBeforeTock, Bool.or_eq_true]
            at hComplete
          simp only [canCompleteBeforeTockSubst, Bool.or_eq_true]
          rcases hComplete with hElse | hBranch
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType hElse rfl)
          · exact Or.inr (hBranches branches hBranchesSize hBranch)

/- Interpreting the distinguished variable as non-completing is exactly the
ordinary completion analysis, which already assigns `false` to every bare
variable.  The branch-list statement is carried locally because exclusive and
conjunctive offers fold the same Boolean disjunction over their branches. -/
theorem PactType.canCompleteBeforeTockSubst_false (name : String) :
    ∀ processType,
      canCompleteBeforeTockSubst name false processType =
        processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCanCompleteBeforeTockSubst name false branches =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            simp [branchCanCompleteBeforeTockSubst,
              PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            have hBranchSize : sizeOf branch.2 < n := by
              have hPair : sizeOf branch.2 < sizeOf branch := by
                obtain ⟨action, branchType⟩ := branch
                simp_wf
                omega
              have hHead : sizeOf branch < sizeOf (branch :: rest) := by
                simp_wf
                omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest < sizeOf (branch :: rest) := by
                simp_wf
                omega
              omega
            unfold branchCanCompleteBeforeTockSubst
              PactType.BranchCanCompleteBeforeTock
            rw [ih (sizeOf branch.2) hBranchSize branch.2 rfl,
              restIH hRestSize]
      cases processType with
      | message msg dir =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | var other => simp [canCompleteBeforeTockSubst,
          PactType.CanCompleteBeforeTock]
      | recur other body =>
          by_cases hName : name = other
          · simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
              hName, ih (sizeOf body) hBodySize body rfl]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]
            simp_wf
            omega
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]

/-- The ordinary syntax predicate is `completionEval` in the everywhere-false
variable environment. -/
theorem PactType.completionEval_eq_canCompleteBeforeTock_of_all_false
    (valuation : String → Bool) : ∀ processType,
    (∀ name, valuation name = false) →
      completionEval valuation processType = processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType valuation with
  | _ n ih =>
      intro hFalse
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval valuation branches =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval,
            PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
            simp only [branchCompletionEval,
              PactType.BranchCanCompleteBeforeTock]
            rw [ih (sizeOf branchType) hBranchSize valuation branchType rfl hFalse,
              restIH hRestSize]
      cases processType with
      | message msg dir =>
          simp [completionEval, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [completionEval, PactType.CanCompleteBeforeTock]
      | tock => simp [completionEval, PactType.CanCompleteBeforeTock]
      | skip => simp [completionEval, PactType.CanCompleteBeforeTock]
      | var name => simp [completionEval, PactType.CanCompleteBeforeTock, hFalse]
      | recur name body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          rw [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf body) hBodySize (Function.update valuation name false)
              body rfl]
          intro other
          by_cases hEq : other = name
          · subst other
            simp
          · simp [Function.update, hEq, hFalse]
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize valuation left rfl hFalse,
            ih (sizeOf right) hRightSize valuation right rfl hFalse]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFalse,
            hBranches branches hBranchesSize]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [completionEval, PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize valuation elseType rfl hFalse,
            hBranches branches hBranchesSize]

/-- The one-variable completion fold is the singleton specialization of the
finite-control valuation semantics.  This is the bridge used when the old
scalar recursion lemmas are lifted to the binder-context induction. -/
theorem PactType.completionEval_singleton_eq_canCompleteBeforeTockSubst
    (name : String) (value : Bool) : ∀ processType : PactType,
    completionEval (Function.update (fun _ => false) name value) processType =
      canCompleteBeforeTockSubst name value processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      let valuation : String → Bool :=
        Function.update (fun _ => false) name value
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval valuation branches =
            branchCanCompleteBeforeTockSubst name value branches := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval,
            branchCanCompleteBeforeTockSubst]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by
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
            simp only [branchCompletionEval,
              branchCanCompleteBeforeTockSubst]
            rw [show completionEval valuation branchType =
                canCompleteBeforeTockSubst name value branchType by
                  simpa [valuation] using
                    ih (sizeOf branchType) hBranchSize branchType rfl,
              restIH hRestSize]
      cases processType with
      | message msg dir =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | progress pid =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | tock =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | skip =>
          simp [valuation, completionEval, canCompleteBeforeTockSubst]
      | var other =>
          by_cases hName : other = name
          · subst other
            simp [valuation, completionEval, canCompleteBeforeTockSubst]
          · simp [valuation, completionEval, canCompleteBeforeTockSubst,
              hName, Ne.symm hName]
      | recur other body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          by_cases hName : name = other
          · subst other
            rw [completionEval, canCompleteBeforeTockSubst]
            simp only [if_pos rfl]
            apply completionEval_eq_canCompleteBeforeTock_of_all_false
            intro variableName
            by_cases hEq : variableName = name
            · subst variableName
              simp [valuation]
            · simp [valuation, Function.update, hEq]
          · rw [completionEval, canCompleteBeforeTockSubst, if_neg hName]
            have hValuationEq : Function.update valuation other false =
                valuation := by
              funext variableName
              by_cases hOther : variableName = other
              · subst variableName
                simp [valuation, Function.update, hName, Ne.symm hName]
              · simp [Function.update, hOther]
            rw [hValuationEq]
            simpa [valuation] using
              ih (sizeOf body) hBodySize body rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          simp [valuation, completionEval, canCompleteBeforeTockSubst,
            ih (sizeOf elseType) hElseSize elseType rfl,
            hBranches branches hBranchesSize]

/-- `completionEval` is monotone in the Boolean interpretation of free
variables.  Binders preserve monotonicity by assigning `false` to the bound
name in both environments. -/
theorem PactType.completionEval_mono
    (source target : String → Bool)
    (hLe : ∀ name, source name = true → target name = true) :
    ∀ processType,
      completionEval source processType = true →
        completionEval target processType = true := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType source target with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchCompletionEval source branches = true →
            branchCompletionEval target branches = true := by
        intro branches hBranchesSize
        induction branches with
        | nil => simp [branchCompletionEval]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
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
            simp only [branchCompletionEval, Bool.or_eq_true]
            intro h
            rcases h with h | h
            · exact Or.inl (ih (sizeOf branchType) hBranchSize source target
                hLe branchType rfl h)
            · exact Or.inr (restIH hRestSize h)
      cases processType with
      | message msg dir => simp [completionEval]
      | progress pid => simp [completionEval]
      | tock => simp [completionEval]
      | skip => simp [completionEval]
      | var name =>
          simpa [completionEval] using hLe name
      | recur name body =>
          have hBodySize : sizeOf body < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [completionEval]
          apply ih (sizeOf body) hBodySize
              (Function.update source name false)
              (Function.update target name false)
          · intro other hTrue
            by_cases hEq : other = name
            · subst other
              simp at hTrue
            · have hSource : source other = true := by
                simpa [Function.update, hEq] using hTrue
              simpa [Function.update, hEq] using hLe other hSource
          · rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf left) hLeftSize source target hLe left
                rfl h)
          · exact Or.inr (ih (sizeOf right) hRightSize source target hLe right
                rfl h)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf left) hLeftSize source target hLe left
                rfl h)
          · exact Or.inr (ih (sizeOf right) hRightSize source target hLe right
                rfl h)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.and_eq_true]
          rintro ⟨hLeft, hRight⟩
          exact ⟨ih (sizeOf left) hLeftSize source target hLe left rfl hLeft,
            ih (sizeOf right) hRightSize source target hLe right rfl hRight⟩
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.and_eq_true]
          rintro ⟨hLeft, hRight⟩
          exact ⟨ih (sizeOf left) hLeftSize source target hLe left rfl hLeft,
            ih (sizeOf right) hRightSize source target hLe right rfl hRight⟩
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf elseType) hElseSize source target hLe
                elseType rfl h)
          · exact Or.inr (hBranches branches hBranchesSize h)
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [completionEval, Bool.or_eq_true]
          intro h
          rcases h with h | h
          · exact Or.inl (ih (sizeOf elseType) hElseSize source target hLe
                elseType rfl h)
          · exact Or.inr (hBranches branches hBranchesSize h)

/-- The completion value of a recursive body is a Boolean fixed point when
fed back to the corresponding variable. -/
theorem PactType.completionEval_update_self
    (valuation : String → Bool) (name : String) (processType : PactType) :
    completionEval
        (Function.update valuation name
          (completionEval (Function.update valuation name false) processType))
        processType =
      completionEval (Function.update valuation name false) processType := by
  let base := Function.update valuation name false
  cases hValue : completionEval base processType with
  | false => simp [base, hValue]
  | true =>
      have hMono := completionEval_mono base
        (Function.update valuation name true) (processType := processType)
          (by
            intro other hTrue
            by_cases hEq : other = name
            · subst other
              simp
            · simpa [base, Function.update, hEq] using hTrue)
      simpa [base, hValue] using hMono hValue

/-- Interpreting a recursive-call variable by the completion value of its
own body is a Boolean fixed point.  This is the syntax equation matched by a
recursion backedge in the constructor graph. -/
theorem PactType.canCompleteBeforeTockSubst_self
    (name : String) (processType : PactType) :
    canCompleteBeforeTockSubst name processType.CanCompleteBeforeTock
        processType = processType.CanCompleteBeforeTock := by
  cases hComplete : processType.CanCompleteBeforeTock with
  | false =>
      simpa [hComplete] using
        PactType.canCompleteBeforeTockSubst_false name processType
  | true =>
      simpa [hComplete] using
        PactType.canCompleteBeforeTock_le_subst name true processType hComplete

/-- A variable forbidden from tail position cannot affect optimistic
completion.  This is the exact elimination rule used in the recursion proof:
sequence-left, parallel, and conjunctive-offer branch contexts all impose
`TailOccurrences name False`, so their parametric completion reduces to the
ordinary syntax predicate. -/
theorem PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false
    (name : String) (value : Bool) : ∀ processType,
    processType.TailOccurrences name False →
      canCompleteBeforeTockSubst name value processType =
        processType.CanCompleteBeforeTock := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hTail
      cases processType with
      | message msg dir =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | progress pid =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | tock =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | skip =>
          simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
      | var other =>
          have hNe : name ≠ other := by
            intro hEq
            have hImpossible : False := by
              simp only [PactType.TailOccurrences] at hTail
              apply hTail
              exact hEq.symm
            exact hImpossible.elim
          simp [canCompleteBeforeTockSubst, hNe,
            PactType.CanCompleteBeforeTock]
      | recur other body =>
          by_cases hName : name = other
          · subst other
            simp [canCompleteBeforeTockSubst, PactType.CanCompleteBeforeTock]
          · have hBodyTail : body.TailOccurrences name False := by
              simp only [PactType.TailOccurrences] at hTail
              rw [if_neg (Ne.symm hName)] at hTail
              exact hTail
            have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [canCompleteBeforeTockSubst, hName, if_false,
              PactType.CanCompleteBeforeTock]
            exact ih (sizeOf body) hBodySize body rfl hBodyTail
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchEq : PactType.branchCanCompleteBeforeTockSubst name value
                branches = PactType.BranchCanCompleteBeforeTock branches := by
            have hList : ∀ rest : List (BareMessage × PactType),
                sizeOf rest < n →
                PactType.TailBranchOccurrences name False rest →
                PactType.branchCanCompleteBeforeTockSubst name value rest =
                  PactType.BranchCanCompleteBeforeTock rest := by
              intro rest
              induction rest with
              | nil =>
                  intro _ _
                  simp [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock]
              | cons branch tail tailIH =>
                  intro hRestSize hRestTail
                  rcases branch with ⟨action, branchType⟩
                  have hBranchFields :
                      branchType.TailOccurrences name False ∧
                        PactType.TailBranchOccurrences name False tail := by
                    simpa only [PactType.TailBranchOccurrences] using
                      hRestTail
                  have hBranchSize : sizeOf branchType < n := by
                    have hPair : sizeOf branchType <
                        sizeOf (action, branchType) := by
                      simp_wf
                      omega
                    have hHead : sizeOf (action, branchType) <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  have hTailSize : sizeOf tail < n := by
                    have hTail : sizeOf tail <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  simp only [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock,
                    ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1,
                    tailIH hTailSize hBranchFields.2]
            apply hList branches
            · rw [← hSize]; simp_wf; omega
            · exact hFields.2
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranchEq]
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchEq : PactType.branchCanCompleteBeforeTockSubst name value
                branches = PactType.BranchCanCompleteBeforeTock branches := by
            have hList : ∀ rest : List (BareMessage × PactType),
                sizeOf rest < n →
                PactType.TailBranchOccurrences name False rest →
                PactType.branchCanCompleteBeforeTockSubst name value rest =
                  PactType.BranchCanCompleteBeforeTock rest := by
              intro rest
              induction rest with
              | nil =>
                  intro _ _
                  simp [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock]
              | cons branch tail tailIH =>
                  intro hRestSize hRestTail
                  rcases branch with ⟨action, branchType⟩
                  have hBranchFields :
                      branchType.TailOccurrences name False ∧
                        PactType.TailBranchOccurrences name False tail := by
                    simpa only [PactType.TailBranchOccurrences] using
                      hRestTail
                  have hBranchSize : sizeOf branchType < n := by
                    have hPair : sizeOf branchType <
                        sizeOf (action, branchType) := by
                      simp_wf
                      omega
                    have hHead : sizeOf (action, branchType) <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  have hTailSize : sizeOf tail < n := by
                    have hTail : sizeOf tail <
                        sizeOf ((action, branchType) :: tail) := by
                      simp_wf
                      omega
                    omega
                  simp only [PactType.branchCanCompleteBeforeTockSubst,
                    PactType.BranchCanCompleteBeforeTock,
                    ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1,
                    tailIH hTailSize hBranchFields.2]
            apply hList branches
            · rw [← hSize]; simp_wf; omega
            · exact hFields.2
          simp only [canCompleteBeforeTockSubst,
            PactType.CanCompleteBeforeTock,
            ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranchEq]

/- Substitution preserves the absence of a free tail occurrence when both
the substituted syntax and the replacement have that property. -/
theorem PactType.tailOccurrences_false_replaceVar
    (name other : String) (replacement : PactType)
    (hReplacement : replacement.TailOccurrences name False) :
    ∀ processType : PactType,
      processType.TailOccurrences name False →
        (processType.replaceVar other replacement).TailOccurrences
          name False := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hProcess
      have hOfferChildren : ∀ (elseType : PactType)
          (branches : List (BareMessage × PactType)),
          sizeOf elseType < n → sizeOf branches < n →
          elseType.TailOccurrences name False ∧
            PactType.TailBranchOccurrences name False branches →
          (elseType.replaceVar other replacement).TailOccurrences name False ∧
            PactType.TailBranchOccurrences name False
              (PactType.replaceBranches branches other replacement) := by
        intro elseType branches hElseSize hBranchesSize hFields
        have hBranches : PactType.TailBranchOccurrences name False
            (PactType.replaceBranches branches other replacement) := by
          have hList : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.TailBranchOccurrences name False rest →
              PactType.TailBranchOccurrences name False
                (PactType.replaceBranches rest other replacement) := by
            intro rest
            induction rest with
            | nil =>
                intro _ _
                simp [PactType.replaceBranches,
                  PactType.TailBranchOccurrences]
            | cons branch rest ihRest =>
                intro hRestSize hRestTail
                rcases branch with ⟨action, branchType⟩
                have hBranchFields :
                    branchType.TailOccurrences name False ∧
                      PactType.TailBranchOccurrences name False rest := by
                  simpa only [PactType.TailBranchOccurrences] using hRestTail
                have hBranchSize : sizeOf branchType < n := by
                  have hPair : sizeOf branchType <
                      sizeOf (action, branchType) := by simp_wf; omega
                  have hHead : sizeOf (action, branchType) <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                have hTailSize : sizeOf rest < n := by
                  have hTail : sizeOf rest <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                simpa only [PactType.replaceBranches,
                  PactType.TailBranchOccurrences] using And.intro
                    (ih (sizeOf branchType) hBranchSize branchType rfl
                      hBranchFields.1)
                    (ihRest hTailSize hBranchFields.2)
          exact hList branches hBranchesSize hFields.2
        exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
          hBranches⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.TailOccurrences]
      | progress pid => simp [PactType.replaceVar, PactType.TailOccurrences]
      | tock => simp [PactType.replaceVar, PactType.TailOccurrences]
      | skip => simp [PactType.replaceVar, PactType.TailOccurrences]
      | var current =>
          by_cases hCurrent : other = current
          · simpa [PactType.replaceVar, hCurrent] using hReplacement
          · simpa [PactType.replaceVar, hCurrent,
              PactType.TailOccurrences] using hProcess
      | recur binder body =>
          by_cases hShadow : other = binder
          · simpa [PactType.replaceVar, hShadow] using hProcess
          · by_cases hBinder : binder = name
            · subst binder
              simp [PactType.replaceVar, hShadow, PactType.TailOccurrences]
            · have hBodyTail : body.TailOccurrences name False := by
                simpa [PactType.TailOccurrences, hBinder] using hProcess
              have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              simpa [PactType.replaceVar, hShadow,
                PactType.TailOccurrences, hBinder] using
                  ih (sizeOf body) hBodySize body rfl hBodyTail
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl hFields.1)
              (ih (sizeOf right) hRightSize right rfl hFields.2)
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize hFields
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hProcess
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize hFields

/- A name forbidden from every free tail position does not occur freely at
all, so capture-avoiding substitution for that name is inert.  This is the
syntax bridge used by the recursion correspondence in every non-tail context
(sequence-left, parallel children, and conjunctive-offer branches). -/
theorem PactType.replaceVar_eq_self_of_tailOccurrences_false
    (name : String) (replacement : PactType) :
    ∀ processType : PactType,
      processType.TailOccurrences name False →
        processType.replaceVar name replacement = processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro hTail
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.TailBranchOccurrences name False branches →
          PactType.replaceBranches branches name replacement = branches := by
        intro branches hBranchesSize hBranchTail
        induction branches with
        | nil => simp [PactType.replaceBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hFields : branchType.TailOccurrences name False ∧
                PactType.TailBranchOccurrences name False rest := by
              simpa only [PactType.TailBranchOccurrences] using hBranchTail
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType <
                  sizeOf (action, branchType) := by simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hRest : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.replaceBranches]
            rw [ih (sizeOf branchType) hBranchSize branchType rfl hFields.1,
              restIH hRestSize hFields.2]
      cases processType with
      | message msg dir => simp [PactType.replaceVar]
      | progress pid => simp [PactType.replaceVar]
      | tock => simp [PactType.replaceVar]
      | skip => simp [PactType.replaceVar]
      | var other =>
          have hAbsent : name ≠ other := by
            intro hEq
            simp only [PactType.TailOccurrences] at hTail
            exact hTail hEq.symm
          simp [PactType.replaceVar, hAbsent]
      | recur binder body =>
          by_cases hShadow : name = binder
          · simp [PactType.replaceVar, hShadow]
          · have hBodyTail : body.TailOccurrences name False := by
              have hBinder : binder ≠ name := by exact Ne.symm hShadow
              simpa only [PactType.TailOccurrences, if_neg hBinder] using hTail
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simp [PactType.replaceVar, hShadow,
              ih (sizeOf body) hBodySize body rfl hBodyTail]
      | choice left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | fairChoice bid left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | seq left right =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | par left right interface =>
          have hFields : left.TailOccurrences name False ∧
              right.TailOccurrences name False := by
            simpa only [PactType.TailOccurrences] using hTail
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf left) hLeftSize left rfl hFields.1,
            ih (sizeOf right) hRightSize right rfl hFields.2]
      | xoffer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]
      | offer elseType branches =>
          have hFields : elseType.TailOccurrences name False ∧
              PactType.TailBranchOccurrences name False branches := by
            simpa only [PactType.TailOccurrences] using hTail
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.replaceVar]
          rw [ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
            hBranches branches hBranchesSize hFields.2]

/- Replacing every free occurrence of a name by its own binder removes that
name from all non-tail positions, independently of the original syntax. -/
theorem PactType.tailOccurrences_false_replaceVar_self_recur
    (name : String) (body : PactType) : ∀ processType : PactType,
    (processType.replaceVar name (.recur name body)).TailOccurrences
      name False := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hOfferChildren : ∀ (elseType : PactType)
          (branches : List (BareMessage × PactType)),
          sizeOf elseType < n → sizeOf branches < n →
          (elseType.replaceVar name (.recur name body)).TailOccurrences
              name False ∧
            PactType.TailBranchOccurrences name False
              (PactType.replaceBranches branches name (.recur name body)) := by
        intro elseType branches hElseSize hBranchesSize
        have hBranches : PactType.TailBranchOccurrences name False
            (PactType.replaceBranches branches name (.recur name body)) := by
          have hList : ∀ rest : List (BareMessage × PactType),
              sizeOf rest < n →
              PactType.TailBranchOccurrences name False
                (PactType.replaceBranches rest name (.recur name body)) := by
            intro rest
            induction rest with
            | nil =>
                intro _
                simp [PactType.replaceBranches,
                  PactType.TailBranchOccurrences]
            | cons branch rest ihRest =>
                intro hRestSize
                rcases branch with ⟨action, branchType⟩
                have hBranchSize : sizeOf branchType < n := by
                  have hPair : sizeOf branchType <
                      sizeOf (action, branchType) := by simp_wf; omega
                  have hHead : sizeOf (action, branchType) <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                have hTailSize : sizeOf rest < n := by
                  have hTail : sizeOf rest <
                      sizeOf ((action, branchType) :: rest) := by simp_wf; omega
                  omega
                simpa only [PactType.replaceBranches,
                  PactType.TailBranchOccurrences] using And.intro
                    (ih (sizeOf branchType) hBranchSize branchType rfl)
                    (ihRest hTailSize)
          exact hList branches hBranchesSize
        exact ⟨ih (sizeOf elseType) hElseSize elseType rfl, hBranches⟩
      cases processType with
      | message msg dir => simp [PactType.replaceVar, PactType.TailOccurrences]
      | progress pid => simp [PactType.replaceVar, PactType.TailOccurrences]
      | tock => simp [PactType.replaceVar, PactType.TailOccurrences]
      | skip => simp [PactType.replaceVar, PactType.TailOccurrences]
      | var current =>
          by_cases hCurrent : name = current
          · simp [PactType.replaceVar, hCurrent, PactType.TailOccurrences]
          · simp [PactType.replaceVar, hCurrent,
              PactType.TailOccurrences, Ne.symm hCurrent]
      | recur binder nestedBody =>
          by_cases hShadow : name = binder
          · simp [PactType.replaceVar, hShadow, PactType.TailOccurrences]
          · have hBinder : binder ≠ name := Ne.symm hShadow
            have hBodySize : sizeOf nestedBody < n := by
              rw [← hSize]; simp_wf; omega
            simpa [PactType.replaceVar, hShadow,
              PactType.TailOccurrences, hBinder] using
                ih (sizeOf nestedBody) hBodySize nestedBody rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            And.intro (ih (sizeOf left) hLeftSize left rfl)
              (ih (sizeOf right) hRightSize right rfl)
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simpa only [PactType.replaceVar, PactType.TailOccurrences] using
            hOfferChildren elseType branches hElseSize hBranchesSize

/-- Replacing an occurrence protected by a clock does not change whether the
surrounding syntax can finish in the current cycle. -/
theorem PactType.guardedOccurrences_replace_canCompleteBeforeTock
    (name : String) (replacement processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) :
    (processType.replaceVar name replacement).CanCompleteBeforeTock =
      processType.CanCompleteBeforeTock := by
  let replaced := processType.replaceVar name replacement
  let fuel := max (sizeOf replaced + 1) (sizeOf processType + 1)
  have hReplacedFuel : sizeOf replaced < fuel := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_max_left (sizeOf replaced + 1) (sizeOf processType + 1))
  have hProcessFuel : sizeOf processType < fuel := by
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_max_right (sizeOf replaced + 1) (sizeOf processType + 1))
  calc
    replaced.CanCompleteBeforeTock =
        typeCanCompleteThisCycleFuel fuel replaced :=
      (typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
        fuel replaced hReplacedFuel).symm
    _ = typeCanCompleteThisCycleFuel fuel processType := by
      exact guardedOccurrences_replace_canCompleteThisCycleFuel
        name replacement processType hGuarded fuel
    _ = processType.CanCompleteBeforeTock :=
      typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
        fuel processType hProcessFuel

/-- Syntax-derived futures of a sequence include the right menu exactly when
the left syntax may optimistically complete before the next clock. -/
theorem typeFutureOffers_sequence (left right : PactType) :
    typeFutureOffers (.seq left right) =
      if left.CanCompleteBeforeTock then
        typeFutureOffers left ∪ typeFutureOffers right
      else typeFutureOffers left := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  have hCompleteFuel : sizeOf left <
      sizeOf (PactType.seq left right) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.seq left right) + 1)
      (PactType.seq left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeCanCompleteThisCycleFuel_eq_canCompleteBeforeTock
      _ left hCompleteFuel,
    typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over ordinary choice. -/
theorem typeFutureOffers_choice (left right : PactType) :
    typeFutureOffers (.choice left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.choice left right) := by
    change sizeOf left + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.choice left right) := by
    change sizeOf right + 1 ≤ 1 + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.choice left right) + 1)
      (PactType.choice left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures distribute over fair choice. -/
theorem typeFutureOffers_fairChoice
    (bid : BranchId) (left right : PactType) :
    typeFutureOffers (.fairChoice bid left right) =
      typeFutureOffers left ∪ typeFutureOffers right := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.fairChoice bid left right) := by
    change sizeOf left + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.fairChoice bid left right) := by
    change sizeOf right + 1 ≤ 1 + bid + sizeOf left + sizeOf right
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.fairChoice bid left right) + 1)
      (PactType.fairChoice bid left right) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- Syntax-derived futures of an exclusive offer contain the else menu, every
branch head, and every branch continuation menu. -/
theorem typeFutureOffers_xoffer
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.xoffer elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  let fuel := sizeOf (PactType.xoffer elseType branches)
  have hElseFuel : sizeOf elseType + 1 ≤ fuel := by
    simp [fuel]
    omega
  have hBranchFuel : ∀ branch ∈ branches,
      sizeOf branch.2 + 1 ≤ fuel := by
    intro branch hBranch
    have hPairSize := List.sizeOf_lt_of_mem hBranch
    have hComponentSize : sizeOf branch.2 < sizeOf branch := by
      rcases branch
      simp_wf
      omega
    simp [fuel]
    omega
  have hFold : ∀ rest : List (BareMessage × PactType),
      (∀ branch ∈ rest, sizeOf branch.2 + 1 ≤ fuel) →
      ∀ initial,
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2) initial =
        rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial := by
    intro rest hRest
    induction rest with
    | nil => simp
    | cons branch tail ih =>
        intro initial
        simp only [List.foldl_cons]
        rw [typeFutureOffersFuel_eq_typeFutureOffers branch.2 fuel
          (hRest branch (by simp))]
        apply ih
        intro entry hEntry
        exact hRest entry (by simp [hEntry])
  change branches.foldl (fun offers branch =>
      offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
      (typeFutureOffersFuel fuel elseType) = _
  rw [typeFutureOffersFuel_eq_typeFutureOffers elseType fuel hElseFuel]
  exact hFold branches hBranchFuel (typeFutureOffers elseType)

/-- Conjunctive offers have the same optimistic syntax menu as exclusive
offers: the else continuation, every branch head, and every branch menu. -/
theorem typeFutureOffers_offer
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    typeFutureOffers (.offer elseType branches) =
      branches.foldl (fun offers branch =>
        offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
        (typeFutureOffers elseType) := by
  simpa only [typeFutureOffers, typeFutureOffersFuel] using
    typeFutureOffers_xoffer elseType branches

/-- Parallel future offers are the optimistic union of both syntax-derived
component menus, with the synchronization interface hidden. -/
theorem typeFutureOffers_parallel
    (left right : PactType) (interface : Interface) :
    typeFutureOffers (.par left right interface) =
      hideTypeOffers interface
        (typeFutureOffers left ∪ typeFutureOffers right) := by
  have hLeftFuel : sizeOf left + 1 ≤
      sizeOf (PactType.par left right interface) := by
    simp_wf
    omega
  have hRightFuel : sizeOf right + 1 ≤
      sizeOf (PactType.par left right interface) := by
    simp_wf
    omega
  change typeFutureOffersFuel
      (sizeOf (PactType.par left right interface) + 1)
      (PactType.par left right interface) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers left _ hLeftFuel,
    typeFutureOffersFuel_eq_typeFutureOffers right _ hRightFuel]

/-- A recursion binder exposes the same syntactic same-cycle future menu as
its body; guardedness is used separately when replacing recursive calls. -/
theorem typeFutureOffers_recur (name : String) (body : PactType) :
    typeFutureOffers (.recur name body) = typeFutureOffers body := by
  have hBodyFuel : sizeOf body + 1 ≤ sizeOf (PactType.recur name body) := by
    simp_wf
    omega
  change typeFutureOffersFuel (sizeOf (PactType.recur name body) + 1)
      (PactType.recur name body) = _
  simp only [typeFutureOffersFuel]
  rw [typeFutureOffersFuel_eq_typeFutureOffers body _ hBodyFuel]

/-- Substituting syntax and then computing its optimistic future menu is
equivalent to interpreting the substituted variable directly in the
parameterized syntax fold.  This is capture-avoiding: a nested binder with the
same name stops the interpretation exactly where `replaceVar` stops. -/
theorem PactType.replaceVar_typeFutureOffers
    (name : String) (replacement processType : PactType) :
    typeFutureOffers (processType.replaceVar name replacement) =
      futureOffersSubst name replacement.CanCompleteBeforeTock
        (typeFutureOffers replacement) processType := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | h n ih =>
      cases processType with
      | message msg dir =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | progress pid =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | tock =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | skip =>
          simp [PactType.replaceVar, futureOffersSubst, typeFutureOffers,
            typeFutureOffersFuel]
      | var other =>
          by_cases hName : name = other
          · subst other
            simp [PactType.replaceVar, futureOffersSubst]
          · simp [PactType.replaceVar, futureOffersSubst, hName,
              typeFutureOffers, typeFutureOffersFuel]
      | recur other body =>
          by_cases hName : name = other
          · subst other
            simp [PactType.replaceVar, futureOffersSubst,
              typeFutureOffers_recur]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]
              simp_wf
              omega
            simp only [PactType.replaceVar, hName, if_false,
              futureOffersSubst, typeFutureOffers_recur]
            exact ih (sizeOf body) hBodySize body rfl
      | choice left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_choice,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | fairChoice bid left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_fairChoice,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | seq left right =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_sequence,
            futureOffersSubst]
          rw [PactType.replaceVar_canCompleteBeforeTock,
            ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | par left right interface =>
          have hLeftSize : sizeOf left < n := by
            rw [← hSize]
            simp_wf
            omega
          have hRightSize : sizeOf right < n := by
            rw [← hSize]
            simp_wf
            omega
          simp only [PactType.replaceVar, typeFutureOffers_parallel,
            futureOffersSubst]
          rw [ih (sizeOf left) hLeftSize left rfl,
            ih (sizeOf right) hRightSize right rfl]
      | xoffer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, entry ∈ branches) →
              ∀ initial,
                (PactType.replaceBranches rest name replacement).foldl
                    (fun offers branch =>
                      offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
                    initial =
                  initial ∪ branchFutureOffersSubst name
                    replacement.CanCompleteBeforeTock
                    (typeFutureOffers replacement) rest := by
            intro rest hRest
            induction rest with
            | nil =>
                intro initial
                simp [PactType.replaceBranches, branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                have hMember : (action, branchType) ∈ branches :=
                  hRest _ (by simp)
                have hBranchSize : sizeOf branchType < n := by
                  have hPair := List.sizeOf_lt_of_mem hMember
                  have hComponent : sizeOf branchType <
                      sizeOf (action, branchType) := by
                    simp_wf
                    omega
                  rw [← hSize]
                  simp_wf
                  omega
                simp only [PactType.replaceBranches, List.foldl_cons,
                  branchFutureOffersSubst]
                rw [ih (sizeOf branchType) hBranchSize branchType rfl,
                  hTail (fun other hOther => hRest other (by simp [hOther]))]
                simp only [Finset.union_assoc]
          simp only [PactType.replaceVar, typeFutureOffers_xoffer,
            futureOffersSubst]
          rw [ih (sizeOf elseType) hElseSize elseType rfl,
            hFold branches (by simp)]
      | offer elseType branches =>
          have hElseSize : sizeOf elseType < n := by
            rw [← hSize]
            simp_wf
            omega
          have hFold : ∀ rest : List (BareMessage × PactType),
              (∀ entry ∈ rest, entry ∈ branches) →
              ∀ initial,
                (PactType.replaceBranches rest name replacement).foldl
                    (fun offers branch =>
                      offers ∪ {branch.1} ∪ typeFutureOffers branch.2)
                    initial =
                  initial ∪ branchFutureOffersSubst name
                    replacement.CanCompleteBeforeTock
                    (typeFutureOffers replacement) rest := by
            intro rest hRest
            induction rest with
            | nil =>
                intro initial
                simp [PactType.replaceBranches, branchFutureOffersSubst]
            | cons entry tail hTail =>
                obtain ⟨action, branchType⟩ := entry
                intro initial
                have hMember : (action, branchType) ∈ branches :=
                  hRest _ (by simp)
                have hBranchSize : sizeOf branchType < n := by
                  have hPair := List.sizeOf_lt_of_mem hMember
                  have hComponent : sizeOf branchType <
                      sizeOf (action, branchType) := by
                    simp_wf
                    omega
                  rw [← hSize]
                  simp_wf
                  omega
                simp only [PactType.replaceBranches, List.foldl_cons,
                  branchFutureOffersSubst]
                rw [ih (sizeOf branchType) hBranchSize branchType rfl,
                  hTail (fun other hOther => hRest other (by simp [hOther]))]
                simp only [Finset.union_assoc]
          simp only [PactType.replaceVar, typeFutureOffers_offer,
            futureOffersSubst]
          rw [ih (sizeOf elseType) hElseSize elseType rfl,
            hFold branches (by simp)]

/-- Unfolding a clock-guarded recursive variable preserves the public
same-cycle future-offer menu. -/
theorem guardedOccurrences_replace_typeFutureOffers_recur
    (name : String) (body processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) :
    typeFutureOffers (processType.replaceVar name (.recur name body)) =
      typeFutureOffers processType := by
  unfold typeFutureOffers
  let unfolded := processType.replaceVar name (.recur name body)
  have hSize : sizeOf processType ≤ sizeOf unfolded := by
    exact PactType.sizeOf_le_replaceVar_recur processType name body
  have hFuel : sizeOf processType + 1 ≤ sizeOf unfolded + 1 := by omega
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hFuel
  rw [guardedOccurrences_replace_typeFutureOffersFuel
    name (.recur name body) processType hGuarded (sizeOf unfolded + 1)]
  rw [hExtra]
  exact typeFutureOffersFuel_add_stable processType
    (sizeOf processType + 1) extra (by omega)

/-- Regression for optimistic, syntax-derived futures: after selecting the
left choice, both distinct sends can still occur before the next clock. -/
theorem syntactic_optimistic_sequence_future_regression :
    typeFutureOffers
        (.seq (.choice (.message "a" .send) .skip) (.message "b" .send)) =
      {("a", .send), ("b", .send)} := by
  decide

/-- Branch offers selected by the future part of this environment. -/
def typeWaitingOffers (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (env.future.image typeNeed) ∩ typeBranchActions branches

/-
Environment-indexed current/future offers and the sibling-local environment
relation are mutually defined: parallel offers depend on the two local steps,
while each local environment depends on the sibling step's offers.
-/
mutual
  @[aesop unsafe]
  inductive TypeOffers :
      TypeEnvironment → PactType → TypeLabel → PactType →
        Finset BareMessage → Finset BareMessage → Prop where
    | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ env.hasNeed (msg, dir) →
        TypeOffers env (.message msg dir) (TypeLabel.message msg dir) .skip
          {(msg, dir)} (typeFutureOffers .skip)
    | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
        env.WellFormed ∧ ¬ env.hasNeed (msg, dir) ∧ env.clock = false →
        TypeOffers env (.message msg dir) TypeLabel.silent (.message msg dir)
          {(msg, dir)} (typeFutureOffers (.message msg dir) \ {(msg, dir)})
    | choice_left (env : TypeEnvironment) (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.choice left right) TypeLabel.silent left
          ∅ (typeFutureOffers left)
    | choice_right (env : TypeEnvironment) (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.choice left right) TypeLabel.silent right
          ∅ (typeFutureOffers right)
    | fair_left (env : TypeEnvironment) (bid : BranchId)
        (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.fairChoice bid left right) (TypeLabel.fair bid true) left
          ∅ (typeFutureOffers left)
    | fair_right (env : TypeEnvironment) (bid : BranchId)
        (left right : PactType) :
        env.WellFormed →
        TypeOffers env (.fairChoice bid left right) (TypeLabel.fair bid false) right
          ∅ (typeFutureOffers right)
    | cycle (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = true →
        TypeOffers env .tock .tock .skip ∅ ∅
    | cycle_wait (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = false →
        TypeOffers env .tock TypeLabel.silent .tock ∅ ∅
    | skip (env : TypeEnvironment) :
        env.WellFormed ∧ env.clock = false ∧ env.immediate = ∅ →
        TypeOffers env .skip TypeLabel.silent .skip ∅ ∅
    | skip_seq (env : TypeEnvironment) (processType : PactType) :
        env.WellFormed →
        TypeOffers env (.seq .skip processType) TypeLabel.silent processType
          ∅ (typeFutureOffers processType)
    | progress (env : TypeEnvironment) (pid : ProcId) :
        env.WellFormed →
        TypeOffers env (.progress pid) (TypeLabel.progress pid) .skip ∅ ∅
    | recur (env : TypeEnvironment) (name : String) (body : PactType) :
        env.WellFormed →
        TypeOffers env (.recur name body) TypeLabel.silent
          (body.replaceVar name (.recur name body)) ∅
          (typeFutureOffers (body.replaceVar name (.recur name body)))
    | seq (env : TypeEnvironment) (left left' right : PactType)
        (label : TypeLabel) (current childFuture : Finset BareMessage) :
        TypeOffers env left label left' current childFuture →
        TypeOffers env (.seq left right) label (.seq left' right) current
          (typeFutureOffers (.seq left' right) \ current)
    | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (action : BareMessage) (processType : PactType) :
        env.WellFormed ∧
          (action, processType) ∈ branches ∧
          TypeBranchEnabled env (action, processType) ∧
          TypeResolved env branches →
        TypeOffers env (.xoffer elseType branches)
          (TypeLabel.message action.1 action.2) processType
          {action} (typeFutureOffers processType)
    | xoffer_else (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.xoffer elseType branches) TypeLabel.silent elseType
          ∅ (typeFutureOffers elseType)
    | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.xoffer elseType branches) TypeLabel.silent
          (.xoffer elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.xoffer elseType branches) \
            typeWaitingOffers env branches)
    | offer_some (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType))
        (enabled : BareMessage × PactType) :
        env.WellFormed ∧ enabled ∈ branches ∧ TypeBranchEnabled env enabled →
        TypeOffers env (.offer elseType branches) TypeLabel.silent
          (parallelTypeBranchesSelecting enabled branches) ∅
          (typeFutureOffers (parallelTypeBranchesSelecting enabled branches))
    | offer_else (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧
          TypeNoImmediateBranch env branches ∧ TypeResolved env branches →
        TypeOffers env (.offer elseType branches) TypeLabel.silent elseType
          (typeBranchActions branches) (typeFutureOffers elseType)
    | offer_wait (env : TypeEnvironment) (elseType : PactType)
        (branches : List (BareMessage × PactType)) :
        env.WellFormed ∧ TypeNoImmediateBranch env branches ∧
          ¬ TypeResolved env branches ∧ env.clock = false →
        TypeOffers env (.offer elseType branches) TypeLabel.silent
          (.offer elseType branches) (typeWaitingOffers env branches)
          (typeFutureOffers (.offer elseType branches) \
            typeWaitingOffers env branches)
    | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
        (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel)
        (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
        TypeOffers leftEnv left leftLabel left' leftCurrent leftFuture →
        TypeOffers rightEnv right rightLabel right' rightCurrent rightFuture →
        LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv →
        LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv →
        outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel →
        TypeOffers outer (.par left right interface)
          (TypeLabel.combine interface leftLabel rightLabel)
          (.par left' right' interface)
          (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))

  /-- The erased sibling-aware local-environment relation. -/
  @[aesop unsafe]
  inductive LocalTypeEnvironment :
      TypeEnvironment → Interface → TypeEnvironment → PactType →
        TypeLabel → TypeEnvironment → Prop where
    | clock (outer : TypeEnvironment) (interface : Interface)
        (sibling : PactType) (label : TypeLabel) :
        outer.clock = true →
        LocalTypeEnvironment outer interface TypeEnvironment.tock
          sibling label TypeEnvironment.tock
    | ordinary (outer siblingEnv localEnv : TypeEnvironment)
        (interface : Interface) (sibling siblingTarget : PactType)
        (label : TypeLabel) (current future : Finset BareMessage) :
        outer.clock = false →
        siblingEnv.clock = false →
        TypeOffers siblingEnv sibling label siblingTarget current future →
        localEnv.clock = false →
        localEnv.immediate =
          outer.immediate ∪ restrictTypeOffers interface current →
        localEnv.future =
          (outer.future ∪ restrictTypeOffers interface future) \ localEnv.immediate →
        LocalTypeEnvironment outer interface siblingEnv sibling label localEnv
end

/-- The operational sequence offer rule reads the future from the residual
syntax.  Selecting `a!` therefore exposes both `a!` and the subsequent `b!`
in the same cycle. -/
theorem syntactic_optimistic_sequence_offer_regression :
    TypeOffers TypeEnvironment.empty
      (.seq (.choice (.message "a" .send) .skip) (.message "b" .send))
      TypeLabel.silent
      (.seq (.message "a" .send) (.message "b" .send)) ∅
      {("a", .send), ("b", .send)} := by
  have hWellFormed : TypeEnvironment.empty.WellFormed := by
    simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
  have hChoice : TypeOffers TypeEnvironment.empty
      (.choice (.message "a" .send) .skip) TypeLabel.silent
      (.message "a" .send) ∅
      (typeFutureOffers (.message "a" .send)) :=
    TypeOffers.choice_left TypeEnvironment.empty (.message "a" .send) .skip
      hWellFormed
  have hSequence := TypeOffers.seq TypeEnvironment.empty
    (.choice (.message "a" .send) .skip) (.message "a" .send)
    (.message "b" .send) TypeLabel.silent ∅
    (typeFutureOffers (.message "a" .send)) hChoice
  simpa [syntactic_optimistic_sequence_future_regression] using hSequence

/-! ## Type transition system -/

/-- The erased, environment-indexed type judgment `Eτ ⊢ τ -α→ τ'`. -/
@[aesop unsafe]
inductive TypeTransition : TypeEnvironment → PactType → TypeLabel → PactType → Prop where
  | action (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      env.hasNeed (msg, dir) →
      --
      TypeTransition env (.message msg dir)
      (TypeLabel.message msg dir)
      .skip
  | action_wait (env : TypeEnvironment) (msg : MessageId) (dir : MessageDir) :
      env.WellFormed ∧
      ¬ env.hasNeed (msg, dir) ∧
      env.clock = false →
      --
      TypeTransition env (.message msg dir)
      TypeLabel.silent
      (.message msg dir)
  | choice_left (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.choice left right)
      TypeLabel.silent
      left
  | choice_right (env : TypeEnvironment) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.choice left right)
      TypeLabel.silent
      right
  | fair_left (env : TypeEnvironment) (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.fairChoice bid left right)
      (TypeLabel.fair bid true)
      left
  | fair_right (env : TypeEnvironment) (bid : BranchId) (left right : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.fairChoice bid left right)
      (TypeLabel.fair bid false)
      right
  | cycle (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = true →
      --
      TypeTransition env .tock
      .tock
      .skip
  | cycle_wait (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = false →
      --
      TypeTransition env .tock
      TypeLabel.silent
      .tock
  | skip (env : TypeEnvironment) :
      env.WellFormed ∧
      env.clock = false ∧
      env.immediate = ∅ →
      --
      TypeTransition env .skip
      TypeLabel.silent
      .skip
  | skip_seq (env : TypeEnvironment) (processType : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.seq .skip processType)
      TypeLabel.silent
      processType
  | progress (env : TypeEnvironment) (pid : ProcId) :
      env.WellFormed →
      --
      TypeTransition env (.progress pid)
      (TypeLabel.progress pid)
      .skip
  | recur (env : TypeEnvironment) (var : String) (body : PactType) :
      env.WellFormed →
      --
      TypeTransition env (.recur var body)
      TypeLabel.silent
      (body.replaceVar var (.recur var body))
  | seq (env : TypeEnvironment) (left left' right : PactType) (label : TypeLabel) :
      TypeTransition env left label left' →
      --
      TypeTransition env (.seq left right)
      label
      (.seq left' right)
  | xoffer_branch (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (action : BareMessage) (processType : PactType) :
      env.WellFormed ∧
      (action, processType) ∈ branches ∧
      TypeBranchEnabled env (action, processType) ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer elseType branches)
      (TypeLabel.message action.1 action.2)
      processType
  | xoffer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.xoffer elseType branches)
      TypeLabel.silent
      elseType
  | xoffer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.xoffer elseType branches)
      TypeLabel.silent
      (.xoffer elseType branches)
  | offer_some (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType))
      (enabled : BareMessage × PactType) :
      env.WellFormed ∧
      enabled ∈ branches ∧
      TypeBranchEnabled env enabled →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      (parallelTypeBranchesSelecting enabled branches)
  | offer_else (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      TypeResolved env branches →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      elseType
  | offer_wait (env : TypeEnvironment) (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      env.WellFormed ∧
      TypeNoImmediateBranch env branches ∧
      ¬ TypeResolved env branches ∧
      env.clock = false →
      --
      TypeTransition env (.offer elseType branches)
      TypeLabel.silent
      (.offer elseType branches)
  | par (outer leftEnv rightEnv : TypeEnvironment) (interface : Interface)
      (left left' right right' : PactType) (leftLabel rightLabel : TypeLabel) :
      TypeTransition leftEnv left leftLabel left' →
      TypeTransition rightEnv right rightLabel right' →
      (outer.WellFormed ∧
        LocalTypeEnvironment outer interface rightEnv right rightLabel leftEnv ∧
        LocalTypeEnvironment outer interface leftEnv left leftLabel rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel) →
      --
      TypeTransition outer (.par left right interface)
      (TypeLabel.combine interface leftLabel rightLabel)
      (.par left' right' interface)

/-- Administrative-`ε` weak closure used by conformance and refinement. -/
def TypeWeakTransition :
    TypeEnvironment → PactType → TypeLabel → PactType → Prop := by
  sorry

structure TypeOfferSummary : Type where
  current : Finset BareMessage
  future : Finset BareMessage
  deriving DecidableEq

def DecoratedTypeTransition
    (env : TypeEnvironment) (source : PactType) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : PactType) : Prop :=
  TypeTransition env source label target ∧
  TypeOffers env source label target offers.current offers.future

/-- Every semantic type step carries at least one environment-specific offer pair. -/
theorem TypeTransition.exists_typeOffers
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ current future, TypeOffers env source label target current future := by
  induction transition with
  | xoffer_branch env elseType branches action processType conditions =>
      exact ⟨{action}, typeFutureOffers processType,
        TypeOffers.xoffer_branch env elseType branches action processType conditions⟩
  | _ => aesop

/-- Package a semantic step together with one of its offer pairs. -/
theorem TypeTransition.exists_decorated
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (transition : TypeTransition env source label target) :
    ∃ offers, DecoratedTypeTransition env source label offers target := by
  obtain ⟨current, future, hOffers⟩ := transition.exists_typeOffers
  exact ⟨{ current := current, future := future }, transition, hOffers⟩

/-- A weak alternating simulation witnessing `P |= τ`. -/
structure ConformanceWitness (process : Proc) (processType : PactType) : Type where
  relation : Proc → PactType → Prop
  initial : relation process processType
  matchStep :
    ∀ {p₀ p₁ : Proc} {τ₀ : PactType} {env : Environment} {label : Label},
      relation p₀ τ₀ →
      ProcessTransition env p₀ label p₁ →
      ∃ τ₁,
        TypeWeakTransition (eraseEnvironment env) τ₀ (eraseLabel label) τ₁ ∧
        relation p₁ τ₁

/-- Process-type conformance (Definition 4.1). -/
def Conforms (process : Proc) (processType : PactType) : Prop :=
  Nonempty (ConformanceWitness process processType)

/-- A type-to-type alternating simulation witness. -/
structure RefinementWitness (precise abstract : PactType) : Type where
  relation : PactType → PactType → Prop
  initial : relation precise abstract
  matchStep :
    ∀ {τ₀ τ₁ τ₀' : PactType} {env : TypeEnvironment} {label : TypeLabel},
      relation τ₀ τ₀' →
      TypeWeakTransition env τ₀ label τ₁ →
      ∃ τ₁', TypeWeakTransition env τ₀' label τ₁' ∧ relation τ₁ τ₁'

/-- `precise ⊑ abstract` (Definition 4.2). -/
def Refines (precise abstract : PactType) : Prop :=
  Nonempty (RefinementWitness precise abstract)

/-- Data-oblivious type checking (Definition 4.3). -/
def DataObliviousChecks (process : Proc) (claimed : PactType) : Prop :=
  Refines (inferProcess process) claimed


end

end Pact
