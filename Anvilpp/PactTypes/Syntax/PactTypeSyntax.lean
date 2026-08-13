import Mathlib.Data.Finset.Image
import Anvilpp.PactSemantics

/-!
# PactType: the type grammar, capture-avoiding substitution, binder freshness/hygiene
-/

namespace Pact

noncomputable section

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

  /- Substitution rewrites only branch continuations, never branch actions.
  Every branch-indexed side condition of the offer semantics
  (`TypeResolved`, `TypeNoImmediateBranch`, `TypeBranchEnabled`,
  `typeWaitingOffers`) therefore survives substitution unchanged. -/
  theorem replaceBranches_map_fst (var : String) (replacement : PactType) :
      ∀ branches : List (BareMessage × PactType),
        (replaceBranches branches var replacement).map Prod.fst =
          branches.map Prod.fst := by
    intro branches
    induction branches with
    | nil => simp [replaceBranches]
    | cons entry rest ih =>
        obtain ⟨action, branchType⟩ := entry
        simp [replaceBranches, ih]

  theorem mem_replaceBranches (var : String) (replacement : PactType)
      (action : BareMessage) (processType : PactType) :
      ∀ branches : List (BareMessage × PactType),
        (action, processType) ∈ branches →
          (action, processType.replaceVar var replacement) ∈
            replaceBranches branches var replacement := by
    intro branches
    induction branches with
    | nil => intro hMember; simp at hMember
    | cons entry rest ih =>
        obtain ⟨entryAction, entryType⟩ := entry
        intro hMember
        rcases List.mem_cons.mp hMember with hHead | hRest
        · rw [Prod.mk.injEq] at hHead
          obtain ⟨hAction, hType⟩ := hHead
          subst hAction
          subst hType
          simp [replaceBranches]
        · rw [replaceBranches]
          exact List.mem_cons_of_mem _ (ih hRest)

  theorem mem_replaceBranches_cases (var : String) (replacement : PactType)
      (entry : BareMessage × PactType) :
      ∀ branches : List (BareMessage × PactType),
        entry ∈ replaceBranches branches var replacement →
          ∃ original ∈ branches,
            entry = (original.1, original.2.replaceVar var replacement) := by
    intro branches
    induction branches with
    | nil => intro hMember; simp [replaceBranches] at hMember
    | cons head rest ih =>
        obtain ⟨headAction, headType⟩ := head
        intro hMember
        rw [replaceBranches] at hMember
        rcases List.mem_cons.mp hMember with hHead | hRest
        · exact ⟨(headAction, headType), List.mem_cons_self, hHead⟩
        · obtain ⟨original, hOriginal, hEqual⟩ := ih hRest
          exact ⟨original, List.mem_cons_of_mem _ hOriginal, hEqual⟩

  /- Substitution of two *distinct* variables commutes, provided the outer
  replacement is closed for the inner name and the term never rebinds the outer
  name.  Both side conditions are real: without the freshness premise a
  shadowing `.recur outerName _` keeps the inner replacement unsubstituted on
  one side only, and without `hOuterClosed` the outer replacement would itself
  be rewritten when it is reached through the inner variable. -/
  theorem replaceVar_comm
      (outerName innerName : String) (outerRepl innerRepl : PactType)
      (hDistinct : ¬ outerName = innerName)
      (hOuterClosed : ∀ q, outerRepl.replaceVar innerName q = outerRepl) :
      ∀ processType : PactType, processType.BinderFreshFor [outerName] →
        (processType.replaceVar innerName innerRepl).replaceVar outerName
            outerRepl =
          (processType.replaceVar outerName outerRepl).replaceVar innerName
            (innerRepl.replaceVar outerName outerRepl) := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            (∀ entry ∈ branches, sizeOf entry.2 < n) →
            BinderFreshForBranches [outerName] branches →
              replaceBranches (replaceBranches branches innerName innerRepl)
                  outerName outerRepl =
                replaceBranches (replaceBranches branches outerName outerRepl)
                  innerName (innerRepl.replaceVar outerName outerRepl) := by
          intro branches hSizes hFresh
          induction branches with
          | nil => simp [replaceBranches]
          | cons entry rest restIH =>
              obtain ⟨action, branchType⟩ := entry
              simp only [BinderFreshForBranches] at hFresh
              simp only [replaceBranches]
              rw [ih (sizeOf branchType) (hSizes (action, branchType) (by simp))
                  branchType rfl hFresh.1,
                restIH (fun entry hEntry => hSizes entry (by simp [hEntry]))
                  hFresh.2]
        cases processType with
        | message msg dir => intro _; simp [replaceVar]
        | progress pid => intro _; simp [replaceVar]
        | tock => intro _; simp [replaceVar]
        | skip => intro _; simp [replaceVar]
        | var current =>
            intro _
            by_cases hInner : innerName = current
            · subst hInner
              have hLeft : ((PactType.var innerName).replaceVar innerName
                  innerRepl).replaceVar outerName outerRepl =
                  innerRepl.replaceVar outerName outerRepl := by
                simp [replaceVar]
              have hRight : ((PactType.var innerName).replaceVar outerName
                  outerRepl).replaceVar innerName
                    (innerRepl.replaceVar outerName outerRepl) =
                  innerRepl.replaceVar outerName outerRepl := by
                simp [replaceVar, hDistinct]
              rw [hLeft, hRight]
            · by_cases hOuter : outerName = current
              · subst hOuter
                have hLeft : ((PactType.var outerName).replaceVar innerName
                    innerRepl).replaceVar outerName outerRepl = outerRepl := by
                  simp [replaceVar, hInner]
                have hRight : ((PactType.var outerName).replaceVar outerName
                    outerRepl).replaceVar innerName
                      (innerRepl.replaceVar outerName outerRepl) =
                    outerRepl := by
                  simp [replaceVar, hOuterClosed]
                rw [hLeft, hRight]
              · simp [replaceVar, hInner, hOuter]
        | recur current body =>
            intro hFresh
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            simp only [BinderFreshFor] at hFresh
            have hOuter : ¬ outerName = current := by
              intro hEq
              exact hFresh.1 (by simp [hEq])
            by_cases hInner : innerName = current
            · have hLeft : ((PactType.recur current body).replaceVar innerName
                  innerRepl).replaceVar outerName outerRepl =
                  .recur current (body.replaceVar outerName outerRepl) := by
                simp [replaceVar, hInner, hOuter]
              have hRight : ((PactType.recur current body).replaceVar outerName
                  outerRepl).replaceVar innerName
                    (innerRepl.replaceVar outerName outerRepl) =
                  .recur current (body.replaceVar outerName outerRepl) := by
                simp [replaceVar, hInner, hOuter]
              rw [hLeft, hRight]
            · have hLeft : ((PactType.recur current body).replaceVar innerName
                  innerRepl).replaceVar outerName outerRepl =
                  .recur current ((body.replaceVar innerName
                    innerRepl).replaceVar outerName outerRepl) := by
                simp [replaceVar, hInner, hOuter]
              have hRight : ((PactType.recur current body).replaceVar outerName
                  outerRepl).replaceVar innerName
                    (innerRepl.replaceVar outerName outerRepl) =
                  .recur current ((body.replaceVar outerName
                    outerRepl).replaceVar innerName
                      (innerRepl.replaceVar outerName outerRepl)) := by
                simp [replaceVar, hInner, hOuter]
              rw [hLeft, hRight,
                ih (sizeOf body) hBodySize body rfl hFresh.2]
        | choice left right =>
            intro hFresh
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf left) hLeftSize left rfl hFresh.1,
              ih (sizeOf right) hRightSize right rfl hFresh.2]
        | fairChoice bid left right =>
            intro hFresh
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf left) hLeftSize left rfl hFresh.1,
              ih (sizeOf right) hRightSize right rfl hFresh.2]
        | seq left right =>
            intro hFresh
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf left) hLeftSize left rfl hFresh.1,
              ih (sizeOf right) hRightSize right rfl hFresh.2]
        | par left right interface =>
            intro hFresh
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf left) hLeftSize left rfl hFresh.1,
              ih (sizeOf right) hRightSize right rfl hFresh.2]
        | xoffer elseType branches =>
            intro hFresh
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : ∀ entry ∈ branches, sizeOf entry.2 < n := by
              intro entry hEntry
              have hPair := List.sizeOf_lt_of_mem hEntry
              have hComponent : sizeOf entry.2 < sizeOf entry := by
                rcases entry
                simp_wf
                omega
              rw [← hSize]
              simp_wf
              omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf elseType) hElseSize elseType rfl hFresh.1,
              hBranches branches hBranchesSize hFresh.2]
        | offer elseType branches =>
            intro hFresh
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : ∀ entry ∈ branches, sizeOf entry.2 < n := by
              intro entry hEntry
              have hPair := List.sizeOf_lt_of_mem hEntry
              have hComponent : sizeOf entry.2 < sizeOf entry := by
                rcases entry
                simp_wf
                omega
              rw [← hSize]
              simp_wf
              omega
            simp only [BinderFreshFor] at hFresh
            rw [replaceVar, replaceVar, replaceVar, replaceVar,
              ih (sizeOf elseType) hElseSize elseType rfl hFresh.1,
              hBranches branches hBranchesSize hFresh.2]

  /- Binder freshness is contravariant in the forbidden-name list. -/
  theorem binderFreshFor_mono
      {smaller larger : List String}
      (hSubset : ∀ name, name ∈ smaller → name ∈ larger) :
      ∀ processType,
        BinderFreshFor larger processType →
          BinderFreshFor smaller processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            BinderFreshForBranches larger branches →
              BinderFreshForBranches smaller branches := by
          intro branches hBranchesSize h
          induction branches with
          | nil => simp [BinderFreshForBranches]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [BinderFreshForBranches] at h ⊢
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
              exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl h.1,
                restIH hRestSize h.2⟩
        cases processType with
        | message msg dir => intro _; simp [BinderFreshFor]
        | progress pid => intro _; simp [BinderFreshFor]
        | tock => intro _; simp [BinderFreshFor]
        | skip => intro _; simp [BinderFreshFor]
        | var current => intro _; simp [BinderFreshFor]
        | recur current body =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            exact ⟨fun hMember => h.1 (hSubset current hMember),
              ih (sizeOf body) hBodySize body rfl h.2⟩
        | choice left right =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize left rfl h.1,
              ih (sizeOf right) hRightSize right rfl h.2⟩
        | fairChoice bid left right =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize left rfl h.1,
              ih (sizeOf right) hRightSize right rfl h.2⟩
        | seq left right =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize left rfl h.1,
              ih (sizeOf right) hRightSize right rfl h.2⟩
        | par left right interface =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf left) hLeftSize left rfl h.1,
              ih (sizeOf right) hRightSize right rfl h.2⟩
        | xoffer elseType branches =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl h.1,
              hBranches branches hBranchesSize h.2⟩
        | offer elseType branches =>
            intro h
            simp only [BinderFreshFor] at h ⊢
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl h.1,
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

end PactType

end

end Pact
