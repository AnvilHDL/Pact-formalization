import Mathlib.Data.Finset.Image
import Anvilpp.PactSemantics

/-!
# Paper-aligned Pact types

This file introduces the updated type syntax, value erasure, semantic
conformance/refinement interfaces, and the finite semantic-automaton interface
used by the paper's headline results.  Definitions whose construction is a
substantial proof obligation are deliberately marked with `sorry` so later
proof work has a stable statement to target.
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

  /- Every message identifier mentioned by a type, including declared
  parallel interfaces and offer heads.  This finite support is used to build
  the signature-independent environment universe for exact future-offer
  analysis. -/
  mutual
    def DeclaredMessageIds : PactType → Finset MessageId
      | .message msg _ => {msg}
      | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => DeclaredMessageIds body
      | .choice left right | .seq left right | .fairChoice _ left right =>
          DeclaredMessageIds left ∪ DeclaredMessageIds right
      | .par left right interface =>
          interface ∪ DeclaredMessageIds left ∪ DeclaredMessageIds right
      | .xoffer elseType branches | .offer elseType branches =>
          DeclaredMessageIds elseType ∪ DeclaredBranchMessageIds branches
    termination_by processType => sizeOf processType

    def DeclaredBranchMessageIds :
        List (BareMessage × PactType) → Finset MessageId
      | [] => ∅
      | (action, processType) :: rest =>
          {action.1} ∪ DeclaredMessageIds processType ∪
            DeclaredBranchMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- Progress and fair-choice declarations used by the canonical future
  analysis alphabet.  They do not affect the pending graph itself, but
  recording them makes that alphabet genuinely support the type it analyzes. -/
  mutual
    def DeclaredProgressIds : PactType → Finset ProcId
      | .progress pid => {pid}
      | .message _ _ | .tock | .skip | .var _ => ∅
      | .recur _ body => DeclaredProgressIds body
      | .choice left right | .seq left right | .fairChoice _ left right |
          .par left right _ =>
          DeclaredProgressIds left ∪ DeclaredProgressIds right
      | .xoffer elseType branches | .offer elseType branches =>
          DeclaredProgressIds elseType ∪
            DeclaredBranchProgressIds branches
    termination_by processType => sizeOf processType

    def DeclaredBranchProgressIds :
        List (BareMessage × PactType) → Finset ProcId
      | [] => ∅
      | (_, processType) :: rest =>
          DeclaredProgressIds processType ∪
            DeclaredBranchProgressIds rest
    termination_by branches => sizeOf branches

    def DeclaredFairIds : PactType → Finset BranchId
      | .fairChoice bid left right =>
          {bid} ∪ DeclaredFairIds left ∪ DeclaredFairIds right
      | .message _ _ | .progress _ | .tock | .skip | .var _ => ∅
      | .recur _ body => DeclaredFairIds body
      | .choice left right | .seq left right | .par left right _ =>
          DeclaredFairIds left ∪ DeclaredFairIds right
      | .xoffer elseType branches | .offer elseType branches =>
          DeclaredFairIds elseType ∪ DeclaredBranchFairIds branches
    termination_by processType => sizeOf processType

    def DeclaredBranchFairIds :
        List (BareMessage × PactType) → Finset BranchId
      | [] => ∅
      | (_, processType) :: rest =>
          DeclaredFairIds processType ∪ DeclaredBranchFairIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- All message identifiers used as synchronization interfaces anywhere in
  a type.  Unlike `DeclaredMessageIds`, this records only parallel binders. -/
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

  /- Parallel interfaces are lexically scoped: an interface at one product
  node is disjoint from every parallel interface below that node.  Sibling
  products may reuse an identifier because neither environment is injected
  through the other. -/
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

  theorem interfaceScoped_parallel_fields
      {left right : PactType} {interface : Interface}
      (hScoped : InterfaceScoped (.par left right interface)) :
      Disjoint interface
          (ParallelInterfaces left ∪ ParallelInterfaces right) ∧
        InterfaceScoped left ∧ InterfaceScoped right := by
    simpa [InterfaceScoped] using hScoped

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

  private def messageIdsWith (wanted : MessageDir)
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

  private def isRawSyncedMessage (syncedMessages : Finset MessageId) :
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

/-- Rewrite a conjunctive type offer into parallel singleton exclusive offers. -/
def parallelTypeBranches : List (BareMessage × PactType) → PactType
  | [] => .skip
  | [branch] => singletonTypeXOffer branch
  | branch :: rest =>
      .par (singletonTypeXOffer branch) (parallelTypeBranches rest) ∅

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
private def typeFutureOffersFuel : Nat → PactType → Finset BareMessage
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

/-- Legacy syntax-only future approximation retained for regression auditing.
The authoritative paper-level future menu is `typeFutureOffers`, defined from
the complete constructor graph below. -/
def structuralFutureOffers (processType : PactType) : Finset BareMessage :=
  typeFutureOffersFuel (sizeOf processType + 1) processType

/-- Guarded substitution preserves the legacy structural approximation. -/
theorem guardedOccurrences_replace_structuralFutureOffers_recur
    (name : String) (body processType : PactType)
    (hGuarded : processType.GuardedOccurrences name False) :
    structuralFutureOffers
        (processType.replaceVar name (.recur name body)) =
      structuralFutureOffers processType := by
  unfold structuralFutureOffers
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

/-- Branch offers selected by the future part of this environment. -/
def typeWaitingOffers (env : TypeEnvironment)
    (branches : List (BareMessage × PactType)) : Finset BareMessage :=
  (env.future.image typeNeed) ∩ typeBranchActions branches

/-- Current and same-cycle-future offers decorating one semantic or compiled
transition.  It is declared before the raw constructor compiler so the graph
representation remains independent of the operational judgments below. -/
structure TypeOfferSummary : Type where
  current : Finset BareMessage
  future : Finset BareMessage
  deriving DecidableEq

/-! ## Constructor-based finite automata -/

/--
The fixed finite alphabet for one type automaton.
-/
structure TypeAlphabet : Type extends MessageAlphabet where
  progress : Finset ProcId
  fair : Finset BranchId
  deriving DecidableEq

namespace TypeAlphabet

  /-- Boundary actions cannot use an internal message identifier (Section 2.1). -/
  def WellFormed (alphabet : TypeAlphabet) : Prop :=
    ∀ action ∈ alphabet.boundary, action.1 ∉ alphabet.interface

  /-- Both polarities of every fixed internal/interface message. -/
  def interfaceActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.interface.biUnion fun msg => {(msg, .send), (msg, .recv)}

  /-- Actions visible to a constructor while it is compiled as a subautomaton. -/
  def localActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.boundary ∪ alphabet.interfaceActions

  /-- Environment polarities complementary to the type's boundary actions. -/
  def environmentActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.boundary.image typeNeed

  def localEnvironmentActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.localActions.image typeNeed

  theorem environmentActions_subset_localEnvironmentActions
      (alphabet : TypeAlphabet) :
      alphabet.environmentActions ⊆ alphabet.localEnvironmentActions := by
    apply Finset.image_mono
    exact Finset.subset_union_left

  /-- The finite set `E_τ` of well-formed erased boundary environments. -/
  def environments (alphabet : TypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.environmentActions.powerset.biUnion fun immediate =>
        (alphabet.environmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  theorem environment_immediate_avoids_interface
      {alphabet : TypeAlphabet} {environment : TypeEnvironment}
      (hAlphabet : alphabet.WellFormed)
      (hEnvironment : environment ∈ alphabet.environments) :
      ∀ action ∈ environment.immediate,
        action.1 ∉ alphabet.interface := by
    simp only [environments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with rfl | ⟨immediate, hImmediate, future, _, rfl⟩
    · simp [TypeEnvironment.tock]
    · intro action hAction hInterface
      have hEnvironmentAction := hImmediate hAction
      simp only [environmentActions, Finset.mem_image] at hEnvironmentAction
      rcases hEnvironmentAction with ⟨boundaryAction, hBoundary, hNeed⟩
      apply hAlphabet boundaryAction hBoundary
      have hMessage := congrArg Prod.fst hNeed
      simp only [typeNeed] at hMessage
      rw [hMessage]
      exact hInterface

  /-- Environments used internally before a parallel constructor hides `I`. -/
  def localEnvironments (alphabet : TypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.localEnvironmentActions.powerset.biUnion fun immediate =>
        (alphabet.localEnvironmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  theorem environments_subset_localEnvironments (alphabet : TypeAlphabet) :
      alphabet.environments ⊆ alphabet.localEnvironments := by
    intro environment hEnvironment
    simp only [environments, localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image] at hEnvironment ⊢
    rcases hEnvironment with hTock | ⟨immediate, hImmediate, future,
      hFuture, rfl⟩
    · exact Or.inl hTock
    · right
      refine ⟨immediate, ?_, future, ?_, rfl⟩
      · exact hImmediate.trans
          (environmentActions_subset_localEnvironmentActions alphabet)
      · intro action hAction
        have hInEnvironment := hFuture hAction
        simp only [Finset.mem_sdiff] at hInEnvironment ⊢
        exact ⟨(environmentActions_subset_localEnvironmentActions alphabet)
          hInEnvironment.1, hInEnvironment.2⟩

  theorem environment_wellFormed {alphabet : TypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.environments) :
      environment.WellFormed := by
    simp only [environments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
    · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
    · constructor
      · simp
      · intro _
        change immediate ∩ future = ∅
        rw [← Finset.disjoint_iff_inter_eq_empty]
        apply Finset.disjoint_left.mpr
        intro action hImmediate hFutureMember
        have hAvailable := hFuture hFutureMember
        simp only [Finset.mem_sdiff] at hAvailable
        exact hAvailable.2 hImmediate

  /-- The fixed observations from which non-clock labels are formed. -/
  def observations (alphabet : TypeAlphabet) : Finset TypeObservation :=
    alphabet.boundary.image (fun action =>
      TypeObservation.message action.1 action.2) ∪
    alphabet.interface.image TypeObservation.resolved ∪
    alphabet.progress.image TypeObservation.progress ∪
    alphabet.fair.biUnion (fun bid =>
      {TypeObservation.fair bid false, TypeObservation.fair bid true})

  def localObservations (alphabet : TypeAlphabet) : Finset TypeObservation :=
    alphabet.localActions.image (fun action =>
      TypeObservation.message action.1 action.2) ∪
    alphabet.interface.image TypeObservation.resolved ∪
    alphabet.progress.image TypeObservation.progress ∪
    alphabet.fair.biUnion (fun bid =>
      {TypeObservation.fair bid false, TypeObservation.fair bid true})

  /-- `Lab_τ = 2^(Label(τ)) ∪ {#}`; the empty subset is epsilon. -/
  def labels (alphabet : TypeAlphabet) : Finset TypeLabel :=
    alphabet.observations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

  def localLabels (alphabet : TypeAlphabet) : Finset TypeLabel :=
    alphabet.localObservations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

  /-- `Offer_τ`: offers exposed outside this type are boundary actions. -/
  def offerSets (alphabet : TypeAlphabet) : Finset (Finset BareMessage) :=
    alphabet.boundary.powerset

  def localOfferSets (alphabet : TypeAlphabet) : Finset (Finset BareMessage) :=
    alphabet.localActions.powerset

  def offerSummaries (alphabet : TypeAlphabet) : Finset TypeOfferSummary :=
    alphabet.offerSets.biUnion fun current =>
      alphabet.offerSets.image fun future =>
        { current := current, future := future }

  /-
  Validate a type against a previously chosen alphabet.  This checks use of
  the signature; it does not synthesize or enlarge the signature from syntax.
  -/
  mutual
    /-- Check that a type uses only declarations from its fixed alphabet. -/
    def Supports (alphabet : TypeAlphabet) : PactType → Prop
      | .message msg dir =>
          (msg, dir) ∈ alphabet.boundary ∨ msg ∈ alphabet.interface
      | .progress pid => pid ∈ alphabet.progress
      | .tock | .skip | .var _ => True
      | .choice left right | .seq left right =>
          alphabet.Supports left ∧ alphabet.Supports right
      | .fairChoice bid left right =>
          bid ∈ alphabet.fair ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .par left right interface =>
          interface ⊆ alphabet.interface ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .recur _ body => alphabet.Supports body
      | .xoffer elseType branches | .offer elseType branches =>
          alphabet.Supports elseType ∧ alphabet.SupportsBranches branches
    termination_by processType => sizeOf processType

    def SupportsBranches (alphabet : TypeAlphabet) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (action, processType) :: rest =>
          (action ∈ alphabet.boundary ∨ action.1 ∈ alphabet.interface) ∧
            alphabet.Supports processType ∧ alphabet.SupportsBranches rest
    termination_by branches => sizeOf branches
    decreasing_by
      all_goals
        simp_wf
        omega
  end

end TypeAlphabet

mutual
  theorem TypeAlphabet.Supports.parallelInterfaces_subset
      {alphabet : TypeAlphabet} {processType : PactType}
      (hSupports : alphabet.Supports processType) :
      processType.ParallelInterfaces ⊆ alphabet.interface := by
    cases processType with
    | message msg dir => simp [PactType.ParallelInterfaces]
    | progress pid => simp [PactType.ParallelInterfaces]
    | tock => simp [PactType.ParallelInterfaces]
    | skip => simp [PactType.ParallelInterfaces]
    | var name => simp [PactType.ParallelInterfaces]
    | recur name body =>
        simpa [PactType.ParallelInterfaces] using
          TypeAlphabet.Supports.parallelInterfaces_subset hSupports
    | choice left right | seq left right =>
        simp only [TypeAlphabet.Supports] at hSupports
        simp only [PactType.ParallelInterfaces, Finset.union_subset_iff]
        exact ⟨TypeAlphabet.Supports.parallelInterfaces_subset hSupports.1,
          TypeAlphabet.Supports.parallelInterfaces_subset hSupports.2⟩
    | fairChoice bid left right =>
        simp only [TypeAlphabet.Supports] at hSupports
        simp only [PactType.ParallelInterfaces, Finset.union_subset_iff]
        exact ⟨TypeAlphabet.Supports.parallelInterfaces_subset hSupports.2.1,
          TypeAlphabet.Supports.parallelInterfaces_subset hSupports.2.2⟩
    | par left right interface =>
        simp only [TypeAlphabet.Supports] at hSupports
        simp only [PactType.ParallelInterfaces, Finset.union_subset_iff]
        exact ⟨⟨hSupports.1,
          TypeAlphabet.Supports.parallelInterfaces_subset hSupports.2.1⟩,
          TypeAlphabet.Supports.parallelInterfaces_subset hSupports.2.2⟩
    | xoffer elseType branches | offer elseType branches =>
        simp only [TypeAlphabet.Supports] at hSupports
        simp only [PactType.ParallelInterfaces, Finset.union_subset_iff]
        exact ⟨TypeAlphabet.Supports.parallelInterfaces_subset hSupports.1,
          hSupports.2.parallelBranchInterfaces_subset⟩
  termination_by sizeOf processType

  theorem TypeAlphabet.SupportsBranches.parallelBranchInterfaces_subset
      {alphabet : TypeAlphabet}
      {branches : List (BareMessage × PactType)}
      (hSupports : alphabet.SupportsBranches branches) :
      PactType.ParallelBranchInterfaces branches ⊆ alphabet.interface := by
    cases branches with
    | nil => simp [PactType.ParallelBranchInterfaces]
    | cons branch rest =>
        rcases branch with ⟨action, processType⟩
        simp only [TypeAlphabet.SupportsBranches] at hSupports
        simp only [PactType.ParallelBranchInterfaces,
          Finset.union_subset_iff]
        exact ⟨hSupports.2.1.parallelInterfaces_subset,
          hSupports.2.2.parallelBranchInterfaces_subset⟩
  termination_by sizeOf branches
decreasing_by
  all_goals
    try subst processType
    try subst branches
    subst_vars
    simp_all
    omega
end

/-- Canonical local environment universe used only to evaluate the paper's
same-cycle future menu.  Treating every mentioned message identifier as local
provides both polarities and makes the analysis independent of a caller's
possibly larger exported alphabet.  The raw constructor fragment does not
filter progress or fair labels, so those fields are immaterial here. -/
private def futureAnalysisAlphabet (processType : PactType) : TypeAlphabet :=
  { boundary := ∅
    interface := processType.DeclaredMessageIds
    progress := processType.DeclaredProgressIds
    fair := processType.DeclaredFairIds }

/-- One letter of the decorated transition alphabet `Σ_τ`. -/
structure TypeAutomatonSymbol : Type where
  environment : TypeEnvironment
  label : TypeLabel
  offers : TypeOfferSummary
  deriving DecidableEq

def TypeAlphabet.transitionAlphabet
    (alphabet : TypeAlphabet) : Finset TypeAutomatonSymbol :=
  alphabet.environments.biUnion fun environment =>
    alphabet.labels.biUnion fun label =>
      alphabet.offerSummaries.image fun offers =>
        { environment := environment, label := label, offers := offers }

/-! ### Construction representation -/

/--
Tagged States

* `root` and `final` are the two distinguished states used by atomic types.
* `child i q` injects state `q` into child automaton `i` of a sum/sequence.
* `pair q₁ q₂` is a state of a synchronized parallel product.
-/
inductive TypeAutomatonState : Type where
  /-- Fresh entry state introduced by a constructor. -/
  | root
  /-- Completed state used by atomic constructors. -/
  | final
  /-- State `state` embedded into child automaton `index`. -/
  | child : Nat → TypeAutomatonState → TypeAutomatonState
  /-- Product state containing one state from each parallel component. -/
  | pair : TypeAutomatonState → TypeAutomatonState → TypeAutomatonState
  deriving DecidableEq

/--
Visible labels become part of the final automaton. Variable labels are
temporary back-edge markers consumed when compiling the matching binder.
-/
inductive AutomatonConstructionLabel : Type where
  | visible : TypeLabel → AutomatonConstructionLabel
  | variable : String → AutomatonConstructionLabel
  deriving DecidableEq

/--
How to fill an edge's future-offer field.

* `explicit offers` copies a future set already computed by a child.
* `at state removed` computes `OF(state) \ removed` after the parent graph is
  complete. This is what prevents a constructor from inspecting a partial
  automaton during recursive construction.
-/
inductive FutureSpec : Type where
  | explicit : Finset BareMessage → FutureSpec
  | at : TypeAutomatonState → Finset BareMessage → FutureSpec
  deriving DecidableEq

/-- An edge whose future-offer field has not necessarily been resolved yet. -/
structure PendingAutomatonEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : FutureSpec
  target : TypeAutomatonState
  deriving DecidableEq

/--
A constructor fragment whose future references remain symbolic.

Keeping `FutureSpec.at` references unresolved is essential for recursion:
an enclosing binder can add a back-edge, changing the future offers reachable
from a child state.  Resolution therefore happens only when an operation
actually needs decorated edges, and once more for the final automaton.
-/
structure AutomatonFragment : Type where
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  /-- States whose represented semantic residual is literally `skip`. -/
  skipping : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

/-- Every symbolic future reference in a fragment points to a declared state. -/
def AutomatonFragment.FutureTargetsInStates
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ target removed,
    edge.future = .at target removed → target ∈ fragment.states

/-- A constructor edge after its future-offer field has been computed. -/
structure AutomatonFragmentEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : Finset BareMessage
  target : TypeAutomatonState
  deriving DecidableEq

/-- Complete state/edge graph used while resolving pending future fields. -/
structure PendingAutomaton : Type where
  states : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

namespace AutomatonConstructionLabel

  /-- Treat a temporary recursion edge as silent for local synchronization. -/
  def semantic : AutomatonConstructionLabel → TypeLabel
    | .visible label => label
    | .variable _ => TypeLabel.silent

  /-- Combine product labels while preserving an unresolved recursion marker. -/
  def combine (interface : Interface)
      (left right : AutomatonConstructionLabel) : AutomatonConstructionLabel :=
    match left, right with
    | .variable name, _ => .variable name
    | _, .variable name => .variable name
    | .visible leftLabel, .visible rightLabel =>
        .visible (TypeLabel.combine interface leftLabel rightLabel)

end AutomatonConstructionLabel

/-! ### Future-offer computation -/

namespace PendingAutomaton

  /-- States whose offers are referenced by outgoing edges from `state`. -/
  def referencedStates (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      -- A clock transition ends the current cycle.  Its decorated `future`
      -- field describes the offers after taking that transition, but those
      -- offers must not be used while computing the menu still reachable
      -- from `state` in the current cycle.
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        match edge.future with
        | .explicit _ => ∅
        | .at target _ => {target}

  /-- Offers already visible directly on outgoing edges from `state`. -/
  def offersAt (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset BareMessage :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        edge.current ∪
          match edge.future with
          | .explicit offers => offers
          | .at _ _ => ∅

  private def futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
    reached ∪ reached.biUnion automaton.referencedStates

  private def futureReachableAux (automaton : PendingAutomaton) :
      Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
    | 0, reached => reached
    | fuel + 1, reached =>
        futureReachableAux automaton fuel (futureStep automaton reached)

  /-- Every symbolic reference in the graph points to a declared state. -/
  def ReferencesClosed (automaton : PendingAutomaton) : Prop :=
    ∀ state ∈ automaton.states,
      automaton.referencedStates state ⊆ automaton.states

  theorem referencesClosed_of_futureTargetsInStates
      (fragment : AutomatonFragment)
      (hTargets : fragment.FutureTargetsInStates) :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    intro state _ target hTarget
    simp only [referencedStates, Finset.mem_biUnion, Finset.mem_filter]
      at hTarget
    rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
    by_cases hClock : edge.label.semantic = TypeLabel.tock
    · simp [hClock] at hFuture
    · simp only [hClock, if_false] at hFuture
      cases hSpec : edge.future with
      | explicit offers => simp [hSpec] at hFuture
      | «at» referenced removed =>
          simp only [hSpec, Finset.mem_singleton] at hFuture
          subst target
          exact hTargets edge hEdge referenced removed hSpec

  private theorem subset_futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureStep reached := by
    exact Finset.subset_union_left

  private theorem futureStep_subset_states
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hReached : reached ⊆ automaton.states) :
      automaton.futureStep reached ⊆ automaton.states := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState
    rcases hState with hState | ⟨source, hSource, hReference⟩
    · exact hReached hState
    · exact hClosed source (hReached hSource) hReference

  private theorem futureReachableAux_fixed_of_futureStep_eq
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hFixed : automaton.futureStep reached = reached) :
      ∀ fuel, futureReachableAux automaton fuel reached = reached := by
    intro fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
        simp only [futureReachableAux, hFixed]
        exact ih

  private theorem futureStep_futureReachableAux
      (automaton : PendingAutomaton) : ∀ fuel reached,
      automaton.futureStep (futureReachableAux automaton fuel reached) =
        futureReachableAux automaton fuel (automaton.futureStep reached) := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        exact ih (automaton.futureStep reached)

  private theorem futureReachableAux_succ
      (automaton : PendingAutomaton) (fuel : Nat)
      (reached : Finset TypeAutomatonState) :
      futureReachableAux automaton (fuel + 1) reached =
        automaton.futureStep (futureReachableAux automaton fuel reached) := by
    simp only [futureReachableAux]
    exact (futureStep_futureReachableAux automaton fuel reached).symm

  /-- If `k` is at least the number of states still missing from `reached`,
  `k` saturation rounds reach a fixed point. -/
  private theorem futureReachableAux_fixed_after_missing
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed) :
      ∀ k reached,
        reached ⊆ automaton.states →
        automaton.states.card ≤ reached.card + k →
        automaton.futureStep (futureReachableAux automaton k reached) =
          futureReachableAux automaton k reached := by
    intro k
    induction k with
    | zero =>
        intro reached hReached hCard
        have hEqual : reached = automaton.states := by
          exact Finset.eq_of_subset_of_card_le hReached (by simpa using hCard)
        rw [hEqual]
        apply Finset.Subset.antisymm
        · exact futureStep_subset_states automaton automaton.states hClosed
            (fun _ h => h)
        · exact subset_futureStep automaton automaton.states
    | succ k ih =>
        intro reached hReached hCard
        let next := automaton.futureStep reached
        have hNextSubset : next ⊆ automaton.states :=
          futureStep_subset_states automaton reached hClosed hReached
        by_cases hFixed : next = reached
        · have hStepFixed : automaton.futureStep reached = reached := by
            simpa [next] using hFixed
          have hAux : futureReachableAux automaton (k + 1) reached = reached := by
            simp only [futureReachableAux]
            rw [hStepFixed]
            exact futureReachableAux_fixed_of_futureStep_eq
              automaton reached hStepFixed k
          rw [hAux]
          exact hStepFixed
        · have hStrict : reached.card < next.card := by
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_subset_ne.mpr
              ⟨subset_futureStep automaton reached, Ne.symm hFixed⟩
          have hNextCard : automaton.states.card ≤ next.card + k := by
            omega
          simpa only [futureReachableAux, next] using
            ih next hNextSubset hNextCard

  /-- Saturation is stable after `|states|` rounds; running any additional
  number of rounds does not change the reached set. -/
  theorem futureReachableAux_add_card_stable
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed)
      (reached : Finset TypeAutomatonState)
      (hReached : reached ⊆ automaton.states) (extra : Nat) :
      futureReachableAux automaton (automaton.states.card + extra) reached =
        futureReachableAux automaton automaton.states.card reached := by
    have hFixed : automaton.futureStep
          (futureReachableAux automaton automaton.states.card reached) =
        futureReachableAux automaton automaton.states.card reached := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · exact hReached
      · omega
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [Nat.add_succ,
          futureReachableAux_succ automaton (automaton.states.card + extra),
          ih, hFixed]

  /-- Pointwise preservation of references lifts to every finite saturation
  depth.  This is the graph-theoretic core used by constructor state tags. -/
  theorem futureReachableAux_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        parent.referencedStates (embed state) =
          (child.referencedStates state).image embed) :
      ∀ fuel reached,
        parent.futureReachableAux fuel (reached.image embed) =
          (child.futureReachableAux fuel reached).image embed := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        have hStep : parent.futureStep (reached.image embed) =
            (child.futureStep reached).image embed := by
          apply Finset.Subset.antisymm
          · intro target hTarget
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hTarget
            rcases hTarget with hDirect | ⟨source, hSource, hTarget⟩
            · rcases Finset.mem_image.mp hDirect with ⟨state, hState, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨state, Finset.mem_union_left _ hState, rfl⟩
            · rcases Finset.mem_image.mp hSource with ⟨state, hState, rfl⟩
              rw [hReferences] at hTarget
              rcases Finset.mem_image.mp hTarget with
                ⟨referenced, hReferenced, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨referenced, Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨state, hState, hReferenced⟩), rfl⟩
          · intro target hTarget
            rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hState ⊢
            rcases hState with hDirect | ⟨source, hSource, hReferenced⟩
            · exact Or.inl (Finset.mem_image.mpr ⟨state, hDirect, rfl⟩)
            · right
              refine ⟨embed source,
                Finset.mem_image.mpr ⟨source, hSource, rfl⟩, ?_⟩
              rw [hReferences]
              exact Finset.mem_image.mpr ⟨state, hReferenced, rfl⟩
        rw [hStep]
        exact ih (child.futureStep reached)

  /-- Offers unioned over an embedded reached set are preserved whenever
  `offersAt` is preserved pointwise by the embedding. -/
  theorem biUnion_offersAt_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hOffers : ∀ state,
        parent.offersAt (embed state) = child.offersAt state)
      (reached : Finset TypeAutomatonState) :
      (reached.image embed).biUnion parent.offersAt =
        reached.biUnion child.offersAt := by
    ext action
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨state, hState, rfl⟩, hAction⟩
      rw [hOffers] at hAction
      exact ⟨state, hState, hAction⟩
    · rintro ⟨state, hState, hAction⟩
      refine ⟨embed state, ⟨state, hState, rfl⟩, ?_⟩
      rw [hOffers]
      exact hAction

  /-- Saturate references for at most `|Q|` rounds. -/
  def futureReachable (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    futureReachableAux automaton automaton.states.card {state}

  /-- If a state has no same-cycle future references, saturation cannot leave
  that state. -/
  theorem futureReachable_eq_singleton_of_referencedStates_eq_empty
      (automaton : PendingAutomaton) (state : TypeAutomatonState)
      (hReferences : automaton.referencedStates state = ∅) :
      automaton.futureReachable state = {state} := by
    unfold futureReachable
    have hAux : ∀ fuel,
        futureReachableAux automaton fuel {state} = {state} := by
      intro fuel
      induction fuel with
      | zero => rfl
      | succ fuel ih =>
          change futureReachableAux automaton fuel
            (({state} : Finset TypeAutomatonState) ∪
              ({state} : Finset TypeAutomatonState).biUnion
                automaton.referencedStates) = {state}
          simp [hReferences, ih]
    exact hAux automaton.states.card

  private theorem futureStep_mono (automaton : PendingAutomaton)
      {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureStep smaller ⊆ automaton.futureStep larger := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState ⊢
    rcases hState with hDirect | ⟨source, hSource, hReference⟩
    · exact Or.inl (hSubset hDirect)
    · exact Or.inr ⟨source, hSubset hSource, hReference⟩

  private theorem futureReachableAux_mono (automaton : PendingAutomaton)
      (fuel : Nat) {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureReachableAux fuel smaller ⊆
        automaton.futureReachableAux fuel larger := by
    induction fuel generalizing smaller larger with
    | zero => exact hSubset
    | succ fuel ih =>
        exact ih (futureStep_mono automaton hSubset)

  private theorem subset_futureReachableAux (automaton : PendingAutomaton)
      (fuel : Nat) (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureReachableAux fuel reached := by
    induction fuel generalizing reached with
    | zero => exact fun _ h => h
    | succ fuel ih =>
        exact (subset_futureStep automaton reached).trans
          (ih (automaton.futureStep reached))

  /-- Saturated same-cycle reachability unfolds by one symbolic-reference
  step.  This is the finite-graph fixed-point equation behind constructor
  roots: a state reaches itself and everything reachable from each of its
  immediate same-cycle references. -/
  theorem futureReachable_unfold (automaton : PendingAutomaton)
      (state : TypeAutomatonState) (hClosed : automaton.ReferencesClosed)
      (hState : state ∈ automaton.states) :
      automaton.futureReachable state =
        {state} ∪ (automaton.referencedStates state).biUnion
          automaton.futureReachable := by
    let closure := automaton.futureReachable state
    let unfolded := ({state} : Finset TypeAutomatonState) ∪
      (automaton.referencedStates state).biUnion automaton.futureReachable
    have hClosureFixed : automaton.futureStep closure = closure := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [closure, futureReachable] using hState
      · omega
    have hStateClosure : state ∈ closure := by
      apply subset_futureReachableAux automaton automaton.states.card {state}
      simp [closure, futureReachable]
    have hReferenceClosure : ∀ reference,
        reference ∈ automaton.referencedStates state →
          automaton.futureReachable reference ⊆ closure := by
      intro reference hReference target hTarget
      have hReferenceState : reference ∈ automaton.states :=
        hClosed state hState hReference
      have hReferenceInClosure : reference ∈ closure := by
        rw [← hClosureFixed]
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨state, hStateClosure, hReference⟩)
      have hSingletonSubset : ({reference} : Finset TypeAutomatonState) ⊆
          closure := by
        simpa using hReferenceInClosure
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hSingletonSubset
      have hClosureStable : automaton.futureReachableAux
          automaton.states.card closure = closure := by
        exact futureReachableAux_fixed_of_futureStep_eq automaton closure
          hClosureFixed automaton.states.card
      rw [hClosureStable] at hMonotone
      exact hMonotone hTarget
    have hUnfoldedSubset : unfolded ⊆ closure := by
      intro target hTarget
      simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion] at hTarget
      rcases hTarget with rfl | ⟨reference, hReference, hReachable⟩
      · exact hStateClosure
      · exact hReferenceClosure reference hReference hReachable
    have hUnfoldedFixed : automaton.futureStep unfolded = unfolded := by
      apply Finset.Subset.antisymm
      · intro target hTarget
        simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hTarget
        rcases hTarget with hDirect | ⟨source, hSource, hReference⟩
        · exact hDirect
        · simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hSource ⊢
          rcases hSource with rfl | ⟨first, hFirst, hSourceReachable⟩
          · exact Or.inr ⟨target, hReference,
              subset_futureReachableAux automaton automaton.states.card
                {target} (by simpa)⟩
          · have hFirstState : first ∈ automaton.states :=
              hClosed state hState hFirst
            have hFirstFixed : automaton.futureStep
                (automaton.futureReachable first) =
                automaton.futureReachable first := by
              apply futureReachableAux_fixed_after_missing automaton hClosed
              · simpa [futureReachable] using hFirstState
              · omega
            have hTargetReachable : target ∈ automaton.futureReachable first := by
              rw [← hFirstFixed]
              exact Finset.mem_union_right _
                (Finset.mem_biUnion.mpr
                  ⟨source, hSourceReachable, hReference⟩)
            exact Or.inr ⟨first, hFirst, hTargetReachable⟩
      · exact subset_futureStep automaton unfolded
    apply Finset.Subset.antisymm
    · have hStart : ({state} : Finset TypeAutomatonState) ⊆ unfolded := by
        exact Finset.subset_union_left
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hStart
      have hUnfoldedStable : automaton.futureReachableAux
          automaton.states.card unfolded = unfolded :=
        futureReachableAux_fixed_of_futureStep_eq automaton unfolded
          hUnfoldedFixed automaton.states.card
      simpa [closure, futureReachable, hUnfoldedStable] using hMonotone
    · exact hUnfoldedSubset

  /-- If an embedding preserves every child reference as a parent reference,
  every state reachable in the child maps to a state reachable in the parent.
  Unlike the equality theorem used for isolated tagged subgraphs, this
  one-sided form permits the parent to add references (for example, a
  sequence bridge out of a completed left state). -/
  theorem futureReachable_image_subset_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        (child.referencedStates state).image embed ⊆
          parent.referencedStates (embed state))
      (hParentClosed : parent.ReferencesClosed)
      (state : TypeAutomatonState) (hParentState : embed state ∈ parent.states) :
      (child.futureReachable state).image embed ⊆
        parent.futureReachable (embed state) := by
    let parentReach := parent.futureReachable (embed state)
    have hParentFixed : parent.futureStep parentReach = parentReach := by
      apply futureReachableAux_fixed_after_missing parent hParentClosed
      · simpa [parentReach, futureReachable] using hParentState
      · omega
    have hLiftAux : ∀ fuel reached,
        reached.image embed ⊆ parentReach →
          (child.futureReachableAux fuel reached).image embed ⊆
            parentReach := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih (child.futureStep reached)
          intro target hTarget
          rcases Finset.mem_image.mp hTarget with ⟨childTarget,
            hChildTarget, rfl⟩
          simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
            at hChildTarget
          rcases hChildTarget with hDirect | ⟨childSource, hSource,
              hReference⟩
          · exact hReached (Finset.mem_image.mpr
              ⟨childTarget, hDirect, rfl⟩)
          · have hMappedSource : embed childSource ∈ parentReach :=
              hReached (Finset.mem_image.mpr ⟨childSource, hSource, rfl⟩)
            have hMappedReference : embed childTarget ∈
                parent.referencedStates (embed childSource) :=
              hReferences childSource
                (Finset.mem_image.mpr ⟨childTarget, hReference, rfl⟩)
            rw [← hParentFixed]
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨embed childSource, hMappedSource, hMappedReference⟩)
    unfold futureReachable
    apply hLiftAux child.states.card {state}
    intro target hTarget
    rcases Finset.mem_image.mp hTarget with ⟨source, hSource, rfl⟩
    simp only [Finset.mem_singleton] at hSource
    subst source
    exact subset_futureReachableAux parent parent.states.card {embed state}
      (by simp)

  /-- A saturated future closure contains the closure starting from any state
  it already contains. -/
  theorem futureReachable_subset_of_mem
      (automaton : PendingAutomaton) (root source : TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed) (hRoot : root ∈ automaton.states)
      (hSource : source ∈ automaton.futureReachable root) :
      automaton.futureReachable source ⊆ automaton.futureReachable root := by
    have hFixed : automaton.futureStep (automaton.futureReachable root) =
        automaton.futureReachable root := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [futureReachable] using hRoot
      · omega
    have hStart : ({source} : Finset TypeAutomatonState) ⊆
        automaton.futureReachable root := by
      simpa using hSource
    have hMonotone := futureReachableAux_mono automaton
      automaton.states.card hStart
    have hStable : automaton.futureReachableAux automaton.states.card
        (automaton.futureReachable root) = automaton.futureReachable root :=
      futureReachableAux_fixed_of_futureStep_eq automaton
        (automaton.futureReachable root) hFixed automaton.states.card
    change automaton.futureReachableAux automaton.states.card {source} ⊆
      automaton.futureReachable root
    rw [← hStable]
    exact hMonotone

  /-- Any set containing the start and closed under immediate symbolic
  references contains the finite saturated future-reachability set. -/
  theorem futureReachable_subset_of_reference_closed
      (automaton : PendingAutomaton) (state : TypeAutomatonState)
      (closedSet : Finset TypeAutomatonState)
      (hStart : state ∈ closedSet)
      (hClosedSet : ∀ source ∈ closedSet,
        automaton.referencedStates source ⊆ closedSet) :
      automaton.futureReachable state ⊆ closedSet := by
    have hAux : ∀ fuel reached, reached ⊆ closedSet →
        automaton.futureReachableAux fuel reached ⊆ closedSet := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih (automaton.futureStep reached)
          intro target hTarget
          simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
            at hTarget
          rcases hTarget with hDirect | ⟨source, hSource, hReference⟩
          · exact hReached hDirect
          · exact hClosedSet source (hReached hSource) hReference
    unfold futureReachable
    apply hAux automaton.states.card {state}
    simpa using hStart

end PendingAutomaton

/--
Compute `OF(q)` on a complete pending automaton.

Starting at `q`, follow every `FutureSpec.at` reference and union the current
and explicit future offers encountered. At most `|Q|` rounds are needed because
revisiting a finite state cannot expose a new state.
-/
def computeFuture (automaton : PendingAutomaton)
    (state : TypeAutomatonState) : Finset BareMessage :=
  (automaton.futureReachable state).biUnion automaton.offersAt

/-- `computeFuture` is the least closed future menu: collect the offers stored
at the current state, then union the complete menus of every immediate
same-cycle symbolic reference. -/
theorem computeFuture_unfold
    (automaton : PendingAutomaton) (state : TypeAutomatonState)
    (hClosed : automaton.ReferencesClosed)
    (hState : state ∈ automaton.states) :
    computeFuture automaton state =
      automaton.offersAt state ∪
        (automaton.referencedStates state).biUnion
          (computeFuture automaton) := by
  rw [computeFuture, automaton.futureReachable_unfold state hClosed hState]
  ext action
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨reached, hReached, hOffer⟩
    rcases hReached with rfl | ⟨reference, hReference, hReachable⟩
    · exact Or.inl hOffer
    · apply Or.inr
      refine ⟨reference, hReference, ?_⟩
      change action ∈
        (automaton.futureReachable reference).biUnion automaton.offersAt
      exact Finset.mem_biUnion.mpr ⟨reached, hReachable, hOffer⟩
  · rintro (hOffer | ⟨reference, hReference, hFuture⟩)
    · exact ⟨state, Or.inl rfl, hOffer⟩
    · change action ∈
          (automaton.futureReachable reference).biUnion automaton.offersAt
        at hFuture
      rcases Finset.mem_biUnion.mp hFuture with
        ⟨reached, hReachable, hOffer⟩
      exact ⟨reached, Or.inr ⟨reference, hReference, hReachable⟩, hOffer⟩

/-- A constructor embedding preserves `computeFuture` once it preserves the
local reference and offer observations.  A larger parent state set merely
runs extra saturation rounds, which are harmless by finite stabilization. -/
theorem computeFuture_eq_of_embedding
    (child parent : PendingAutomaton)
    (embed : TypeAutomatonState → TypeAutomatonState)
    (hReferences : ∀ state,
      parent.referencedStates (embed state) =
        (child.referencedStates state).image embed)
    (hOffers : ∀ state,
      parent.offersAt (embed state) = child.offersAt state)
    (hClosed : child.ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ child.states)
    (hCard : child.states.card ≤ parent.states.card) :
    computeFuture parent (embed state) = computeFuture child state := by
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hCard
  unfold computeFuture PendingAutomaton.futureReachable
  rw [show ({embed state} : Finset TypeAutomatonState) =
      ({state} : Finset TypeAutomatonState).image embed by simp]
  rw [PendingAutomaton.futureReachableAux_image_of_embedding
    child parent embed hReferences]
  rw [hExtra,
    child.futureReachableAux_add_card_stable hClosed {state} (by
      simpa using hState) extra]
  exact PendingAutomaton.biUnion_offersAt_image_of_embedding
    child parent embed hOffers _

/-- With no outgoing same-cycle reference, future resolution is exactly the
offers stored directly at the state. -/
theorem computeFuture_eq_offersAt_of_referencedStates_eq_empty
    (automaton : PendingAutomaton) (state : TypeAutomatonState)
    (hReferences : automaton.referencedStates state = ∅) :
    computeFuture automaton state = automaton.offersAt state := by
  rw [computeFuture,
    automaton.futureReachable_eq_singleton_of_referencedStates_eq_empty
      state hReferences]
  simp

/-- A graph containing only explicit future fields has no symbolic future
references.  Parallel products have this form after their child decorations
have been resolved. -/
theorem PendingAutomaton.referencedStates_eq_empty_of_all_explicit
    (automaton : PendingAutomaton)
    (hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers)
    (state : TypeAutomatonState) :
    automaton.referencedStates state = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  obtain ⟨offers, hOffers⟩ := hExplicit edge hEdge
  simp [hOffers] at hFuture

/-- Consequently, resolution on an all-explicit graph only unions the offers
stored directly on outgoing edges. -/
theorem computeFuture_eq_offersAt_of_all_explicit
    (automaton : PendingAutomaton)
    (hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers)
    (state : TypeAutomatonState) :
    computeFuture automaton state = automaton.offersAt state := by
  apply computeFuture_eq_offersAt_of_referencedStates_eq_empty
  exact automaton.referencedStates_eq_empty_of_all_explicit hExplicit state

/-- Regression for the clock boundary in future resolution.  Although the
edge out of `root` is decorated with the offers available at `final`, those
offers belong to the next cycle and are therefore not reachable from `root`
for the purpose of `OF(root)`.  This is the graph shape produced by the left
side of `tock ; a!`. -/
theorem computeFuture_stops_at_clock_regression :
    let action : BareMessage := ("a", .send)
    let clockEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .tock
        label := .visible .tock
        current := ∅
        future := .at .final ∅
        target := .final }
    let messageEdge : PendingAutomatonEdge :=
      { source := .final
        environment := .empty
        label := .visible .silent
        current := {action}
        future := .explicit ∅
        target := .final }
    let graph : PendingAutomaton :=
      { states := {.root, .final}, edges := {clockEdge, messageEdge} }
    computeFuture graph .root = ∅ := by
  native_decide

/-- A recursion marker has no future menu until its binder installs the
back-edge.  Resolving a child fragment before that installation therefore
loses information: this is the small graph phenomenon that constructor
combinators (notably parallel product) must preserve symbolically. -/
theorem computeFuture_changes_when_recursion_backedge_is_installed :
    let action : BareMessage := ("a", .send)
    let variableEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .empty
        label := .variable "x"
        current := ∅
        future := .explicit ∅
        target := .final }
    let backEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .empty
        label := .visible .silent
        current := ∅
        future := .at .final ∅
        target := .final }
    let messageEdge : PendingAutomatonEdge :=
      { source := .final
        environment := .empty
        label := .visible .silent
        current := {action}
        future := .explicit ∅
        target := .final }
    let openGraph : PendingAutomaton :=
      { states := {.root, .final}, edges := {variableEdge, messageEdge} }
    let closedGraph : PendingAutomaton :=
      { states := {.root, .final}, edges := {backEdge, messageEdge} }
    computeFuture openGraph .root = ∅ ∧
      computeFuture closedGraph .root = {action} := by
  native_decide

/-- Package a constructor graph without resolving its future references. -/
private def finishAutomatonFragment
    (states : Finset TypeAutomatonState) (initial : TypeAutomatonState)
    (accepting skipping : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) : AutomatonFragment :=
  { states := states
    initial := initial
    accepting := accepting
    skipping := skipping
    edges := edges }

/-- Resolve future fields against all states and edges currently in a fragment. -/
private def resolvedAutomatonEdges
    (automaton : AutomatonFragment) : Finset AutomatonFragmentEdge :=
  let pending : PendingAutomaton :=
    { states := automaton.states, edges := automaton.edges }
  automaton.edges.image fun edge =>
      let resolvedFuture :=
        match edge.future with
        | .explicit offers => offers
        | .at state removed => computeFuture pending state \ removed
      { source := edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := resolvedFuture
        target := edge.target }

private def childState (index : Nat) (state : TypeAutomatonState) :
    TypeAutomatonState := .child index state

private def childStates (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.states.image (childState index)

private def childAccepting (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.accepting.image (childState index)

private def childSkipping (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.skipping.image (childState index)

private def childFutureSpec (index : Nat) : FutureSpec → FutureSpec
  | .explicit offers => .explicit offers
  | .at state removed => .at (childState index state) removed

private def childPendingEdge (index : Nat)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState index edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := childFutureSpec index edge.future
    target := childState index edge.target }

private def childPendingEdges (index : Nat) (automaton : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  automaton.edges.image (childPendingEdge index)

/-! ### Interface operations for parallel products -/

/-- Remove offers whose message identifier belongs to the internal interface. -/
private def hideOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

/-- Keep only offers whose message identifier belongs to the interface. -/
private def interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Hide the interface from the union of two component environments. -/
private def combineAutomatonEnvironment (interface : Interface)
    (left right : TypeEnvironment) : TypeEnvironment :=
  if left.clock && right.clock then TypeEnvironment.tock
  else
    { immediate := hideOffers interface (left.immediate ∪ right.immediate)
      future := hideOffers interface (left.future ∪ right.future)
      clock := false }

/-- A local-environment witness may choose a different target and offer
summary from the actual component transition, but it must start at the same
residual under the same environment and semantic label. -/
private def matchesAutomatonOfferWitness
    (actual witness : AutomatonFragmentEdge) : Prop :=
  witness.source = actual.source ∧
    witness.environment = actual.environment ∧
    witness.label.semantic = actual.label.semantic

/-- Exact automaton counterpart of the two `LocalTypeEnvironment` premises.

The actual edges determine the product target and its exposed current/future
summary.  The two witness edges justify the sibling-local environments; this
mirrors the semantic rule's existential sibling target and offer summary.
Using the equations verbatim is important because the future equation removes
the local immediate set and therefore does not require current/future
disjointness. -/
private def syncAutomatonEdgeWitnesses (interface : Interface)
    (left right leftWitness rightWitness : AutomatonFragmentEdge) : Prop :=
  let outer := combineAutomatonEnvironment interface
    left.environment right.environment
  matchesAutomatonOfferWitness left leftWitness ∧
    matchesAutomatonOfferWitness right rightWitness ∧
    (if left.environment.clock then
      left.environment = TypeEnvironment.tock ∧
        right.environment = TypeEnvironment.tock
    else
      left.environment.clock = false ∧
        right.environment.clock = false ∧
        left.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface rightWitness.current ∧
        left.environment.future =
          (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
            left.environment.immediate ∧
        right.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface leftWitness.current ∧
        right.environment.future =
          (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
            right.environment.immediate) ∧
    TypeLabel.Sync interface left.label.semantic right.label.semantic

/-- Component edges synchronize when suitable local-environment offer
witnesses occur in their respective resolved edge relations. -/
private def syncAutomatonEdges (interface : Interface)
    (leftEdges rightEdges : Finset AutomatonFragmentEdge)
    (left right : AutomatonFragmentEdge) : Prop :=
  ∃ leftWitness ∈ leftEdges, ∃ rightWitness ∈ rightEdges,
    syncAutomatonEdgeWitnesses interface left right leftWitness rightWitness

/-- Regression: interface synchronization alone cannot pair edges that see
different boundary environments. -/
theorem syncAutomatonEdges_rejects_boundary_environment_mismatch :
    let action : BareMessage := ("b", .send)
    let left : AutomatonFragmentEdge :=
      { source := .root
        environment :=
          { immediate := {typeNeed action}, future := ∅, clock := false }
        label := .visible (TypeLabel.message action.1 action.2)
        current := {action}
        future := ∅
        target := .final }
    let right : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := ∅
        future := ∅
        target := .root }
    ¬ syncAutomatonEdges ∅ {left} {right} left right := by
  classical
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, typeNeed]

/-- Regression for the existential local-environment reading: the actual left
edge may select the `a` branch while a distinct silent edge from the same
source/environment witnesses the `b` offer used to construct the right local
environment. -/
theorem syncAutomatonEdges_accepts_independent_offer_witness :
    let aSend : BareMessage := ("a", .send)
    let aRecv : BareMessage := ("a", .recv)
    let bSend : BareMessage := ("b", .send)
    let interface : Interface := {"a"}
    let leftEnvironment : TypeEnvironment :=
      { immediate := {aRecv}, future := ∅, clock := false }
    let leftActual : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {aSend}
        target := .child 0 .root }
    let leftWitness : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {bSend}
        target := .child 1 .root }
    let rightActual : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := {aRecv}
        future := ∅
        target := .root }
    syncAutomatonEdges interface {leftActual, leftWitness} {rightActual}
      leftActual rightActual := by
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, TypeLabel.Sync,
    TypeLabel.silent, AutomatonConstructionLabel.semantic, TypeLabel.sends,
    TypeLabel.recvs, TypeLabel.messageIdsWith]
  native_decide

/-! ### Reusable constructor combinators -/

/--
Build a recursion binder with an explicit silent header step.

The fresh root represents the binder itself. Matching variable edges inside
the tagged body are replaced by silent back-edges to the body entry, which is
the graph representation of substituting the binder at those occurrences.
-/
private def buildRecursionAutomaton (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) : AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 body
  let accepting := childAccepting 0 body
  let skipping := childSkipping 0 body
  let headerEdges : Finset PendingAutomatonEdge :=
    signature.localEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
  let bodyEdges : Finset PendingAutomatonEdge := body.edges.image fun edge =>
    if edge.label = .variable name then
      { source := childState 0 edge.source
        environment := edge.environment
        label := AutomatonConstructionLabel.visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
    else
      { source := childState 0 edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := childFutureSpec 0 edge.future
        target := childState 0 edge.target }
  finishAutomatonFragment states .root accepting skipping (headerEdges ∪ bodyEdges)

private theorem buildRecursionAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.FutureTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    (buildRecursionAutomaton signature name body).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with hHeader | hBody
  · rcases hHeader with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
      childState, hBodyInitial]
  · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
    by_cases hVariable : bodyEdge.label = .variable name
    · simp only [hVariable, if_true] at hFuture
      cases hFuture
      simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
        childState, hBodyInitial]
    · simp only [hVariable, if_false] at hFuture
      cases hSpec : bodyEdge.future with
      | explicit offers =>
          simp [childFutureSpec, hSpec] at hFuture
      | «at» bodyTarget removed =>
          simp only [childFutureSpec, hSpec] at hFuture
          cases hFuture
          have hBodyTarget := hBodyTargets bodyEdge hBodyEdge
            bodyTarget removed hSpec
          simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
            childState, hBodyTarget]

/--
Build a binary choice.

`Q` contains a fresh root and tagged copies of both child state sets. Selection
edges leave the root, and the accepting states are the union of both children.
The supplied labels distinguish ordinary epsilon choice from fair choice.
-/
private def buildChoiceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) (selectionLeft selectionRight : TypeLabel) :
    AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 left ∪ childStates 1 right
  let accepting := childAccepting 0 left ∪ childAccepting 1 right
  let skipping := childSkipping 0 left ∪ childSkipping 1 right
  let selections := signature.localEnvironments.biUnion fun environment =>
    { { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionLeft
        current := ∅
        future := .at (childState 0 left.initial) ∅
        target := childState 0 left.initial },
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionRight
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial } }
  finishAutomatonFragment states .root accepting skipping
    (childPendingEdges 0 left ∪ childPendingEdges 1 right ∪ selections)

private theorem buildChoiceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ left.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildChoiceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildChoiceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.referencedStates (.child 0 state) =
      (child.referencedStates state).image (.child 0) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_left signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_right signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.offersAt (.child 0 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_left signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_right signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

/-- Future resolution inside the left tagged child of a choice is exactly the
child fragment's own future resolution. -/
theorem buildChoiceAutomaton_computeFuture_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ left.states)
    (hCard : left.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    computeFuture parent (.child 0 state) = computeFuture child state := by
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent : PendingAutomaton :=
    { states := choice.states, edges := choice.edges }
  let child : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  apply computeFuture_eq_of_embedding child parent (.child 0)
  · exact buildChoiceAutomaton_referencedStates_left signature left right
      selectionLeft selectionRight
  · exact buildChoiceAutomaton_offersAt_left signature left right
      selectionLeft selectionRight
  · exact hClosed
  · exact hState
  · exact hCard

/-- Future resolution inside the right tagged child of a choice is exactly the
child fragment's own future resolution. -/
theorem buildChoiceAutomaton_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    computeFuture parent (.child 1 state) = computeFuture child state := by
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent : PendingAutomaton :=
    { states := choice.states, edges := choice.edges }
  let child : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  apply computeFuture_eq_of_embedding child parent (.child 1)
  · exact buildChoiceAutomaton_referencedStates_right signature left right
      selectionLeft selectionRight
  · exact buildChoiceAutomaton_offersAt_right signature left right
      selectionLeft selectionRight
  · exact hClosed
  · exact hState
  · exact hCard

private theorem buildChoiceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton signature left right
      selectionLeft selectionRight).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hLeftTargets childEdge hChildEdge
          childTarget removed hSpec
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hRight with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hRightTargets childEdge hChildEdge
          childTarget removed hSpec
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hLeftInitial]
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hRightInitial]

/--
Build sequential composition without collapsing its administrative step.

Left transitions remain inside the tagged left graph. Every completed left
state has a separate silent bridge into the right entry, representing
`skip ; τ → τ`. Only right accepting states are accepting for the sequence.
-/
private def buildSequenceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) : AutomatonFragment :=
  let states := childStates 0 left ∪
    (left.edges.image fun edge => childState 0 edge.target) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  let skipping := childSkipping 1 right
  let leftEdges : Finset PendingAutomatonEdge := left.edges.image fun edge =>
    { source := childState 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := .at (childState 0 edge.target) edge.current
      target := childState 0 edge.target }
  let bridgeEdges : Finset PendingAutomatonEdge :=
    left.skipping.biUnion fun state =>
      signature.localEnvironments.image fun environment =>
        { source := childState 0 state
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 1 right.initial) ∅
          target := childState 1 right.initial }
  finishAutomatonFragment states (childState 0 left.initial) accepting skipping
    (leftEdges ∪ childPendingEdges 1 right ∪ bridgeEdges)

private theorem buildSequenceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (_hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton signature left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at hEdge
  rcases hEdge with (hLeft | hRight) | hBridge
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    cases hFuture
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    left
    right
    exact ⟨leftEdge, hLeftEdge, rfl⟩
  · rcases hRight with ⟨rightEdge, hRightEdge, rfl⟩
    cases hSpec : rightEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» rightTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hRightTarget := hRightTargets rightEdge hRightEdge
          rightTarget removed hSpec
        simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
          childState, hRightTarget]
  · rcases hBridge with ⟨leftState, hLeftSkipping, environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
      childState, hRightInitial]

private def fragmentSuccessors (automaton : AutomatonFragment)
    (state : TypeAutomatonState) : Finset TypeAutomatonState :=
  (automaton.edges.filter fun edge => edge.source = state).image
    PendingAutomatonEdge.target

private def fragmentReachableAux (automaton : AutomatonFragment) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      fragmentReachableAux automaton fuel
        (reached ∪ reached.biUnion (fragmentSuccessors automaton))

private theorem mem_fragmentReachableAux
    (automaton : AutomatonFragment) (state : TypeAutomatonState) :
    ∀ fuel reached,
      state ∈ reached → state ∈ fragmentReachableAux automaton fuel reached := by
  intro fuel
  induction fuel with
  | zero => simp [fragmentReachableAux]
  | succ fuel ih =>
      intro reached hState
      apply ih
      exact Finset.mem_union_left _ hState

private def restrictReachableFragment (automaton : AutomatonFragment) :
    AutomatonFragment :=
  let reachable := fragmentReachableAux automaton automaton.states.card {automaton.initial}
  { states := automaton.states.filter fun state => state ∈ reachable
    initial := automaton.initial
    accepting := automaton.accepting.filter fun state => state ∈ reachable
    skipping := automaton.skipping.filter fun state => state ∈ reachable
    edges := automaton.edges.filter fun edge =>
      edge.source ∈ reachable ∧ edge.target ∈ reachable }

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂`, the initial state is `(i₁,i₂)`, and accepting states are pairs
of accepting component states. Only pairs of synchronizing edges are retained;
their interface actions are hidden before the resulting edge is exposed.  The
full finite Cartesian carrier is retained: `TypeCompilationRelation` also
relates syntactic product pairs that are unreachable from the initial pair,
and its step correspondence is intentionally valid at those states as well.
-/
private def buildParallelAutomaton (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let leftEdges := resolvedAutomatonEdges left
  let rightEdges := resolvedAutomatonEdges right
  let states : Finset TypeAutomatonState :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let accepting : Finset TypeAutomatonState :=
    left.accepting.biUnion fun leftState =>
      right.accepting.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let edges : Finset PendingAutomatonEdge := leftEdges.biUnion fun leftEdge =>
    (rightEdges.filter fun rightEdge =>
      syncAutomatonEdges interface leftEdges rightEdges
        leftEdge rightEdge).image fun rightEdge =>
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := AutomatonConstructionLabel.combine interface
            leftEdge.label rightEdge.label
          current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
          future := .explicit
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := .pair leftEdge.target rightEdge.target }
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting ∅ edges
  exact product

private theorem buildParallelAutomaton_futureTargetsInStates
    (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨leftEdge, _, rightEdge, _, rfl⟩
  simp at hFuture

private theorem mem_foldl_union_iff
    {Element Item : Type} [DecidableEq Element]
    (items : List Item) (part : Item → Finset Element)
    (initial : Finset Element) (element : Element) :
    element ∈ items.foldl (fun accumulated item =>
      accumulated ∪ part item) initial ↔
      element ∈ initial ∨ ∃ item ∈ items, element ∈ part item := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

private theorem childPendingEdges_futureTargetsInStates
    (index : Nat) (fragment : AutomatonFragment)
    (hTargets : fragment.FutureTargetsInStates) :
    ∀ edge ∈ childPendingEdges index fragment, ∀ target removed,
      edge.future = .at target removed →
        target ∈ childStates index fragment := by
  classical
  intro edge hEdge target removed hFuture
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hSpec : childEdge.future with
  | explicit offers =>
      simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
  | «at» childTarget childRemoved =>
      simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
      cases hFuture
      have hChildTarget := hTargets childEdge hChildEdge childTarget
        removed hSpec
      simp [childStates, childState, hChildTarget]

private def indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childStates (indexed.2 + 1) indexed.1.2) ∅

private def indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childAccepting (indexed.2 + 1) indexed.1.2) ∅

private def indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childSkipping (indexed.2 + 1) indexed.1.2) ∅

private def indexedFragmentEdges
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset PendingAutomatonEdge :=
  automata.zipIdx.foldl (fun edges indexed =>
    edges ∪ childPendingEdges (indexed.2 + 1) indexed.1.2) ∅

private theorem indexedFragment_futureTargetsInStates
    (automata : List (BareMessage × AutomatonFragment))
    (hTargets : ∀ entry ∈ automata, entry.2.FutureTargetsInStates) :
    ∀ edge ∈ indexedFragmentEdges automata, ∀ target removed,
      edge.future = .at target removed →
        target ∈ indexedFragmentStates automata := by
  classical
  intro edge hEdge target removed hFuture
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    simp only [childPendingEdges, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget childRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hTargets indexed.1 hEntry childEdge hChildEdge
          childTarget removed hSpec
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        simp [childStates, childState, hChildTarget]

/--
Build an exclusive offer with one fresh root.

Child `0` is the else continuation; children `1..n` are branch continuations.
From the root there are three kinds of edges:

* `branchEdges`: fire an immediately enabled and resolved branch;
* `waitEdges`: remain at the root while a branch may still arrive this cycle;
* `elseEdges`: select the else continuation once no branch can still arrive.
-/
private def buildExclusiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 elseAutomaton ∪
    indexedFragmentStates branchAutomata
  let accepting := childAccepting 0 elseAutomaton ∪
    indexedFragmentAccepting branchAutomata
  let skipping := childSkipping 0 elseAutomaton ∪
    indexedFragmentSkipping branchAutomata
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let branchEdges : Finset PendingAutomatonEdge := branchAutomata.zipIdx.foldl
    (fun edges indexed =>
      let index := indexed.2
      let action := indexed.1.1
      let automaton := indexed.1.2
      let newEdges : Finset PendingAutomatonEdge :=
        let enablingEnvironments := signature.localEnvironments.filter fun environment =>
          typeNeed action ∈ environment.immediate ∧
          needs ∩ environment.future = ∅
        enablingEnvironments.image fun environment =>
          { source := TypeAutomatonState.root
            environment := environment
            label := .visible (TypeLabel.message action.1 action.2)
            current := {action}
            future := .at (childState (index + 1) automaton.initial) ∅
            target := childState (index + 1) automaton.initial }
      edges ∪ newEdges) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting skipping
    (childPendingEdges 0 elseAutomaton ∪ indexedFragmentEdges branchAutomata ∪
      branchEdges ∪ waitEdges ∪ elseEdges)

private theorem buildExclusiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton signature branches elseAutomaton
      branchAutomata).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates branchAutomata
      hBranchTargets edge hIndexed target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
    · simp at hEmpty
    · have hEntry : indexed.1 ∈ branchAutomata := by
        have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexedEntry
        simpa using hMapped
      simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hFuture
      cases hFuture
      have hInitial := hBranchInitial indexed.1 hEntry
      have hIndexedState :
          childState (indexed.2 + 1) indexed.1.2.initial ∈
            indexedFragmentStates branchAutomata := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexedEntry, ?_⟩
        simp [childStates, childState, hInitial]
      simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/--
Build a conjunctive offer with one fresh root.

If at least one branch is enabled, enter the precompiled parallel product of
singleton exclusive offers. If no branch is immediate or future, enter the
else continuation. The conjunction and else automata are tagged as children
`0` and `1`, respectively.
-/
private def buildConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 conjunction ∪
    childStates 1 elseAutomaton
  let accepting := childAccepting 0 conjunction ∪ childAccepting 1 elseAutomaton
  let skipping := childSkipping 0 conjunction ∪ childSkipping 1 elseAutomaton
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let enabledEdges : Finset PendingAutomatonEdge :=
    let enablingEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate ≠ ∅
    enablingEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 conjunction.initial) ∅
        target := childState 0 conjunction.initial }
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting skipping
    (childPendingEdges 0 conjunction ∪ childPendingEdges 1 elseAutomaton ∪
      enabledEdges ∪ waitEdges ∪ elseEdges)

private theorem buildConjunctiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : conjunction.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : conjunction.initial ∈ conjunction.states) :
    (buildConjunctiveOfferAutomaton signature branches elseAutomaton
      conjunction).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElse) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 conjunction
      hConjunctionTargets edge hConjunction target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := childPendingEdges_futureTargetsInStates 1 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hConjunctionInitial]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-!
### Constructor compiler
-/

/-
`compileTypeFuel` also compiles the type generated for a conjunctive offer.
Consequently, a plain recursion-depth calculation on `PactType` is not quite
enough: the generated parallel tree must be accounted for as well.

These three mutually recursive functions calculate exactly the structural
budget needed by the calls below.  Atomic constructors need one unit.  A
compound constructor needs one unit plus the largest budget of any recursive
call that it makes.
-/
mutual
  def typeCompilationFuel : PactType → Nat
    | .message _ _ => 1
    | .progress _ => 1
    | .tock => 1
    | .skip => 1
    | .var _ => 1
    | .recur _ body => 1 + typeCompilationFuel body
    | .choice left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .fairChoice _ left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .seq left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .par left right _ =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .xoffer elseType branches =>
        1 + max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches)
    | .offer elseType branches =>
        1 + max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches)
  termination_by processType => sizeOf processType

  /-- Largest compilation budget among all branch continuations. -/
  def typeBranchCompilationFuel :
      List (BareMessage × PactType) → Nat
    | [] => 0
    | (_, processType) :: rest =>
        max (typeCompilationFuel processType)
          (typeBranchCompilationFuel rest)
  termination_by branches => sizeOf branches

  /-- Budget for the parallel singleton offers generated by an `offer`. -/
  def conjunctiveCompilationFuel :
      List (BareMessage × PactType) → Nat
    | [] => 1
    | [(_, processType)] =>
        1 + max 1 (typeCompilationFuel processType)
    | (_, processType) :: next :: rest =>
        1 + max
          (1 + max 1 (typeCompilationFuel processType))
          (conjunctiveCompilationFuel (next :: rest))
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/--
The auxiliary budget is exactly the budget of the parallel type generated for
a conjunctive offer.  This is the non-structural recursive call that motivates
the custom fuel calculation.
-/
theorem typeCompilationFuel_parallelTypeBranches
    (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranches branches) =
      conjunctiveCompilationFuel branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, typeCompilationFuel,
        conjunctiveCompilationFuel]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            typeCompilationFuel, typeBranchCompilationFuel,
            conjunctiveCompilationFuel]
      | cons next tail =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            typeCompilationFuel, typeBranchCompilationFuel,
          conjunctiveCompilationFuel, ih]

theorem PactType.allVariablesBound_parallelTypeBranches
    (bound : List String) (branches : List (BareMessage × PactType))
    (hBound : AllBranchVariablesBound bound branches) :
    AllVariablesBound bound (parallelTypeBranches branches) := by
  induction branches with
  | nil => simp [parallelTypeBranches, AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            AllVariablesBound, AllBranchVariablesBound] using hBound.1
      | cons next tail =>
          simp only [parallelTypeBranches, AllVariablesBound]
          constructor
          · simpa [singletonTypeXOffer, AllVariablesBound,
              AllBranchVariablesBound] using hBound.1
          · apply ih
            exact hBound.2

/-- `fuel` covers every recursive call made while compiling `processType`. -/
def TypeCompilationFuelSufficient
    (processType : PactType) (fuel : Nat) : Prop :=
  typeCompilationFuel processType ≤ fuel

/-- The calculated compilation budget is sufficient by construction. -/
theorem typeCompilationFuel_sufficient (processType : PactType) :
    TypeCompilationFuelSufficient processType
      (typeCompilationFuel processType) := by
  exact le_rfl

/-- Every type receives at least the one unit needed to enter its constructor. -/
theorem typeCompilationFuel_positive (processType : PactType) :
    0 < typeCompilationFuel processType := by
  cases processType <;> simp [typeCompilationFuel] <;> omega

/-- Sufficient fuel can never select the defensive zero-fuel case at the root. -/
theorem TypeCompilationFuelSufficient.positive
    {processType : PactType} {fuel : Nat}
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    0 < fuel :=
  lt_of_lt_of_le (typeCompilationFuel_positive processType) hFuel

private theorem typeCompilationFuel_le_typeBranchCompilationFuel
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hEntry : entry ∈ branches) :
    typeCompilationFuel entry.2 ≤ typeBranchCompilationFuel branches := by
  induction branches with
  | nil => simp at hEntry
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · simp [typeBranchCompilationFuel]
      · exact le_trans (ih hRest) (by
          simp [typeBranchCompilationFuel])

private def compileTypeFuel (signature : TypeAlphabet) :
    Nat → PactType → AutomatonFragment
  -- Exhausted fuel is an unreachable defensive case for the public compiler.
  | 0, _ =>
      { states := {.root}
        initial := .root
        accepting := ∅
        skipping := ∅
        edges := ∅ }
  | fuel + 1, processType => by
      classical
      match processType with
      -- skip: Q = {root}, i = root, F = {root}; epsilon self-loops.
      | .skip =>
          let idleEnvironments := signature.localEnvironments.filter fun environment =>
            environment.clock = false ∧ environment.immediate = ∅
          exact finishAutomatonFragment {.root} .root {.root} {.root} <|
            idleEnvironments.image fun environment =>
              { source := .root
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .root }

      -- message: fire to final when its complement is immediate; otherwise wait.
      | .message msg dir =>
          let action : BareMessage := (msg, dir)
          let firingEdges : Finset PendingAutomatonEdge :=
            (signature.localEnvironments.filter fun environment =>
              environment.hasNeed action).image fun environment =>
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible (TypeLabel.message msg dir)
                  current := {action}
                  future := .explicit ∅
                  target := .final }
          let waitingEdges : Finset PendingAutomatonEdge :=
            (signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              ¬ environment.hasNeed action).image fun environment =>
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.silent
                  current := {action}
                  future := .explicit ∅
                  target := .root }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            (firingEdges ∪ waitingEdges ∪ finalEdges)

      -- clock: a clock environment moves root to final; non-clock input waits.
      | .tock =>
          let actionEdges : Finset PendingAutomatonEdge :=
            signature.localEnvironments.image fun environment =>
              if environment.clock then
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.tock
                  current := ∅
                  future := .explicit ∅
                  target := .final }
              else
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.silent
                  current := ∅
                  future := .explicit ∅
                  target := .root }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            (actionEdges ∪ finalEdges)

      -- progress: emit the marker and enter final; final then idles silently.
      | .progress pid =>
          let actionEdges : Finset PendingAutomatonEdge :=
            signature.localEnvironments.image fun environment =>
              { source := TypeAutomatonState.root
                environment := environment
                label := .visible (TypeLabel.progress pid)
                current := ∅
                future := .explicit ∅
                target := .final }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            (actionEdges ∪ finalEdges)

      -- variable: create a temporary labelled edge for an enclosing binder.
      | .var name =>
          exact finishAutomatonFragment {.root, .final} .root ∅ ∅ <|
            signature.localEnvironments.image fun environment =>
              { source := .root
                environment := environment
                label := .variable name
                current := ∅
                future := .explicit ∅
                target := .final }

      -- recursion: replace matching variable edges by silent back-edges.
      | .recur name body =>
          exact buildRecursionAutomaton signature name
            (compileTypeFuel signature fuel body)
      -- ordinary choice: add a fresh root with two silent selection edges.
      | .choice left right =>
          exact buildChoiceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            TypeLabel.silent TypeLabel.silent

      -- fair choice: use the same sum construction with observable outcomes.
      | .fairChoice bid left right =>
          exact buildChoiceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)

      -- sequence: redirect transitions entering a left final state into right.
      | .seq left right =>
          exact buildSequenceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)

      -- parallel: form the reachable synchronized product on `interface`.
      | .par left right interface =>
          exact buildParallelAutomaton interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)

      -- exclusive offer: compile else and every branch independently first.
      | .xoffer elseType branches =>
          let elseAutomaton := compileTypeFuel signature fuel elseType
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          exact buildExclusiveOfferAutomaton
            signature branches elseAutomaton branchAutomata

      -- conjunctive offer: compile its singleton-offer parallel product first.
      | .offer elseType branches =>
          let elseAutomaton := compileTypeFuel signature fuel elseType
          let conjunction := compileTypeFuel signature fuel
            (parallelTypeBranches branches)
          exact buildConjunctiveOfferAutomaton
            signature branches elseAutomaton conjunction

/-- Once fuel covers the custom compilation budget, one more unit leaves the
constructor fragment unchanged. -/
private theorem compileTypeFuel_succ_stable (signature : TypeAlphabet) :
    ∀ fuel processType, typeCompilationFuel processType ≤ fuel →
      compileTypeFuel signature (fuel + 1) processType =
        compileTypeFuel signature fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => rfl
      | progress pid => rfl
      | tock => rfl
      | skip => rfl
      | var name => rfl
      | recur name body =>
          change buildRecursionAutomaton signature name
              (compileTypeFuel signature (fuel + 1) body) =
            buildRecursionAutomaton signature name
              (compileTypeFuel signature fuel body)
          rw [ih body (by
            simp [typeCompilationFuel] at hFuel
            omega)]
      | choice left right =>
          change buildChoiceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
              TypeLabel.silent TypeLabel.silent
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | fairChoice bid left right =>
          change buildChoiceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | seq left right =>
          change buildSequenceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right) =
            buildSequenceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | par left right interface =>
          change buildParallelAutomaton interface
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right) =
            buildParallelAutomaton interface
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | xoffer elseType branches =>
          change buildExclusiveOfferAutomaton signature branches
              (compileTypeFuel signature (fuel + 1) elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel signature (fuel + 1) branch.2)) =
            buildExclusiveOfferAutomaton signature branches
              (compileTypeFuel signature fuel elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel signature fuel branch.2))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse]
          congr 1
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hMap : ∀ rest,
              typeBranchCompilationFuel rest ≤ fuel →
              (rest.map fun branch =>
                (branch.1, compileTypeFuel signature (fuel + 1) branch.2)) =
              (rest.map fun branch =>
                (branch.1, compileTypeFuel signature fuel branch.2)) := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro hRest
                rcases branch with ⟨action, branchType⟩
                simp only [List.map_cons]
                have hBranch : typeCompilationFuel branchType ≤ fuel := by
                  simp [typeBranchCompilationFuel] at hRest
                  omega
                rw [ih branchType hBranch]
                congr 1
                apply tailIH
                simp [typeBranchCompilationFuel] at hRest ⊢
                omega
          exact hMap branches hBranches
      | offer elseType branches =>
          change buildConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature (fuel + 1) elseType)
              (compileTypeFuel signature (fuel + 1)
                (parallelTypeBranches branches)) =
            buildConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature fuel elseType)
              (compileTypeFuel signature fuel (parallelTypeBranches branches))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hConjunction :
              typeCompilationFuel (parallelTypeBranches branches) ≤ fuel := by
            rw [typeCompilationFuel_parallelTypeBranches]
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse,
            ih (parallelTypeBranches branches) hConjunction]

/-- Any two sufficient parent budgets produce the same constructor fragment. -/
private theorem compileTypeFuel_add_stable
    (signature : TypeAlphabet) (processType : PactType)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    compileTypeFuel signature (fuel + extra) processType =
      compileTypeFuel signature fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        compileTypeFuel_succ_stable signature (fuel + extra) processType
          (by omega),
        ih]

private theorem compileTypeFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    compileTypeFuel signature leftFuel processType =
      compileTypeFuel signature rightFuel processType := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (compileTypeFuel_add_stable signature processType leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact compileTypeFuel_add_stable signature processType rightFuel extra hRight

/-- Every raw constructor edge has passed recursion-marker elimination and is
therefore labelled by a semantic type label. -/
def CompilationPendingEdgesVisible
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ edge ∈ fragment.edges, ∃ label, edge.label = .visible label

/-- A decorated automaton edge represented as the tuple `(q, σ, q')`. -/
structure TypeAutomatonEdge : Type where
  source : TypeAutomatonState
  symbol : TypeAutomatonSymbol
  target : TypeAutomatonState
  deriving DecidableEq

/-- Final finite automaton exposed to conformance and compatibility proofs. -/
structure TypeAutomaton : Type where
  signature : TypeAlphabet
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  alphabet : Finset TypeAutomatonSymbol
  edges : Finset TypeAutomatonEdge

namespace TypeAutomaton

  /-- Membership of a decorated edge in the finite transition relation. -/
  def HasEdge (automaton : TypeAutomaton)
      (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
      (offers : TypeOfferSummary) (target : TypeAutomatonState) : Prop :=
    { source := source,
      symbol := { environment := env, label := label, offers := offers },
      target := target } ∈ automaton.edges

end TypeAutomaton

/-- States mentioned by a finite decorated edge relation. -/
private def typeAutomatonEdgeStates
    (edges : Finset TypeAutomatonEdge) : Finset TypeAutomatonState :=
  edges.biUnion fun edge => {edge.source, edge.target}

/--
Compile a type by composing its constructor automata,
then remove unresolved variable edges and transitions outside the fixed external alphabet.
-/
def compileType
    (signature : TypeAlphabet)
    (processType : PactType) : TypeAutomaton :=
  let fuel := typeCompilationFuel processType
  let constructed := compileTypeFuel signature fuel processType
  let constructedEdges := resolvedAutomatonEdges constructed
  let transitionAlphabet := signature.transitionAlphabet
  let edges : Finset TypeAutomatonEdge := constructedEdges.biUnion fun edge =>
    match edge.label with
    | .variable _ => ∅
    | .visible label =>
        let symbol : TypeAutomatonSymbol :=
          { environment := edge.environment
            label := label
            offers := { current := edge.current, future := edge.future } }
        if symbol ∈ transitionAlphabet then
          {{ source := edge.source, symbol := symbol, target := edge.target }}
        else ∅
  { signature := signature
    -- Closing the exported carrier under edge endpoints makes the usual
    -- finite-automaton state invariant explicit even if an intermediate
    -- constructor has retained an otherwise unreachable endpoint.
    states := constructed.states ∪ typeAutomatonEdgeStates edges
    initial := constructed.initial
    accepting := constructed.accepting
    alphabet := transitionAlphabet
    edges := edges }

/-- A visible edge in a constructor fragment after resolving its symbolic
future field against that complete fragment.  This is the internal edge view
used by the structural correspondence proof, before the public alphabet
filter is applied. -/
def AutomatonFragment.HasResolvedEdge (fragment : AutomatonFragment)
    (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = source ∧ edge.environment = env ∧
      edge.label = .visible label ∧ edge.current = offers.current ∧
      (match edge.future with
        | .explicit future => future
        | .at state removed =>
            computeFuture
              { states := fragment.states, edges := fragment.edges }
              state \ removed) = offers.future ∧
      edge.target = target

/-- Once a symbol belongs to the fixed alphabet, public edge membership is
exactly resolved membership in the constructor fragment. -/
theorem compileType_hasEdge_iff_hasResolvedEdge
    (signature : TypeAlphabet) (processType : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature processType).HasEdge source env label offers target ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel processType) processType)
        source env label offers target := by
  classical
  simp [TypeAutomaton.HasEdge, compileType,
    AutomatonFragment.HasResolvedEdge, resolvedAutomatonEdges, hSymbol]
  aesop

/-- Exact optimistic future offers from the existing constructor graph: union
all current and explicit future offers reachable through symbolic same-cycle
references, stopping at clock edges.  This is the lowercase-paper `FutOff`
interpretation and, in particular, observes synchronization before exposing a
parallel continuation. -/
def graphFutureOffers (processType : PactType) : Finset BareMessage :=
  let signature := futureAnalysisAlphabet processType
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  computeFuture { states := fragment.states, edges := fragment.edges }
    fragment.initial

/-- The exact optimistic future menu from lowercase `pact.pdf`: all offers
reachable in the existing complete constructor graph before the next clock. -/
def typeFutureOffers (processType : PactType) : Finset BareMessage :=
  graphFutureOffers processType

private theorem computeFuture_eq_empty_of_empty_edges
    (automaton : PendingAutomaton)
    (hEmpty : ∀ edge ∈ automaton.edges,
      edge.current = ∅ ∧ edge.future = .explicit ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  have hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    exact ⟨∅, (hEmpty edge hEdge).2⟩
  rw [computeFuture_eq_offersAt_of_all_explicit automaton hExplicit]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, _⟩, hOffer⟩
  obtain ⟨hCurrent, hFuture⟩ := hEmpty edge hEdge
  simp [hCurrent, hFuture] at hOffer

@[simp] theorem typeFutureOffers_skip :
    typeFutureOffers .skip = ∅ := by
  unfold typeFutureOffers graphFutureOffers
  let signature := futureAnalysisAlphabet (.skip)
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.skip)) (.skip)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending fragment.initial = ∅
  apply computeFuture_eq_empty_of_empty_edges pending
  intro edge hEdge
  simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment] at hEdge
  rcases hEdge with ⟨_, _, rfl⟩
  exact ⟨rfl, rfl⟩

@[simp] theorem typeFutureOffers_progress (pid : ProcId) :
    typeFutureOffers (.progress pid) = ∅ := by
  unfold typeFutureOffers graphFutureOffers
  let signature := futureAnalysisAlphabet (.progress pid)
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.progress pid)) (.progress pid)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending fragment.initial = ∅
  apply computeFuture_eq_empty_of_empty_edges pending
  intro edge hEdge
  simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment] at hEdge
  rcases hEdge with hAction | hFinal
  · rcases hAction with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩
  · rcases hFinal with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩

@[simp] theorem typeFutureOffers_tock :
    typeFutureOffers .tock = ∅ := by
  unfold typeFutureOffers graphFutureOffers
  let signature := futureAnalysisAlphabet (.tock)
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.tock)) (.tock)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending fragment.initial = ∅
  apply computeFuture_eq_empty_of_empty_edges pending
  intro edge hEdge
  simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment] at hEdge
  rcases hEdge with hAction | hFinal
  · rcases hAction with ⟨environment, _, rfl⟩
    by_cases hClock : environment.clock = true <;> simp [hClock]
  · rcases hFinal with ⟨_, _, rfl⟩
    exact ⟨rfl, rfl⟩

@[simp] theorem typeFutureOffers_var (name : String) :
    typeFutureOffers (.var name) = ∅ := by
  unfold typeFutureOffers graphFutureOffers
  let signature := futureAnalysisAlphabet (.var name)
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.var name)) (.var name)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending fragment.initial = ∅
  apply computeFuture_eq_empty_of_empty_edges pending
  intro edge hEdge
  simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
    finishAutomatonFragment] at hEdge
  rcases hEdge with ⟨_, _, rfl⟩
  exact ⟨rfl, rfl⟩

@[simp] theorem typeFutureOffers_message
    (msg : MessageId) (dir : MessageDir) :
    typeFutureOffers (.message msg dir) = {(msg, dir)} := by
  unfold typeFutureOffers graphFutureOffers
  let signature := futureAnalysisAlphabet (.message msg dir)
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.message msg dir)) (.message msg dir)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hExplicit : ∀ edge ∈ pending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hWaiting with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
  change computeFuture pending fragment.initial = {(msg, dir)}
  have hInitial : fragment.initial = .root := by
    simp [fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment]
  rw [hInitial,
    computeFuture_eq_offersAt_of_all_explicit pending hExplicit]
  ext action
  constructor
  · intro hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.message] using hOffer
    · rcases hWaiting with ⟨_, _, rfl⟩
      simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent] using hOffer
    · rcases hFinal with ⟨_, _, rfl⟩
      simp at hSource
  · intro hAction
    simp only [Finset.mem_singleton] at hAction
    subst action
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter]
    let emptyEdge : PendingAutomatonEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := {(msg, dir)}
        future := .explicit ∅
        target := .root }
    refine ⟨emptyEdge, ?_, ?_⟩
    · constructor
      · simp [pending, fragment, emptyEdge, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment,
          TypeAlphabet.localEnvironments,
          TypeAlphabet.localEnvironmentActions,
          TypeEnvironment.empty, TypeEnvironment.hasNeed]
      · rfl
    · simp [emptyEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent]

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
          (parallelTypeBranches branches) ∅
          (typeFutureOffers (parallelTypeBranches branches))
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
      (parallelTypeBranches branches)
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


/-! ### Synchronization-aware future correction

The obsolete syntax-only parallel regression is recorded in `AGENT.md`.  The
authoritative `typeFutureOffers` above now reads the existing synchronized
constructor graph, so blocked internal handshakes cannot expose continuations.
-/

/-- The source of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_source_mem
    (signature : TypeAlphabet) (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge
      source env label offers target) :
    source ∈ (compileType signature processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- The target of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_target_mem
    (signature : TypeAlphabet) (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge
      source env label offers target) :
    target ∈ (compileType signature processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- Regression theorem: compiled `skip` has no edge in a clock environment. -/
theorem compileType_skip_has_no_clock_edge
    (signature : TypeAlphabet) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    ¬ (compileType signature .skip).HasEdge
      (compileType signature .skip).initial
      TypeEnvironment.tock TypeLabel.silent offers target := by
  simp [TypeAutomaton.HasEdge, compileType, typeCompilationFuel,
    compileTypeFuel, finishAutomatonFragment, resolvedAutomatonEdges,
    TypeEnvironment.tock]
  intro environment _ hClock _
  split_ifs
  · simp only [Finset.mem_singleton]
    intro edgeEquality
    have clockEquality := congrArg
      (fun edge : TypeAutomatonEdge => edge.symbol.environment.clock)
      edgeEquality
    simp [hClock] at clockEquality
  · simp

/-!
### Semantic residuals represented by constructor states

This relation is the invariant used by the correspondence proof.  The first
type is the fragment originally compiled; the final type is the operational
residual represented by the tagged state in the middle.
-/

inductive TypeCompilationRelation :
    PactType → TypeAutomatonState → PactType → Prop where
  | skip : TypeCompilationRelation .skip .root .skip
  | message_source (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .root (.message msg dir)
  | message_final (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .final .skip
  | cycle_source : TypeCompilationRelation .tock .root .tock
  | cycle_final : TypeCompilationRelation .tock .final .skip
  | progress_source (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .root (.progress pid)
  | progress_final (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .final .skip
  | variable (name : String) :
      TypeCompilationRelation (.var name) .root (.var name)
  | recur_source (name : String) (body : PactType) :
      TypeCompilationRelation (.recur name body) .root (.recur name body)
  | recur_body (name : String) (body residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation body state residual →
      TypeCompilationRelation (.recur name body) (.child 0 state)
        (residual.replaceVar name (.recur name body))
  | choice_source (left right : PactType) :
      TypeCompilationRelation (.choice left right) .root (.choice left right)
  | choice_left (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.choice left right) (.child 0 state) residual
  | choice_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.choice left right) (.child 1 state) residual
  | fair_source (bid : BranchId) (left right : PactType) :
      TypeCompilationRelation (.fairChoice bid left right) .root
        (.fairChoice bid left right)
  | fair_left (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 0 state) residual
  | fair_right (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 1 state) residual
  | sequence_left (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq residual right)
  | sequence_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.seq left right) (.child 1 state) residual
  | parallel (left right leftResidual rightResidual : PactType)
      (interface : Interface) (leftState rightState : TypeAutomatonState) :
      TypeCompilationRelation left leftState leftResidual →
      TypeCompilationRelation right rightState rightResidual →
      TypeCompilationRelation (.par left right interface)
        (.pair leftState rightState)
        (.par leftResidual rightResidual interface)
  | xoffer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.xoffer elseType branches) .root
        (.xoffer elseType branches)
  | xoffer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.xoffer elseType branches) (.child 0 state) residual
  | xoffer_branch (elseType branchType residual : PactType)
      (branches : List (BareMessage × PactType)) (action : BareMessage)
      (index : Nat) (state : TypeAutomatonState) :
      branches[index]? = some (action, branchType) →
      TypeCompilationRelation branchType state residual →
      TypeCompilationRelation (.xoffer elseType branches)
        (.child (index + 1) state) residual
  | offer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.offer elseType branches) .root
        (.offer elseType branches)
  | offer_branches (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation (parallelTypeBranches branches) state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 0 state) residual
  | offer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 1 state) residual

/-- A constructor state represents at most one semantic residual. -/
theorem TypeCompilationRelation.residual_unique
    {original left right : PactType} {state : TypeAutomatonState}
    (hLeft : TypeCompilationRelation original state left)
    (hRight : TypeCompilationRelation original state right) : left = right := by
  induction hLeft generalizing right <;> cases hRight <;>
    try simp_all
  all_goals
    first
    | solve_by_elim
    | (congr 1; solve_by_elim)
    | (constructor <;> solve_by_elim)

/-- Replacing a variable by its recursion binder yields literal `skip` exactly
when the original residual was already literal `skip`.  This is the
substitution fact needed to transport the compiler's `skipping` marker through
a recursion binder. -/
theorem PactType.replaceVar_recur_eq_skip_iff
    (processType : PactType) (name : String) (body : PactType) :
    (processType.replaceVar name (.recur name body) = .skip) ↔
      processType = .skip := by
  cases processType <;> simp only [PactType.replaceVar] <;>
    try simp
  all_goals split <;> simp_all

/-- Sufficiently fuelled compilation starts in the state representing its input. -/
private theorem compileTypeFuel_initial_relation (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      TypeCompilationRelation processType
        (compileTypeFuel signature fuel processType).initial processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => exact TypeCompilationRelation.message_source msg dir
      | progress pid => exact TypeCompilationRelation.progress_source pid
      | tock => exact TypeCompilationRelation.cycle_source
      | skip => exact TypeCompilationRelation.skip
      | var name => exact TypeCompilationRelation.variable name
      | recur name body => exact TypeCompilationRelation.recur_source name body
      | choice left right => exact TypeCompilationRelation.choice_source left right
      | fairChoice bid left right =>
          exact TypeCompilationRelation.fair_source bid left right
      | seq left right =>
          apply TypeCompilationRelation.sequence_left
          apply ih left
          simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
          omega
      | par left right interface =>
          apply TypeCompilationRelation.parallel
          · apply ih left
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          · apply ih right
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
      | xoffer elseType branches =>
          exact TypeCompilationRelation.xoffer_source elseType branches
      | offer elseType branches =>
          exact TypeCompilationRelation.offer_source elseType branches

/-- The public compiler's initial state represents the original type. -/
theorem compileType_initial_relation
    (signature : TypeAlphabet) (processType : PactType) :
    TypeCompilationRelation processType
      (compileType signature processType).initial processType := by
  apply compileTypeFuel_initial_relation signature
  exact typeCompilationFuel_sufficient processType

/-- Every sufficiently fuelled fragment contains its distinguished entry state. -/
private theorem compileTypeFuel_initial_mem (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).initial ∈
        (compileTypeFuel signature fuel processType).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => simp [compileTypeFuel, finishAutomatonFragment]
      | progress pid => simp [compileTypeFuel, finishAutomatonFragment]
      | tock => simp [compileTypeFuel, finishAutomatonFragment]
      | skip => simp [compileTypeFuel, finishAutomatonFragment]
      | var name => simp [compileTypeFuel, finishAutomatonFragment]
      | recur name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | choice left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fairChoice bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hInitialOrTarget :
              (compileTypeFuel signature fuel left).initial ∈
                  (compileTypeFuel signature fuel left).states ∨
                ∃ edge ∈ (compileTypeFuel signature fuel left).edges,
                  edge.target =
                    (compileTypeFuel signature fuel left).initial :=
            Or.inl (ih left hLeft)
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using
              hInitialOrTarget
      | par left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          have hRightMem := ih right hRight
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment]
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hLeftMem, ?_⟩
          exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
      | xoffer elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | offer elseType branches =>
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment]

/-- Every symbolic future reference produced by sufficiently fuelled
compilation points to a state declared by the same constructor fragment. -/
private theorem compileTypeFuel_futureTargetsInStates
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
        (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          cases hEdge with
          | inl hFirst =>
            cases hFirst with
            | inl hFiring =>
              rcases hFiring with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
            | inr hWaiting =>
              rcases hWaiting with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
          | inr hFinal =>
            rcases hFinal with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture
            cases hFuture
      | progress pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · rcases hAction with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
          · rcases hFinal with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
      | tock =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨environment, _, hEdge⟩ |
            ⟨environment, _, hEdge⟩)
          · rw [← hEdge] at hFuture
            split at hFuture <;> cases hFuture
          · rw [← hEdge] at hFuture
            cases hFuture
      | skip =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEdge⟩
          rw [← hEdge] at hFuture
          cases hFuture
      | var name =>
          simp [AutomatonFragment.FutureTargetsInStates, compileTypeFuel,
            finishAutomatonFragment]
      | recur name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            TypeLabel.silent TypeLabel.silent
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par left right interface =>
          exact buildParallelAutomaton_futureTargetsInStates interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          apply buildExclusiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply ih branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
          · exact compileTypeFuel_initial_mem signature fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply compileTypeFuel_initial_mem signature fuel branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hConjunction : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          exact buildConjunctiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            (compileTypeFuel signature fuel (parallelTypeBranches branches))
            (ih elseType hElse)
            (ih (parallelTypeBranches branches) hConjunction)
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (compileTypeFuel_initial_mem signature fuel
              (parallelTypeBranches branches) hConjunction)

/-- Sufficient compilation produces a pending graph closed under all
same-cycle symbolic references. -/
private theorem compileTypeFuel_referencesClosed
    (signature : TypeAlphabet) (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed := by
  exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

/-- The initial state exposed by the public compiler belongs to its state set. -/
theorem compileType_initial_mem
    (signature : TypeAlphabet) (processType : PactType) :
    (compileType signature processType).initial ∈
      (compileType signature processType).states := by
  simp only [compileType, Finset.mem_union]
  left
  apply compileTypeFuel_initial_mem signature
  exact typeCompilationFuel_sufficient processType

/-- Membership of a tagged state in an indexed family of skipping fragments
can be read at the corresponding list index. -/
private theorem childState_mem_indexedFragmentSkipping_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentSkipping automata ↔
      state ∈ entry.2.skipping := by
  classical
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildSkipping, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildSkipping
  · intro hSkipping
    rcases List.getElem?_eq_some_iff.mp hEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childSkipping, childState, hSkipping]

private theorem root_not_mem_indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentSkipping automata := by
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

private theorem child_zero_not_mem_indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentSkipping automata := by
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

/-- At every state represented by a sufficiently fuelled constructor
fragment, the compiler's syntactic `skipping` marker is exact: it holds
precisely when the represented operational residual is literal `skip`. -/
theorem compileTypeFuel_skipping_iff
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
        (state ∈ (compileTypeFuel signature fuel processType).skipping ↔
          residual = .skip) := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_final msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_final =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_final pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur_source name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          rw [PactType.replaceVar_recur_eq_skip_iff]
          simpa [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | choice_source left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | fair_source bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | sequence_left left right childResidual childQ hChildRelated =>
          simp [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment]
      | xoffer_source elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState,
            root_not_mem_indexedFragmentSkipping]
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hElseTag : childState 0 childQ ∈
                childSkipping 0 (compileTypeFuel signature fuel elseType) ↔
              childQ ∈
                (compileTypeFuel signature fuel elseType).skipping := by
            simp [childSkipping, childState]
          have hNotIndexed : childState 0 childQ ∉
              indexedFragmentSkipping
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature fuel branch.2)) :=
            child_zero_not_mem_indexedFragmentSkipping _ childQ
          constructor
          · rintro (hElse | hIndexed)
            · exact hChild.mp (hElseTag.mp hElse)
            · exact (hNotIndexed hIndexed).elim
          · intro hSkip
            left
            exact hElseTag.mpr (hChild.mpr hSkip)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hIndexBound, hIndexValue⟩
            have hBranchMem : (action, branchType) ∈ branches := by
              have hMember := List.getElem_mem hIndexBound
              simpa [hIndexValue] using hMember
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentSkipping_iff
            branchAutomata index
              (action, compileTypeFuel signature fuel branchType)
              hAutomatonEntry childQ
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotElse : childState (index + 1) childQ ∉
              childSkipping 0 (compileTypeFuel signature fuel elseType) := by
            simp [childSkipping, childState]
          constructor
          · rintro (hElse | hBranch)
            · exact (hNotElse hElse).elim
            · exact hChild.mp (hIndexed.mp hBranch)
          · intro hSkip
            right
            exact hIndexed.mpr (hChild.mpr hSkip)
      | offer_source elseType branches =>
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | offer_branches elseType _ branches childQ
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih (parallelTypeBranches branches) hConjunctionFuel
            childQ residual hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild

/-- The compiler's skipping-state marker agrees exactly with literal `skip`
at every state represented by the compilation relation. -/
def CompilationSkippingCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      (state ∈ (compileTypeFuel signature
          (typeCompilationFuel processType) processType).skipping ↔
        residual = .skip)

theorem compilationSkippingCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationSkippingCorrect signature processType := by
  exact compileTypeFuel_skipping_iff signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Graph future resolution agrees with syntactic same-cycle future offers at
every state/residual represented by the final pending compilation fragment. -/
def CompilationFutureCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      computeFuture pending state = typeFutureOffers residual

/-- The reusable `stepIff` property for the concrete compiler relation. -/
def CompilationStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature processType).alphabet →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature processType).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation processType state' residual')

/-- The raw pending-fragment form of `CompilationStepCorrect`.  Unlike the
public automaton theorem, it retains symbolic future references and therefore
composes through constructors such as recursion. -/
def CompilationFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        fragment.HasResolvedEdge state env label offers state' ∧
        TypeCompilationRelation processType state' residual')

private theorem computeFuture_eq_empty_of_edges_empty
    (automaton : PendingAutomaton)
    (hEmpty : ∀ edge ∈ automaton.edges,
      edge.current = ∅ ∧ edge.future = .explicit ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  have hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    exact ⟨∅, (hEmpty edge hEdge).2⟩
  rw [computeFuture_eq_offersAt_of_all_explicit automaton hExplicit]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, _⟩, hOffer⟩
  obtain ⟨hCurrent, hFuture⟩ := hEmpty edge hEdge
  simp [hCurrent, hFuture] at hOffer

/-- Future correctness for `skip`. -/
theorem compilationFutureCorrect_skip (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature (typeCompilationFuel .skip) .skip
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers .skip
  rw [typeFutureOffers_skip]
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-- Future correctness for an atomic progress marker. -/
theorem compilationFutureCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFutureCorrect signature (.progress pid) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.progress pid)) (.progress pid)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa only [typeFutureOffers_progress, typeFutureOffers_skip] using hEmpty _

/-- Future correctness for the clock constructor. -/
theorem compilationFutureCorrect_tock (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .tock := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel .tock) .tock
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨environment, _, rfl⟩
      by_cases hClock : environment.clock = true <;>
        simp [hClock]
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa only [typeFutureOffers_tock, typeFutureOffers_skip] using hEmpty _

/-- Future correctness for an atomic message. -/
theorem compilationFutureCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFutureCorrect signature (.message msg dir) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.message msg dir)) (.message msg dir)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hExplicit : ∀ edge ∈ pending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hWaiting with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  rw [computeFuture_eq_offersAt_of_all_explicit pending hExplicit]
  cases hRelated with
  | message_source =>
      rw [typeFutureOffers_message]
      ext action
      constructor
      · intro hAction
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter] at hAction
        rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
        simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨_, _, rfl⟩
          simpa [AutomatonConstructionLabel.semantic,
            TypeLabel.message] using hOffer
        · rcases hWaiting with ⟨_, _, rfl⟩
          simpa [AutomatonConstructionLabel.semantic,
            TypeLabel.silent] using hOffer
        · rcases hFinal with ⟨_, _, rfl⟩
          simp at hSource
      · intro hAction
        simp only [Finset.mem_singleton] at hAction
        subst action
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter]
        let emptyEdge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.empty
            label := .visible TypeLabel.silent
            current := {(msg, dir)}
            future := .explicit ∅
            target := .root }
        refine ⟨emptyEdge, ?_, ?_⟩
        · constructor
          · simp [pending, fragment, emptyEdge, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment,
              TypeAlphabet.localEnvironments,
              TypeAlphabet.localEnvironmentActions,
              TypeEnvironment.empty, TypeEnvironment.hasNeed]
          · rfl
        · simp [emptyEdge, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
  | message_final =>
      rw [typeFutureOffers_skip]
      change pending.offersAt .final = ∅
      rw [Finset.eq_empty_iff_forall_notMem]
      intro action hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment] at hEdge
      rcases hEdge with hFiring | hWaiting | hFinal
      · rcases hFiring with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hWaiting with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hFinal with ⟨_, _, rfl⟩
        simp at hOffer

/-- Future correctness for a free-variable marker fragment. -/
theorem compilationFutureCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationFutureCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.var name)) (.var name)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers (.var name)
  rw [typeFutureOffers_var]
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-! ### Parallel environment reconstruction -/

namespace TypeEnvironment

/-- Neither half of an environment mentions a message hidden by the given
parallel interface.  This is the exact outer-domain condition needed for
`combineAutomatonEnvironment` to reconstruct that environment. -/
def AvoidsInterface (environment : TypeEnvironment)
    (interface : Interface) : Prop :=
  (∀ action ∈ environment.immediate, action.1 ∉ interface) ∧
    ∀ action ∈ environment.future, action.1 ∉ interface

theorem tock_avoidsInterface (interface : Interface) :
    TypeEnvironment.tock.AvoidsInterface interface := by
  simp [AvoidsInterface, TypeEnvironment.tock]

theorem AvoidsInterface.mono
    {environment : TypeEnvironment} {larger smaller : Interface}
    (hAvoids : environment.AvoidsInterface larger)
    (hSubset : smaller ⊆ larger) :
    environment.AvoidsInterface smaller := by
  exact ⟨fun action hAction hSmaller =>
      hAvoids.1 action hAction (hSubset hSmaller),
    fun action hAction hSmaller =>
      hAvoids.2 action hAction (hSubset hSmaller)⟩

end TypeEnvironment

namespace TypeAlphabet

/-- Construction-local environments satisfy the same clock/disjointness
invariant as exported environments. -/
theorem localEnvironment_wellFormed {alphabet : TypeAlphabet}
    {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments) :
    environment.WellFormed := by
  simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      exact (Finset.mem_sdiff.mp (hFuture hFutureMember)).2 hImmediate

/-- A construction-local clock environment is exactly the distinguished
clock environment. -/
theorem localEnvironment_eq_tock_of_clock
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments)
    (hClock : environment.clock = true) :
    environment = TypeEnvironment.tock := by
  have hWellFormed := localEnvironment_wellFormed hEnvironment
  rcases hWellFormed.1 hClock with ⟨hImmediate, hFuture⟩
  cases environment
  simp_all [TypeEnvironment.tock]

/-- The future half of an exported environment cannot mention an internal
message identifier. -/
theorem environment_future_avoids_interface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments) :
    ∀ action ∈ environment.future,
      action.1 ∉ alphabet.interface := by
  simp only [environments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.tock]
  · intro action hAction hInterface
    have hEnvironmentAction := (Finset.mem_sdiff.mp (hFuture hAction)).1
    simp only [environmentActions, Finset.mem_image] at hEnvironmentAction
    rcases hEnvironmentAction with ⟨boundaryAction, hBoundary, hNeed⟩
    apply hAlphabet boundaryAction hBoundary
    have hMessage := congrArg Prod.fst hNeed
    simp only [typeNeed] at hMessage
    rw [hMessage]
    exact hInterface

/-- Every exported environment avoids each declared sub-interface. -/
theorem environment_avoids_subinterface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    {interface : Interface}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments)
    (hInterface : interface ⊆ alphabet.interface) :
    environment.AvoidsInterface interface := by
  constructor
  · intro action hAction hInternal
    exact environment_immediate_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)
  · intro action hAction hInternal
    exact environment_future_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)

end TypeAlphabet

/-- Ordinary sibling-field equations preserve avoidance of every interface
disjoint from the one whose offers are injected. -/
private theorem TypeEnvironment.avoidsInterface_of_ordinary_fields
    {outer localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {current future : Finset BareMessage}
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers parentInterface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers parentInterface future) \
        localEnvironment.immediate) :
    localEnvironment.AvoidsInterface childInterface := by
  constructor
  · intro action hAction hChild
    rw [hImmediate] at hAction
    rcases Finset.mem_union.mp hAction with hOuter | hParent
    · exact hOuterAvoids.1 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild
  · intro action hAction hChild
    rw [hFuture] at hAction
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hAction).1 with
      hOuter | hParent
    · exact hOuterAvoids.2 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild

/-- Passing through a sibling-local environment may add only actions from the
parent interface.  Hence it preserves avoidance of any disjoint descendant
interface. -/
theorem LocalTypeEnvironment.avoidsInterface_of_disjoint
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer parentInterface siblingEnvironment
      sibling label localEnvironment)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface) :
    localEnvironment.AvoidsInterface childInterface := by
  cases hLocal with
  | clock outer parentInterface sibling label hClock =>
      exact TypeEnvironment.tock_avoidsInterface childInterface
  | ordinary outer siblingEnvironment localEnvironment parentInterface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      constructor
      · intro action hAction hChild
        rw [hImmediate] at hAction
        rcases Finset.mem_union.mp hAction with hOuter | hParent
        · exact hOuterAvoids.1 action hOuter hChild
        · have hParentMessage := (Finset.mem_filter.mp hParent).2
          exact Finset.disjoint_left.mp hDisjoint hParentMessage hChild
      · intro action hAction hChild
        rw [hFuture] at hAction
        have hAvailable := (Finset.mem_sdiff.mp hAction).1
        rcases Finset.mem_union.mp hAvailable with hOuter | hParent
        · exact hOuterAvoids.2 action hOuter hChild
        · have hParentMessage := (Finset.mem_filter.mp hParent).2
          exact Finset.disjoint_left.mp hDisjoint hParentMessage hChild

/-- Interface scoping supplies the disjointness needed when an immediate
parallel child is entered through its parent's local-environment relation. -/
theorem LocalTypeEnvironment.avoids_nested_parallel_interface
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {sibling left right : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer parentInterface siblingEnvironment
      sibling label localEnvironment)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hScoped : Disjoint parentInterface
      (PactType.ParallelInterfaces (.par left right childInterface))) :
    localEnvironment.AvoidsInterface childInterface := by
  apply hLocal.avoidsInterface_of_disjoint hOuterAvoids
  rw [Finset.disjoint_left] at hScoped ⊢
  intro message hParent hChild
  exact hScoped hParent
    (PactType.parallel_interface_subset_parallelInterfaces left right
      childInterface hChild)

private theorem hideOffers_partition (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface offers ∪ interfaceOffers interface offers = offers := by
  ext action
  simp [hideOffers, interfaceOffers]
  tauto

private theorem hideOffers_disjoint_interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) :
    Disjoint (hideOffers interface offers) (interfaceOffers interface offers) := by
  rw [Finset.disjoint_left]
  intro action hHidden hInterface
  exact (Finset.mem_filter.mp hHidden).2
    (Finset.mem_filter.mp hInterface).2

private theorem finset_eq_of_hideOffers_eq_of_interfaceOffers_eq
    (interface : Interface) {left right : Finset BareMessage}
    (hHidden : hideOffers interface left = hideOffers interface right)
    (hInterface : interfaceOffers interface left =
      interfaceOffers interface right) :
    left = right := by
  rw [← hideOffers_partition interface left,
    ← hideOffers_partition interface right, hHidden, hInterface]

private theorem hideOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left ∪ right) =
      hideOffers interface left ∪ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left ∪ right) =
      interfaceOffers interface left ∪ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem hideOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp [hideOffers, restrictTypeOffers]

private theorem interfaceOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    interfaceOffers interface (restrictTypeOffers interface offers) =
      restrictTypeOffers interface offers := by
  ext action
  simp [interfaceOffers, restrictTypeOffers]

private theorem hideOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left \ right) =
      hideOffers interface left \ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left \ right) =
      interfaceOffers interface left \ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem finset_sdiff_eq_self_of_disjoint {left right : Finset BareMessage}
    (hDisjoint : Disjoint left right) : left \ right = left := by
  ext action
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hLeft
    exact ⟨hLeft, fun hRight => Finset.disjoint_left.mp hDisjoint hLeft hRight⟩

private theorem hideOffers_eq_self_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    hideOffers interface offers = offers := by
  ext action
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hAction
    exact Finset.mem_filter.mpr ⟨hAction, hAvoids action hAction⟩

private theorem interfaceOffers_eq_empty_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    interfaceOffers interface offers = ∅ := by
  ext action
  simp only [interfaceOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hOffers, hInterface⟩
    exact (hAvoids action hOffers hInterface).elim
  · intro hEmpty
    simpa using hEmpty

/-- The product environment reconstruction uses only well-formedness and
avoidance of the current interface; exportedness is one sufficient way to
obtain those facts, but nested products use this more general form. -/
private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
    (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hOuterWellFormed : outer.WellFormed)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hOuterAvoids.1
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hOuterAvoids.2
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/
private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields
    (signature : TypeAlphabet) (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterWellFormed :=
    TypeAlphabet.environment_wellFormed hOuterEnvironment
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hImmediateAvoids :
      ∀ action ∈ outer.immediate, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_immediate_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hFutureAvoids :
      ∀ action ∈ outer.future, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_future_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hImmediateAvoids
  have hInterfaceOuterImmediate :=
    interfaceOffers_eq_empty_of_avoids interface outer.immediate hImmediateAvoids
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hFutureAvoids
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- Elimination form of `LocalTypeEnvironment` exposing the exact ordinary
environment equations without losing the clock alternative. -/
private theorem LocalTypeEnvironment.clock_or_ordinary
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    (outer.clock = true ∧
        siblingEnvironment = TypeEnvironment.tock ∧
        localEnvironment = TypeEnvironment.tock) ∨
      ∃ siblingTarget current future,
        outer.clock = false ∧
        siblingEnvironment.clock = false ∧
        TypeOffers siblingEnvironment sibling label siblingTarget
          current future ∧
        localEnvironment.clock = false ∧
        localEnvironment.immediate =
          outer.immediate ∪ restrictTypeOffers interface current ∧
        localEnvironment.future =
          (outer.future ∪ restrictTypeOffers interface future) \
            localEnvironment.immediate := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      exact Or.inl ⟨hClock, rfl, rfl⟩
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      exact Or.inr ⟨siblingTarget, current, future, hOuterClock,
        hSiblingClock, hOffers, hLocalClock, hImmediate, hFuture⟩

/-- Regression: the current syntactic linearity check does not yet imply
disjoint current/future decorations.  An `offer` may expose a branch head as
current while its else continuation immediately re-offers the same message. -/
theorem sameCycleMessageLinear_offer_else_current_future_overlap :
    let action : BareMessage := ("same", .send)
    let elseType : PactType := .message action.1 action.2
    let processType : PactType := .offer elseType [(action, .skip)]
    processType.SameCycleMessageLinear ∧
      TypeOffers TypeEnvironment.empty processType TypeLabel.silent elseType
        {action} {action} ∧
      ¬ Disjoint ({action} : Finset BareMessage) {action} := by
  dsimp
  constructor
  · simp [PactType.SameCycleMessageLinear,
      PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds]
  · constructor
    · have hOffers := TypeOffers.offer_else TypeEnvironment.empty
          (.message "same" .send) [(("same", .send), .skip)] (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed,
              TypeNoImmediateBranch, TypeResolved, typeBranchNeeds, typeNeed])
      simpa [typeBranchActions] using
        hOffers
    · intro hDisjoint
      have hMember : (("same", .send) : BareMessage) ∈
          ({("same", .send)} : Finset BareMessage) := by simp
      exact Finset.disjoint_left.mp hDisjoint hMember hMember

/-- Package explicitly chosen witness edges into the existential product test. -/
private theorem syncAutomatonEdges_of_witnesses
    (interface : Interface) {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hLeftWitness : leftWitness ∈ leftEdges)
    (hRightWitness : rightWitness ∈ rightEdges)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    syncAutomatonEdges interface leftEdges rightEdges left right := by
  exact ⟨leftWitness, hLeftWitness, rightWitness, hRightWitness, hSync⟩

/-- The ordinary local-environment fields, using independent witness offer
summaries, are exactly the strict witness synchronization predicate. -/
private theorem syncAutomatonEdgeWitnesses_of_ordinaryLocalFields
    (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hLeftMatch : matchesAutomatonOfferWitness left leftWitness)
    (hRightMatch : matchesAutomatonOfferWitness right rightWitness)
    (hLeftClock : left.environment.clock = false)
    (hRightClock : right.environment.clock = false)
    (hLeftImmediate : left.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightWitness.current)
    (hLeftFuture : left.environment.future =
      (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
        left.environment.immediate)
    (hRightImmediate : right.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftWitness.current)
    (hRightFuture : right.environment.future =
      (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
        right.environment.immediate)
    (hLabelSync : TypeLabel.Sync interface left.label.semantic
      right.label.semantic) :
    syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness := by
  unfold syncAutomatonEdgeWitnesses
  simp only [hLeftClock, if_false]
  rw [hOuter]
  exact ⟨hLeftMatch, hRightMatch,
    ⟨True.intro, hRightClock, hLeftImmediate, hLeftFuture,
      hRightImmediate, hRightFuture⟩, hLabelSync⟩

/-- Realizing the offer summaries existentially stored in two semantic local
judgments as resolved witness edges yields the compiler's existential product
test.  Actual edges are used as witnesses in the clock case. -/
private theorem localTypeEnvironments_to_syncAutomatonEdges
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterLocal : outer ∈ signature.localEnvironments :=
      signature.environments_subset_localEnvironments hOuterEnvironment
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterLocal hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields
          signature interface hAlphabet hInterface hOuterEnvironment
          hOuterClock hLeftClock hRightClock hLeftImmediate hLeftFuture
          hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Local-domain form of sibling-environment reconstruction.  Avoidance of
the current interface replaces exportedness/signature well-formedness. -/
private theorem localTypeEnvironments_to_syncAutomatonEdges_local
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.localEnvironments)
    (hOuterAvoids : outer.AvoidsInterface interface)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterEnvironment hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields_of_avoids
          interface
          (TypeAlphabet.localEnvironment_wellFormed hOuterEnvironment)
          hOuterAvoids hOuterClock hLeftClock hRightClock hLeftImmediate
          hLeftFuture hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Strict witness synchronization reconstructs the two semantic
sibling-local environments using the witness summaries, while the actual
edges retain the product target and exposed offer summary. -/
private theorem syncAutomatonEdgeWitnesses_to_localTypeEnvironments
    (interface : Interface)
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    {leftType leftTarget rightType rightTarget : PactType}
    (hLeftOffers : TypeOffers leftWitness.environment leftType
      leftWitness.label.semantic leftTarget leftWitness.current
      leftWitness.future)
    (hRightOffers : TypeOffers rightWitness.environment rightType
      rightWitness.label.semantic rightTarget rightWitness.current
      rightWitness.future)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    let outer := combineAutomatonEnvironment interface
      left.environment right.environment
    LocalTypeEnvironment outer interface right.environment rightType
        right.label.semantic left.environment ∧
      LocalTypeEnvironment outer interface left.environment leftType
        left.label.semantic right.environment := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨hLeftMatch, hRightMatch, hFields, hLabelSync⟩
  rcases hLeftMatch with ⟨hLeftSource, hLeftEnvironment, hLeftLabel⟩
  rcases hRightMatch with ⟨hRightSource, hRightEnvironment, hRightLabel⟩
  rw [hLeftEnvironment, hLeftLabel] at hLeftOffers
  rw [hRightEnvironment, hRightLabel] at hRightOffers
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp only [combineAutomatonEnvironment, TypeEnvironment.tock]
      exact ⟨LocalTypeEnvironment.clock TypeEnvironment.tock interface
          rightType right.label.semantic rfl,
        LocalTypeEnvironment.clock TypeEnvironment.tock interface
          leftType left.label.semantic rfl⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨_, hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      let outer := combineAutomatonEnvironment interface
        left.environment right.environment
      have hOuterClock : outer.clock = false := by
        simp [outer, combineAutomatonEnvironment, hLeftClock, hRightClock]
      change LocalTypeEnvironment outer interface right.environment rightType
          right.label.semantic left.environment ∧
        LocalTypeEnvironment outer interface left.environment leftType
          left.label.semantic right.environment
      exact ⟨
        LocalTypeEnvironment.ordinary outer right.environment left.environment
          interface rightType rightTarget right.label.semantic
          rightWitness.current rightWitness.future hOuterClock hRightClock
          hRightOffers hLeftClock hLeftImmediate hLeftFuture,
        LocalTypeEnvironment.ordinary outer left.environment right.environment
          interface leftType leftTarget left.label.semantic
          leftWitness.current leftWitness.future hOuterClock hLeftClock
          hLeftOffers hRightClock hRightImmediate hRightFuture⟩

/-- The step-for-step relation of Lemma 4.5. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')

/-- The atomic `skip` constructor already satisfies the full step correspondence. -/
theorem compileType_skip_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .skip (compileType signature .skip)) := by
  let related : PactType → TypeAutomatonState → Prop :=
    fun residual state => residual = .skip ∧ state = .root
  refine ⟨
    { relation := related
      initial := by simp [related, compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      initial_mem := by simp [compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hAlphabet
  rcases hRelated with ⟨rfl, rfl⟩
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hAlphabetParts :
        env ∈ signature.environments ∧
          label ∈ signature.labels ∧
          { current := current, future := future } ∈
            signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hAlphabet
    exact hAlphabetParts.1
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  constructor
  · rintro ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
            refine ⟨.root, ?_, by simp [related]⟩
            simp only [TypeAutomaton.HasEdge]
            have hSymbol :
                { environment := env, label := TypeLabel.silent,
                  offers := { current := ∅, future := ∅ } } ∈
                    signature.transitionAlphabet := by
              simpa [compileType] using hAlphabet
            simp [compileType, typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, resolvedAutomatonEdges]
            exact ⟨env, ⟨hLocalEnvironment, conditions.2.1,
              conditions.2.2⟩, by simp [hSymbol]⟩
  · rintro ⟨state', hEdge, hTarget⟩
    rcases hTarget with ⟨rfl, rfl⟩
    have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
    simp only [TypeAutomaton.HasEdge] at hEdge
    simp [compileType, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, resolvedAutomatonEdges] at hEdge
    simp only [DecoratedTypeTransition]
    aesop

/-- The firing edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_action_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.message msg dir)
      current := {(msg, dir)}
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.message msg dir)
        current := {(msg, dir)}
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNeed]
  · simp [hSymbol]

/-- The waiting edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_wait_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNoNeed : ¬ env.hasNeed (msg, dir)) (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := {(msg, dir)}
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := {(msg, dir)}
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNoNeed, hClock]
  · simp [hSymbol]

/-- The completed atomic message idles exactly like semantic `skip`. -/
theorem compileType_message_final_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.message_action_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) (TypeLabel.message msg dir)
      .skip current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.message msg dir = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.message]

private theorem TypeOffers.message_wait_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) TypeLabel.silent
      (.message msg dir) current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.silent]

private theorem TypeOffers.skip_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .skip TypeLabel.silent .skip current future) :
    current = ∅ ∧ future = ∅ := by
  cases hOffers <;>
    simp_all

/-- Semantic steps of an atomic message have matching compiled edges. -/
theorem compileType_message_step_to_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.message msg dir)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.message msg dir)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.message msg dir) state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | message_source =>
      cases hTransition with
      | action _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_action_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | action_wait _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.message_source msg dir⟩
          apply compileType_message_wait_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

  | message_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_final_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_message_edge_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.message msg dir)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = {(msg, dir)} ∧ future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨edgeEnv, ⟨_, hNeed⟩, rfl⟩
          simp_all
        · rcases hWaiting with ⟨edgeEnv, ⟨_, hClock, hNoNeed⟩, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic message is justified by its semantic step. -/
theorem compileType_message_edge_to_step
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hEdge : (compileType signature (.message msg dir)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.message msg dir) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_message_edge_cases signature msg dir hEdge
  rcases hCases with hFiring | hWaiting | hFinal
  · rcases hFiring with ⟨rfl, rfl, rfl, rfl, rfl, hNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_final =>
            refine ⟨TypeTransition.action env msg dir
              ⟨hWellFormed, hNeed⟩, ?_⟩
            simpa using
              TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_source =>
            refine ⟨TypeTransition.action_wait env msg dir
              ⟨hWellFormed, hNoNeed, hClock⟩, ?_⟩
            simpa using
              TypeOffers.action_wait env msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | message_final =>
        cases hTarget with
        | message_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic message constructor satisfies the complete step correspondence. -/
theorem compileType_message_correspondence
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    Nonempty (TypeAutomatonCorrespondence (.message msg dir)
      (compileType signature (.message msg dir))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.message msg dir) state residual
      initial := compileType_initial_relation signature (.message msg dir)
      initial_mem := compileType_initial_mem signature (.message msg dir)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_message_step_to_edge signature msg dir
      hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_message_edge_to_step signature msg dir
      hEnvironment hRelated hEdge hTarget

/-! ### Atomic clock correspondence -/

/-- The firing edge of an atomic clock is present with its exact decoration. -/
theorem compileType_tock_action_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = true)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.tock
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.tock
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A non-clock environment gives an atomic clock its silent waiting edge. -/
theorem compileType_tock_wait_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A completed atomic clock has the standard silent idle edge. -/
theorem compileType_tock_final_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.tock_action_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.tock .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.tock = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.tock_wait_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.silent .tock current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic clock have matching compiled edges. -/
theorem compileType_tock_step_to_edge
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation .tock state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature .tock).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature .tock).HasEdge state env label offers state' ∧
        TypeCompilationRelation .tock state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | cycle_source =>
      cases hTransition with
      | cycle _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_action_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | cycle_wait _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.cycle_source⟩
          apply compileType_tock_wait_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
  | cycle_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_final_edge signature
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_tock_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature .tock).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hAction | hFinal
        · rcases hAction with ⟨edgeEnv, hLocal, rfl⟩
          by_cases hClock : edgeEnv.clock
          · left
            simp_all
          · right
            left
            simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic clock is justified by its semantic step. -/
theorem compileType_tock_edge_to_step
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation .tock state residual)
    (hEdge : (compileType signature .tock).HasEdge state env label offers state')
    (hTarget : TypeCompilationRelation .tock state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_tock_edge_cases signature hEdge
  rcases hCases with hAction | hWaiting | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.cycle env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle env ⟨hWellFormed, hClock⟩⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_source =>
            exact ⟨TypeTransition.cycle_wait env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle_wait env ⟨hWellFormed, hClock⟩⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | cycle_final =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic clock constructor satisfies the complete step correspondence. -/
theorem compileType_tock_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .tock
      (compileType signature .tock)) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation .tock state residual
      initial := compileType_initial_relation signature .tock
      initial_mem := compileType_initial_mem signature .tock
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_tock_step_to_edge signature hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_tock_edge_to_step signature
      hEnvironment hRelated hEdge hTarget

/-! ### Atomic progress correspondence -/

/-- The emitting edge of an atomic progress marker is present. -/
theorem compileType_progress_action_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.progress pid)
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.progress pid)
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.progress pid)
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment]
  · simp [hSymbol]

/-- A completed progress marker has the standard silent idle edge. -/
theorem compileType_progress_final_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.progress_fields
    {env : TypeEnvironment} {pid : ProcId}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.progress pid) (TypeLabel.progress pid)
      .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.progress pid = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic progress marker have matching compiled edges. -/
theorem compileType_progress_step_to_edge
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.progress pid)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.progress pid)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.progress pid) state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | progress_source =>
      cases hTransition with
      | progress _ _ =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.progress_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_action_edge signature pid
          · exact hEnvironment
          · simpa [compileType] using hSymbol
  | progress_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_final_edge signature pid
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_progress_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.progress pid)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.progress pid ∧ current = ∅ ∧ future = ∅) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hAction | hFinal
        · rcases hAction with ⟨edgeEnv, _, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic progress marker has a semantic step. -/
theorem compileType_progress_edge_to_step
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hEdge : (compileType signature (.progress pid)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.progress pid) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_progress_edge_cases signature pid hEdge
  rcases hCases with hAction | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl⟩
    cases hRelated with
    | progress_source =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.progress env pid hWellFormed,
              TypeOffers.progress env pid hWellFormed⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | progress_final =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic progress constructor satisfies the complete correspondence. -/
theorem compileType_progress_correspondence
    (signature : TypeAlphabet) (pid : ProcId) :
    Nonempty (TypeAutomatonCorrespondence (.progress pid)
      (compileType signature (.progress pid))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.progress pid) state residual
      initial := compileType_initial_relation signature (.progress pid)
      initial_mem := compileType_initial_mem signature (.progress pid)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_progress_step_to_edge signature pid hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_progress_edge_to_step signature pid
      hEnvironment hRelated hEdge hTarget

/-! ### Raw atomic fragment correspondence -/

/-- The raw `skip` fragment has exactly its well-formed non-clock idle
self-loops, for every construction-local environment. -/
theorem compilationFragmentStepCorrect_skip
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .skip := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated
  rcases offers with ⟨current, future⟩
  constructor
  · rintro ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
        refine ⟨.root, ?_, TypeCompilationRelation.skip⟩
        refine ⟨
          { source := .root
            environment := env
            label := .visible TypeLabel.silent
            current := ∅
            future := .explicit ∅
            target := .root }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, hLocalEnvironment, conditions.2.1,
          conditions.2.2]
  · rintro ⟨target, hEdge, hTarget⟩
    rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
      hCurrent, hFuture, hEdgeTarget⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hPending
    rcases hPending with ⟨edgeEnvironment,
      ⟨hEdgeLocal, hClock, hImmediate⟩, rfl⟩
    simp at hSource hEnvironment hLabel hCurrent hFuture hEdgeTarget
    subst_vars
    cases hTarget
    have hWellFormed :=
      TypeAlphabet.localEnvironment_wellFormed hEdgeLocal
    exact ⟨TypeTransition.skip edgeEnvironment
        ⟨hWellFormed, hClock, hImmediate⟩,
      TypeOffers.skip edgeEnvironment
        ⟨hWellFormed, hClock, hImmediate⟩⟩

private theorem compileTypeFuel_message_resolved_edge_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.message msg dir))
      (.message msg dir)).HasResolvedEdge source env label
        { current := current, future := future } target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧
        label = TypeLabel.silent ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
      (source = .final ∧ target = .final ∧
        label = TypeLabel.silent ∧ current = ∅ ∧ future = ∅ ∧
        env.clock = false ∧ env.immediate = ∅) := by
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    at hPending
  rcases hPending with hFiring | hWaiting | hFinal
  · rcases hFiring with ⟨edgeEnvironment, hNeed, rfl⟩
    simp_all
  · rcases hWaiting with ⟨edgeEnvironment, ⟨hClock, hNoNeed⟩, rfl⟩
    simp_all
  · rcases hFinal with
      ⟨edgeEnvironment, ⟨_, hClock, hImmediate⟩, rfl⟩
    simp_all

/-- Raw message correspondence includes firing, same-cycle waiting, and the
completed idle state over every construction-local environment. -/
theorem compilationFragmentStepCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFragmentStepCorrect signature (.message msg dir) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  have hWellFormed :=
    TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  cases hRelated with
  | message_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | action _ _ _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.message_action_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible (TypeLabel.message msg dir)
                current := {(msg, dir)}
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment, conditions.2]
        | action_wait _ _ _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.message_wait_fields hOffers
            refine ⟨.root, ?_, TypeCompilationRelation.message_source msg dir⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.silent
                current := {(msg, dir)}
                future := .explicit ∅
                target := .root }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment, conditions.2.1,
              conditions.2.2]
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileTypeFuel_message_resolved_edge_cases
          signature msg dir hEdge
        rcases hCases with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨_, rfl, rfl, rfl, rfl, hNeed⟩
          cases hTarget with
          | message_final =>
              refine ⟨TypeTransition.action env msg dir
                  ⟨hWellFormed, hNeed⟩, ?_⟩
              simpa using
                TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩
        · rcases hWaiting with
            ⟨_, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩
          cases hTarget with
          | message_source =>
              refine ⟨TypeTransition.action_wait env msg dir
                  ⟨hWellFormed, hNoNeed, hClock⟩, ?_⟩
              simpa using TypeOffers.action_wait env msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩
        · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
          simp at hSource
  | message_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment, conditions.2.1,
              conditions.2.2]
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileTypeFuel_message_resolved_edge_cases
          signature msg dir hEdge
        rcases hCases with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨hSource, _, _, _, _, _⟩
          simp at hSource
        · rcases hWaiting with ⟨hSource, _, _, _, _, _, _⟩
          simp at hSource
        · rcases hFinal with
            ⟨_, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
          cases hTarget with
          | message_final =>
              exact ⟨TypeTransition.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩,
                TypeOffers.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩⟩

private theorem compileTypeFuel_progress_resolved_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.progress pid))
      (.progress pid)).HasResolvedEdge source env label
        { current := current, future := future } target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.progress pid ∧ current = ∅ ∧ future = ∅) ∨
      (source = .final ∧ target = .final ∧
        label = TypeLabel.silent ∧ current = ∅ ∧ future = ∅ ∧
        env.clock = false ∧ env.immediate = ∅) := by
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    simp_all
  · rcases hFinal with
      ⟨edgeEnvironment, ⟨_, hClock, hImmediate⟩, rfl⟩
    simp_all

/-- Raw progress-marker correspondence over construction-local environments. -/
theorem compilationFragmentStepCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFragmentStepCorrect signature (.progress pid) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  have hWellFormed :=
    TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  cases hRelated with
  | progress_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | progress =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.progress_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible (TypeLabel.progress pid)
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment]
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_progress_resolved_edge_cases signature pid hEdge
          with hAction | hFinal
        · rcases hAction with ⟨_, rfl, rfl, rfl, rfl⟩
          cases hTarget with
          | progress_final =>
              exact ⟨TypeTransition.progress env pid hWellFormed,
                TypeOffers.progress env pid hWellFormed⟩
        · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
          simp at hSource
  | progress_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment, conditions.2.1,
              conditions.2.2]
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_progress_resolved_edge_cases signature pid hEdge
          with hAction | hFinal
        · rcases hAction with ⟨hSource, _, _, _, _⟩
          simp at hSource
        · rcases hFinal with
            ⟨_, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
          cases hTarget with
          | progress_final =>
              exact ⟨TypeTransition.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩,
                TypeOffers.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩⟩

private theorem compileTypeFuel_tock_resolved_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileTypeFuel signature (typeCompilationFuel .tock)
      .tock).HasResolvedEdge source env label
        { current := current, future := future } target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    at hPending
  rcases hPending with hAction | hFinal
  · rcases hAction with ⟨edgeEnvironment, _, rfl⟩
    by_cases hClock : edgeEnvironment.clock = true
    · left
      simp_all [hClock]
    · right
      left
      have hFalse : edgeEnvironment.clock = false := by
        exact Bool.eq_false_of_not_eq_true hClock
      simp_all [hClock, hFalse]
  · rcases hFinal with
      ⟨edgeEnvironment, ⟨_, hClock, hImmediate⟩, rfl⟩
    simp_all

/-- Raw clock correspondence over construction-local environments. -/
theorem compilationFragmentStepCorrect_tock
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .tock := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  have hWellFormed :=
    TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  cases hRelated with
  | cycle_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | cycle _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.tock_action_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.tock
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            left
            exact ⟨env, hLocalEnvironment, by simp [conditions.2]⟩
        | cycle_wait _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.tock_wait_fields hOffers
            refine ⟨.root, ?_, TypeCompilationRelation.cycle_source⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .root }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            left
            exact ⟨env, hLocalEnvironment, by simp [conditions.2]⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_tock_resolved_edge_cases signature hEdge with
          hAction | hWaiting | hFinal
        · rcases hAction with ⟨_, rfl, rfl, rfl, rfl, hClock⟩
          cases hTarget with
          | cycle_final =>
              exact ⟨TypeTransition.cycle env ⟨hWellFormed, hClock⟩,
                TypeOffers.cycle env ⟨hWellFormed, hClock⟩⟩
        · rcases hWaiting with ⟨_, rfl, rfl, rfl, rfl, hClock⟩
          cases hTarget with
          | cycle_source =>
              exact ⟨TypeTransition.cycle_wait env ⟨hWellFormed, hClock⟩,
                TypeOffers.cycle_wait env ⟨hWellFormed, hClock⟩⟩
        · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
          simp at hSource
  | cycle_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
            refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, hLocalEnvironment, conditions.2.1,
              conditions.2.2]
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_tock_resolved_edge_cases signature hEdge with
          hAction | hWaiting | hFinal
        · rcases hAction with ⟨hSource, _, _, _, _, _⟩
          simp at hSource
        · rcases hWaiting with ⟨hSource, _, _, _, _, _⟩
          simp at hSource
        · rcases hFinal with
            ⟨_, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
          cases hTarget with
          | cycle_final =>
              exact ⟨TypeTransition.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩,
                TypeOffers.skip env
                  ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- A free variable contributes only an internal recursion marker, never a
visible raw step.  An enclosing recursion binder is solely responsible for
turning that marker into a silent backedge. -/
theorem compilationFragmentStepCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationFragmentStepCorrect signature (.var name) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated
  constructor
  · rintro ⟨hTransition, _⟩
    cases hTransition
  · rintro ⟨target, hEdge, _⟩
    rcases hEdge with ⟨edge, hPending, _, _, hLabel, _, _, _⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hPending
    rcases hPending with ⟨_, _, rfl⟩
    simp at hLabel

/-! ### Ordinary choice correspondence -/

/-- The two graph-future calculations needed to decorate the fresh selection
edges of an ordinary choice.  This isolates the graph/syntax future theorem
from the otherwise structural correspondence argument. -/
def ChoiceFutureCorrect
    (signature : TypeAlphabet) (left right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 leftFragment.initial) =
      typeFutureOffers left ∧
    computeFuture pending (.child 1 rightFragment.initial) =
      typeFutureOffers right

private theorem buildChoiceAutomaton_hasResolvedEdge_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : left.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildChoiceAutomaton signature left right selectionLeft selectionRight)
        (.child 0 source) env label offers (.child 0 target) ↔
      AutomatonFragment.HasResolvedEdge left source env label offers target := by
  classical
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  have hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hTargets
  have hCard : left.states.card ≤ choice.states.card := by
    have hSubset : childStates 0 left ⊆ choice.states := by
      intro state hState
      simp [choice, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      left.states.card = (childStates 0 left).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ choice.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      injection hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
          left right selectionLeft selectionRight referenced hClosed
          hReferenced hCard
        simp only [hSpec]
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_left signature left right
        selectionLeft selectionRight source (childPendingEdge 0 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 0 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
            left right selectionLeft selectionRight referenced hClosed
            hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem buildChoiceAutomaton_hasResolvedEdge_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : right.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildChoiceAutomaton signature left right selectionLeft selectionRight)
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge right source env label offers target := by
  classical
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  have hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hTargets
  have hCard : right.states.card ≤ choice.states.card := by
    have hSubset : childStates 1 right ⊆ choice.states := by
      intro state hState
      simp [choice, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ choice.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      injection hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
          left right selectionLeft selectionRight referenced hClosed
          hReferenced hCard
        simp only
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildChoiceAutomaton_outgoing_right signature left right
        selectionLeft selectionRight source (childPendingEdge 1 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
            left right selectionLeft selectionRight referenced hClosed
            hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem buildChoiceAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    AutomatonFragment.HasResolvedEdge fragment .root env label offers target ↔
      (env ∈ signature.localEnvironments ∧ label = selectionLeft ∧
        offers.current = ∅ ∧
        computeFuture pending (.child 0 left.initial) = offers.future ∧
        target = .child 0 left.initial) ∨
      (env ∈ signature.localEnvironments ∧ label = selectionRight ∧
        offers.current = ∅ ∧
        computeFuture pending (.child 1 right.initial) = offers.future ∧
        target = .child 1 right.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildChoiceAutomaton,
    finishAutomatonFragment, childPendingEdges, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨edge, ((hLeft | hRight) | hSelection), hSource,
      hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · rcases hLeft with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨edgeEnvironment, hLocal, hEdge | hEdge⟩
      · rw [hEdge] at hSource hEnvironment hLabel hCurrent hFuture hTarget
        simp only [Finset.sdiff_empty, childState] at hFuture
        left
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        aesop
      · rw [hEdge] at hSource hEnvironment hLabel hCurrent hFuture hTarget
        simp only [Finset.sdiff_empty, childState] at hFuture
        right
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        aesop
  · rintro (hLeft | hRight)
    · rcases hLeft with ⟨hLocal, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible selectionLeft
          current := ∅
          future := .at (.child 0 left.initial) ∅
          target := .child 0 left.initial }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact ⟨env, hLocal, Or.inl rfl⟩
      · simp [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hRight with ⟨hLocal, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible selectionRight
          current := ∅
          future := .at (.child 1 right.initial) ∅
          target := .child 1 right.initial }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact ⟨env, hLocal, Or.inr rfl⟩
      · simp [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm

private theorem choiceFutureCorrect_core
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right)
    (hLeftClosed :
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let fragment := compileTypeFuel signature fuel left
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed)
    (hRightClosed :
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let fragment := compileTypeFuel signature fuel right
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 0 leftFragment.initial) =
        typeFutureOffers left ∧
      computeFuture pending (.child 1 rightFragment.initial) =
        typeFutureOffers right := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftState : leftFragment.initial ∈ leftFragment.states := by
    exact compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightState : rightFragment.initial ∈ rightFragment.states := by
    exact compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hLeftCard : leftFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 leftFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      leftFragment.states.card = (childStates 0 leftFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hRightCard : rightFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 rightFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      rightFragment.states.card = (childStates 1 rightFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hLeftSemantic : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      leftFragment.initial = typeFutureOffers left := by
    unfold CompilationFutureCorrect at hLeftCorrect
    have hRelation := compileTypeFuel_initial_relation signature fuel left
      hLeftFuel
    have hResult := hLeftCorrect leftFragment.initial left hRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left
      hLeftFuel (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    unfold CompilationFutureCorrect at hRightCorrect
    have hRelation := compileTypeFuel_initial_relation signature fuel right
      hRightFuel
    have hResult := hRightCorrect rightFragment.initial right hRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature right
      hRightFuel (typeCompilationFuel_sufficient right)
    simpa [rightFragment, hStable] using hResult
  constructor
  · rw [buildChoiceAutomaton_computeFuture_left signature leftFragment
      rightFragment selectionLeft selectionRight leftFragment.initial
      hLeftClosed hLeftState hLeftCard]
    exact hLeftSemantic
  · rw [buildChoiceAutomaton_computeFuture_right signature leftFragment
      rightFragment selectionLeft selectionRight rightFragment.initial
      hRightClosed hRightState hRightCard]
    exact hRightSemantic

/-- Choice-root future correctness follows compositionally from correctness
of both compiled children; reference closure is now supplied by the compiler
invariant rather than exposed as a separate hypothesis. -/
theorem choiceFutureCorrect_of_compilation
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    ChoiceFutureCorrect signature left right := by
  apply choiceFutureCorrect_core signature left right
    TypeLabel.silent TypeLabel.silent hLeftCorrect hRightCorrect
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]

/-- Visible edges inside the left tagged child of a compiled choice are
exactly the standalone child's visible edges. -/
theorem compileType_choice_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge
        (.child 0 source) env label offers (.child 0 target) ↔
      (compileType signature left).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 0 source) (.child 0 target) env label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature left source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : leftFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent source target env label
      offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
    (typeCompilationFuel_sufficient left)
  simpa only [leftFragment, hStable]

/-- Visible edges inside the right tagged child of a compiled choice are
exactly the standalone child's visible edges. -/
theorem compileType_choice_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 1 source) (.child 1 target) env label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature right source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : rightFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent source target env label
      offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
    (typeCompilationFuel_sufficient right)
  simpa only [rightFragment, hStable]

theorem compileType_choice_left_child_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      (.child 0 source) env label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
      (compileType signature left).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 0 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
      TypeLabel.silent TypeLabel.silent source pendingEdge).mp
      ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_choice_left_child_edge_iff signature left right source
    childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

theorem compileType_choice_right_child_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      (compileType signature right).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      (.child 1 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
      TypeLabel.silent TypeLabel.silent source pendingEdge).mp
      ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_choice_right_child_edge_iff signature left right source
    childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every public edge leaving an ordinary-choice root is one of its two
selection edges, with the graph-resolved child future. -/
theorem compileType_choice_root_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hEdge : (compileType signature (.choice left right)).HasEdge
      .root env label offers target) :
    (label = TypeLabel.silent ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers left ∧
        target = .child 0 (compileType signature left).initial) ∨
      (label = TypeLabel.silent ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers right ∧
        target = .child 1 (compileType signature right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
    hLeftFuel (typeCompilationFuel_sufficient left)
  have hRightStable := compileTypeFuel_eq_of_sufficient signature right
    hRightFuel (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
      .root target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  have hCases :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment TypeLabel.silent TypeLabel.silent env label offers
      target).mp hResolved
  unfold ChoiceFutureCorrect at hFuture
  rcases hCases with hLeft | hRight
  · left
    rcases hLeft with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.1.symm.trans hComputed).symm
    · simpa [leftFragment, compileType, hLeftStable] using hTarget
  · right
    rcases hRight with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.2.symm.trans hComputed).symm
    · simpa [rightFragment, compileType, hRightStable] using hTarget

/-- The left selection edge of an ordinary choice, conditional only on the
graph-future equality used in its decoration. -/
theorem compileType_choice_left_selection_edge
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers left))
      (.child 0 (compileType signature left).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 leftFragment.initial) = typeFutureOffers left := by
    simpa [pending] using hFuture.1
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers left
      target := .child 0 leftFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 leftFragment.initial) ∅
        target := .child 0 leftFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inl ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

/-- The right selection edge of an ordinary choice. -/
theorem compileType_choice_right_selection_edge
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.choice left right)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    TypeLabel.silent TypeLabel.silent
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : rightFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature right
        (by simpa [rightFragment] using hRightFuel)
        (typeCompilationFuel_sufficient right))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture.2
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inr ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

private theorem TypeOffers.choice_left_fields
    {env : TypeEnvironment} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.choice left right) TypeLabel.silent left
      current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.choice_right_fields
    {env : TypeEnvironment} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.choice left right) TypeLabel.silent right
      current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Root-state step correspondence for the left selection of an ordinary
choice.  Child-state lifting is deliberately not needed here. -/
theorem compileType_choice_left_selection_step_iff
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.choice left right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left ↔
      ∃ state',
        (compileType signature (.choice left right)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) state' ∧
          TypeCompilationRelation (.choice left right) state' left := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
    · exact compileType_choice_left_selection_edge signature left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.choice_left left right left _
        (compileType_initial_relation signature left)
  · intro _
    exact ⟨TypeTransition.choice_left env left right hWellFormed,
      TypeOffers.choice_left env left right hWellFormed⟩

/-- Root-state step correspondence for the right selection of an ordinary
choice. -/
theorem compileType_choice_right_selection_step_iff
    (signature : TypeAlphabet) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : ChoiceFutureCorrect signature left right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.choice left right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.choice left right)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.choice left right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_choice_right_selection_edge signature left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.choice_right left right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.choice_right env left right hWellFormed,
      TypeOffers.choice_right env left right hWellFormed⟩

/-- Ordinary choice preserves full step correspondence once both closed child
compilations and their graph futures are correct. -/
theorem compilationStepCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationStepCorrect signature left)
    (hRightStep : CompilationStepCorrect signature right)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationStepCorrect signature (.choice left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label { current := current, future := future } ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hFields :
        env ∈ signature.environments ∧
          label ∈ signature.labels ∧
          { current := current, future := future } ∈
            signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact hFields.1
  have hChoiceFuture := choiceFutureCorrect_of_compilation signature left right
    hLeftFuture hRightFuture
  cases hRelated with
  | choice_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | choice_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_left_fields hOffers
            refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
            · exact compileType_choice_left_selection_edge signature left right
                hEnvironment hChoiceFuture hSignatureSymbol
            · exact TypeCompilationRelation.choice_left left right left _
                (compileType_initial_relation signature left)
        | choice_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_right_fields hOffers
            refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
            · exact compileType_choice_right_selection_edge signature left right
                hEnvironment hChoiceFuture hSignatureSymbol
            · exact TypeCompilationRelation.choice_right left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileType_choice_root_edge_cases signature left right
          hSignatureSymbol hChoiceFuture hEdge
        rcases hCases with hLeft | hRight
        · rcases hLeft with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | choice_left _ _ targetResidual _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.choice_left env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.choice_left env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
        · rcases hRight with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | choice_right _ _ targetResidual _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.choice_right env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.choice_right env left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature left).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hLeftStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · exact (compileType_choice_left_child_edge_iff signature left right
              childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.choice_left left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_choice_left_child_edge_cases signature left right
          hSignatureSymbol hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | choice_left _ _ _ _ hChildTarget =>
            exact (hLeftStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature right).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileType_choice_right_child_edge_iff signature left right
              childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.choice_right left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_choice_right_child_edge_cases signature left right
          hSignatureSymbol hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | choice_right _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-! ### Fair-choice selection edges -/

/-- Graph-future correctness for the two fair-choice selection edges. -/
def FairChoiceFutureCorrect
    (signature : TypeAlphabet) (bid : BranchId)
    (left right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 leftFragment.initial) =
      typeFutureOffers left ∧
    computeFuture pending (.child 1 rightFragment.initial) =
      typeFutureOffers right

/-- Fair-choice selection futures are the same tagged-child graph calculation
as ordinary choice, with observable branch labels on the two root edges. -/
theorem fairChoiceFutureCorrect_of_compilation
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    FairChoiceFutureCorrect signature bid left right := by
  apply choiceFutureCorrect_core signature left right
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    hLeftCorrect hRightCorrect
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]
  · apply compileTypeFuel_referencesClosed
    simp [TypeCompilationFuelSufficient]

/-- Visible edges inside the left tagged child of a compiled fair choice are
exactly the standalone child's visible edges. -/
theorem compileType_fairChoice_left_child_edge_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge
        (.child 0 source) env label offers (.child 0 target) ↔
      (compileType signature left).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 0 source) (.child 0 target) env
      label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature left source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : leftFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
      source target env label offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
    (typeCompilationFuel_sufficient left)
  simpa only [leftFragment, hStable]

/-- Visible edges inside the right tagged child of a compiled fair choice are
exactly the standalone child's visible edges. -/
theorem compileType_fairChoice_right_child_edge_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 1 source) (.child 1 target) env
      label offers hSymbol,
    compileType_hasEdge_iff_hasResolvedEdge signature right source target env
      label offers hSymbol]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : rightFragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment,
    buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
      source target env label offers hTargets]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
    (typeCompilationFuel_sufficient right)
  simpa only [rightFragment, hStable]

/-- Every edge from a left-tagged fair-choice state remains in the left
tagged child. -/
theorem compileType_fairChoice_left_child_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      (.child 0 source) env label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
      (compileType signature left).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 0 source) target env label offers
      hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_left signature leftFragment rightFragment
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) source
      pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_fairChoice_left_child_edge_iff signature bid left right
    source childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every edge from a right-tagged fair-choice state remains in the right
tagged child. -/
theorem compileType_fairChoice_right_child_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      (compileType signature right).HasEdge source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) (.child 1 source) target env label offers
      hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildChoiceAutomaton_outgoing_right signature leftFragment rightFragment
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) source
      pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_fairChoice_right_child_edge_iff signature bid left right
    source childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- Every public edge leaving a fair-choice root is one of its two labelled
selection edges, with the graph-resolved child future. -/
theorem compileType_fairChoice_root_edge_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hEdge : (compileType signature (.fairChoice bid left right)).HasEdge
      .root env label offers target) :
    (label = TypeLabel.fair bid true ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers left ∧
        target = .child 0 (compileType signature left).initial) ∨
      (label = TypeLabel.fair bid false ∧ offers.current = ∅ ∧
        offers.future = typeFutureOffers right ∧
        target = .child 1 (compileType signature right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
    hLeftFuel (typeCompilationFuel_sufficient left)
  have hRightStable := compileTypeFuel_eq_of_sufficient signature right
    hRightFuel (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature
      (.fairChoice bid left right) .root target env label offers hSymbol).mp
      hEdge
  rw [hFragment] at hResolved
  have hCases :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false) env
      label offers target).mp hResolved
  unfold FairChoiceFutureCorrect at hFuture
  rcases hCases with hLeft | hRight
  · left
    rcases hLeft with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.1.symm.trans hComputed).symm
    · simpa [leftFragment, compileType, hLeftStable] using hTarget
  · right
    rcases hRight with ⟨_, hLabel, hCurrent, hComputed, hTarget⟩
    refine ⟨hLabel, hCurrent, ?_, ?_⟩
    · exact (hFuture.2.symm.trans hComputed).symm
    · simpa [rightFragment, compileType, hRightStable] using hTarget

/-- The left selection edge of a fair choice. -/
theorem compileType_fairChoice_left_selection_edge
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge .root env
      (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left))
      (.child 0 (compileType signature left).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 leftFragment.initial) = typeFutureOffers left := by
    simpa [pending] using hFuture.1
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.fair bid true)
      current := ∅
      future := typeFutureOffers left
      target := .child 0 leftFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.fair bid true)
        current := ∅
        future := .at (.child 0 leftFragment.initial) ∅
        target := .child 0 leftFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inl ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

/-- The right selection edge of a fair choice. -/
theorem compileType_fairChoice_right_selection_edge
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.fairChoice bid left right)).HasEdge .root env
      (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : rightFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature right
        (by simpa [rightFragment] using hRightFuel)
        (typeCompilationFuel_sufficient right))
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture.2
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.fair bid false)
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.fair bid false)
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      right
      right
      exact ⟨env, hLocalEnvironment, Or.inr ⟨rfl, rfl⟩⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hInitial]

private theorem TypeOffers.fair_left_fields
    {env : TypeEnvironment} {bid : BranchId} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.fairChoice bid left right)
      (TypeLabel.fair bid true) left current future) :
    current = ∅ ∧ future = typeFutureOffers left := by
  generalize hLabel : TypeLabel.fair bid true = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.fair_right_fields
    {env : TypeEnvironment} {bid : BranchId} {left right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.fairChoice bid left right)
      (TypeLabel.fair bid false) right current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.fair bid false = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Root-state step correspondence for the taken-left fair branch. -/
theorem compileType_fairChoice_left_selection_step_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid true)
      (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.fairChoice bid left right)
        (TypeLabel.fair bid true)
        (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left ↔
      ∃ state',
        (compileType signature (.fairChoice bid left right)).HasEdge .root env
            (TypeLabel.fair bid true)
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) state' ∧
          TypeCompilationRelation (.fairChoice bid left right) state' left := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
    · exact compileType_fairChoice_left_selection_edge signature bid left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.fair_left bid left right left _
        (compileType_initial_relation signature left)
  · intro _
    exact ⟨TypeTransition.fair_left env bid left right hWellFormed,
      TypeOffers.fair_left env bid left right hWellFormed⟩

/-- Root-state step correspondence for the taken-right fair branch. -/
theorem compileType_fairChoice_right_selection_step_iff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : FairChoiceFutureCorrect signature bid left right)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.fair bid false)
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.fairChoice bid left right)
        (TypeLabel.fair bid false)
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.fairChoice bid left right)).HasEdge .root env
            (TypeLabel.fair bid false)
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.fairChoice bid left right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_fairChoice_right_selection_edge signature bid left right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.fair_right bid left right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.fair_right env bid left right hWellFormed,
      TypeOffers.fair_right env bid left right hWellFormed⟩

/-- Fair choice preserves full step correspondence once both closed child
compilations and their graph futures are correct. -/
theorem compilationStepCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftStep : CompilationStepCorrect signature left)
    (hRightStep : CompilationStepCorrect signature right)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationStepCorrect signature (.fairChoice bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label { current := current, future := future } ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hFields :
        env ∈ signature.environments ∧
          label ∈ signature.labels ∧
          { current := current, future := future } ∈
            signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact hFields.1
  have hFairFuture := fairChoiceFutureCorrect_of_compilation signature bid
    left right hLeftFuture hRightFuture
  cases hRelated with
  | fair_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | fair_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_left_fields hOffers
            refine ⟨.child 0 (compileType signature left).initial, ?_, ?_⟩
            · exact compileType_fairChoice_left_selection_edge signature bid
                left right hEnvironment hFairFuture hSignatureSymbol
            · exact TypeCompilationRelation.fair_left bid left right left _
                (compileType_initial_relation signature left)
        | fair_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_right_fields hOffers
            refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
            · exact compileType_fairChoice_right_selection_edge signature bid
                left right hEnvironment hFairFuture hSignatureSymbol
            · exact TypeCompilationRelation.fair_right bid left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hCases := compileType_fairChoice_root_edge_cases signature bid
          left right hSignatureSymbol hFairFuture hEdge
        rcases hCases with hLeft | hRight
        · rcases hLeft with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | fair_left _ _ _ targetResidual _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.fair_left env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.fair_left env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
        · rcases hRight with ⟨rfl, hCurrent, hFuture, hState⟩
          cases hCurrent
          cases hFuture
          cases hState
          cases hTarget with
          | fair_right _ _ _ targetResidual _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.fair_right env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment),
                TypeOffers.fair_right env bid left right
                  (TypeAlphabet.environment_wellFormed hEnvironment)⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature left).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hLeftStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · exact (compileType_fairChoice_left_child_edge_iff signature bid
              left right childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.fair_left bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_fairChoice_left_child_edge_cases signature bid
          left right hSignatureSymbol hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | fair_left _ _ _ _ _ hChildTarget =>
            exact (hLeftStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label
              { current := current, future := future } ∈
            (compileType signature right).alphabet := by
        simpa [compileType] using hSignatureSymbol
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hChildSymbol).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileType_fairChoice_right_child_edge_iff signature bid
              left right childState childTarget env label
              { current := current, future := future } hSignatureSymbol).mpr
            hChildEdge
        · exact TypeCompilationRelation.fair_right bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileType_fairChoice_right_child_edge_cases signature bid
          left right hSignatureSymbol hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | fair_right _ _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hChildSymbol).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-! ### Whole-fragment future correctness for binary choices -/

/-- At a fresh choice root, future resolution is exactly the union of the
two child-entry futures.  The theorem is stated for both ordinary and fair
selection labels; neither kind of selection crosses a clock boundary. -/
private theorem buildChoiceAutomaton_computeFuture_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      computeFuture { states := left.states, edges := left.edges }
          left.initial ∪
        computeFuture { states := right.states, edges := right.edges }
          right.initial := by
  classical
  let fragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hClosed : pending.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hRoot : (.root : TypeAutomatonState) ∈ pending.states := by
    simp [pending, fragment, buildChoiceAutomaton, finishAutomatonFragment]
  have hOffers : pending.offersAt .root = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [pending, fragment, buildChoiceAutomaton,
      finishAutomatonFragment, childPendingEdges, Finset.mem_union,
      Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hOffer
        simp [AutomatonConstructionLabel.semantic] at hOffer
      · rw [hEdge] at hOffer
        simp [AutomatonConstructionLabel.semantic] at hOffer
  have hReferences : pending.referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} := by
    ext state
    constructor
    · intro hState
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter] at hState
      rcases hState with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
      simp only [pending, fragment, buildChoiceAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
        Finset.mem_singleton] at hEdge
      rcases hEdge with (hLeft | hRight) | hSelection
      · rcases hLeft with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
      · rcases hRight with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
      · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
        · rw [hEdge] at hReference
          simp [AutomatonConstructionLabel.semantic, hSelectionLeft]
            at hReference
          simp [childState, hReference]
        · rw [hEdge] at hReference
          simp [AutomatonConstructionLabel.semantic, hSelectionRight]
            at hReference
          simp [childState, hReference]
    · intro hState
      simp only [Finset.mem_insert, Finset.mem_singleton] at hState
      rcases hState with rfl | rfl
      · let edge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.tock
            label := .visible selectionLeft
            current := ∅
            future := .at (.child 0 left.initial) ∅
            target := .child 0 left.initial }
        simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
          Finset.mem_filter]
        refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
        · simp only [pending, fragment, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton]
          right
          exact ⟨TypeEnvironment.tock,
            by simp [TypeAlphabet.localEnvironments], Or.inl rfl⟩
        · simp [edge, AutomatonConstructionLabel.semantic,
            hSelectionLeft]
      · let edge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.tock
            label := .visible selectionRight
            current := ∅
            future := .at (.child 1 right.initial) ∅
            target := .child 1 right.initial }
        simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
          Finset.mem_filter]
        refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
        · simp only [pending, fragment, buildChoiceAutomaton,
            finishAutomatonFragment, childPendingEdges, Finset.mem_union,
            Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
            Finset.mem_singleton]
          right
          exact ⟨TypeEnvironment.tock,
            by simp [TypeAlphabet.localEnvironments], Or.inr rfl⟩
        · simp [edge, AutomatonConstructionLabel.semantic,
            hSelectionRight]
  have hLeftClosed :
      ({ states := left.states, edges := left.edges } :
        PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left
      hLeftTargets
  have hRightClosed :
      ({ states := right.states, edges := right.edges } :
        PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  have hLeftCard : left.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 left ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      left.states.card = (childStates 0 left).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hRightCard : right.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 right ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  change computeFuture pending .root = _
  rw [computeFuture_unfold pending .root hClosed hRoot, hOffers, hReferences]
  simp only [Finset.empty_union, Finset.biUnion_insert,
    Finset.biUnion_singleton]
  have hLeftEmbedding := buildChoiceAutomaton_computeFuture_left signature
    left right selectionLeft selectionRight left.initial hLeftClosed
    hLeftInitial hLeftCard
  have hRightEmbedding := buildChoiceAutomaton_computeFuture_right signature
    left right selectionLeft selectionRight right.initial hRightClosed
    hRightInitial hRightCard
  refine congrArg₂ (fun first second => first ∪ second)
    hLeftEmbedding ?_
  simpa using hRightEmbedding

/-- State-carrier side of the compiler relation.  Future embeddings need this
independently of the semantic equality: saturation stability is stated for a
declared child state. -/
def CompilationStateCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      state ∈ (compileTypeFuel signature
        (typeCompilationFuel processType) processType).states

private theorem childState_mem_indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) (hState : state ∈ entry.2.states) :
    childState (index + 1) state ∈ indexedFragmentStates automata := by
  classical
  rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
  have hZipBound : index < automata.zipIdx.length := by
    simpa using hBound
  have hIndexed : (entry, index) ∈ automata.zipIdx := by
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := automata) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  rw [indexedFragmentStates, mem_foldl_union_iff]
  right
  refine ⟨(entry, index), hIndexed, ?_⟩
  simp [childStates, childState, hState]

/-- Every state named by `TypeCompilationRelation` belongs to the matching
sufficiently fuelled compiler fragment.  This carrier invariant is independent
of future semantics and is shared by every constructor embedding. -/
private theorem compileTypeFuel_relation_state_mem
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          state ∈ (compileTypeFuel signature fuel processType).states := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_final msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_final =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_final pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur_source name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          simpa [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_source left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_source bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | sequence_left left right childResidual childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ childResidual
            hChildRelated
          have hTagged : childState 0 childQ ∈
              childStates 0 (compileTypeFuel signature fuel left) := by
            exact Finset.mem_image.mpr ⟨childQ, hChild, rfl⟩
          rw [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment]
          change childState 0 childQ ∈
            (childStates 0 (compileTypeFuel signature fuel left) ∪
              (compileTypeFuel signature fuel left).edges.image
                (fun edge => childState 0 edge.target)) ∪
              childStates 1 (compileTypeFuel signature fuel right)
          simp only [Finset.mem_union]
          exact Or.inl (Or.inl hTagged)
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel leftState leftResidual hLeftRelated
          have hRight := ih right hRightFuel rightState rightResidual
            hRightRelated
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, hLeft, hRight]
      | xoffer_source elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          have hTagged : childState 0 childQ ∈
              childStates 0 (compileTypeFuel signature fuel elseType) := by
            exact Finset.mem_image.mpr ⟨childQ, hChild, rfl⟩
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState 0 childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel branch.2))
          simp only [Finset.mem_union]
          exact Or.inl (Or.inr hTagged)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchMem : (action, branchType) ∈ branches := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hBound, hValue⟩
            have hMember := List.getElem_mem hBound
            simpa [hValue] using hMember
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
            le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentStates branchAutomata
            index (action, compileTypeFuel signature fuel branchType)
            hAutomatonEntry childQ hChild
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState (index + 1) childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates branchAutomata
          simp only [Finset.mem_union]
          exact Or.inr hIndexed
      | offer_source elseType branches =>
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment]
      | offer_branches elseType _ branches childQ
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih (parallelTypeBranches branches) hConjunctionFuel
            childQ residual hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild

theorem compilationStateCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationStateCorrect signature processType := by
  exact compileTypeFuel_relation_state_mem signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- The future at a compiled binary-choice root is the union of the two
semantic child-entry menus. -/
private theorem compiledChoiceRootFuture_eq_union
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftCorrect : CompilationFutureCorrect signature left)
    (hRightCorrect : CompilationFutureCorrect signature right) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending .root =
      typeFutureOffers left ∪ typeFutureOffers right := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRoot := buildChoiceAutomaton_computeFuture_root signature leftFragment
    rightFragment selectionLeft selectionRight hSelectionLeft hSelectionRight
    (compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel)
    (compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel)
    hLeftInitial hRightInitial
  have hLeftRelation : TypeCompilationRelation left leftFragment.initial left :=
    compileTypeFuel_initial_relation signature fuel left hLeftFuel
  have hRightRelation :
      TypeCompilationRelation right rightFragment.initial right :=
    compileTypeFuel_initial_relation signature fuel right hRightFuel
  have hLeftSemantic : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      leftFragment.initial = typeFutureOffers left := by
    have hResult := hLeftCorrect leftFragment.initial left hLeftRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
    simpa [leftFragment, hStable] using hResult
  have hRightSemantic : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      rightFragment.initial = typeFutureOffers right := by
    have hResult := hRightCorrect rightFragment.initial right hRightRelation
    have hStable := compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
    simpa [rightFragment, hStable] using hResult
  exact hRoot.trans (congrArg₂ (fun first second => first ∪ second)
    hLeftSemantic hRightSemantic)

private theorem compiledChoiceLeftFuture_eq
    (signature : TypeAlphabet) (left right residual : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation left state residual)
    (hFuture : CompilationFutureCorrect signature left)
    (hStateCorrect : CompilationStateCorrect signature left) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 0 state) = typeFutureOffers residual := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hStable := compileTypeFuel_eq_of_sufficient signature left hFuel
    (typeCompilationFuel_sufficient left)
  have hState : state ∈ leftFragment.states := by
    have hExact := hStateCorrect state residual hRelated
    simpa [leftFragment, hStable] using hExact
  have hClosed :
      ({ states := leftFragment.states, edges := leftFragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    apply compileTypeFuel_referencesClosed
    exact hFuel
  have hCard : leftFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 leftFragment ⊆ fragment.states := by
      intro child hChild
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hChild]
    calc
      leftFragment.states.card = (childStates 0 leftFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hEmbedding := buildChoiceAutomaton_computeFuture_left signature
    leftFragment rightFragment selectionLeft selectionRight state hClosed
    hState hCard
  have hSemantic := hFuture state residual hRelated
  have hSemanticShared : computeFuture
      { states := leftFragment.states, edges := leftFragment.edges }
      state = typeFutureOffers residual := by
    simpa [leftFragment, hStable] using hSemantic
  change computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 state) = typeFutureOffers residual
  exact hEmbedding.trans hSemanticShared

private theorem compiledChoiceRightFuture_eq
    (signature : TypeAlphabet) (left right residual : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation right state residual)
    (hFuture : CompilationFutureCorrect signature right)
    (hStateCorrect : CompilationStateCorrect signature right) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildChoiceAutomaton signature leftFragment rightFragment
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 1 state) = typeFutureOffers residual := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hFuel
    (typeCompilationFuel_sufficient right)
  have hState : state ∈ rightFragment.states := by
    have hExact := hStateCorrect state residual hRelated
    simpa [rightFragment, hStable] using hExact
  have hClosed :
      ({ states := rightFragment.states, edges := rightFragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    apply compileTypeFuel_referencesClosed
    exact hFuel
  have hCard : rightFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 rightFragment ⊆ fragment.states := by
      intro child hChild
      simp [fragment, buildChoiceAutomaton, finishAutomatonFragment, hChild]
    calc
      rightFragment.states.card = (childStates 1 rightFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hEmbedding := buildChoiceAutomaton_computeFuture_right signature
    leftFragment rightFragment selectionLeft selectionRight state hClosed
    hState hCard
  have hSemantic := hFuture state residual hRelated
  have hSemanticShared : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      state = typeFutureOffers residual := by
    simpa [rightFragment, hStable] using hSemantic
  change computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 state) = typeFutureOffers residual
  exact hEmbedding.trans hSemanticShared

/-- Whole-fragment future correctness composes through ordinary choice.
The induction hypotheses are signature-polymorphic because the public
`typeFutureOffers` on the right is evaluated in its canonical analysis
alphabet, while the compiled graph on the left uses the caller's alphabet. -/
theorem compilationFutureCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftFuture : ∀ alphabet, CompilationFutureCorrect alphabet left)
    (hRightFuture : ∀ alphabet, CompilationFutureCorrect alphabet right) :
    CompilationFutureCorrect signature (.choice left right) := by
  intro state residual hRelated
  cases hRelated with
  | choice_source =>
      have hCaller := compiledChoiceRootFuture_eq_union signature left right
        TypeLabel.silent TypeLabel.silent (by simp [TypeLabel.silent])
        (by simp [TypeLabel.silent]) (hLeftFuture signature)
        (hRightFuture signature)
      let canonical := futureAnalysisAlphabet (.choice left right)
      have hCanonical := compiledChoiceRootFuture_eq_union canonical left right
        TypeLabel.silent TypeLabel.silent (by simp [TypeLabel.silent])
        (by simp [TypeLabel.silent]) (hLeftFuture canonical)
        (hRightFuture canonical)
      have hCallerRoot : computeFuture
          { states := (compileTypeFuel signature
              (typeCompilationFuel (.choice left right))
              (.choice left right)).states,
            edges := (compileTypeFuel signature
              (typeCompilationFuel (.choice left right))
              (.choice left right)).edges }
          .root = typeFutureOffers left ∪ typeFutureOffers right := by
        simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          using hCaller
      have hCanonicalRoot : typeFutureOffers (.choice left right) =
          typeFutureOffers left ∪ typeFutureOffers right := by
        unfold typeFutureOffers graphFutureOffers
        simpa only [canonical, typeCompilationFuel, Nat.one_add,
          compileTypeFuel] using hCanonical
      exact hCallerRoot.trans hCanonicalRoot.symm
  | choice_left _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        _ TypeLabel.silent TypeLabel.silent childState
        hChildRelated (hLeftFuture signature)
        (compilationStateCorrect_of_compilation signature left)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        using hChild
  | choice_right _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        _ TypeLabel.silent TypeLabel.silent childState
        hChildRelated (hRightFuture signature)
        (compilationStateCorrect_of_compilation signature right)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        using hChild

/-- Whole-fragment future correctness composes through fair choice by the
same tagged-sum calculation; only the two non-clock selection labels differ. -/
theorem compilationFutureCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftFuture : ∀ alphabet, CompilationFutureCorrect alphabet left)
    (hRightFuture : ∀ alphabet, CompilationFutureCorrect alphabet right) :
    CompilationFutureCorrect signature (.fairChoice bid left right) := by
  intro state residual hRelated
  cases hRelated with
  | fair_source =>
      have hCaller := compiledChoiceRootFuture_eq_union signature left right
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
        (hLeftFuture signature) (hRightFuture signature)
      let canonical := futureAnalysisAlphabet (.fairChoice bid left right)
      have hCanonical := compiledChoiceRootFuture_eq_union canonical left right
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair])
        (hLeftFuture canonical) (hRightFuture canonical)
      have hCallerRoot : computeFuture
          { states := (compileTypeFuel signature
              (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right)).states,
            edges := (compileTypeFuel signature
              (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right)).edges }
          .root = typeFutureOffers left ∪ typeFutureOffers right := by
        simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
          using hCaller
      have hCanonicalRoot : typeFutureOffers (.fairChoice bid left right) =
          typeFutureOffers left ∪ typeFutureOffers right := by
        unfold typeFutureOffers graphFutureOffers
        simpa only [canonical, typeCompilationFuel, Nat.one_add,
          compileTypeFuel] using hCanonical
      exact hCallerRoot.trans hCanonicalRoot.symm
  | fair_left _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceLeftFuture_eq signature left right
        _ (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated (hLeftFuture signature)
        (compilationStateCorrect_of_compilation signature left)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        using hChild
  | fair_right _ _ _ childResidual childState hChildRelated =>
      have hChild := compiledChoiceRightFuture_eq signature left right
        _ (TypeLabel.fair bid true) (TypeLabel.fair bid false)
        childState hChildRelated (hRightFuture signature)
        (compilationStateCorrect_of_compilation signature right)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        using hChild

/-! ### Sequence entry and literal-skip bridge -/

/-- The compiled entry of a sequence is the tagged entry of its left child. -/
theorem compileType_sequence_initial_eq
    (signature : TypeAlphabet) (left right : PactType) :
    (compileType signature (.seq left right)).initial =
      .child 0 (compileType signature left).initial := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hInitial : leftFragment.initial =
      (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
    exact congrArg AutomatonFragment.initial
      (compileTypeFuel_eq_of_sufficient signature left
        (by simpa [leftFragment] using hLeftFuel)
        (typeCompilationFuel_sufficient left))
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  simp only [compileType]
  rw [hFragment]
  simp [fragment, buildSequenceAutomaton, finishAutomatonFragment,
    childState, hInitial]

private theorem buildSequenceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 0 state ↔
      (∃ childEdge ∈ left.edges,
        childEdge.source = state ∧
        edge =
          { source := childState 0 childEdge.source
            environment := childEdge.environment
            label := childEdge.label
            current := childEdge.current
            future := .at (childState 0 childEdge.target) childEdge.current
            target := childState 0 childEdge.target }) ∨
      (state ∈ left.skipping ∧
        ∃ environment ∈ signature.localEnvironments,
          edge =
            { source := childState 0 state
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 1 right.initial) ∅
              target := childState 1 right.initial }) := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with (hLeft | hRight) | hBridge
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childState] using hChildSource
      left
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hBridge with ⟨bridgeState, hSkipping, environment,
        hEnvironment, hEdge⟩
      have hBridgeSource := hSource
      rw [← hEdge] at hBridgeSource
      have hState : bridgeState = state := by
        simpa [childState] using hBridgeSource
      subst bridgeState
      right
      exact ⟨hSkipping, environment, hEnvironment, hEdge.symm⟩
  · rintro (hLeft | hBridge)
    · rcases hLeft with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)
      · simp [childState, hChildSource]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      constructor
      · simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        right
        exact ⟨state, hSkipping, environment, hEnvironment, rfl⟩
      · rfl

private theorem buildSequenceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let sequence := buildSequenceAutomaton signature left right
    edge ∈ sequence.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion] at hEdge
    rcases hEdge with (hLeft | hRight) | hBridge
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      have hChildSource' : childEdge.source = state := by
        simpa [childPendingEdge, childState] using hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource', hEdge.symm⟩
    · rcases hBridge with ⟨bridgeState, _, environment, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSequenceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

/-- The part of a child graph that sequencing actually follows.  Sequencing
replaces every child decoration by a symbolic reference to the edge target,
so this graph records current offers along all non-clock transition paths and
deliberately forgets the child's original `FutureSpec`. -/
private def sequenceExecutionAutomaton
    (child : AutomatonFragment) : PendingAutomaton :=
  { states := child.states ∪ child.edges.image PendingAutomatonEdge.target
    edges := child.edges.image fun edge =>
      { source := edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := .at edge.target edge.current
        target := edge.target } }

private theorem sequenceExecutionAutomaton_referencesClosed
    (child : AutomatonFragment) :
    (sequenceExecutionAutomaton child).ReferencesClosed := by
  classical
  intro source hSource target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  by_cases hTock : childEdge.label.semantic = TypeLabel.tock
  · simp [hTock] at hFuture
  · simp only [hTock, if_false, Finset.mem_singleton] at hFuture
    subst target
    simp only [sequenceExecutionAutomaton, Finset.mem_union,
      Finset.mem_image]
    exact Or.inr ⟨childEdge, hChildEdge, rfl⟩

private theorem buildSequenceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.referencedStates (.child 0 state) =
      ((sequenceExecutionAutomaton left).referencedStates state).image
          (.child 0) ∪
        if state ∈ left.skipping then {.child 1 right.initial} else ∅ := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hFuture⟩
    rcases hEdge with hLeft | hBridge
    · rcases hLeft with
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      by_cases hTock : childEdge.label.semantic = TypeLabel.tock
      · simp [hTock] at hFuture
      · simp only [hTock, if_false, Finset.mem_singleton] at hFuture
        subst target
        left
        refine ⟨childEdge.target, ?_, rfl⟩
        refine ⟨
          { source := childEdge.source
            environment := childEdge.environment
            label := childEdge.label
            current := childEdge.current
            future := .at childEdge.target childEdge.current
            target := childEdge.target },
          ⟨?_, by simpa using hChildSource⟩, ?_⟩
        · exact ⟨childEdge, hChildEdge, rfl⟩
        · simp [hTock]
    · rcases hBridge with ⟨hSkipping, environment, hEnvironment, rfl⟩
      have hTarget : target = childState 1 right.initial := by
        simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
          using hFuture
      subst target
      right
      simp [childState, hSkipping]
  · intro hTarget
    rcases hTarget with hLeft | hBridge
    · rcases hLeft with ⟨childTarget, hChildTarget, rfl⟩
      rcases hChildTarget with ⟨edge, ⟨hEdge, hSource⟩, hFuture⟩
      rcases hEdge with ⟨childEdge, hChildEdge, hEdge⟩
      rw [← hEdge] at hSource hFuture
      have hChildSource : childEdge.source = state := by simpa using hSource
      have hChildTarget : childEdge.target = childTarget := by
        by_cases hTock : childEdge.label.semantic = TypeLabel.tock
        · simp [hTock] at hFuture
        · have hEquality : childTarget = childEdge.target := by
            simpa [hTock] using hFuture
          exact hEquality.symm
      subst childTarget
      refine ⟨_, Or.inl ⟨childEdge, hChildEdge, hChildSource, rfl⟩, ?_⟩
      by_cases hTock : childEdge.label.semantic = TypeLabel.tock
      · simp [hTock] at hFuture
      · simp [hTock, childState]
    · by_cases hSkipping : state ∈ left.skipping
      · simp only [hSkipping, if_true, Finset.mem_singleton] at hBridge
        subst target
        let environment := TypeEnvironment.tock
        refine ⟨_, Or.inr ⟨hSkipping, environment, ?_, rfl⟩, ?_⟩
        · simp [environment, TypeAlphabet.localEnvironments]
        · simp [childState, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
      · simp [hSkipping] at hBridge

private theorem buildSequenceAutomaton_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    parent.offersAt (.child 0 state) =
      (sequenceExecutionAutomaton left).offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_left signature left right]
  simp only [sequenceExecutionAutomaton, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hOffer⟩
    rcases hEdge with hLeft | hBridge
    · rcases hLeft with ⟨childEdge, hChildEdge, hSource, rfl⟩
      refine ⟨_, ⟨⟨childEdge, hChildEdge, rfl⟩, hSource⟩, ?_⟩
      simpa using hOffer
    · rcases hBridge with ⟨_, environment, _, rfl⟩
      simp at hOffer
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
    refine ⟨_, Or.inl ⟨childEdge, hChildEdge, hSource, rfl⟩, ?_⟩
    simpa using hOffer

private theorem buildSequenceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildSequenceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildSequenceAutomaton_outgoing_right signature left right]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

/-- Exact same-cycle reachability from a tagged left sequence state.  It is
the execution closure of the left child, plus the right closure exactly when
that left closure meets a skipping state.  This is the graph invariant that a
scalar child future equation alone cannot express. -/
private theorem buildSequenceAutomaton_futureReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := execution.futureReachable state
    let canBridge := ∃ completed ∈ leftReach, completed ∈ left.skipping
    parent.futureReachable (.child 0 state) =
      leftReach.image (.child 0) ∪
        if canBridge then
          (rightPending.futureReachable right.initial).image (.child 1)
        else ∅ := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let execution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := execution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach, completed ∈ left.skipping
  change parent.futureReachable (childState 0 state) =
    leftReach.image (childState 0) ∪
      if canBridge then rightReach.image (childState 1) else ∅
  have hExecutionClosed : execution.ReferencesClosed := by
    exact sequenceExecutionAutomaton_referencesClosed left
  have hRightClosed : rightPending.ReferencesClosed := by
    exact PendingAutomaton.referencesClosed_of_futureTargetsInStates right
      hRightTargets
  have hParentClosed : parent.ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates sequence
    exact buildSequenceAutomaton_futureTargetsInStates signature left right
      hLeftTargets hRightTargets hRightInitial
  have hExecutionState : state ∈ execution.states := by
    simp [execution, sequenceExecutionAutomaton, hLeftState]
  have hParentLeftState : childState 0 state ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hLeftState]
  have hParentRightState : childState 1 right.initial ∈ parent.states := by
    simp [parent, sequence, buildSequenceAutomaton, finishAutomatonFragment,
      childStates, childState, hRightInitial]
  have hLeftReferences : ∀ child,
      parent.referencedStates (childState 0 child) =
        (execution.referencedStates child).image (childState 0) ∪
          if child ∈ left.skipping then
            {childState 1 right.initial}
          else ∅ := by
    intro child
    exact buildSequenceAutomaton_referencedStates_left signature left right
      child
  have hRightReferences : ∀ child,
      parent.referencedStates (childState 1 child) =
        (rightPending.referencedStates child).image (childState 1) := by
    intro child
    exact buildSequenceAutomaton_referencedStates_right signature left right
      child
  have hExecutionFixed : execution.futureStep leftReach = leftReach := by
    apply PendingAutomaton.futureReachableAux_fixed_after_missing execution
      hExecutionClosed
    · simpa [leftReach, PendingAutomaton.futureReachable] using
        hExecutionState
    · omega
  have hRightFixed : rightPending.futureStep rightReach = rightReach := by
    apply PendingAutomaton.futureReachableAux_fixed_after_missing rightPending
      hRightClosed
    · simpa [rightReach, PendingAutomaton.futureReachable] using
        hRightInitial
    · omega
  have hStateReach : state ∈ leftReach := by
    change state ∈ execution.futureReachable state
    rw [execution.futureReachable_unfold state hExecutionClosed
      hExecutionState]
    simp
  have hLeftReachSubset : leftReach.image (childState 0) ⊆
      parent.futureReachable (childState 0 state) := by
    apply PendingAutomaton.futureReachable_image_subset_of_embedding
      execution parent (childState 0)
    · intro child
      rw [hLeftReferences child]
      exact Finset.subset_union_left
    · exact hParentClosed
    · exact hParentLeftState
  by_cases hCanBridge : canBridge
  · have hBridgeStart : childState 1 right.initial ∈
        parent.futureReachable (childState 0 state) := by
      rcases hCanBridge with ⟨completed, hCompletedReach, hSkipping⟩
      have hTaggedCompleted : childState 0 completed ∈
          parent.futureReachable (childState 0 state) :=
        hLeftReachSubset (Finset.mem_image.mpr
          ⟨completed, hCompletedReach, rfl⟩)
      have hBridgeReference : childState 1 right.initial ∈
          parent.referencedStates (childState 0 completed) := by
        rw [hLeftReferences completed]
        simp [hSkipping]
      have hParentFixed : parent.futureStep
          (parent.futureReachable (childState 0 state)) =
            parent.futureReachable (childState 0 state) := by
        apply PendingAutomaton.futureReachableAux_fixed_after_missing parent
          hParentClosed
        · simpa [PendingAutomaton.futureReachable] using hParentLeftState
        · omega
      rw [← hParentFixed]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨childState 0 completed, hTaggedCompleted, hBridgeReference⟩)
    have hRightFromEntry : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 1 right.initial) := by
      apply PendingAutomaton.futureReachable_image_subset_of_embedding
        rightPending parent (childState 1)
      · intro child
        rw [hRightReferences child]
      · exact hParentClosed
      · exact hParentRightState
    have hRightEntryToRoot :
        parent.futureReachable (childState 1 right.initial) ⊆
          parent.futureReachable (childState 0 state) :=
      PendingAutomaton.futureReachable_subset_of_mem parent
        (childState 0 state) (childState 1 right.initial) hParentClosed
        hParentLeftState hBridgeStart
    have hRightReachSubset : rightReach.image (childState 1) ⊆
        parent.futureReachable (childState 0 state) :=
      hRightFromEntry.trans hRightEntryToRoot
    simp only [hCanBridge, if_true]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state)
        (leftReach.image (childState 0) ∪
          rightReach.image (childState 1))
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩)
      · intro source hSource target hReference
        simp only [Finset.mem_union, Finset.mem_image] at hSource ⊢
        rcases hSource with ⟨child, hChildReach, rfl⟩ |
            ⟨child, hChildReach, rfl⟩
        · rw [hLeftReferences child] at hReference
          rcases Finset.mem_union.mp hReference with hChildReference |
            hBridgeReference
          · rcases Finset.mem_image.mp hChildReference with
              ⟨childTarget, hChildTarget, rfl⟩
            left
            refine ⟨childTarget, ?_, rfl⟩
            rw [← hExecutionFixed]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨child, hChildReach, hChildTarget⟩)
          · by_cases hSkipping : child ∈ left.skipping
            · simp [hSkipping] at hBridgeReference
              subst target
              right
              refine ⟨right.initial, ?_, rfl⟩
              rw [← hRightFixed]
              exact Finset.mem_union_left _ hRightInitial
            · simp [hSkipping] at hBridgeReference
        · rw [hRightReferences child] at hReference
          rcases Finset.mem_image.mp hReference with
            ⟨childTarget, hChildTarget, rfl⟩
          right
          refine ⟨childTarget, ?_, rfl⟩
          rw [← hRightFixed]
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨child, hChildReach, hChildTarget⟩)
    · intro target hTarget
      simp only [Finset.mem_union] at hTarget
      exact hTarget.elim hLeftReachSubset hRightReachSubset
  · simp only [hCanBridge, if_false, Finset.union_empty]
    apply Finset.Subset.antisymm
    · apply PendingAutomaton.futureReachable_subset_of_reference_closed
        parent (childState 0 state) (leftReach.image (childState 0))
      · exact Finset.mem_image.mpr ⟨state, hStateReach, rfl⟩
      · intro source hSource target hReference
        rcases Finset.mem_image.mp hSource with ⟨child, hChildReach, rfl⟩
        rw [hLeftReferences child] at hReference
        rcases Finset.mem_union.mp hReference with hChildReference |
          hBridgeReference
        · rcases Finset.mem_image.mp hChildReference with
            ⟨childTarget, hChildTarget, rfl⟩
          apply Finset.mem_image.mpr
          refine ⟨childTarget, ?_, rfl⟩
          rw [← hExecutionFixed]
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨child, hChildReach, hChildTarget⟩)
        · by_cases hSkipping : child ∈ left.skipping
          · exact (hCanBridge ⟨child, hChildReach, hSkipping⟩).elim
          · simp [hSkipping] at hBridgeReference
    · exact hLeftReachSubset

/-- Future offers at a tagged left sequence state are the current offers along
the child's non-clock execution closure, together with the right-entry future
exactly when that closure can cross a literal-skip bridge. -/
private theorem buildSequenceAutomaton_computeFuture_left_formula
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hLeftState : state ∈ left.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    let sequence := buildSequenceAutomaton signature left right
    let parent : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    let execution := sequenceExecutionAutomaton left
    let rightPending : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    let leftReach := execution.futureReachable state
    let canBridge := ∃ completed ∈ leftReach, completed ∈ left.skipping
    computeFuture parent (.child 0 state) =
      computeFuture execution state ∪
        if canBridge then computeFuture rightPending right.initial else ∅ := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let execution := sequenceExecutionAutomaton left
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let leftReach := execution.futureReachable state
  let rightReach := rightPending.futureReachable right.initial
  let canBridge := ∃ completed ∈ leftReach, completed ∈ left.skipping
  change computeFuture parent (childState 0 state) =
    computeFuture execution state ∪
      if canBridge then computeFuture rightPending right.initial else ∅
  have hReach := buildSequenceAutomaton_futureReachable_left signature left
    right state hLeftState hLeftTargets hRightTargets hRightInitial
  have hLeftOffers : ∀ child,
      parent.offersAt (childState 0 child) = execution.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_left signature left right child
  have hRightOffers : ∀ child,
      parent.offersAt (childState 1 child) = rightPending.offersAt child := by
    intro child
    exact buildSequenceAutomaton_offersAt_right signature left right child
  unfold computeFuture
  change (parent.futureReachable (childState 0 state)).biUnion
      parent.offersAt = _
  rw [hReach]
  by_cases hCanBridge : canBridge
  · simp only [hCanBridge, if_true, Finset.biUnion_union]
    rw [PendingAutomaton.biUnion_offersAt_image_of_embedding execution parent
        (childState 0) hLeftOffers leftReach,
      PendingAutomaton.biUnion_offersAt_image_of_embedding rightPending parent
        (childState 1) hRightOffers rightReach]
    rfl
  · simp only [hCanBridge, if_false, Finset.union_empty,
      Finset.biUnion_empty]
    exact PendingAutomaton.biUnion_offersAt_image_of_embedding execution
      parent (childState 0) hLeftOffers leftReach

private theorem buildSequenceAutomaton_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildSequenceAutomaton signature left right).states.card) :
    computeFuture
        { states := (buildSequenceAutomaton signature left right).states
          edges := (buildSequenceAutomaton signature left right).edges }
        (.child 1 state) =
      computeFuture { states := right.states, edges := right.edges } state := by
  let sequence := buildSequenceAutomaton signature left right
  let parent : PendingAutomaton :=
    { states := sequence.states, edges := sequence.edges }
  let child : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  apply computeFuture_eq_of_embedding child parent (.child 1)
  · exact buildSequenceAutomaton_referencedStates_right signature left right
  · exact buildSequenceAutomaton_offersAt_right signature left right
  · exact hClosed
  · exact hState
  · exact hCard

/-- A state in the tagged right component of a compiled sequence has exactly
the semantic future of the residual represented by that child state.  The
sequence bridge is one-way, so this is a genuine tagged-subgraph embedding. -/
private theorem compiledSequenceRightFuture_eq
    (signature : TypeAlphabet) (left right residual : PactType)
    (state : TypeAutomatonState)
    (hRelated : TypeCompilationRelation right state residual)
    (hFuture : CompilationFutureCorrect signature right)
    (hStateCorrect : CompilationStateCorrect signature right) :
    let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
    let leftFragment := compileTypeFuel signature fuel left
    let rightFragment := compileTypeFuel signature fuel right
    let fragment := buildSequenceAutomaton signature leftFragment rightFragment
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    computeFuture pending (.child 1 state) = typeFutureOffers residual := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hStable := compileTypeFuel_eq_of_sufficient signature right hFuel
    (typeCompilationFuel_sufficient right)
  have hState : state ∈ rightFragment.states := by
    have hExact := hStateCorrect state residual hRelated
    simpa [rightFragment, hStable] using hExact
  have hClosed :
      ({ states := rightFragment.states, edges := rightFragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    apply compileTypeFuel_referencesClosed
    exact hFuel
  have hCard : rightFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 rightFragment ⊆ fragment.states := by
      intro child hChild
      simp [fragment, buildSequenceAutomaton, finishAutomatonFragment, hChild]
    calc
      rightFragment.states.card = (childStates 1 rightFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
    leftFragment rightFragment state hClosed hState hCard
  have hSemantic := hFuture state residual hRelated
  have hSemanticShared : computeFuture
      { states := rightFragment.states, edges := rightFragment.edges }
      state = typeFutureOffers residual := by
    simpa [rightFragment, hStable] using hSemantic
  change computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 state) = typeFutureOffers residual
  exact hEmbedding.trans hSemanticShared

/-- The graph information about a child that sequential composition needs.
For every represented residual, re-running the child from that residual must
preserve both (1) current offers along non-clock transition targets and
(2) whether that execution closure reaches a skipping state.  These two
observables, rather than scalar `CompilationFutureCorrect`, determine the
future of an enclosing sequence. -/
def CompilationSequenceExecutionCorrect
    (sourceAlphabet targetAlphabet : TypeAlphabet)
    (processType : PactType) : Prop :=
  let sourceFragment := compileTypeFuel sourceAlphabet
    (typeCompilationFuel processType) processType
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      let targetFragment := compileTypeFuel targetAlphabet
        (typeCompilationFuel residual) residual
      let sourceExecution := sequenceExecutionAutomaton sourceFragment
      let targetExecution := sequenceExecutionAutomaton targetFragment
      computeFuture sourceExecution state =
          computeFuture targetExecution targetFragment.initial ∧
        ((∃ completed ∈ sourceExecution.futureReachable state,
              completed ∈ sourceFragment.skipping) ↔
          ∃ completed ∈
              targetExecution.futureReachable targetFragment.initial,
            completed ∈ targetFragment.skipping)

/-- Sequence future correctness reduces exactly to execution-graph transport
for the left child and ordinary future correctness for the right child.  The
transport hypothesis is alphabet-polymorphic because the residual menu uses
its canonical graph-analysis alphabet. -/
theorem compilationFutureCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftExecution : ∀ sourceAlphabet targetAlphabet,
      CompilationSequenceExecutionCorrect sourceAlphabet targetAlphabet left)
    (hRightFuture : ∀ alphabet,
      CompilationFutureCorrect alphabet right) :
    CompilationFutureCorrect signature (.seq left right) := by
  intro state residual hRelated
  cases hRelated with
  | sequence_right _ _ childResidual childQ hChildRelated =>
      have hChild := compiledSequenceRightFuture_eq signature left right
        childResidual childQ hChildRelated (hRightFuture signature)
        (compilationStateCorrect_of_compilation signature right)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
        using hChild
  | sequence_left _ _ childResidual childQ hChildRelated =>
      let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
      let leftFragment := compileTypeFuel signature fuel left
      let rightFragment := compileTypeFuel signature fuel right
      let fragment := buildSequenceAutomaton signature leftFragment rightFragment
      let pending : PendingAutomaton :=
        { states := fragment.states, edges := fragment.edges }
      let leftExecution := sequenceExecutionAutomaton leftFragment
      let rightPending : PendingAutomaton :=
        { states := rightFragment.states, edges := rightFragment.edges }
      let leftReach := leftExecution.futureReachable childQ
      let callerCanBridge := ∃ completed ∈ leftReach,
        completed ∈ leftFragment.skipping
      have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hRightFuel : TypeCompilationFuelSufficient right fuel := by
        simp [TypeCompilationFuelSufficient, fuel]
      have hLeftStable := compileTypeFuel_eq_of_sufficient signature left
        hLeftFuel (typeCompilationFuel_sufficient left)
      have hRightStable := compileTypeFuel_eq_of_sufficient signature right
        hRightFuel (typeCompilationFuel_sufficient right)
      have hLeftState : childQ ∈ leftFragment.states := by
        have hExact := compilationStateCorrect_of_compilation signature left
          childQ childResidual hChildRelated
        simpa [leftFragment, hLeftStable] using hExact
      have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
        compileTypeFuel_initial_mem signature fuel right hRightFuel
      have hCallerFormula :=
        buildSequenceAutomaton_computeFuture_left_formula signature
          leftFragment rightFragment childQ hLeftState
          (compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel)
          (compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel)
          hRightInitial
      have hCallerRight : computeFuture rightPending rightFragment.initial =
          typeFutureOffers right := by
        have hRelation := compileTypeFuel_initial_relation signature fuel right
          hRightFuel
        have hSemantic := hRightFuture signature rightFragment.initial right
          hRelation
        simpa [rightPending, rightFragment, hRightStable] using hSemantic
      let canonical := futureAnalysisAlphabet (.seq childResidual right)
      let canonicalFuel := max (typeCompilationFuel childResidual)
        (typeCompilationFuel right)
      let canonicalLeft := compileTypeFuel canonical canonicalFuel childResidual
      let canonicalRight := compileTypeFuel canonical canonicalFuel right
      let canonicalFragment := buildSequenceAutomaton canonical canonicalLeft
        canonicalRight
      let canonicalPending : PendingAutomaton :=
        { states := canonicalFragment.states, edges := canonicalFragment.edges }
      let canonicalExecution := sequenceExecutionAutomaton canonicalLeft
      let canonicalRightPending : PendingAutomaton :=
        { states := canonicalRight.states, edges := canonicalRight.edges }
      let canonicalReach := canonicalExecution.futureReachable
        canonicalLeft.initial
      let canonicalCanBridge := ∃ completed ∈ canonicalReach,
        completed ∈ canonicalLeft.skipping
      have hCanonicalLeftFuel : TypeCompilationFuelSufficient childResidual
          canonicalFuel := by
        simp [TypeCompilationFuelSufficient, canonicalFuel]
      have hCanonicalRightFuel : TypeCompilationFuelSufficient right
          canonicalFuel := by
        simp [TypeCompilationFuelSufficient, canonicalFuel]
      have hCanonicalLeftStable := compileTypeFuel_eq_of_sufficient canonical
        childResidual hCanonicalLeftFuel
        (typeCompilationFuel_sufficient childResidual)
      have hCanonicalRightStable := compileTypeFuel_eq_of_sufficient canonical
        right hCanonicalRightFuel (typeCompilationFuel_sufficient right)
      have hCanonicalLeftInitial : canonicalLeft.initial ∈
          canonicalLeft.states :=
        compileTypeFuel_initial_mem canonical canonicalFuel childResidual
          hCanonicalLeftFuel
      have hCanonicalRightInitial : canonicalRight.initial ∈
          canonicalRight.states :=
        compileTypeFuel_initial_mem canonical canonicalFuel right
          hCanonicalRightFuel
      have hCanonicalFormula :=
        buildSequenceAutomaton_computeFuture_left_formula canonical
          canonicalLeft canonicalRight canonicalLeft.initial
          hCanonicalLeftInitial
          (compileTypeFuel_futureTargetsInStates canonical canonicalFuel
            childResidual hCanonicalLeftFuel)
          (compileTypeFuel_futureTargetsInStates canonical canonicalFuel right
            hCanonicalRightFuel)
          hCanonicalRightInitial
      have hCanonicalRight : computeFuture canonicalRightPending
          canonicalRight.initial = typeFutureOffers right := by
        have hRelation := compileTypeFuel_initial_relation canonical
          canonicalFuel right hCanonicalRightFuel
        have hSemantic := hRightFuture canonical canonicalRight.initial right
          hRelation
        simpa [canonicalRightPending, canonicalRight,
          hCanonicalRightStable] using hSemantic
      have hTransportExact := hLeftExecution signature canonical childQ
        childResidual hChildRelated
      have hExecutionEq : computeFuture leftExecution childQ =
          computeFuture canonicalExecution canonicalLeft.initial := by
        simpa [leftExecution, leftFragment, canonicalExecution, canonicalLeft,
          hLeftStable, hCanonicalLeftStable] using hTransportExact.1
      have hCanBridgeIff : callerCanBridge ↔ canonicalCanBridge := by
        simpa [callerCanBridge, leftReach, leftExecution, leftFragment,
          canonicalCanBridge, canonicalReach, canonicalExecution,
          canonicalLeft, hLeftStable, hCanonicalLeftStable] using
            hTransportExact.2
      have hCaller : computeFuture pending (childState 0 childQ) =
          computeFuture leftExecution childQ ∪
            if callerCanBridge then
              computeFuture rightPending rightFragment.initial
            else ∅ := by
        simpa [pending, fragment, leftExecution, rightPending, leftReach,
          callerCanBridge] using hCallerFormula
      have hCanonical : typeFutureOffers (.seq childResidual right) =
          computeFuture canonicalExecution canonicalLeft.initial ∪
            if canonicalCanBridge then
              computeFuture canonicalRightPending canonicalRight.initial
            else ∅ := by
        unfold typeFutureOffers graphFutureOffers
        have hFormula : computeFuture canonicalPending
              (childState 0 canonicalLeft.initial) =
            computeFuture canonicalExecution canonicalLeft.initial ∪
              if canonicalCanBridge then
                computeFuture canonicalRightPending canonicalRight.initial
              else ∅ := by
          simpa [canonicalPending, canonicalFragment, canonicalExecution,
            canonicalRightPending, canonicalReach, canonicalCanBridge]
            using hCanonicalFormula
        simpa only [canonical, typeCompilationFuel, Nat.one_add,
          compileTypeFuel] using hFormula
      have hMenus : computeFuture leftExecution childQ ∪
            (if callerCanBridge then
              computeFuture rightPending rightFragment.initial else ∅) =
          computeFuture canonicalExecution canonicalLeft.initial ∪
            (if canonicalCanBridge then
              computeFuture canonicalRightPending canonicalRight.initial
            else ∅) := by
        rw [hExecutionEq]
        by_cases hCallerCan : callerCanBridge
        · have hCanonicalCan := hCanBridgeIff.mp hCallerCan
          simp [hCallerCan, hCanonicalCan, hCallerRight, hCanonicalRight]
        · have hCanonicalCannot : ¬ canonicalCanBridge := by
            exact fun h => hCallerCan (hCanBridgeIff.mpr h)
          simp [hCallerCan, hCanonicalCannot]
      have hResult := hCaller.trans (hMenus.trans hCanonical.symm)
      simpa only [pending, fragment, typeCompilationFuel, Nat.one_add,
        compileTypeFuel] using hResult

private theorem buildSequenceAutomaton_hasResolvedEdge_right_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hTargets : right.FutureTargetsInStates) :
    AutomatonFragment.HasResolvedEdge
        (buildSequenceAutomaton signature left right)
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge right source env label offers target := by
  classical
  let sequence := buildSequenceAutomaton signature left right
  have hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hTargets
  have hCard : right.states.card ≤ sequence.states.card := by
    have hSubset : childStates 1 right ⊆ sequence.states := by
      intro state hState
      simp [sequence, buildSequenceAutomaton, finishAutomatonFragment, hState]
    calc
      right.states.card = (childStates 1 right).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEqual
        injection hEqual
      _ ≤ sequence.states.card := Finset.card_le_card hSubset
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    simp only [childPendingEdge] at hEnvironment hLabel hCurrent hTarget
    have hChildTarget : childEdge.target = target := by
      simpa [childState] using hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, ?_, hChildTarget⟩
    cases hSpec : childEdge.future with
    | explicit future =>
        simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
    | «at» referenced removed =>
        have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
        have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
          left right referenced hClosed hReferenced hCard
        simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          at hFuture
        rw [hEmbedding] at hFuture
        exact hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_right signature left right source
        (childPendingEdge 1 childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge 1 childEdge, hOutgoing.1, hOutgoing.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed hSpec
          have hEmbedding := buildSequenceAutomaton_computeFuture_right signature
            left right referenced hClosed hReferenced hCard
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          rw [hEmbedding]
          simp only [hSpec] at hFuture
          exact hFuture
    · simp [childPendingEdge, childState, hChildTarget]

/-- A left-child edge is re-decorated from the future menu at its tagged
target.  Its original resolved future remains existentially available for the
child fragment correspondence, while its current offers are preserved. -/
private theorem buildSequenceAutomaton_hasResolvedEdge_left_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 0 target) ↔
      ∃ childFuture,
        left.HasResolvedEdge source env label
            { current := offers.current, future := childFuture } target ∧
          computeFuture pending (.child 0 target) \ offers.current =
            offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge
    · rcases hChild with ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      have hChildTarget : childEdge.target = target := by
        simpa [childState] using hTarget
      let childFuture : Finset BareMessage :=
        match childEdge.future with
        | .explicit future => future
        | .at state removed =>
            computeFuture { states := left.states, edges := left.edges }
              state \ removed
      refine ⟨childFuture, ?_, ?_⟩
      · refine ⟨childEdge, hChildEdge, hChildSource, hEnvironment,
          hLabel, hCurrent, ?_, hChildTarget⟩
        rfl
      · rw [hCurrent] at hFuture
        simpa [childState, hChildTarget] using hFuture
    · rcases hBridge with ⟨_, _, _, _, rfl⟩
      simp [childState] at hTarget
  · rintro ⟨childFuture,
      ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
        hCurrent, _, hChildTarget⟩, hFuture⟩
    let lifted : PendingAutomatonEdge :=
      { source := childState 0 childEdge.source
        environment := childEdge.environment
        label := childEdge.label
        current := childEdge.current
        future := .at (childState 0 childEdge.target) childEdge.current
        target := childState 0 childEdge.target }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        lifted).mpr (Or.inl
          ⟨childEdge, hChildEdge, hChildSource, rfl⟩)
    refine ⟨lifted, hOutgoing.1, hOutgoing.2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lifted] using hEnvironment
    · simpa [lifted] using hLabel
    · simpa [lifted] using hCurrent
    · simpa [lifted, childState, hChildTarget, hCurrent] using hFuture
    · simp [lifted, childState, hChildTarget]

/-- Exact classification of an administrative sequence bridge. -/
private theorem buildSequenceAutomaton_hasResolvedEdge_bridge_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    let sequence := buildSequenceAutomaton signature left right
    let pending : PendingAutomaton :=
      { states := sequence.states, edges := sequence.edges }
    sequence.HasResolvedEdge (.child 0 source) env label offers
        (.child 1 right.initial) ↔
      source ∈ left.skipping ∧ env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 1 right.initial) = offers.future := by
  classical
  dsimp only
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right
        source edge).mp ⟨hEdge, hSource⟩
    rcases hOutgoing with hChild | hBridge
    · rcases hChild with ⟨childEdge, _, _, rfl⟩
      simp [childState] at hTarget
    · rcases hBridge with ⟨hSkipping, bridgeEnvironment,
        hBridgeEnvironment, rfl⟩
      simp only at hEnvironment hLabel hCurrent hFuture hTarget
      have hEnvironmentEq : bridgeEnvironment = env := hEnvironment
      subst bridgeEnvironment
      refine ⟨hSkipping, hBridgeEnvironment, ?_, ?_, ?_⟩
      · simpa using hLabel.symm
      · simpa using hCurrent.symm
      · simpa using hFuture
  · rintro ⟨hSkipping, hEnvironment, rfl, hCurrent, hFuture⟩
    let bridge : PendingAutomatonEdge :=
      { source := childState 0 source
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial }
    have hOutgoing :=
      (buildSequenceAutomaton_outgoing_left signature left right source
        bridge).mpr (Or.inr ⟨hSkipping, env, hEnvironment, rfl⟩)
    refine ⟨bridge, hOutgoing.1, hOutgoing.2, rfl, rfl, ?_, ?_, rfl⟩
    · simpa [bridge] using hCurrent.symm
    · simpa [bridge] using hFuture

/-- Canonical raw-fragment form of a lifted left sequence edge.  The parent
recomputes the future at the represented target, while preserving the child's
current offer set. -/
theorem compileTypeFuel_sequence_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers (.child 0 target) ↔
      ∃ childFuture,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture } target ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 0 target) \ offers.current = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment source target env label offers
  simpa only [fragment, hLeftStable, hFragment] using hCore

/-- Canonical raw-fragment form of an embedded right sequence edge. -/
theorem compileTypeFuel_sequence_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers target := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment source target env label offers hRightTargets
  simpa only [fragment, hRightStable] using hCore

/-- Canonical raw-fragment classification of the administrative bridge from a
skipping left state to the right entry. -/
theorem compileTypeFuel_sequence_bridge_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
        (.child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) ↔
      source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment, ← hRightStable]
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_bridge_iff signature leftFragment
      rightFragment source env label offers
  simpa only [fragment, hFragment, hLeftStable, hRightStable] using hCore

/-- Exact target-shape classification for every raw edge leaving a tagged left
sequence state. -/
theorem compileTypeFuel_sequence_left_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 0 source) env label offers target) :
    (∃ childTarget childFuture,
        target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture }
              childTarget ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 0 childTarget) \ offers.current = offers.future) ∨
      (source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future ∧
        target = .child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment,
    hLabel, hCurrent, hResolvedFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_left signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with hChild | hBridge
  · rcases hChild with ⟨childEdge, _, _, hPending⟩
    have hTargetEq : target = .child 0 childEdge.target := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers (.child 0 childEdge.target) := by
      rw [hFragment]
      simpa [hTargetEq] using (show fragment.HasResolvedEdge
        (.child 0 source) env label offers target from
          ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
            hCurrent, hResolvedFuture, hTarget⟩)
    rcases (compileTypeFuel_sequence_left_child_edge_iff signature left right
      source childEdge.target env label offers).mp hFixed with
      ⟨childFuture, hChildResolved, hFuture⟩
    left
    exact ⟨childEdge.target, childFuture, hTargetEq, hChildResolved, hFuture⟩
  · rcases hBridge with ⟨_, _, _, hPending⟩
    have hTargetEq : target = .child 1 rightFragment.initial := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right))
        (.child 0 source) env label offers
          (.child 1 (compileTypeFuel signature
            (typeCompilationFuel right) right).initial) := by
      rw [hFragment]
      simpa [hTargetEq, hRightStable] using (show fragment.HasResolvedEdge
        (.child 0 source) env label offers target from
          ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
            hCurrent, hResolvedFuture, hTarget⟩)
    have hFields :=
      (compileTypeFuel_sequence_bridge_edge_iff signature left right source env
        label offers).mp hFixed
    right
    exact ⟨hFields.1, hFields.2.1, hFields.2.2.1,
      hFields.2.2.2.1, hFields.2.2.2.2,
      by simpa [hRightStable] using hTargetEq⟩

/-- Exact target-shape classification for every raw edge leaving a tagged right
sequence state. -/
theorem compileTypeFuel_sequence_right_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel (.seq left right))
        (.seq left right))
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  rcases hEdge with ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_right signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileTypeFuel_sequence_right_child_edge_iff signature left right
    source childEdge.target env label offers).mp
  rw [hFragment]
  simpa [hTargetEq] using (show fragment.HasResolvedEdge
    (.child 1 source) env label offers target from
      ⟨pendingEdge, hPendingEdge, hSource, hEnvironment, hLabel, hCurrent,
        hFuture, hTarget⟩)

/-- Public left-child edges are exactly child-fragment edges whose future is
recomputed from the represented sequence target. -/
theorem compileType_sequence_left_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.seq left right)).HasEdge
        (.child 0 source) env label offers (.child 0 target) ↔
      ∃ childFuture,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture } target ∧
          computeFuture
              { states :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).states
                edges :=
                  (compileTypeFuel signature
                    (typeCompilationFuel (.seq left right))
                    (.seq left right)).edges }
              (.child 0 target) \ offers.current = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
    (.child 0 source) (.child 0 target) env label offers hSymbol]
  rw [hFragment]
  change fragment.HasResolvedEdge (.child 0 source) env label offers
      (.child 0 target) ↔ _
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment source target env label offers
  simpa only [fragment, hLeftStable, hFragment] using hCore

/-- Right-child edges are embedded without changing any decoration. -/
theorem compileType_sequence_right_fragment_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.seq left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers target := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
    (.child 1 source) (.child 1 target) env label offers hSymbol]
  rw [hFragment]
  change fragment.HasResolvedEdge (.child 1 source) env label offers
      (.child 1 target) ↔ _
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment source target env label offers hRightTargets
  simpa only [fragment, hRightStable] using hCore

/-- Exported right-child edges therefore agree exactly with the standalone
right automaton whenever the common symbol survives the boundary filter. -/
theorem compileType_sequence_right_child_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.seq left right)).HasEdge
        (.child 1 source) env label offers (.child 1 target) ↔
      (compileType signature right).HasEdge source env label offers target := by
  rw [compileType_sequence_right_fragment_edge_iff signature left right
    source target env label offers hSymbol]
  symm
  exact compileType_hasEdge_iff_hasResolvedEdge signature right source target
    env label offers hSymbol

/-- Public bridge membership, including its exact graph-resolved future. -/
theorem compileType_sequence_bridge_edge_iff
    (signature : TypeAlphabet) (left right : PactType)
    (source : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature (.seq left right)).HasEdge
        (.child 0 source) env label offers
        (.child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) ↔
      source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
    (.child 0 source)
    (.child 1 (compileTypeFuel signature
      (typeCompilationFuel right) right).initial)
    env label offers hSymbol]
  rw [hFragment]
  rw [← hRightStable]
  change fragment.HasResolvedEdge (.child 0 source) env label offers
      (.child 1 rightFragment.initial) ↔ _
  have hCore :=
    buildSequenceAutomaton_hasResolvedEdge_bridge_iff signature leftFragment
      rightFragment source env label offers
  simpa only [fragment, hFragment, hLeftStable, hRightStable] using hCore

/-- Every edge leaving a tagged left state is either a re-decorated left-child
edge or the unique administrative bridge into the right entry. -/
theorem compileType_sequence_left_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.seq left right)).HasEdge
      (.child 0 source) env label offers target) :
    (∃ childTarget childFuture,
        target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            source env label
              { current := offers.current, future := childFuture }
              childTarget ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 0 childTarget) \ offers.current = offers.future) ∨
      (source ∈ (compileTypeFuel signature
          (typeCompilationFuel left) left).skipping ∧
        env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture
            { states :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).states
              edges :=
                (compileTypeFuel signature
                  (typeCompilationFuel (.seq left right))
                  (.seq left right)).edges }
            (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) = offers.future ∧
        target = .child 1 (compileTypeFuel signature
          (typeCompilationFuel right) right).initial) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
      (.child 0 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_left signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with hChild | hBridge
  · rcases hChild with ⟨childEdge, _, _, hPending⟩
    have hTargetEq : target = .child 0 childEdge.target := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : (compileType signature (.seq left right)).HasEdge
        (.child 0 source) env label offers (.child 0 childEdge.target) := by
      simpa [hTargetEq] using hEdge
    rcases (compileType_sequence_left_child_edge_iff signature left right
      source childEdge.target env label offers hSymbol).mp hFixed with
      ⟨childFuture, hChildResolved, hFuture⟩
    left
    exact ⟨childEdge.target, childFuture, hTargetEq, hChildResolved, hFuture⟩
  · rcases hBridge with ⟨_, _, _, hPending⟩
    have hTargetEq : target = .child 1 rightFragment.initial := by
      rw [hPending] at hTarget
      simpa [childState] using hTarget.symm
    have hFixed : (compileType signature (.seq left right)).HasEdge
        (.child 0 source) env label offers
          (.child 1 (compileTypeFuel signature
            (typeCompilationFuel right) right).initial) := by
      simpa [hTargetEq, hRightStable] using hEdge
    have hBridgeFields :=
      (compileType_sequence_bridge_edge_iff signature left right source env
        label offers hSymbol).mp hFixed
    right
    exact ⟨hBridgeFields.1, hBridgeFields.2.1, hBridgeFields.2.2.1,
      hBridgeFields.2.2.2.1, hBridgeFields.2.2.2.2,
      by simpa [hRightStable] using hTargetEq⟩

/-- Every edge leaving a tagged right state remains inside the right child. -/
theorem compileType_sequence_right_edge_cases
    (signature : TypeAlphabet) (left right : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hEdge : (compileType signature (.seq left right)).HasEdge
      (.child 1 source) env label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel right) right)
        source env label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature leftFragment rightFragment
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq left right))
          (.seq left right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved :=
    (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
      (.child 1 source) target env label offers hSymbol).mp hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPendingEdge, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildSequenceAutomaton_outgoing_right signature leftFragment rightFragment
      source pendingEdge).mp ⟨hPendingEdge, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPending⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPending] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEq, ?_⟩
  apply (compileType_sequence_right_fragment_edge_iff signature left right
    source childEdge.target env label offers hSymbol).mp
  simpa [hTargetEq] using hEdge

/-- The graph-future equality used to decorate the administrative bridge of
`skip ; right`. -/
def SequenceSkipBridgeFutureCorrect
    (signature : TypeAlphabet) (right : PactType) : Prop :=
  let fuel := max (typeCompilationFuel .skip) (typeCompilationFuel right)
  let skipFragment := compileTypeFuel signature fuel .skip
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature skipFragment rightFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 1 rightFragment.initial) =
    typeFutureOffers right

/-- The administrative bridge from the completed literal `skip` child to the
right entry is present with its exact offer decoration. -/
theorem compileType_sequence_skip_bridge_edge
    (signature : TypeAlphabet) (right : PactType) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : SequenceSkipBridgeFutureCorrect signature right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    (compileType signature (.seq .skip right)).HasEdge
      (.child 0 (compileType signature .skip).initial) env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right))
      (.child 1 (compileType signature right).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let fuel := max (typeCompilationFuel .skip) (typeCompilationFuel right)
  let skipFragment := compileTypeFuel signature fuel .skip
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildSequenceAutomaton signature skipFragment rightFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hSkipFuel : TypeCompilationFuelSufficient .skip fuel := by
    simp [TypeCompilationFuelSufficient, typeCompilationFuel, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hSkipFragment : skipFragment =
      compileTypeFuel signature (typeCompilationFuel .skip) .skip :=
    compileTypeFuel_eq_of_sufficient signature .skip hSkipFuel
      (typeCompilationFuel_sufficient .skip)
  have hRightFragment : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hSkipping : skipFragment.initial ∈ skipFragment.skipping := by
    rw [hSkipFragment]
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 1 rightFragment.initial) = typeFutureOffers right := by
    simpa [pending] using hFuture
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.seq .skip right))
          (.seq .skip right) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    simp [fragment, skipFragment, rightFragment, fuel, typeCompilationFuel]
  refine ⟨
    { source := .child 0 skipFragment.initial
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers right
      target := .child 1 rightFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .child 0 skipFragment.initial
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 1 rightFragment.initial) ∅
        target := .child 1 rightFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      change _ ∈ fragment.edges
      simp only [fragment, buildSequenceAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image]
      right
      exact ⟨skipFragment.initial, hSkipping, env, hLocalEnvironment, rfl⟩
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, hSkipFragment, hRightFragment]

private theorem TypeOffers.skip_sequence_fields
    {env : TypeEnvironment} {right : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq .skip right) TypeLabel.silent right
      current future) :
    current = ∅ ∧ future = typeFutureOffers right := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.sequence_fields
    {env : TypeEnvironment} {left left' right : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq left right) label (.seq left' right)
      current future) :
    ∃ childFuture,
      TypeOffers env left label left' current childFuture ∧
        future = typeFutureOffers (.seq left' right) \ current := by
  generalize hLabel : label = actualLabel at hOffers
  cases hOffers with
  | seq _ _ _ _ _ _ childFuture hChild =>
      subst actualLabel
      exact ⟨childFuture, hChild, rfl⟩
  | _ => simp_all

/-- Sequence preserves raw constructor-fragment step correspondence.  The
proof uses child fragment correspondence (not exported edges), exact parent
future correctness for re-decoration, and exact left skipping correctness for
the administrative bridge. -/
theorem compilationFragmentStepCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hSequenceFuture : CompilationFutureCorrect signature (.seq left right))
    (hLeftSkipping : CompilationSkippingCorrect signature left) :
    CompilationFragmentStepCorrect signature (.seq left right) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated with
  | sequence_left _ _ childResidual childState hChildRelated =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip_seq =>
            obtain ⟨hCurrent, hOfferFuture⟩ :=
              TypeOffers.skip_sequence_fields hOffers
            have hSkipping : childState ∈
                (compileTypeFuel signature (typeCompilationFuel left) left).skipping :=
              (hLeftSkipping childState .skip hChildRelated).mpr rfl
            have hRightInitial : TypeCompilationRelation right
                (compileTypeFuel signature (typeCompilationFuel right) right).initial
                right := by
              simpa [compileType] using
                (compileType_initial_relation signature right)
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 1 (compileTypeFuel signature
                  (typeCompilationFuel right) right).initial) right :=
              TypeCompilationRelation.sequence_right left right right _
                hRightInitial
            have hComputed := hSequenceFuture _ _ hTarget
            refine ⟨.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial, ?_, hTarget⟩
            apply (compileTypeFuel_sequence_bridge_edge_iff signature left right
              childState env TypeLabel.silent offers).mpr
            exact ⟨hSkipping, hLocalEnvironment, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm⟩
        | seq _ _ childTarget _ _ hChildTransition =>
            obtain ⟨childFuture, hChildOffers, hOfferFuture⟩ :=
              TypeOffers.sequence_fields hOffers
            rcases (hLeftStep (residual' := childTarget) (label := label)
                (offers := { current := offers.current, future := childFuture })
                hChildRelated hLocalEnvironment).mp
                ⟨hChildTransition, hChildOffers⟩ with
              ⟨childState', hChildEdge, hChildTarget⟩
            have hTarget : TypeCompilationRelation (.seq left right)
                (.child 0 childState') (.seq childTarget right) :=
              TypeCompilationRelation.sequence_left left right childTarget _
                hChildTarget
            have hComputed := hSequenceFuture _ _ hTarget
            refine ⟨.child 0 childState', ?_, hTarget⟩
            apply (compileTypeFuel_sequence_left_child_edge_iff signature left
              right childState childState' env label offers).mpr
            refine ⟨childFuture, hChildEdge, ?_⟩
            rw [hComputed]
            exact hOfferFuture.symm
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
        · rcases hChild with
            ⟨childTarget, childFuture, rfl, hChildEdge, hComputed⟩
          cases hTarget with
          | sequence_left _ _ targetResidual _ hChildTarget =>
              rcases (hLeftStep hChildRelated hLocalEnvironment).mpr
                  ⟨childTarget, hChildEdge, hChildTarget⟩ with
                ⟨hChildTransition, hChildOffers⟩
              refine ⟨TypeTransition.seq env childResidual targetResidual right
                  label hChildTransition, ?_⟩
              have hParentTarget : TypeCompilationRelation (.seq left right)
                  (.child 0 childTarget) (.seq targetResidual right) :=
                TypeCompilationRelation.sequence_left left right targetResidual _
                  hChildTarget
              have hTargetFuture := hSequenceFuture _ _ hParentTarget
              have hSemanticFuture :
                  typeFutureOffers (.seq targetResidual right) \
                      offers.current = offers.future :=
                (congrArg (fun available => available \ offers.current)
                  hTargetFuture).symm.trans hComputed
              simpa only [hSemanticFuture] using
                (TypeOffers.seq env childResidual targetResidual right label
                  offers.current childFuture hChildOffers)
        · rcases hBridge with
            ⟨hSkipping, _, hLabel, hCurrent, hComputed, rfl⟩
          cases hTarget with
          | sequence_right _ _ targetResidual _ hChildTarget =>
              have hRightInitial : TypeCompilationRelation right
                  (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial right := by
                simpa [compileType] using
                  (compileType_initial_relation signature right)
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget hRightInitial
              cases hResidual
              have hChildResidual : childResidual = .skip :=
                (hLeftSkipping childState childResidual hChildRelated).mp
                  hSkipping
              subst childResidual
              have hParentTarget : TypeCompilationRelation (.seq left right)
                  (.child 1 (compileTypeFuel signature
                    (typeCompilationFuel right) right).initial) right :=
                TypeCompilationRelation.sequence_right left right right _
                  hChildTarget
              have hTargetFuture := hSequenceFuture _ _ hParentTarget
              have hOfferFuture : offers.future = typeFutureOffers right :=
                hComputed.symm.trans hTargetFuture
              subst label
              refine ⟨TypeTransition.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment),
                ?_⟩
              simpa only [hCurrent, hOfferFuture] using
                (TypeOffers.skip_seq env right
                  (TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment))
  | sequence_right _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hRightStep hChildRelated hLocalEnvironment).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_sequence_right_child_edge_iff signature left
              right childState childTarget env label offers).mpr hChildEdge
        · exact TypeCompilationRelation.sequence_right left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_sequence_right_edge_cases signature left right
          hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | sequence_right _ _ _ _ hChildTarget =>
            exact (hRightStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Exported sequence step correspondence follows from the raw constructor
theorem once the source symbol passes the fixed public alphabet filter. -/
theorem compilationStepCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hSequenceFuture : CompilationFutureCorrect signature (.seq left right))
    (hLeftSkipping : CompilationSkippingCorrect signature left) :
    CompilationStepCorrect signature (.seq left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_sequence signature left right
    hLeftStep hRightStep hSequenceFuture hLeftSkipping
    (residual := residual) (residual' := residual') (state := state)
    (env := env) (label := label) (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
        state target env label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature (.seq left right)
        state target env label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-! ### Exclusive and conjunctive offer correspondence -/

/- The following two observations package the common part of every tagged
child embedding.  Offer constructors use more than two children, so the
binary-choice-specific embedding lemmas above cannot be applied directly. -/
private theorem taggedChild_referencedStates_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    parent.referencedStates (childState index state) =
      (child.referencedStates state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [hOutgoing]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem taggedChild_offersAt_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (state : TypeAutomatonState) :
    parent.offersAt (childState index state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [hOutgoing]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem taggedChild_computeFuture_of_outgoing
    (parent child : PendingAutomaton) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hClosed : child.ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ child.states)
    (hCard : child.states.card ≤ parent.states.card) :
    computeFuture parent (childState index state) =
      computeFuture child state := by
  apply computeFuture_eq_of_embedding child parent (childState index)
  · exact taggedChild_referencedStates_of_outgoing parent child index
      hOutgoing
  · exact taggedChild_offersAt_of_outgoing parent child index hOutgoing
  · exact hClosed
  · exact hState
  · exact hCard

private theorem taggedChild_hasResolvedEdge_iff_of_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hTargets : child.FutureTargetsInStates)
    (hCard : child.states.card ≤ parent.states.card)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    parent.HasResolvedEdge (childState index source) env label offers
        (childState index target) ↔
      child.HasResolvedEdge source env label offers target := by
  classical
  let parentPending : PendingAutomaton :=
    { states := parent.states, edges := parent.edges }
  let childPending : PendingAutomaton :=
    { states := child.states, edges := child.edges }
  have hClosed : childPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates child hTargets
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    have hEmbedded := (hOutgoing source edge).mp ⟨hEdge, hSource⟩
    rcases hEmbedded with
      ⟨childEdge, hChildEdge, hChildSource, hEdgeEquality⟩
    have hChildTarget : childEdge.target = target := by
      rw [hEdgeEquality] at hTarget
      simpa [childPendingEdge, childState] using hTarget
    refine ⟨childEdge, hChildEdge, hChildSource, ?_, ?_, ?_, ?_,
      hChildTarget⟩
    · simpa [hEdgeEquality, childPendingEdge] using hEnvironment
    · simpa [hEdgeEquality, childPendingEdge] using hLabel
    · simpa [hEdgeEquality, childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [hEdgeEquality, childPendingEdge, childFutureSpec, hSpec]
            using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          have hComputed := taggedChild_computeFuture_of_outgoing
            parentPending childPending index hOutgoing hClosed referenced
            hReferenced hCard
          simp only [hEdgeEquality, childPendingEdge, childFutureSpec, hSpec,
            childState] at hFuture
          have hRemoved := congrArg (fun available => available \ removed)
            hComputed
          simpa [hSpec, parentPending, childPending] using
            hRemoved.symm.trans hFuture
  · rintro ⟨childEdge, hChildEdge, hChildSource, hEnvironment, hLabel,
      hCurrent, hFuture, hChildTarget⟩
    have hEmbedded := (hOutgoing source
      (childPendingEdge index childEdge)).mpr
      ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    refine ⟨childPendingEdge index childEdge, hEmbedded.1, hEmbedded.2,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa [childPendingEdge] using hEnvironment
    · simpa [childPendingEdge] using hLabel
    · simpa [childPendingEdge] using hCurrent
    · cases hSpec : childEdge.future with
      | explicit future =>
          simpa [childPendingEdge, childFutureSpec, hSpec] using hFuture
      | «at» referenced removed =>
          have hReferenced := hTargets childEdge hChildEdge referenced removed
            hSpec
          have hComputed := taggedChild_computeFuture_of_outgoing
            parentPending childPending index hOutgoing hClosed referenced
            hReferenced hCard
          simp only [hSpec] at hFuture
          simp only [childPendingEdge, childFutureSpec, childState, hSpec]
          have hRemoved := congrArg (fun available => available \ removed)
            hComputed
          simpa [hSpec, parentPending, childPending] using
            hRemoved.trans hFuture
    · simp [childPendingEdge, childState, hChildTarget]

private theorem taggedChild_hasResolvedEdge_cases_of_outgoing
    (parent child : AutomatonFragment) (index : Nat)
    (hOutgoing : ∀ state edge,
      edge ∈ parent.edges ∧ edge.source = childState index state ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧
            edge = childPendingEdge index childEdge)
    (hTargets : child.FutureTargetsInStates)
    (hCard : child.states.card ≤ parent.states.card)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : parent.HasResolvedEdge (childState index source) env label offers
      target) :
    ∃ childTarget,
      target = childState index childTarget ∧
        child.HasResolvedEdge source env label offers childTarget := by
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  have hEmbedded := (hOutgoing source edge).mp ⟨hPending, hSource⟩
  rcases hEmbedded with
    ⟨childEdge, _, _, hEdgeEquality⟩
  have hTargetEquality : target = childState index childEdge.target := by
    rw [hEdgeEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (taggedChild_hasResolvedEdge_iff_of_outgoing parent child index
    hOutgoing hTargets hCard source childEdge.target env label offers).mp
  rw [← hTargetEquality]
  exact ⟨edge, hPending, hSource, hEnvironment, hLabel, hCurrent,
    hFuture, hTarget⟩

/- Every edge from the else child of an exclusive offer is exactly the
corresponding tagged child edge. -/
private theorem buildExclusiveOfferAutomaton_outgoing_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = childState 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · simp only [childPendingEdges, Finset.mem_image] at hElse
      rcases hElse with ⟨childEdge, hChildEdge, hEquality⟩
      have hChildSource := hSource
      rw [← hEquality] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      left
      left
      exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
    · simp [childPendingEdge, childState, hChildSource]

/- Every edge from an indexed branch child of an exclusive offer is exactly
the corresponding tagged child edge. -/
private theorem buildExclusiveOfferAutomaton_outgoing_branch
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : branchAutomata[index]? = some entry)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    edge ∈ offer.edges ∧ edge.source = childState (index + 1) state ↔
      ∃ childEdge ∈ entry.2.edges,
        childEdge.source = state ∧
          edge = childPendingEdge (index + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · simp only [childPendingEdges, Finset.mem_image] at hElse
      rcases hElse with ⟨childEdge, _, hEquality⟩
      rw [← hEquality] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        have hIndex : indexed.2 = index := by
          simp [childPendingEdge, childState] at hChildSource
          omega
        have hInnerSource : childEdge.source = state := by
          simp [childPendingEdge, childState, hIndex] at hChildSource
          exact hChildSource
        have hIndexedFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
          at hIndexedFields
        rcases hIndexedFields with ⟨hBound, hValue⟩
        have hIndexedEntry : branchAutomata[indexed.2]? =
            some indexed.1 := by
          rw [List.getElem?_eq_getElem hBound, ← hValue]
        have hEntryEq : indexed.1 = entry := by
          have hOptions := congrArg
            (fun position => branchAutomata[position]?) hIndex
          change branchAutomata[indexed.2]? = branchAutomata[index]? at hOptions
          rw [hIndexedEntry, hEntry] at hOptions
          exact Option.some.inj hOptions
        rw [hEntryEq] at hChildEdge
        rw [hIndex] at hEquality
        exact ⟨childEdge, hChildEdge, hInnerSource, hEquality.symm⟩
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _, hEquality⟩
      rw [← hEquality] at hSource
      cases hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hZipBound : index < branchAutomata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ branchAutomata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    constructor
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      left
      left
      left
      right
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      right
      exact ⟨(entry, index), hIndexed,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/- The two tagged child families of a conjunctive offer are disjoint from all
fresh root edges. -/
private theorem buildConjunctiveOfferAutomaton_outgoing_child
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (index : Nat) (child : AutomatonFragment)
    (hIndex : (index = 0 ∧ child = conjunction) ∨
      (index = 1 ∧ child = elseAutomaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    edge ∈ offer.edges ∧ edge.source = childState index state ↔
      ∃ childEdge ∈ child.edges,
        childEdge.source = state ∧ edge = childPendingEdge index childEdge := by
  classical
  rcases hIndex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · constructor
    · rintro ⟨hEdge, hSource⟩
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hChild | hOther) | hEnabled) | hWait) | hElse)
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
      · simp only [childPendingEdges, Finset.mem_image] at hOther
        rcases hOther with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
        rcases hEnabled with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hElse
        rcases hElse with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        left
        left
        left
        left
        exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
      · simp [childPendingEdge, childState, hChildSource]
  · constructor
    · rintro ⟨hEdge, hSource⟩
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hEdge
      rcases hEdge with ((((hOther | hChild) | hEnabled) | hWait) | hElse)
      · simp only [childPendingEdges, Finset.mem_image] at hOther
        rcases hOther with ⟨childEdge, _, hEquality⟩
        rw [← hEquality] at hSource
        simp [childPendingEdge, childState] at hSource
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEquality⟩
        have hChildSource := hSource
        rw [← hEquality] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        exact ⟨childEdge, hChildEdge, hChildSource, hEquality.symm⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
        rcases hEnabled with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
      · simp only [Finset.mem_image, Finset.mem_filter] at hElse
        rcases hElse with ⟨environment, _, hEquality⟩
        rw [← hEquality] at hSource
        cases hSource
    · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
      constructor
      · simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
          Finset.mem_union]
        left
        left
        left
        right
        exact Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩
      · simp [childPendingEdge, childState, hChildSource]

/- Exact resolved-edge classifier at the fresh exclusive-offer root. -/
private theorem buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildExclusiveOfferAutomaton signature branches
      elseAutomaton branchAutomata
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (∃ indexed ∈ branchAutomata.zipIdx,
        env ∈ signature.localEnvironments ∧
          typeNeed indexed.1.1 ∈ env.immediate ∧
          typeBranchNeeds branches ∩ env.future = ∅ ∧
          label = TypeLabel.message indexed.1.1.1 indexed.1.1.2 ∧
          offers.current = {indexed.1.1} ∧
          computeFuture pending
              (childState (indexed.2 + 1) indexed.1.2.initial) =
            offers.future ∧
          target = childState (indexed.2 + 1) indexed.1.2.initial) ∨
      (env ∈ signature.localEnvironments ∧ env.clock = false ∧
        typeBranchNeeds branches ∩ env.future ≠ ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeWaitingOffers env branches ∧
        computeFuture pending .root \ typeWaitingOffers env branches =
          offers.future ∧ target = .root) ∨
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future = ∅ ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (childState 0 elseAutomaton.initial) =
          offers.future ∧ target = childState 0 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hElse | hIndexed) | hBranch) | hWait) | hElseEdge),
      hSource, hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · simp only [childPendingEdges, Finset.mem_image] at hElse
      rcases hElse with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
        rcases hNewEdge with ⟨edgeEnvironment, hConditions, rfl⟩
        left
        simp only [Finset.sdiff_empty] at hFuture
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        rcases hConditions with ⟨hLocal, hEnabled, hResolved⟩
        subst env
        have hSemanticLabel : label =
            TypeLabel.message indexed.1.1.1 indexed.1.1.2 := by
          have hCongruence :=
            congrArg AutomatonConstructionLabel.semantic hLabel
          simpa using hCongruence.symm
        exact ⟨indexed, hIndexed, hLocal, hEnabled, hResolved,
          hSemanticLabel, hCurrent.symm, hFuture, hTarget.symm⟩
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      left
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hClock, hFutureBranches⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      refine ⟨hLocal, hClock, hFutureBranches, hSemanticLabel, ?_, ?_,
        hTarget.symm⟩
      · simpa only [typeWaitingOffers] using hCurrent.symm
      · simpa only [typeWaitingOffers, Finset.union_assoc,
          Finset.singleton_union] using hFuture
    · simp only [Finset.mem_image, Finset.mem_filter] at hElseEdge
      rcases hElseEdge with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      right
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate, hResolved⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hResolved, hSemanticLabel,
        hCurrent.symm, hFuture, hTarget.symm⟩
  · rintro (hBranch | hWait | hElse)
    · rcases hBranch with ⟨indexed, hIndexed, hLocal, hEnabled,
        hResolved, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible
            (TypeLabel.message indexed.1.1.1 indexed.1.1.2)
          current := {indexed.1.1}
          future := .at
            (childState (indexed.2 + 1) indexed.1.2.initial) ∅
          target := childState (indexed.2 + 1) indexed.1.2.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        rw [mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hEnabled, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hWait with ⟨hLocal, hClock, hFutureBranches, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeWaitingOffers env branches
          future := .at .root (typeWaitingOffers env branches)
          target := .root }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hClock, hFutureBranches⟩⟩, by
              simp [typeWaitingOffers]⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hElse with ⟨hLocal, hImmediate, hResolved, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 elseAutomaton.initial) ∅
          target := childState 0 elseAutomaton.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hImmediate, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
/- Exact resolved-edge classifier at the fresh conjunctive-offer root. -/
private theorem buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate ≠ ∅ ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (childState 0 conjunction.initial) =
          offers.future ∧ target = childState 0 conjunction.initial) ∨
      (env ∈ signature.localEnvironments ∧ env.clock = false ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future ≠ ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeWaitingOffers env branches ∧
        computeFuture pending .root \ typeWaitingOffers env branches =
          offers.future ∧ target = .root) ∨
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future = ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeBranchActions branches ∧
        computeFuture pending (childState 1 elseAutomaton.initial) =
          offers.future ∧ target = childState 1 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hConjunction | hElseChild) | hEnabled) | hWait) |
      hElseEdge), hSource, hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · simp only [childPendingEdges, Finset.mem_image] at hConjunction
      rcases hConjunction with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [childPendingEdges, Finset.mem_image] at hElseChild
      rcases hElseChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
      rcases hEnabled with ⟨edgeEnvironment, hConditions, rfl⟩
      left
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hSemanticLabel, hCurrent.symm,
        hFuture, hTarget.symm⟩
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      left
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with
        ⟨hLocal, hClock, hImmediate, hFutureBranches⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      refine ⟨hLocal, hClock, hImmediate, hFutureBranches, hSemanticLabel,
        ?_, ?_, hTarget.symm⟩
      · simpa only [typeWaitingOffers] using hCurrent.symm
      · simpa only [typeWaitingOffers, Finset.union_assoc,
          Finset.singleton_union] using hFuture
    · simp only [Finset.mem_image, Finset.mem_filter] at hElseEdge
      rcases hElseEdge with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      right
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate, hResolved⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hResolved, hSemanticLabel,
        hCurrent.symm, hFuture, hTarget.symm⟩
  · rintro (hEnabled | hWait | hElse)
    · rcases hEnabled with ⟨hLocal, hImmediate, hLabel, hCurrent,
        hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 conjunction.initial) ∅
          target := childState 0 conjunction.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr ⟨hLocal, hImmediate⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hWait with ⟨hLocal, hClock, hImmediate, hFutureBranches,
        hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeWaitingOffers env branches
          future := .at .root (typeWaitingOffers env branches)
          target := .root }, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hClock, hImmediate, hFutureBranches⟩⟩, by
              simp [typeWaitingOffers]⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hElse with ⟨hLocal, hImmediate, hResolved, hLabel,
        hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := typeBranchActions branches
          future := .at (childState 1 elseAutomaton.initial) ∅
          target := childState 1 elseAutomaton.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr
            ⟨hLocal, ⟨hImmediate, hResolved⟩⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm

private theorem compileTypeFuel_xoffer_else_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches)).HasResolvedEdge
          (childState 0 source) env label offers (childState 0 target) ↔
      (compileTypeFuel signature (typeCompilationFuel elseType) elseType).HasResolvedEdge
        source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hCard : elseFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      elseFragment.states.card = (childStates 0 elseFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge :=
    buildExclusiveOfferAutomaton_outgoing_else signature branches
      elseFragment branchAutomata
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    elseFragment 0 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature elseType
    hElseFuel (typeCompilationFuel_sufficient elseType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, branchAutomata, fuel, hStable] using hRaw

private theorem compileTypeFuel_xoffer_branch_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (action : BareMessage) (branchType : PactType) (index : Nat)
    (hEntry : branches[index]? = some (action, branchType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches)).HasResolvedEdge
          (childState (index + 1) source) env label offers
          (childState (index + 1) target) ↔
      (compileTypeFuel signature
        (typeCompilationFuel branchType) branchType).HasResolvedEdge
          source env label offers target := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchFragment := compileTypeFuel signature fuel branchType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hBranchMember : (action, branchType) ∈ branches := by
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hMember := List.getElem_mem hBound
    simpa [hValue] using hMember
  have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
    exact le_trans
      (typeCompilationFuel_le_typeBranchCompilationFuel branches
        (action, branchType) hBranchMember)
      (by simp [fuel])
  have hTargets : branchFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel branchType
      hBranchFuel
  have hAutomatonEntry : branchAutomata[index]? =
      some (action, branchFragment) := by
    simp [branchAutomata, branchFragment, hEntry]
  have hZipEntry : ((action, branchFragment), index) ∈
      branchAutomata.zipIdx := by
    rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < branchAutomata.zipIdx.length := by
      simpa using hBound
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := branchAutomata) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  have hCard : branchFragment.states.card ≤ fragment.states.card := by
    have hIndexedSubset : childStates (index + 1) branchFragment ⊆
        indexedFragmentStates branchAutomata := by
      intro state hState
      rw [indexedFragmentStates, mem_foldl_union_iff]
      right
      exact ⟨((action, branchFragment), index), hZipEntry, hState⟩
    have hSubset : childStates (index + 1) branchFragment ⊆
        fragment.states := by
      intro state hState
      have hIndexed := hIndexedSubset hState
      simp [fragment, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, hIndexed]
    calc
      branchFragment.states.card =
          (childStates (index + 1) branchFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧
          edge.source = childState (index + 1) state ↔
        ∃ childEdge ∈ branchFragment.edges,
          childEdge.source = state ∧
            edge = childPendingEdge (index + 1) childEdge :=
    buildExclusiveOfferAutomaton_outgoing_branch signature branches
      elseFragment branchAutomata index (action, branchFragment)
      hAutomatonEntry
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    branchFragment (index + 1) hOutgoing hTargets hCard source target env
    label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature branchType
    hBranchFuel (typeCompilationFuel_sufficient branchType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    elseFragment, branchFragment, branchAutomata, fuel, hStable] using hRaw

private theorem compileTypeFuel_offer_conjunction_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState 0 source) env label offers (childState 0 target) ↔
      (compileTypeFuel signature
        (typeCompilationFuel (parallelTypeBranches branches))
        (parallelTypeBranches branches)).HasResolvedEdge
          source env label offers target := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel]
  have hTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hCard : conjunction.states.card ≤ fragment.states.card := by
    have hSubset : childStates 0 conjunction ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      conjunction.states.card = (childStates 0 conjunction).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ conjunction.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge :=
    buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    conjunction 0 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature conjunctionType
    hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    conjunction, conjunctionType, elseFragment, fuel, hStable] using hRaw

private theorem compileTypeFuel_offer_else_child_edge_iff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileTypeFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches)).HasResolvedEdge
          (childState 1 source) env label offers (childState 1 target) ↔
      (compileTypeFuel signature (typeCompilationFuel elseType) elseType).HasResolvedEdge
        source env label offers target := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hCard : elseFragment.states.card ≤ fragment.states.card := by
    have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
      intro state hState
      simp [fragment, buildConjunctiveOfferAutomaton,
        finishAutomatonFragment, hState]
    calc
      elseFragment.states.card = (childStates 1 elseFragment).card := by
        simp only [childStates]
        symm
        apply Finset.card_image_of_injective
        intro first second hEquality
        injection hEquality
      _ ≤ fragment.states.card := Finset.card_le_card hSubset
  have hOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 1 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 1 childEdge :=
    buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 1 elseFragment (Or.inr ⟨rfl, rfl⟩)
  have hRaw := taggedChild_hasResolvedEdge_iff_of_outgoing fragment
    elseFragment 1 hOutgoing hTargets hCard source target env label offers
  have hStable := compileTypeFuel_eq_of_sufficient signature elseType
    hElseFuel (typeCompilationFuel_sufficient elseType)
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel, fragment,
    conjunction, conjunctionType, elseFragment, fuel, hStable] using hRaw

private theorem compileTypeFuel_xoffer_else_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches)).HasResolvedEdge
        (childState 0 source) env label offers target) :
    ∃ childTarget,
      target = childState 0 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel elseType) elseType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildExclusiveOfferAutomaton_outgoing_else signature branches
      elseFragment branchAutomata source pendingEdge).mp
      ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 0 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_xoffer_else_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_xoffer_branch_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (action : BareMessage) (branchType : PactType) (index : Nat)
    (hEntry : branches[index]? = some (action, branchType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches)).HasResolvedEdge
        (childState (index + 1) source) env label offers target) :
    ∃ childTarget,
      target = childState (index + 1) childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel branchType) branchType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchFragment := compileTypeFuel signature fuel branchType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hAutomatonEntry : branchAutomata[index]? =
      some (action, branchFragment) := by
    simp [branchAutomata, branchFragment, hEntry]
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildExclusiveOfferAutomaton_outgoing_branch signature branches
      elseFragment branchAutomata index (action, branchFragment)
      hAutomatonEntry source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target =
      childState (index + 1) childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_xoffer_branch_child_edge_iff signature elseType
    branches action branchType index hEntry source childEdge.target env label
    offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_offer_conjunction_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches)).HasResolvedEdge
        (childState 0 source) env label offers target) :
    ∃ childTarget,
      target = childState 0 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranches branches))
          (parallelTypeBranches branches)).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
      source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 0 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_offer_conjunction_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem compileTypeFuel_offer_else_child_edge_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches)).HasResolvedEdge
        (childState 1 source) env label offers target) :
    ∃ childTarget,
      target = childState 1 childTarget ∧
        (compileTypeFuel signature
          (typeCompilationFuel elseType) elseType).HasResolvedEdge
            source env label offers childTarget := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hResolved := hEdge
  rw [hFragment] at hResolved
  rcases hResolved with ⟨pendingEdge, hPending, hSource, _, _, _, _,
    hTarget⟩
  have hOutgoing :=
    (buildConjunctiveOfferAutomaton_outgoing_child signature branches
      elseFragment conjunction 1 elseFragment (Or.inr ⟨rfl, rfl⟩)
      source pendingEdge).mp ⟨hPending, hSource⟩
  rcases hOutgoing with ⟨childEdge, _, _, hPendingEquality⟩
  have hTargetEquality : target = childState 1 childEdge.target := by
    rw [hPendingEquality] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  refine ⟨childEdge.target, hTargetEquality, ?_⟩
  apply (compileTypeFuel_offer_else_child_edge_iff signature elseType
    branches source childEdge.target env label offers).mp
  simpa [hTargetEquality] using hEdge

private theorem typeBranchEnabled_exists_iff
    (env : TypeEnvironment) (branches : List (BareMessage × PactType)) :
    (∃ enabled ∈ branches, TypeBranchEnabled env enabled) ↔
      typeBranchNeeds branches ∩ env.immediate ≠ ∅ := by
  classical
  constructor
  · rintro ⟨enabled, hEnabledMember, hEnabled⟩ hEmpty
    have hNeed : typeNeed enabled.1 ∈ typeBranchNeeds branches := by
      simp only [typeBranchNeeds, List.mem_toFinset, List.mem_map]
      exact ⟨enabled, hEnabledMember, rfl⟩
    have hIntersection : typeNeed enabled.1 ∈
        typeBranchNeeds branches ∩ env.immediate :=
      Finset.mem_inter.mpr ⟨hNeed, hEnabled⟩
    rw [hEmpty] at hIntersection
    simp at hIntersection
  · intro hNonempty
    have hWitness := Finset.nonempty_iff_ne_empty.mpr hNonempty
    rcases hWitness with ⟨need, hNeed⟩
    rcases Finset.mem_inter.mp hNeed with ⟨hBranchNeed, hImmediate⟩
    simp only [typeBranchNeeds, List.mem_toFinset, List.mem_map]
      at hBranchNeed
    rcases hBranchNeed with ⟨enabled, hEnabledMember, hNeedEquality⟩
    refine ⟨enabled, hEnabledMember, ?_⟩
    unfold TypeBranchEnabled
    rw [hNeedEquality]
    exact hImmediate

private theorem List.exists_getElem?_eq_some_of_mem
    {Element : Type} {element : Element} {items : List Element}
    (hMember : element ∈ items) :
    ∃ index : Nat, items[index]? = some element := by
  rcases List.mem_iff_getElem.mp hMember with ⟨index, hBound, hValue⟩
  refine ⟨index, ?_⟩
  rw [List.getElem?_eq_getElem hBound, hValue]

private theorem TypeLabel.message_injective
    {first second : BareMessage}
    (hEquality : TypeLabel.message first.1 first.2 =
      TypeLabel.message second.1 second.2) :
    first = second := by
  rcases first with ⟨firstMessage, firstDirection⟩
  rcases second with ⟨secondMessage, secondDirection⟩
  simp [TypeLabel.message] at hEquality
  simp [hEquality.1, hEquality.2]

private theorem TypeLabel.message_ne_silent (action : BareMessage) :
    TypeLabel.message action.1 action.2 ≠ TypeLabel.silent := by
  rcases action with ⟨message, direction⟩
  simp [TypeLabel.message, TypeLabel.silent]

private theorem TypeOffers.xoffer_branch_fields
    {env : TypeEnvironment} {elseType branchType : PactType}
    {branches : List (BareMessage × PactType)} {action : BareMessage}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      (TypeLabel.message action.1 action.2) branchType current future) :
    current = {action} ∧ future = typeFutureOffers branchType := by
  generalize hLabel : TypeLabel.message action.1 action.2 = actualLabel
    at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ actualAction _ _ =>
      have hAction := TypeLabel.message_injective hLabel
      subst actualAction
      exact ⟨rfl, rfl⟩
  | xoffer_else =>
      exact (TypeLabel.message_ne_silent action hLabel).elim
  | xoffer_wait =>
      exact (TypeLabel.message_ne_silent action hLabel).elim

private theorem TypeOffers.xoffer_else_fields
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      TypeLabel.silent elseType current future) :
    current = ∅ ∧ future = typeFutureOffers elseType := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ action _ _ =>
      exact (TypeLabel.message_ne_silent action hLabel.symm).elim
  | xoffer_else => exact ⟨rfl, rfl⟩

private theorem TypeOffers.xoffer_wait_fields
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer elseType branches)
      TypeLabel.silent (.xoffer elseType branches) current future) :
    current = typeWaitingOffers env branches ∧
      future = typeFutureOffers (.xoffer elseType branches) \
        typeWaitingOffers env branches := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | xoffer_branch _ _ _ action _ _ =>
      exact (TypeLabel.message_ne_silent action hLabel.symm).elim
  | xoffer_wait => exact ⟨rfl, rfl⟩

/-- Exclusive offers preserve raw pending-fragment step correspondence. -/
theorem compilationFragmentStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationFragmentStepCorrect signature (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | xoffer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | xoffer_branch _ _ _ action _ hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled, hResolved⟩
            rcases TypeOffers.xoffer_branch_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient residual' fuel := by
              exact le_trans
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, residual') hBranchMember)
                (by simp [fuel])
            let branchFragment := compileTypeFuel signature fuel residual'
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation signature fuel residual'
                hBranchFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            have hAutomatonEntry : branchAutomata[index]? =
                some (action, branchFragment) := by
              simp [branchAutomata, branchFragment, hEntry]
            rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
              ⟨hBound, hValue⟩
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa using hBound
            have hZipEntry : ((action, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            refine ⟨childState (index + 1) branchFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              (TypeLabel.message action.1 action.2) ⟨current, future⟩
              (childState (index + 1) branchFragment.initial)).mpr
            left
            exact ⟨((action, branchFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hImmediate, hResolved⟩
            rcases TypeOffers.xoffer_else_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hImmediate, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_wait _ _ _ hConditions =>
            rcases hConditions with ⟨_, hUnresolved, hClock⟩
            rcases TypeOffers.xoffer_wait_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.xoffer elseType branches) .root
                (.xoffer elseType branches) :=
              TypeCompilationRelation.xoffer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, by
                simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent,
              hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment branchAutomata env label
          ⟨current, future⟩
          target).mp hEdge with hBranch | hWait | hElse
        · rcases hBranch with ⟨indexed, hIndexed, _, hEnabled, hResolved,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [branchAutomata] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel branch.2) := by
            rw [hValue]
            simp [branchAutomata, branch]
          rw [hIndexedValue] at hEnabled hLabel hCurrent hEdgeFuture hTargetState
          subst target
          have hBranchMember : branch ∈ branches :=
            List.getElem_mem hBranchBound
          have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                branch hBranchMember)
              (by simp [fuel])
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation signature fuel branch.2
              hBranchFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel branch.2).initial)
              branch.2 :=
            TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
              branches branch.1 indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers branch.2 := hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
          · exact
              (TypeOffers.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
        · rcases hWait with ⟨_, hClock, hFutureBranches, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.xoffer elseType branches) .root
              (.xoffer elseType branches) :=
            TypeCompilationRelation.xoffer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
          · exact
              (TypeOffers.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
        · rcases hElse with ⟨_, hImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
          · exact
              (TypeOffers.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr
            hChildEdge
        · exact TypeCompilationRelation.xoffer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      constructor
      · intro hSemanticStep
        rcases (hStep hChildRelated hLocalEnvironment).mp hSemanticStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_branch_child_edge_iff signature
            elseType branches action branchType index hEntry childQ
            childTarget env label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.xoffer_branch elseType branchType
            residual' branches action index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
          elseType branches action branchType index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_branch _ targetBranchType _ _ targetAction _ _
            hTargetEntry hChildTarget =>
            have hEntryEquality : (action, branchType) =
                (targetAction, targetBranchType) :=
              Option.some.inj (hEntry.symm.trans hTargetEntry)
            cases hEntryEquality
            exact (hStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Public exclusive-offer correspondence follows by alphabet export. -/
theorem compilationStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationStepCorrect signature (.xoffer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_xoffer signature elseType
    branches hElseStep hBranchStep hFuture (residual := residual)
    (residual' := residual') (state := state) (env := env) (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mpr hEdge, hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mp hEdge, hTarget⟩

private theorem TypeOffers.offer_some_fields_of_enabled
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hEnabled : ∃ enabled ∈ branches, TypeBranchEnabled env enabled)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      (parallelTypeBranches branches) current future) :
    current = ∅ ∧
      future = typeFutureOffers (parallelTypeBranches branches) := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : parallelTypeBranches branches = actualTarget at hOffers
  cases hOffers with
  | offer_some => exact ⟨rfl, rfl⟩
  | offer_else _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim
  | offer_wait _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim

private theorem TypeOffers.offer_else_fields_of_resolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hResolved : TypeResolved env branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      elseType current future) :
    current = typeBranchActions branches ∧
      future = typeFutureOffers elseType := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : elseType = actualTarget at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else => exact ⟨rfl, rfl⟩

private theorem TypeOffers.offer_wait_fields_of_unresolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {target : PactType} {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hUnresolved : ¬ TypeResolved env branches)
    (hTarget : target = .offer elseType branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      target current future) :
    current = typeWaitingOffers env branches ∧
      future = typeFutureOffers (.offer elseType branches) \
        typeWaitingOffers env branches := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else _ _ _ hConditions =>
      exact (hUnresolved hConditions.2.2).elim
  | offer_wait => exact ⟨rfl, rfl⟩

/-- Conjunctive offers preserve raw pending-fragment step correspondence. -/
theorem compilationFragmentStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : CompilationFragmentStepCorrect signature
      (parallelTypeBranches branches))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationFragmentStepCorrect signature (.offer elseType branches) := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness hOffers with ⟨hCurrent, hOfferFuture⟩
            have hConjunctionFuel :
                TypeCompilationFuelSufficient conjunctionType fuel := by
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranches]
              simp [fuel]
            have hInitial : TypeCompilationRelation conjunctionType
                conjunction.initial conjunctionType :=
              compileTypeFuel_initial_relation signature fuel conjunctionType
                hConjunctionFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 conjunction.initial) conjunctionType :=
              TypeCompilationRelation.offer_branches elseType conjunctionType
                branches conjunction.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 conjunction.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 conjunction.initial)).mpr
            left
            exact ⟨hLocalEnvironment,
              (typeBranchEnabled_exists_iff env branches).mp
                hEnabledWitness,
              rfl, hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 1 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 1 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 1 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment conjunction env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨_, hImmediate, hLabel, hCurrent,
            hEdgeFuture, hTargetState⟩
          subst target
          have hConjunctionFuel :
              TypeCompilationFuelSufficient conjunctionType fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [fuel]
          have hInitial : TypeCompilationRelation conjunctionType
              conjunction.initial conjunctionType :=
            compileTypeFuel_initial_relation signature fuel conjunctionType
              hConjunctionFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 conjunction.initial) conjunctionType :=
            TypeCompilationRelation.offer_branches elseType conjunctionType
              branches conjunction.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers conjunctionType :=
            hEdgeFuture.symm.trans hComputed
          rcases (typeBranchEnabled_exists_iff env branches).mpr hImmediate
            with ⟨enabled, hBranchMember, hBranchEnabled⟩
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 1 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep hChildRelated hLocalEnvironment).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ _ hChildTarget =>
            exact (hConjunctionStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Public conjunctive-offer correspondence follows by alphabet export. -/
theorem compilationStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : CompilationFragmentStepCorrect signature
      (parallelTypeBranches branches))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationStepCorrect signature (.offer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_offer signature elseType
    branches hConjunctionStep hElseStep hFuture (residual := residual)
    (residual' := residual') (state := state) (env := env) (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer elseType branches) state target env label offers
        hSignatureSymbol).mpr hEdge, hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer elseType branches) state target env label offers
        hSignatureSymbol).mp hEdge, hTarget⟩

/-- Complete root-equivalent correspondence for the literal-skip sequence
bridge. -/
theorem compileType_sequence_skip_bridge_step_iff
    (signature : TypeAlphabet) (right : PactType) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : SequenceSkipBridgeFutureCorrect signature right)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
        signature.transitionAlphabet) :
    DecoratedTypeTransition env (.seq .skip right) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right ↔
      ∃ state',
        (compileType signature (.seq .skip right)).HasEdge
            (.child 0 (compileType signature .skip).initial) env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) state' ∧
          TypeCompilationRelation (.seq .skip right) state' right := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 1 (compileType signature right).initial, ?_, ?_⟩
    · exact compileType_sequence_skip_bridge_edge signature right
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.sequence_right .skip right right _
        (compileType_initial_relation signature right)
  · intro _
    exact ⟨TypeTransition.skip_seq env right hWellFormed,
      TypeOffers.skip_seq env right hWellFormed⟩

private theorem TypeOffers.sequence_choice_left_fields
    {env : TypeEnvironment} {left right continuation : PactType}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.seq (.choice left right) continuation)
      TypeLabel.silent (.seq left continuation) current future) :
    current = ∅ ∧
      future = typeFutureOffers (.seq left continuation) := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | seq _ _ _ _ _ _ childFuture hChild =>
      subst actualLabel
      have hFields := TypeOffers.choice_left_fields
        (env := env) (left := left) (right := right)
        (current := current) (future := childFuture) hChild
      simpa [hFields.1] using hFields
  | _ => simp_all

/-!
Future offers are optimistic over the remainder of the current cycle.  This
regression records the smallest nested administrative step: after selecting
the left branch of `(choice a! skip) ; b!`, both `a!` and the subsequent `b!`
belong to the future menu.  The constructor graph and semantic offer rule must
agree on that set.
-/
theorem nested_sequence_future_scope_regression :
    let first : BareMessage := ("a", .send)
    let second : BareMessage := ("b", .send)
    let left : PactType := .choice (.message first.1 first.2) .skip
    let processType : PactType := .seq left (.message second.1 second.2)
    let source : TypeAutomatonState := .child 0 .root
    let target : TypeAutomatonState := .child 0 (.child 0 .root)
    let leftFinal : TypeAutomatonState := .child 0 (.child 0 .final)
    let continuation : TypeAutomatonState := .child 1 .root
    let readyForFirst : TypeEnvironment :=
      { immediate := {typeNeed first}, future := ∅, clock := false }
    let selectionEdge : PendingAutomatonEdge :=
      { source := source
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := ∅
        future := .at target ∅
        target := target }
    let firstEdge : PendingAutomatonEdge :=
      { source := target
        environment := readyForFirst
        label := .visible (TypeLabel.message first.1 first.2)
        current := {first}
        future := .at continuation ∅
        target := leftFinal }
    let secondEdge : PendingAutomatonEdge :=
      { source := continuation
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := {second}
        future := .explicit ∅
        target := continuation }
    let graph : PendingAutomaton :=
      { states := {source, target, leftFinal, continuation}
        edges := {selectionEdge, firstEdge, secondEdge} }
    let residual : PactType :=
      .seq (.message first.1 first.2) (.message second.1 second.2)
    let offers : TypeOfferSummary :=
      { current := ∅, future := typeFutureOffers residual }
    TypeCompilationRelation processType source processType ∧
      TypeCompilationRelation processType target residual ∧
      computeFuture graph target = {first, second} ∧
      DecoratedTypeTransition TypeEnvironment.empty processType
        TypeLabel.silent offers residual := by
  dsimp
  constructor
  · exact TypeCompilationRelation.sequence_left
      (.choice (.message "a" .send) .skip) (.message "b" .send)
      (.choice (.message "a" .send) .skip) .root
      (TypeCompilationRelation.choice_source (.message "a" .send) .skip)
  constructor
  · exact TypeCompilationRelation.sequence_left
      (.choice (.message "a" .send) .skip) (.message "b" .send)
      (.message "a" .send) (.child 0 .root)
      (TypeCompilationRelation.choice_left (.message "a" .send) .skip
        (.message "a" .send) .root
        (TypeCompilationRelation.message_source "a" .send))
  constructor
  · native_decide
  · constructor
    · exact TypeTransition.seq TypeEnvironment.empty
        (.choice (.message "a" .send) .skip) (.message "a" .send)
        (.message "b" .send) TypeLabel.silent
        (TypeTransition.choice_left TypeEnvironment.empty
          (.message "a" .send) .skip (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed]))
    · have hChoice := TypeOffers.choice_left TypeEnvironment.empty
          (.message "a" .send) .skip (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed])
      have hSequence := TypeOffers.seq TypeEnvironment.empty
        (.choice (.message "a" .send) .skip) (.message "a" .send)
        (.message "b" .send) TypeLabel.silent ∅
        (typeFutureOffers (.message "a" .send)) hChoice
      simpa using hSequence

/-! ### Parallel-product correspondence -/

/-- A visible resolved child edge is exactly the record form of the raw
`HasResolvedEdge` relation. -/
private theorem mem_resolvedAutomatonEdges_visible_iff
    (fragment : AutomatonFragment) (source target : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    ({ source := source
       environment := environment
       label := .visible label
       current := offers.current
       future := offers.future
       target := target } : AutomatonFragmentEdge) ∈
        resolvedAutomatonEdges fragment ↔
      fragment.HasResolvedEdge source environment label offers target := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image,
    AutomatonFragment.HasResolvedEdge]
  constructor
  · rintro ⟨edge, hEdge, hResolved⟩
    have hSource := congrArg AutomatonFragmentEdge.source hResolved
    have hEnvironment := congrArg AutomatonFragmentEdge.environment hResolved
    have hLabel := congrArg AutomatonFragmentEdge.label hResolved
    have hCurrent := congrArg AutomatonFragmentEdge.current hResolved
    have hFuture := congrArg AutomatonFragmentEdge.future hResolved
    have hTarget := congrArg AutomatonFragmentEdge.target hResolved
    refine ⟨edge, hEdge, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hSource
    · simpa using hEnvironment
    · simpa using hLabel
    · simpa using hCurrent
    · simpa using hFuture
    · simpa using hTarget
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    refine ⟨edge, hEdge, ?_⟩
    cases edge
    simp_all

/-- Offer derivations carry the matching undecorated transition.  This is used
for the independent sibling-offer witnesses in the parallel product. -/
private theorem TypeOffers.to_transition
    {environment : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers environment source label target current future) :
    TypeTransition environment source label target := by
  apply TypeOffers.rec
    (motive_1 := fun env source label target _ _ _ =>
      TypeTransition env source label target)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
  all_goals aesop
  exact TypeTransition.xoffer_branch env elseType branches (fst, snd)
    processType ⟨left, left_1, left_2, right⟩

private theorem restrictTypeOffers_subset_localEnvironmentActions
    (signature : TypeAlphabet) (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (offers : Finset BareMessage) :
    restrictTypeOffers interface offers ⊆
      signature.localEnvironmentActions := by
  intro action hAction
  rcases action with ⟨message, direction⟩
  have hInternal : message ∈ signature.interface :=
    hInterface (Finset.mem_filter.mp hAction).2
  simp only [TypeAlphabet.localEnvironmentActions, Finset.mem_image]
  cases direction
  · refine ⟨(message, MessageDir.recv), ?_, rfl⟩
    simp [TypeAlphabet.localActions, TypeAlphabet.interfaceActions, hInternal]
  · refine ⟨(message, MessageDir.send), ?_, rfl⟩
    simp [TypeAlphabet.localActions, TypeAlphabet.interfaceActions, hInternal]

/-- A semantic sibling-local environment stays inside the compiler's local
universe when its outer environment is already construction-local. -/
private theorem TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {sibling : PactType} {label : TypeLabel}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    localEnvironment ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuter⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
        · rw [hImmediate]
          apply Finset.union_subset
          · exact hOuterImmediate
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface current
        · rw [hFuture]
          intro action hAction
          have hAvailable := Finset.mem_sdiff.mp hAction
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hAvailable.2⟩
          rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
          · exact (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface future hInternal
        · cases localEnvironment
          simp_all

/-- A semantic sibling-local environment is contained in the compiler's local
environment universe whenever its outer environment is exported and the
constructor interface is declared by the signature. -/
private theorem TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment
    (signature : TypeAlphabet) (interface : Interface)
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {sibling : PactType} {label : TypeLabel}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.environments)
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    localEnvironment ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      simp only [TypeAlphabet.environments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuter⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        right
        refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
        · rw [hImmediate]
          apply Finset.union_subset
          · exact hOuterImmediate.trans
              (signature.environmentActions_subset_localEnvironmentActions)
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface current
        · rw [hFuture]
          intro action hAction
          have hAvailable := Finset.mem_sdiff.mp hAction
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hAvailable.2⟩
          rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
          · exact signature.environmentActions_subset_localEnvironmentActions
              (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
          · exact restrictTypeOffers_subset_localEnvironmentActions signature
              interface hInterface future hInternal
        · cases localEnvironment
          simp_all

/-- The set-theoretic fields of an ordinary sibling-local environment are
enough to place it in the compiler's local environment universe.  This
version does not require the semantic offer derivation and is therefore
usable before synchronization witnesses have been reconstructed. -/
private theorem TypeAlphabet.localEnvironment_mem_of_ordinary_fields
    (signature : TypeAlphabet) (interface : Interface)
    {outer localEnvironment : TypeEnvironment}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLocalClock : localEnvironment.clock = false)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface future) \
        localEnvironment.immediate) :
    localEnvironment ∈ signature.localEnvironments := by
  simp only [TypeAlphabet.environments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hOuter
  rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
    outerFuture, hOuterFuture, hOuter⟩
  · subst outer
    simp [TypeEnvironment.tock] at hOuterClock
  · subst outer
    simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image]
    right
    refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
    · rw [hImmediate]
      apply Finset.union_subset
      · exact hOuterImmediate.trans
          signature.environmentActions_subset_localEnvironmentActions
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface current
    · rw [hFuture]
      intro action hAction
      have hAvailable := Finset.mem_sdiff.mp hAction
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hAvailable.2⟩
      rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
      · exact signature.environmentActions_subset_localEnvironmentActions
          (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface future hInternal
    · cases localEnvironment
      simp_all

/-- Ordinary local-environment fields preserve the construction-local
environment universe when the outer environment is itself construction-local. -/
private theorem TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer localEnvironment : TypeEnvironment}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hOuterClock : outer.clock = false)
    (hLocalClock : localEnvironment.clock = false)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface future) \
        localEnvironment.immediate) :
    localEnvironment ∈ signature.localEnvironments := by
  simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hOuter
  rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
    outerFuture, hOuterFuture, hOuter⟩
  · subst outer
    simp [TypeEnvironment.tock] at hOuterClock
  · subst outer
    simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image]
    right
    refine ⟨localEnvironment.immediate, ?_, localEnvironment.future, ?_, ?_⟩
    · rw [hImmediate]
      apply Finset.union_subset
      · exact hOuterImmediate
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface current
    · rw [hFuture]
      intro action hAction
      have hAvailable := Finset.mem_sdiff.mp hAction
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, hAvailable.2⟩
      rcases Finset.mem_union.mp hAvailable.1 with hBoundary | hInternal
      · exact (Finset.mem_sdiff.mp (hOuterFuture hBoundary)).1
      · exact restrictTypeOffers_subset_localEnvironmentActions signature
          interface hInterface future hInternal
    · cases localEnvironment
      simp_all

/-- A synchronized product witness over an exported outer environment forces
both component environments into the compiler's local environment domain. -/
private theorem TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses
    (signature : TypeAlphabet) (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment ∈ signature.localEnvironments ∧
      right.environment ∈ signature.localEnvironments := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedEnvironment :
          combineAutomatonEnvironment interface left.environment
              right.environment ∈ signature.environments := by
        rw [hOuter]
        exact hOuterEnvironment
      have hCombinedClock :
          (combineAutomatonEnvironment interface left.environment
              right.environment).clock = false := by
        simp [combineAutomatonEnvironment, hLeftClock]
      exact ⟨
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hLeftClock hLeftImmediate hLeftFuture,
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hRightClock hRightImmediate hRightFuture⟩

/-- Local-domain counterpart of
`localEnvironments_of_syncAutomatonEdgeWitnesses`. -/
private theorem TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses_local
    (signature : TypeAlphabet) (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.localEnvironments)
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment ∈ signature.localEnvironments ∧
      right.environment ∈ signature.localEnvironments := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨_, hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedEnvironment :
          combineAutomatonEnvironment interface left.environment
              right.environment ∈ signature.localEnvironments := by
        rw [hOuter]
        exact hOuterEnvironment
      have hCombinedClock :
          (combineAutomatonEnvironment interface left.environment
              right.environment).clock = false := by
        simp [combineAutomatonEnvironment, hLeftClock]
      exact ⟨
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hLeftClock hLeftImmediate hLeftFuture,
        TypeAlphabet.localEnvironment_mem_of_ordinary_fields_local signature
          interface hInterface hCombinedEnvironment hCombinedClock
          hRightClock hRightImmediate hRightFuture⟩

/-- Synchronization field equations preserve avoidance of every descendant
interface disjoint from the product's own interface. -/
private theorem syncAutomatonEdgeWitnesses_environments_avoid
    (interface childInterface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint interface childInterface)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    left.environment.AvoidsInterface childInterface ∧
      right.environment.AvoidsInterface childInterface := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨_, _, hFields, _⟩
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      exact ⟨TypeEnvironment.tock_avoidsInterface childInterface,
        TypeEnvironment.tock_avoidsInterface childInterface⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      have hCombinedAvoids :
          (combineAutomatonEnvironment interface left.environment
              right.environment).AvoidsInterface childInterface := by
        rw [hOuter]
        exact hOuterAvoids
      exact ⟨
        TypeEnvironment.avoidsInterface_of_ordinary_fields hCombinedAvoids
          hDisjoint hLeftImmediate hLeftFuture,
        TypeEnvironment.avoidsInterface_of_ordinary_fields hCombinedAvoids
          hDisjoint hRightImmediate hRightFuture⟩

/-- Exact pending-edge classifier for the synchronized product constructor. -/
private theorem buildParallelAutomaton_mem_edges_iff
    (interface : Interface) (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    edge ∈ (buildParallelAutomaton interface left right).edges ↔
      ∃ leftEdge ∈ resolvedAutomatonEdges left,
        ∃ rightEdge ∈ resolvedAutomatonEdges right,
          syncAutomatonEdges interface (resolvedAutomatonEdges left)
              (resolvedAutomatonEdges right) leftEdge rightEdge ∧
          edge =
            { source := .pair leftEdge.source rightEdge.source
              environment := combineAutomatonEnvironment interface
                leftEdge.environment rightEdge.environment
              label := AutomatonConstructionLabel.combine interface
                leftEdge.label rightEdge.label
              current := hideOffers interface
                (leftEdge.current ∪ rightEdge.current)
              future := .explicit (hideOffers interface
                (leftEdge.future ∪ rightEdge.future))
              target := .pair leftEdge.target rightEdge.target } := by
  classical
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, hSync⟩,
      hEdge⟩
    exact ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hSync, hEdge.symm⟩
  · rintro ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hSync, rfl⟩
    exact ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, hSync⟩, rfl⟩

/-- Exact raw classifier for a synchronized product edge.  Its two component
edges are already resolved before synchronization, so the product future is
explicit and no additional graph-future hypothesis is needed. -/
private theorem buildParallelAutomaton_hasResolvedEdge_iff
    (interface : Interface) (left right : AutomatonFragment)
    (leftSource rightSource leftTarget rightTarget : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    (buildParallelAutomaton interface left right).HasResolvedEdge
        (.pair leftSource rightSource) environment label offers
        (.pair leftTarget rightTarget) ↔
      ∃ leftEdge ∈ resolvedAutomatonEdges left,
        ∃ rightEdge ∈ resolvedAutomatonEdges right,
          leftEdge.source = leftSource ∧ rightEdge.source = rightSource ∧
          syncAutomatonEdges interface (resolvedAutomatonEdges left)
              (resolvedAutomatonEdges right) leftEdge rightEdge ∧
          combineAutomatonEnvironment interface leftEdge.environment
              rightEdge.environment = environment ∧
          AutomatonConstructionLabel.combine interface leftEdge.label
              rightEdge.label = .visible label ∧
          hideOffers interface (leftEdge.current ∪ rightEdge.current) =
              offers.current ∧
          hideOffers interface (leftEdge.future ∪ rightEdge.future) =
              offers.future ∧
          leftEdge.target = leftTarget ∧ rightEdge.target = rightTarget := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with
      ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, hSync⟩, hEdge⟩
    subst edge
    simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
    have hSources := hSource
    have hTargets := hTarget
    injection hSources with hLeftSource hRightSource
    injection hTargets with hLeftTarget hRightTarget
    exact ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge,
      hLeftSource, hRightSource, hSync, hEnvironment, hLabel, hCurrent,
      hFuture, hLeftTarget, hRightTarget⟩
  · rintro ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge,
      hLeftSource, hRightSource, hSync, hEnvironment, hLabel, hCurrent,
      hFuture, hLeftTarget, hRightTarget⟩
    let edge : PendingAutomatonEdge :=
      { source := .pair leftEdge.source rightEdge.source
        environment := combineAutomatonEnvironment interface
          leftEdge.environment rightEdge.environment
        label := AutomatonConstructionLabel.combine interface leftEdge.label
          rightEdge.label
        current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        future := .explicit
          (hideOffers interface (leftEdge.future ∪ rightEdge.future))
        target := .pair leftEdge.target rightEdge.target }
    refine ⟨edge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, hSync⟩, rfl⟩
    · simp [edge, hLeftSource, hRightSource]
    · simpa [edge] using hEnvironment
    · simpa [edge] using hLabel
    · simpa [edge] using hCurrent
    · simpa [edge] using hFuture
    · simp [edge, hLeftTarget, hRightTarget]

/-- Canonical compiler-fragment form of the exact pending product-edge
classifier.  Component futures have already been resolved when the product is
built, while the product edge records their hidden union explicitly. -/
theorem compileTypeFuel_parallel_mem_edges_iff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (edge : PendingAutomatonEdge) :
    edge ∈ (compileTypeFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface)).edges ↔
      ∃ leftEdge ∈ resolvedAutomatonEdges (compileTypeFuel signature
          (typeCompilationFuel left) left),
        ∃ rightEdge ∈ resolvedAutomatonEdges (compileTypeFuel signature
            (typeCompilationFuel right) right),
          syncAutomatonEdges interface
              (resolvedAutomatonEdges (compileTypeFuel signature
                (typeCompilationFuel left) left))
              (resolvedAutomatonEdges (compileTypeFuel signature
                (typeCompilationFuel right) right)) leftEdge rightEdge ∧
          edge =
            { source := .pair leftEdge.source rightEdge.source
              environment := combineAutomatonEnvironment interface
                leftEdge.environment rightEdge.environment
              label := AutomatonConstructionLabel.combine interface
                leftEdge.label rightEdge.label
              current := hideOffers interface
                (leftEdge.current ∪ rightEdge.current)
              future := .explicit (hideOffers interface
                (leftEdge.future ∪ rightEdge.future))
              target := .pair leftEdge.target rightEdge.target } := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface) =
        buildParallelAutomaton interface leftFragment rightFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  simpa only [hLeftStable, hRightStable] using
    (buildParallelAutomaton_mem_edges_iff interface leftFragment rightFragment
      edge)

/-- Canonical compiler-fragment form of the synchronized product classifier. -/
theorem compileTypeFuel_parallel_hasResolvedEdge_iff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (leftSource rightSource leftTarget rightTarget : TypeAutomatonState)
    (environment : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface))
        (.pair leftSource rightSource) environment label offers
        (.pair leftTarget rightTarget) ↔
      ∃ leftEnvironment rightEnvironment leftLabel rightLabel
          leftOffers rightOffers,
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel left) left)
            leftSource leftEnvironment leftLabel leftOffers leftTarget ∧
        AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel right) right)
            rightSource rightEnvironment rightLabel rightOffers rightTarget ∧
        let leftEdge : AutomatonFragmentEdge :=
          { source := leftSource
            environment := leftEnvironment
            label := .visible leftLabel
            current := leftOffers.current
            future := leftOffers.future
            target := leftTarget }
        let rightEdge : AutomatonFragmentEdge :=
          { source := rightSource
            environment := rightEnvironment
            label := .visible rightLabel
            current := rightOffers.current
            future := rightOffers.future
            target := rightTarget }
        syncAutomatonEdges interface
            (resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel left) left))
            (resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel right) right)) leftEdge rightEdge ∧
          combineAutomatonEnvironment interface leftEnvironment
              rightEnvironment = environment ∧
          TypeLabel.combine interface leftLabel rightLabel = label ∧
          hideOffers interface (leftOffers.current ∪ rightOffers.current) =
              offers.current ∧
          hideOffers interface (leftOffers.future ∪ rightOffers.future) =
              offers.future := by
  classical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment =
      compileTypeFuel signature (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment =
      compileTypeFuel signature (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.par left right interface))
          (.par left right interface) =
        buildParallelAutomaton interface leftFragment rightFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  constructor
  · intro hEdge
    rcases (buildParallelAutomaton_hasResolvedEdge_iff interface leftFragment
      rightFragment leftSource rightSource leftTarget rightTarget environment
      label offers).mp hEdge with
      ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hLeftSource, hRightSource,
        hSync, hEnvironment, hLabel, hCurrent, hFuture, hLeftTarget,
        hRightTarget⟩
    cases hLeftLabel : leftEdge.label with
    | «variable» name =>
        simp [AutomatonConstructionLabel.combine, hLeftLabel] at hLabel
    | visible leftLabel =>
        cases hRightLabel : rightEdge.label with
        | «variable» name =>
            simp [AutomatonConstructionLabel.combine, hLeftLabel, hRightLabel]
              at hLabel
        | visible rightLabel =>
            let leftOffers : TypeOfferSummary :=
              { current := leftEdge.current, future := leftEdge.future }
            let rightOffers : TypeOfferSummary :=
              { current := rightEdge.current, future := rightEdge.future }
            have hLeftResolved : AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature (typeCompilationFuel left) left)
                leftSource leftEdge.environment leftLabel leftOffers
                leftTarget := by
              apply (mem_resolvedAutomatonEdges_visible_iff
                (compileTypeFuel signature (typeCompilationFuel left) left)
                leftSource leftTarget leftEdge.environment leftLabel
                leftOffers).mp
              simpa [leftOffers, hLeftStable, hLeftSource, hLeftTarget,
                hLeftLabel] using hLeftEdge
            have hRightResolved : AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature (typeCompilationFuel right) right)
                rightSource rightEdge.environment rightLabel rightOffers
                rightTarget := by
              apply (mem_resolvedAutomatonEdges_visible_iff
                (compileTypeFuel signature (typeCompilationFuel right) right)
                rightSource rightTarget rightEdge.environment rightLabel
                rightOffers).mp
              simpa [rightOffers, hRightStable, hRightSource, hRightTarget,
                hRightLabel] using hRightEdge
            refine ⟨leftEdge.environment, rightEdge.environment, leftLabel,
              rightLabel, leftOffers, rightOffers, hLeftResolved,
              hRightResolved, ?_⟩
            dsimp only
            have hSync' := hSync
            rw [hLeftStable, hRightStable] at hSync'
            refine ⟨?_, hEnvironment, ?_, ?_, ?_⟩
            · have hLeftShape :
                  ({ source := leftSource,
                    environment := leftEdge.environment,
                    label := .visible leftLabel,
                    current := leftEdge.current,
                    future := leftEdge.future,
                    target := leftTarget } : AutomatonFragmentEdge) =
                    leftEdge := by
                  apply AutomatonFragmentEdge.ext <;>
                    simp [hLeftSource, hLeftTarget, hLeftLabel]
              have hRightShape :
                  ({ source := rightSource,
                    environment := rightEdge.environment,
                    label := .visible rightLabel,
                    current := rightEdge.current,
                    future := rightEdge.future,
                    target := rightTarget } : AutomatonFragmentEdge) =
                    rightEdge := by
                  apply AutomatonFragmentEdge.ext <;>
                    simp [hRightSource, hRightTarget, hRightLabel]
              simpa [leftOffers, rightOffers, hLeftShape, hRightShape] using
                hSync'
            · simpa [AutomatonConstructionLabel.combine, hLeftLabel,
                hRightLabel] using hLabel
            · simpa [leftOffers, rightOffers] using hCurrent
            · simpa [leftOffers, rightOffers] using hFuture
  · rintro ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
      leftOffers, rightOffers, hLeftResolved, hRightResolved, hFields⟩
    dsimp only at hFields
    rcases hFields with ⟨hSync, hEnvironment, hLabel, hCurrent, hFuture⟩
    let leftEdge : AutomatonFragmentEdge :=
      { source := leftSource
        environment := leftEnvironment
        label := .visible leftLabel
        current := leftOffers.current
        future := leftOffers.future
        target := leftTarget }
    let rightEdge : AutomatonFragmentEdge :=
      { source := rightSource
        environment := rightEnvironment
        label := .visible rightLabel
        current := rightOffers.current
        future := rightOffers.future
        target := rightTarget }
    have hLeftEdge : leftEdge ∈ resolvedAutomatonEdges leftFragment := by
      rw [hLeftStable]
      exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
        hLeftResolved
    have hRightEdge : rightEdge ∈ resolvedAutomatonEdges rightFragment := by
      rw [hRightStable]
      exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
        hRightResolved
    apply (buildParallelAutomaton_hasResolvedEdge_iff interface leftFragment
      rightFragment leftSource rightSource leftTarget rightTarget environment
      label offers).mpr
    refine ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, rfl, rfl, ?_,
      hEnvironment, ?_, hCurrent, hFuture, rfl, rfl⟩
    · simpa [leftEdge, rightEdge, hLeftStable, hRightStable] using hSync
    · simpa [leftEdge, rightEdge,
        AutomatonConstructionLabel.combine] using hLabel

/-- Independent offer-summary witnesses chosen by a product synchronization
must be semantically realizable at the same related child source whenever
that source also has the visible edge used by the product step.  This is the
precise resolved-edge closure obligation used by the reverse parallel proof;
it deliberately says nothing about an isolated unresolved recursion marker. -/
def CompilationResolvedOfferWitnessCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {actualOffers : TypeOfferSummary} {actualTarget : TypeAutomatonState},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    fragment.HasResolvedEdge state environment label actualOffers
      actualTarget →
    ∀ witness ∈ resolvedAutomatonEdges fragment,
      witness.source = state →
      witness.environment = environment →
      witness.label.semantic = label →
      ∃ target,
        TypeOffers environment residual label target witness.current
          witness.future

/-- Scoped form of resolved sibling-witness realization used by the
admissible structural induction. -/
def CompilationScopedResolvedOfferWitnessCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {actualOffers : TypeOfferSummary} {actualTarget : TypeAutomatonState},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    fragment.HasResolvedEdge state environment label actualOffers
      actualTarget →
    ∀ witness ∈ resolvedAutomatonEdges fragment,
      witness.source = state →
      witness.environment = environment →
      witness.label.semantic = label →
      ∃ target,
        TypeOffers environment residual label target witness.current
          witness.future

/-- Every visible resolved edge leaving a represented source reaches another
represented residual.  Dead endpoints of unresolved variable markers are
intentionally outside this invariant. -/
def CompilationResolvedEdgeTargetsRelated
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {source : TypeAutomatonState} {residual : PactType}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState},
    TypeCompilationRelation processType source residual →
    fragment.HasResolvedEdge source environment label offers target →
    ∃ targetResidual,
      TypeCompilationRelation processType target targetResidual

/-- Every resolved edge of an exclusive offer reaches a represented
residual, assuming the corresponding property for its compiled children. -/
theorem CompilationResolvedEdgeTargetsRelated_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType)
    (hBranchTargets : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationResolvedEdgeTargetsRelated signature branchType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | xoffer_source =>
      rw [hFragment] at hEdge
      rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment branchAutomata environment label
        offers target).mp hEdge with hBranch | hWait | hElse
      · rcases hBranch with ⟨indexed, hIndexed, _, _, _, _, _, _,
          hTarget⟩
        have hIndexedFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
          at hIndexedFields
        rcases hIndexedFields with ⟨hBound, hValue⟩
        have hBranchBound : indexed.2 < branches.length := by
          simpa [branchAutomata] using hBound
        let branch := branches[indexed.2]
        have hEntry : branches[indexed.2]? = some branch := by
          rw [List.getElem?_eq_getElem hBranchBound]
        have hIndexedValue : indexed.1 =
            (branch.1, compileTypeFuel signature fuel branch.2) := by
          rw [hValue]
          simp [branchAutomata, branch]
        rw [hIndexedValue] at hTarget
        subst target
        have hBranchMember : branch ∈ branches :=
          List.getElem_mem hBranchBound
        have hBranchFuel :
            TypeCompilationFuelSufficient branch.2 fuel := by
          exact le_trans
            (typeCompilationFuel_le_typeBranchCompilationFuel branches
              branch hBranchMember)
            (by simp [fuel])
        have hInitial : TypeCompilationRelation branch.2
            (compileTypeFuel signature fuel branch.2).initial branch.2 :=
          compileTypeFuel_initial_relation signature fuel branch.2 hBranchFuel
        exact ⟨branch.2,
          TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
            branches branch.1 indexed.2 _ hEntry hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.xoffer elseType branches,
          TypeCompilationRelation.xoffer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.xoffer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_xoffer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
        elseType branches action branchType index hEntry hEdge with
        ⟨childTarget, rfl, hChildEdge⟩
      have hTargets : CompilationResolvedEdgeTargetsRelated signature
          branchType := hBranchTargets action branchType index hEntry
      rcases hTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_branch elseType branchType
          targetResidual branches action index childTarget hEntry
          hTargetRelated⟩

/-- Every resolved edge of a conjunctive offer reaches a represented
residual, assuming the corresponding property for its two compiled children. -/
theorem CompilationResolvedEdgeTargetsRelated_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionTargets : CompilationResolvedEdgeTargetsRelated signature
      (parallelTypeBranches branches))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.offer elseType branches) := by
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | offer_source =>
      rw [hFragment] at hEdge
      rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment conjunction environment label offers
        target).mp hEdge with hEnabled | hWait | hElse
      · rcases hEnabled with ⟨_, _, _, _, _, hTarget⟩
        subst target
        have hConjunctionFuel :
            TypeCompilationFuelSufficient conjunctionType fuel := by
          rw [TypeCompilationFuelSufficient,
            typeCompilationFuel_parallelTypeBranches]
          simp [fuel]
        have hInitial : TypeCompilationRelation conjunctionType
            conjunction.initial conjunctionType :=
          compileTypeFuel_initial_relation signature fuel conjunctionType
            hConjunctionFuel
        exact ⟨conjunctionType,
          TypeCompilationRelation.offer_branches elseType conjunctionType
            branches conjunction.initial hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.offer elseType branches,
          TypeCompilationRelation.offer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.offer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
        elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hConjunctionTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_branches elseType targetResidual
          branches childTarget hTargetRelated⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_else elseType targetResidual branches
          childTarget hTargetRelated⟩

private theorem resolvedAutomatonEdge_label_visible_of_pendingEdgesVisible
    (fragment : AutomatonFragment)
    (hVisible : ∀ edge ∈ fragment.edges,
      ∃ label, edge.label = .visible label)
    {edge : AutomatonFragmentEdge}
    (hEdge : edge ∈ resolvedAutomatonEdges fragment) :
    ∃ label, edge.label = .visible label := by
  classical
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨pending, hPending, hResolved⟩
  obtain ⟨label, hLabel⟩ := hVisible pending hPending
  refine ⟨label, ?_⟩
  have hResolvedLabel := congrArg AutomatonFragmentEdge.label hResolved
  simpa [hLabel] using hResolvedLabel.symm

/-- Visible-edge target totality plus raw step correctness realizes every
resolved synchronization witness.  These are the two logically independent
facts hidden by the informal phrase "the child edge alphabet is closed". -/
theorem compilationResolvedOfferWitnessCorrect_of_step_targets_visible
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationFragmentStepCorrect signature processType)
    (hTargets : CompilationResolvedEdgeTargetsRelated signature processType)
    (hVisible : CompilationPendingEdgesVisible signature processType) :
    CompilationResolvedOfferWitnessCorrect signature processType := by
  intro residual state environment label actualOffers actualTarget hRelated
    hLocalEnvironment hActualEdge witness hWitness hSource hEnvironment hLabel
  obtain ⟨witnessLabel, hWitnessLabel⟩ :=
    resolvedAutomatonEdge_label_visible_of_pendingEdgesVisible _ hVisible
      hWitness
  have hSemanticLabel : witnessLabel = label := by
    have hSemantic := hLabel
    rw [hWitnessLabel] at hSemantic
    simpa [AutomatonConstructionLabel.semantic] using hSemantic
  let witnessOffers : TypeOfferSummary :=
    { current := witness.current, future := witness.future }
  have hWitnessResolved : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel processType) processType)
      state environment label witnessOffers witness.target := by
    apply (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mp
    have hWitnessShape :
        ({ source := state, environment := environment,
          label := .visible label, current := witness.current,
          future := witness.future, target := witness.target } :
          AutomatonFragmentEdge) = witness := by
      apply AutomatonFragmentEdge.ext <;>
        simp [hSource, hEnvironment, hWitnessLabel, hSemanticLabel]
    simpa only [witnessOffers, hWitnessShape] using hWitness
  obtain ⟨targetResidual, hTargetRelated⟩ :=
    hTargets hRelated hWitnessResolved
  have hDecorated := (hStep hRelated hLocalEnvironment).mpr
    ⟨witness.target, hWitnessResolved, hTargetRelated⟩
  exact ⟨targetResidual, hDecorated.2⟩

/-- Raw step correspondence on the exact domain of one parallel node: a
construction-local environment whose actions avoid that node's hidden
interface.  This domain is stable under lexically disjoint nested interfaces. -/
def CompilationParallelFragmentStepCorrect
    (signature : TypeAlphabet) (interface : Interface)
    (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface interface →
    (DecoratedTypeTransition environment residual label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge state environment label offers target ∧
        TypeCompilationRelation processType target residual')

/-- Induction-friendly raw correspondence domain.  The environment avoids all
parallel interfaces syntactically nested in the current residual fragment. -/
def CompilationScopedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    (DecoratedTypeTransition environment residual label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge state environment label offers target ∧
        TypeCompilationRelation processType target residual')

theorem compilationScopedFragmentStepCorrect_of_fragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationFragmentStepCorrect signature processType) :
    CompilationScopedFragmentStepCorrect signature processType := by
  intro residual residual' state environment label offers hRelated
    hEnvironment hAvoids
  exact hStep hRelated hEnvironment

theorem compilationScopedResolvedOfferWitnessCorrect_of_step_targets_visible
    (signature : TypeAlphabet) (processType : PactType)
    (hStep : CompilationScopedFragmentStepCorrect signature processType)
    (hTargets : CompilationResolvedEdgeTargetsRelated signature processType)
    (hVisible : CompilationPendingEdgesVisible signature processType) :
    CompilationScopedResolvedOfferWitnessCorrect signature processType := by
  intro residual state environment label actualOffers actualTarget hRelated
    hLocalEnvironment hAvoids hActualEdge witness hWitness hSource
    hEnvironment hLabel
  obtain ⟨witnessLabel, hWitnessLabel⟩ :=
    resolvedAutomatonEdge_label_visible_of_pendingEdgesVisible _ hVisible
      hWitness
  have hSemanticLabel : witnessLabel = label := by
    have hSemantic := hLabel
    rw [hWitnessLabel] at hSemantic
    simpa [AutomatonConstructionLabel.semantic] using hSemantic
  let witnessOffers : TypeOfferSummary :=
    { current := witness.current, future := witness.future }
  have hWitnessResolved : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature (typeCompilationFuel processType) processType)
      state environment label witnessOffers witness.target := by
    apply (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mp
    have hWitnessShape :
        ({ source := state, environment := environment,
          label := .visible label, current := witness.current,
          future := witness.future, target := witness.target } :
          AutomatonFragmentEdge) = witness := by
      apply AutomatonFragmentEdge.ext <;>
        simp [hSource, hEnvironment, hWitnessLabel, hSemanticLabel]
    simpa only [witnessOffers, hWitnessShape] using hWitness
  obtain ⟨targetResidual, hTargetRelated⟩ :=
    hTargets hRelated hWitnessResolved
  have hDecorated := (hStep hRelated hLocalEnvironment hAvoids).mpr
    ⟨witness.target, hWitnessResolved, hTargetRelated⟩
  exact ⟨targetResidual, hDecorated.2⟩

/-- A scoped raw theorem yields the public fixed-alphabet theorem whenever
all nested interfaces are declared by the signature. -/
theorem compilationStepCorrect_of_scopedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hAlphabet : signature.WellFormed)
    (hInterfaces : processType.ParallelInterfaces ⊆ signature.interface)
    (hStep : CompilationScopedFragmentStepCorrect signature processType) :
    CompilationStepCorrect signature processType := by
  intro residual residual' state environment label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk environment label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFields : environment ∈ signature.environments ∧
      label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
    simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
  have hRaw := hStep (residual := residual) (residual' := residual')
    (state := state) (environment := environment) (label := label)
    (offers := offers) hRelated
    (signature.environments_subset_localEnvironments hFields.1)
    (signature.environment_avoids_subinterface hAlphabet hFields.1
      hInterfaces)
  constructor
  · intro hSemantic
    rcases hRaw.mp hSemantic with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType state
        target environment label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType state
        target environment label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-- Raw step correspondence restricted to exported environments.  Parallel
products need exactly this domain: their outer environment is exported, while
the synchronization equations construct local environments for both children. -/
def CompilationExportedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.environments →
    (DecoratedTypeTransition environment residual label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge state environment label offers target ∧
        TypeCompilationRelation processType target residual')

private theorem TypeOffers.parallel_fields
    {outer : TypeEnvironment} {left right target : PactType}
    {interface : Interface} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers outer (.par left right interface) label target
      current future) :
    ∃ leftEnvironment rightEnvironment leftTarget rightTarget
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture,
      target = .par leftTarget rightTarget interface ∧
      label = TypeLabel.combine interface leftLabel rightLabel ∧
      hideTypeOffers interface (leftCurrent ∪ rightCurrent) = current ∧
      hideTypeOffers interface (leftFuture ∪ rightFuture) = future ∧
      TypeOffers leftEnvironment left leftLabel leftTarget leftCurrent
        leftFuture ∧
      TypeOffers rightEnvironment right rightLabel rightTarget rightCurrent
        rightFuture ∧
      LocalTypeEnvironment outer interface rightEnvironment right rightLabel
        leftEnvironment ∧
      LocalTypeEnvironment outer interface leftEnvironment left leftLabel
        rightEnvironment ∧
      outer.WellFormed ∧ TypeLabel.Sync interface leftLabel rightLabel := by
  cases hOffers with
  | par outer leftEnvironment rightEnvironment interface left leftTarget right
      rightTarget leftLabel rightLabel leftCurrent leftFuture rightCurrent
      rightFuture hLeftOffers hRightOffers hLeftLocal hRightLocal hFields =>
      exact ⟨leftEnvironment, rightEnvironment, leftTarget, rightTarget,
        leftLabel, rightLabel, leftCurrent, leftFuture, rightCurrent,
        rightFuture, rfl, rfl, rfl, rfl, hLeftOffers, hRightOffers,
        hLeftLocal, hRightLocal, hFields⟩

private theorem compileTypeFuel_parallel_resolvedEdge_target_pair
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    {leftSource rightSource target : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (compileTypeFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface))
      (.pair leftSource rightSource) environment label offers target) :
    ∃ leftTarget rightTarget, target = .pair leftTarget rightTarget := by
  rcases hEdge with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (compileTypeFuel_parallel_mem_edges_iff signature left right
      interface pending).mp hPending with
    ⟨leftEdge, hLeftEdge, rightEdge, hRightEdge, hSync, hPending⟩
  subst pending
  exact ⟨leftEdge.target, rightEdge.target, hTarget.symm⟩

/-- Visible-edge target relatedness composes pointwise through the product
state relation. -/
theorem compilationResolvedEdgeTargetsRelated_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature
      (.par left right interface) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftSource rightSource
      hLeftRelated hRightRelated =>
      obtain ⟨leftTarget, rightTarget, rfl⟩ :=
        compileTypeFuel_parallel_resolvedEdge_target_pair signature left right
          interface hEdge
      rcases (compileTypeFuel_parallel_hasResolvedEdge_iff signature left right
          interface leftSource rightSource leftTarget rightTarget environment
          label offers).mp hEdge with
        ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
          leftOffers, rightOffers, hLeftEdge, hRightEdge, hFields⟩
      obtain ⟨leftTargetResidual, hLeftTargetRelated⟩ :=
        hLeftTargets hLeftRelated hLeftEdge
      obtain ⟨rightTargetResidual, hRightTargetRelated⟩ :=
        hRightTargets hRightRelated hRightEdge
      exact ⟨.par leftTargetResidual rightTargetResidual interface,
        TypeCompilationRelation.parallel left right leftTargetResidual
          rightTargetResidual interface leftTarget rightTarget
          hLeftTargetRelated hRightTargetRelated⟩

/-- Parallel preserves raw correspondence throughout its exact local domain.
The children are invoked only at the local environments reconstructed from
the two semantic/synchronized sibling judgments. -/
theorem compilationParallelFragmentStepCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hLeftWitness : CompilationResolvedOfferWitnessCorrect signature left)
    (hRightWitness : CompilationResolvedOfferWitnessCorrect signature right) :
    CompilationParallelFragmentStepCorrect signature interface
      (.par left right interface) := by
  intro residual residual' state environment label offers hRelated
    hOuterEnvironment hOuterAvoids
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      constructor
      · rintro ⟨_, hOffers⟩
        obtain ⟨leftEnvironment, rightEnvironment, leftTarget, rightTarget,
            leftLabel, rightLabel, leftCurrent, leftFuture, rightCurrent,
            rightFuture, hTarget, hLabel, hCurrent, hFuture, hLeftOffers,
            hRightOffers, hLeftLocal, hRightLocal, hOuterWellFormed,
            hLabelSync⟩ := TypeOffers.parallel_fields hOffers
        have hLeftLocalEnvironment :
            leftEnvironment ∈ signature.localEnvironments :=
          TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local signature
            interface hInterface hOuterEnvironment hLeftLocal
        have hRightLocalEnvironment :
            rightEnvironment ∈ signature.localEnvironments :=
          TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local signature
            interface hInterface hOuterEnvironment hRightLocal
        rcases (hLeftStep (residual' := leftTarget) (label := leftLabel)
            (offers := { current := leftCurrent, future := leftFuture })
            hLeftRelated hLeftLocalEnvironment).mp
            ⟨TypeOffers.to_transition hLeftOffers, hLeftOffers⟩ with
          ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩
        rcases (hRightStep (residual' := rightTarget) (label := rightLabel)
            (offers := { current := rightCurrent, future := rightFuture })
            hRightRelated hRightLocalEnvironment).mp
            ⟨TypeOffers.to_transition hRightOffers, hRightOffers⟩ with
          ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩
        let leftSummary : TypeOfferSummary :=
          { current := leftCurrent, future := leftFuture }
        let rightSummary : TypeOfferSummary :=
          { current := rightCurrent, future := rightFuture }
        let leftAutomatonEdge : AutomatonFragmentEdge :=
          { source := leftState
            environment := leftEnvironment
            label := .visible leftLabel
            current := leftCurrent
            future := leftFuture
            target := leftTargetState }
        let rightAutomatonEdge : AutomatonFragmentEdge :=
          { source := rightState
            environment := rightEnvironment
            label := .visible rightLabel
            current := rightCurrent
            future := rightFuture
            target := rightTargetState }
        have hLeftEdgeMember : leftAutomatonEdge ∈
            resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel left) left) := by
          exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hLeftEdge
        have hRightEdgeMember : rightAutomatonEdge ∈
            resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel right) right) := by
          exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hRightEdge
        have hLeftRealizes :
            ∀ {target current future},
              TypeOffers leftEnvironment leftResidual leftLabel target
                  current future →
              ∃ witness ∈ resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel left) left),
                matchesAutomatonOfferWitness leftAutomatonEdge witness ∧
                  witness.current = current ∧ witness.future = future := by
          intro target current future hSiblingOffers
          rcases (hLeftStep (residual' := target) (label := leftLabel)
              (offers := { current := current, future := future })
              hLeftRelated hLeftLocalEnvironment).mp
              ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
            ⟨targetState, hResolved, hTargetRelated⟩
          let witness : AutomatonFragmentEdge :=
            { source := leftState
              environment := leftEnvironment
              label := .visible leftLabel
              current := current
              future := future
              target := targetState }
          refine ⟨witness, ?_, ?_, rfl, rfl⟩
          · exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
              hResolved
          · simp [matchesAutomatonOfferWitness, leftAutomatonEdge, witness,
              AutomatonConstructionLabel.semantic]
        have hRightRealizes :
            ∀ {target current future},
              TypeOffers rightEnvironment rightResidual rightLabel target
                  current future →
              ∃ witness ∈ resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel right) right),
                matchesAutomatonOfferWitness rightAutomatonEdge witness ∧
                  witness.current = current ∧ witness.future = future := by
          intro target current future hSiblingOffers
          rcases (hRightStep (residual' := target) (label := rightLabel)
              (offers := { current := current, future := future })
              hRightRelated hRightLocalEnvironment).mp
              ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
            ⟨targetState, hResolved, hTargetRelated⟩
          let witness : AutomatonFragmentEdge :=
            { source := rightState
              environment := rightEnvironment
              label := .visible rightLabel
              current := current
              future := future
              target := targetState }
          refine ⟨witness, ?_, ?_, rfl, rfl⟩
          · exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
              hResolved
          · simp [matchesAutomatonOfferWitness, rightAutomatonEdge, witness,
              AutomatonConstructionLabel.semantic]
        obtain ⟨hSynchronized, hCombinedEnvironment⟩ :=
          localTypeEnvironments_to_syncAutomatonEdges_local signature interface
            hInterface hOuterEnvironment hOuterAvoids hLeftEdgeMember
            hRightEdgeMember hLeftLocal hRightLocal hLeftRealizes
            hRightRealizes hLabelSync
        refine ⟨.pair leftTargetState rightTargetState, ?_, ?_⟩
        · apply (compileTypeFuel_parallel_hasResolvedEdge_iff signature left
            right interface leftState rightState leftTargetState
            rightTargetState environment label
            { current := current, future := future }).mpr
          refine ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
            leftSummary, rightSummary, hLeftEdge, hRightEdge, ?_⟩
          dsimp only
          refine ⟨?_, hCombinedEnvironment, hLabel.symm, ?_, ?_⟩
          · simpa [leftAutomatonEdge, rightAutomatonEdge, leftSummary,
              rightSummary] using hSynchronized
          · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
              using hCurrent
          · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
              using hFuture
        · rw [hTarget]
          exact TypeCompilationRelation.parallel left right leftTarget
            rightTarget interface leftTargetState rightTargetState
            hLeftTargetRelated hRightTargetRelated
      · rintro ⟨targetState, hEdge, hTargetRelated⟩
        cases hTargetRelated with
        | parallel _ _ leftTarget rightTarget _ leftTargetState
            rightTargetState hLeftTargetRelated hRightTargetRelated =>
            rcases (compileTypeFuel_parallel_hasResolvedEdge_iff signature
                left right interface leftState rightState leftTargetState
                rightTargetState environment label
                { current := current, future := future }).mp hEdge with
              ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
                leftSummary, rightSummary, hLeftEdge, hRightEdge,
                hSynchronized, hCombinedEnvironment, hLabel, hCurrent,
                hFuture⟩
            let leftAutomatonEdge : AutomatonFragmentEdge :=
              { source := leftState
                environment := leftEnvironment
                label := .visible leftLabel
                current := leftSummary.current
                future := leftSummary.future
                target := leftTargetState }
            let rightAutomatonEdge : AutomatonFragmentEdge :=
              { source := rightState
                environment := rightEnvironment
                label := .visible rightLabel
                current := rightSummary.current
                future := rightSummary.future
                target := rightTargetState }
            change syncAutomatonEdges interface
                (resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel left) left))
                (resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                leftAutomatonEdge rightAutomatonEdge at hSynchronized
            rcases hSynchronized with ⟨leftWitnessEdge, hLeftWitnessEdge,
              rightWitnessEdge, hRightWitnessEdge, hWitnessSync⟩
            have hLocalEnvironments :=
              TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses_local
                signature interface hInterface hOuterEnvironment
                hCombinedEnvironment hWitnessSync
            rcases (hLeftStep hLeftRelated hLocalEnvironments.1).mpr
                ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩ with
              ⟨hLeftTransition, hLeftOffers⟩
            rcases (hRightStep hRightRelated hLocalEnvironments.2).mpr
                ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩ with
              ⟨hRightTransition, hRightOffers⟩
            have hWitnessFields := hWitnessSync
            unfold syncAutomatonEdgeWitnesses at hWitnessFields
            rcases hWitnessFields with ⟨hLeftMatch, hRightMatch, hFields,
              hLabelSyncRaw⟩
            obtain ⟨leftWitnessTarget, hLeftWitnessOffers⟩ :=
              hLeftWitness hLeftRelated hLocalEnvironments.1 hLeftEdge
                leftWitnessEdge hLeftWitnessEdge hLeftMatch.1 hLeftMatch.2.1
                hLeftMatch.2.2
            obtain ⟨rightWitnessTarget, hRightWitnessOffers⟩ :=
              hRightWitness hRightRelated hLocalEnvironments.2 hRightEdge
                rightWitnessEdge hRightWitnessEdge hRightMatch.1
                hRightMatch.2.1 hRightMatch.2.2
            have hLeftWitnessOffers' : TypeOffers leftWitnessEdge.environment
                leftResidual leftWitnessEdge.label.semantic leftWitnessTarget
                leftWitnessEdge.current leftWitnessEdge.future := by
              rw [hLeftMatch.2.1, hLeftMatch.2.2]
              exact hLeftWitnessOffers
            have hRightWitnessOffers' : TypeOffers rightWitnessEdge.environment
                rightResidual rightWitnessEdge.label.semantic
                rightWitnessTarget rightWitnessEdge.current
                rightWitnessEdge.future := by
              rw [hRightMatch.2.1, hRightMatch.2.2]
              exact hRightWitnessOffers
            have hSemanticLocals :=
              syncAutomatonEdgeWitnesses_to_localTypeEnvironments interface
                hLeftWitnessOffers' hRightWitnessOffers' hWitnessSync
            dsimp only at hSemanticLocals
            have hSemanticLocals' :
                LocalTypeEnvironment environment interface rightEnvironment
                    rightResidual rightLabel leftEnvironment ∧
                  LocalTypeEnvironment environment interface leftEnvironment
                    leftResidual leftLabel rightEnvironment := by
              simpa [leftAutomatonEdge, rightAutomatonEdge,
                hCombinedEnvironment] using hSemanticLocals
            have hLabelSync : TypeLabel.Sync interface leftLabel rightLabel := by
              simpa [leftAutomatonEdge, rightAutomatonEdge,
                AutomatonConstructionLabel.semantic] using hLabelSyncRaw
            have hEnvironmentWellFormed : environment.WellFormed :=
              signature.localEnvironment_wellFormed hOuterEnvironment
            have hParentTransition := TypeTransition.par environment
              leftEnvironment rightEnvironment interface leftResidual
              leftTarget rightResidual rightTarget leftLabel rightLabel
              hLeftTransition hRightTransition
              ⟨hEnvironmentWellFormed, hSemanticLocals'.1,
                hSemanticLocals'.2, hLabelSync⟩
            have hParentOffers := TypeOffers.par environment leftEnvironment
              rightEnvironment interface leftResidual leftTarget rightResidual
              rightTarget leftLabel rightLabel leftSummary.current
              leftSummary.future rightSummary.current rightSummary.future
              hLeftOffers hRightOffers hSemanticLocals'.1 hSemanticLocals'.2
              ⟨hEnvironmentWellFormed, hLabelSync⟩
            rw [← hLabel, ← hCurrent, ← hFuture]
            simpa [hideOffers, hideTypeOffers] using
              And.intro hParentTransition hParentOffers

/-- Interface-scoped parallel composition.  This is the form consumed by the
admissible-type induction: ancestor-injected offers lie on an interface
disjoint from every descendant product interface. -/
theorem compilationScopedFragmentStepCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hScoped : PactType.InterfaceScoped
      (PactType.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    (hLeftWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature left)
    (hRightWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature right) :
    CompilationScopedFragmentStepCorrect signature
      (PactType.par left right interface) := by
  have hScopedFields := PactType.interfaceScoped_parallel_fields hScoped
  have hDisjointLeft : Disjoint interface left.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hLeftMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_left _ hLeftMessage)
  have hDisjointRight : Disjoint interface right.ParallelInterfaces := by
    rw [Finset.disjoint_left] at hScopedFields ⊢
    intro message hInterfaceMessage hRightMessage
    exact hScopedFields.1 hInterfaceMessage
      (Finset.mem_union_right _ hRightMessage)
  have hInterfaceSubset : interface ⊆
      (.par left right interface).ParallelInterfaces := by
    simp [PactType.ParallelInterfaces]
  have hLeftSubset : left.ParallelInterfaces ⊆
      (.par left right interface).ParallelInterfaces := by
    simp [PactType.ParallelInterfaces]
  have hRightSubset : right.ParallelInterfaces ⊆
      (.par left right interface).ParallelInterfaces := by
    simp [PactType.ParallelInterfaces]
  intro residual residual' state environment label offers hRelated
    hOuterEnvironment hOuterAvoids
  rcases offers with ⟨current, future⟩
  have hOuterAvoidsInterface := hOuterAvoids.mono hInterfaceSubset
  have hOuterAvoidsLeft := hOuterAvoids.mono hLeftSubset
  have hOuterAvoidsRight := hOuterAvoids.mono hRightSubset
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftState rightState
      hLeftRelated hRightRelated =>
      constructor
      · rintro ⟨_, hOffers⟩
        obtain ⟨leftEnvironment, rightEnvironment, leftTarget, rightTarget,
            leftLabel, rightLabel, leftCurrent, leftFuture, rightCurrent,
            rightFuture, hTarget, hLabel, hCurrent, hFuture, hLeftOffers,
            hRightOffers, hLeftLocal, hRightLocal, hOuterWellFormed,
            hLabelSync⟩ := TypeOffers.parallel_fields hOffers
        have hLeftLocalEnvironment :
            leftEnvironment ∈ signature.localEnvironments :=
          TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
            signature interface hInterface hOuterEnvironment hLeftLocal
        have hRightLocalEnvironment :
            rightEnvironment ∈ signature.localEnvironments :=
          TypeAlphabet.localEnvironment_mem_of_localTypeEnvironment_local
            signature interface hInterface hOuterEnvironment hRightLocal
        have hLeftAvoids :
            leftEnvironment.AvoidsInterface left.ParallelInterfaces :=
          hLeftLocal.avoidsInterface_of_disjoint hOuterAvoidsLeft
            hDisjointLeft
        have hRightAvoids :
            rightEnvironment.AvoidsInterface right.ParallelInterfaces :=
          hRightLocal.avoidsInterface_of_disjoint hOuterAvoidsRight
            hDisjointRight
        rcases (hLeftStep (residual' := leftTarget) (label := leftLabel)
            (offers := { current := leftCurrent, future := leftFuture })
            hLeftRelated hLeftLocalEnvironment hLeftAvoids).mp
            ⟨TypeOffers.to_transition hLeftOffers, hLeftOffers⟩ with
          ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩
        rcases (hRightStep (residual' := rightTarget) (label := rightLabel)
            (offers := { current := rightCurrent, future := rightFuture })
            hRightRelated hRightLocalEnvironment hRightAvoids).mp
            ⟨TypeOffers.to_transition hRightOffers, hRightOffers⟩ with
          ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩
        let leftSummary : TypeOfferSummary :=
          { current := leftCurrent, future := leftFuture }
        let rightSummary : TypeOfferSummary :=
          { current := rightCurrent, future := rightFuture }
        let leftAutomatonEdge : AutomatonFragmentEdge :=
          { source := leftState
            environment := leftEnvironment
            label := .visible leftLabel
            current := leftCurrent
            future := leftFuture
            target := leftTargetState }
        let rightAutomatonEdge : AutomatonFragmentEdge :=
          { source := rightState
            environment := rightEnvironment
            label := .visible rightLabel
            current := rightCurrent
            future := rightFuture
            target := rightTargetState }
        have hLeftEdgeMember : leftAutomatonEdge ∈
            resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel left) left) := by
          exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hLeftEdge
        have hRightEdgeMember : rightAutomatonEdge ∈
            resolvedAutomatonEdges (compileTypeFuel signature
              (typeCompilationFuel right) right) := by
          exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
            hRightEdge
        have hLeftRealizes :
            ∀ {target current future},
              TypeOffers leftEnvironment leftResidual leftLabel target
                  current future →
              ∃ witness ∈ resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel left) left),
                matchesAutomatonOfferWitness leftAutomatonEdge witness ∧
                  witness.current = current ∧ witness.future = future := by
          intro target current future hSiblingOffers
          rcases (hLeftStep (residual' := target) (label := leftLabel)
              (offers := { current := current, future := future })
              hLeftRelated hLeftLocalEnvironment hLeftAvoids).mp
              ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
            ⟨targetState, hResolved, hTargetRelated⟩
          let witness : AutomatonFragmentEdge :=
            { source := leftState
              environment := leftEnvironment
              label := .visible leftLabel
              current := current
              future := future
              target := targetState }
          refine ⟨witness, ?_, ?_, rfl, rfl⟩
          · exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
              hResolved
          · simp [matchesAutomatonOfferWitness, leftAutomatonEdge, witness,
              AutomatonConstructionLabel.semantic]
        have hRightRealizes :
            ∀ {target current future},
              TypeOffers rightEnvironment rightResidual rightLabel target
                  current future →
              ∃ witness ∈ resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel right) right),
                matchesAutomatonOfferWitness rightAutomatonEdge witness ∧
                  witness.current = current ∧ witness.future = future := by
          intro target current future hSiblingOffers
          rcases (hRightStep (residual' := target) (label := rightLabel)
              (offers := { current := current, future := future })
              hRightRelated hRightLocalEnvironment hRightAvoids).mp
              ⟨TypeOffers.to_transition hSiblingOffers, hSiblingOffers⟩ with
            ⟨targetState, hResolved, hTargetRelated⟩
          let witness : AutomatonFragmentEdge :=
            { source := rightState
              environment := rightEnvironment
              label := .visible rightLabel
              current := current
              future := future
              target := targetState }
          refine ⟨witness, ?_, ?_, rfl, rfl⟩
          · exact (mem_resolvedAutomatonEdges_visible_iff _ _ _ _ _ _).mpr
              hResolved
          · simp [matchesAutomatonOfferWitness, rightAutomatonEdge, witness,
              AutomatonConstructionLabel.semantic]
        obtain ⟨hSynchronized, hCombinedEnvironment⟩ :=
          localTypeEnvironments_to_syncAutomatonEdges_local signature interface
            hInterface hOuterEnvironment hOuterAvoidsInterface hLeftEdgeMember
            hRightEdgeMember hLeftLocal hRightLocal hLeftRealizes
            hRightRealizes hLabelSync
        refine ⟨.pair leftTargetState rightTargetState, ?_, ?_⟩
        · apply (compileTypeFuel_parallel_hasResolvedEdge_iff signature left
            right interface leftState rightState leftTargetState
            rightTargetState environment label
            { current := current, future := future }).mpr
          refine ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
            leftSummary, rightSummary, hLeftEdge, hRightEdge, ?_⟩
          dsimp only
          refine ⟨?_, hCombinedEnvironment, hLabel.symm, ?_, ?_⟩
          · simpa [leftAutomatonEdge, rightAutomatonEdge, leftSummary,
              rightSummary] using hSynchronized
          · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
              using hCurrent
          · simpa [leftSummary, rightSummary, hideOffers, hideTypeOffers]
              using hFuture
        · rw [hTarget]
          exact TypeCompilationRelation.parallel left right leftTarget
            rightTarget interface leftTargetState rightTargetState
            hLeftTargetRelated hRightTargetRelated
      · rintro ⟨targetState, hEdge, hTargetRelated⟩
        cases hTargetRelated with
        | parallel _ _ leftTarget rightTarget _ leftTargetState
            rightTargetState hLeftTargetRelated hRightTargetRelated =>
            rcases (compileTypeFuel_parallel_hasResolvedEdge_iff signature
                left right interface leftState rightState leftTargetState
                rightTargetState environment label
                { current := current, future := future }).mp hEdge with
              ⟨leftEnvironment, rightEnvironment, leftLabel, rightLabel,
                leftSummary, rightSummary, hLeftEdge, hRightEdge,
                hSynchronized, hCombinedEnvironment, hLabel, hCurrent,
                hFuture⟩
            let leftAutomatonEdge : AutomatonFragmentEdge :=
              { source := leftState
                environment := leftEnvironment
                label := .visible leftLabel
                current := leftSummary.current
                future := leftSummary.future
                target := leftTargetState }
            let rightAutomatonEdge : AutomatonFragmentEdge :=
              { source := rightState
                environment := rightEnvironment
                label := .visible rightLabel
                current := rightSummary.current
                future := rightSummary.future
                target := rightTargetState }
            change syncAutomatonEdges interface
                (resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel left) left))
                (resolvedAutomatonEdges (compileTypeFuel signature
                  (typeCompilationFuel right) right))
                leftAutomatonEdge rightAutomatonEdge at hSynchronized
            rcases hSynchronized with ⟨leftWitnessEdge, hLeftWitnessEdge,
              rightWitnessEdge, hRightWitnessEdge, hWitnessSync⟩
            have hLocalEnvironments :=
              TypeAlphabet.localEnvironments_of_syncAutomatonEdgeWitnesses_local
                signature interface hInterface hOuterEnvironment
                hCombinedEnvironment hWitnessSync
            have hLeftAvoidsPair :=
              syncAutomatonEdgeWitnesses_environments_avoid interface
                left.ParallelInterfaces hCombinedEnvironment hOuterAvoidsLeft
                hDisjointLeft hWitnessSync
            have hRightAvoidsPair :=
              syncAutomatonEdgeWitnesses_environments_avoid interface
                right.ParallelInterfaces hCombinedEnvironment hOuterAvoidsRight
                hDisjointRight hWitnessSync
            rcases (hLeftStep hLeftRelated hLocalEnvironments.1
                hLeftAvoidsPair.1).mpr
                ⟨leftTargetState, hLeftEdge, hLeftTargetRelated⟩ with
              ⟨hLeftTransition, hLeftOffers⟩
            rcases (hRightStep hRightRelated hLocalEnvironments.2
                hRightAvoidsPair.2).mpr
                ⟨rightTargetState, hRightEdge, hRightTargetRelated⟩ with
              ⟨hRightTransition, hRightOffers⟩
            have hWitnessFields := hWitnessSync
            unfold syncAutomatonEdgeWitnesses at hWitnessFields
            rcases hWitnessFields with ⟨hLeftMatch, hRightMatch, hFields,
              hLabelSyncRaw⟩
            obtain ⟨leftWitnessTarget, hLeftWitnessOffers⟩ :=
              hLeftWitness hLeftRelated hLocalEnvironments.1
                hLeftAvoidsPair.1 hLeftEdge leftWitnessEdge hLeftWitnessEdge
                hLeftMatch.1 hLeftMatch.2.1 hLeftMatch.2.2
            obtain ⟨rightWitnessTarget, hRightWitnessOffers⟩ :=
              hRightWitness hRightRelated hLocalEnvironments.2
                hRightAvoidsPair.2 hRightEdge rightWitnessEdge
                hRightWitnessEdge hRightMatch.1 hRightMatch.2.1
                hRightMatch.2.2
            have hLeftWitnessOffers' : TypeOffers leftWitnessEdge.environment
                leftResidual leftWitnessEdge.label.semantic leftWitnessTarget
                leftWitnessEdge.current leftWitnessEdge.future := by
              rw [hLeftMatch.2.1, hLeftMatch.2.2]
              exact hLeftWitnessOffers
            have hRightWitnessOffers' : TypeOffers rightWitnessEdge.environment
                rightResidual rightWitnessEdge.label.semantic
                rightWitnessTarget rightWitnessEdge.current
                rightWitnessEdge.future := by
              rw [hRightMatch.2.1, hRightMatch.2.2]
              exact hRightWitnessOffers
            have hSemanticLocals :=
              syncAutomatonEdgeWitnesses_to_localTypeEnvironments interface
                hLeftWitnessOffers' hRightWitnessOffers' hWitnessSync
            dsimp only at hSemanticLocals
            have hSemanticLocals' :
                LocalTypeEnvironment environment interface rightEnvironment
                    rightResidual rightLabel leftEnvironment ∧
                  LocalTypeEnvironment environment interface leftEnvironment
                    leftResidual leftLabel rightEnvironment := by
              simpa [leftAutomatonEdge, rightAutomatonEdge,
                hCombinedEnvironment] using hSemanticLocals
            have hLabelSync : TypeLabel.Sync interface leftLabel rightLabel := by
              simpa [leftAutomatonEdge, rightAutomatonEdge,
                AutomatonConstructionLabel.semantic] using hLabelSyncRaw
            have hEnvironmentWellFormed : environment.WellFormed :=
              signature.localEnvironment_wellFormed hOuterEnvironment
            have hParentTransition := TypeTransition.par environment
              leftEnvironment rightEnvironment interface leftResidual
              leftTarget rightResidual rightTarget leftLabel rightLabel
              hLeftTransition hRightTransition
              ⟨hEnvironmentWellFormed, hSemanticLocals'.1,
                hSemanticLocals'.2, hLabelSync⟩
            have hParentOffers := TypeOffers.par environment leftEnvironment
              rightEnvironment interface leftResidual leftTarget rightResidual
              rightTarget leftLabel rightLabel leftSummary.current
              leftSummary.future rightSummary.current rightSummary.future
              hLeftOffers hRightOffers hSemanticLocals'.1 hSemanticLocals'.2
              ⟨hEnvironmentWellFormed, hLabelSync⟩
            rw [← hLabel, ← hCurrent, ← hFuture]
            simpa [hideOffers, hideTypeOffers] using
              And.intro hParentTransition hParentOffers

/-- Public parallel correspondence directly from the induction-facing scoped
hypotheses. -/
theorem compilationStepCorrect_parallel_scoped
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hAlphabet : signature.WellFormed)
    (hSupports : signature.Supports (PactType.par left right interface))
    (hScoped : PactType.InterfaceScoped
      (PactType.par left right interface))
    (hLeftStep : CompilationScopedFragmentStepCorrect signature left)
    (hRightStep : CompilationScopedFragmentStepCorrect signature right)
    (hLeftWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature left)
    (hRightWitness :
      CompilationScopedResolvedOfferWitnessCorrect signature right) :
    CompilationStepCorrect signature (.par left right interface) := by
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  apply compilationStepCorrect_of_scopedFragmentStepCorrect signature
    (.par left right interface) hAlphabet
    hSupports.parallelInterfaces_subset
  exact compilationScopedFragmentStepCorrect_parallel signature left right
    interface hSupportFields.1 hScoped hLeftStep hRightStep hLeftWitness
    hRightWitness

/-- Exported environments are a special case of the exact local parallel
domain because signature well-formedness keeps them disjoint from every
declared constructor interface. -/
theorem compilationExportedFragmentStepCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hLeftWitness : CompilationResolvedOfferWitnessCorrect signature left)
    (hRightWitness : CompilationResolvedOfferWitnessCorrect signature right) :
    CompilationExportedFragmentStepCorrect signature
      (.par left right interface) := by
  intro residual residual' state environment label offers hRelated
    hOuterEnvironment
  exact compilationParallelFragmentStepCorrect_parallel signature left right
    interface hInterface hLeftStep hRightStep hLeftWitness hRightWitness
    hRelated (signature.environments_subset_localEnvironments hOuterEnvironment)
    (signature.environment_avoids_subinterface hAlphabet hOuterEnvironment
      hInterface)

/-- Public synchronized-product step correspondence.  Membership in the
fixed transition alphabet supplies the exported outer environment required
by the raw parallel theorem. -/
theorem compilationStepCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hLeftStep : CompilationFragmentStepCorrect signature left)
    (hRightStep : CompilationFragmentStepCorrect signature right)
    (hLeftWitness : CompilationResolvedOfferWitnessCorrect signature left)
    (hRightWitness : CompilationResolvedOfferWitnessCorrect signature right) :
    CompilationStepCorrect signature (.par left right interface) := by
  intro residual residual' state environment label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk environment label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hOuterEnvironment : environment ∈ signature.environments := by
    have hFields : environment ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact hFields.1
  have hRaw := compilationExportedFragmentStepCorrect_parallel signature left
    right interface hAlphabet hInterface hLeftStep hRightStep hLeftWitness
    hRightWitness (residual := residual) (residual' := residual')
    (state := state) (environment := environment) (label := label)
    (offers := offers) hRelated hOuterEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.par left right interface) state target environment label offers
        hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.par left right interface) state target environment label offers
        hSignatureSymbol).mp hEdge,
      hTarget⟩

/-! ### Recursion header correspondence -/

/-- The graph-future equality used to decorate the explicit silent edge from
a recursion binder header into its body.  The semantic target is the usual
capture-avoiding unfolding of the body. -/
def RecursionHeaderFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  computeFuture pending (.child 0 bodyFragment.initial) =
    typeFutureOffers (body.replaceVar name (.recur name body))

/-- The recursion binder's explicit header edge is present with the exact
decoration of the unfolded body. -/
theorem compileType_recursion_header_edge
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    (compileType signature (.recur name body)).HasEdge .root env
      TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body))))
      (.child 0 (compileType signature body).initial) := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let fragment := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hComputed : computeFuture
      { states := fragment.states, edges := fragment.edges }
      (.child 0 bodyFragment.initial) =
        typeFutureOffers (body.replaceVar name (.recur name body)) := by
    simpa [pending, fragment, bodyFragment] using hFuture
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
          (.recur name body) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := typeFutureOffers (body.replaceVar name (.recur name body))
      target := .child 0 bodyFragment.initial }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 bodyFragment.initial) ∅
        target := .child 0 bodyFragment.initial }, ?_, ?_⟩
    · rw [hFragment]
      simp [fragment, buildRecursionAutomaton, finishAutomatonFragment,
        hLocalEnvironment]
      left
      rfl
    · rw [hFragment]
      simp [hComputed]
  · simp [hSymbol, bodyFragment]

/-- Complete root-state correspondence for the explicit recursion-unfolding
step. -/
theorem compileType_recursion_header_step_iff
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hFuture : RecursionHeaderFutureCorrect signature name body)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅
        (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
          signature.transitionAlphabet) :
    DecoratedTypeTransition env (.recur name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅
          (typeFutureOffers (body.replaceVar name (.recur name body))))
        (body.replaceVar name (.recur name body)) ↔
      ∃ state',
        (compileType signature (.recur name body)).HasEdge .root env
            TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur name body))))
            state' ∧
          TypeCompilationRelation (.recur name body) state'
            (body.replaceVar name (.recur name body)) := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro _
    refine ⟨.child 0 (compileType signature body).initial, ?_, ?_⟩
    · exact compileType_recursion_header_edge signature name body
        hEnvironment hFuture hSymbol
    · exact TypeCompilationRelation.recur_body name body body _
        (compileType_initial_relation signature body)
  · intro _
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-! ### Raw recursion-fragment classification -/

/- A variable forbidden from the current tail position has no free
occurrence there, so replacing it is inert.  The matching nested-binder case
is handled by shadowing: replacement stops at that binder without inspecting
its body. -/
mutual
  theorem PactType.replaceVar_eq_self_of_tailOccurrences_false
      (processType replacement : PactType) (name : String)
      (hTail : processType.TailOccurrences name False) :
      processType.replaceVar name replacement = processType := by
    cases processType with
    | message msg dir => simp [PactType.replaceVar]
    | progress pid => simp [PactType.replaceVar]
    | tock => simp [PactType.replaceVar]
    | skip => simp [PactType.replaceVar]
    | var other =>
        simp only [PactType.TailOccurrences] at hTail
        have hNe : name ≠ other := by
          intro hEquality
          exact hTail hEquality.symm
        simp [PactType.replaceVar, hNe]
    | recur other nestedBody =>
        by_cases hShadow : other = name
        · have hTarget : name = other := hShadow.symm
          simp [PactType.replaceVar, hTarget]
        · simp only [PactType.TailOccurrences, hShadow, if_false] at hTail
          have hTarget : name ≠ other := by
            intro hEquality
            exact hShadow hEquality.symm
          simp only [PactType.replaceVar, hTarget, if_false]
          rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
            nestedBody replacement name hTail]
    | choice left right =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hLeft, hRight⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              left replacement name hLeft,
          PactType.replaceVar_eq_self_of_tailOccurrences_false
              right replacement name hRight]
    | fairChoice bid left right =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hLeft, hRight⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              left replacement name hLeft,
          PactType.replaceVar_eq_self_of_tailOccurrences_false
              right replacement name hRight]
    | seq left right =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hLeft, hRight⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              left replacement name hLeft,
          PactType.replaceVar_eq_self_of_tailOccurrences_false
              right replacement name hRight]
    | par left right interface =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hLeft, hRight⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              left replacement name hLeft,
          PactType.replaceVar_eq_self_of_tailOccurrences_false
              right replacement name hRight]
    | xoffer elseType branches =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hElse, hBranches⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              elseType replacement name hElse,
          PactType.replaceBranches_eq_self_of_tailOccurrences_false
              branches replacement name hBranches]
    | offer elseType branches =>
        simp only [PactType.TailOccurrences] at hTail
        rcases hTail with ⟨hElse, hBranches⟩
        simp only [PactType.replaceVar]
        rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
              elseType replacement name hElse,
          PactType.replaceBranches_eq_self_of_tailOccurrences_false
              branches replacement name hBranches]
  termination_by sizeOf processType

  theorem PactType.replaceBranches_eq_self_of_tailOccurrences_false
      (branches : List (BareMessage × PactType)) (replacement : PactType)
      (name : String)
      (hTail : PactType.TailBranchOccurrences name False branches) :
      PactType.replaceBranches branches name replacement = branches := by
    cases branches with
    | nil => simp [PactType.replaceBranches]
    | cons branch rest =>
        cases hBranchEq : branch with
        | mk action branchType =>
            simp only [hBranchEq, PactType.TailBranchOccurrences] at hTail
            rcases hTail with ⟨hBranch, hRest⟩
            simp only [PactType.replaceBranches]
            rw [PactType.replaceVar_eq_self_of_tailOccurrences_false
                  branchType replacement name hBranch,
              PactType.replaceBranches_eq_self_of_tailOccurrences_false
                  rest replacement name hRest]
  termination_by sizeOf branches
decreasing_by
  all_goals
    simp_all
    omega
end

/-- Exact classifier for resolved edges leaving the fresh recursion header.
This version stays in the pending constructor fragment, before the public
alphabet filter. -/
private theorem buildRecursionAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge .root env label offers target ↔
      env ∈ signature.localEnvironments ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (.child 0 body.initial) = offers.future ∧
        target = .child 0 body.initial := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hEdge with hHeader | hBody
    · rcases hHeader with ⟨edgeEnvironment, hLocal, rfl⟩
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      aesop
    · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
      by_cases hVariable : bodyEdge.label = .variable name
      · simp [hVariable, childState] at hSource
      · simp [hVariable, childState] at hSource
  · rintro ⟨hLocal, rfl, hCurrent, hFuture, rfl⟩
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (.child 0 body.initial) ∅
        target := .child 0 body.initial }, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · left
      exact ⟨env, hLocal, rfl⟩
    · exact hCurrent.symm
    · simpa using hFuture

/-- A matching variable marker in the body is installed as a silent backedge
to the tagged body entry.  Its future is deliberately resolved in the whole
recursion graph, which is the information lost by resolving the body first. -/
private theorem buildRecursionAutomaton_variable_marker_hasResolvedEdge
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ body.edges)
    (hVariable : edge.label = .variable name) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 edge.source) edge.environment
      TypeLabel.silent
      { current := ∅,
        future := computeFuture pending (.child 0 body.initial) }
      (.child 0 body.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge]
  refine ⟨
    { source := .child 0 edge.source
      environment := edge.environment
      label := .visible TypeLabel.silent
      current := ∅
      future := .at (.child 0 body.initial) ∅
      target := .child 0 body.initial }, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image]
    right
    refine ⟨edge, hEdge, ?_⟩
    simp [hVariable, childState]
  · simp

/-- Every resolved edge from a tagged recursion-body state is either the
installed matching-variable backedge or an unchanged non-matching body edge.
The latter's symbolic future is resolved in the enclosing recursion graph. -/
private theorem buildRecursionAutomaton_body_hasResolvedEdge_iff
    (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) (source : TypeAutomatonState)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let recursion := buildRecursionAutomaton signature name body
    let pending : PendingAutomaton :=
      { states := recursion.states, edges := recursion.edges }
    recursion.HasResolvedEdge (.child 0 source) env label offers target ↔
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label = .variable name ∧
          edge.environment = env ∧ label = TypeLabel.silent ∧
          offers.current = ∅ ∧
          computeFuture pending (.child 0 body.initial) = offers.future ∧
          target = .child 0 body.initial) ∨
      (∃ edge ∈ body.edges,
        edge.source = source ∧ edge.label ≠ .variable name ∧
          edge.environment = env ∧ edge.label = .visible label ∧
          edge.current = offers.current ∧
          (match edge.future with
            | .explicit future => future
            | .at state removed =>
                computeFuture pending (.child 0 state) \ removed) =
              offers.future ∧
          target = .child 0 edge.target) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨lifted, hLifted, hSource, hEnvironment, hLabel, hCurrent,
      hFuture, hTarget⟩
    rcases hLifted with hHeader | hBody
    · rcases hHeader with ⟨headerEnvironment, hLocal, rfl⟩
      simp at hSource
    · rcases hBody with ⟨edge, hEdge, rfl⟩
      by_cases hVariable : edge.label = .variable name
      · simp only [hVariable, if_true, Finset.sdiff_empty, childState]
          at hSource hEnvironment hLabel hCurrent hFuture hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hVisibleLabel : label = TypeLabel.silent := by
          injection hLabel with hEquality
          exact hEquality.symm
        left
        exact ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hVisibleLabel, hCurrent.symm, hFuture, hTarget.symm⟩
      · simp only [hVariable, if_false, childState]
          at hSource hEnvironment hLabel hCurrent hTarget
        have hEdgeSource : edge.source = source := by
          injection hSource
        have hEdgeTarget : target = .child 0 edge.target := hTarget.symm
        right
        refine ⟨edge, hEdge, hEdgeSource, hVariable, hEnvironment,
          hLabel, hCurrent, ?_, hEdgeTarget⟩
        cases hSpec : edge.future with
        | explicit future =>
            simpa [hVariable, hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hVariable, hSpec, childFutureSpec, childState]
              using hFuture
  · rintro (hMarker | hBody)
    · rcases hMarker with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (.child 0 body.initial) ∅
          target := .child 0 body.initial }, ?_, ?_, hEnvironment, ?_,
            hCurrent.symm, ?_, hTarget.symm⟩
      · right
        refine ⟨edge, hEdge, ?_⟩
        simp [hVariable, childState]
      · simpa [hSource]
      · simpa [hLabel]
      · simpa using hFuture
    · rcases hBody with ⟨edge, hEdge, hSource, hVariable,
        hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
      refine ⟨
        { source := .child 0 edge.source
          environment := edge.environment
          label := edge.label
          current := edge.current
          future := childFutureSpec 0 edge.future
          target := .child 0 edge.target }, ?_, ?_, hEnvironment,
            hLabel, hCurrent, ?_, ?_⟩
      · right
        exact ⟨edge, hEdge, by simp [hVariable, childState]⟩
      · simpa [hSource, childState]
      · cases hSpec : edge.future with
        | explicit future =>
            simpa [hSpec, childFutureSpec] using hFuture
        | «at» state removed =>
            simpa [hSpec, childFutureSpec, childState] using hFuture
      · simpa [hTarget, childState]

/-- Ambient future invariant required by recursion.  It deliberately computes
inside the closed binder graph: at a matching variable state the installed
backedge exposes the next iteration's offers, while a clock edge prevents
those offers from leaking into the preceding cycle. -/
def RecursionBodyFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  ∀ state residual,
    TypeCompilationRelation body state residual →
      computeFuture pending (.child 0 state) =
        typeFutureOffers (residual.replaceVar name (.recur name body))

/-- Whole-fragment future correctness immediately supplies the ambient
tagged-body invariant required by the recursion constructor. -/
theorem recursionBodyFutureCorrect_of_compilationFutureCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : CompilationFutureCorrect signature (.recur name body)) :
    RecursionBodyFutureCorrect signature name body := by
  intro state residual hRelated
  simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using
    hFuture (.child 0 state)
      (residual.replaceVar name (.recur name body))
      (TypeCompilationRelation.recur_body name body residual state hRelated)

/-- The genuinely recursion-specific tagged-body obligation.  It interprets
matching variable markers as calls of the surrounding binder and resolves all
symbolic futures only after that binder has installed its backedges. -/
def RecursionBodyStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.recur name body)) (.recur name body)
  ∀ {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation body state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual')

/-- Induction-facing recursion-body obligation.  Unlike the historical raw
package above, it is restricted to environments avoiding every parallel
interface in the body, which is the domain actually propagated by admissible
constructor nesting. -/
def RecursionBodyScopedStepCorrect
    (signature : TypeAlphabet) (name : String) (body : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.recur name body)) (.recur name body)
  ∀ {state : TypeAutomatonState} {residual residual' : PactType}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation body state residual →
    env ∈ signature.localEnvironments →
    env.AvoidsInterface body.ParallelInterfaces →
    (DecoratedTypeTransition env
        (residual.replaceVar name (.recur name body)) label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge (.child 0 state) env label offers target ∧
        TypeCompilationRelation (.recur name body) target residual')

/-- Inversion of a decorated recursion-header step. -/
private theorem TypeTransition.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel}
    (hTransition : TypeTransition env (.recur name body) label target) :
    env.WellFormed ∧ label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) := by
  cases hTransition <;> simp_all

private theorem TypeOffers.recur_fields
    {env : TypeEnvironment} {name : String} {body target : PactType}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.recur name body) label target current future) :
    label = TypeLabel.silent ∧
      target = body.replaceVar name (.recur name body) ∧
      current = ∅ ∧
      future = typeFutureOffers
        (body.replaceVar name (.recur name body)) := by
  cases hOffers <;> simp_all

private theorem decoratedTypeTransition_recur_iff
    (env : TypeEnvironment) (name : String) (body target : PactType)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    DecoratedTypeTransition env (.recur name body) label offers target ↔
      env.WellFormed ∧ label = TypeLabel.silent ∧
        target = body.replaceVar name (.recur name body) ∧
        offers.current = ∅ ∧
        offers.future =
          typeFutureOffers (body.replaceVar name (.recur name body)) := by
  constructor
  · rintro ⟨hTransition, hOffers⟩
    have hTransitionFields := TypeTransition.recur_fields hTransition
    have hOfferFields := TypeOffers.recur_fields hOffers
    exact ⟨hTransitionFields.1, hTransitionFields.2.1,
      hTransitionFields.2.2, hOfferFields.2.2.1,
      hOfferFields.2.2.2⟩
  · rintro ⟨hWellFormed, rfl, rfl, hCurrent, hFuture⟩
    cases offers
    simp only at hCurrent hFuture
    subst_vars
    exact ⟨TypeTransition.recur env name body hWellFormed,
      TypeOffers.recur env name body hWellFormed⟩

/-- The root-state branch of raw recursion correspondence.  This needs only
the ambient future invariant; guardedness and tail-recursiveness enter when
establishing that invariant and the tagged-body branch. -/
theorem compilationFragmentStepCorrect_recursion_root
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    {residual' : PactType} {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hLocalEnvironment : env ∈ signature.localEnvironments) :
    DecoratedTypeTransition env (.recur name body) label offers residual' ↔
      ∃ state',
        (compileTypeFuel signature
          (typeCompilationFuel (.recur name body))
          (.recur name body)).HasResolvedEdge .root env label offers state' ∧
        TypeCompilationRelation (.recur name body) state' residual' := by
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  let pending : PendingAutomaton :=
    { states := recursion.states, edges := recursion.edges }
  have hBodyInitial : TypeCompilationRelation body bodyFragment.initial body := by
    exact compileTypeFuel_initial_relation signature
      (typeCompilationFuel body) body
      (typeCompilationFuel_sufficient body)
  have hComputed : computeFuture pending (.child 0 bodyFragment.initial) =
      typeFutureOffers (body.replaceVar name (.recur name body)) := by
    have hAmbient := hFuture bodyFragment.initial body hBodyInitial
    simpa [RecursionBodyFutureCorrect, bodyFragment, recursion, pending]
      using hAmbient
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
        recursion := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hTargetRelation : TypeCompilationRelation (.recur name body)
      (.child 0 bodyFragment.initial)
      (body.replaceVar name (.recur name body)) :=
    TypeCompilationRelation.recur_body name body body _ hBodyInitial
  constructor
  · intro hStep
    rcases (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mp hStep with
      ⟨hWellFormed, hLabel, hResidual, hCurrent, hOfferFuture⟩
    subst residual'
    refine ⟨.child 0 bodyFragment.initial, ?_, hTargetRelation⟩
    rw [hFragment]
    apply (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers (.child 0 bodyFragment.initial)).mpr
    exact ⟨hLocalEnvironment, hLabel, hCurrent, hComputed.trans
      hOfferFuture.symm, rfl⟩
  · rintro ⟨target, hEdge, hTarget⟩
    rw [hFragment] at hEdge
    rcases (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
      bodyFragment env label offers target).mp hEdge with
      ⟨_, hLabel, hCurrent, hEdgeFuture, hTargetState⟩
    subst target
    have hResidual : residual' =
        body.replaceVar name (.recur name body) :=
      TypeCompilationRelation.residual_unique hTarget hTargetRelation
    apply (decoratedTypeTransition_recur_iff env name body residual'
      label offers).mpr
    exact ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
      hLabel, hResidual, hCurrent,
      (hComputed.symm.trans hEdgeFuture).symm⟩

/-- Once the ambient future and tagged-body substitution invariants have been
established, the two source shapes of a recursion fragment compose into the
raw one-step correspondence. -/
theorem compilationFragmentStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationFragmentStepCorrect signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated with
  | recur_source =>
      exact compilationFragmentStepCorrect_recursion_root signature name body
        hFuture hLocalEnvironment
  | recur_body _ _ childResidual childState hChildRelated =>
      exact hBodyStep hChildRelated hLocalEnvironment

/-- Scoped recursion closure.  The binder header needs only the ambient
future equality; tagged body states consume the scoped substitution theorem. -/
theorem compilationScopedFragmentStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyScopedStepCorrect signature name body) :
    CompilationScopedFragmentStepCorrect signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  cases hRelated with
  | recur_source =>
      exact compilationFragmentStepCorrect_recursion_root signature name body
        hFuture hLocalEnvironment
  | recur_body _ _ childResidual childState hChildRelated =>
      apply hBodyStep hChildRelated hLocalEnvironment
      simpa [PactType.ParallelInterfaces] using hAvoids

/-- Raw fragment correspondence exports uniformly through the fixed public
alphabet filter. -/
theorem compilationStepCorrect_of_fragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType)
    (hRaw : CompilationFragmentStepCorrect signature processType) :
    CompilationStepCorrect signature processType := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hFragment := hRaw (residual' := residual') (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hFragment.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mpr hEdge,
      hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hFragment.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature processType
        state target env label offers hSignatureSymbol).mp hEdge,
      hTarget⟩

/-- Public recursion correspondence follows from the two closed-graph
recursion invariants. -/
theorem compilationStepCorrect_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyStepCorrect signature name body) :
    CompilationStepCorrect signature (.recur name body) :=
  compilationStepCorrect_of_fragmentStepCorrect signature (.recur name body)
    (compilationFragmentStepCorrect_recursion signature name body
      hFuture hBodyStep)

/-- Public recursion correspondence from the induction-facing scoped body
obligation. -/
theorem compilationStepCorrect_recursion_scoped
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hAlphabet : signature.WellFormed)
    (hSupports : signature.Supports (.recur name body))
    (hFuture : RecursionBodyFutureCorrect signature name body)
    (hBodyStep : RecursionBodyScopedStepCorrect signature name body) :
    CompilationStepCorrect signature (.recur name body) := by
  apply compilationStepCorrect_of_scopedFragmentStepCorrect signature
    (.recur name body) hAlphabet hSupports.parallelInterfaces_subset
  exact compilationScopedFragmentStepCorrect_recursion signature name body
    hFuture hBodyStep

/-! ### Visible-edge target relatedness: non-product constructors -/

theorem compilationResolvedEdgeTargetsRelated_skip
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .skip := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    at hPending
  rcases hPending with ⟨edgeEnvironment, hConditions, rfl⟩
  simp only at hTarget
  subst target
  exact ⟨.skip, TypeCompilationRelation.skip⟩

theorem compilationResolvedEdgeTargetsRelated_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationResolvedEdgeTargetsRelated signature (.message msg dir) := by
  intro source residual environment label offers target hRelated hEdge
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | message_source =>
      rcases compileTypeFuel_message_resolved_edge_cases signature msg dir
          hEdge with hAction | hWait | hFinal
      · rcases hAction with ⟨_, rfl, _, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩
      · rcases hWait with ⟨_, rfl, _, _, _, _, _⟩
        exact ⟨.message msg dir,
          TypeCompilationRelation.message_source msg dir⟩
      · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
        simp at hSource
  | message_final =>
      rcases compileTypeFuel_message_resolved_edge_cases signature msg dir
          hEdge with hAction | hWait | hFinal
      · rcases hAction with ⟨hSource, _, _, _, _, _⟩
        simp at hSource
      · rcases hWait with ⟨hSource, _, _, _, _, _, _⟩
        simp at hSource
      · rcases hFinal with ⟨_, rfl, _, _, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.message_final msg dir⟩

theorem compilationResolvedEdgeTargetsRelated_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationResolvedEdgeTargetsRelated signature (.progress pid) := by
  intro source residual environment label offers target hRelated hEdge
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | progress_source =>
      rcases compileTypeFuel_progress_resolved_edge_cases signature pid hEdge
        with hAction | hFinal
      · rcases hAction with ⟨_, rfl, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩
      · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
        simp at hSource
  | progress_final =>
      rcases compileTypeFuel_progress_resolved_edge_cases signature pid hEdge
        with hAction | hFinal
      · rcases hAction with ⟨hSource, _, _, _, _⟩
        simp at hSource
      · rcases hFinal with ⟨_, rfl, _, _, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.progress_final pid⟩

theorem compilationResolvedEdgeTargetsRelated_tock
    (signature : TypeAlphabet) :
    CompilationResolvedEdgeTargetsRelated signature .tock := by
  intro source residual environment label offers target hRelated hEdge
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | cycle_source =>
      rcases compileTypeFuel_tock_resolved_edge_cases signature hEdge with
        hAction | hWait | hFinal
      · rcases hAction with ⟨_, rfl, _, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.cycle_final⟩
      · rcases hWait with ⟨_, rfl, _, _, _, _⟩
        exact ⟨.tock, TypeCompilationRelation.cycle_source⟩
      · rcases hFinal with ⟨hSource, _, _, _, _, _, _⟩
        simp at hSource
  | cycle_final =>
      rcases compileTypeFuel_tock_resolved_edge_cases signature hEdge with
        hAction | hWait | hFinal
      · rcases hAction with ⟨hSource, _, _, _, _, _⟩
        simp at hSource
      · rcases hWait with ⟨hSource, _, _, _, _, _⟩
        simp at hSource
      · rcases hFinal with ⟨_, rfl, _, _, _, _, _⟩
        exact ⟨.skip, TypeCompilationRelation.cycle_final⟩

theorem compilationResolvedEdgeTargetsRelated_var
    (signature : TypeAlphabet) (name : String) :
    CompilationResolvedEdgeTargetsRelated signature (.var name) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated
  rcases hEdge with ⟨edge, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
    at hPending
  rcases hPending with ⟨edgeEnvironment, hLocal, rfl⟩
  simp at hLabel

theorem compilationResolvedEdgeTargetsRelated_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.seq left right) := by
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | sequence_left _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_sequence_left_edge_cases signature left right
          hEdge with hChild | hBridge
      · rcases hChild with
          ⟨childTarget, childFuture, rfl, hChildEdge, hComputed⟩
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hLeftTargets hChildRelated hChildEdge
        exact ⟨.seq targetResidual right,
          TypeCompilationRelation.sequence_left left right targetResidual
            childTarget hTargetRelated⟩
      · rcases hBridge with ⟨hSkipping, hLocal, hLabel, hCurrent,
          hFuture, rfl⟩
        have hInitial : TypeCompilationRelation right
            (compileTypeFuel signature (typeCompilationFuel right) right).initial
            right :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel right) right
            (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.sequence_right left right
          right _ hInitial⟩
  | sequence_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_sequence_right_edge_cases signature left right
          hEdge with ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual,
        TypeCompilationRelation.sequence_right left right targetResidual
          childTarget hTargetRelated⟩

private theorem compileTypeFuel_choiceLike_root_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      .root environment label offers target) :
    target = .child 0 (compileTypeFuel signature
        (typeCompilationFuel left) left).initial ∨
      target = .child 1 (compileTypeFuel signature
        (typeCompilationFuel right) right).initial := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hFields :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment selectionLeft selectionRight environment label offers
      target).mp (by simpa [fuel, leftFragment, rightFragment] using hEdge)
  rcases hFields with hSelected | hSelected
  · left
    simpa [hLeftStable] using hSelected.2.2.2.2
  · right
    simpa [hRightStable] using hSelected.2.2.2.2

private theorem compileTypeFuel_choiceLike_left_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 0 source) environment label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel left) left)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hParent : fragment.HasResolvedEdge (.child 0 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_left signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 0 source) environment label
      offers (.child 0 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 0 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hLeftStable] using hChild⟩

private theorem compileTypeFuel_choiceLike_right_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 1 source) environment label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel right) right)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hParent : fragment.HasResolvedEdge (.child 1 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_right signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 1 source) environment label
      offers (.child 1 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 1 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hRightStable] using hChild⟩

theorem compilationResolvedEdgeTargetsRelated_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature (.choice left right) := by
  intro source residual environment label offers target hRelated hEdge
  have hParent : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent)
      source environment label offers target := by
    simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using hEdge
  cases hRelated with
  | choice_source =>
      rcases compileTypeFuel_choiceLike_root_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left, TypeCompilationRelation.choice_left left right left _
          hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.choice_right left right right _
          hInitial⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.choice_left left right
        targetResidual childTarget hTargetRelated⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
          TypeLabel.silent TypeLabel.silent hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.choice_right left right
        targetResidual childTarget hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftTargets : CompilationResolvedEdgeTargetsRelated signature left)
    (hRightTargets : CompilationResolvedEdgeTargetsRelated signature right) :
    CompilationResolvedEdgeTargetsRelated signature
      (.fairChoice bid left right) := by
  intro source residual environment label offers target hRelated hEdge
  have hParent : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false))
      source environment label offers target := by
    simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel] using hEdge
  cases hRelated with
  | fair_source =>
      rcases compileTypeFuel_choiceLike_root_target_cases signature left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        hSelected | hSelected
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel left) left (typeCompilationFuel_sufficient left)
        exact ⟨left, TypeCompilationRelation.fair_left bid left right left _
          hInitial⟩
      · rw [hSelected]
        have hInitial := compileTypeFuel_initial_relation signature
          (typeCompilationFuel right) right (typeCompilationFuel_sufficient right)
        exact ⟨right, TypeCompilationRelation.fair_right bid left right right _
          hInitial⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_left_target_cases signature left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hLeftTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.fair_left bid left right
        targetResidual childTarget hTargetRelated⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      rcases compileTypeFuel_choiceLike_right_target_cases signature left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) hParent with
        ⟨childTarget, rfl, hChildEdge⟩
      obtain ⟨targetResidual, hTargetRelated⟩ :=
        hRightTargets hChildRelated hChildEdge
      exact ⟨targetResidual, TypeCompilationRelation.fair_right bid left right
        targetResidual childTarget hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_recursion
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hBodyTargets : CompilationResolvedEdgeTargetsRelated signature body) :
    CompilationResolvedEdgeTargetsRelated signature (.recur name body) := by
  intro source residual environment label offers target hRelated hEdge
  let bodyFragment := compileTypeFuel signature (typeCompilationFuel body) body
  let recursion := buildRecursionAutomaton signature name bodyFragment
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.recur name body)) (.recur name body) =
        recursion := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment] at hEdge
  cases hRelated with
  | recur_source =>
      rcases (buildRecursionAutomaton_root_hasResolvedEdge_iff signature name
          bodyFragment environment label offers target).mp hEdge with
        ⟨hLocal, hLabel, hCurrent, hFuture, rfl⟩
      have hInitial : TypeCompilationRelation body bodyFragment.initial body :=
        compileTypeFuel_initial_relation signature (typeCompilationFuel body)
          body (typeCompilationFuel_sufficient body)
      exact ⟨body.replaceVar name (.recur name body),
        TypeCompilationRelation.recur_body name body body _ hInitial⟩
  | recur_body _ _ childResidual childState hChildRelated =>
      rcases (buildRecursionAutomaton_body_hasResolvedEdge_iff signature name
          bodyFragment childState environment label offers target).mp hEdge with
        hMarker | hBody
      · rcases hMarker with ⟨edge, hPending, hSource, hVariable,
          hEnvironment, hLabel, hCurrent, hFuture, rfl⟩
        have hInitial : TypeCompilationRelation body bodyFragment.initial body :=
          compileTypeFuel_initial_relation signature
            (typeCompilationFuel body) body
            (typeCompilationFuel_sufficient body)
        exact ⟨body.replaceVar name (.recur name body),
          TypeCompilationRelation.recur_body name body body _ hInitial⟩
      · rcases hBody with ⟨edge, hPending, hSource, hNotVariable,
          hEnvironment, hLabel, hCurrent, hFuture, rfl⟩
        let childOffers : TypeOfferSummary :=
          { current := edge.current
            future := match edge.future with
              | .explicit future => future
              | .at state removed =>
                  computeFuture
                    { states := bodyFragment.states,
                      edges := bodyFragment.edges } state \ removed }
        have hChildEdge : bodyFragment.HasResolvedEdge childState environment
            label childOffers edge.target := by
          refine ⟨edge, hPending, hSource, hEnvironment, hLabel, rfl, ?_, rfl⟩
          cases hSpec : edge.future <;> simp [childOffers, hSpec]
        obtain ⟨targetResidual, hTargetRelated⟩ :=
          hBodyTargets hChildRelated (by
            simpa [bodyFragment] using hChildEdge)
        exact ⟨targetResidual.replaceVar name (.recur name body),
          TypeCompilationRelation.recur_body name body targetResidual
            edge.target hTargetRelated⟩

/-- Every compiled parallel edge hides immediate interface actions. -/
theorem compileType_parallel_edge_hides_immediate_interface
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature (.par left right interface)).HasEdge
      source env label offers target) :
    ∀ action ∈ env.immediate, action.1 ∉ interface := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        have hEnvironment := congrArg
          (fun edge : TypeAutomatonEdge => edge.symbol.environment) hOutput
        simp only at hEnvironment
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        change env = pendingEdge.environment at hEnvironment
        have hFuel :
            typeCompilationFuel (.par left right interface) =
              Nat.succ (max (typeCompilationFuel left)
                (typeCompilationFuel right)) := by
          rw [typeCompilationFuel]
          omega
        rw [hFuel] at hPendingEdge
        simp only [compileTypeFuel] at hPendingEdge
        change pendingEdge ∈
            (buildParallelAutomaton interface
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).edges
          at hPendingEdge
        simp only [buildParallelAutomaton, finishAutomatonFragment]
          at hPendingEdge
        have hProductEdge := hPendingEdge
        simp only [Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_filter] at hProductEdge
        rcases hProductEdge with ⟨leftEdge, _, rightEdge, ⟨_, _⟩, rfl⟩
        intro action hAction hInterface
        rw [hEnvironment] at hAction
        unfold combineAutomatonEnvironment at hAction
        split at hAction
        · simp [TypeEnvironment.tock] at hAction
        · exact (Finset.mem_filter.mp hAction).2 hInterface
      · simp at hOutput

/-- The process-to-automaton simulation of Lemma 4.6. -/
structure ProcessAutomatonCorrespondence
    (process : Proc) (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : Proc → TypeAutomatonState → Prop
  initial : relation process automaton.initial
  matchStep :
    ∀ {p₀ p₁ : Proc} {state : TypeAutomatonState}
      {env : Environment} {label : Label},
      relation p₀ state →
      ProcessTransition env p₀ label p₁ →
      ∃ state' offers,
        automaton.HasEdge state (eraseEnvironment env) (eraseLabel label) offers state' ∧
        relation p₁ state'

end

end Pact
