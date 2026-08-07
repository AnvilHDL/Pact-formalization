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

/-- All message actions that may still be offered before the next clock. -/
def typeFutureOffers (processType : PactType) : Finset BareMessage :=
  typeFutureOffersFuel (sizeOf processType + 1) processType

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
          (if left' = .skip then typeFutureOffers right else childFuture)
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
  let states := childStates 0 left ∪ childStates 1 right
  let accepting := childAccepting 1 right
  let skipping := childSkipping 1 right
  let leftEdges : Finset PendingAutomatonEdge := left.edges.image fun edge =>
    { source := childState 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := if edge.target ∈ left.skipping then
        .at (childState 1 right.initial) ∅
      else childFutureSpec 0 edge.future
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
    (hLeftTargets : left.FutureTargetsInStates)
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
    by_cases hSkipping : leftEdge.target ∈ left.skipping
    · simp only [hSkipping, if_true] at hFuture
      cases hFuture
      simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
        childState, hRightInitial]
    · simp only [hSkipping, if_false] at hFuture
      cases hSpec : leftEdge.future with
      | explicit offers =>
          simp [childFutureSpec, hSpec] at hFuture
      | «at» leftTarget removed =>
          simp only [childFutureSpec, hSpec] at hFuture
          cases hFuture
          have hLeftTarget := hLeftTargets leftEdge hLeftEdge
            leftTarget removed hSpec
          simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
            childState, hLeftTarget]
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
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using ih left hLeft
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
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
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
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

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
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

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
          simpa using hOffer
        · rcases hWaiting with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hFinal with ⟨_, _, rfl⟩
          simp at hSource
      · intro hAction
        simp only [typeFutureOffers, typeFutureOffersFuel,
          Finset.mem_singleton] at hAction
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
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-! ### Parallel environment reconstruction -/

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

end TypeAlphabet

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
      simpa [typeBranchActions, typeFutureOffers, typeFutureOffersFuel] using
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
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
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
    simp_all [TypeLabel.message, typeFutureOffers, typeFutureOffersFuel]

private theorem TypeOffers.message_wait_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) TypeLabel.silent
      (.message msg dir) current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.silent, typeFutureOffers, typeFutureOffersFuel]

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
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_source =>
            refine ⟨TypeTransition.action_wait env msg dir
              ⟨hWellFormed, hNoNeed, hClock⟩, ?_⟩
            simpa [typeFutureOffers, typeFutureOffersFuel] using
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
        rw [← hCurrent] at hFuture
        simp only [Finset.sdiff_empty, childState] at hFuture
        left
        simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
        aesop
      · rw [hEdge] at hSource hEnvironment hLabel hCurrent hFuture hTarget
        rw [← hCurrent] at hFuture
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
    simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
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
              subst targetResidual
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
              subst targetResidual
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
