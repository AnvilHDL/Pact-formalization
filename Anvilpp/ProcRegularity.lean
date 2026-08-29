import Anvilpp.PactSemantics

/-!
# Proc regularity predicates, mirroring `PactTypeRegularity.lean`
-/


noncomputable section

namespace Proc

  mutual
    /-- A process must pass through a clock tick before it can complete. -/
    def MustTockBeforeCompletion : Proc → Prop
      | .cycle _ => True
      | .seq _ left right =>
          MustTockBeforeCompletion left ∨ MustTockBeforeCompletion right
      | .par _ left right _ =>
          MustTockBeforeCompletion left ∧ MustTockBeforeCompletion right
      | .recur _ _ body => MustTockBeforeCompletion body
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          MustTockBeforeCompletion left ∧ MustTockBeforeCompletion right
      | .letp _ _ _ p => MustTockBeforeCompletion p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          MustTockBeforeCompletion elseProcess ∧
            BranchesMustTockBeforeCompletion branches
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _ => False
    termination_by process => sizeOf process

    def BranchesMustTockBeforeCompletion : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          MustTockBeforeCompletion (ChoiceBranch.continuation branch) ∧
            BranchesMustTockBeforeCompletion rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Every free occurrence of a recursion variable is reached only after a
    clock step. -/
    def GuardedOccurrences (name : String) (guarded : Prop) : Proc → Prop
      | .var _ other => other = name → guarded
      | .seq _ left right =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name
              (guarded ∨ MustTockBeforeCompletion left) right
      | .par _ left right _ =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name guarded right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          GuardedOccurrences name guarded left ∧
            GuardedOccurrences name guarded right
      | .letp _ _ _ p => GuardedOccurrences name guarded p
      | .recur _ other body =>
          if other = name then True else GuardedOccurrences name guarded body
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          GuardedOccurrences name guarded elseProcess ∧
            GuardedBranchOccurrences name guarded branches
      | .send _ _ _ p | .recv _ _ _ p =>
          GuardedOccurrences name guarded p
      | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def GuardedBranchOccurrences (name : String) (guarded : Prop) :
        List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          GuardedOccurrences name guarded (ChoiceBranch.continuation branch) ∧
            GuardedBranchOccurrences name guarded rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Every recursive backedge is protected by a prior clock. -/
    def ClockGuarded : Proc → Prop
      | .recur _ name body =>
          GuardedOccurrences name False body ∧ ClockGuarded body
      | .seq _ left right | .par _ left right _ =>
          ClockGuarded left ∧ ClockGuarded right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          ClockGuarded left ∧ ClockGuarded right
      | .letp _ _ _ p => ClockGuarded p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ClockGuarded elseProcess ∧ ClockGuardedBranches branches
      | .send _ _ _ p | .recv _ _ _ p => ClockGuarded p
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def ClockGuardedBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          ClockGuarded (ChoiceBranch.continuation branch) ∧
            ClockGuardedBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Tail-regular recursion: a recursive call is sound as a backedge
    exactly when it does not retain a surrounding control context. -/
    def TailOccurrences (name : String) (tail : Prop) : Proc → Prop
      | .var _ other => other = name → tail
      | .seq _ left right =>
          TailOccurrences name False left ∧
            TailOccurrences name tail right
      | .par _ left right _ =>
          TailOccurrences name False left ∧
            TailOccurrences name False right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          TailOccurrences name tail left ∧
            TailOccurrences name tail right
      | .letp _ _ _ p => TailOccurrences name False p
      | .recur _ other body =>
          if other = name then True else TailOccurrences name tail body
      | .xoffer _ elseProcess branches =>
          TailOccurrences name tail elseProcess ∧
            TailBranchOccurrences name tail branches
      | .offer _ elseProcess branches =>
          TailOccurrences name tail elseProcess ∧
            TailBranchOccurrences name False branches
      | .send _ _ _ p | .recv _ _ _ p => TailOccurrences name False p
      | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def TailBranchOccurrences (name : String) (tail : Prop) :
        List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          TailOccurrences name tail (ChoiceBranch.continuation branch) ∧
            TailBranchOccurrences name tail rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Every binder is used only in tail positions, and every nested binder
    has the same property. -/
    def TailRecursive : Proc → Prop
      | .recur _ name body =>
          TailOccurrences name True body ∧ TailRecursive body
      | .seq _ left right | .par _ left right _ =>
          TailRecursive left ∧ TailRecursive right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          TailRecursive left ∧ TailRecursive right
      | .letp _ _ _ p => TailRecursive p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          TailRecursive elseProcess ∧ TailRecursiveBranches branches
      | .send _ _ _ p | .recv _ _ _ p => TailRecursive p
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def TailRecursiveBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          TailRecursive (ChoiceBranch.continuation branch) ∧
            TailRecursiveBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Per-cycle message linearity: messages that may occur before the
    first clock. -/
    def PrefixMessageIds : Proc → Finset MessageId
      | .send _ msg _ _ | .recv _ msg _ _ => {msg}
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => ∅
      | .recur _ _ body => PrefixMessageIds body
      | .par _ left right _ =>
          PrefixMessageIds left ∪ PrefixMessageIds right
      | .seq _ left right =>
          PrefixMessageIds left ∪
            if Pact.Proc.CanCompleteBeforeTock left then PrefixMessageIds right
            else ∅
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          PrefixMessageIds left ∪ PrefixMessageIds right
      | .letp _ _ _ p => PrefixMessageIds p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          PrefixMessageIds elseProcess ∪ BranchPrefixMessageIds branches
    termination_by process => sizeOf process

    def BranchPrefixMessageIds : List ChoiceBranch → Finset MessageId
      | [] => ∅
      | branch :: rest =>
          {ChoiceBranch.action branch |>.1} ∪
            PrefixMessageIds (ChoiceBranch.continuation branch) ∪
            BranchPrefixMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def SuffixMessageIds : Proc → Finset MessageId
      | .send _ msg _ _ | .recv _ msg _ _ => {msg}
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => ∅
      | .recur _ _ body => SuffixMessageIds body
      | .par _ left right _ =>
          SuffixMessageIds left ∪ SuffixMessageIds right
      | .seq _ left right =>
          SuffixMessageIds right ∪
            if Pact.Proc.CanCompleteBeforeTock right then SuffixMessageIds left
            else ∅
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          SuffixMessageIds left ∪ SuffixMessageIds right
      | .letp _ _ _ p => SuffixMessageIds p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          SuffixMessageIds elseProcess ∪ BranchSuffixMessageIds branches
    termination_by process => sizeOf process

    def BranchSuffixMessageIds : List ChoiceBranch → Finset MessageId
      | [] => ∅
      | branch :: rest =>
          SuffixMessageIds (ChoiceBranch.continuation branch) ∪
            (if Pact.Proc.CanCompleteBeforeTock (ChoiceBranch.continuation branch)
             then {ChoiceBranch.action branch |>.1} else ∅) ∪
            BranchSuffixMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def SameCycleMessageLinear : Proc → Prop
      | .seq _ left right =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right ∧
            Disjoint (SuffixMessageIds left) (PrefixMessageIds right)
      | .recur _ _ body =>
          SameCycleMessageLinear body ∧
            Disjoint (SuffixMessageIds body) (PrefixMessageIds body)
      | .par _ left right _ =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right
      | .letp _ _ _ p => SameCycleMessageLinear p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          SameCycleMessageLinear elseProcess ∧
            SameCycleMessageLinearBranches branches ∧
            ∀ branch ∈ branches,
              (ChoiceBranch.action branch).1 ∉ PrefixMessageIds elseProcess
      | .send _ _ _ p | .recv _ _ _ p => SameCycleMessageLinear p
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def SameCycleMessageLinearBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          SameCycleMessageLinear (ChoiceBranch.continuation branch) ∧
            (ChoiceBranch.action branch).1 ∉
              PrefixMessageIds (ChoiceBranch.continuation branch) ∧
            SameCycleMessageLinearBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Message names mentioned by a process, used by
    `ParallelMessageOwnership`'s sibling-disjointness conditions. -/
    def MessageIds : Proc → Finset MessageId
      | .send _ msg _ _ | .recv _ msg _ _ => {msg}
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => ∅
      | .recur _ _ body => MessageIds body
      | .par _ left right _ | .seq _ left right |
          .ifunfair _ _ left right | .iffair _ _ _ left right =>
          MessageIds left ∪ MessageIds right
      | .letp _ _ _ p => MessageIds p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          MessageIds elseProcess ∪ BranchMessageIds branches
    termination_by process => sizeOf process

    def BranchMessageIds : List ChoiceBranch → Finset MessageId
      | [] => ∅
      | branch :: rest =>
          {(ChoiceBranch.action branch).1} ∪
            MessageIds (ChoiceBranch.continuation branch) ∪
            BranchMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def MessageActions : Proc → Finset BareMessage
      | .send _ msg _ _ => {(msg, MessageDir.send)}
      | .recv _ msg _ _ => {(msg, MessageDir.recv)}
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => ∅
      | .recur _ _ body => MessageActions body
      | .par _ left right _ | .seq _ left right |
          .ifunfair _ _ left right | .iffair _ _ _ left right =>
          MessageActions left ∪ MessageActions right
      | .letp _ _ _ p => MessageActions p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          MessageActions elseProcess ∪ BranchMessageActions branches
    termination_by process => sizeOf process

    def BranchMessageActions : List ChoiceBranch → Finset BareMessage
      | [] => ∅
      | branch :: rest =>
          {ChoiceBranch.action branch} ∪
            MessageActions (ChoiceBranch.continuation branch) ∪
            BranchMessageActions rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def ProgressIds : Proc → Finset ProcId
      | .endp _ pid => {pid}
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .cycle _ => ∅
      | .recur _ _ body => ProgressIds body
      | .par _ left right _ | .seq _ left right |
          .ifunfair _ _ left right | .iffair _ _ _ left right =>
          ProgressIds left ∪ ProgressIds right
      | .letp _ _ _ p => ProgressIds p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ProgressIds elseProcess ∪ BranchProgressIds branches
    termination_by process => sizeOf process

    def BranchProgressIds : List ChoiceBranch → Finset ProcId
      | [] => ∅
      | branch :: rest =>
          ProgressIds (ChoiceBranch.continuation branch) ∪
            BranchProgressIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def FairChoiceIds : Proc → Finset BranchId
      | .iffair _ bid _ left right =>
          {bid} ∪ FairChoiceIds left ∪ FairChoiceIds right
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => ∅
      | .recur _ _ body => FairChoiceIds body
      | .par _ left right _ | .seq _ left right | .ifunfair _ _ left right =>
          FairChoiceIds left ∪ FairChoiceIds right
      | .letp _ _ _ p => FairChoiceIds p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          FairChoiceIds elseProcess ∪ BranchFairChoiceIds branches
    termination_by process => sizeOf process

    def BranchFairChoiceIds : List ChoiceBranch → Finset BranchId
      | [] => ∅
      | branch :: rest =>
          FairChoiceIds (ChoiceBranch.continuation branch) ∪
            BranchFairChoiceIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def ParallelProgressOwnership : Proc → Prop
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => True
      | .recur _ _ body => ParallelProgressOwnership body
      | .seq _ left right | .ifunfair _ _ left right |
          .iffair _ _ _ left right =>
          ParallelProgressOwnership left ∧ ParallelProgressOwnership right
      | .letp _ _ _ p => ParallelProgressOwnership p
      | .par _ left right _ =>
          Disjoint (ProgressIds left) (ProgressIds right) ∧
            ParallelProgressOwnership left ∧ ParallelProgressOwnership right
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ParallelProgressOwnership elseProcess ∧
            ParallelProgressOwnershipBranches branches
    termination_by process => sizeOf process

    def ParallelProgressOwnershipBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          ParallelProgressOwnership (ChoiceBranch.continuation branch) ∧
            Disjoint (ProgressIds (ChoiceBranch.continuation branch))
              (BranchProgressIds rest) ∧
            ParallelProgressOwnershipBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def ParallelFairChoiceOwnership : Proc → Prop
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => True
      | .recur _ _ body => ParallelFairChoiceOwnership body
      | .seq _ left right | .ifunfair _ _ left right |
          .iffair _ _ _ left right =>
          ParallelFairChoiceOwnership left ∧ ParallelFairChoiceOwnership right
      | .letp _ _ _ p => ParallelFairChoiceOwnership p
      | .par _ left right _ =>
          Disjoint (FairChoiceIds left) (FairChoiceIds right) ∧
            ParallelFairChoiceOwnership left ∧
              ParallelFairChoiceOwnership right
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ParallelFairChoiceOwnership elseProcess ∧
            ParallelFairChoiceOwnershipBranches branches
    termination_by process => sizeOf process

    def ParallelFairChoiceOwnershipBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          ParallelFairChoiceOwnership (ChoiceBranch.continuation branch) ∧
            Disjoint (FairChoiceIds (ChoiceBranch.continuation branch))
              (BranchFairChoiceIds rest) ∧
            ParallelFairChoiceOwnershipBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    def ParallelMessageOwnership : Proc → Prop
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => True
      | .recur _ _ body => ParallelMessageOwnership body
      | .seq _ left right | .ifunfair _ _ left right |
          .iffair _ _ _ left right =>
          ParallelMessageOwnership left ∧ ParallelMessageOwnership right
      | .letp _ _ _ p => ParallelMessageOwnership p
      | .par _ left right interface =>
          Disjoint (MessageIds left \ interface) (MessageIds right \ interface) ∧
            Disjoint (MessageActions left) (MessageActions right) ∧
            ParallelMessageOwnership left ∧ ParallelMessageOwnership right
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ParallelMessageOwnership elseProcess ∧
            ParallelMessageOwnershipBranches branches
    termination_by process => sizeOf process

    def ParallelMessageOwnershipBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          ParallelMessageOwnership (ChoiceBranch.continuation branch) ∧
            Disjoint ({(ChoiceBranch.action branch).1} ∪
                MessageIds (ChoiceBranch.continuation branch))
              (BranchMessageIds rest) ∧
            Disjoint ({ChoiceBranch.action branch} ∪
                MessageActions (ChoiceBranch.continuation branch))
              (BranchMessageActions rest) ∧
            ParallelMessageOwnershipBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- All synchronization interfaces occurring below a process. -/
    def ParallelInterfaces : Proc → Finset MessageId
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => ∅
      | .recur _ _ body => ParallelInterfaces body
      | .seq _ left right | .ifunfair _ _ left right |
          .iffair _ _ _ left right =>
          ParallelInterfaces left ∪ ParallelInterfaces right
      | .letp _ _ _ p => ParallelInterfaces p
      | .par _ left right interface =>
          interface ∪ ParallelInterfaces left ∪ ParallelInterfaces right
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          ParallelInterfaces elseProcess ∪ ParallelBranchInterfaces branches
    termination_by process => sizeOf process

    def ParallelBranchInterfaces : List ChoiceBranch → Finset MessageId
      | [] => ∅
      | branch :: rest =>
          ParallelInterfaces (ChoiceBranch.continuation branch) ∪
            ParallelBranchInterfaces rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- A parallel binder may not reuse an interface owned by an ancestor or
    a descendant binder. -/
    def InterfaceScoped : Proc → Prop
      | .send _ _ _ _ | .recv _ _ _ _ | .var _ _ | .skip _ | .endp _ _
      | .cycle _ => True
      | .recur _ _ body => InterfaceScoped body
      | .seq _ left right | .ifunfair _ _ left right |
          .iffair _ _ _ left right =>
          InterfaceScoped left ∧ InterfaceScoped right
      | .letp _ _ _ p => InterfaceScoped p
      | .par _ left right interface =>
          Disjoint interface
              (ParallelInterfaces left ∪ ParallelInterfaces right) ∧
            InterfaceScoped left ∧ InterfaceScoped right
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          InterfaceScoped elseProcess ∧ InterfaceScopedBranches branches
    termination_by process => sizeOf process

    def InterfaceScopedBranches : List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          InterfaceScoped (ChoiceBranch.continuation branch) ∧
            InterfaceScopedBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  mutual
    /-- Lexical recursion-binder hygiene: a nested binder must not reuse the
    name of an enclosing binder. -/
    def BinderHygienic (bound : List String) : Proc → Prop
      | .recur _ name body =>
          name ∉ bound ∧ BinderHygienic (name :: bound) body
      | .seq _ left right | .par _ left right _ =>
          BinderHygienic bound left ∧ BinderHygienic bound right
      | .ifunfair _ _ left right | .iffair _ _ _ left right =>
          BinderHygienic bound left ∧ BinderHygienic bound right
      | .letp _ _ _ p => BinderHygienic bound p
      | .xoffer _ elseProcess branches | .offer _ elseProcess branches =>
          BinderHygienic bound elseProcess ∧
            BinderHygienicBranches bound branches
      | .send _ _ _ p | .recv _ _ _ p => BinderHygienic bound p
      | .var _ _ | .skip _ | .endp _ _ | .cycle _ => True
    termination_by process => sizeOf process

    def BinderHygienicBranches (bound : List String) :
        List ChoiceBranch → Prop
      | [] => True
      | branch :: rest =>
          BinderHygienic bound (ChoiceBranch.continuation branch) ∧
            BinderHygienicBranches bound rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      first
      | (simp_wf; omega)
      | (have hBranch :
             sizeOf (ChoiceBranch.continuation branch) < sizeOf branch := by
           cases branch <;> simp [ChoiceBranch.continuation] <;> omega
         simp_wf
         omega)
  end

  /-- The paper's admissible regular processes, mirroring
  `ClosedGuardedRegular` on `PactType`. -/
  def ClosedGuardedRegular (process : Proc) : Prop :=
    Proc.AllVariablesBound [] [] process ∧
      BinderHygienic [] process ∧
      ClockGuarded process ∧
      TailRecursive process ∧
      SameCycleMessageLinear process ∧
      ParallelMessageOwnership process ∧
      ParallelProgressOwnership process ∧
      ParallelFairChoiceOwnership process ∧
      InterfaceScoped process

end Proc

/-- The paper's admissible processes: alphabet-well-formed and regular,
mirroring `AdmissibleType` (without a fixed-signature component, since a
process is checked against its own carried alphabet rather than an ambient
`TypeAlphabet`/automaton signature). -/
def AdmissibleProcess (process : Proc) : Prop :=
  process.AlphabetWellFormed ∧ Proc.ClosedGuardedRegular process

end
