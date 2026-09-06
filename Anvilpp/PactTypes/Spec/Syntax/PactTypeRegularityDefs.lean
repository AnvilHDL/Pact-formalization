import Anvilpp.PactTypes.Proofs.Syntax.PactTypeSyntaxLemmas

namespace Pact

noncomputable section

namespace PactType

  /-! Every recursive backedge in a type is protected by a prior clock. -/
  mutual
    def ClockGuarded : PactType → Prop
      | .recur _ name body =>
          GuardedOccurrences name False body ∧ ClockGuarded body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          ClockGuarded left ∧ ClockGuarded right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ClockGuarded elseType ∧ ClockGuardedBranches branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
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
      | .var _ other => other = name → tail
      | .seq _ left right =>
          TailOccurrences name False left ∧
            TailOccurrences name tail right
      | .par _ left right _ =>
          TailOccurrences name False left ∧
            TailOccurrences name False right
      | .choice _ left right | .fairChoice _ _ left right =>
          TailOccurrences name tail left ∧
            TailOccurrences name tail right
      | .recur _ other body =>
          if other = name then True else TailOccurrences name tail body
      | .xoffer _ elseType branches =>
          TailOccurrences name tail elseType ∧
            TailBranchOccurrences name tail branches
      | .offer _ elseType branches =>
          TailOccurrences name tail elseType ∧
            TailBranchOccurrences name False branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ => True
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

  /- Bulk form of `TailOccurrences`: every name in `names` individually
  satisfies the single-name predicate against the same `processType`. Lets
  one hypothesis carry "none of these ambient enclosing-binder names occur
  here" for an arbitrary-length list, propagated through a structural
  induction exactly the way a single `TailOccurrences` fact already is. -/
  /- Every binder is used only in tail positions, and every nested binder has
  the same property.  This is the finite-control part of regularity. -/
  mutual
    def TailRecursive : PactType → Prop
      | .recur _ name body =>
          TailOccurrences name True body ∧ TailRecursive body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          TailRecursive left ∧ TailRecursive right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          TailRecursive elseType ∧ TailRecursiveBranches branches
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
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
      | .message _ _ _ | .progress _ _ | .skip _ => true
      | .tock _ | .var _ _ => false
      | .recur _ _ body => CanCompleteBeforeTock body
      | .choice _ left right | .fairChoice _ _ left right =>
          CanCompleteBeforeTock left || CanCompleteBeforeTock right
      | .seq _ left right | .par _ left right _ =>
          CanCompleteBeforeTock left && CanCompleteBeforeTock right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
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
      | .message _ msg _ => {msg}
      | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => PrefixMessageIds body
      | .choice _ left right | .fairChoice _ _ left right |
          .par _ left right _ =>
          PrefixMessageIds left ∪ PrefixMessageIds right
      | .seq _ left right =>
          PrefixMessageIds left ∪
            if CanCompleteBeforeTock left then PrefixMessageIds right else ∅
      | .xoffer _ elseType branches | .offer _ elseType branches =>
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
      | .message _ msg _ => {msg}
      | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => SuffixMessageIds body
      | .choice _ left right | .fairChoice _ _ left right |
          .par _ left right _ =>
          SuffixMessageIds left ∪ SuffixMessageIds right
      | .seq _ left right =>
          SuffixMessageIds right ∪
            if CanCompleteBeforeTock right then SuffixMessageIds left else ∅
      | .xoffer _ elseType branches | .offer _ elseType branches =>
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
      | .seq _ left right =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right ∧
            Disjoint (SuffixMessageIds left) (PrefixMessageIds right)
      | .recur _ _ body =>
          SameCycleMessageLinear body ∧
            Disjoint (SuffixMessageIds body) (PrefixMessageIds body)
      | .choice _ left right | .fairChoice _ _ left right |
          .par _ left right _ =>
          SameCycleMessageLinear left ∧ SameCycleMessageLinear right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          SameCycleMessageLinear elseType ∧
            SameCycleMessageLinearBranches branches ∧
            ∀ branch ∈ branches, branch.1.1 ∉ PrefixMessageIds elseType
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
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

  /-!
  ### Parallel message ownership

  `MessageIds` forgets polarity and records the message names mentioned by a
  type.  `MessageActions` keeps polarity and records the concrete message
  actions mentioned by a type.  Offer branch heads count as message actions,
  because choosing a branch observes that action before entering the branch
  body.

  `ParallelMessageOwnership` is the sibling-ownership condition used at
  parallel nodes.  Away from the synchronizing interface, siblings may not use
  the same message name.  At the polarized-action level, siblings may not own
  the same concrete action.  Thus an interface message may be shared only in
  complementary polarities, which is the shape needed by synchronized steps.
  -/
  mutual
    def MessageIds : PactType → Finset MessageId
      | .message _ msg _ => {msg}
      | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => MessageIds body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          MessageIds left ∪ MessageIds right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          MessageIds elseType ∪ BranchMessageIds branches
    termination_by processType => sizeOf processType

    def BranchMessageIds : List (BareMessage × PactType) → Finset MessageId
      | [] => ∅
      | (action, processType) :: rest =>
          {action.1} ∪ MessageIds processType ∪ BranchMessageIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-! Progress and fair-choice identifiers are also observable in labels.
  Parallel siblings therefore own disjoint sets of these identifiers. -/
  mutual
    def ProgressIds : PactType → Finset ProcId
      | .progress _ pid => {pid}
      | .message _ _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => ProgressIds body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          ProgressIds left ∪ ProgressIds right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ProgressIds elseType ∪ BranchProgressIds branches
    termination_by processType => sizeOf processType

    def BranchProgressIds : List (BareMessage × PactType) → Finset ProcId
      | [] => ∅
      | (_, processType) :: rest =>
          ProgressIds processType ∪ BranchProgressIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def FairChoiceIds : PactType → Finset BranchId
      | .fairChoice _ bid left right =>
          {bid} ∪ FairChoiceIds left ∪ FairChoiceIds right
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => FairChoiceIds body
      | .choice _ left right | .seq _ left right | .par _ left right _ =>
          FairChoiceIds left ∪ FairChoiceIds right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          FairChoiceIds elseType ∪ BranchFairChoiceIds branches
    termination_by processType => sizeOf processType

    def BranchFairChoiceIds : List (BareMessage × PactType) → Finset BranchId
      | [] => ∅
      | (_, processType) :: rest =>
          FairChoiceIds processType ∪ BranchFairChoiceIds rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /-! Progress and fair-choice identifiers are used linearly: sibling subterms
  declare disjoint identifiers, and a fair binder does not reuse one of its own
  body's.  A recursion body may repeat its identifiers across iterations. -/
  mutual
    def ProgressLinear : PactType → Prop
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => ProgressLinear body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right | .par _ left right _ =>
          ProgressLinear left ∧ ProgressLinear right ∧
            Disjoint (ProgressIds left) (ProgressIds right)
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ProgressLinear elseType ∧ ProgressLinearBranches branches ∧
            Disjoint (ProgressIds elseType) (BranchProgressIds branches)
    termination_by processType => sizeOf processType

    def ProgressLinearBranches : List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          ProgressLinear processType ∧
            Disjoint (ProgressIds processType) (BranchProgressIds rest) ∧
            ProgressLinearBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def FairChoiceLinear : PactType → Prop
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => FairChoiceLinear body
      | .fairChoice _ bid left right =>
          FairChoiceLinear left ∧ FairChoiceLinear right ∧
            Disjoint (FairChoiceIds left) (FairChoiceIds right) ∧
            bid ∉ FairChoiceIds left ∪ FairChoiceIds right
      | .choice _ left right | .seq _ left right | .par _ left right _ =>
          FairChoiceLinear left ∧ FairChoiceLinear right ∧
            Disjoint (FairChoiceIds left) (FairChoiceIds right)
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          FairChoiceLinear elseType ∧ FairChoiceLinearBranches branches ∧
            Disjoint (FairChoiceIds elseType) (BranchFairChoiceIds branches)
    termination_by processType => sizeOf processType

    def FairChoiceLinearBranches : List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          FairChoiceLinear processType ∧
            Disjoint (FairChoiceIds processType) (BranchFairChoiceIds rest) ∧
            FairChoiceLinearBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def ParallelProgressOwnership : PactType → Prop
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => ParallelProgressOwnership body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right =>
          ParallelProgressOwnership left ∧ ParallelProgressOwnership right
      | .par _ left right _ =>
          Disjoint (ProgressIds left) (ProgressIds right) ∧
            ParallelProgressOwnership left ∧ ParallelProgressOwnership right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ParallelProgressOwnership elseType ∧
            ParallelProgressOwnershipBranches branches
    termination_by processType => sizeOf processType

    def ParallelProgressOwnershipBranches :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          ParallelProgressOwnership processType ∧
            Disjoint (ProgressIds processType) (BranchProgressIds rest) ∧
            ParallelProgressOwnershipBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def ParallelFairChoiceOwnership : PactType → Prop
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => ParallelFairChoiceOwnership body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right =>
          ParallelFairChoiceOwnership left ∧ ParallelFairChoiceOwnership right
      | .par _ left right _ =>
          Disjoint (FairChoiceIds left) (FairChoiceIds right) ∧
            ParallelFairChoiceOwnership left ∧ ParallelFairChoiceOwnership right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ParallelFairChoiceOwnership elseType ∧
            ParallelFairChoiceOwnershipBranches branches
    termination_by processType => sizeOf processType

    def ParallelFairChoiceOwnershipBranches :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          ParallelFairChoiceOwnership processType ∧
            Disjoint (FairChoiceIds processType) (BranchFairChoiceIds rest) ∧
            ParallelFairChoiceOwnershipBranches rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  mutual
    def ParallelMessageOwnership : PactType → Prop
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => ParallelMessageOwnership body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right =>
          ParallelMessageOwnership left ∧ ParallelMessageOwnership right
      | .par _ left right interface =>
          MessageIds left ∩ MessageIds right ⊆ interface ∧
            ParallelMessageOwnership left ∧ ParallelMessageOwnership right
      | .xoffer _ elseType branches =>
          ParallelMessageOwnership elseType ∧
            ParallelMessageOwnershipBodies branches
      | .offer _ elseType branches =>
          ParallelMessageOwnership elseType ∧
            ParallelMessageOwnershipBodies branches
    termination_by processType => sizeOf processType

    def ParallelMessageOwnershipBodies :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (_, processType) :: rest =>
          ParallelMessageOwnership processType ∧
            ParallelMessageOwnershipBodies rest
    termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      simp_wf
      omega
  end

  /- Pointwise ownership together with the separation a conjunctive offer's
  branches enjoy.  This bundle is what the branch product consumes. -/
  def ParallelMessageOwnershipBranches :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (action, processType) :: rest =>
        ParallelMessageOwnership processType ∧
          Disjoint ({action.1} ∪ MessageIds processType) (BranchMessageIds rest) ∧
          Disjoint ({action} ∪ MessageActions processType)
            (BranchMessageActions rest) ∧
          ParallelMessageOwnershipBranches rest
  termination_by branches => sizeOf branches
  decreasing_by
    simp_wf
    omega

  /- All synchronization interfaces occurring below a type.  This is used by
  the compositional proof only; it does not alter operational future offers. -/
  mutual
    def ParallelInterfaces : PactType → Finset MessageId
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => ∅
      | .recur _ _ body => ParallelInterfaces body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right =>
          ParallelInterfaces left ∪ ParallelInterfaces right
      | .par _ left right interface =>
          interface ∪ ParallelInterfaces left ∪ ParallelInterfaces right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
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
      | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
      | .recur _ _ body => InterfaceScoped body
      | .choice _ left right | .seq _ left right |
          .fairChoice _ _ left right =>
          InterfaceScoped left ∧ InterfaceScoped right
      | .par _ left right interface =>
          Disjoint interface
              (ParallelInterfaces left ∪ ParallelInterfaces right) ∧
            InterfaceScoped left ∧ InterfaceScoped right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
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

end PactType

/-- Message identifiers declared by an alphabet. -/
def PactTypeAlphabet.messageIds (alphabet : PactTypeAlphabet) :
    Finset MessageId :=
  alphabet.actions.image Prod.fst

/- The second interface-scoping clause: every subterm's own alphabet declares
none of the interfaces occurring in that subterm. -/
mutual
  def PactType.InterfaceAlphabetScoped : PactType → Prop
    | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .recur alphabet _ body =>
        Disjoint (PactTypeAlphabet.messageIds alphabet)
            (PactType.ParallelInterfaces body) ∧
          PactType.InterfaceAlphabetScoped body
    | .choice alphabet left right | .seq alphabet left right |
        .fairChoice alphabet _ left right =>
        Disjoint (PactTypeAlphabet.messageIds alphabet)
            (PactType.ParallelInterfaces left ∪
              PactType.ParallelInterfaces right) ∧
          PactType.InterfaceAlphabetScoped left ∧
          PactType.InterfaceAlphabetScoped right
    | .par alphabet left right interface =>
        Disjoint (PactTypeAlphabet.messageIds alphabet)
            (interface ∪ PactType.ParallelInterfaces left ∪
              PactType.ParallelInterfaces right) ∧
          PactType.InterfaceAlphabetScoped left ∧
          PactType.InterfaceAlphabetScoped right
    | .xoffer alphabet elseType branches
    | .offer alphabet elseType branches =>
        Disjoint (PactTypeAlphabet.messageIds alphabet)
            (PactType.ParallelInterfaces elseType ∪
              PactType.ParallelBranchInterfaces branches) ∧
          PactType.InterfaceAlphabetScoped elseType ∧
          PactType.InterfaceAlphabetScopedBranches branches
  termination_by processType => sizeOf processType

  def PactType.InterfaceAlphabetScopedBranches :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        PactType.InterfaceAlphabetScoped processType ∧
          PactType.InterfaceAlphabetScopedBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- A node's own alphabet declares none of the interfaces below it. -/
theorem PactType.InterfaceAlphabetScoped.avoids :
    ∀ {processType : PactType}, processType.InterfaceAlphabetScoped →
      ∀ action ∈ processType.alphabet.actions,
        action.1 ∉ PactType.ParallelInterfaces processType := by
  intro processType hScoped action hAction hIn
  cases processType with
  | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
      simp [PactType.ParallelInterfaces] at hIn
  | recur _ _ _ | choice _ _ _ | seq _ _ _ | fairChoice _ _ _ _
  | par _ _ _ _ | xoffer _ _ _ | offer _ _ _ =>
      simp only [PactType.ParallelInterfaces] at hIn
      simp only [PactType.InterfaceAlphabetScoped] at hScoped
      simp only [PactType.alphabet] at hAction
      exact Finset.disjoint_left.mp hScoped.1
        (Finset.mem_image.mpr ⟨action, hAction, rfl⟩) hIn

/- Every conjunctive offer keeps its branches on disjoint message identifiers,
counting each branch's head together with its body. -/
mutual
  def PactType.ConjunctiveMessageOwnership : PactType → Prop
    | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .recur _ _ body => PactType.ConjunctiveMessageOwnership body
    | .choice _ left right | .seq _ left right | .fairChoice _ _ left right
    | .par _ left right _ =>
        PactType.ConjunctiveMessageOwnership left ∧
          PactType.ConjunctiveMessageOwnership right
    | .xoffer _ elseType branches =>
        PactType.ConjunctiveMessageOwnership elseType ∧
          PactType.ConjunctiveMessageOwnershipBodies branches
    | .offer _ elseType branches =>
        PactType.ConjunctiveMessageOwnership elseType ∧
          PactType.ConjunctiveMessageOwnershipBranches branches
  termination_by processType => sizeOf processType

  /- Branch bodies of an exclusive offer carry the condition but impose no
  pairwise disjointness of their own. -/
  def PactType.ConjunctiveMessageOwnershipBodies :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        PactType.ConjunctiveMessageOwnership processType ∧
          PactType.ConjunctiveMessageOwnershipBodies rest
  termination_by branches => sizeOf branches

  def PactType.ConjunctiveMessageOwnershipBranches :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (action, processType) :: rest =>
        PactType.ConjunctiveMessageOwnership processType ∧
          Disjoint ({action.1} ∪ PactType.MessageIds processType)
            (PactType.BranchMessageIds rest) ∧
          PactType.ConjunctiveMessageOwnershipBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/-- Two conjunctive-offer branches use disjoint declarations: disjoint head
actions and continuation actions, disjoint progress identifiers, and disjoint
fair-choice identifiers.  This is what lets the branches be handed disjoint
parts of one alphabet. -/
def BranchDeclarationsDisjoint (b1 b2 : BareMessage × PactType) : Prop :=
  Disjoint ({b1.1} ∪ PactType.MessageActions b1.2)
      ({b2.1} ∪ PactType.MessageActions b2.2) ∧
    Disjoint (PactType.ProgressIds b1.2) (PactType.ProgressIds b2.2) ∧
    Disjoint (PactType.FairChoiceIds b1.2) (PactType.FairChoiceIds b2.2)

mutual
  /-- Every conjunctive offer below a type has branches owning disjoint
  declarations.  This is what an admissible source type's ownership invariants
  give, and what the generated branch product consumes.  Only `.offer` builds
  that product, so only `.offer` carries the pairwise condition: an `.xoffer`
  selects one branch and discards the rest, and imposing disjointness there
  would not survive unfolding a binder in a branch's tail position. -/
  def PactType.OfferBranchesDisjoint : PactType → Prop
    | .message _ _ _ | .progress _ _ | .tock _ | .skip _ | .var _ _ => True
    | .recur _ _ body => OfferBranchesDisjoint body
    | .choice _ left right | .seq _ left right | .fairChoice _ _ left right |
        .par _ left right _ =>
        OfferBranchesDisjoint left ∧ OfferBranchesDisjoint right
    | .xoffer _ elseType branches =>
        OfferBranchesDisjoint elseType ∧ OfferBranchesDisjointBranches branches
    | .offer _ elseType branches =>
        OfferBranchesDisjoint elseType ∧
          List.Pairwise BranchDeclarationsDisjoint branches ∧
          OfferBranchesDisjointBranches branches
  termination_by processType => sizeOf processType

  def PactType.OfferBranchesDisjointBranches :
      List (BareMessage × PactType) → Prop
    | [] => True
    | (_, processType) :: rest =>
        OfferBranchesDisjoint processType ∧ OfferBranchesDisjointBranches rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end

end Pact
