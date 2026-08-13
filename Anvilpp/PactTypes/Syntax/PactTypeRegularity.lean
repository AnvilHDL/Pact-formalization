import Anvilpp.PactTypes.Syntax.PactTypeSyntax

/-!
# PactType regularity predicates: clock guarding, tail occurrences, message linearity, interface scoping
-/

namespace Pact

noncomputable section

namespace PactType

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

  /-- A variable outside the ambient bound-name list has no free occurrence
  in a type whose variables are all bound by that list. -/
  theorem tailOccurrences_false_of_allVariablesBound_not_mem
      (name : String) (bound : List String) :
      ∀ processType,
        AllVariablesBound bound processType →
        name ∉ bound →
        TailOccurrences name False processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType bound with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            AllBranchVariablesBound bound branches →
            name ∉ bound →
            TailBranchOccurrences name False branches := by
          intro branches hBranchesSize hBound hNotMem
          induction branches with
          | nil => simp [AllBranchVariablesBound, TailBranchOccurrences]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              have hFields : AllVariablesBound bound branchType ∧
                  AllBranchVariablesBound bound rest := by
                simpa only [AllBranchVariablesBound] using hBound
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
              simp only [TailBranchOccurrences]
              exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                  hFields.1 hNotMem,
                restIH hRestSize hFields.2⟩
        intro hBound hNotMem
        cases processType with
        | message _ _ | progress _ | tock | skip =>
            simp [TailOccurrences]
        | var other =>
            simp only [AllVariablesBound] at hBound
            simp only [TailOccurrences]
            intro hEq
            subst other
            exact hNotMem hBound
        | recur binder body =>
            by_cases hBinder : binder = name
            · simp [TailOccurrences, hBinder]
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              have hBodyBound : AllVariablesBound (binder :: bound) body := by
                simpa only [AllVariablesBound] using hBound
              have hNameNotMem : name ∉ binder :: bound := by
                simp [Ne.symm hBinder, hNotMem]
              simpa only [TailOccurrences, if_neg hBinder] using
                ih (sizeOf body) hBodySize (binder :: bound) body rfl
                  hBodyBound hNameNotMem
        | choice left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | fairChoice _ left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | seq left right =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | par left right _ =>
            have hLeftSize : sizeOf left < n := by
              rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound left ∧
                AllVariablesBound bound right := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hFields.1 hNotMem,
              ih (sizeOf right) hRightSize bound right rfl hFields.2 hNotMem⟩
        | xoffer elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound elseType ∧
                AllBranchVariablesBound bound branches := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl
                hFields.1 hNotMem,
              hBranches branches hBranchesSize hFields.2 hNotMem⟩
        | offer elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields : AllVariablesBound bound elseType ∧
                AllBranchVariablesBound bound branches := by
              simpa only [AllVariablesBound] using hBound
            simp only [TailOccurrences]
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl
                hFields.1 hNotMem,
              hBranches branches hBranchesSize hFields.2 hNotMem⟩

  /- If `name` occurs nowhere in `processType` (in the unconditional,
  non-tail-restricted sense `TailOccurrences name False`), then `name` can be
  dropped from the bound-name list without affecting `AllVariablesBound`: every
  `.var` leaf that was relying on `name` being in the list must, since it
  cannot itself be `name`, already be covered by the rest of the list. -/
  theorem allVariablesBound_drop_of_tailOccurrences_false
      (name : String) (bound : List String) :
      ∀ processType,
        TailOccurrences name False processType →
        AllVariablesBound (name :: bound) processType →
          AllVariablesBound bound processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType bound with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            TailBranchOccurrences name False branches →
            AllBranchVariablesBound (name :: bound) branches →
              AllBranchVariablesBound bound branches := by
          intro branches hBranchesSize hTail h
          induction branches with
          | nil => simp [AllBranchVariablesBound]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              simp only [TailBranchOccurrences] at hTail
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
                have hHead : sizeOf rest < sizeOf ((action, branchType) :: rest) := by
                  simp_wf
                  omega
                omega
              exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                  hTail.1 h.1,
                restIH hRestSize hTail.2 h.2⟩
        cases processType with
        | var other =>
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound, List.mem_cons] at h ⊢
            rcases h with hEq | h
            · exact absurd hEq hTail
            · exact h
        | message _ _ | progress _ | tock | skip =>
            simp [AllVariablesBound]
        | recur other body =>
            have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            by_cases hEq : other = name
            · rw [hEq] at h ⊢
              exact allVariablesBound_mono
                (smaller := name :: name :: bound) (larger := name :: bound)
                (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact List.mem_cons_self
                  · exact hx)
                body h
            · rw [if_neg hEq] at hTail
              have hReorder : AllVariablesBound (name :: other :: bound) body :=
                allVariablesBound_mono
                  (smaller := other :: name :: bound)
                  (larger := name :: other :: bound)
                  (fun x hx => by
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact List.mem_cons_of_mem name List.mem_cons_self
                    · rcases List.mem_cons.mp hx with rfl | hx
                      · exact List.mem_cons_self
                      · exact List.mem_cons_of_mem name
                          (List.mem_cons_of_mem other hx))
                  body h
              exact ih (sizeOf body) hBodySize (other :: bound) body rfl
                hTail hReorder
        | choice left right | fairChoice _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | seq left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | par left right _ =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | xoffer elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl hTail.1
                h.1,
              hBranches branches hBranchesSize hTail.2 h.2⟩
        | offer elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf elseType) hElseSize bound elseType rfl hTail.1
                h.1,
              hBranches branches hBranchesSize hTail.2 h.2⟩

  /- Bulk form of `TailOccurrences`: every name in `names` individually
  satisfies the single-name predicate against the same `processType`. Lets
  one hypothesis carry "none of these ambient enclosing-binder names occur
  here" for an arbitrary-length list, propagated through a structural
  induction exactly the way a single `TailOccurrences` fact already is. -/
  def AllTailOccurrences (names : List String) (tail : Prop)
      (processType : PactType) : Prop :=
    ∀ n ∈ names, TailOccurrences n tail processType

  /- Bulk form of `allVariablesBound_drop_of_tailOccurrences_false`: every
  name in `names` can be dropped from the bound-name list at once, provided
  none of them occur in `processType`. -/
  theorem allVariablesBound_drop_of_allTailOccurrences_false
      (names bound : List String) (processType : PactType)
      (hTail : AllTailOccurrences names False processType)
      (hBound : AllVariablesBound (names ++ bound) processType) :
      AllVariablesBound bound processType := by
    induction names with
    | nil => simpa using hBound
    | cons n rest ih =>
        simp only [List.cons_append] at hBound
        have hRest : AllVariablesBound (rest ++ bound) processType :=
          allVariablesBound_drop_of_tailOccurrences_false n (rest ++ bound)
            processType (hTail n List.mem_cons_self) hBound
        exact ih (fun m hm => hTail m (List.mem_cons_of_mem n hm)) hRest

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

end

end Pact
