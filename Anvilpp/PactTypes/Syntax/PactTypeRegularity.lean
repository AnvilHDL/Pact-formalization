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

  /-- `TailOccurrences` is monotone in its tail parameter: every clause either
  passes `tail` through unchanged or replaces it by a constant. -/
  theorem tailOccurrences_mono (name : String) {tail₁ tail₂ : Prop}
      (hImp : tail₁ → tail₂) :
      ∀ processType : PactType,
        TailOccurrences name tail₁ processType →
          TailOccurrences name tail₂ processType := by
    intro processType
    induction hSize : sizeOf processType using Nat.strong_induction_on
        generalizing processType with
    | _ n ih =>
        have hBranches : ∀ branches : List (BareMessage × PactType),
            sizeOf branches < n →
            TailBranchOccurrences name tail₁ branches →
            TailBranchOccurrences name tail₂ branches := by
          intro branches hBranchesSize hTail
          induction branches with
          | nil => simp [TailBranchOccurrences]
          | cons branch rest restIH =>
              rcases branch with ⟨action, branchType⟩
              have hFields : TailOccurrences name tail₁ branchType ∧
                  TailBranchOccurrences name tail₁ rest := by
                simpa only [TailBranchOccurrences] using hTail
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
              simpa only [TailBranchOccurrences] using
                And.intro (ih (sizeOf branchType) hBranchSize branchType rfl
                    hFields.1)
                  (restIH hRestSize hFields.2)
        intro hTail
        cases processType with
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [TailOccurrences]
        | var _ other =>
            simp only [TailOccurrences] at hTail ⊢
            exact fun hEq => hImp (hTail hEq)
        | recur _ binder body =>
            by_cases hBinder : binder = name
            · simp [TailOccurrences, hBinder]
            · have hBodySize : sizeOf body < n := by
                rw [← hSize]; simp_wf; omega
              simpa only [TailOccurrences, if_neg hBinder] using
                ih (sizeOf body) hBodySize body rfl
                  (by simpa only [TailOccurrences, if_neg hBinder] using hTail)
        | choice _ left right | fairChoice _ _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf left) hLeftSize left rfl hFields.1,
              ih (sizeOf right) hRightSize right rfl hFields.2⟩
        | seq _ left right =>
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨hFields.1, ih (sizeOf right) hRightSize right rfl hFields.2⟩
        | par _ left right _ =>
            simpa only [TailOccurrences] using hTail
        | xoffer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hBranchesSize : sizeOf branches < n := by
              rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
              hBranches branches hBranchesSize hFields.2⟩
        | offer _ elseType branches =>
            have hElseSize : sizeOf elseType < n := by
              rw [← hSize]; simp_wf; omega
            have hFields := hTail
            simp only [TailOccurrences] at hFields ⊢
            exact ⟨ih (sizeOf elseType) hElseSize elseType rfl hFields.1,
              hFields.2⟩

  /-- Branch-list form of `tailOccurrences_mono`. -/
  theorem tailBranchOccurrences_mono (name : String) {tail₁ tail₂ : Prop}
      (hImp : tail₁ → tail₂) :
      ∀ branches : List (BareMessage × PactType),
        TailBranchOccurrences name tail₁ branches →
          TailBranchOccurrences name tail₂ branches := by
    intro branches
    induction branches with
    | nil => simp [TailBranchOccurrences]
    | cons branch rest ih =>
        rcases branch with ⟨action, branchType⟩
        intro hTail
        have hFields : TailOccurrences name tail₁ branchType ∧
            TailBranchOccurrences name tail₁ rest := by
          simpa only [TailBranchOccurrences] using hTail
        simpa only [TailBranchOccurrences] using
          And.intro (tailOccurrences_mono name hImp branchType hFields.1)
            (ih hFields.2)

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
          | nil => simp [TailBranchOccurrences]
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
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [TailOccurrences]
        | var _ other =>
            simp only [AllVariablesBound] at hBound
            simp only [TailOccurrences]
            intro hEq
            subst other
            exact hNotMem hBound
        | recur _ binder body =>
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
        | choice _ left right =>
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
        | fairChoice _ _ left right =>
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
        | seq _ left right =>
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
        | par _ left right _ =>
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
        | xoffer _ elseType branches =>
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
        | offer _ elseType branches =>
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
        | var _ other =>
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound, List.mem_cons] at h ⊢
            rcases h with hEq | h
            · exact absurd hEq hTail
            · exact h
        | message _ _ _ | progress _ _ | tock _ | skip _ =>
            simp [AllVariablesBound]
        | recur _ other body =>
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
        | choice _ left right | fairChoice _ _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | seq _ left right =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | par _ left right _ =>
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            have hRightSize : sizeOf right < n := by
              rw [← hSize]; simp_wf; omega
            intro hTail h
            simp only [TailOccurrences] at hTail
            simp only [AllVariablesBound] at h ⊢
            exact ⟨ih (sizeOf left) hLeftSize bound left rfl hTail.1 h.1,
              ih (sizeOf right) hRightSize bound right rfl hTail.2 h.2⟩
        | xoffer _ elseType branches =>
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
        | offer _ elseType branches =>
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
          Disjoint (MessageIds left \ interface) (MessageIds right \ interface) ∧
            Disjoint (MessageActions left) (MessageActions right) ∧
            ParallelMessageOwnership left ∧ ParallelMessageOwnership right
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          ParallelMessageOwnership elseType ∧
            ParallelMessageOwnershipBranches branches
    termination_by processType => sizeOf processType

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
    all_goals
      simp_wf
      omega
  end

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

end

end Pact
