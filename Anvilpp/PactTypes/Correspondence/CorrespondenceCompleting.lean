import Anvilpp.PactTypes.Correspondence.CorrespondenceSequence

/-!
# Completing correspondence for choice/fairChoice/parallel/xoffer/offer; parallel future correspondence
-/

namespace Pact

noncomputable section

private theorem buildChoiceAutomaton_root_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) :
    TypeAutomatonState.root ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      left.initial ∈ left.completing ∨ right.initial ∈ right.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

private theorem buildChoiceAutomaton_left_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      state ∈ left.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

private theorem buildChoiceAutomaton_right_mem_completing_iff
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (leftLabel rightLabel : TypeLabel) (state : TypeAutomatonState) :
    childState 1 state ∈
        (buildChoiceAutomaton signature left right leftLabel rightLabel).completing ↔
      state ∈ right.completing := by
  classical
  by_cases hComplete : left.initial ∈ left.completing ∨
      right.initial ∈ right.completing <;>
    simp [buildChoiceAutomaton, finishAutomatonFragment, childCompleting,
      childState, hComplete]

/-- Ordinary choice completes optimistically when either branch completes. -/
theorem compilationCompletingCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    CompilationCompletingCorrect signature (.choice left right) := by
  intro state residual hRelated
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
  have hLeftInitial : leftFragment.initial ∈ leftFragment.completing ↔
      left.CanCompleteBeforeTock = true := by
    have hCanonical := hLeft _ left
      (compileType_initial_relation_of_canonical signature left
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hLeftCanonical))
    simpa [leftFragment, hLeftStable, compileType] using hCanonical
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hCanonical := hRight _ right
      (compileType_initial_relation_of_canonical signature right
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hRightCanonical))
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | choice_source =>
      rw [buildChoiceAutomaton_root_mem_completing_iff]
      simpa [PactType.CanCompleteBeforeTock] using
        (or_congr hLeftInitial hRightInitial)
  | choice_left _ _ _ childQ hChildRelated =>
      have hCanonical := hLeft childQ _ hChildRelated
      have hChild : childQ ∈ leftFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [leftFragment, hLeftStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_left_mem_completing_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent childQ).trans
            hChild))
  | choice_right _ _ _ childQ hChildRelated =>
      have hCanonical := hRight childQ _ hChildRelated
      have hChild : childQ ∈ rightFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [rightFragment, hRightStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_right_mem_completing_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent childQ).trans
            hChild))

/-- Fair choice has the same completion predicate as ordinary choice; its
selection labels do not affect same-cycle completion. -/
theorem compilationCompletingCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    CompilationCompletingCorrect signature (.fairChoice bid left right) := by
  intro state residual hRelated
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
  have hLeftInitial : leftFragment.initial ∈ leftFragment.completing ↔
      left.CanCompleteBeforeTock = true := by
    have hCanonical := hLeft _ left
      (compileType_initial_relation_of_canonical signature left
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hLeftCanonical))
    simpa [leftFragment, hLeftStable, compileType] using hCanonical
  have hRightInitial : rightFragment.initial ∈ rightFragment.completing ↔
      right.CanCompleteBeforeTock = true := by
    have hCanonical := hRight _ right
      (compileType_initial_relation_of_canonical signature right
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hRightCanonical))
    simpa [rightFragment, hRightStable, compileType] using hCanonical
  have hFragment :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature leftFragment rightFragment
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | fair_source =>
      rw [buildChoiceAutomaton_root_mem_completing_iff]
      simpa [PactType.CanCompleteBeforeTock] using
        (or_congr hLeftInitial hRightInitial)
  | fair_left _ _ _ _ childQ hChildRelated =>
      have hCanonical := hLeft childQ _ hChildRelated
      have hChild : childQ ∈ leftFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [leftFragment, hLeftStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_left_mem_completing_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) childQ).trans hChild))
  | fair_right _ _ _ _ childQ hChildRelated =>
      have hCanonical := hRight childQ _ hChildRelated
      have hChild : childQ ∈ rightFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        simpa [rightFragment, hRightStable] using hCanonical
      exact (by simpa [childState] using
        ((buildChoiceAutomaton_right_mem_completing_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) childQ).trans hChild))

/-- Parallel completion is the conjunction of the represented child
completion predicates, matching the syntax-level optimistic analysis. -/
theorem compilationCompletingCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeft : CompilationCompletingCorrect signature left)
    (hRight : CompilationCompletingCorrect signature right) :
    CompilationCompletingCorrect signature (.par left right interface) := by
  intro state residual hRelated
  cases hRelated with
  | parallel _ _ leftResidual rightResidual _ leftQ rightQ
      hLeftRelated hRightRelated _ =>
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
      have hLeftChild : leftQ ∈ leftFragment.completing ↔
          leftResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hLeft leftQ leftResidual hLeftRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightChild : rightQ ∈ rightFragment.completing ↔
          rightResidual.CanCompleteBeforeTock = true := by
        have hCanonical := hRight rightQ rightResidual hRightRelated
        simpa [rightFragment, hRightStable] using hCanonical
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
      simpa [buildParallelAutomaton, finishAutomatonFragment,
        leftFragment, rightFragment, PactType.CanCompleteBeforeTock] using
          (and_congr hLeftChild hRightChild)
  | parallel_fuse _ _ _ leftQ rightQ hLeftRelated hRightRelated =>
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
      have hLeftChild : leftQ ∈ leftFragment.completing ↔
          (PactType.skip).CanCompleteBeforeTock = true := by
        have hCanonical := hLeft leftQ .skip hLeftRelated
        simpa [leftFragment, hLeftStable] using hCanonical
      have hRightChild : rightQ ∈ rightFragment.completing ↔
          (PactType.skip).CanCompleteBeforeTock = true := by
        have hCanonical := hRight rightQ .skip hRightRelated
        simpa [rightFragment, hRightStable] using hCanonical
      simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
      simpa [buildParallelAutomaton, finishAutomatonFragment,
        leftFragment, rightFragment, PactType.CanCompleteBeforeTock] using
          (and_congr hLeftChild hRightChild)

/-! ### Offer completion correspondence -/

theorem branchCanCompleteBeforeTock_eq_any
    (branches : List (BareMessage × PactType)) :
    PactType.BranchCanCompleteBeforeTock branches =
      branches.any (fun branch => branch.2.CanCompleteBeforeTock) := by
  induction branches with
  | nil => simp [PactType.BranchCanCompleteBeforeTock]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.BranchCanCompleteBeforeTock, ih]

/-- Exclusive offers inherit optimistic completion from the else continuation
or any branch continuation, and tagged continuation states inherit the exact
child predicate. -/
theorem compilationCompletingCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : CompilationCompletingCorrect signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
        (index : Nat), branches[index]? = some (action, branchType) →
          CompilationCompletingCorrect signature branchType)
    (hElseCanonical : elseType.EntryCanonical) :
    CompilationCompletingCorrect signature (.xoffer elseType branches) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseInitial : elseFragment.initial ∈ elseFragment.completing ↔
      elseType.CanCompleteBeforeTock = true := by
    have hCanonical := hElse _ elseType
      (compileType_initial_relation_of_canonical signature elseType
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hElseCanonical))
    simpa [elseFragment, hElseStable, compileType] using hCanonical
  simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  change state ∈
      (buildExclusiveOfferAutomaton signature branches elseFragment
        branchAutomata).completing ↔ residual.CanCompleteBeforeTock = true
  cases hRelated with
  | xoffer_source =>
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      have hNotElse : TypeAutomatonState.root ∉
          childCompleting 0 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hNotIndexed := root_not_mem_indexedFragmentCompleting branchAutomata
      have hCondition :
          (elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) = true) ↔
            (PactType.xoffer elseType branches).CanCompleteBeforeTock = true := by
        simp only [PactType.CanCompleteBeforeTock]
        rw [branchCanCompleteBeforeTock_eq_any branches]
        simp [hElseInitial]
      constructor
      · rintro ((hHeader | hElseMember) | hIndexed)
        · by_cases hConditionValue :
              elseFragment.initial ∈ elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true
          · exact hCondition.mp hConditionValue
          · rw [if_neg hConditionValue] at hHeader
            have hFalse : False := by simpa using hHeader
            exact hFalse.elim
        · exact (hNotElse hElseMember).elim
        · exact (hNotIndexed hIndexed).elim
      · intro hResidual
        left
        left
        have hConditionValue := hCondition.mpr hResidual
        rw [if_pos hConditionValue]
        exact Finset.mem_singleton_self _
  | xoffer_else _ _ _ childQ hChildRelated =>
      have hChild : childQ ∈ elseFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hElse childQ residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hNotHeader : childState 0 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotIndexed := child_zero_not_mem_indexedFragmentCompleting
        branchAutomata childQ
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hElseMember) | hIndexed)
        · exact (hNotHeader hHeader).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hElseMember
        · exact (hNotIndexed hIndexed).elim
      · intro hResidual
        left
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual
  | xoffer_branch _ branchType _ _ action index childQ hEntry hChildRelated =>
      have hBranchMem : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
        apply le_trans
        · exact typeCompilationFuel_le_typeBranchCompilationFuel branches
            (action, branchType) hBranchMem
        · simp [fuel]
      have hBranchStable : compileTypeFuel signature fuel branchType =
          compileTypeFuel signature (typeCompilationFuel branchType)
            branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hChild : childQ ∈
          (compileTypeFuel signature fuel branchType).completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hBranches action branchType index hEntry
          childQ residual hChildRelated
        simpa [hBranchStable] using hCanonical
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, compileTypeFuel signature fuel branchType) := by
        simp [branchAutomata, hEntry]
      have hIndexed := childState_mem_indexedFragmentCompleting_iff
        branchAutomata index
          (action, compileTypeFuel signature fuel branchType)
          hAutomatonEntry childQ
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      have hNotHeader : childState (index + 1) childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotElse : childState (index + 1) childQ ∉
          childCompleting 0 elseFragment := by
        intro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, hOther, hEquality⟩
        have hImpossible : 0 = index + 1 := by injection hEquality
        omega
      constructor
      · rintro ((hHeader | hElseMember) | hIndexedMember)
        · exact (hNotHeader hHeader).elim
        · exact (hNotElse hElseMember).elim
        · exact hChild.mp (hIndexed.mp hIndexedMember)
      · intro hResidual
        right
        exact hIndexed.mpr (hChild.mpr hResidual)

/-- Completion correctness for the generated conjunction used by `.offer`.
This is proved directly over the branch list, avoiding a non-structural
recursive call on `parallelTypeBranches`. -/
theorem compilationCompletingCorrect_parallelTypeBranches
    (signature : TypeAlphabet) : ∀ branches,
    (∀ (action : BareMessage) (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType) →
    CompilationCompletingCorrect signature (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simpa [parallelTypeBranches] using
        (compilationCompletingCorrect_skip signature)
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hBranches
      have hHead : CompilationCompletingCorrect signature branchType :=
        hBranches action branchType 0 (by simp)
      have hSingleton : CompilationCompletingCorrect signature
          (singletonTypeXOffer (action, branchType)) := by
        apply compilationCompletingCorrect_xoffer signature .skip
          [(action, branchType)]
        · exact compilationCompletingCorrect_skip signature
        · intro selected selectedType index hEntry
          have hIndex : index = 0 := by
            simpa using (List.getElem?_eq_some_iff.mp hEntry).1
          subst index
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          exact hHead
        · simp [PactType.EntryCanonical]
      cases rest with
      | nil =>
          simpa [parallelTypeBranches] using hSingleton
      | cons next tail =>
          have hRest : ∀ (selected : BareMessage) (selectedType : PactType)
              (index : Nat),
              (next :: tail)[index]? = some (selected, selectedType) →
                CompilationCompletingCorrect signature selectedType := by
            intro selected selectedType index hEntry
            exact hBranches selected selectedType (index + 1) (by
              simpa using hEntry)
          have hTail := ih hRest
          simpa [parallelTypeBranches] using
            (compilationCompletingCorrect_parallel signature
              (singletonTypeXOffer (action, branchType))
              (parallelTypeBranches (next :: tail)) ∅ hSingleton hTail)

/-- Conjunctive offers inherit optimistic completion from the else
continuation or any branch continuation.  Tagged states inherit the exact
completion predicate of the generated conjunction or else child. -/
theorem compilationCompletingCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElse : CompilationCompletingCorrect signature elseType)
    (hConjunction : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationCompletingCorrect signature
          (parallelTypeBranchesSelecting selected branches))
    (hElseCanonical : elseType.EntryCanonical) :
    CompilationCompletingCorrect signature (.offer elseType branches) := by
  intro state residual hRelated
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseInitial : elseFragment.initial ∈ elseFragment.completing ↔
      elseType.CanCompleteBeforeTock = true := by
    have hCanonical := hElse _ elseType
      (compileType_initial_relation_of_canonical signature elseType
        (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
          hElseCanonical))
    simpa [elseFragment, hElseStable, compileType] using hCanonical
  simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  change state ∈
      (buildSelectedConjunctiveOfferAutomaton signature branches elseFragment
        selectedConjunctions).completing ↔ residual.CanCompleteBeforeTock = true
  cases hRelated with
  | offer_source =>
      have hNotConjunction : TypeAutomatonState.root ∉
          indexedFragmentCompleting selectedConjunctions := by
        rintro hMember
        simp only [indexedFragmentCompleting, mem_foldl_union_iff] at hMember
        rcases hMember with hEmpty | ⟨indexed, _, hMember⟩
        · simp at hEmpty
        · simp only [childCompleting, Finset.mem_image] at hMember
          rcases hMember with ⟨child, _, hEquality⟩
          cases hEquality
      have hNotElse : TypeAutomatonState.root ∉
          childCompleting 0 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hCondition :
          (elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch =>
                branch.2.CanCompleteBeforeTock) = true) ↔
            (PactType.offer elseType branches).CanCompleteBeforeTock = true := by
        simp only [PactType.CanCompleteBeforeTock]
        rw [branchCanCompleteBeforeTock_eq_any branches]
        simp [hElseInitial]
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hElseMember) | hConjunctionMember)
        · by_cases hValue :
              elseFragment.initial ∈ elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true
          · exact hCondition.mp hValue
          · rw [if_neg hValue] at hHeader
            simp at hHeader
        · exact (hNotElse hElseMember).elim
        · exact (hNotConjunction hConjunctionMember).elim
      · intro hResidual
        left
        left
        have hValue := hCondition.mpr hResidual
        rw [if_pos hValue]
        exact Finset.mem_singleton_self _
  | offer_branches _ childResidual _ selected index childQ hEntry hChildRelated =>
      have hEntryMem : selected ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hSelectedFuel : TypeCompilationFuelSufficient
          (parallelTypeBranchesSelecting selected branches) fuel := by
        simp only [TypeCompilationFuelSufficient,
          typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
        exact le_max_right _ _
      let selectedFragment := compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)
      have hSelectedStable : selectedFragment = compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature
          (parallelTypeBranchesSelecting selected branches) hSelectedFuel
          (typeCompilationFuel_sufficient _)
      have hAutomatonEntry : selectedConjunctions[index]? =
          some (selected.1, selectedFragment) := by
        simp [selectedConjunctions, selectedFragment, hEntry]
      have hChild : childQ ∈ selectedFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hConjunction selected index hEntry childQ residual
          hChildRelated
        simpa [selectedFragment, hSelectedStable] using hCanonical
      have hNotHeader : childState (index + 1) childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotElse : childState (index + 1) childQ ∉
          childCompleting 0 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, _, hEquality⟩
        have hImpossible : (0 : Nat) = index + 1 := by injection hEquality
        omega
      have hConjunctionMember : childState (index + 1) childQ ∈
          indexedFragmentCompleting selectedConjunctions ↔
            childQ ∈ selectedFragment.completing := by
        rw [indexedFragmentCompleting, mem_foldl_union_iff]
        constructor
        · rintro (hEmpty | ⟨indexed, hIndexed, hMember⟩)
          · simp at hEmpty
          simp only [childCompleting, Finset.mem_image] at hMember
          rcases hMember with ⟨other, hOther, hEquality⟩
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hIndexedEntry : selectedConjunctions[indexed.2]? =
              some indexed.1 := by
            rw [List.getElem?_eq_getElem hBound, hValue]
          have hIndexEq : indexed.2 = index := by
            simp only [childState, TypeAutomatonState.child.injEq] at hEquality
            omega
          have hOtherEq : other = childQ := by
            simp only [childState, TypeAutomatonState.child.injEq] at hEquality
            exact hEquality.2
          rw [hIndexEq] at hIndexedEntry
          rw [hIndexedEntry] at hAutomatonEntry
          have hIndexedValue : indexed.1 = (selected.1, selectedFragment) :=
            Option.some.inj hAutomatonEntry
          rw [hIndexedValue] at hOther
          rw [hOtherEq] at hOther
          exact hOther
        · intro hMember
          rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
            ⟨hBound, hValue⟩
          have hZipEntry : ((selected.1, selectedFragment), index) ∈
              selectedConjunctions.zipIdx := by
            have hZipBound : index < selectedConjunctions.zipIdx.length := by
              simpa using hBound
            have hMemberZip := List.getElem_mem hZipBound
            have hAt := List.getElem_zipIdx (l := selectedConjunctions)
              (i := index) (j := 0) hZipBound
            simp only [zero_add] at hAt
            rw [hAt, hValue] at hMemberZip
            exact hMemberZip
          refine Or.inr ⟨((selected.1, selectedFragment), index), hZipEntry, ?_⟩
          simpa [childCompleting, childState] using hMember
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hElseMember) | hConjMember)
        · exact (hNotHeader hHeader).elim
        · exact (hNotElse hElseMember).elim
        · exact hChild.mp (hConjunctionMember.mp hConjMember)
      · intro hResidual
        right
        exact hConjunctionMember.mpr (hChild.mpr hResidual)
  | offer_else _ childResidual _ childQ hChildRelated =>
      have hChild : childQ ∈ elseFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hElse childQ residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hNotHeader : childState 0 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotConjunction : childState 0 childQ ∉
          indexedFragmentCompleting selectedConjunctions := by
        rintro hMember
        simp only [indexedFragmentCompleting, mem_foldl_union_iff] at hMember
        rcases hMember with hEmpty | ⟨indexed, _, hMember⟩
        · simp at hEmpty
        · simp only [childCompleting, Finset.mem_image] at hMember
          rcases hMember with ⟨other, _, hEquality⟩
          have hImpossible : indexed.2 + 1 = 0 := by injection hEquality
          omega
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hElseMember) | hConjMember)
        · exact (hNotHeader hHeader).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hElseMember
        · exact (hNotConjunction hConjMember).elim
      · intro hResidual
        left
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual

/-
  intro state residual hRelated
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel, conjunctionType]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hConjunctionStable : conjunction = compileTypeFuel signature
      (typeCompilationFuel conjunctionType) conjunctionType :=
    compileTypeFuel_eq_of_sufficient signature conjunctionType
      hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  have hElseInitial : elseFragment.initial ∈ elseFragment.completing ↔
      elseType.CanCompleteBeforeTock = true := by
    have hCanonical := hElse _ elseType
      (compileType_initial_relation signature elseType)
    simpa [elseFragment, hElseStable, compileType] using hCanonical
  simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  change state ∈
      (buildConjunctiveOfferAutomaton signature branches elseFragment
        conjunction).completing ↔ residual.CanCompleteBeforeTock = true
  cases hRelated with
  | offer_source =>
      have hNotConjunction : TypeAutomatonState.root ∉
          childCompleting 0 conjunction := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hNotElse : TypeAutomatonState.root ∉
          childCompleting 1 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨child, _, hEquality⟩
        cases hEquality
      have hCondition :
          (elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch =>
                branch.2.CanCompleteBeforeTock) = true) ↔
            (PactType.offer elseType branches).CanCompleteBeforeTock = true := by
        simp only [PactType.CanCompleteBeforeTock]
        rw [branchCanCompleteBeforeTock_eq_any branches]
        simp [hElseInitial]
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · by_cases hValue :
              elseFragment.initial ∈ elseFragment.completing ∨
                branches.any (fun branch =>
                  branch.2.CanCompleteBeforeTock) = true
          · exact hCondition.mp hValue
          · rw [if_neg hValue] at hHeader
            simp at hHeader
        · exact (hNotConjunction hConjunctionMember).elim
        · exact (hNotElse hElseMember).elim
      · intro hResidual
        left
        have hValue := hCondition.mpr hResidual
        rw [if_pos hValue]
        exact Or.inl (Finset.mem_singleton_self _)
  | offer_branches _ childResidual _ childQ hChildRelated =>
      have hChild : childQ ∈ conjunction.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hConjunction childQ residual hChildRelated
        simpa [conjunction, conjunctionType, hConjunctionStable]
          using hCanonical
      have hNotHeader : childState 0 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotElse : childState 0 childQ ∉ childCompleting 1 elseFragment := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, _, hEquality⟩
        have hImpossible : 1 = 0 := by injection hEquality
        omega
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · exact (hNotHeader hHeader).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hConjunctionMember
        · exact (hNotElse hElseMember).elim
      · intro hResidual
        left
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual
  | offer_else _ childResidual _ childQ hChildRelated =>
      have hChild : childQ ∈ elseFragment.completing ↔
          residual.CanCompleteBeforeTock = true := by
        have hCanonical := hElse childQ residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hNotHeader : childState 1 childQ ∉
          (if elseFragment.initial ∈ elseFragment.completing ∨
              branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
            {TypeAutomatonState.root}
          else (∅ : Finset TypeAutomatonState)) := by
        split <;> simp [childState]
      have hNotConjunction : childState 1 childQ ∉
          childCompleting 0 conjunction := by
        rintro hMember
        simp only [childCompleting, Finset.mem_image] at hMember
        rcases hMember with ⟨other, _, hEquality⟩
        have hImpossible : 0 = 1 := by injection hEquality
        omega
      simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      constructor
      · rintro ((hHeader | hConjunctionMember) | hElseMember)
        · exact (hNotHeader hHeader).elim
        · exact (hNotConjunction hConjunctionMember).elim
        · apply hChild.mp
          simpa [childCompleting, childState] using hElseMember
      · intro hResidual
        right
        simpa [childCompleting, childState] using hChild.mpr hResidual
-/

/-! ### Parallel future correspondence -/

/-- The optimistic product observations make parallel future correctness
compose directly from the two child future invariants.  Operational future
offers remain syntax-derived; the automaton equation is proved against
`typeFutureOffers_parallel`. -/
theorem compilationFutureCorrect_parallel
    (signature : TypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftFuture : CompilationFutureCorrect signature left)
    (hRightFuture : CompilationFutureCorrect signature right) :
    CompilationFutureCorrect signature (.par left right interface) := by
  sorry -- TODO(redevelopment): body used buildParallelAutomaton_computeFuture,
  -- deleted with the old synthetic-future-edge mechanism; needs re-deriving
  -- against computeFutureOf's native product-state case; .

end

end Pact
