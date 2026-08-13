import Anvilpp.PactTypes.Correspondence.Offers.XOfferStepCorrect

/-!
# compilationFutureCorrect_xoffer_of_children
-/

namespace Pact

noncomputable section

else continuation and every indexed branch continuation.  The operational
menu on the right remains the syntax-derived `typeFutureOffers_xoffer`. -/
theorem compilationFutureCorrect_xoffer_of_children
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.SupportsBranches branches)
    (hElseFuture : CompilationFutureCorrect signature elseType)
    (hBranchFuture : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationFutureCorrect signature branchType) :
    CompilationFutureCorrect signature (.xoffer elseType branches) := by
  classical
  intro state residual hRelated
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hSupportedLocal : ∀ rest : List (BareMessage × PactType),
      signature.SupportsBranches rest → ∀ branch ∈ rest,
        branch.1 ∈ signature.localActions := by
    intro rest hRest
    induction rest with
    | nil => simp
    | cons head tail ih =>
        rcases head with ⟨headAction, headType⟩
        rcases headAction with ⟨headMessage, headDirection⟩
        intro branch hBranch
        simp only [TypeAlphabet.SupportsBranches.eq_2] at hRest
        simp only [List.mem_cons] at hBranch
        rcases hBranch with rfl | hBranch
        · rcases hRest.1 with hBoundary | hInterface
          · exact Finset.mem_union_left _ hBoundary
          · apply Finset.mem_union_right
            simp only [TypeAlphabet.interfaceActions,
              Finset.mem_biUnion]
            refine ⟨headMessage, hInterface, ?_⟩
            cases headDirection <;> simp
        · exact ih hRest.2.2 branch hBranch
  have hAvailableOriginal : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions := by
    intro branch hBranch
    have hSupportedAction : branch.1 ∈ signature.localActions :=
      hSupportedLocal branches hSupports branch hBranch
    exact Finset.mem_image.mpr ⟨branch.1, hSupportedAction, rfl⟩
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailableOriginal branch hBranch
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
      (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel])
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      hBranchFuel
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
      (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel])
    exact compileTypeFuel_initial_mem signature fuel branch.2 hBranchFuel
  cases hRelated with
  | xoffer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (exclusiveOfferEntryStates elseFragment branchAutomata).biUnion
              (computeFuture pending) := by
        simpa [pending, fragment] using
          buildExclusiveOfferAutomaton_computeFuture_root signature branches
            elseFragment branchAutomata (by simp [branchAutomata]) hAvailable
              hElseTargets hBranchTargets hElseInitial hBranchInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding := buildExclusiveOfferAutomaton_computeFuture_else
        signature branches elseFragment branchAutomata elseFragment.initial
          hElseTargets hElseInitial hElseCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation signature elseType
      have hElseSemantic := hElseFuture elseFragment.initial elseType
        hElseRelation
      have hElseMenu : computeFuture pending
          (childState 0 elseFragment.initial) =
          typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        simpa [pending, fragment] using hElseEmbedding.trans hStandalone
      have hIndexedMenu : ∀ indexed ∈ branchAutomata.zipIdx,
          ∃ branchType,
            branches[indexed.2]? = some (indexed.1.1, branchType) ∧
              computeFuture pending
                  (childState (indexed.2 + 1) indexed.1.2.initial) =
                typeFutureOffers branchType := by
        intro indexed hIndexed
        rcases indexed with ⟨entry, index⟩
        have hFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
        rcases hFields with ⟨hAutomatonBound, hValue⟩
        have hBound : index < branches.length := by
          simpa [branchAutomata] using hAutomatonBound
        let branch := branches[index]
        have hBranchEntry : branches[index]? = some branch := by
          rw [List.getElem?_eq_getElem hBound]
        let branchFragment := compileTypeFuel signature fuel branch.2
        have hExpectedEntry : branchAutomata[index]? =
            some (branch.1, branchFragment) := by
          simp [branchAutomata, branchFragment, hBranchEntry]
        have hActualEntry : branchAutomata[index]? = some entry := by
          rw [List.getElem?_eq_getElem hAutomatonBound, ← hValue]
        have hEntryEquality : entry = (branch.1, branchFragment) :=
          Option.some.inj (hActualEntry.symm.trans hExpectedEntry)
        subst entry
        have hBranchMember : branch ∈ branches :=
          List.getElem_mem hBound
        have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel :=
          (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
            hBranchMember).trans (by simp [fuel])
        have hBranchStable : branchFragment = compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2 :=
          compileTypeFuel_eq_of_sufficient signature branch.2 hBranchFuel
            (typeCompilationFuel_sufficient branch.2)
        have hBranchTargets' : branchFragment.FutureTargetsInStates :=
          compileTypeFuel_futureTargetsInStates signature fuel branch.2
            hBranchFuel
        have hBranchInitial' : branchFragment.initial ∈
            branchFragment.states :=
          compileTypeFuel_initial_mem signature fuel branch.2 hBranchFuel
        have hCard : branchFragment.states.card ≤ fragment.states.card := by
          have hIndexedSubset : childStates (index + 1) branchFragment ⊆
              indexedFragmentStates branchAutomata := by
            intro child hChild
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            exact ⟨((branch.1, branchFragment), index), hIndexed, hChild⟩
          have hSubset : childStates (index + 1) branchFragment ⊆
              fragment.states := by
            intro child hChild
            have hChild' := hIndexedSubset hChild
            simp [fragment, buildExclusiveOfferAutomaton,
              finishAutomatonFragment, hChild']
          calc
            branchFragment.states.card =
                (childStates (index + 1) branchFragment).card := by
              simp only [childStates]
              symm
              apply Finset.card_image_of_injective
              intro first second hEqual
              injection hEqual
            _ ≤ fragment.states.card := Finset.card_le_card hSubset
        have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_branch
          signature branches elseFragment branchAutomata index
            (branch.1, branchFragment) hExpectedEntry branchFragment.initial
              hBranchTargets' hBranchInitial' hCard
        have hBranchRelation : TypeCompilationRelation branch.2
            branchFragment.initial branch.2 := by
          simpa [branchFragment, hBranchStable] using
            compileType_initial_relation signature branch.2
        have hSemantic := hBranchFuture branch.1 branch.2 index
          hBranchEntry branchFragment.initial branch.2 hBranchRelation
        have hStandalone : computeFuture
            { states := branchFragment.states, edges := branchFragment.edges }
            branchFragment.initial = typeFutureOffers branch.2 := by
          simpa [branchFragment, hBranchStable] using hSemantic
        refine ⟨branch.2, ?_, ?_⟩
        · simpa using hBranchEntry
        · simpa [pending, fragment] using hEmbedding.trans hStandalone
      have hEntryMenus : ∀ action,
          action ∈
              (exclusiveOfferEntryStates elseFragment branchAutomata).biUnion
                (computeFuture pending) ↔
            action ∈ typeFutureOffers elseType ∨
              ∃ branch ∈ branches,
                action ∈ typeFutureOffers branch.2 := by
        intro action
        constructor
        · intro hAction
          rcases Finset.mem_biUnion.mp hAction with
            ⟨entryState, hEntryState, hEntryOffer⟩
          unfold exclusiveOfferEntryStates at hEntryState
          simp only [Finset.mem_union, Finset.mem_singleton] at hEntryState
          rcases hEntryState with hElse | hBranch
          · subst entryState
            exact Or.inl (by simpa [hElseMenu] using hEntryOffer)
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty |
              ⟨indexed, hIndexed, hEntryState⟩
            · simp at hEmpty
            simp only [Finset.mem_singleton] at hEntryState
            subst entryState
            rcases hIndexedMenu indexed hIndexed with
              ⟨branchType, hBranchEntry, hMenu⟩
            have hBranchMember : (indexed.1.1, branchType) ∈ branches := by
              rcases List.getElem?_eq_some_iff.mp hBranchEntry with
                ⟨hBound, hValue⟩
              have hMember := List.getElem_mem hBound
              simpa [hValue] using hMember
            exact Or.inr ⟨(indexed.1.1, branchType), hBranchMember,
              by simpa [hMenu] using hEntryOffer⟩
        · rintro (hElseOffer | ⟨branch, hBranch, hBranchOffer⟩)
          · apply Finset.mem_biUnion.mpr
            refine ⟨childState 0 elseFragment.initial, ?_, ?_⟩
            · simp [exclusiveOfferEntryStates]
            · simpa [hElseMenu] using hElseOffer
          · rcases List.mem_iff_getElem.mp hBranch with
              ⟨index, hBound, hValue⟩
            let branchFragment := compileTypeFuel signature fuel branch.2
            have hBranchEntry : branches[index]? = some branch := by
              rw [List.getElem?_eq_getElem hBound, hValue]
            have hAutomatonEntry : branchAutomata[index]? =
                some (branch.1, branchFragment) := by
              simp [branchAutomata, branchFragment, hBranchEntry]
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa [branchAutomata] using hBound
            have hZipEntry : ((branch.1, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hAutomatonBound : index < branchAutomata.length := by
                simpa [branchAutomata] using hBound
              have hValue' : branchAutomata[index] =
                  (branch.1, branchFragment) := by
                exact (List.getElem?_eq_some_iff.mp hAutomatonEntry).2
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt] at hMember
              rw [hValue'] at hMember
              exact hMember
            rcases hIndexedMenu ((branch.1, branchFragment), index)
              hZipEntry with ⟨targetType, hTargetEntry, hMenu⟩
            have hTargetType : targetType = branch.2 := by
              have hOptions := hTargetEntry.symm.trans hBranchEntry
              exact (Prod.mk.inj (Option.some.inj hOptions)).2
            subst targetType
            apply Finset.mem_biUnion.mpr
            refine ⟨childState (index + 1) branchFragment.initial, ?_, ?_⟩
            · unfold exclusiveOfferEntryStates
              simp only [Finset.mem_union, Finset.mem_singleton]
              right
              rw [mem_foldl_union_iff]
              right
              exact ⟨((branch.1, branchFragment), index), hZipEntry, by simp⟩
            · simpa [hMenu] using hBranchOffer
      have hSyntax := typeFutureOffers_xoffer elseType branches
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.xoffer elseType branches) := by
        rw [hRootGraph, hSyntax]
        ext action
        rw [Finset.mem_union, mem_futureOfferBranchFold_iff,
          hEntryMenus action]
        constructor
        · rintro (hHead | hElse | ⟨branch, hBranch, hFuture⟩)
          · right
            have hMapped : action ∈ branches.map Prod.fst := by
              simpa [typeBranchActions] using hHead
            rcases List.mem_map.mp hMapped with
              ⟨branch, hBranch, hAction⟩
            exact ⟨branch, hBranch, Or.inl hAction.symm⟩
          · exact Or.inl hElse
          · exact Or.inr ⟨branch, hBranch, Or.inr hFuture⟩
        · rintro (hElse | ⟨branch, hBranch, hHead | hFuture⟩)
          · exact Or.inr (Or.inl hElse)
          · left
            simpa [typeBranchActions, hHead] using
              (List.mem_map_of_mem (f := Prod.fst) hBranch)
          · exact Or.inr (Or.inr ⟨branch, hBranch, hFuture⟩)
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, fuel] using
          hMenuEquality
  | xoffer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_else
        signature branches elseFragment branchAutomata childState hElseTargets
          hChildState hCard
      have hSemantic := hElseFuture childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, fuel] using
          hEmbedding.trans hSemanticShared
  | xoffer_branch _ branchType _ _ action index childState
      hEntry hChildRelated =>
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hBranchMember).trans (by simp [fuel])
      let branchFragment := compileTypeFuel signature fuel branchType
      have hBranchStable : branchFragment = compileTypeFuel signature
          (typeCompilationFuel branchType) branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, branchFragment) := by
        simp [branchAutomata, branchFragment, hEntry]
      have hChildState : childState ∈ branchFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          branchType childState residual hChildRelated
        simpa [branchFragment, hBranchStable] using hCanonical
      have hTargets : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
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
          intro child hChild
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry, hChild⟩
        have hSubset : childStates (index + 1) branchFragment ⊆
            fragment.states := by
          intro child hChild
          have hIndexed := hIndexedSubset hChild
          simp [fragment, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, hIndexed]
        calc
          branchFragment.states.card =
              (childStates (index + 1) branchFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildExclusiveOfferAutomaton_computeFuture_branch
        signature branches elseFragment branchAutomata index
          (action, branchFragment) hAutomatonEntry childState hTargets
            hChildState hCard
      have hSemantic := hBranchFuture action branchType index hEntry
        childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := branchFragment.states, edges := branchFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [branchFragment, hBranchStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, branchAutomata, branchFragment,
        fuel] using hEmbedding.trans hSemanticShared

end

end Pact
