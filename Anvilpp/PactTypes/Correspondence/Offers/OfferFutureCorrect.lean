import Anvilpp.PactTypes.Correspondence.Offers.XOfferFutureCorrect

/-!
# compilationFutureCorrect_offer_of_children
-/

namespace Pact

noncomputable section

/-- Whole-fragment future correctness for conjunctive offers.  Each enabled
witness's selected conjunction is treated as an indexed child and the else
continuation as child `0`; the root calculation is then identified with the
syntax-derived `typeFutureOffers_offer` fold.  Selection does not change the
fold value at any index, so a single per-index future hypothesis suffices. -/
theorem compilationFutureCorrect_offer_of_children
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.SupportsBranches branches)
    (hElseFuture : CompilationFutureCorrect signature elseType)
    (hConjunctionFuture : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationFutureCorrect signature
          (parallelTypeBranchesSelecting selected branches)) :
    CompilationFutureCorrect signature (.offer elseType branches) := by
  classical
  intro state residual hRelated
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hActions : selectedConjunctions.map Prod.fst = branches.map Prod.fst := by
    simp [selectedConjunctions]
  have hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupports
  have hSelectedAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailable branch hBranch
  have hEntryFuel : ∀ entry ∈ branches,
      TypeCompilationFuelSufficient
        (parallelTypeBranchesSelecting entry branches) fuel := by
    intro entry _
    simp only [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
    exact le_max_right _ _
  have hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel
      (parallelTypeBranchesSelecting branch branches) (hEntryFuel branch hBranch)
  have hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    simp only [selectedConjunctions, List.mem_map] at hEntry
    rcases hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel
      (parallelTypeBranchesSelecting branch branches) (hEntryFuel branch hBranch)
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  rw [hFragment]
  cases hRelated with
  | offer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (selectedConjunctiveOfferEntryStates elseFragment
              selectedConjunctions).biUnion (computeFuture pending) := by
        simpa [pending, fragment] using
          buildSelectedConjunctiveOfferAutomaton_computeFuture_root signature
            branches elseFragment selectedConjunctions hSelectedAvailable
              hElseTargets hConjunctionTargets hElseInitial hConjunctionInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding : computeFuture pending (childState 0 elseFragment.initial) =
          computeFuture { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
          ({ states := elseFragment.states, edges := elseFragment.edges } :
            PendingAutomaton) 0
          (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
            elseFragment selectedConjunctions)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            elseFragment hElseTargets)
          elseFragment.initial hElseInitial hElseCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation signature elseType
      have hElseSemantic := hElseFuture elseFragment.initial elseType
        hElseRelation
      have hElseMenu : computeFuture pending
          (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        exact hElseEmbedding.trans hStandalone
      have hConjunctionMenu : ∀ index entry, selectedConjunctions[index]? =
          some entry → computeFuture pending (childState (index + 1) entry.2.initial) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
        intro index entry hEntry
        have hEntryMem : entry ∈ selectedConjunctions := by
          rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
          have hMember := List.getElem_mem hBound
          simpa [hValue] using hMember
        have hCard : entry.2.states.card ≤ fragment.states.card := by
          have hIndexedSubset : childStates (index + 1) entry.2 ⊆
              indexedFragmentStates selectedConjunctions := by
            intro s hs
            rw [indexedFragmentStates, mem_foldl_union_iff]
            right
            rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
            have hZipBound : index < selectedConjunctions.zipIdx.length := by
              simpa using hBound
            have hZipEntry : (entry, index) ∈ selectedConjunctions.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            exact ⟨(entry, index), hZipEntry, hs⟩
          have hSubset : childStates (index + 1) entry.2 ⊆ fragment.states := by
            intro s hs
            have hIndexed := hIndexedSubset hs
            simp [fragment, buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, hIndexed]
          calc
            entry.2.states.card = (childStates (index + 1) entry.2).card := by
              simp only [childStates]
              symm
              apply Finset.card_image_of_injective
              intro first second hEqual
              injection hEqual
            _ ≤ fragment.states.card := Finset.card_le_card hSubset
        have hEmbedding : computeFuture pending (childState (index + 1) entry.2.initial) =
            computeFuture { states := entry.2.states, edges := entry.2.edges }
              entry.2.initial :=
          taggedChild_computeFuture_of_outgoing
            ({ states := fragment.states, edges := fragment.edges } :
              PendingAutomaton)
            ({ states := entry.2.states, edges := entry.2.edges } :
              PendingAutomaton) (index + 1)
            (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
              signature branches elseFragment selectedConjunctions index entry
                hEntry)
            (PendingAutomaton.referencesClosed_of_futureTargetsInStates
              entry.2 (hConjunctionTargets entry hEntryMem))
            entry.2.initial (hConjunctionInitial entry hEntryMem) hCard
        have hIndexBound : index < branches.length := by
          have := List.getElem?_eq_some_iff.mp hEntry
          simpa [selectedConjunctions] using this.1
        let branch := branches[index]
        have hBranchEntry : branches[index]? = some branch := by
          simp [branch, List.getElem?_eq_getElem hIndexBound]
        have hBranchEq : entry = (branch.1, compileTypeFuel signature fuel
            (parallelTypeBranchesSelecting branch branches)) := by
          have hEntry' : selectedConjunctions[index]? = some entry := hEntry
          simp only [selectedConjunctions, List.getElem?_map, hBranchEntry,
            Option.map_some, Option.some.injEq] at hEntry'
          exact hEntry'.symm
        have hBranchMem : branch ∈ branches := by
          rcases List.getElem?_eq_some_iff.mp hBranchEntry with ⟨hBound, hValue⟩
          have hMember := List.getElem_mem hBound
          simpa [hValue] using hMember
        have hStable : entry.2 = compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting branch branches))
            (parallelTypeBranchesSelecting branch branches) := by
          rw [hBranchEq]
          exact compileTypeFuel_eq_of_sufficient signature
            (parallelTypeBranchesSelecting branch branches)
            (hEntryFuel branch hBranchMem) (typeCompilationFuel_sufficient _)
        have hSelectedRelation : TypeCompilationRelation
            (parallelTypeBranchesSelecting branch branches)
            entry.2.initial (parallelTypeBranchesSelecting branch branches) := by
          simpa [hStable] using
            compileType_initial_relation signature
              (parallelTypeBranchesSelecting branch branches)
        have hSemantic := hConjunctionFuture branch index hBranchEntry
          entry.2.initial (parallelTypeBranchesSelecting branch branches)
          hSelectedRelation
        have hSemanticShared : computeFuture
            { states := entry.2.states, edges := entry.2.edges } entry.2.initial =
              typeFutureOffers (parallelTypeBranchesSelecting branch branches) := by
          simpa [hStable] using hSemantic
        rw [hEmbedding, hSemanticShared,
          typeFutureOffers_parallelTypeBranchesSelecting_eq_fold]
      have hEntryMenus : (selectedConjunctiveOfferEntryStates elseFragment
          selectedConjunctions).biUnion (computeFuture pending) =
            typeFutureOffers elseType ∪
              if branches = [] then ∅ else
                branches.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
        ext action
        simp only [selectedConjunctiveOfferEntryStates, Finset.mem_biUnion,
          Finset.mem_union]
        constructor
        · rintro ⟨s, (hs | hs), hAction⟩
          · simp only [Finset.mem_singleton] at hs
            subst hs
            left
            simpa [hElseMenu] using hAction
          · rw [mem_foldl_union_iff] at hs
            rcases hs with hEmpty | ⟨indexed, hIndexed, hs⟩
            · simp at hEmpty
            simp only [Finset.mem_singleton] at hs
            subst hs
            right
            have hNonempty : branches ≠ [] := by
              rintro rfl
              simp [selectedConjunctions] at hIndexed
            rw [if_neg hNonempty]
            have hIndexedFields := List.mem_zipIdx hIndexed
            simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
              at hIndexedFields
            rcases hIndexedFields with ⟨hBound, hValue⟩
            have hEntry : selectedConjunctions[indexed.2]? = some indexed.1 := by
              rw [List.getElem?_eq_getElem hBound, hValue]
            rw [← hConjunctionMenu indexed.2 indexed.1 hEntry]
            exact hAction
        · rintro (hAction | hAction)
          · exact ⟨childState 0 elseFragment.initial, Or.inl (by simp),
              by simpa [hElseMenu] using hAction⟩
          · by_cases hEmpty : branches = []
            · subst hEmpty
              simp at hAction
            · rw [if_neg hEmpty] at hAction
              cases hBranches : branches with
              | nil => exact absurd hBranches hEmpty
              | cons head tail =>
                  have hEntry0 : selectedConjunctions[0]? = some
                      (head.1, compileTypeFuel signature fuel
                        (parallelTypeBranchesSelecting head branches)) := by
                    simp [selectedConjunctions, hBranches]
                  refine ⟨childState 1 (compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting head branches)).initial,
                    Or.inr ?_, ?_⟩
                  · rw [mem_foldl_union_iff]
                    right
                    refine ⟨((head.1, compileTypeFuel signature fuel
                      (parallelTypeBranchesSelecting head branches)), 0), ?_, by simp⟩
                    rcases List.getElem?_eq_some_iff.mp hEntry0 with
                      ⟨hBound, hValue⟩
                    have hZipBound : (0 : Nat) <
                        selectedConjunctions.zipIdx.length := by simpa using hBound
                    have hMember := List.getElem_mem hZipBound
                    have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                      (i := 0) (j := 0) hZipBound
                    simp only [zero_add] at hAt
                    rw [hAt, hValue] at hMember
                    exact hMember
                  · rw [hConjunctionMenu 0 _ hEntry0]
                    exact hAction
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.offer elseType branches) := by
        rw [hRootGraph, hEntryMenus, typeFutureOffers_offer]
        by_cases hEmpty : branches = []
        · subst branches
          simp [typeBranchActions, typeFutureOffers, typeFutureOffersFuel]
        · rw [if_neg hEmpty]
          ext action
          rw [Finset.mem_union, Finset.mem_union,
            mem_futureOfferBranchFold_iff action branches ∅,
            mem_futureOfferBranchFold_iff action branches
              (typeFutureOffers elseType)]
          have hHeadIff : action ∈ typeBranchActions branches ↔
              ∃ branch ∈ branches, action = branch.1 := by
            constructor
            · intro hHead
              have hMapped : action ∈ branches.map Prod.fst := by
                simpa [typeBranchActions] using hHead
              rcases List.mem_map.mp hMapped with ⟨branch, hBranch, hAction⟩
              exact ⟨branch, hBranch, hAction.symm⟩
            · rintro ⟨branch, hBranch, hAction⟩
              simpa [typeBranchActions, hAction] using
                (List.mem_map_of_mem (f := Prod.fst) hBranch)
          rw [hHeadIff]
          constructor
          · rintro (⟨branch, hBranch, hAction⟩ | hElse | hEmptyMem | hExists)
            · exact Or.inr ⟨branch, hBranch, Or.inl hAction⟩
            · exact Or.inl hElse
            · simp at hEmptyMem
            · exact Or.inr hExists
          · rintro (hElse | ⟨branch, hBranch, hHead | hAction⟩)
            · exact Or.inr (Or.inl hElse)
            · exact Or.inl ⟨branch, hBranch, hHead⟩
            · exact Or.inr (Or.inr (Or.inr ⟨branch, hBranch, Or.inr hAction⟩))
      simpa only [pending, fragment] using hMenuEquality
  | offer_branches _ _ _ selected index state' hEntry hChildRelated =>
      have hEntryMem : selected ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hSelectedFuel := hEntryFuel selected hEntryMem
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
      have hChildState : state' ∈ selectedFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          (parallelTypeBranchesSelecting selected branches) state' residual
          hChildRelated
        simpa [selectedFragment, hSelectedStable] using hCanonical
      have hCard : selectedFragment.states.card ≤ fragment.states.card := by
        have hIndexedSubset : childStates (index + 1) selectedFragment ⊆
            indexedFragmentStates selectedConjunctions := by
          intro s hs
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
            ⟨hBound, hValue⟩
          have hZipBound : index < selectedConjunctions.zipIdx.length := by
            simpa using hBound
          have hZipEntry : ((selected.1, selectedFragment), index) ∈
              selectedConjunctions.zipIdx := by
            have hMember := List.getElem_mem hZipBound
            have hAt := List.getElem_zipIdx (l := selectedConjunctions)
              (i := index) (j := 0) hZipBound
            simp only [zero_add] at hAt
            rw [hAt, hValue] at hMember
            exact hMember
          exact ⟨((selected.1, selectedFragment), index), hZipEntry, hs⟩
        have hSubset : childStates (index + 1) selectedFragment ⊆
            fragment.states := by
          intro s hs
          have hIndexed := hIndexedSubset hs
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hIndexed]
        calc
          selectedFragment.states.card =
              (childStates (index + 1) selectedFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding : computeFuture pending
          (childState (index + 1) state') = computeFuture
          { states := selectedFragment.states, edges := selectedFragment.edges }
          state' :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } :
            PendingAutomaton)
          ({ states := selectedFragment.states, edges := selectedFragment.edges } :
            PendingAutomaton) (index + 1)
          (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            selectedFragment
              (compileTypeFuel_futureTargetsInStates signature fuel
                (parallelTypeBranchesSelecting selected branches)
                hSelectedFuel))
          state' hChildState hCard
      have hSemantic := hConjunctionFuture selected index hEntry state'
        residual hChildRelated
      have hSemanticShared : computeFuture
          { states := selectedFragment.states, edges := selectedFragment.edges }
          state' = typeFutureOffers residual := by
        simpa [selectedFragment, hSelectedStable] using hSemantic
      simpa only [pending, fragment] using hEmbedding.trans hSemanticShared
  | offer_else _ _ _ state' hChildRelated =>
      have hChildState : state' ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType state' residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 0 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding : computeFuture pending (childState 0 state') =
          computeFuture { states := elseFragment.states, edges := elseFragment.edges }
            state' :=
        taggedChild_computeFuture_of_outgoing
          ({ states := fragment.states, edges := fragment.edges } : PendingAutomaton)
          ({ states := elseFragment.states, edges := elseFragment.edges } :
            PendingAutomaton) 0
          (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
            elseFragment selectedConjunctions)
          (PendingAutomaton.referencesClosed_of_futureTargetsInStates
            elseFragment hElseTargets)
          state' hChildState hCard
      have hSemantic := hElseFuture state' residual hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          state' = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [pending, fragment] using hEmbedding.trans hSemanticShared
/-
  classical
  intro state residual hRelated
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
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
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hConjunctionTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hConjunctionInitial : conjunction.initial ∈ conjunction.states :=
    compileTypeFuel_initial_mem signature fuel conjunctionType
      hConjunctionFuel
  have hAvailable : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupports
  cases hRelated with
  | offer_source =>
      have hRootGraph : computeFuture pending .root =
          typeBranchActions branches ∪
            (conjunctiveOfferEntryStates branches elseFragment
              conjunction).biUnion (computeFuture pending) := by
        simpa [pending, fragment] using
          buildConjunctiveOfferAutomaton_computeFuture_root signature branches
            elseFragment conjunction hAvailable hElseTargets
              hConjunctionTargets hElseInitial hConjunctionInitial
      have hElseCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 1 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hConjunctionCard : conjunction.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 conjunction ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          conjunction.states.card = (childStates 0 conjunction).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hElseEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 1 elseFragment
          (Or.inr ⟨rfl, rfl⟩) elseFragment.initial hElseTargets hElseInitial
            hElseCard
      have hConjunctionEmbedding :=
        buildConjunctiveOfferAutomaton_computeFuture_child signature branches
          elseFragment conjunction 0 conjunction (Or.inl ⟨rfl, rfl⟩)
            conjunction.initial hConjunctionTargets hConjunctionInitial
              hConjunctionCard
      have hElseRelation : TypeCompilationRelation elseType
          elseFragment.initial elseType := by
        simpa [elseFragment, hElseStable] using
          compileType_initial_relation signature elseType
      have hConjunctionRelation : TypeCompilationRelation conjunctionType
          conjunction.initial conjunctionType := by
        simpa [conjunction, hConjunctionStable] using
          compileType_initial_relation signature conjunctionType
      have hElseSemantic := hElseFuture elseFragment.initial elseType
        hElseRelation
      have hConjunctionSemantic := hConjunctionFuture conjunction.initial
        conjunctionType hConjunctionRelation
      have hElseMenu : computeFuture pending
          (childState 1 elseFragment.initial) =
          typeFutureOffers elseType := by
        have hStandalone : computeFuture
            { states := elseFragment.states, edges := elseFragment.edges }
            elseFragment.initial = typeFutureOffers elseType := by
          simpa [elseFragment, hElseStable] using hElseSemantic
        simpa [pending, fragment] using hElseEmbedding.trans hStandalone
      have hConjunctionMenu : computeFuture pending
          (childState 0 conjunction.initial) =
          typeFutureOffers conjunctionType := by
        have hStandalone : computeFuture
            { states := conjunction.states, edges := conjunction.edges }
            conjunction.initial = typeFutureOffers conjunctionType := by
          simpa [conjunction, hConjunctionStable] using hConjunctionSemantic
        simpa [pending, fragment] using
          hConjunctionEmbedding.trans hStandalone
      have hEntryMenus :
          (conjunctiveOfferEntryStates branches elseFragment
              conjunction).biUnion (computeFuture pending) =
            typeFutureOffers elseType ∪
              if branches = [] then ∅ else typeFutureOffers conjunctionType := by
        ext action
        by_cases hEmpty : branches = []
        · subst branches
          simp [conjunctiveOfferEntryStates, hElseMenu]
        · simp [conjunctiveOfferEntryStates, hEmpty, hElseMenu,
            hConjunctionMenu, or_comm]
      have hMenuEquality : computeFuture pending .root =
          typeFutureOffers (.offer elseType branches) := by
        rw [hRootGraph, hEntryMenus, typeFutureOffers_offer]
        by_cases hEmpty : branches = []
        · subst branches
          simp [typeBranchActions, typeFutureOffers, typeFutureOffersFuel]
        · rw [if_neg hEmpty,
            typeFutureOffers_parallelTypeBranches_eq_fold]
          ext action
          rw [Finset.mem_union, Finset.mem_union,
            mem_futureOfferBranchFold_iff action branches ∅,
            mem_futureOfferBranchFold_iff action branches
              (typeFutureOffers elseType)]
          simp
          intro hHead
          right
          have hMapped : action ∈ branches.map Prod.fst := by
            simpa [typeBranchActions] using hHead
          rcases List.mem_map.mp hMapped with
            ⟨branch, hBranch, hAction⟩
          rcases branch with ⟨⟨message, direction⟩, branchType⟩
          exact ⟨message, direction, branchType, hBranch,
            Or.inl hAction.symm⟩
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hMenuEquality
  | offer_branches _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ conjunction.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          conjunctionType childState residual hChildRelated
        simpa [conjunction, hConjunctionStable] using hCanonical
      have hCard : conjunction.states.card ≤ fragment.states.card := by
        have hSubset : childStates 0 conjunction ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          conjunction.states.card = (childStates 0 conjunction).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 0 conjunction
          (Or.inl ⟨rfl, rfl⟩) childState hConjunctionTargets hChildState hCard
      have hSemantic := hConjunctionFuture childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := conjunction.states, edges := conjunction.edges }
          childState = typeFutureOffers residual := by
        simpa [conjunction, hConjunctionStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hEmbedding.trans hSemanticShared
  | offer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hCard : elseFragment.states.card ≤ fragment.states.card := by
        have hSubset : childStates 1 elseFragment ⊆ fragment.states := by
          intro child hChild
          simp [fragment, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, hChild]
        calc
          elseFragment.states.card = (childStates 1 elseFragment).card := by
            simp only [childStates]
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ fragment.states.card := Finset.card_le_card hSubset
      have hEmbedding := buildConjunctiveOfferAutomaton_computeFuture_child
        signature branches elseFragment conjunction 1 elseFragment
          (Or.inr ⟨rfl, rfl⟩) childState hElseTargets hChildState hCard
      have hSemantic := hElseFuture childState residual hChildRelated
      have hSemanticShared : computeFuture
          { states := elseFragment.states, edges := elseFragment.edges }
          childState = typeFutureOffers residual := by
        simpa [elseFragment, hElseStable] using hSemantic
      simpa only [typeCompilationFuel, Nat.one_add, compileTypeFuel,
        fragment, pending, elseFragment, conjunction, conjunctionType, fuel]
        using hEmbedding.trans hSemanticShared
-/

end

end Pact
