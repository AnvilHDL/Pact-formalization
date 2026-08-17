import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionLeaf

/-!
# xoffer regular leaf
-/

namespace Pact

noncomputable section


/-- Exclusive-offer closure packages its indexed branch/else/wait
classifiers.  Completion is supplied by the strong-induction hypotheses for
the else continuation and every indexed branch. -/

private theorem compilationFutureCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.xoffer elseType branches) := by
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  exact compilationFutureCorrect_xoffer_of_children signature elseType
    branches hSupportFields.2 hElse.future
      (fun action branchType index hEntry =>
        (hBranches action branchType index hEntry).future)

private theorem compilationFragmentStepCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.xoffer elseType branches) := by
  exact compilationScopedFragmentStepCorrect_xoffer signature elseType
    branches hElse.scopedStep
      (fun action branchType index hEntry =>
        (hBranches action branchType index hEntry).scopedStep)
      hFuture

private theorem compilationSequenceExecutionCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationSequenceExecutionCorrect signature
      (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  let entries := exclusiveOfferEntryStates elseFragment branchAutomata
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
  have hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel branch.2
      ((typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel]))
  have hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel branch.2
      ((typeCompilationFuel_le_typeBranchCompilationFuel branches branch
        hBranch).trans (by simp [fuel]))
  have hFragmentTargets : fragment.FutureTargetsInStates := by
    exact buildExclusiveOfferAutomaton_futureTargetsInStates signature
      branches elseFragment branchAutomata hElseTargets hBranchTargets
        hElseInitial hBranchInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [fragment, buildExclusiveOfferAutomaton, finishAutomatonFragment]
  have hSupportFields := hSupports
  simp only [TypeAlphabet.Supports] at hSupportFields
  have hAvailableOriginal : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2
  have hAvailable : ∀ entry ∈ branchAutomata,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨branch, hBranch, rfl⟩
    exact hAvailableOriginal branch hBranch
  have hUpper : pending.referencedStates .root ⊆ insert .root entries := by
    simpa [pending, fragment, entries] using
      buildExclusiveOfferAutomaton_root_references_upper signature branches
        elseFragment branchAutomata
  have hEntries : entries ⊆ pending.referencedStates .root := by
    simpa [pending, fragment, entries] using
      buildExclusiveOfferAutomaton_entries_referenced signature branches
        elseFragment branchAutomata hAvailable
  have hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed := by
    intro edge hEdge hSource
    exact sequenceExecution_buildExclusiveOffer_root_shape signature
      branches elseFragment branchAutomata edge hEdge hSource
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hWholeFuture := compilationFutureCorrect_xoffer_regular_leaf signature
    elseType branches hSupports hElse hBranches
  have hBranchCompleting : ∀ (action : BareMessage)
      (branchType : PactType) (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType := by
    intro action branchType index hEntry
    exact (hBranches action branchType index hEntry).completing
  have hWholeCompleting := compilationCompletingCorrect_xoffer signature
    elseType branches hElse.completing hBranchCompleting
  have hElseStates : elseFragment.states.image (childState 0) ⊆
      fragment.states := by
    intro tagged hTagged
    rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
    simp [fragment, buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hState]
  have hElseOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
    intro state edge
    simpa [fragment] using
      (buildExclusiveOfferAutomaton_outgoing_else signature branches
        elseFragment branchAutomata state edge)
  have hElseRootRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    simpa [elseFragment, hElseStable, compileType] using
      compileType_initial_relation signature elseType
  have hElseRootExecution := hElse.execution elseFragment.initial elseType
    hElseRootRelation
  have hElseRootExecution' :
      computeFuture (sequenceExecutionAutomaton elseFragment)
          elseFragment.initial = typeFutureOffers elseType ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton elseFragment).futureReachable
                elseFragment.initial,
              completed ∈ elseFragment.accepting ∨
                completed ∈ elseFragment.completing) ↔
          elseType.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, elseFragment, hElseStable]
      using hElseRootExecution
  have hEntryFacts : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry ∧
        ((∃ completed ∈ execution.futureReachable entry,
            completed ∈ fragment.accepting ∨
              completed ∈ fragment.completing) →
          (PactType.xoffer elseType branches).CanCompleteBeforeTock = true) := by
    intro entry hEntry
    simp only [entries, exclusiveOfferEntryStates, Finset.mem_union,
      Finset.mem_singleton] at hEntry
    rcases hEntry with rfl | hBranchEntry
    · have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
          elseFragment.initial hElseInitial
      have hParentRelation : TypeCompilationRelation
          (.xoffer elseType branches) (childState 0 elseFragment.initial)
            elseType := TypeCompilationRelation.xoffer_else elseType elseType
              branches elseFragment.initial hElseRootRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hElseRootExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
            elseFragment.initial hElseInitial
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState 0 state ∈ fragment.accepting ↔
              state ∈ elseFragment.accepting := by
          intro state
          exact buildExclusiveOffer_child0_accepting_iff signature branches
            elseFragment branchAutomata state
        have hComplete : ∀ state,
            childState 0 state ∈ fragment.completing ↔
              state ∈ elseFragment.completing := by
          intro state
          exact buildExclusiveOffer_child0_completing_iff signature branches
            elseFragment branchAutomata state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton elseFragment).futureReachable
              elseFragment.initial,
            childCompleted ∈ elseFragment.accepting ∨
              childCompleted ∈ elseFragment.completing :=
          (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
            hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hElseCan := hElseRootExecution'.2.mp hChildWitness
        simp [PactType.CanCompleteBeforeTock, hElseCan]
    · rw [mem_foldl_union_iff] at hBranchEntry
      rcases hBranchEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
      · simp at hEmpty
      simp only [Finset.mem_singleton] at hEntryState
      subst entry
      rcases compiledBranch_zipIdx_cases signature fuel branches indexed
          (by simpa [branchAutomata] using hIndexed) with
        ⟨action, branchType, hSyntaxEntry, hCompiledEntry⟩
      rcases indexed with ⟨compiledEntry, index⟩
      simp only at hCompiledEntry
      subst compiledEntry
      let branchFragment := compileTypeFuel signature fuel branchType
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
          ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) hBranchMember).trans (by simp [fuel])
      have hBranchStable : branchFragment = compileTypeFuel signature
          (typeCompilationFuel branchType) branchType :=
        compileTypeFuel_eq_of_sufficient signature branchType hBranchFuel
          (typeCompilationFuel_sufficient branchType)
      have hBranchInitialState : branchFragment.initial ∈
          branchFragment.states :=
        compileTypeFuel_initial_mem signature fuel branchType hBranchFuel
      have hBranchTargets' : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
      have hAutomatonEntry : branchAutomata[index]? =
          some (action, branchFragment) := by
        simp [branchAutomata, branchFragment, hSyntaxEntry]
      have hZipEntry : ((action, branchFragment), index) ∈
          branchAutomata.zipIdx := by
        simpa [branchAutomata, branchFragment] using hIndexed
      have hBranchStates : branchFragment.states.image
          (childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
        have hIndexedState : childState (index + 1) state ∈
            indexedFragmentStates branchAutomata := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry,
            by simp [childStates, childState, hState]⟩
        simp [fragment, buildExclusiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hBranchOutgoing : ∀ state edge,
          edge ∈ fragment.edges ∧
              edge.source = childState (index + 1) state ↔
            ∃ childEdge ∈ branchFragment.edges,
              childEdge.source = state ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro state edge
        simpa [fragment, branchFragment] using
          (buildExclusiveOfferAutomaton_outgoing_branch signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state edge)
      have hBranchRelation : TypeCompilationRelation branchType
          branchFragment.initial branchType := by
        simpa [branchFragment, hBranchStable, compileType] using
          compileType_initial_relation signature branchType
      have hBranchBundle := hBranches action branchType index hSyntaxEntry
      have hBranchExecution := hBranchBundle.execution
        branchFragment.initial branchType hBranchRelation
      have hBranchExecution' :
          computeFuture (sequenceExecutionAutomaton branchFragment)
              branchFragment.initial = typeFutureOffers branchType ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton branchFragment).futureReachable
                    branchFragment.initial,
                  completed ∈ branchFragment.accepting ∨
                    completed ∈ branchFragment.completing) ↔
              branchType.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, branchFragment,
          hBranchStable] using hBranchExecution
      have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment branchFragment (index + 1) hBranchOutgoing hBranchStates
          hBranchTargets' branchFragment.initial hBranchInitialState
      have hParentRelation : TypeCompilationRelation
          (.xoffer elseType branches)
            (childState (index + 1) branchFragment.initial) branchType :=
        TypeCompilationRelation.xoffer_branch elseType branchType branchType
          branches action index branchFragment.initial hSyntaxEntry
            hBranchRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hBranchExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment branchFragment (index + 1) hBranchOutgoing hBranchStates
            hBranchTargets' branchFragment.initial hBranchInitialState
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState (index + 1) state ∈ fragment.accepting ↔
              state ∈ branchFragment.accepting := by
          intro state
          exact buildExclusiveOffer_branch_accepting_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state
        have hComplete : ∀ state,
            childState (index + 1) state ∈ fragment.completing ↔
              state ∈ branchFragment.completing := by
          intro state
          exact buildExclusiveOffer_branch_completing_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton branchFragment).futureReachable
              branchFragment.initial,
            childCompleted ∈ branchFragment.accepting ∨
              childCompleted ∈ branchFragment.completing :=
          (taggedCompletionWitness_iff fragment branchFragment (index + 1)
            _ hSkip hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hBranchCan := hBranchExecution'.2.mp hChildWitness
        have hAny : branches.any
            (fun branch => branch.2.CanCompleteBeforeTock) = true := by
          apply List.any_eq_true.mpr
          exact ⟨(action, branchType), hBranchMember, hBranchCan⟩
        simp [PactType.CanCompleteBeforeTock,
          branchCanCompleteBeforeTock_eq_any, hAny]
  have hEntryFuture : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry := by
    intro entry hEntry
    exact (hEntryFacts entry hEntry).1
  have hRootFutureEquality : computeFuture execution .root =
      computeFuture pending .root := by
    exact sequenceExecution_computeFuture_root_eq fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries hEntryFuture
  have hRootReach : execution.futureReachable .root =
      {.root} ∪ entries.biUnion execution.futureReachable := by
    exact sequenceExecution_futureReachable_root fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | xoffer_source =>
      constructor
      · have hPendingRoot := hWholeFuture .root
          (.xoffer elseType branches)
            (TypeCompilationRelation.xoffer_source elseType branches)
        rw [hParent] at hPendingRoot
        exact hRootFutureEquality.trans hPendingRoot
      · constructor
        · rintro ⟨completed, hReach, hCompleted⟩
          rw [hRootReach] at hReach
          simp only [Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hReach
          rcases hReach with hAtRoot | ⟨entry, hEntry, hAtEntry⟩
          · subst completed
            have hRootNotAccepting :
                (.root : TypeAutomatonState) ∉ fragment.accepting := by
              exact buildExclusiveOffer_root_not_accepting signature branches
                elseFragment branchAutomata
            have hRootCompleting : (.root : TypeAutomatonState) ∈
                fragment.completing := hCompleted.resolve_left
              hRootNotAccepting
            exact (hWholeCompleting .root (.xoffer elseType branches)
              (TypeCompilationRelation.xoffer_source elseType branches)).mp
                (by simpa [hParent] using hRootCompleting)
          · exact (hEntryFacts entry hEntry).2
              ⟨completed, hAtEntry, hCompleted⟩
        · intro hCanComplete
          have hRootCompleting :=
            (hWholeCompleting .root (.xoffer elseType branches)
              (TypeCompilationRelation.xoffer_source elseType branches)).mpr
                hCanComplete
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          right
          simpa [hParent] using hRootCompleting
  | xoffer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hChildCanonical := hElse.execution childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton elseFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton elseFragment).futureReachable
                    childState,
                  completed ∈ elseFragment.accepting ∨
                    completed ∈ elseFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, elseFragment,
          hElseStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState 0 childState),
              completed ∈ fragment.accepting ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState 0 child ∈ fragment.accepting ↔
              child ∈ elseFragment.accepting := by
          intro child
          exact buildExclusiveOffer_child0_accepting_iff signature branches
            elseFragment branchAutomata child
        have hComplete : ∀ child,
            Pact.childState 0 child ∈ fragment.completing ↔
              child ∈ elseFragment.completing := by
          intro child
          exact buildExclusiveOffer_child0_completing_iff signature branches
            elseFragment branchAutomata child
        exact (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
          hComplete).trans hChild.2
  | xoffer_branch _ branchType _ _ action index childState hSyntaxEntry
      hChildRelated =>
      have hBranchMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
          ⟨hBound, hValue⟩
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
        simp [branchAutomata, branchFragment, hSyntaxEntry]
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
      have hChildState : childState ∈ branchFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          branchType childState residual hChildRelated
        simpa [branchFragment, hBranchStable] using hCanonical
      have hTargets : branchFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel branchType
          hBranchFuel
      have hStates : branchFragment.states.image
          (Pact.childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨child, hChild, rfl⟩
        have hIndexedState : Pact.childState (index + 1) child ∈
            indexedFragmentStates branchAutomata := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((action, branchFragment), index), hZipEntry,
            by simp [childStates, Pact.childState, hChild]⟩
        simp [fragment, buildExclusiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hOutgoing : ∀ source edge,
          edge ∈ fragment.edges ∧
              edge.source = Pact.childState (index + 1) source ↔
            ∃ childEdge ∈ branchFragment.edges,
              childEdge.source = source ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro source edge
        simpa [fragment, branchFragment] using
          (buildExclusiveOfferAutomaton_outgoing_branch signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry source edge)
      have hChildCanonical :=
        (hBranches action branchType index hSyntaxEntry).execution childState
          residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton branchFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton branchFragment).futureReachable
                    childState,
                  completed ∈ branchFragment.accepting ∨
                    completed ∈ branchFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, branchFragment,
          hBranchStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          branchFragment (index + 1) hOutgoing hStates hTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            branchFragment (index + 1) hOutgoing hStates hTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState (index + 1) childState),
              completed ∈ fragment.accepting ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.accepting ↔
              child ∈ branchFragment.accepting := by
          intro child
          exact buildExclusiveOffer_branch_accepting_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry child
        have hComplete : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.completing ↔
              child ∈ branchFragment.completing := by
          intro child
          exact buildExclusiveOffer_branch_completing_iff signature branches
            elseFragment branchAutomata index (action, branchFragment)
              hAutomatonEntry child
        exact (taggedCompletionWitness_iff fragment branchFragment
          (index + 1) _ hSkip hComplete).trans hChild.2

theorem compilationProofBundle_xoffer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.xoffer elseType branches) := by
  have hFuture := compilationFutureCorrect_xoffer_regular_leaf signature
    elseType branches hSupports hElse hBranches
  have hBranchCompleting : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationCompletingCorrect signature branchType := by
    intro action branchType index hEntry
    exact (hBranches action branchType index hEntry).completing
  exact
    { future := hFuture
      completing := compilationCompletingCorrect_xoffer signature elseType
        branches hElse.completing hBranchCompleting
      scopedStep := compilationFragmentStepCorrect_xoffer_regular_leaf
        signature elseType branches hSignature hSupports hGuarded hTail
          hLinear hScoped hFuture hElse hBranches
      execution := compilationSequenceExecutionCorrect_xoffer_regular_leaf
        signature elseType branches hSupports hElse hBranches }

end

end Pact
