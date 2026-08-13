import Anvilpp.PactTypes.Correspondence.Offers.ExclusiveOfferGraph

/-!
# The resolved-edge classifier at the fresh exclusive-offer root
-/

namespace Pact

noncomputable section

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

end

end Pact
