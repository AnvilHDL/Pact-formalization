import Anvilpp.PactTypes.Correspondence.Offers.ConjunctiveOfferGraph

/-!
# The resolved-edge classifier at the fresh conjunctive-offer root
-/

namespace Pact

noncomputable section

/- Exact resolved-edge classifier at the fresh conjunctive-offer root. -/
private theorem buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) :
    let fragment := buildConjunctiveOfferAutomaton signature branches
      elseAutomaton conjunction
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    fragment.HasResolvedEdge .root env label offers target ↔
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate ≠ ∅ ∧
        label = TypeLabel.silent ∧ offers.current = ∅ ∧
        computeFuture pending (childState 0 conjunction.initial) =
          offers.future ∧ target = childState 0 conjunction.initial) ∨
      (env ∈ signature.localEnvironments ∧ env.clock = false ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future ≠ ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeWaitingOffers env branches ∧
        computeFuture pending .root \ typeWaitingOffers env branches =
          offers.future ∧ target = .root) ∨
      (env ∈ signature.localEnvironments ∧
        typeBranchNeeds branches ∩ env.immediate = ∅ ∧
        typeBranchNeeds branches ∩ env.future = ∅ ∧
        label = TypeLabel.silent ∧
        offers.current = typeBranchActions branches ∧
        computeFuture pending (childState 1 elseAutomaton.initial) =
          offers.future ∧ target = childState 1 elseAutomaton.initial) := by
  classical
  simp only [AutomatonFragment.HasResolvedEdge,
    buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  constructor
  · rintro ⟨edge, ((((hConjunction | hElseChild) | hEnabled) | hWait) |
      hElseEdge), hSource, hEnvironment, hLabel, hCurrent, hFuture, hTarget⟩
    · simp only [childPendingEdges, Finset.mem_image] at hConjunction
      rcases hConjunction with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [childPendingEdges, Finset.mem_image] at hElseChild
      rcases hElseChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
      rcases hEnabled with ⟨edgeEnvironment, hConditions, rfl⟩
      left
      simp only [Finset.sdiff_empty] at hFuture
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with ⟨hLocal, hImmediate⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      exact ⟨hLocal, hImmediate, hSemanticLabel, hCurrent.symm,
        hFuture, hTarget.symm⟩
    · simp only [Finset.mem_image, Finset.mem_filter] at hWait
      rcases hWait with ⟨edgeEnvironment, hConditions, rfl⟩
      right
      left
      simp only at hSource hEnvironment hLabel hCurrent hFuture hTarget
      rcases hConditions with
        ⟨hLocal, hClock, hImmediate, hFutureBranches⟩
      subst env
      have hSemanticLabel : label = TypeLabel.silent := by
        have hCongruence :=
          congrArg AutomatonConstructionLabel.semantic hLabel
        simpa using hCongruence.symm
      refine ⟨hLocal, hClock, hImmediate, hFutureBranches, hSemanticLabel,
        ?_, ?_, hTarget.symm⟩
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
  · rintro (hEnabled | hWait | hElse)
    · rcases hEnabled with ⟨hLocal, hImmediate, hLabel, hCurrent,
        hFuture, hTarget⟩
      refine ⟨
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 0 conjunction.initial) ∅
          target := childState 0 conjunction.initial },
        ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · left
        left
        right
        exact Finset.mem_image.mpr ⟨env,
          Finset.mem_filter.mpr ⟨hLocal, hImmediate⟩, rfl⟩
      · simpa [hLabel]
      · simpa using hCurrent.symm
      · simpa using hFuture
      · exact hTarget.symm
    · rcases hWait with ⟨hLocal, hClock, hImmediate, hFutureBranches,
        hLabel, hCurrent, hFuture, hTarget⟩
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
            ⟨hLocal, ⟨hClock, hImmediate, hFutureBranches⟩⟩, by
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
          current := typeBranchActions branches
          future := .at (childState 1 elseAutomaton.initial) ∅
          target := childState 1 elseAutomaton.initial },
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
