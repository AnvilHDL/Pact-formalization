import Anvilpp.PactTypes.NewCorrespondence.Helpers.RecursionRelations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def xofferRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.xoffer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i action branchType q,
      branches[i]? = some (action, branchType) ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet branchType (compileType signature branchType))
        entry.1 q)

set_option maxHeartbeats 4000000 in
/-- Proves every related exclusive-offer pair has the exclusive-offer shape. -/
lemma relationMembership_xoffer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)))
        residual state) :
    xofferRelationShape signature elseType branches (residual, state) := by
  have hFuelEq : typeCompilationFuel (.xoffer elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩ |
      ⟨item, hItem, entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · subst hResidual
    subst hState
    have hElseRelated : relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
          elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
        (le_max_left _ _) le_rfl]
      exact hEntry
    exact Or.inr (Or.inl ⟨entry.2, rfl, hElseRelated⟩)
  · subst hResidual
    subst hState
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hBranchMem : item.1 ∈ branches := List.mem_of_getElem? hGet
    have hBranchFuel : typeCompilationFuel item.1.2 ≤
        max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches) :=
      le_trans
        (typeCompilationFuel_le_typeBranchCompilationFuel
          branches item.1 hBranchMem)
        (le_max_right _ _)
    have hBranchRelated : relationMembership
        (buildRelationSet item.1.2 (compileType signature item.1.2))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel item.1.2)
          item.1.2
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature item.1.2
        hBranchFuel le_rfl]
      exact hEntry
    exact Or.inr (Or.inr ⟨item.2, item.1.1, item.1.2, entry.2,
      hGet, rfl, hBranchRelated⟩)
  -- have hElseFuel : typeCompilationFuel elseType ≤
  --     typeCompilationFuel (.xoffer elseType branches) := by
  --   simp only [typeCompilationFuel]; omega
  -- have hElseFuelStrict : typeCompilationFuel elseType + 1 ≤
  --     typeCompilationFuel (.xoffer elseType branches) := by
  --   simp only [typeCompilationFuel]; omega
  -- have hBranchFuel : ∀ branch ∈ branches,
  --     typeCompilationFuel branch.2 ≤ typeCompilationFuel (.xoffer elseType branches) := by
  --   intro branch hBranch
  --   have h1 := typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch
  --   simp only [typeCompilationFuel]; omega
  -- have hBranchFuelStrict : ∀ branch ∈ branches,
  --     typeCompilationFuel branch.2 + 1 ≤
  --       typeCompilationFuel (.xoffer elseType branches) := by
  --   intro branch hBranch
  --   have h1 := typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch
  --   simp only [typeCompilationFuel]; omega
  -- have hFuelEq : typeCompilationFuel (.xoffer elseType branches) =
  --     max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
  --   simp only [typeCompilationFuel]; omega
  -- have hWhole :
  --     compileTypeFuel signature (typeCompilationFuel (.xoffer elseType branches))
  --       (.xoffer elseType branches) =
  --       buildExclusiveOfferAutomaton signature branches
  --         (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --         (branches.map fun branch => (branch.1, compileTypeFuel signature
  --           (typeCompilationFuel branch.2) branch.2)) := by
  --   rw [hFuelEq]
  --   show buildExclusiveOfferAutomaton signature branches
  --       (compileTypeFuel signature
  --         (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) elseType)
  --       (branches.map fun branch => (branch.1, compileTypeFuel signature
  --         (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches))
  --         branch.2)) =
  --     buildExclusiveOfferAutomaton signature branches
  --       (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --       (branches.map fun branch => (branch.1, compileTypeFuel signature
  --         (typeCompilationFuel branch.2) branch.2))
  --   congr 1
  --   · exact compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl
  --   · apply List.map_congr_left
  --     intro branch hBranch
  --     congr 1
  --     exact compileTypeFuel_eq_of_sufficient signature branch.2
  --       (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
  --         (le_max_right _ _)) le_rfl
  -- have hInit : (compileType signature (.xoffer elseType branches)).initial =
  --     TypeAutomatonState.root := by
  --   show (compileTypeFuel signature (typeCompilationFuel (.xoffer elseType branches))
  --     (.xoffer elseType branches)).initial = TypeAutomatonState.root
  --   rw [hWhole]
  --   simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
  -- have hRootRelated : relationMembership
  --     (buildRelationSet (.xoffer elseType branches)
  --       (compileType signature (.xoffer elseType branches)))
  --     (.xoffer elseType branches) TypeAutomatonState.root := by
  --   rw [← hInit]
  --   exact buildRelationSet_initial (.xoffer elseType branches)
  --     (compileType signature (.xoffer elseType branches))
  -- have hRootFuture : computeFutureOf signature (.xoffer elseType branches)
  --     TypeAutomatonState.root = typeFutureOffers (.xoffer elseType branches) :=
  --   helper_h15_future_offers_agree signature hRootRelated
  -- refine buildRelationSet_preserves (.xoffer elseType branches)
  --   (compileType signature (.xoffer elseType branches))
  --   (xofferRelationShape signature elseType branches)
  --   (by
  --     show xofferRelationShape signature elseType branches
  --       (.xoffer elseType branches,
  --         (compileType signature (.xoffer elseType branches)).initial)
  --     rw [hInit]; exact Or.inl rfl)
  --   (by
  --     intro entry hEntry successor hSuccessor
  --     rcases relationSuccessors_mem_cases (compileType signature (.xoffer elseType branches))
  --       entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature (.xoffer elseType branches)
  --       (show (compileType signature (.xoffer elseType branches)).HasEdge edge.source
  --         edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
  --         from hEdgeMem)
  --     have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
  --       (.xoffer elseType branches) edge.source edge.target edge.symbol.environment
  --       edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
  --     rw [hWhole] at hResolved
  --     obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
  --       hPTarget⟩ := hResolved
  --     rcases hEntry with hRoot |
  --       ⟨q, hStateEq, hMem⟩ |
  --       ⟨i, action, branchType, q, hBranchesEq, hStateEq, hMem⟩
  --     · -- root case: entry represents the whole exclusive offer; the three
  --       -- root-edge families reconstruct the matching semantic offer rule.
  --       have hEntry1 : entry.1 = .xoffer elseType branches := by rw [hRoot]
  --       have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
  --         rw [hPSource, hSource, hRoot]
  --       simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
  --         at hPendingMem
  --       rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved2)
  --       · exfalso
  --         simp only [childPendingEdges, Finset.mem_image] at hElse
  --         obtain ⟨childEdge, _, hEq⟩ := hElse
  --         rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · exfalso
  --         rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
  --         rcases hIndexed with hEmpty | ⟨indexed, _, hNewEdge⟩
  --         · simp at hEmpty
  --         · simp only [childPendingEdges, Finset.mem_image] at hNewEdge
  --           obtain ⟨childEdge, _, hEq⟩ := hNewEdge
  --           rw [← hEq] at hRootSource
  --           simp [childPendingEdge, childState] at hRootSource
  --       · -- fire family: reconstructs `xoffer_branch`
  --         rw [mem_foldl_union_iff] at hBranch
  --         rcases hBranch with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
  --         · simp at hEmpty
  --         · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
  --           obtain ⟨⟨branchAction, automaton⟩, index⟩ := indexed
  --           rcases hNewEdge with ⟨environment, ⟨hEnvMem, hEnabled, hResolvedNeeds⟩, rfl⟩
  --           have hIndexedGet :
  --               (branches.map fun branch => (branch.1, compileTypeFuel signature
  --                 (typeCompilationFuel branch.2) branch.2))[index]? =
  --                 some (branchAction, automaton) :=
  --             List.mk_mem_zipIdx_iff_getElem?.mp hIndexedEntry
  --           obtain ⟨branchType', hBranchGet, hAutEq⟩ :=
  --             (branches_map_getElem?_eq_some_iff signature branches index branchAction
  --               automaton).mp hIndexedGet
  --           have hWF : environment.WellFormed :=
  --             localEnvironment_wellFormed signature hEnvMem
  --           have hBranchMem : (branchAction, branchType') ∈ branches :=
  --             List.mem_iff_getElem?.mpr ⟨index, hBranchGet⟩
  --           simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --           have hLabelEq : edge.symbol.label = TypeLabel.message branchAction.1
  --               branchAction.2 := by injection hPLabel.symm
  --           have hCurrentEq : edge.symbol.offers.current = {branchAction} := hPCurrent.symm
  --           have hFutureEq : edge.symbol.offers.future = typeFutureOffers branchType' := by
  --             rw [← hPFuture, ← hAutEq, computeFutureOf_exclusiveOffer_branch signature
  --               elseType branches (.xoffer elseType branches) hWhole index branchAction
  --               branchType' hBranchGet (hBranchFuelStrict (branchAction, branchType')
  --                 hBranchMem) (compileTypeFuel signature (typeCompilationFuel branchType')
  --                 branchType').initial (compileTypeFuel_initial_mem signature
  --                 (typeCompilationFuel branchType') branchType' le_rfl), Finset.sdiff_empty]
  --             show computeFutureOf signature branchType' (compileType signature
  --               branchType').initial = typeFutureOffers branchType'
  --             exact helper_h15_future_offers_agree signature
  --               (buildRelationSet_initial branchType' (compileType signature branchType'))
  --           have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk {branchAction}
  --               (typeFutureOffers branchType') := by
  --             rw [show edge.symbol.offers = TypeOfferSummary.mk
  --               edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --               hCurrentEq, hFutureEq]
  --           have hResidualEq : successor.1 = branchType' := by
  --             rw [hEntry1] at hStep
  --             rw [hLabelEq, hOffersEq] at hStep
  --             exact decoratedTypeTransition_target_unique hStep
  --               (hPEnv ▸ ⟨TypeTransition.xoffer_branch environment elseType branches
  --                 branchAction branchType'
  --                 ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩,
  --                 TypeOffers.xoffer_branch environment elseType branches
  --                   branchAction branchType'
  --                   ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩⟩)
  --           have hTargetEq : successor.2 = .child (index + 1)
  --               (compileTypeFuel signature (typeCompilationFuel branchType')
  --                 branchType').initial := by
  --             rw [hTarget, ← hPTarget, ← hAutEq]
  --           exact Or.inr (Or.inr ⟨index, branchAction, branchType',
  --             (compileTypeFuel signature (typeCompilationFuel branchType') branchType').initial,
  --             hBranchGet, hTargetEq, hResidualEq ▸
  --               buildRelationSet_initial branchType' (compileType signature branchType')⟩)
  --       · -- wait family: a silent self-loop, reconstructs `xoffer_wait`
  --         simp only [Finset.mem_image, Finset.mem_filter] at hWait
  --         rcases hWait with ⟨environment, ⟨hEnvMem, hClock, hUnresolved⟩, rfl⟩
  --         have hWF : environment.WellFormed := localEnvironment_wellFormed signature hEnvMem
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current =
  --             typeWaitingOffers environment branches := hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future =
  --             typeFutureOffers (.xoffer elseType branches) \
  --               typeWaitingOffers environment branches := by
  --           rw [← hPFuture, hRootFuture]
  --           rfl
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk
  --             (typeWaitingOffers environment branches)
  --             (typeFutureOffers (.xoffer elseType branches) \
  --               typeWaitingOffers environment branches) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hResidualEq : successor.1 = .xoffer elseType branches := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             (hPEnv ▸ ⟨TypeTransition.xoffer_wait environment elseType branches
  --               ⟨hWF, hUnresolved, hClock⟩,
  --               TypeOffers.xoffer_wait environment elseType branches
  --                 ⟨hWF, hUnresolved, hClock⟩⟩)
  --         have hTargetEq : successor.2 = TypeAutomatonState.root := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inl (by rw [show successor = (successor.1, successor.2) from rfl,
  --           hResidualEq, hTargetEq])
  --       · -- else family: reconstructs `xoffer_else`
  --         simp only [Finset.mem_image, Finset.mem_filter] at hResolved2
  --         rcases hResolved2 with ⟨environment, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
  --         have hWF : environment.WellFormed := localEnvironment_wellFormed signature hEnvMem
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current = ∅ := hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future = typeFutureOffers elseType := by
  --           rw [← hPFuture, computeFutureOf_exclusiveOffer_else signature elseType branches
  --             (.xoffer elseType branches) hWhole hElseFuelStrict
  --             (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
  --             (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
  --               le_rfl), Finset.sdiff_empty]
  --           show computeFutureOf signature elseType (compileType signature elseType).initial =
  --             typeFutureOffers elseType
  --           exact helper_h15_future_offers_agree signature
  --             (buildRelationSet_initial elseType (compileType signature elseType))
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk ∅
  --             (typeFutureOffers elseType) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hResidualEq : successor.1 = elseType := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             (hPEnv ▸ ⟨TypeTransition.xoffer_else environment elseType branches
  --               ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
  --               TypeOffers.xoffer_else environment elseType branches
  --                 ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩)
  --         have hTargetEq : successor.2 = .child 0
  --             (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel elseType)
  --           elseType).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial elseType (compileType signature elseType)⟩)
  --     · -- else-child case: entry is already related to `q` inside `elseType`'s own relation
  --       have hChildSource : pendingEdge.source = .child 0 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildExclusiveOfferAutomaton_outgoing_else signature branches
  --           (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --           (branches.map fun branch => (branch.1, compileTypeFuel signature
  --             (typeCompilationFuel branch.2) branch.2)) q pendingEdge).mp
  --           ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature elseType).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature elseType q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r
  --                 hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_exclusiveOffer_else signature elseType branches
  --                 (.xoffer elseType branches) hWhole hElseFuelStrict t hStateMem]
  --       have hTargetEq : successor.2 = .child 0 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique elseType (compileType signature elseType)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inl ⟨childEdge.target, hTargetEq, hInnerMem⟩)
  --     · -- branch-child case: entry is already related to `q` inside branch `i`'s own relation
  --       have hChildSource : pendingEdge.source = .child (i + 1) q := by
  --         rw [hPSource, hSource, hStateEq]
  --       have hAutomataGet :
  --           (branches.map fun branch => (branch.1, compileTypeFuel signature
  --             (typeCompilationFuel branch.2) branch.2))[i]? =
  --             some (action, compileTypeFuel signature (typeCompilationFuel branchType)
  --               branchType) :=
  --         (branches_map_getElem?_eq_some_iff signature branches i action
  --           (compileTypeFuel signature (typeCompilationFuel branchType) branchType)).mpr
  --           ⟨branchType, hBranchesEq, rfl⟩
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildExclusiveOfferAutomaton_outgoing_branch signature branches
  --           (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --           (branches.map fun branch => (branch.1, compileTypeFuel signature
  --             (typeCompilationFuel branch.2) branch.2))
  --           i action (compileTypeFuel signature (typeCompilationFuel branchType) branchType)
  --           hAutomataGet q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature branchType).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature branchType q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hBranchMem : (action, branchType) ∈ branches :=
  --                 List.mem_iff_getElem?.mpr ⟨i, hBranchesEq⟩
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel branchType) branchType le_rfl childEdge hChildEdgeMem
  --                 t r hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
  --                 (.xoffer elseType branches) hWhole i action branchType hBranchesEq
  --                 (hBranchFuelStrict (action, branchType) hBranchMem) t hStateMem]
  --       have hTargetEq : successor.2 = .child (i + 1) childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique branchType (compileType signature branchType)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inr ⟨i, action, branchType, childEdge.target, hBranchesEq, hTargetEq,
  --         hInnerMem⟩))
  --   (residual, state) hRelated

/-- Proves a `.child 0`-tagged state's future menu, in a compiled conjunctive offer, agrees with the else child's own. -/
theorem computeFutureOf_selectedConjunctiveOffer_else
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildSelectedConjunctiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))))
    (hFuel : typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel elseType)
      elseType).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature elseType state := by
  sorry

/-- Proves a `.child (i+1)`-tagged state's future menu, in a compiled conjunctive offer, agrees with branch `i`'s generated commit type's own. -/
theorem computeFutureOf_selectedConjunctiveOffer_branch
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildSelectedConjunctiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))))
    (i : Nat) (selected : BareMessage × PactType)
    (hSelected : branches[i]? = some selected)
    (hFuel : typeCompilationFuel (parallelTypeBranchesSelecting selected branches) +
      1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature
      (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
      (parallelTypeBranchesSelecting selected branches)).states) :
    computeFutureOf signature whole (.child (i + 1) state) =
      computeFutureOf signature (parallelTypeBranchesSelecting selected branches)
        state := by
  sorry

/-- Characterizes a public conjunctive-offer edge leaving a tagged else-child state as a copy of the else automaton's own outgoing edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_else
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl
        ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

/-- Characterizes a public conjunctive-offer edge leaving a tagged branch-`i`-child state as a copy of that branch's generated commit type's own outgoing edge. -/
theorem buildSelectedConjunctiveOfferAutomaton_outgoing_branch
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let offer := buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions
    edge ∈ offer.edges ∧ edge.source = .child (i + 1) state ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet :
              selectedConjunctions[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton :=
          congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childPendingEdges, Finset.mem_union,
        Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Relates a branch's generated commit type found by index after mapping compiled fragments in to the same branch found by index in the original list. -/
theorem branches_map_selecting_getElem?_eq_some_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment) :
    (branches.map fun selected => (selected.1, compileTypeFuel signature
        (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
        (parallelTypeBranchesSelecting selected branches)))[i]? =
        some (action, automaton) ↔
      ∃ branchType, branches[i]? = some (action, branchType) ∧
        compileTypeFuel signature
          (typeCompilationFuel
            (parallelTypeBranchesSelecting (action, branchType) branches))
          (parallelTypeBranchesSelecting (action, branchType) branches) =
          automaton := by
  rw [List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨branchAction, branchType⟩, hGet, hEq⟩
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨hAction, hAut⟩ := hEq
    subst hAction
    exact ⟨branchType, hGet, hAut⟩
  · rintro ⟨branchType, hGet, hAut⟩
    exact ⟨(action, branchType), hGet, by simp [hAut]⟩

/-- Defines the related-state shape for a compiled conjunctive offer: the root represents the whole offer, a tagged child represents a residual of `τ0` or a generated branch commit. -/
def offerRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.offer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i selected q,
      branches[i]? = some selected ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting selected branches)
          (compileType signature
            (parallelTypeBranchesSelecting selected branches)))
        entry.1 q)

set_option maxHeartbeats 4000000 in
/-- Proves every related conjunctive-offer pair has the conjunctive-offer shape. -/
lemma relationMembership_offer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.offer elseType branches)
          (compileType signature (.offer elseType branches)))
        residual state) :
    offerRelationShape signature elseType branches (residual, state) := by
  have hFuelEq : typeCompilationFuel (.offer elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    mem_foldl_union_iff, Finset.notMem_empty, false_or,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩ |
      ⟨item, hItem, entry, hEntry, hResidual, hState⟩
  · exact Or.inl (Prod.ext hResidual hState)
  · subst hResidual
    subst hState
    have hElseRelated : relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel elseType)
          elseType
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature elseType
        (le_max_left _ _) le_rfl]
      exact hEntry
    exact Or.inr (Or.inl ⟨entry.2, rfl, hElseRelated⟩)
  · subst hResidual
    subst hState
    have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hItem
    have hSelectedFuel :
        typeCompilationFuel
            (parallelTypeBranchesSelecting item.1 branches) ≤
          max (typeCompilationFuel elseType)
            (conjunctiveCompilationFuel branches) := by
      rw [typeCompilationFuel_parallelTypeBranchesSelecting]
      exact le_max_right _ _
    have hSelectedRelated : relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting item.1 branches)
          (compileType signature
            (parallelTypeBranchesSelecting item.1 branches)))
        entry.1 entry.2 := by
      show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature
          (typeCompilationFuel
            (parallelTypeBranchesSelecting item.1 branches))
          (parallelTypeBranchesSelecting item.1 branches)
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature
        (parallelTypeBranchesSelecting item.1 branches)
        hSelectedFuel le_rfl]
      exact hEntry
    exact Or.inr (Or.inr ⟨item.2, item.1, entry.2,
      hGet, rfl, hSelectedRelated⟩)
  -- refine buildRelationSet_preserves (.offer elseType branches)
  --   (compileType signature (.offer elseType branches))
  --   (offerRelationShape signature elseType branches)
  --   (by
  --     show offerRelationShape signature elseType branches
  --       (.offer elseType branches,
  --         (compileType signature (.offer elseType branches)).initial)
  --     rw [hInit]; exact Or.inl rfl)
  --   (by
  --     intro entry hEntry successor hSuccessor
  --     rcases relationSuccessors_mem_cases (compileType signature (.offer elseType branches))
  --       entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature (.offer elseType branches)
  --       (show (compileType signature (.offer elseType branches)).HasEdge edge.source
  --         edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
  --         from hEdgeMem)
  --     have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
  --       (.offer elseType branches) edge.source edge.target edge.symbol.environment
  --       edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
  --     rw [hWhole] at hResolved
  --     obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
  --       hPTarget⟩ := hResolved
  --     rcases hEntry with hRoot |
  --       ⟨q, hStateEq, hMem⟩ |
  --       ⟨i, selected, q, hBranchesEq, hStateEq, hMem⟩
  --     · -- root case: entry represents the whole conjunctive offer; the three
  --       -- root-edge families reconstruct the matching semantic offer rule.
  --       have hEntry1 : entry.1 = .offer elseType branches := by rw [hRoot]
  --       have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
  --         rw [hPSource, hSource, hRoot]
  --       simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
  --         Finset.mem_union] at hPendingMem
  --       rcases hPendingMem with ((((hElse | hIndexed) | hEnabledFamily) | hWait) | hResolved2)
  --       · exfalso
  --         simp only [childPendingEdges, Finset.mem_image] at hElse
  --         obtain ⟨childEdge, _, hEq⟩ := hElse
  --         rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · exfalso
  --         rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
  --         rcases hIndexed with hEmpty | ⟨indexed, _, hNewEdge⟩
  --         · simp at hEmpty
  --         · simp only [childPendingEdges, Finset.mem_image] at hNewEdge
  --           obtain ⟨childEdge, _, hEq⟩ := hNewEdge
  --           rw [← hEq] at hRootSource
  --           simp [childPendingEdge, childState] at hRootSource
  --       · -- fire family: reconstructs `offer_some`
  --         rw [mem_foldl_union_iff] at hEnabledFamily
  --         rcases hEnabledFamily with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
  --         · simp at hEmpty
  --         · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
  --           obtain ⟨⟨branchAction, automaton⟩, index⟩ := indexed
  --           rcases hNewEdge with ⟨environment, ⟨hEnvMem, hEnabled⟩, rfl⟩
  --           have hIndexedGet :
  --               (branches.map fun selected => (selected.1, compileTypeFuel signature
  --                 (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
  --                 (parallelTypeBranchesSelecting selected branches)))[index]? =
  --                 some (branchAction, automaton) :=
  --             List.mk_mem_zipIdx_iff_getElem?.mp hIndexedEntry
  --           obtain ⟨branchType', hBranchGet, hAutEq⟩ :=
  --             (branches_map_selecting_getElem?_eq_some_iff signature branches index
  --               branchAction automaton).mp hIndexedGet
  --           have hWF : environment.WellFormed :=
  --             localEnvironment_wellFormed signature hEnvMem
  --           have hSelectedMem : (branchAction, branchType') ∈ branches :=
  --             List.mem_iff_getElem?.mpr ⟨index, hBranchGet⟩
  --           simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --           have hLabelEq : edge.symbol.label = TypeLabel.silent := by
  --             injection hPLabel.symm
  --           have hCurrentEq : edge.symbol.offers.current = ∅ := hPCurrent.symm
  --           have hFutureEq : edge.symbol.offers.future =
  --               typeFutureOffers (parallelTypeBranchesSelecting
  --                 (branchAction, branchType') branches) := by
  --             rw [← hPFuture, ← hAutEq, computeFutureOf_selectedConjunctiveOffer_branch
  --               signature elseType branches (.offer elseType branches) hWhole index
  --               (branchAction, branchType') hBranchGet
  --               (hBranchFuelStrict (branchAction, branchType'))
  --               (compileTypeFuel signature (typeCompilationFuel
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches))
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial
  --               (compileTypeFuel_initial_mem signature (typeCompilationFuel
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches))
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches)
  --                 le_rfl), Finset.sdiff_empty]
  --             show computeFutureOf signature
  --               (parallelTypeBranchesSelecting (branchAction, branchType') branches)
  --               (compileType signature
  --                 (parallelTypeBranchesSelecting (branchAction, branchType')
  --                   branches)).initial =
  --               typeFutureOffers (parallelTypeBranchesSelecting
  --                 (branchAction, branchType') branches)
  --             exact helper_h15_future_offers_agree signature
  --               (buildRelationSet_initial
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches)
  --                 (compileType signature
  --                   (parallelTypeBranchesSelecting (branchAction, branchType') branches)))
  --           have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk ∅
  --               (typeFutureOffers (parallelTypeBranchesSelecting
  --                 (branchAction, branchType') branches)) := by
  --             rw [show edge.symbol.offers = TypeOfferSummary.mk
  --               edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --               hCurrentEq, hFutureEq]
  --           have hResidualEq : successor.1 =
  --               parallelTypeBranchesSelecting (branchAction, branchType') branches := by
  --             rw [hEntry1] at hStep
  --             rw [hLabelEq, hOffersEq] at hStep
  --             exact decoratedTypeTransition_target_unique hStep
  --               (hPEnv ▸ ⟨TypeTransition.offer_some environment elseType branches
  --                 (branchAction, branchType')
  --                 ⟨hWF, hSelectedMem, hEnabled⟩,
  --                 TypeOffers.offer_some environment elseType branches
  --                   (branchAction, branchType')
  --                   ⟨hWF, hSelectedMem, hEnabled⟩⟩)
  --           have hTargetEq : successor.2 = .child (index + 1)
  --               (compileTypeFuel signature (typeCompilationFuel
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches))
  --                 (parallelTypeBranchesSelecting
  --                   (branchAction, branchType') branches)).initial := by
  --             rw [hTarget, ← hPTarget, ← hAutEq]
  --           exact Or.inr (Or.inr ⟨index, (branchAction, branchType'),
  --             (compileTypeFuel signature (typeCompilationFuel
  --               (parallelTypeBranchesSelecting (branchAction, branchType') branches))
  --               (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial,
  --             hBranchGet, hTargetEq, hResidualEq ▸
  --               buildRelationSet_initial
  --                 (parallelTypeBranchesSelecting (branchAction, branchType') branches)
  --                 (compileType signature
  --                   (parallelTypeBranchesSelecting (branchAction, branchType')
  --                     branches))⟩)
  --       · -- wait family: a silent self-loop, reconstructs `offer_wait`
  --         simp only [Finset.mem_image, Finset.mem_filter] at hWait
  --         rcases hWait with ⟨environment, ⟨hEnvMem, hClock, hNoImmediate, hUnresolved⟩, rfl⟩
  --         have hWF : environment.WellFormed := localEnvironment_wellFormed signature hEnvMem
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current =
  --             typeWaitingOffers environment branches := hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future =
  --             typeFutureOffers (.offer elseType branches) \
  --               typeWaitingOffers environment branches := by
  --           rw [← hPFuture, hRootFuture]
  --           rfl
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk
  --             (typeWaitingOffers environment branches)
  --             (typeFutureOffers (.offer elseType branches) \
  --               typeWaitingOffers environment branches) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hResidualEq : successor.1 = .offer elseType branches := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             (hPEnv ▸ ⟨TypeTransition.offer_wait environment elseType branches
  --               ⟨hWF, hNoImmediate, hUnresolved, hClock⟩,
  --               TypeOffers.offer_wait environment elseType branches
  --                 ⟨hWF, hNoImmediate, hUnresolved, hClock⟩⟩)
  --         have hTargetEq : successor.2 = TypeAutomatonState.root := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inl (by rw [show successor = (successor.1, successor.2) from rfl,
  --           hResidualEq, hTargetEq])
  --       · -- else family: reconstructs `offer_else`
  --         simp only [Finset.mem_image, Finset.mem_filter] at hResolved2
  --         rcases hResolved2 with ⟨environment, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
  --         have hWF : environment.WellFormed := localEnvironment_wellFormed signature hEnvMem
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current = typeBranchActions branches :=
  --           hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future = typeFutureOffers elseType := by
  --           rw [← hPFuture, computeFutureOf_selectedConjunctiveOffer_else signature elseType
  --             branches (.offer elseType branches) hWhole hElseFuelStrict
  --             (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
  --             (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
  --               le_rfl), Finset.sdiff_empty]
  --           show computeFutureOf signature elseType (compileType signature elseType).initial =
  --             typeFutureOffers elseType
  --           exact helper_h15_future_offers_agree signature
  --             (buildRelationSet_initial elseType (compileType signature elseType))
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk (typeBranchActions branches)
  --             (typeFutureOffers elseType) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hResidualEq : successor.1 = elseType := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             (hPEnv ▸ ⟨TypeTransition.offer_else environment elseType branches
  --               ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
  --               TypeOffers.offer_else environment elseType branches
  --                 ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩)
  --         have hTargetEq : successor.2 = .child 0
  --             (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel elseType)
  --           elseType).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial elseType (compileType signature elseType)⟩)
  --     · -- else-child case: entry is already related to `q` inside `elseType`'s own relation
  --       have hChildSource : pendingEdge.source = .child 0 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
  --           (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --           (branches.map fun selected => (selected.1, compileTypeFuel signature
  --             (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
  --             (parallelTypeBranchesSelecting selected branches))) q pendingEdge).mp
  --           ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature elseType).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature elseType q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r
  --                 hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
  --                 (.offer elseType branches) hWhole hElseFuelStrict t hStateMem]
  --       have hTargetEq : successor.2 = .child 0 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique elseType (compileType signature elseType)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inl ⟨childEdge.target, hTargetEq, hInnerMem⟩)
  --     · -- branch-child case: entry is already related to `q` inside branch `i`'s
  --       -- generated commit type's own relation
  --       have hChildSource : pendingEdge.source = .child (i + 1) q := by
  --         rw [hPSource, hSource, hStateEq]
  --       have hAutomataGet :
  --           (branches.map fun selected' => (selected'.1, compileTypeFuel signature
  --             (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
  --             (parallelTypeBranchesSelecting selected' branches)))[i]? =
  --             some (selected.1, compileTypeFuel signature (typeCompilationFuel
  --               (parallelTypeBranchesSelecting selected branches))
  --               (parallelTypeBranchesSelecting selected branches)) := by
  --         rw [List.getElem?_map, hBranchesEq]
  --         rfl
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildSelectedConjunctiveOfferAutomaton_outgoing_branch signature branches
  --           (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
  --           (branches.map fun selected' => (selected'.1, compileTypeFuel signature
  --             (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
  --             (parallelTypeBranchesSelecting selected' branches)))
  --           i selected.1 (compileTypeFuel signature (typeCompilationFuel
  --             (parallelTypeBranchesSelecting selected branches))
  --             (parallelTypeBranchesSelecting selected branches))
  --           hAutomataGet q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature
  --           (parallelTypeBranchesSelecting selected branches)).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature
  --           (parallelTypeBranchesSelecting selected branches) q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
  --                 (parallelTypeBranchesSelecting selected branches) le_rfl childEdge
  --                 hChildEdgeMem t r hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
  --                 (.offer elseType branches) hWhole i selected hBranchesEq
  --                 (hBranchFuelStrict selected) t hStateMem]
  --       have hTargetEq : successor.2 = .child (i + 1) childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique
  --           (parallelTypeBranchesSelecting selected branches)
  --           (compileType signature (parallelTypeBranchesSelecting selected branches))
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inr ⟨i, selected, childEdge.target, hBranchesEq, hTargetEq,
  --         hInnerMem⟩))
  --   (residual, state) hRelated


end

end Pact
