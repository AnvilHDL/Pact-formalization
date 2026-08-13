import Anvilpp.PactTypes.Correspondence.Offers.OfferStepCorrect

/-!
# compilationResolvedEdgeTargetsRelated_xoffer / _offer
-/

namespace Pact

noncomputable section

/-! ### Visible-edge target relatedness -/

theorem compilationResolvedEdgeTargetsRelated_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType)
    (hBranchTargets : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationResolvedEdgeTargetsRelated signature branchType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.xoffer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (typeBranchCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let branchAutomata := branches.map fun branch =>
    (branch.1, compileTypeFuel signature fuel branch.2)
  let fragment := buildExclusiveOfferAutomaton signature branches
    elseFragment branchAutomata
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.xoffer elseType branches))
      (.xoffer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | xoffer_source =>
      rw [hFragment] at hEdge
      rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment branchAutomata environment label
        offers target).mp hEdge with hBranch | hWait | hElse
      · rcases hBranch with ⟨indexed, hIndexed, _, _, _, _, _, _, hTarget⟩
        have hIndexedFields := List.mem_zipIdx hIndexed
        simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
          at hIndexedFields
        rcases hIndexedFields with ⟨hBound, hValue⟩
        have hBranchBound : indexed.2 < branches.length := by
          simpa [branchAutomata] using hBound
        let branch := branches[indexed.2]
        have hEntry : branches[indexed.2]? = some branch := by
          rw [List.getElem?_eq_getElem hBranchBound]
        have hIndexedValue : indexed.1 =
            (branch.1, compileTypeFuel signature fuel branch.2) := by
          rw [hValue]
          simp [branchAutomata, branch]
        rw [hIndexedValue] at hTarget
        subst target
        have hBranchMember : branch ∈ branches :=
          List.getElem_mem hBranchBound
        have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
          exact le_trans
            (typeCompilationFuel_le_typeBranchCompilationFuel branches branch
              hBranchMember)
            (by simp [fuel])
        have hInitial : TypeCompilationRelation branch.2
            (compileTypeFuel signature fuel branch.2).initial branch.2 :=
          compileTypeFuel_initial_relation signature fuel branch.2 hBranchFuel
        exact ⟨branch.2,
          TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
            branches branch.1 indexed.2 _ hEntry hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.xoffer elseType branches,
          TypeCompilationRelation.xoffer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.xoffer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_xoffer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
        elseType branches action branchType index hEntry hEdge with
        ⟨childTarget, rfl, hChildEdge⟩
      have hTargets : CompilationResolvedEdgeTargetsRelated signature
          branchType := hBranchTargets action branchType index hEntry
      rcases hTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.xoffer_branch elseType branchType
          targetResidual branches action index childTarget hEntry
          hTargetRelated⟩

theorem compilationResolvedEdgeTargetsRelated_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionTargets : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationResolvedEdgeTargetsRelated signature
          (parallelTypeBranchesSelecting selected branches))
    (hElseTargets : CompilationResolvedEdgeTargetsRelated signature elseType) :
    CompilationResolvedEdgeTargetsRelated signature
      (.offer elseType branches) := by
  classical
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun entry =>
    (entry.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting entry branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | offer_source =>
      rw [hFragment] at hEdge
      rcases hEdge with ⟨edge, hEdgeMem, hSource, _, _, _, _, hTarget⟩
      simp only [fragment, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union] at hEdgeMem
      rcases hEdgeMem with ((((hElse | hIndexed) | hEnabled) | hWait) |
        hResolved)
      · simp only [childPendingEdges, Finset.mem_image] at hElse
        rcases hElse with ⟨childEdge, _, rfl⟩
        simp [childPendingEdge, childState] at hSource
      · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hChild
          rcases hChild with ⟨childEdge, _, rfl⟩
          simp [childPendingEdge, childState] at hSource
      · rw [mem_foldl_union_iff] at hEnabled
        rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          rcases hNewEdge with ⟨edgeEnvironment, _, rfl⟩
          simp only [childPendingEdge] at hTarget
          have hIndexedFields := List.mem_zipIdx hIndexed
          simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
            at hIndexedFields
          rcases hIndexedFields with ⟨hBound, hValue⟩
          have hBranchBound : indexed.2 < branches.length := by
            simpa [selectedConjunctions] using hBound
          let branch := branches[indexed.2]
          have hEntry : branches[indexed.2]? = some branch := by
            rw [List.getElem?_eq_getElem hBranchBound]
          have hIndexedValue : indexed.1 =
              (branch.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)) := by
            rw [hValue]
            simp [selectedConjunctions, branch]
          rw [hIndexedValue] at hTarget
          subst target
          have hBranchFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting branch branches) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
            exact le_max_right _ _
          have hInitial : TypeCompilationRelation
              (parallelTypeBranchesSelecting branch branches)
              (compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting branch branches)).initial
              (parallelTypeBranchesSelecting branch branches) :=
            compileTypeFuel_initial_relation signature fuel
              (parallelTypeBranchesSelecting branch branches) hBranchFuel
          exact ⟨parallelTypeBranchesSelecting branch branches,
            TypeCompilationRelation.offer_branches elseType
              (parallelTypeBranchesSelecting branch branches) branches branch
              indexed.2 _ hEntry hInitial⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨edgeEnvironment, _, rfl⟩
        simp only [childPendingEdge] at hTarget
        subst target
        exact ⟨.offer elseType branches,
          TypeCompilationRelation.offer_source elseType branches⟩
      · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
        rcases hResolved with ⟨edgeEnvironment, _, rfl⟩
        simp only [childPendingEdge] at hTarget
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.offer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | offer_branches _ childResidual _ selected index childQ hEntry
      hChildRelated =>
      rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
        elseType branches selected index hEntry hEdge with
        ⟨childTarget, rfl, hChildEdge⟩
      rcases hConjunctionTargets selected index hEntry hChildRelated
        hChildEdge with ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_branches elseType targetResidual
          branches selected index childTarget hEntry hTargetRelated⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
/-
  classical
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  have hFragment : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
      (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  intro source residual environment label offers target hRelated hEdge
  cases hRelated with
  | offer_source =>
      rw [hFragment] at hEdge
      rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
        signature branches elseFragment conjunction environment label offers
        target).mp hEdge with hEnabled | hWait | hElse
      · rcases hEnabled with ⟨_, _, _, _, _, hTarget⟩
        subst target
        have hConjunctionFuel :
            TypeCompilationFuelSufficient conjunctionType fuel := by
          rw [TypeCompilationFuelSufficient,
            typeCompilationFuel_parallelTypeBranches]
          simp [fuel]
        have hInitial : TypeCompilationRelation conjunctionType
            conjunction.initial conjunctionType :=
          compileTypeFuel_initial_relation signature fuel conjunctionType
            hConjunctionFuel
        exact ⟨conjunctionType,
          TypeCompilationRelation.offer_branches elseType conjunctionType
            branches conjunction.initial hInitial⟩
      · rcases hWait with ⟨_, _, _, _, _, _, _, hTarget⟩
        subst target
        exact ⟨.offer elseType branches,
          TypeCompilationRelation.offer_source elseType branches⟩
      · rcases hElse with ⟨_, _, _, _, _, _, hTarget⟩
        subst target
        have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
          simp [TypeCompilationFuelSufficient, fuel]
        have hInitial : TypeCompilationRelation elseType
            elseFragment.initial elseType :=
          compileTypeFuel_initial_relation signature fuel elseType hElseFuel
        exact ⟨elseType,
          TypeCompilationRelation.offer_else elseType elseType branches
            elseFragment.initial hInitial⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
        elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hConjunctionTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_branches elseType targetResidual
          branches childTarget hTargetRelated⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      rcases compileTypeFuel_offer_else_child_edge_cases signature elseType
        branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
      rcases hElseTargets hChildRelated hChildEdge with
        ⟨targetResidual, hTargetRelated⟩
      exact ⟨targetResidual,
        TypeCompilationRelation.offer_else elseType targetResidual branches
          childTarget hTargetRelated⟩
-/

end

end Pact
