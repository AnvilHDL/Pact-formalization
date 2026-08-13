import Anvilpp.PactTypes.Correspondence.Offers.OfferEdgeClassifiers

/-!
# compilationFragmentStepCorrect_xoffer, compilationScopedFragmentStepCorrect_xoffer, compilationStepCorrect_xoffer
-/

namespace Pact

noncomputable section

/-- Exclusive offers preserve raw pending-fragment step correspondence. -/
theorem compilationFragmentStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationFragmentStepCorrect signature (.xoffer elseType branches) := by
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
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | xoffer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | xoffer_branch _ _ _ action _ hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled, hResolved⟩
            rcases TypeOffers.xoffer_branch_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient residual' fuel := by
              exact le_trans
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, residual') hBranchMember)
                (by simp [fuel])
            let branchFragment := compileTypeFuel signature fuel residual'
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation signature fuel residual'
                hBranchFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            have hAutomatonEntry : branchAutomata[index]? =
                some (action, branchFragment) := by
              simp [branchAutomata, branchFragment, hEntry]
            rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
              ⟨hBound, hValue⟩
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa using hBound
            have hZipEntry : ((action, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            refine ⟨childState (index + 1) branchFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              (TypeLabel.message action.1 action.2) ⟨current, future⟩
              (childState (index + 1) branchFragment.initial)).mpr
            left
            exact ⟨((action, branchFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hImmediate, hResolved⟩
            rcases TypeOffers.xoffer_else_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hImmediate, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_wait _ _ _ hConditions =>
            rcases hConditions with ⟨_, hUnresolved, hClock⟩
            rcases TypeOffers.xoffer_wait_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.xoffer elseType branches) .root
                (.xoffer elseType branches) :=
              TypeCompilationRelation.xoffer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, by
                simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent,
              hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment branchAutomata env label
          ⟨current, future⟩
          target).mp hEdge with hBranch | hWait | hElse
        · rcases hBranch with ⟨indexed, hIndexed, _, hEnabled, hResolved,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
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
          rw [hIndexedValue] at hEnabled hLabel hCurrent hEdgeFuture hTargetState
          subst target
          have hBranchMember : branch ∈ branches :=
            List.getElem_mem hBranchBound
          have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                branch hBranchMember)
              (by simp [fuel])
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation signature fuel branch.2
              hBranchFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel branch.2).initial)
              branch.2 :=
            TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
              branches branch.1 indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers branch.2 := hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
          · exact
              (TypeOffers.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
        · rcases hWait with ⟨_, hClock, hFutureBranches, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.xoffer elseType branches) .root
              (.xoffer elseType branches) :=
            TypeCompilationRelation.xoffer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
          · exact
              (TypeOffers.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
        · rcases hElse with ⟨_, hImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
          · exact
              (TypeOffers.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr
            hChildEdge
        · exact TypeCompilationRelation.xoffer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      constructor
      · intro hSemanticStep
        rcases (hStep hChildRelated hLocalEnvironment).mp hSemanticStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_branch_child_edge_iff signature
            elseType branches action branchType index hEntry childQ
            childTarget env label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.xoffer_branch elseType branchType
            residual' branches action index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
          elseType branches action branchType index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_branch _ targetBranchType _ _ targetAction _ _
            hTargetEntry hChildTarget =>
            have hEntryEquality : (action, branchType) =
                (targetAction, targetBranchType) :=
              Option.some.inj (hEntry.symm.trans hTargetEntry)
            cases hEntryEquality
            exact (hStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Exclusive offers preserve scoped pending-fragment step correspondence. -/
theorem compilationScopedFragmentStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationScopedFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationScopedFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationScopedFragmentStepCorrect signature (.xoffer elseType branches) := by
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
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | xoffer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | xoffer_branch _ _ _ action _ hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled, hResolved⟩
            rcases TypeOffers.xoffer_branch_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient residual' fuel := by
              exact le_trans
                (typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, residual') hBranchMember)
                (by simp [fuel])
            let branchFragment := compileTypeFuel signature fuel residual'
            have hInitial : TypeCompilationRelation residual'
                branchFragment.initial residual' :=
              compileTypeFuel_initial_relation signature fuel residual'
                hBranchFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches)
                (childState (index + 1) branchFragment.initial) residual' :=
              TypeCompilationRelation.xoffer_branch elseType residual'
                residual' branches action index branchFragment.initial
                hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            have hAutomatonEntry : branchAutomata[index]? =
                some (action, branchFragment) := by
              simp [branchAutomata, branchFragment, hEntry]
            rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
              ⟨hBound, hValue⟩
            have hZipBound : index < branchAutomata.zipIdx.length := by
              simpa using hBound
            have hZipEntry : ((action, branchFragment), index) ∈
                branchAutomata.zipIdx := by
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := branchAutomata)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            refine ⟨childState (index + 1) branchFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              (TypeLabel.message action.1 action.2) ⟨current, future⟩
              (childState (index + 1) branchFragment.initial)).mpr
            left
            exact ⟨((action, branchFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hImmediate, hResolved⟩
            rcases TypeOffers.xoffer_else_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.xoffer elseType branches) (childState 0 elseFragment.initial)
                elseType :=
              TypeCompilationRelation.xoffer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hImmediate, hResolved, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | xoffer_wait _ _ _ hConditions =>
            rcases hConditions with ⟨_, hUnresolved, hClock⟩
            rcases TypeOffers.xoffer_wait_fields hOffers with
              ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.xoffer elseType branches) .root
                (.xoffer elseType branches) :=
              TypeCompilationRelation.xoffer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment branchAutomata env
              TypeLabel.silent ⟨current, future⟩
              .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, by
                simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent,
              hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildExclusiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment branchAutomata env label
          ⟨current, future⟩
          target).mp hEdge with hBranch | hWait | hElse
        · rcases hBranch with ⟨indexed, hIndexed, _, hEnabled, hResolved,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
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
          rw [hIndexedValue] at hEnabled hLabel hCurrent hEdgeFuture hTargetState
          subst target
          have hBranchMember : branch ∈ branches :=
            List.getElem_mem hBranchBound
          have hBranchFuel : TypeCompilationFuelSufficient branch.2 fuel := by
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                branch hBranchMember)
              (by simp [fuel])
          have hInitial : TypeCompilationRelation branch.2
              (compileTypeFuel signature fuel branch.2).initial branch.2 :=
            compileTypeFuel_initial_relation signature fuel branch.2
              hBranchFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel branch.2).initial)
              branch.2 :=
            TypeCompilationRelation.xoffer_branch elseType branch.2 branch.2
              branches branch.1 indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers branch.2 := hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
          · exact
              (TypeOffers.xoffer_branch env elseType branches branch.1
                branch.2 ⟨TypeAlphabet.localEnvironment_wellFormed
                  hLocalEnvironment, hBranchMember, hEnabled, hResolved⟩)
        · rcases hWait with ⟨_, hClock, hFutureBranches, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.xoffer elseType branches) .root
              (.xoffer elseType branches) :=
            TypeCompilationRelation.xoffer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
          · exact
              (TypeOffers.xoffer_wait env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  by simpa [TypeResolved] using hFutureBranches, hClock⟩)
        · rcases hElse with ⟨_, hImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.xoffer elseType branches) (childState 0 elseFragment.initial)
              elseType :=
            TypeCompilationRelation.xoffer_else elseType elseType branches
              elseFragment.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers elseType :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact
              (TypeTransition.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
          · exact
              (TypeOffers.xoffer_else env elseType branches
                ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                  hImmediate, hResolved⟩)
  | xoffer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hStep
        rcases (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr
            hChildEdge
        · exact TypeCompilationRelation.xoffer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | xoffer_branch _ branchType _ _ action index childQ hEntry
      hChildRelated =>
      have hStep : CompilationScopedFragmentStepCorrect signature branchType :=
        hBranchStep action branchType index hEntry
      have hMember : (action, branchType) ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
        have hAt := List.getElem_mem hBound
        simpa [hValue] using hAt
      have hAvoidsBranch : env.AvoidsInterface
          branchType.ParallelInterfaces :=
        hAvoids.mono (by
          intro message hMessage
          simp only [PactType.ParallelInterfaces, Finset.mem_union]
          right
          exact parallelInterfaces_subset_parallelBranchInterfaces_of_mem
            hMember hMessage)
      constructor
      · intro hSemanticStep
        rcases (hStep hChildRelated hLocalEnvironment hAvoidsBranch).mp hSemanticStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_xoffer_branch_child_edge_iff signature
            elseType branches action branchType index hEntry childQ
            childTarget env label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.xoffer_branch elseType branchType
            residual' branches action index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_xoffer_branch_child_edge_cases signature
          elseType branches action branchType index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | xoffer_branch _ targetBranchType _ _ targetAction _ _
            hTargetEntry hChildTarget =>
            have hEntryEquality : (action, branchType) =
                (targetAction, targetBranchType) :=
              Option.some.inj (hEntry.symm.trans hTargetEntry)
            cases hEntryEquality
            exact (hStep hChildRelated hLocalEnvironment hAvoidsBranch).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

/-- Public exclusive-offer correspondence follows by alphabet export. -/
theorem compilationStepCorrect_xoffer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseStep : CompilationFragmentStepCorrect signature elseType)
    (hBranchStep : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat),
      branches[index]? = some (action, branchType) →
        CompilationFragmentStepCorrect signature branchType)
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches)) :
    CompilationStepCorrect signature (.xoffer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  have hSignatureSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLocalEnvironment : env ∈ signature.localEnvironments := by
    have hFields : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [TypeAlphabet.transitionAlphabet] using hSignatureSymbol
    exact signature.environments_subset_localEnvironments hFields.1
  have hRaw := compilationFragmentStepCorrect_xoffer signature elseType
    branches hElseStep hBranchStep hFuture (residual := residual)
    (residual' := residual') (state := state) (env := env) (label := label)
    (offers := offers) hRelated hLocalEnvironment
  constructor
  · intro hStep
    rcases hRaw.mp hStep with ⟨target, hEdge, hTarget⟩
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mpr hEdge, hTarget⟩
  · rintro ⟨target, hEdge, hTarget⟩
    apply hRaw.mpr
    exact ⟨target,
      (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) state target env label offers
        hSignatureSymbol).mp hEdge, hTarget⟩

/-- Whole-fragment future correctness for exclusive offers, composed from the

end

end Pact
