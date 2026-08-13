import Anvilpp.PactTypes.Correspondence.Offers.OfferFutureCorrect

/-!
# compilationScopedFragmentStepCorrect_offer
-/

namespace Pact

noncomputable section

private theorem TypeOffers.offer_some_fields_of_enabled
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hEnabled : ∃ enabled ∈ branches, TypeBranchEnabled env enabled)
    (enabled : BareMessage × PactType)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      (parallelTypeBranchesSelecting enabled branches) current future) :
    current = ∅ ∧
      future = typeFutureOffers
        (parallelTypeBranchesSelecting enabled branches) := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : parallelTypeBranchesSelecting enabled branches =
    actualTarget at hOffers
  cases hOffers with
  | offer_some => exact ⟨rfl, rfl⟩
  | offer_else _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim
  | offer_wait _ _ _ hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp hEnabled
      exact (hNonempty hConditions.2.1).elim

private theorem TypeOffers.offer_else_fields_of_resolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hResolved : TypeResolved env branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      elseType current future) :
    current = typeBranchActions branches ∧
      future = typeFutureOffers elseType := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  generalize hTarget : elseType = actualTarget at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else => exact ⟨rfl, rfl⟩

private theorem TypeOffers.offer_wait_fields_of_unresolved
    {env : TypeEnvironment} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {target : PactType} {current future : Finset BareMessage}
    (hNoImmediate : TypeNoImmediateBranch env branches)
    (hUnresolved : ¬ TypeResolved env branches)
    (hTarget : target = .offer elseType branches)
    (hOffers : TypeOffers env (.offer elseType branches) TypeLabel.silent
      target current future) :
    current = typeWaitingOffers env branches ∧
      future = typeFutureOffers (.offer elseType branches) \
        typeWaitingOffers env branches := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers with
  | offer_some _ _ _ enabled hConditions =>
      have hNonempty := (typeBranchEnabled_exists_iff env branches).mp
        ⟨enabled, hConditions.2.1, hConditions.2.2⟩
      exact (hNonempty hNoImmediate).elim
  | offer_else _ _ _ hConditions =>
      exact (hUnresolved hConditions.2.2).elim
  | offer_wait => exact ⟨rfl, rfl⟩

/- The former unrestricted `compilationFragmentStepCorrect_offer` theorem was
removed here.  It described the obsolete all-else conjunction child and had no
callers.  The compiler and semantics now agree through the proved scoped
theorem below, indexed by `parallelTypeBranchesSelecting selected branches`. -/
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
  intro residual residual' state env label offers hRelated hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness hOffers with ⟨hCurrent, hOfferFuture⟩
            have hConjunctionFuel :
                TypeCompilationFuelSufficient conjunctionType fuel := by
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranches]
              simp [fuel]
            have hInitial : TypeCompilationRelation conjunctionType
                conjunction.initial conjunctionType :=
              compileTypeFuel_initial_relation signature fuel conjunctionType
                hConjunctionFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 conjunction.initial) conjunctionType :=
              TypeCompilationRelation.offer_branches elseType conjunctionType
                branches conjunction.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 conjunction.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 conjunction.initial)).mpr
            left
            exact ⟨hLocalEnvironment,
              (typeBranchEnabled_exists_iff env branches).mp
                hEnabledWitness,
              rfl, hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 1 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 1 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 1 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment conjunction env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨_, hImmediate, hLabel, hCurrent,
            hEdgeFuture, hTargetState⟩
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
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 conjunction.initial) conjunctionType :=
            TypeCompilationRelation.offer_branches elseType conjunctionType
              branches conjunction.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers conjunctionType :=
            hEdgeFuture.symm.trans hComputed
          rcases (typeBranchEnabled_exists_iff env branches).mpr hImmediate
            with ⟨enabled, hBranchMember, hBranchEnabled⟩
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 1 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
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
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep hChildRelated hLocalEnvironment).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ _ hChildTarget =>
            exact (hConjunctionStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
-/

theorem compilationScopedFragmentStepCorrect_offer
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hConjunctionStep : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationScopedFragmentStepCorrect signature
          (parallelTypeBranchesSelecting selected branches))
    (hElseStep : CompilationScopedFragmentStepCorrect signature elseType)
    (hFuture : CompilationFutureCorrect signature
      (.offer elseType branches)) :
    CompilationScopedFragmentStepCorrect signature
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
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness enabled hOffers with ⟨hCurrent, hOfferFuture⟩
            rcases List.exists_getElem?_eq_some_of_mem hBranchMember with
              ⟨index, hEntry⟩
            have hBranchFuel : TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting enabled branches) fuel := by
              simp only [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
              exact le_max_right _ _
            let selectedFragment := compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting enabled branches)
            have hInitial : TypeCompilationRelation
                (parallelTypeBranchesSelecting enabled branches)
                selectedFragment.initial
                (parallelTypeBranchesSelecting enabled branches) :=
              compileTypeFuel_initial_relation signature fuel
                (parallelTypeBranchesSelecting enabled branches) hBranchFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState (index + 1) selectedFragment.initial)
                (parallelTypeBranchesSelecting enabled branches) :=
              TypeCompilationRelation.offer_branches elseType
                (parallelTypeBranchesSelecting enabled branches) branches
                enabled index selectedFragment.initial hEntry hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState (index + 1) selectedFragment.initial, ?_,
              hTarget⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩
              (childState (index + 1) selectedFragment.initial)).mpr
            left
            have hAutomatonEntry : selectedConjunctions[index]? =
                some (enabled.1, selectedFragment) := by
              simp [selectedConjunctions, selectedFragment, hEntry]
            have hZipEntry : ((enabled.1, selectedFragment), index) ∈
                selectedConjunctions.zipIdx := by
              rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
                ⟨hBound, hValue⟩
              have hZipBound : index < selectedConjunctions.zipIdx.length := by
                simpa using hBound
              have hMember := List.getElem_mem hZipBound
              have hAt := List.getElem_zipIdx (l := selectedConjunctions)
                (i := index) (j := 0) hZipBound
              simp only [zero_add] at hAt
              rw [hAt, hValue] at hMember
              exact hMember
            exact ⟨((enabled.1, selectedFragment), index), hZipEntry,
              hLocalEnvironment, hEnabled, rfl, hCurrent,
              hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment selectedConjunctions env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildSelectedConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment selectedConjunctions env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨indexed, hIndexed, hLocal, hImmediate,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
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
          have hBranchMember : branch ∈ branches := List.getElem_mem hBranchBound
          have hBranchEnabled : TypeBranchEnabled env branch := by
            have hNeed : typeNeed branch.1 ∈ env.immediate := by
              rw [← congrArg Prod.fst hIndexedValue]
              exact hImmediate
            exact hNeed
          rw [hIndexedValue] at hTargetState hEdgeFuture
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
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState (indexed.2 + 1)
                (compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting branch branches)).initial)
              (parallelTypeBranchesSelecting branch branches) :=
            TypeCompilationRelation.offer_branches elseType
              (parallelTypeBranchesSelecting branch branches) branches branch
              indexed.2 _ hEntry hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future =
              typeFutureOffers (parallelTypeBranchesSelecting branch branches) :=
            hEdgeFuture.symm.trans hComputed
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches branch
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches branch
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
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
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ selected index childQ hEntry
      hChildRelated =>
      have hAvoidsSelected : env.AvoidsInterface
          (parallelTypeBranchesSelecting selected branches).ParallelInterfaces :=
        hAvoids.mono (by
          intro message hMessage
          simp only [PactType.ParallelInterfaces, Finset.mem_union]
          right
          exact parallelTypeBranchesSelecting_parallelInterfaces_subset
            selected branches hMessage)
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep selected index hEntry hChildRelated
          hLocalEnvironment hAvoidsSelected).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState (index + 1) childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches selected index hEntry childQ childTarget env
            label ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches selected index childTarget hEntry hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches selected index hEntry hEdge with
          ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ selected' _ _ hEntry' hChildTarget =>
            have hSelectedEq : selected = selected' := by
              rw [hEntry] at hEntry'
              exact Option.some.inj hEntry'
            exact (hConjunctionStep selected index hEntry hChildRelated
              hLocalEnvironment hAvoidsSelected).mpr
              ⟨childTarget, hChildEdge, hSelectedEq ▸ hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
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
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsElse : env.AvoidsInterface elseType.ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp [PactType.ParallelInterfaces, hMessage])
  have hAvoidsConjunction : env.AvoidsInterface
      (parallelTypeBranches branches).ParallelInterfaces :=
    hAvoids.mono (by
      intro message hMessage
      simp only [PactType.ParallelInterfaces, Finset.mem_union]
      right
      exact parallelTypeBranches_parallelInterfaces_subset branches hMessage)
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | offer_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | offer_some _ _ _ enabled hConditions =>
            rcases hConditions with
              ⟨_, hBranchMember, hEnabled⟩
            have hEnabledWitness :
                ∃ branch ∈ branches, TypeBranchEnabled env branch :=
              ⟨enabled, hBranchMember, hEnabled⟩
            rcases TypeOffers.offer_some_fields_of_enabled
              hEnabledWitness hOffers with ⟨hCurrent, hOfferFuture⟩
            have hConjunctionFuel :
                TypeCompilationFuelSufficient conjunctionType fuel := by
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranches]
              simp [fuel]
            have hInitial : TypeCompilationRelation conjunctionType
                conjunction.initial conjunctionType :=
              compileTypeFuel_initial_relation signature fuel conjunctionType
                hConjunctionFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 0 conjunction.initial) conjunctionType :=
              TypeCompilationRelation.offer_branches elseType conjunctionType
                branches conjunction.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 0 conjunction.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 0 conjunction.initial)).mpr
            left
            exact ⟨hLocalEnvironment,
              (typeBranchEnabled_exists_iff env branches).mp
                hEnabledWitness,
              rfl, hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_else _ _ _ hConditions =>
            rcases hConditions with ⟨_, hNoImmediate, hResolved⟩
            rcases TypeOffers.offer_else_fields_of_resolved hNoImmediate
              hResolved hOffers with ⟨hCurrent, hOfferFuture⟩
            have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
              simp [TypeCompilationFuelSufficient, fuel]
            have hInitial : TypeCompilationRelation elseType
                elseFragment.initial elseType :=
              compileTypeFuel_initial_relation signature fuel elseType
                hElseFuel
            have hTarget : TypeCompilationRelation
                (.offer elseType branches)
                (childState 1 elseFragment.initial) elseType :=
              TypeCompilationRelation.offer_else elseType elseType branches
                elseFragment.initial hInitial
            have hComputed := hFuture _ _ hTarget
            rw [hFragment] at hComputed
            refine ⟨childState 1 elseFragment.initial, ?_, hTarget⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩
              (childState 1 elseFragment.initial)).mpr
            right
            right
            exact ⟨hLocalEnvironment, hNoImmediate, hResolved, rfl,
              hCurrent, hComputed.trans hOfferFuture.symm, rfl⟩
        | offer_wait _ _ _ hConditions =>
            rcases hConditions with
              ⟨_, hNoImmediate, hUnresolved, hClock⟩
            rcases TypeOffers.offer_wait_fields_of_unresolved hNoImmediate
              hUnresolved rfl hOffers with ⟨hCurrent, hOfferFuture⟩
            have hSourceRelation : TypeCompilationRelation
                (.offer elseType branches) .root
                (.offer elseType branches) :=
              TypeCompilationRelation.offer_source elseType branches
            have hComputed := hFuture _ _ hSourceRelation
            rw [hFragment] at hComputed
            have hRemoved := congrArg
              (fun available => available \ typeWaitingOffers env branches)
              hComputed
            refine ⟨.root, ?_, hSourceRelation⟩
            rw [hFragment]
            apply (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
              signature branches elseFragment conjunction env
              TypeLabel.silent ⟨current, future⟩ .root).mpr
            right
            left
            exact ⟨hLocalEnvironment, hClock, hNoImmediate,
              by simpa [TypeResolved] using hUnresolved,
              rfl, hCurrent, hRemoved.trans hOfferFuture.symm, rfl⟩
      · rintro ⟨target, hEdge, hTarget⟩
        rw [hFragment] at hEdge
        rcases (buildConjunctiveOfferAutomaton_root_hasResolvedEdge_iff
          signature branches elseFragment conjunction env label
          ⟨current, future⟩ target).mp hEdge with
          hEnabled | hWait | hElse
        · rcases hEnabled with ⟨_, hImmediate, hLabel, hCurrent,
            hEdgeFuture, hTargetState⟩
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
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 0 conjunction.initial) conjunctionType :=
            TypeCompilationRelation.offer_branches elseType conjunctionType
              branches conjunction.initial hInitial
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hExpectedTarget
          subst residual'
          have hComputed := hFuture _ _ hExpectedTarget
          rw [hFragment] at hComputed
          have hOfferFuture : future = typeFutureOffers conjunctionType :=
            hEdgeFuture.symm.trans hComputed
          rcases (typeBranchEnabled_exists_iff env branches).mpr hImmediate
            with ⟨enabled, hBranchMember, hBranchEnabled⟩
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
          · exact TypeOffers.offer_some env elseType branches enabled
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hBranchMember, hBranchEnabled⟩
        · rcases hWait with ⟨_, hClock, hNoImmediate, hFutureBranches,
            hLabel, hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hSourceRelation : TypeCompilationRelation
              (.offer elseType branches) .root
              (.offer elseType branches) :=
            TypeCompilationRelation.offer_source elseType branches
          have hResidual := TypeCompilationRelation.residual_unique hTarget
            hSourceRelation
          subst residual'
          have hComputed := hFuture _ _ hSourceRelation
          rw [hFragment] at hComputed
          have hRemoved := congrArg
            (fun available => available \ typeWaitingOffers env branches)
            hComputed
          have hOfferFuture : future =
              typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches :=
            hEdgeFuture.symm.trans hRemoved
          cases hLabel
          cases hCurrent
          cases hOfferFuture
          constructor
          · exact TypeTransition.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
          · exact TypeOffers.offer_wait env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate,
                by simpa [TypeResolved] using hFutureBranches, hClock⟩
        · rcases hElse with ⟨_, hNoImmediate, hResolved, hLabel,
            hCurrent, hEdgeFuture, hTargetState⟩
          subst target
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, fuel]
          have hInitial : TypeCompilationRelation elseType
              elseFragment.initial elseType :=
            compileTypeFuel_initial_relation signature fuel elseType hElseFuel
          have hExpectedTarget : TypeCompilationRelation
              (.offer elseType branches)
              (childState 1 elseFragment.initial) elseType :=
            TypeCompilationRelation.offer_else elseType elseType branches
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
          · exact TypeTransition.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
          · exact TypeOffers.offer_else env elseType branches
              ⟨TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment,
                hNoImmediate, hResolved⟩
  | offer_branches _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hConjunctionStep hChildRelated hLocalEnvironment hAvoidsConjunction).mp
          hSemanticStep with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 0 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_conjunction_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_branches elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_conjunction_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_branches _ _ _ _ hChildTarget =>
            exact (hConjunctionStep hChildRelated hLocalEnvironment hAvoidsConjunction).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | offer_else _ childResidual _ childQ hChildRelated =>
      constructor
      · intro hSemanticStep
        rcases (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mp hSemanticStep
          with ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨childState 1 childTarget, ?_, ?_⟩
        · exact (compileTypeFuel_offer_else_child_edge_iff signature
            elseType branches childQ childTarget env label
            ⟨current, future⟩).mpr hChildEdge
        · exact TypeCompilationRelation.offer_else elseType residual'
            branches childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        rcases compileTypeFuel_offer_else_child_edge_cases signature
          elseType branches hEdge with ⟨childTarget, rfl, hChildEdge⟩
        cases hTarget with
        | offer_else _ _ _ _ hChildTarget =>
            exact (hElseStep hChildRelated hLocalEnvironment hAvoidsElse).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
-/

end

end Pact
