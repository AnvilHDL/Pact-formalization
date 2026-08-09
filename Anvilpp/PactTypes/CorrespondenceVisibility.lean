import Anvilpp.PactTypes.CorrespondenceCore

/-!
# Compiler-label visibility

Closed syntax cannot leave a temporary recursion-variable marker on a semantic
compiler edge.  Parallel `.future` observations remain construction-only and
are deliberately allowed.
-/

namespace Pact

noncomputable section

private theorem allVariablesBound_branch_of_mem_visibility
    (bound : List String) : ∀ branches entry,
    PactType.AllBranchVariablesBound bound branches → entry ∈ branches →
      PactType.AllVariablesBound bound entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.AllBranchVariablesBound] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

private theorem allVariablesBound_parallelTypeBranches_visibility
    (bound : List String) (branches : List (BareMessage × PactType))
    (hBound : PactType.AllBranchVariablesBound bound branches) :
    PactType.AllVariablesBound bound (parallelTypeBranches branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.AllVariablesBound, PactType.AllBranchVariablesBound]
            using hBound.1
      | cons next tail =>
          simp only [parallelTypeBranches, PactType.AllVariablesBound]
          constructor
          · simpa [singletonTypeXOffer, PactType.AllVariablesBound,
              PactType.AllBranchVariablesBound] using hBound.1
          · exact ih hBound.2

private theorem allVariablesBound_parallelTypeBranchesSelecting_visibility
    (bound : List String) (selected : BareMessage × PactType) :
    ∀ branches,
      PactType.AllBranchVariablesBound bound branches →
      PactType.AllVariablesBound bound
        (parallelTypeBranchesSelecting selected branches) := by
  intro branches hBound
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hEq, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1,
              allVariablesBound_parallelTypeBranches_visibility bound
                (next :: tail) hBound.2]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1, ih hBound.2]

/-- Any temporary variable label in a fuel-bounded compiler fragment names a
variable permitted by the surrounding syntactic binder context. -/
theorem compileTypeFuel_variable_label_mem_bound
    (signature : TypeAlphabet) : ∀ fuel processType bound,
    PactType.AllVariablesBound bound processType →
    ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
      ∀ name, edge.label = .variable name → name ∈ bound := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType bound hBound edge hEdge name hLabel
      simp [compileTypeFuel] at hEdge
  | succ fuel ih =>
      intro processType bound hBound edge hEdge name hLabel
      cases processType with
      | message msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment] at hEdge
          rcases hEdge with hFire | hWait | hFinal
          all_goals
            rcases ‹∃ _, _› with ⟨_, _, hEq⟩
            have hContr := congrArg PendingAutomatonEdge.label hEq
            rw [hLabel] at hContr
            cases hContr
      | progress pid =>
          simp [compileTypeFuel, finishAutomatonFragment] at hEdge
          rcases hEdge with hAction | hFinal
          all_goals
            rcases ‹∃ _, _› with ⟨_, _, hEq⟩
            have hContr := congrArg PendingAutomatonEdge.label hEq
            rw [hLabel] at hContr
            cases hContr
      | tock =>
          simp [compileTypeFuel, finishAutomatonFragment] at hEdge
          rcases hEdge with hAction | hFinal
          · rcases hAction with ⟨environment, _, hEq⟩
            have hContr := congrArg PendingAutomatonEdge.label hEq
            rw [hLabel] at hContr
            split at hContr <;> cases hContr
          · rcases hFinal with ⟨_, _, hEq⟩
            have hContr := congrArg PendingAutomatonEdge.label hEq
            rw [hLabel] at hContr
            cases hContr
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment] at hEdge
          rcases hEdge with ⟨_, _, hEq⟩
          have hContr := congrArg PendingAutomatonEdge.label hEq
          rw [hLabel] at hContr
          cases hContr
      | var variableName =>
          simp only [PactType.AllVariablesBound] at hBound
          simp [compileTypeFuel, finishAutomatonFragment] at hEdge
          rcases hEdge with ⟨_, _, hEq⟩
          rw [← hEq] at hLabel
          injection hLabel with hName
          subst name
          exact hBound
      | choice left right =>
          simp only [PactType.AllVariablesBound] at hBound
          simp only [compileTypeFuel] at hEdge
          simp only [buildChoiceAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · simp only [childPendingEdges, Finset.mem_image] at hLeft
            rcases hLeft with ⟨child, hChild, hEq⟩
            exact ih left bound hBound.1 child hChild name (by
              rw [← hEq] at hLabel
              simpa [childPendingEdge] using hLabel)
          · simp only [childPendingEdges, Finset.mem_image] at hRight
            rcases hRight with ⟨child, hChild, hEq⟩
            exact ih right bound hBound.2 child hChild name (by
              rw [← hEq] at hLabel
              simpa [childPendingEdge] using hLabel)
          · simp only [Finset.mem_biUnion, Finset.mem_insert,
              Finset.mem_singleton] at hSelection
            rcases hSelection with ⟨_, _, hEq | hEq⟩
            all_goals rw [hEq] at hLabel; cases hLabel
      | fairChoice bid left right =>
          simp only [PactType.AllVariablesBound] at hBound
          simp only [compileTypeFuel] at hEdge
          simp only [buildChoiceAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hEdge
          rcases hEdge with (hLeft | hRight) | hSelection
          · simp only [childPendingEdges, Finset.mem_image] at hLeft
            rcases hLeft with ⟨child, hChild, hEq⟩
            exact ih left bound hBound.1 child hChild name (by
              rw [← hEq] at hLabel
              simpa [childPendingEdge] using hLabel)
          · simp only [childPendingEdges, Finset.mem_image] at hRight
            rcases hRight with ⟨child, hChild, hEq⟩
            exact ih right bound hBound.2 child hChild name (by
              rw [← hEq] at hLabel
              simpa [childPendingEdge] using hLabel)
          · simp only [Finset.mem_biUnion, Finset.mem_insert,
              Finset.mem_singleton] at hSelection
            rcases hSelection with ⟨_, _, hEq | hEq⟩
            all_goals rw [hEq] at hLabel; cases hLabel
      | recur binder body =>
          simp only [PactType.AllVariablesBound] at hBound
          simp only [compileTypeFuel] at hEdge
          simp only [buildRecursionAutomaton, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hEdge
          rcases hEdge with hHeader | hBody
          · rcases hHeader with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
          · rcases hBody with ⟨child, hChild, hEq⟩
            rw [← hEq] at hLabel
            by_cases hVariable : child.label = .variable binder
            · simp only [hVariable, if_true] at hLabel
              cases hLabel
            · simp only [hVariable, if_false] at hLabel
              have hBodyName := ih body (binder :: bound) hBound child hChild
                name (by simpa using hLabel)
              simp only [List.mem_cons] at hBodyName
              rcases hBodyName with hSame | hBoundName
              · rw [hSame] at hLabel
                exact (hVariable hLabel).elim
              · exact hBoundName
      | seq left right =>
          simp only [PactType.AllVariablesBound] at hBound
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
          · simp only [Finset.mem_image] at hLeft
            rcases hLeft with ⟨child, hChild, hEq⟩
            exact ih left bound hBound.1 child hChild name (by
              rw [← hEq] at hLabel
              simpa using hLabel)
          · simp only [childPendingEdges, Finset.mem_image] at hRight
            rcases hRight with ⟨child, hChild, hEq⟩
            exact ih right bound hBound.2 child hChild name (by
              rw [← hEq] at hLabel
              simpa [childPendingEdge] using hLabel)
          · simp only [Finset.mem_biUnion, Finset.mem_image] at hBridge
            rcases hBridge with ⟨_, _, _, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
          · simp only [Finset.mem_image] at hFutureBridge
            rcases hFutureBridge with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
      | par left right interface =>
          simp only [PactType.AllVariablesBound] at hBound
          have hLeftVariable : ∀ resolved ∈ resolvedAutomatonEdges
              (compileTypeFuel signature fuel left), ∀ selected,
              resolved.label = .variable selected → selected ∈ bound := by
            intro resolved hResolved selected hSelected
            simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolved
            rcases hResolved with ⟨pending, hPending, hEq⟩
            apply ih left bound hBound.1 pending hPending selected
            have hEqLabel := congrArg AutomatonFragmentEdge.label hEq
            exact hEqLabel.trans hSelected
          have hRightVariable : ∀ resolved ∈ resolvedAutomatonEdges
              (compileTypeFuel signature fuel right), ∀ selected,
              resolved.label = .variable selected → selected ∈ bound := by
            intro resolved hResolved selected hSelected
            simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolved
            rcases hResolved with ⟨pending, hPending, hEq⟩
            apply ih right bound hBound.2 pending hPending selected
            have hEqLabel := congrArg AutomatonFragmentEdge.label hEq
            exact hEqLabel.trans hSelected
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with hTransition | hObservation
          · simp only [Finset.mem_biUnion, Finset.mem_image,
              Finset.mem_filter] at hTransition
            rcases hTransition with
              ⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _⟩, hEq⟩
            rw [← hEq] at hLabel
            rcases hLeftEdge with ⟨hLeftMember, hLeftSemantic⟩
            rcases hRightEdge with ⟨hRightMember, hRightSemantic⟩
            cases hLeftLabel : leftEdge.label with
            | visible leftLabel =>
                cases hRightLabel : rightEdge.label with
                | visible rightLabel =>
                    simp [AutomatonConstructionLabel.combine, hLeftLabel,
                      hRightLabel] at hLabel
                | «variable» rightName =>
                    simp only [AutomatonConstructionLabel.combine, hLeftLabel,
                      hRightLabel] at hLabel
                    injection hLabel with hName
                    subst name
                    exact hRightVariable rightEdge hRightMember rightName
                      hRightLabel
                | future => exact (hRightSemantic hRightLabel).elim
            | «variable» leftName =>
                simp only [AutomatonConstructionLabel.combine, hLeftLabel]
                  at hLabel
                injection hLabel with hName
                subst name
                exact hLeftVariable leftEdge hLeftMember leftName hLeftLabel
            | future => exact (hLeftSemantic hLeftLabel).elim
          · rcases hObservation with hLeftObservation | hRightObservation
            · simp only [Finset.mem_biUnion, Finset.mem_image]
                at hLeftObservation
              rcases hLeftObservation with ⟨_, _, _, _, hEq⟩
              rw [← hEq] at hLabel
              cases hLabel
            · simp only [Finset.mem_biUnion, Finset.mem_image]
                at hRightObservation
              rcases hRightObservation with ⟨_, _, _, _, hEq⟩
              rw [← hEq] at hLabel
              cases hLabel
      | xoffer elseType branches =>
          simp only [PactType.AllVariablesBound] at hBound
          let elseFragment := compileTypeFuel signature fuel elseType
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          simp only [compileTypeFuel] at hEdge
          change edge ∈ (buildExclusiveOfferAutomaton signature branches
            elseFragment branchAutomata).edges at hEdge
          simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) |
            hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElse
            rcases hElse with ⟨child, hChild, hEq⟩
            exact ih elseType bound hBound.1 child (by
              simpa [elseFragment] using hChild) name (by
                rw [← hEq] at hLabel
                simpa [childPendingEdge] using hLabel)
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChild, hEq⟩
              have hAutomatonEntry : indexed.1 ∈ branchAutomata := by
                have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
                  List.mem_map_of_mem (f := Prod.fst) hIndexed
                simpa using hMapped
              rcases List.mem_map.mp hAutomatonEntry with
                ⟨branch, hBranchMember, hAutomatonEq⟩
              rcases branch with ⟨action, branchType⟩
              have hBranchBound : PactType.AllVariablesBound bound branchType :=
                allVariablesBound_branch_of_mem_visibility bound branches
                  (action, branchType) hBound.2 hBranchMember
              have hFragmentEq : indexed.1.2 =
                  compileTypeFuel signature fuel branchType := by
                simpa [branchAutomata] using
                  congrArg Prod.snd hAutomatonEq.symm
              exact ih branchType bound hBranchBound child (by
                  simpa [hFragmentEq] using hChild) name (by
                    rw [← hEq] at hLabel
                    simpa [childPendingEdge] using hLabel)
          · rw [mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, hIndexed, hGenerated⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hGenerated
              rcases hGenerated with ⟨_, _, hEq⟩
              rw [← hEq] at hLabel
              cases hLabel
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
      | offer elseType branches =>
          simp only [PactType.AllVariablesBound] at hBound
          let elseFragment := compileTypeFuel signature fuel elseType
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          simp only [compileTypeFuel] at hEdge
          change edge ∈ (buildSelectedConjunctiveOfferAutomaton signature
            branches elseFragment selectedConjunctions).edges at hEdge
          simp only [buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hEdge
          rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) |
            hResolved)
          · simp only [childPendingEdges, Finset.mem_image] at hElse
            rcases hElse with ⟨child, hChild, hEq⟩
            exact ih elseType bound hBound.1 child (by
                simpa [elseFragment] using hChild) name (by
                  rw [← hEq] at hLabel
                  simpa [childPendingEdge] using hLabel)
          · rw [indexedFragmentEdges, mem_foldl_union_iff] at hConjunction
            rcases hConjunction with hEmpty |
              ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · simp only [childPendingEdges, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChild, hEq⟩
              have hFields := List.mem_zipIdx hIndexed
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
              rcases hFields with ⟨hIndexBound, hIndexedEq⟩
              have hEntryMember : indexed.1 ∈ selectedConjunctions := by
                have hMember := List.getElem_mem hIndexBound
                simpa [hIndexedEq] using hMember
              rcases List.mem_map.mp hEntryMember with
                ⟨selected, hSelected, hAutomatonEq⟩
              have hSelectedBound : PactType.AllVariablesBound bound
                  (parallelTypeBranchesSelecting selected branches) :=
                allVariablesBound_parallelTypeBranchesSelecting_visibility
                  bound selected branches hBound.2
              have hFragmentEq : indexed.1.2 = compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches) := by
                simpa [selectedConjunctions] using
                  congrArg Prod.snd hAutomatonEq.symm
              exact ih (parallelTypeBranchesSelecting selected branches) bound
                hSelectedBound child (by simpa [hFragmentEq] using hChild) name
                  (by rw [← hEq] at hLabel
                      simpa [childPendingEdge] using hLabel)
          · rw [mem_foldl_union_iff] at hEnabled
            rcases hEnabled with hEmpty | ⟨_, _, hNewEdge⟩
            · simp at hEmpty
            · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
              rcases hNewEdge with ⟨_, _, hEq⟩
              rw [← hEq] at hLabel
              cases hLabel
          · simp only [Finset.mem_image, Finset.mem_filter] at hWait
            rcases hWait with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel
          · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
            rcases hResolved with ⟨_, _, hEq⟩
            rw [← hEq] at hLabel
            cases hLabel

/-- A fully closed compiler fragment has only visible semantic pending edges;
the remaining non-visible edges are the explicit optimistic-future
observations of synchronized products. -/
theorem compilationPendingEdgesVisible_of_allVariablesBound
    (signature : TypeAlphabet) (processType : PactType)
    (hClosed : PactType.AllVariablesBound [] processType) :
    CompilationPendingEdgesVisible signature processType := by
  intro edge hEdge hSemantic
  cases hLabel : edge.label with
  | visible label => exact ⟨label, rfl⟩
  | «variable» name =>
      have hBound := compileTypeFuel_variable_label_mem_bound signature
        (typeCompilationFuel processType) processType [] hClosed edge hEdge
          name hLabel
      simp at hBound
  | future => exact (hSemantic hLabel).elim

end

end Pact
