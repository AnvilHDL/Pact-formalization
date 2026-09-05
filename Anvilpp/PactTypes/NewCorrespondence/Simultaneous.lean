import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Recursion
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Sequence

/-!
Same-cycle completion at the compound fragments, the parallel product menu, and
`correspondence_simultaneous`: the three helpers of Lemma 4.5 proved together by
one induction on `typeCompilationFuel`.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

lemma sameCycleCompletionAgrees_choice
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.choice alphabet left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) =
        buildChoiceAutomaton alphabet leftAuto rightAuto
          TypeLabel.silent TypeLabel.silent := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildChoiceAutomaton alphabet
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent =
      buildChoiceAutomaton alphabet leftAuto rightAuto
        TypeLabel.silent TypeLabel.silent
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  rw [hWhole]
  have hEmptyLocal :
      TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hShape := helper_h12_binaryChoice_shape (.choice alphabet left right) left right
    (by simp only [buildRelationSetCoreFuel]) hFuelEq hRelated
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      TypeLabel.silent TypeLabel.silent)
    leftAuto 0
    (automatonNonClockStep_binaryChoice_child0 alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
    (buildChoiceAutomaton_child0_accepting_iff alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      TypeLabel.silent TypeLabel.silent)
    rightAuto 1
    (automatonNonClockStep_binaryChoice_child1 alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
    (buildChoiceAutomaton_child1_accepting_iff alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
  rcases hShape with ⟨hResidualEq, hStateEq⟩ |
    ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    rw [typeSameCycleCanComplete_choice_iff,
      automatonSameCycleReachesAccepting_root_binaryChoice alphabet
        leftAuto rightAuto _ _
        hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.silent])
        (by simp [TypeLabel.isTock, TypeLabel.silent])]
    have hIHLeft := hLeftComplete
      (buildRelationSet_initial left (compileType left))
    have hIHRight := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHLeft hIHRight
    rw [← hLeftAutoDef] at hIHLeft
    rw [← hRightAutoDef] at hIHRight
    rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
  · subst hStateEq
    exact (hTag0 q).trans (hLeftComplete hLeftRelated)
  · subst hStateEq
    exact (hTag1 q).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_fairChoice
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.fairChoice alphabet bid left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
        buildChoiceAutomaton alphabet leftAuto rightAuto
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildChoiceAutomaton alphabet
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton alphabet leftAuto rightAuto
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  rw [hWhole]
  have hEmptyLocal :
      TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hShape := helper_h12_binaryChoice_shape (.fairChoice alphabet bid left right)
    left right (by simp only [buildRelationSetCoreFuel]) hFuelEq hRelated
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    leftAuto 0
    (automatonNonClockStep_binaryChoice_child0 alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    (buildChoiceAutomaton_child0_accepting_iff alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    rightAuto 1
    (automatonNonClockStep_binaryChoice_child1 alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    (buildChoiceAutomaton_child1_accepting_iff alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
  rcases hShape with ⟨hResidualEq, hStateEq⟩ |
    ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    rw [typeSameCycleCanComplete_fairChoice_iff,
      automatonSameCycleReachesAccepting_root_binaryChoice alphabet
        leftAuto rightAuto _ _
        hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.fair])
        (by simp [TypeLabel.isTock, TypeLabel.fair])]
    have hIHLeft := hLeftComplete
      (buildRelationSet_initial left (compileType left))
    have hIHRight := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHLeft hIHRight
    rw [← hLeftAutoDef] at hIHLeft
    rw [← hRightAutoDef] at hIHRight
    rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
  · subst hStateEq
    exact (hTag0 q).trans (hLeftComplete hLeftRelated)
  · subst hStateEq
    exact (hTag1 q).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_seq
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.seq alphabet left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left
    with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) =
        buildSequenceAutomaton leftAuto rightAuto := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildSequenceAutomaton
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
      buildSequenceAutomaton leftAuto rightAuto
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildSequenceAutomaton leftAuto rightAuto) rightAuto 1
    (automatonNonClockStep_sequence_child1 leftAuto rightAuto)
    (buildSequenceAutomaton_child1_accepting_iff leftAuto rightAuto)
  rw [hWhole]
  rcases helper_h12_seq_shape alphabet left right hRelated with
    ⟨ρ, q1, hResidualEq, hStateEq, hLeftRelated, hSurvives⟩ |
    ⟨q2, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    have hIHLeft := hLeftComplete hLeftRelated
    have hIHRightInit := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHRightInit
    rw [← hRightAutoDef] at hIHRightInit
    rw [typeSameCycleCanComplete_seq_iff]
    constructor
    · rintro ⟨finalState, hReach, hFinal⟩
      rcases automatonSameCycleReaches_sequence_child0_cases
          leftAuto rightAuto q1 finalState hReach with
        ⟨q', hEq, -⟩ | ⟨q', hLeftReach, hAccepting, hRest⟩
      · exfalso
        rw [hEq] at hFinal
        simp [buildSequenceAutomaton, finishAutomatonFragment,
          childAccepting, childState] at hFinal
      · exact ⟨hIHLeft.mp ⟨q', hLeftReach, hAccepting⟩,
          hIHRightInit.mp
            ((hTag1 rightAuto.initial).mp ⟨finalState, hRest, hFinal⟩)⟩
    · rintro ⟨hLeftDone, hRightDone⟩
      obtain ⟨q', hLeftReach, hAccepting⟩ := hIHLeft.mpr hLeftDone
      obtain ⟨q2', hRightReach, hRightFinal⟩ :=
        (hTag1 rightAuto.initial).mpr (hIHRightInit.mpr hRightDone)
      refine ⟨q2', Relation.ReflTransGen.trans ?_ hRightReach, hRightFinal⟩
      have hNotDeleted : q1 ∉ sequenceDeleted leftAuto := by
        simp only [sequenceDeleted, Finset.mem_sdiff, Finset.mem_singleton,
          not_and, not_not]
        intro hAcceptingQ1
        rcases hSurvives with hNot | hInit
        · exact absurd hAcceptingQ1
            (by simpa only [compileType, ← hLeftAutoDef] using hNot)
        · simpa only [compileType, ← hLeftAutoDef] using hInit
      rcases automatonSameCycleReaches_sequence_lift_left_of_not_deleted
          leftAuto rightAuto q1 q' hLeftReach hAccepting hNotDeleted with
        hPath | hEq
      · exact hPath
      · -- `q1` already accepts, so it is `left`'s entry and its own idle
        -- step redirects into the right entry.
        subst hEq
        have hEntry : q1 = leftAuto.initial := by
          rcases hSurvives with hNot | hInit
          · exact absurd hAccepting (by
              simpa only [compileType, ← hLeftAutoDef] using hNot)
          · simpa only [compileType, ← hLeftAutoDef] using hInit
        rw [hEntry] at hAccepting ⊢
        obtain ⟨target, hStep, hTargetAccepting⟩ :=
          compileTypeFuel_nonClockStep_of_initial_accepting
            (typeCompilationFuel left) left hAccepting
        refine Relation.ReflTransGen.single ?_
        refine (automatonNonClockStep_sequence_child0 leftAuto
          rightAuto leftAuto.initial _).mpr ⟨target, hStep, ?_⟩
        rw [sequenceRedirect, if_pos hTargetAccepting]
  · subst hStateEq
    exact (hTag1 q2).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_xoffer
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseComplete : SameCycleCompletionAgrees elseType)
    (hBranchComplete : ∀ entry ∈ branches, SameCycleCompletionAgrees entry.2) :
    SameCycleCompletionAgrees (.xoffer alphabet elseType branches) := by
  intro residual state hRelated
  have hEmptyLocal : TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  set elseAuto := compileTypeFuel (typeCompilationFuel elseType) elseType
    with hElseAutoDef
  set branchAutos := branches.map (fun branch =>
    (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2))
    with hBranchAutosDef
  have hWhole :
      compileTypeFuel
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) =
        buildExclusiveOfferAutomaton alphabet branches elseAuto branchAutos := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches)) elseType)
        (branches.map fun branch => (branch.1, compileTypeFuel (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) branch.2)) = _
    rw [hElseAutoDef, hBranchAutosDef,
      compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl]
    congr 1
    apply List.map_congr_left
    intro branch hBranch
    congr 1
    exact compileTypeFuel_eq_of_sufficient branch.2
      (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
        (le_max_right _ _)) le_rfl
  have hMapGet : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) →
      ∃ branchType, branches[i]? = some (action, branchType) ∧
        automaton = compileTypeFuel (typeCompilationFuel branchType) branchType := by
    intro i action automaton hGet
    rw [hBranchAutosDef, List.getElem?_map] at hGet
    cases hb : branches[i]? with
    | none => rw [hb] at hGet; exact absurd hGet (by simp)
    | some b =>
        rw [hb] at hGet
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hGet
        exact ⟨b.2, by rw [← hGet.1], hGet.2.symm⟩
  have hMapGetRev : ∀ (i : Nat) (branch : BareMessage × PactType),
      branches[i]? = some branch →
      branchAutos[i]? = some (branch.1,
        compileTypeFuel (typeCompilationFuel branch.2) branch.2) := by
    intro i branch hGet
    rw [hBranchAutosDef, List.getElem?_map, hGet]
    rfl
  have hFiringEnv : (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) →
      ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } : TypeEnvironment)
        ∈ alphabet.localEnvironments := by
    intro hBranchActions i action automaton hGet
    obtain ⟨branchType, hBranchGet, -⟩ := hMapGet i action automaton hGet
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
    have hAction : action ∈ alphabet.actions := hBranchActions _ hMem
    simpa [typeNeed] using
      firing_environment_mem_localEnvironmentsFor alphabet action.1 action.2
        (by simpa using hAction)
  rw [hWhole]
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildExclusiveOfferAutomaton alphabet branches elseAuto branchAutos)
    elseAuto 0
    (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ 0
      (exclusiveOffer_outgoing_else alphabet branches elseAuto branchAutos)
      q target)
    (buildExclusiveOfferAutomaton_child0_accepting_iff alphabet branches
      elseAuto branchAutos)
  have hTagBranch : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) → ∀ q,
      (AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton alphabet
        branches elseAuto branchAutos) (childState (i + 1) q) ↔
        AutomatonSameCycleReachesAccepting automaton q) := by
    intro i action automaton hGet
    exact automatonSameCycleReachesAccepting_of_child_tag _ automaton (i + 1)
      (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ (i + 1)
        (exclusiveOffer_outgoing_branch alphabet branches elseAuto branchAutos
          i action automaton hGet) q target)
      (buildExclusiveOfferAutomaton_branch_accepting_iff alphabet branches
        elseAuto branchAutos i action automaton hGet)
  -- Every root edge family the offer builder emits is gated on the
  -- branch heads being declared, so one root step witnesses the gate.
  have hRootStepActions : ∀ {target : TypeAutomatonState},
      AutomatonNonClockStep (buildExclusiveOfferAutomaton alphabet
        branches elseAuto branchAutos) TypeAutomatonState.root target →
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions := by
    intro target hStep
    obtain ⟨edge, hEdge, hSource, -, -⟩ := hStep
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, -, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, ⟨-, -, -, hActions⟩, -⟩
        exact hActions
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, ⟨-, -, -, hActions⟩, -⟩
      exact hActions
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
  rcases helper_h12_xoffer_shape alphabet elseType branches hRelated with
    ⟨hResidualEq, hStateEq⟩ | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, action, branchType, q, hGet, hStateEq, hBranchRelated⟩
  · subst hResidualEq; subst hStateEq
    by_cases hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    · rw [typeSameCycleCanComplete_xoffer_iff alphabet elseType branches hBranchActions,
        automatonSameCycleReachesAccepting_root_exclusiveOffer alphabet branches
          elseAuto branchAutos hEmptyLocal hBranchActions
          (hFiringEnv hBranchActions)]
      have hIHElse := hElseComplete
        (buildRelationSet_initial elseType (compileType elseType))
      simp only [compileType] at hIHElse
      rw [← hElseAutoDef] at hIHElse
      rw [hTag0 elseAuto.initial, hIHElse]
      constructor
      · rintro (hElse | ⟨i, action, automaton, hGet, hReach⟩)
        · exact Or.inl hElse
        · obtain ⟨branchType, hBranchGet, hAutoEq⟩ := hMapGet i action automaton hGet
          have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
          subst hAutoEq
          refine Or.inr ⟨(action, branchType), hMem, ?_⟩
          have hIHBranch := hBranchComplete _ hMem
            (buildRelationSet_initial branchType (compileType branchType))
          simp only [compileType] at hIHBranch
          exact hIHBranch.mp ((hTagBranch i action _ hGet _).mp hReach)
      · rintro (hElse | ⟨entry, hMem, hEntry⟩)
        · exact Or.inl hElse
        · obtain ⟨i, hBranchGet⟩ := List.mem_iff_getElem?.mp hMem
          refine Or.inr ⟨i, entry.1,
            compileTypeFuel (typeCompilationFuel entry.2) entry.2,
            hMapGetRev i entry hBranchGet, ?_⟩
          have hIHBranch := hBranchComplete _ hMem
            (buildRelationSet_initial entry.2 (compileType entry.2))
          simp only [compileType] at hIHBranch
          exact (hTagBranch i entry.1 _ (hMapGetRev i entry hBranchGet) _).mpr
            (hIHBranch.mpr hEntry)
    -- Undeclared branch head: the builders emit no root edge and the
    -- `xoffer_*` rules do not fire, so both sides are unreachable.
    · constructor
      · rintro ⟨finalState, hReach, hFinal⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReach with rfl | ⟨mid, hStep, -⟩
        · exact buildExclusiveOfferAutomaton_root_not_accepting alphabet
            branches elseAuto branchAutos hFinal
        · exact hBranchActions (hRootStepActions hStep)
      · rintro ⟨targetAlphabet, hReaches⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReaches with h |
          ⟨mid, ⟨env, label, hTrans, -⟩, -⟩
        · exact nomatch h
        · refine hBranchActions ?_
          cases hTrans with
          | xoffer_branch _ _ _ _ _ _ _ hActions => exact hActions
          | xoffer_else _ _ _ _ _ hActions => exact hActions
          | xoffer_wait _ _ _ _ _ hActions => exact hActions
  · subst hStateEq
    exact (hTag0 q).trans (hElseComplete hElseRelated)
  · subst hStateEq
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
    exact ((hTagBranch i action _
      (hMapGetRev i (action, branchType) hGet) q).trans
      (hBranchComplete _ hMem hBranchRelated))

lemma sameCycleCompletionAgrees_offer
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseComplete : SameCycleCompletionAgrees elseType)
    (hSelectedComplete : ∀ selected ∈ branches,
      SameCycleCompletionAgrees
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    SameCycleCompletionAgrees (.offer alphabet elseType branches) := by
  intro residual state hRelated
  have hEmptyLocal : TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  set elseAuto := compileTypeFuel (typeCompilationFuel elseType) elseType
    with hElseAutoDef
  set conjAutos := branches.map (fun selected =>
    (selected.1,
      compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)))
    with hConjAutosDef
  have hWhole :
      compileTypeFuel
        (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
        buildSelectedConjunctiveOfferAutomaton alphabet branches elseAuto
          conjAutos := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildSelectedConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches)) elseType)
        (branches.map fun selected => (selected.1,
          compileTypeFuel (max (typeCompilationFuel elseType)
            (conjunctiveCompilationFuel branches))
            (parallelTypeBranchesSelecting alphabet selected branches))) = _
    rw [hElseAutoDef, hConjAutosDef,
      compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl]
    congr 1
    apply List.map_congr_left
    intro selected hSelectedMem
    congr 1
    refine compileTypeFuel_eq_of_sufficient
      (parallelTypeBranchesSelecting alphabet selected branches) ?_ le_rfl
    show typeCompilationFuel
      (parallelTypeBranchesSelecting alphabet selected branches) ≤ _
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact le_max_right _ _
  have hMapGet : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) →
      ∃ selected, branches[i]? = some selected ∧ selected.1 = action ∧
        automaton = compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) := by
    intro i action automaton hGet
    rw [hConjAutosDef, List.getElem?_map] at hGet
    cases hb : branches[i]? with
    | none => rw [hb] at hGet; exact absurd hGet (by simp)
    | some b =>
        rw [hb] at hGet
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hGet
        exact ⟨b, rfl, hGet.1, hGet.2.symm⟩
  have hMapGetRev : ∀ (i : Nat) (selected : BareMessage × PactType),
      branches[i]? = some selected →
      conjAutos[i]? = some (selected.1,
        compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches)) := by
    intro i selected hGet
    rw [hConjAutosDef, List.getElem?_map, hGet]
    rfl
  have hFiringEnv : (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) →
      ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } : TypeEnvironment)
        ∈ alphabet.localEnvironments := by
    intro hBranchActions i action automaton hGet
    obtain ⟨selected, hSelGet, hActionEq, -⟩ := hMapGet i action automaton hGet
    have hMem : selected ∈ branches := List.mem_of_getElem? hSelGet
    have hAction : action ∈ alphabet.actions := hActionEq ▸ hBranchActions _ hMem
    simpa [typeNeed] using
      firing_environment_mem_localEnvironmentsFor alphabet action.1 action.2
        (by simpa using hAction)
  rw [hWhole]
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAuto conjAutos)
    elseAuto 0
    (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ 0
      (conjunctiveOffer_outgoing_else alphabet branches elseAuto conjAutos)
      q target)
    (buildSelectedConjunctiveOfferAutomaton_child0_accepting_iff alphabet branches
      elseAuto conjAutos)
  have hTagBranch : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) → ∀ q,
      (AutomatonSameCycleReachesAccepting (buildSelectedConjunctiveOfferAutomaton
        alphabet branches elseAuto conjAutos) (childState (i + 1) q) ↔
        AutomatonSameCycleReachesAccepting automaton q) := by
    intro i action automaton hGet
    exact automatonSameCycleReachesAccepting_of_child_tag _ automaton (i + 1)
      (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ (i + 1)
        (conjunctiveOffer_outgoing_branch alphabet branches elseAuto conjAutos
          i action automaton hGet) q target)
      (buildSelectedConjunctiveOfferAutomaton_branch_accepting_iff alphabet branches
        elseAuto conjAutos i action automaton hGet)
  -- Every root edge family the conjunctive builder emits is gated on the branch
  -- heads being declared, so one root step witnesses the gate.
  have hRootStepActions : ∀ {target : TypeAutomatonState},
      AutomatonNonClockStep (buildSelectedConjunctiveOfferAutomaton alphabet
        branches elseAuto conjAutos) TypeAutomatonState.root target →
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions := by
    intro target hStep
    obtain ⟨edge, hEdge, hSource, -, -⟩ := hStep
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, -, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, ⟨-, -, hActions⟩, -⟩
        exact hActions
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
  rcases relationMembership_offer_cases alphabet elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, selected, q, hGet, hStateEq, hSelectedRelated⟩
  · injection hRoot with hResidualEq hStateEq
    subst hResidualEq; subst hStateEq
    by_cases hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    · rw [typeSameCycleCanComplete_offer_iff alphabet elseType branches hBranchActions,
        automatonSameCycleReachesAccepting_root_conjunctiveOffer alphabet branches
          elseAuto conjAutos hEmptyLocal hBranchActions
          (hFiringEnv hBranchActions)]
      have hIHElse := hElseComplete
        (buildRelationSet_initial elseType (compileType elseType))
      simp only [compileType] at hIHElse
      rw [← hElseAutoDef] at hIHElse
      rw [hTag0 elseAuto.initial, hIHElse]
      constructor
      · rintro (hElse | ⟨i, action, automaton, hGet, hReach⟩)
        · exact Or.inl hElse
        · obtain ⟨selected, hSelGet, -, hAutoEq⟩ := hMapGet i action automaton hGet
          have hMem : selected ∈ branches := List.mem_of_getElem? hSelGet
          subst hAutoEq
          refine Or.inr ⟨selected, hMem, ?_⟩
          have hIHSel := hSelectedComplete selected hMem
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting alphabet selected branches)
              (compileType
                (parallelTypeBranchesSelecting alphabet selected branches)))
          simp only [compileType] at hIHSel
          exact hIHSel.mp ((hTagBranch i action _ hGet _).mp hReach)
      · rintro (hElse | ⟨selected, hMem, hEntry⟩)
        · exact Or.inl hElse
        · obtain ⟨i, hSelGet⟩ := List.mem_iff_getElem?.mp hMem
          refine Or.inr ⟨i, selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches),
            hMapGetRev i selected hSelGet, ?_⟩
          have hIHSel := hSelectedComplete selected hMem
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting alphabet selected branches)
              (compileType
                (parallelTypeBranchesSelecting alphabet selected branches)))
          simp only [compileType] at hIHSel
          exact (hTagBranch i selected.1 _ (hMapGetRev i selected hSelGet) _).mpr
            (hIHSel.mpr hEntry)
    -- Undeclared branch head: the builders emit no root edge and the `offer_*`
    -- rules do not fire, so both sides are unreachable.
    · constructor
      · rintro ⟨finalState, hReach, hFinal⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReach with rfl | ⟨mid, hStep, -⟩
        · exact buildSelectedConjunctiveOfferAutomaton_root_not_accepting alphabet
            branches elseAuto conjAutos hFinal
        · exact hBranchActions (hRootStepActions hStep)
      · rintro ⟨targetAlphabet, hReaches⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReaches with h |
          ⟨mid, ⟨env, label, hTrans, -⟩, -⟩
        · exact nomatch h
        · refine hBranchActions ?_
          cases hTrans with
          | offer_some _ _ _ _ _ _ hActions => exact hActions
          | offer_else _ _ _ _ _ hActions => exact hActions
          | offer_wait _ _ _ _ _ hActions => exact hActions
  · subst hStateEq
    exact (hTag0 q).trans (hElseComplete hElseRelated)
  · subst hStateEq
    have hMem : selected ∈ branches := List.mem_of_getElem? hGet
    exact ((hTagBranch i selected.1 _ (hMapGetRev i selected hGet) q).trans
      (hSelectedComplete selected hMem hSelectedRelated))


open PendingAutomaton

/-- A product state carries its own product term: the compiler reads the
interface and both component states straight off the state. -/
theorem stateProductInfo_par_pair (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 : TypeAutomatonState) :
    stateProductInfo (.par alphabet left right interface) (.pair q1 q2) =
      some (interface, left, right, q1, q2) := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuel, stateProductInfoFuel]

/-- The done state is not a product state. -/
theorem stateProductInfo_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    stateProductInfo (.par alphabet left right interface) .final = none := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuel, stateProductInfoFuel]

set_option maxHeartbeats 1000000 in
/-- The menu at a product state is the hidden union of the component menus. -/
theorem computeFutureOf_par_pair (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (q1 q2 : TypeAutomatonState)
    (hSurvLeft : ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left)
          left).states,
        (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
        PendingAutomaton).futureReachable q1,
      computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right)
          right).states,
        (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
        PendingAutomaton).futureReachable q2,
      computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hq1 : q1 ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hq2 : q2 ∈ (compileTypeFuel (typeCompilationFuel right) right).states) :
    computeFutureOf (.par alphabet left right interface) (.pair q1 q2) =
      hideTypeOffers interface
        (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
  classical
  set N : Nat := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hN
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      N + 1 := by simp only [hN, typeCompilationFuel]; omega
  have hLeftLe : typeCompilationFuel left ≤ N := le_max_left _ _
  have hRightLe : typeCompilationFuel right ≤ N := le_max_right _ _
  have hParentClosed := compiledMenuGraphFuel_referencesClosed (N + 1)
    (.par alphabet left right interface)
    (by simp only [TypeCompilationFuelSufficient, hFuel]; exact le_rfl)
    (by simp only [PactType.OfferBranchesDisjoint]
        exact ⟨hLeftDisjoint, hRightDisjoint⟩)
  simp only [compiledMenuGraphFuel] at hParentClosed
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set parent : PendingAutomaton :=
    { states := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).edges } with hParent
  set parentMenu : FiniteMenuGraph := parent.withMenuDependencies
    (compileTypeMenuLinksFuel
      (min (N + 1) (typeCompilationFuel (.par alphabet left right interface)))
      (.par alphabet left right interface)) with hParentMenu
  -- the product term of the pair state itself is the whole right-hand side
  have hInfo : stateProductInfo (PactType.par alphabet left right interface)
      (.pair q1 q2) = some (interface, left, right, q1, q2) := by
    simp only [stateProductInfo, hFuel, stateProductInfoFuel]
  have hMenuLeft : computeFutureOfFuel N left q1 = computeFutureOf left q1 :=
    computeFutureOfFuel_eq_of_sufficient left q1 hLeftLe le_rfl
  have hMenuRight : computeFutureOfFuel N right q2 = computeFutureOf right q2 :=
    computeFutureOfFuel_eq_of_sufficient right q2 hRightLe le_rfl
  have hRhsSubset :
      hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) ⊆
        (parentMenu.futureReachable (.pair q1 q2)).biUnion fun visited =>
          parent.offersAt visited ∪
            match stateProductInfo (PactType.par alphabet left right interface)
              visited with
            | some (i, l, r, a, b) =>
                hideTypeOffers i (computeFutureOfFuel N l a ∪
                  computeFutureOfFuel N r b)
            | none => ∅ := by
    intro action hAction
    refine Finset.mem_biUnion.mpr ⟨.pair q1 q2,
      FiniteMenuGraph.mem_futureReachable_self parentMenu _, ?_⟩
    refine Finset.mem_union_right _ ?_
    rw [hInfo]
    simpa [hMenuLeft, hMenuRight] using hAction
  -- the filter by the parent alphabet is exactly the interface hiding
  have hBound : computeFutureOf left q1 ∪ computeFutureOf right q2 ⊆
      left.alphabet.actions ∪ right.alphabet.actions :=
    Finset.union_subset_union (computeFutureOf_subset_alphabet left q1)
      (computeFutureOf_subset_alphabet right q2)
  have hFilterEq :
      (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
          (fun action => action ∈
            (PactType.par alphabet left right interface).alphabet.actions) =
        hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
    have := filter_parent_actions_eq_hide hCompatible
      (computeFutureOf left q1 ∪ computeFutureOf right q2) hBound
    simpa [PactType.alphabet] using this
  apply Finset.Subset.antisymm
  · intro action hAction
    obtain ⟨hRaw, hGate⟩ := Finset.mem_filter.mp hAction
    obtain ⟨visited, hVisited, hContrib⟩ := Finset.mem_biUnion.mp hRaw
    -- every visited state contributes within the two component menus
    have hInMenus : action ∈
        computeFutureOf left q1 ∪ computeFutureOf right q2 := by
      have hParEq : compileTypeFuel (N + 1)
          (PactType.par alphabet left right interface) =
          buildParallelAutomaton alphabet left.alphabet right.alphabet interface
            (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N (left.reannotate alphabet))
            (compileTypeFuel N (right.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel right))
              (right.reannotate alphabet)) := by
        simp only [compileTypeFuel]
      have hLeftFragEq : compileTypeFuel N left =
          compileTypeFuel (typeCompilationFuel left) left :=
        compileTypeFuel_eq_of_sufficient left hLeftLe le_rfl
      have hRightFragEq : compileTypeFuel N right =
          compileTypeFuel (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient right hRightLe le_rfl
      have hReach := buildParallelAutomaton_pair_futureReachable_subset
        alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N (left.reannotate alphabet))
        (compileTypeFuel N (right.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left))
          (left.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel right))
          (right.reannotate alphabet))
        (compileTypeFuel_futureTargetsAreEdgeTargets N left)
        (compileTypeFuel_explicitOnlyAtAccepting N left)
        (compileTypeFuel_futureTargetsAreEdgeTargets N right)
        (compileTypeFuel_explicitOnlyAtAccepting N right)
        (compileTypeFuel_referencesClosed N left hLeftLe hLeftDisjoint)
        (compileTypeFuel_referencesClosed N right hRightLe hRightDisjoint)
        (compileTypeMenuLinksFuel
          (min (N + 1) (typeCompilationFuel (.par alphabet left right interface)))
          (.par alphabet left right interface))
        (compileTypeMenuLinksFuel_pair _ _)
        (compileTypeMenuLinksFuel_final _ _)
        (by rw [← hParEq]; exact hParentClosed)
        q1 q2 (by rw [hLeftFragEq]; exact hq1) (by rw [hRightFragEq]; exact hq2)
      rw [hParentMenu, hParent, hParEq] at hVisited
      have hCases := hReach hVisited
      rcases Finset.mem_insert.mp hCases with rfl | hRest
      · -- the done state offers nothing and carries no product term
        exfalso
        rw [hParent, hParEq] at hContrib
        have hShape := buildParallelAutomaton_final_edge_shape
          alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N (left.reannotate alphabet))
          (compileTypeFuel N (right.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left))
            (left.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel right))
            (right.reannotate alphabet))
        have hInfoFinal : stateProductInfo
            (PactType.par alphabet left right interface)
            TypeAutomatonState.final = none := by
          simp only [stateProductInfo, hFuel, stateProductInfoFuel]
        rw [hInfoFinal, Finset.union_empty] at hContrib
        rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hContrib
        obtain ⟨edge, hEdge, hMem⟩ := hContrib
        obtain ⟨hCurrent, hFuture⟩ := hShape edge
          (Finset.mem_filter.mp hEdge).1 (Finset.mem_filter.mp hEdge).2
        rw [hCurrent, hFuture] at hMem
        simp at hMem
      rcases Finset.mem_union.mp hRest with hPairOrRight | hLeftSurv
      · rcases Finset.mem_union.mp hPairOrRight with hPair | hRightSurv
        · -- a reachable product state: its own product term, bounded by
          -- same-cycle monotonicity in each component
          obtain ⟨pair, hPairMem, rfl⟩ := Finset.mem_image.mp hPair
          obtain ⟨hFst, hSnd⟩ := Finset.mem_product.mp hPairMem
          have hInfoPair : stateProductInfo
              (PactType.par alphabet left right interface)
              (.pair pair.1 pair.2) =
              some (interface, left, right, pair.1, pair.2) := by
            simp only [stateProductInfo, hFuel, stateProductInfoFuel]
          rw [hInfoPair] at hContrib
          rcases Finset.mem_union.mp hContrib with hOffers | hProduct
          · -- a synchronized product edge publishes only component offers
            rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hOffers
            obtain ⟨edge, hEdgeMem, hActionMem⟩ := hOffers
            have hEdge := (Finset.mem_filter.mp hEdgeMem).1
            have hSrc := (Finset.mem_filter.mp hEdgeMem).2
            rw [hParent, hParEq] at hEdge
            have hShapes := buildParallelAutomaton_outgoing_pair
              alphabet left.alphabet right.alphabet interface
              (compileTypeFuel N left) (compileTypeFuel N right)
              (compileTypeFuel N (left.reannotate alphabet))
              (compileTypeFuel N (right.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
              (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
              (computeFutureOfFuel (min N (typeCompilationFuel left))
                (left.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel right))
                (right.reannotate alphabet))
              pair.1 pair.2 edge hEdge hSrc
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            -- the gate transfers to each child by parallel compatibility
            have hGateLeft : action ∈ left.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_left hCompatible
                (by simpa [PactType.alphabet] using hGate)
            have hGateRight : action ∈ right.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_right hCompatible
                (by simpa [PactType.alphabet] using hGate)
            -- a component edge's own current sits in that component's menu
            have hLeftIn : ∀ (le : AutomatonFragmentEdge),
                le ∈ resolveAutomatonEdgesWith (compileTypeFuel N left)
                  (computeFutureOfFuel (min N (typeCompilationFuel left)) left) →
                le.source = pair.1 → le.label.semantic ≠ TypeLabel.tock →
                action ∈ le.current →
                action ∈ computeFutureOf left pair.1 := by
              intro le hle hlSrc hlTock hIn
              refine offersAt_subset_computeFutureOf left pair.1 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateLeft⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hle
              obtain ⟨orig, hOrig, rfl⟩ := hle
              simp only at hlSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hlSrc⟩, ?_⟩
              · rw [← hLeftFragEq]; exact hOrig
              · simp only at hlTock
                rw [if_neg hlTock]
                exact Finset.mem_union_left _ hIn
            have hRightIn : ∀ (re : AutomatonFragmentEdge),
                re ∈ resolveAutomatonEdgesWith (compileTypeFuel N right)
                  (computeFutureOfFuel (min N (typeCompilationFuel right))
                    right) →
                re.source = pair.2 → re.label.semantic ≠ TypeLabel.tock →
                action ∈ re.current →
                action ∈ computeFutureOf right pair.2 := by
              intro re hre hrSrc hrTock hIn
              refine offersAt_subset_computeFutureOf right pair.2 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateRight⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hre
              obtain ⟨orig, hOrig, rfl⟩ := hre
              simp only at hrSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hrSrc⟩, ?_⟩
              · rw [← hRightFragEq]; exact hOrig
              · simp only at hrTock
                rw [if_neg hrTock]
                exact Finset.mem_union_left _ hIn
            -- every product edge resolves its future by pointer, never by an
            -- explicit menu, so `offersAt` reads only its current offers
            have hFutureShape : ∀ e ∈ (compileTypeFuel (N + 1)
                (PactType.par alphabet left right interface)).edges,
                e.source = TypeAutomatonState.pair pair.1 pair.2 →
                e.label.semantic ≠ TypeLabel.tock →
                ∀ offers, e.future ≠ FutureSpec.explicit offers := by
              intro e he heSrc hTock offers hExplicit
              have hAcc := compileTypeFuel_explicitOnlyAtAccepting (N + 1)
                (PactType.par alphabet left right interface) e he hTock offers
                hExplicit
              -- the parallel fragment accepts only at the done state, whose
              -- source cannot be the product state we are visiting
              rw [hParEq] at hAcc he
              simp only [buildParallelAutomaton, finishAutomatonFragment,
                Finset.mem_singleton] at hAcc
              obtain ⟨-, hFuture⟩ := buildParallelAutomaton_final_edge_shape
                alphabet left.alphabet right.alphabet interface
                (compileTypeFuel N left) (compileTypeFuel N right)
                (compileTypeFuel N (left.reannotate alphabet))
                (compileTypeFuel N (right.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
                (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
                (computeFutureOfFuel (min N (typeCompilationFuel left))
                  (left.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel right))
                  (right.reannotate alphabet)) e he hAcc
              rw [hFuture] at hExplicit
              injection hExplicit with hOffers
              rw [heSrc] at hAcc
              simp at hAcc
            -- a contributing edge is never a clock edge
            by_cases hEdgeTock : edge.label.semantic = TypeLabel.tock
            · rw [if_pos hEdgeTock] at hActionMem; simp at hActionMem
            rw [if_neg hEdgeTock] at hActionMem
            rcases hShapes with
              ⟨le, hle, re, hre, hlSrc, hrSrc, hCur, hLbl, hSync, -⟩ |
              ⟨re, hre, hrSrc, hCur, hLbl, -⟩ | ⟨le, hle, hlSrc, hCur, hLbl, -⟩
            · -- a synchronized product edge hides a union of component offers
              obtain ⟨hlTock, hrTock⟩ := sync_components_not_tock
                left.alphabet right.alphabet interface hSync
                (by rw [← hLbl]; exact hEdgeTock)
              have hRaw : action ∈ le.current ∪ re.current := by
                rcases Finset.mem_union.mp hActionMem with hCur' | hFut
                · rw [hCur] at hCur'
                  exact (Finset.mem_filter.mp hCur').1
                · cases hFut' : edge.future with
                  | explicit offers =>
                      exact absurd hFut' (hFutureShape edge (by
                        rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                  | «at» s r => rw [hFut'] at hFut; simp at hFut
              rcases Finset.mem_union.mp hRaw with hL | hR
              · exact Finset.mem_union_left _
                  (hLeftMono (hLeftIn le hle hlSrc hlTock hL))
              · exact Finset.mem_union_right _
                  (hRightMono (hRightIn re hre hrSrc hrTock hR))
            · -- the left component completed: only right offers appear
              refine Finset.mem_union_right _ (hRightMono
                (hRightIn re hre hrSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
            · -- the right component completed: only left offers appear
              refine Finset.mem_union_left _ (hLeftMono
                (hLeftIn le hle hlSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
          · -- the product term at a reachable pair
            simp only at hProduct
            rw [computeFutureOfFuel_eq_of_sufficient left pair.1 hLeftLe le_rfl,
              computeFutureOfFuel_eq_of_sufficient right pair.2 hRightLe
                le_rfl] at hProduct
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            have hHide : hideTypeOffers interface
                (computeFutureOf left pair.1 ∪ computeFutureOf right pair.2) ⊆
                computeFutureOf left pair.1 ∪ computeFutureOf right pair.2 := by
              intro a ha
              exact (Finset.mem_filter.mp ha).1
            exact Finset.union_subset_union hLeftMono hRightMono
              (hHide hProduct)
        · -- a right survivor sub-reach: collapses to the re-signed component's
          -- menu by the survivor transport, then to the component's own
          obtain ⟨tEntry, htEntry, hInSub⟩ := Finset.mem_biUnion.mp hRightSurv
          refine Finset.mem_union_right _ ?_
          obtain ⟨htEntry, htAcc⟩ := Finset.mem_filter.mp htEntry
          have hCollapse : action ∈
              computeFutureOf (right.reannotate alphabet) tEntry := by
            rw [← computeFutureOf_par_survivorRight alphabet left right
              interface hLeftDisjoint hRightDisjoint tEntry
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).1,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                  _ q2 _ (by rw [hRightFragEq]; exact hq2)
                  (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                    hRightDisjoint s hs)) htEntry)
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).2.2,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact htAcc)]
            rw [computeFutureOf, hFuel, computeFutureOfFuel]
            refine Finset.mem_filter.mpr ⟨?_, hGate⟩
            refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
            rw [hParEq]
            exact hInSub
          have htStates : tEntry ∈
              (compileTypeFuel (typeCompilationFuel right) right).states := by
            rw [← hRightFragEq]
            exact (PendingAutomaton.futureReachable_subset_of_reference_closed
              _ q2 _ (by rw [hRightFragEq]; exact hq2)
              (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                hRightDisjoint s hs)) htEntry
          have hMono := computeFutureOf_mono_of_futureReachable right
            hRightDisjoint hq2
            (by rw [← hRightFragEq]; exact htEntry)
          exact hMono (hSurvRight tEntry (by rw [← hRightFragEq]; exact htEntry)
            hCollapse)
      · -- the mirror, for a left survivor sub-reach
        obtain ⟨sEntry, hsEntry, hInSub⟩ := Finset.mem_biUnion.mp hLeftSurv
        obtain ⟨hsEntry, hsAcc⟩ := Finset.mem_filter.mp hsEntry
        refine Finset.mem_union_left _ ?_
        have hCollapse : action ∈
            computeFutureOf (left.reannotate alphabet) sEntry := by
          rw [← computeFutureOf_par_survivorLeft alphabet left right
            interface hLeftDisjoint hRightDisjoint sEntry
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).1,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                _ q1 _ (by rw [hLeftFragEq]; exact hq1)
                (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
                  hLeftDisjoint s hs)) hsEntry)
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).2.2,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact hsAcc)]
          rw [computeFutureOf, hFuel, computeFutureOfFuel]
          refine Finset.mem_filter.mpr ⟨?_, hGate⟩
          refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
          rw [hParEq]
          exact hInSub
        have hsStates : sEntry ∈
            (compileTypeFuel (typeCompilationFuel left) left).states := by
          rw [← hLeftFragEq]
          exact (PendingAutomaton.futureReachable_subset_of_reference_closed
            _ q1 _ (by rw [hLeftFragEq]; exact hq1)
            (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
              hLeftDisjoint s hs)) hsEntry
        have hMono := computeFutureOf_mono_of_futureReachable left
          hLeftDisjoint hq1
          (by rw [← hLeftFragEq]; exact hsEntry)
        exact hMono (hSurvLeft sEntry (by rw [← hLeftFragEq]; exact hsEntry)
          hCollapse)
    rw [← hFilterEq]
    exact Finset.mem_filter.mpr ⟨hInMenus, hGate⟩
  · intro action hAction
    have hMemRaw := hRhsSubset hAction
    refine Finset.mem_filter.mpr ⟨hMemRaw, ?_⟩
    have hIn : action ∈ (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
        (fun a => a ∈ (PactType.par alphabet left right interface).alphabet.actions) := by
      rw [hFilterEq]; exact hAction
    exact (Finset.mem_filter.mp hIn).2

/-- The compiled parallel product, unfolded at its own fuel. -/
theorem compileTypeFuel_par_eq (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    compileTypeFuel (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
      buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right))
          (left.reannotate alphabet))
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right))
          (right.reannotate alphabet))
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel left)) left)
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel right)) right)
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel left)) (left.reannotate alphabet))
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel right)) (right.reannotate alphabet)) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]

/-- The completed product state offers nothing: its only edges are the idle
self-loops, which carry no current offers and name no further state. -/
theorem computeFutureOf_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    computeFutureOf (.par alphabet left right interface) .final = ∅ := by
  classical
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hShape : ∀ edge ∈ (compileTypeFuel
      (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
      (PactType.par alphabet left right interface)).edges,
      edge.source = TypeAutomatonState.final →
      edge.current = ∅ ∧ edge.future = .explicit ∅ := by
    intro edge hEdge hSource
    simp only [compileTypeFuel] at hEdge
    exact buildParallelAutomaton_final_edge_shape _ _ _ _ _ _ _ _ _ _ _ _
      edge hEdge hSource
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set pending : PendingAutomaton :=
    { states := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).edges }
    with hPendingDef
  have hRefs : pending.referencedStates TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro target hTarget
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hTargetMem⟩ := hTarget
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    rw [(hShape edge hMem hSource).2] at hTargetMem
    simp at hTargetMem
  have hOffers : pending.offersAt TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro action hAction
    rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
    obtain ⟨edge, hEdge, hActionMem⟩ := hAction
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    obtain ⟨hCurrent, hFuture⟩ := hShape edge hMem hSource
    rw [hCurrent, hFuture] at hActionMem
    simp at hActionMem
  rw [FiniteMenuGraph.futureReachable_eq_singleton_of_referencedStates_eq_empty
      _ .final (by simp only [PendingAutomaton.withMenuDependencies, hRefs,
        compileTypeMenuLinksFuel_final, Finset.union_empty])]
  simp only [Finset.singleton_biUnion, hOffers,
    stateProductInfo_par_final alphabet left right interface,
    Finset.empty_union, Finset.filter_empty]

/-- H-menus at a parallel product, by the four families of related states. -/
theorem futureOffersAgree_par (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (hSurvLeft : ∀ (rho : PactType) (q1 : TypeAutomatonState),
      relationMembership (buildRelationSet left (compileType left)) rho q1 →
      ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left) left).states,
          (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
          PendingAutomaton).futureReachable q1,
        computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ (rho : PactType) (q2 : TypeAutomatonState),
      relationMembership (buildRelationSet right (compileType right)) rho q2 →
      ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right) right).states,
          (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
          PendingAutomaton).futureReachable q2,
        computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right)
    (hLeftResign : FutureOffersAgree (left.reannotate alphabet))
    (hRightResign : FutureOffersAgree (right.reannotate alphabet)) :
    FutureOffersAgree (.par alphabet left right interface) := by
  classical
  intro residual state hRelated
  rcases relationMembership_par_cases alphabet left right interface hRelated with
    ⟨q1, q2, rL, rR, hEq, hL, hR⟩ | ⟨q1, rL, hEq, hL, hNotAcc⟩ |
      ⟨q2, rR, hEq, hR, hNotAcc⟩ | hFinal
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_pair alphabet left right interface hLeftDisjoint
        hRightDisjoint hCompatible q1 q2 (hSurvLeft rL q1 hL) (hSurvRight rR q2 hR)
        (relationMembership_state_mem left _ q1 hLeftDisjoint hL)
        (relationMembership_state_mem right _ q2 hRightDisjoint hR),
      hLeft hL, hRight hR, typeFutureOffers_parallel]
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorLeft alphabet left right interface
        hLeftDisjoint hRightDisjoint q1
        (relationMembership_state_mem (left.reannotate alphabet) _ q1
          (reannotate_offerBranchesDisjoint left alphabet hLeftDisjoint) hL)
        hNotAcc]
    exact hLeftResign hL
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorRight alphabet left right interface
        hLeftDisjoint hRightDisjoint q2
        (relationMembership_state_mem (right.reannotate alphabet) _ q2
          (reannotate_offerBranchesDisjoint right alphabet hRightDisjoint) hR)
        hNotAcc]
    exact hRightResign hR
  · injection hFinal with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_final alphabet left right interface]
    simp only [typeFutureOffers, typeFutureOffersFuel]

#print axioms stateProductInfo_par_pair
#print axioms stateProductInfo_par_final
#print axioms compileTypeFuel_par_eq
#print axioms buildParallelAutomaton_final_edge_shape
#print axioms computeFutureOf_par_final

/-- The paper's survivor bullet: the re-signed component's menu at a state is
bounded by the component's own.  The state is related by Lemma 4.5's
reachability clause, the re-signing transport moves that witness across, and
`<dead-declarations-inert>` equates the two menus. -/
theorem survivorMenuBound (component : PactType) (target : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (hTargetWF : target.WellFormed)
    (hNoInterface : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces component)
    (hComponent : FutureOffersAgree component)
    (hResign : FutureOffersAgree (component.reannotate target))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) residual state)
    (hActions : target.actions ⊆ residual.alphabet.actions)
    (hResidualWF : residual.AlphabetWellFormed) :
    computeFutureOf (component.reannotate target) state ⊆
      computeFutureOf component state := by
  classical
  obtain ⟨theta, hThetaRelated, hLive⟩ :=
    survivorTransport_all component bound hWF target hTargetWF hNoInterface
      residual state hRelated
  rw [hResign hThetaRelated, hComponent hRelated,
    ← PactType.liveEq_preserves_futOff hLive]
  exact typeFutureOffers_reannotate_subset residual target hResidualWF hActions

/-- Lemma 4.5's reachability clause, in the same-cycle form the menus need: from
a related state, every state reachable before the next clock is related.  The
marker escape of the closure lemma cannot fire, because a closed type compiles
without marker edges. -/
theorem futureReachable_related
    (processType : PactType)
    (hClosed : PactType.AllVariablesBound [] processType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (hResign : ∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target))
    (hAccepting : ∀ (component : PactType) (target : PactTypeAlphabet)
      (fuel : Nat), component.OfferBranchesDisjoint →
      (compileTypeFuel fuel (component.reannotate target)).accepting =
        (compileTypeFuel fuel component).accepting)
    (hResignDisjoint : ∀ (component : PactType) (target : PactTypeAlphabet),
      component.OfferBranchesDisjoint →
      (component.reannotate target).OfferBranchesDisjoint)
    (hSelectingDisjoint : ∀ (alphabet : PactTypeAlphabet)
      (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      PactType.OfferBranchesDisjointBranches branches →
      (parallelTypeBranchesSelecting alphabet selected
        branches).OfferBranchesDisjoint)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet processType (compileType processType)) residual state) :
    ∀ p ∈ (⟨(compileTypeFuel (typeCompilationFuel processType)
          processType).states,
        (compileTypeFuel (typeCompilationFuel processType)
          processType).edges⟩ : PendingAutomaton).futureReachable state,
      ∃ rho, relationMembership
        (buildRelationSet processType (compileType processType)) rho p := by
  classical
  set frag := compileTypeFuel (typeCompilationFuel processType) processType
    with hFrag
  set pending : PendingAutomaton := ⟨frag.states, frag.edges⟩ with hPending
  -- the related states form a reference-closed set
  set allowed : Finset TypeAutomatonState :=
    frag.states.filter (fun p => ∃ rho, relationMembership
      (buildRelationSet processType (compileType processType)) rho p)
    with hAllowed
  have hStep : ∀ s ∈ allowed, pending.referencedStates s ⊆ allowed := by
    intro s hs t ht
    obtain ⟨hsStates, rho, hRho⟩ := Finset.mem_filter.mp hs
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at ht
    obtain ⟨edge, hEdge, hMem⟩ := ht
    have hEdgeMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hMem; simp at hMem
    rw [if_neg hTock] at hMem
    have hTargetEq : t = edge.target := by
      cases hFut : edge.future with
      | explicit offers => rw [hFut] at hMem; simp at hMem
      | «at» s' r =>
          rw [hFut] at hMem
          simp only [Finset.mem_singleton] at hMem
          rw [hMem, compileTypeFuel_futureTargetsAreEdgeTargets
            (typeCompilationFuel processType) processType edge hEdgeMem s' r
            hFut]
    subst hTargetEq
    rcases buildRelationSetCoreFuel_edge_target_mem hResign hAccepting
        hResignDisjoint hSelectingDisjoint (typeCompilationFuel processType)
        processType le_rfl hDisjoint edge hEdgeMem with
      ⟨rho', hRho'⟩ | ⟨markerName, hMarker⟩
    · refine Finset.mem_filter.mpr ⟨?_, rho', hRho'⟩
      exact compileTypeFuel_edgeTargetsInStates _ _ le_rfl hDisjoint edge
        hEdgeMem
    · exact absurd hMarker (compileTypeFuel_noMarker_of_closed _ processType
        hClosed markerName edge hEdgeMem)
  intro p hp
  have hSeed : state ∈ allowed :=
    Finset.mem_filter.mpr
      ⟨relationMembership_state_mem processType residual state hDisjoint
        hRelated, residual, hRelated⟩
  exact (Finset.mem_filter.mp
    (PendingAutomaton.futureReachable_subset_of_reference_closed pending state
      allowed hSeed hStep hp)).2

/-- The survivor bound over a whole same-cycle reach: Lemma 4.5's reachability
clause makes every reachable state related, and the survivor bullet then bounds
its re-signed menu. -/
theorem survivorMenuBound_reach (component : PactType)
    (target : PactTypeAlphabet) (bound : List String)
    (hWF : TypeWellFormedIn bound component)
    (hClosed : PactType.AllVariablesBound [] component)
    (hDisjoint : component.OfferBranchesDisjoint)
    (hResign : ∀ (c : PactType) (a : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel c →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (c.reannotate a))
    (hAccepting : ∀ (c : PactType) (a : PactTypeAlphabet) (fuel : Nat),
      c.OfferBranchesDisjoint →
      (compileTypeFuel fuel (c.reannotate a)).accepting =
        (compileTypeFuel fuel c).accepting)
    (hResignDisjoint : ∀ (c : PactType) (a : PactTypeAlphabet),
      c.OfferBranchesDisjoint → (c.reannotate a).OfferBranchesDisjoint)
    (hSelectingDisjoint : ∀ (a : PactTypeAlphabet)
      (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      PactType.OfferBranchesDisjointBranches branches →
      (parallelTypeBranchesSelecting a selected branches).OfferBranchesDisjoint)
    (hTargetWF : target.WellFormed)
    (hNoInterface : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces component)
    (hComponent : FutureOffersAgree component)
    (hResignAgree : FutureOffersAgree (component.reannotate target))
    (hResidualWF : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet component (compileType component))
        residual state → residual.AlphabetWellFormed)
    (hResidualActions : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet component (compileType component))
        residual state → target.actions ⊆ residual.alphabet.actions)
    {seed : PactType} {q : TypeAutomatonState}
    (hSeed : relationMembership
      (buildRelationSet component (compileType component)) seed q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      computeFutureOf (component.reannotate target) s ⊆
        computeFutureOf component s := by
  intro s hs
  obtain ⟨rho, hRho⟩ := futureReachable_related component hClosed hDisjoint
    hResign hAccepting hResignDisjoint hSelectingDisjoint hSeed s hs
  exact survivorMenuBound component target bound hWF hTargetWF hNoInterface
    hComponent hResignAgree hRho (hResidualActions hRho) (hResidualWF hRho)

/-- In a marker-free component, the current-offer hypothesis makes every
same-cycle successor of a related state related. -/
theorem futureReachable_related_of_currentOffer
    (component : PactType) (hDisjoint : component.OfferBranchesDisjoint)
    (hNoMarker : ∀ name,
      (compileTypeFuel (typeCompilationFuel component) component).NoMarkerFor name)
    (hCurrent : CurrentOfferCorrespondence component)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) rho q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      ∃ theta, relationMembership
        (buildRelationSet component (compileType component)) theta s := by
  classical
  let fragment := compileTypeFuel (typeCompilationFuel component) component
  let pending : PendingAutomaton := ⟨fragment.states, fragment.edges⟩
  let allowed := fragment.states.filter fun s => ∃ theta,
    relationMembership (buildRelationSet component (compileType component)) theta s
  have hStep : ∀ s ∈ allowed, pending.referencedStates s ⊆ allowed := by
    intro s hs t ht
    obtain ⟨_, theta, hTheta⟩ := Finset.mem_filter.mp hs
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at ht
    obtain ⟨edge, hEdge, hRef⟩ := ht
    obtain ⟨hEdgeMem, hSource⟩ := Finset.mem_filter.mp hEdge
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hRef
      simp at hRef
    rw [if_neg hTock] at hRef
    have hTarget : t = edge.target := by
      cases hFuture : edge.future with
      | explicit offers => rw [hFuture] at hRef; simp at hRef
      | «at» target removed =>
          rw [hFuture] at hRef
          simp only [Finset.mem_singleton] at hRef
          rw [hRef, compileTypeFuel_futureTargetsAreEdgeTargets
            (typeCompilationFuel component) component edge hEdgeMem
            target removed hFuture]
    subst t
    cases hLabel : edge.label with
    | «variable» name => exact False.elim (hNoMarker name edge hEdgeMem hLabel)
    | visible label =>
        have hPublic : (compileType component).HasEdge s edge.environment label
            ⟨edge.current, match edge.future with
              | .explicit offers => offers
              | .at target removed => computeFutureOf component target \ removed⟩
            edge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge]
          exact ⟨edge, hEdgeMem, hSource, rfl, hLabel, rfl, rfl, rfl⟩
        obtain ⟨theta', _, _, hTheta'⟩ := hCurrent.2 hTheta hPublic
        exact Finset.mem_filter.mpr
          ⟨compileTypeFuel_edgeTargetsInStates _ _ le_rfl hDisjoint edge hEdgeMem,
            theta', hTheta'⟩
  have hSeed : q ∈ allowed := Finset.mem_filter.mpr
    ⟨relationMembership_state_mem component rho q hDisjoint hRelated, rho, hRelated⟩
  intro s hs
  exact (Finset.mem_filter.mp
    (PendingAutomaton.futureReachable_subset_of_reference_closed pending q
      allowed hSeed hStep hs)).2

/-- At a related child state, narrowing to the parent alphabet cannot add
survivor offers. The current-offer hypothesis supplies the reachable witnesses;
the two menu hypotheses and survivor transport compare their menus. -/
theorem survivorMenuBound_par
    (component : PactType) (alphabet : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (hAlphabet : alphabet.WellFormed)
    (hSubset : alphabet.actions ⊆ component.alphabet.actions)
    (hTail : ∀ name, component.TailOccurrences name False)
    (hCurrent : CurrentOfferCorrespondence component)
    (hMenu : FutureOffersAgree component)
    (hResignMenu : FutureOffersAgree (component.reannotate alphabet))
    (rho : PactType) (q : TypeAutomatonState)
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) rho q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      computeFutureOf (component.reannotate alphabet) s ⊆
        computeFutureOf component s := by
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  obtain ⟨hA, _, _, _, _, hTR, _, _, _, _, _, _, hIS, hIAS, _⟩ := id hWF
  intro s hs
  obtain ⟨theta, hTheta⟩ := futureReachable_related_of_currentOffer component
    hDisjoint (fun name => compileTypeFuel_noMarkerFor name _ _ (hTail name))
    hCurrent hRelated s hs
  apply survivorMenuBound component alphabet bound hWF hAlphabet
    (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS
      action (hSubset hAction)) hMenu hResignMenu hTheta
  · rw [relationMembership_alphabet_eq_of_wellFormed component theta s hA hTheta]
    exact hSubset
  · exact relationMembership_alphabetWellFormed
      committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
      component theta s hA hIS hIAS hTR hDisjoint hTheta

/-- The parallel menu case uses only well-formedness and the lower-rank
current-offer and menu hypotheses. -/
theorem futureOffersAgree_par_of_typeWF
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeftCurrent : CurrentOfferCorrespondence left)
    (hRightCurrent : CurrentOfferCorrespondence right)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right)
    (hLeftResign : FutureOffersAgree (left.reannotate alphabet))
    (hRightResign : FutureOffersAgree (right.reannotate alphabet)) :
    FutureOffersAgree (.par alphabet left right interface) := by
  obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
  have hAlphabet : alphabet.WellFormed :=
    PactType.AlphabetWellFormed.alphabet_wellFormed hWF.1
  have hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface := by
    have h := hWF.1
    simp only [PactType.AlphabetWellFormed] at h
    exact h.2.1
  have hTail : ∀ name, left.TailOccurrences name False ∧
      right.TailOccurrences name False := by
    intro name
    simpa only [PactType.TailOccurrences] using hWF.2.2.2.1 name
  intro rho q hRelated
  exact futureOffersAgree_par alphabet left right interface
    (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
    (offerBranchesDisjoint_of_wellFormedIn hRightWF) hCompatible
    (survivorMenuBound_par left alphabet bound hLeftWF hAlphabet
      (PactTypeAlphabet.parent_actions_subset_left hCompatible)
      (fun name => (hTail name).1) hLeftCurrent hLeft hLeftResign)
    (survivorMenuBound_par right alphabet bound hRightWF hAlphabet
      (PactTypeAlphabet.parent_actions_subset_right hCompatible)
      (fun name => (hTail name).2) hRightCurrent hRight hRightResign)
    hLeft hRight hLeftResign hRightResign hRelated

#print axioms futureReachable_related_of_currentOffer
#print axioms survivorMenuBound_par
#print axioms futureOffersAgree_par_of_typeWF

/-- The three helpers, proved together by induction on `typeCompilationFuel`. -/
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      CurrentOfferCorrespondence processType ∧
        SameCycleCompletionAgrees processType ∧
        FutureOffersAgree processType := by
  intro bound processType
  induction hFuel : typeCompilationFuel processType
      using Nat.strong_induction_on generalizing bound processType with
  | _ n ih =>
    intro hWF
    cases processType with
    | skip alphabet =>
        exact ⟨currentOfferCorrespondence_skip alphabet,
          sameCycleCompletionAgrees_skip alphabet,
          futureOffersAgree_skip alphabet⟩
    | var alphabet name =>
        exact ⟨currentOfferCorrespondence_var alphabet name,
          sameCycleCompletionAgrees_var alphabet name,
          futureOffersAgree_var alphabet name⟩
    | message alphabet msg dir =>
        exact ⟨currentOfferCorrespondence_message alphabet msg dir,
          sameCycleCompletionAgrees_message alphabet msg dir,
          futureOffersAgree_message alphabet msg dir⟩
    | tock alphabet =>
        exact ⟨currentOfferCorrespondence_tock alphabet,
          sameCycleCompletionAgrees_tock alphabet,
          futureOffersAgree_tock alphabet⟩
    | progress alphabet pid =>
        exact ⟨currentOfferCorrespondence_progress alphabet pid,
          sameCycleCompletionAgrees_progress alphabet pid,
          futureOffersAgree_progress alphabet pid⟩
    | choice alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_choice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_choice alphabet left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_choice alphabet left right hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_choice alphabet left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2.2 hRight.2.2
    | fairChoice alphabet bid left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_fairChoice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_fairChoice alphabet bid left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_fairChoice alphabet bid left right
            hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_fairChoice alphabet bid left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2.2 hRight.2.2
    | seq alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_seq alphabet left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_seq alphabet left right
            (offerBranchesDisjoint_of_ownership left
              hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            hWF resignTransport_relationMembership
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            (fun hRel =>
              relationMembership_alphabetWellFormed
                committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
                left _ _ hLeftWF.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.1
                (offerBranchesDisjoint_of_ownership left
                  hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                hRel)
            hLeft.1 hRight.1
        · apply futureOffersAgree_seq alphabet left right
            (offerBranchesDisjoint_of_ownership left
              hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2.2 hRight.2.2
          -- Paper: propagate the optimistic flag backwards through execution references and L.
          sorry -- remaining part of the original `.seq` menu obligation
    | par alphabet left right interface =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeftResignFuel :
            typeCompilationFuel (left.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hLeftFuel
        have hRightResignFuel :
            typeCompilationFuel (right.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hRightFuel
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        obtain ⟨hLeftResignWF, hRightResignWF⟩ := typeWellFormedIn_survivor hWF
        have hLeftResign :=
          ih _ hLeftResignFuel bound (left.reannotate alphabet) rfl hLeftResignWF
        have hRightResign :=
          ih _ hRightResignFuel bound (right.reannotate alphabet) rfl
            hRightResignWF
        refine ⟨?_, ?_, ?_⟩
        · sorry -- current-offer correspondence, `.par`
        · sorry -- same-cycle completion, `.par`
        · exact futureOffersAgree_par_of_typeWF hWF hLeft.1 hRight.1
            hLeft.2.2 hRight.2.2 hLeftResign.2.2 hRightResign.2.2
    | recur alphabet name body =>
        have hBodyWF := typeWellFormedIn_recur hWF
        have hBodyFuel : typeCompilationFuel body < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBody := ih _ hBodyFuel (name :: bound) body rfl hBodyWF
        refine ⟨?_, ?_, ?_⟩
        · exact currentOfferCorrespondence_recur_of_typeWF alphabet name body
            hWF hBody.1
        · sorry -- same-cycle completion, `.recur`
        · sorry -- menu equation, `.recur`
    | xoffer alphabet elseType branches =>
        obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBranchFuel : ∀ entry ∈ branches,
            typeCompilationFuel entry.2 < n := by
          intro entry hEntry
          rw [← hFuel]
          simp only [typeCompilationFuel]
          have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry
            hEntry
          omega
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hBranch : ∀ entry ∈ branches,
            CurrentOfferCorrespondence entry.2 ∧
              SameCycleCompletionAgrees entry.2 ∧ FutureOffersAgree entry.2 :=
          fun entry hEntry =>
            ih _ (hBranchFuel entry hEntry) bound entry.2 rfl
              (hBranchWF entry hEntry)
        refine ⟨?_, sameCycleCompletionAgrees_xoffer alphabet elseType branches
            hElse.2.1 (fun entry hEntry => (hBranch entry hEntry).2.1), ?_⟩
        · refine currentOfferCorrespondence_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (fun a t hMem =>
              offerBranchesDisjoint_of_ownership t
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun a t hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem]; rfl)
            hElse.1 (fun a t hMem => (hBranch (a, t) hMem).1)
        · exact futureOffersAgree_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.xoffer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun branch hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem)
            hElse.2.2 (fun branch hMem => (hBranch branch hMem).2.2)
    | offer alphabet elseType branches =>
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hGeneratedFuel : ∀ selected,
            typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
          intro selected
          rw [← hFuel, typeCompilationFuel_parallelTypeBranchesSelecting]
          simp only [typeCompilationFuel]
          omega
        obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hSelected : ∀ selected ∈ branches,
            CurrentOfferCorrespondence
                (parallelTypeBranchesSelecting alphabet selected branches) ∧
              SameCycleCompletionAgrees
                (parallelTypeBranchesSelecting alphabet selected branches) ∧
              FutureOffersAgree
                (parallelTypeBranchesSelecting alphabet selected branches) :=
          fun selected hMem =>
            ih _ (hGeneratedFuel selected) bound _ rfl (hSelectedWF selected hMem)
        refine ⟨?_, sameCycleCompletionAgrees_offer alphabet elseType branches
            hElse.2.1
            (fun selected hMem => (hSelected selected hMem).2.1), ?_⟩
        · refine currentOfferCorrespondence_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            ?_
            (fun selected hMem =>
              offerBranchesDisjoint_of_ownership _
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun selected hMem => by
              rw [parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem]; rfl)
            hElse.1 (fun selected hMem => (hSelected selected hMem).1)
          · intro branch hMem
            have hWholeDisjoint :=
              offerBranchesDisjoint_of_ownership
                (.offer alphabet elseType branches)
                hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
                hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp only [PactType.OfferBranchesDisjoint] at hWholeDisjoint
            exact offerBranchesDisjoint_of_mem_branch hWholeDisjoint.2.2 hMem
        · refine futureOffersAgree_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.offer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun selected hMem =>
              parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem)
            ?_ hElse.2.2 (fun selected hMem => (hSelected selected hMem).2.2)
          -- The generated product's menu, from the raw branch bodies.  The gate
          -- is exactly the declaredness the syntax lemma needs.
          intro hGate selected hMem
          have h := hWF.1
          simp only [PactType.AlphabetWellFormed] at h
          exact typeFutureOffers_parallelTypeBranchesSelecting alphabet selected
            branches hGate
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).1)
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).2)


end

end Pact
