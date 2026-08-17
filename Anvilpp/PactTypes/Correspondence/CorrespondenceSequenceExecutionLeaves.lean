import Anvilpp.PactTypes.Correspondence.CorrespondenceBundle

/-!
# CompilationSequenceExecutionCorrect leaves: skip/progress/var/tock/message/choice/fairChoice/sequence
-/

namespace Pact

noncomputable section

private theorem computeFuture_eq_empty_of_offersAt_eq_empty
    (automaton : PendingAutomaton)
    (hOffers : ∀ state, automaton.offersAt state = ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  unfold computeFuture
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  rcases Finset.mem_biUnion.mp hAction with ⟨reached, _, hOffer⟩
  rw [hOffers reached] at hOffer
  simp at hOffer

private theorem sequenceExecutionAutomaton_offersAt_eq_empty
    (fragment : AutomatonFragment) (state : TypeAutomatonState)
    (hEdges : ∀ edge ∈ fragment.edges, edge.source = state →
      edge.current = ∅ ∧ edge.label ≠ .future) :
    (sequenceExecutionAutomaton fragment).offersAt state = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
  simp only [sequenceExecutionAutomaton, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  have hFields := hEdges childEdge hChildEdge hSource
  rcases hFields with ⟨hCurrent, hNotFuture⟩
  cases hLabel : childEdge.label with
  | future => exact (hNotFuture hLabel).elim
  | visible label =>
      simp [hLabel, hCurrent, AutomatonConstructionLabel.semantic] at hOffer
  | «variable» name =>
      simp [hLabel, hCurrent, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] at hOffer

theorem compilationSequenceExecutionCorrect_skip
    (signature : TypeAlphabet) :
    CompilationSequenceExecutionCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hAction
    unfold computeFuture at hAction
    simp only [Finset.mem_biUnion] at hAction
    rcases hAction with ⟨reached, _, hOffer⟩
    simp [sequenceExecutionAutomaton, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hOffer
  · constructor
    · intro _
      simp [PactType.CanCompleteBeforeTock]
    · intro _
      refine ⟨.root,
        PendingAutomaton.mem_futureReachable_self _ .root, ?_⟩
      simp [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]

theorem compilationSequenceExecutionCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationSequenceExecutionCorrect signature (.progress pid) := by
  intro state residual hRelated
  cases hRelated with
  | progress_source | progress_final =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with ⟨environment, _, rfl⟩ |
          ⟨environment, _, rfl⟩ <;> simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨_, PendingAutomaton.mem_futureReachable_self _ _, ?_⟩
          simp [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]

/-- A free-variable marker never completes and carries no future offers of its
own: its compiled fragment has empty `skipping`/`completing` sets, and every
edge is labelled `.variable name` with empty current offers. -/
theorem compilationSequenceExecutionCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationSequenceExecutionCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  constructor
  · apply computeFuture_eq_empty_of_offersAt_eq_empty
    intro reached
    apply sequenceExecutionAutomaton_offersAt_eq_empty
    intro edge hEdge hSource
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image] at hEdge
    obtain ⟨environment, _, rfl⟩ := hEdge
    simp
  · constructor
    · rintro ⟨completed, _, hAccepting | hCompleting⟩
      · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
          at hAccepting
      · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
          at hCompleting
    · intro hComplete
      simp [PactType.CanCompleteBeforeTock] at hComplete

theorem compilationSequenceExecutionCorrect_tock
    (signature : TypeAlphabet) :
    CompilationSequenceExecutionCorrect signature .tock := by
  intro state residual hRelated
  cases hRelated with
  | cycle_source =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with hAction | hFinal
        · rcases hAction with ⟨environment, _, rfl⟩
          split <;> simp
        · rcases hFinal with ⟨environment, _, rfl⟩
          simp
      · constructor
        · rintro ⟨completed, hReachable, hCompleted⟩
          let fragment := compileTypeFuel signature
            (typeCompilationFuel PactType.tock) PactType.tock
          let execution := sequenceExecutionAutomaton fragment
          have hTargets : fragment.FutureTargetsInStates := by
            exact compileTypeFuel_futureTargetsInStates signature
              (typeCompilationFuel PactType.tock) PactType.tock
                (typeCompilationFuel_sufficient PactType.tock)
          have hClosed : execution.ReferencesClosed :=
            sequenceExecutionAutomaton_referencesClosed fragment hTargets
          have hRoot : TypeAutomatonState.root ∈ execution.states := by
            simp [execution, fragment, sequenceExecutionAutomaton,
              typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment]
          have hReachSubset : execution.futureReachable .root ⊆
              {.root} := by
            apply execution.futureReachable_subset_of_reference_closed
            · simp
            · intro source hSource target hReference
              simp only [Finset.mem_singleton] at hSource ⊢
              subst source
              simp only [PendingAutomaton.referencedStates,
                Finset.mem_biUnion, Finset.mem_filter] at hReference
              rcases hReference with
                ⟨edge, ⟨hEdge, hEdgeSource⟩, hFuture⟩
              simp only [execution, fragment, sequenceExecutionAutomaton,
                Finset.mem_image] at hEdge
              rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
              simp only [typeCompilationFuel, compileTypeFuel,
                finishAutomatonFragment, Finset.mem_union,
                Finset.mem_image] at hChildEdge
              rcases hChildEdge with hAction | hFinalEdge
              · rcases hAction with ⟨environment, _, rfl⟩
                by_cases hClock : environment.clock = true
                · simp [hClock, AutomatonConstructionLabel.semantic]
                    at hFuture
                · simpa [hClock, AutomatonConstructionLabel.semantic,
                    TypeLabel.silent] using hFuture
              · rcases hFinalEdge with ⟨environment, _, rfl⟩
                simp at hEdgeSource
          have hCompletedRoot : completed = .root := by
            simpa [execution, fragment] using hReachSubset hReachable
          subst completed
          simp [fragment, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment] at hCompleted
        · intro hComplete
          simp [PactType.CanCompleteBeforeTock] at hComplete
  | cycle_final =>
      constructor
      · apply computeFuture_eq_empty_of_offersAt_eq_empty
        intro reached
        apply sequenceExecutionAutomaton_offersAt_eq_empty
        intro edge hEdge hSource
        simp only [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
          at hEdge
        rcases hEdge with hAction | hFinal
        · rcases hAction with ⟨environment, _, rfl⟩
          split <;> simp
        · rcases hFinal with ⟨environment, _, rfl⟩
          simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.final,
            PendingAutomaton.mem_futureReachable_self _ .final, ?_⟩
          simp [typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]

theorem compilationSequenceExecutionCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationSequenceExecutionCorrect signature (.message msg dir) := by
  let processType := PactType.message msg dir
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let execution := sequenceExecutionAutomaton fragment
  have hTargets : fragment.FutureTargetsInStates := by
    exact compileTypeFuel_futureTargetsInStates signature
      (typeCompilationFuel processType) processType
        (typeCompilationFuel_sufficient processType)
  have hClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hTargets
  have hRoot : TypeAutomatonState.root ∈ execution.states := by
    simp [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hFinal : TypeAutomatonState.final ∈ execution.states := by
    simp [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  have hExecutionStates : execution.states = {.root, .final} := by
    ext candidate
    simp only [execution, fragment, processType, sequenceExecutionAutomaton,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · intro hCandidate
      rcases hCandidate with (rfl | rfl) | ⟨edge, hEdge, rfl⟩
      · simp
      · simp
      · rcases hEdge with (hFiring | hWaiting) | hFinalEdge
        · rcases hFiring with ⟨environment, _, rfl⟩
          simp
        · rcases hWaiting with ⟨environment, _, rfl⟩
          simp
        · rcases hFinalEdge with ⟨environment, _, rfl⟩
          simp
    · intro hCandidate
      exact Or.inl hCandidate
  have hOffersRoot : execution.offersAt .root = {(msg, dir)} := by
    ext action
    constructor
    · intro hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp only [execution, fragment, processType,
        sequenceExecutionAutomaton, Finset.mem_image] at hEdge
      rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
      simp only [typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
        at hChildEdge
      rcases hChildEdge with (hFiring | hWaiting) | hFinalEdge
      · rcases hFiring with ⟨environment, _, rfl⟩
        have hNotTock : TypeLabel.message msg dir ≠ TypeLabel.tock := by
          simp [TypeLabel.message]
        simp [AutomatonConstructionLabel.semantic, hNotTock] at hOffer
        simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
      · rcases hWaiting with ⟨environment, _, rfl⟩
        have hNotTock : TypeLabel.silent ≠ TypeLabel.tock := by
          simp [TypeLabel.silent]
        simp [AutomatonConstructionLabel.semantic, hNotTock] at hOffer
        simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
      · rcases hFinalEdge with ⟨environment, _, rfl⟩
        simp at hSource
    · intro hAction
      simp only [Finset.mem_singleton] at hAction
      subst action
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter]
      let environment := TypeEnvironment.empty
      let childEdge : PendingAutomatonEdge :=
        { source := .root
          environment := environment
          label := .visible TypeLabel.silent
          current := {(msg, dir)}
          future := .explicit ∅
          target := .root }
      let edge : PendingAutomatonEdge :=
        { source := childEdge.source
          environment := childEdge.environment
          label := childEdge.label
          current := childEdge.current
          future := .at childEdge.target childEdge.current
          target := childEdge.target }
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [edge, execution, sequenceExecutionAutomaton,
          Finset.mem_image]
        refine ⟨childEdge, ?_, rfl⟩
        simp [childEdge, fragment, processType, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment, environment,
          TypeAlphabet.localEnvironments, TypeEnvironment.empty,
          TypeEnvironment.hasNeed]
      · simp [edge, childEdge, AutomatonConstructionLabel.semantic,
          TypeLabel.silent]
  have hOffersFinal : execution.offersAt .final = ∅ := by
    apply sequenceExecutionAutomaton_offersAt_eq_empty
    intro edge hEdge hSource
    simp only [fragment, processType, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_image] at hEdge
    rcases hEdge with (hFiring | hWaiting) | hFinalEdge
    · rcases hFiring with ⟨environment, _, rfl⟩
      simp at hSource
    · rcases hWaiting with ⟨environment, _, rfl⟩
      simp at hSource
    · rcases hFinalEdge with ⟨environment, _, rfl⟩
      simp
  intro state residual hRelated
  cases hRelated with
  | message_source =>
      constructor
      · ext action
        constructor
        · intro hAction
          unfold computeFuture at hAction
          rcases Finset.mem_biUnion.mp hAction with
            ⟨reached, hReachable, hOffer⟩
          have hReachState : reached ∈ execution.states :=
            (execution.futureReachable_subset_of_reference_closed .root
              execution.states hRoot
                (fun source hSource => hClosed source hSource)) hReachable
          have hCases : reached = .root ∨ reached = .final := by
            rw [hExecutionStates] at hReachState
            simpa using hReachState
          rcases hCases with rfl | rfl
          · rw [hOffersRoot] at hOffer
            simpa [typeFutureOffers, typeFutureOffersFuel] using hOffer
          · rw [hOffersFinal] at hOffer
            simp at hOffer
        · intro hAction
          simp only [typeFutureOffers, typeFutureOffersFuel,
            Finset.mem_singleton] at hAction
          subst action
          unfold computeFuture
          apply Finset.mem_biUnion.mpr
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          rw [hOffersRoot]
          simp
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          simp [fragment, processType, typeCompilationFuel,
            compileTypeFuel, finishAutomatonFragment]
  | message_final =>
      constructor
      · have hReachSubset : execution.futureReachable .final ⊆
            {.final} := by
          apply execution.futureReachable_subset_of_reference_closed
          · simp
          · intro source hSource target hReference
            simp only [Finset.mem_singleton] at hSource ⊢
            subst source
            simp only [PendingAutomaton.referencedStates,
              Finset.mem_biUnion, Finset.mem_filter] at hReference
            rcases hReference with ⟨edge, ⟨hEdge, hSource⟩, hFuture⟩
            simp only [execution, sequenceExecutionAutomaton,
              Finset.mem_image] at hEdge
            rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
            simp only [fragment, processType, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
              Finset.mem_image] at hChildEdge
            rcases hChildEdge with (hFiring | hWaiting) | hFinalEdge
            · rcases hFiring with ⟨environment, _, rfl⟩
              simp at hSource
            · rcases hWaiting with ⟨environment, _, rfl⟩
              simp at hSource
            · rcases hFinalEdge with ⟨environment, _, rfl⟩
              simpa [AutomatonConstructionLabel.semantic,
                TypeLabel.silent] using hFuture
        unfold computeFuture
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro action hAction
        rcases Finset.mem_biUnion.mp hAction with
          ⟨reached, hReachable, hOffer⟩
        have hReachedFinal : reached = .final := by
          simpa using hReachSubset hReachable
        subst reached
        rw [hOffersFinal] at hOffer
        simp at hOffer
      · constructor
        · intro _
          simp [PactType.CanCompleteBeforeTock]
        · intro _
          refine ⟨.final, execution.mem_futureReachable_self .final, ?_⟩
          simp [fragment, processType, typeCompilationFuel,
            compileTypeFuel, finishAutomatonFragment]

theorem compilationSequenceExecutionCorrect_choice
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    CompilationSequenceExecutionCorrect signature (.choice left right) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let parentFragment := buildChoiceAutomaton signature leftFragment
    rightFragment TypeLabel.silent TypeLabel.silent
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.choice left right)) (.choice left right) =
      parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hLeftRootCanonical := hLeft _ left
    (compileType_initial_relation_of_canonical signature left
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hLeftCanonical))
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation_of_canonical signature right
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical))
  have hLeftRoot :
      computeFuture (sequenceExecutionAutomaton leftFragment)
          leftFragment.initial = typeFutureOffers left ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton leftFragment).futureReachable
                leftFragment.initial,
              completed ∈ leftFragment.accepting ∨
                completed ∈ leftFragment.completing) ↔
          left.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, leftFragment, hLeftStable,
      compileType] using hLeftRootCanonical
  have hRightRoot :
      computeFuture (sequenceExecutionAutomaton rightFragment)
          rightFragment.initial = typeFutureOffers right ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton rightFragment).futureReachable
                rightFragment.initial,
              completed ∈ rightFragment.accepting ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightFragment, hRightStable,
      compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | choice_source =>
      constructor
      · rw [sequenceExecution_buildChoice_computeFuture_root signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent])
          hLeftTargets hRightTargets hLeftInitial hRightInitial,
        typeFutureOffers_choice]
        exact congrArg₂ (fun first second => first ∪ second)
          hLeftRoot.1 hRightRoot.1
      · have hRootWitness :=
          sequenceExecution_buildChoice_completionWitness_root_iff
            signature leftFragment rightFragment TypeLabel.silent
            TypeLabel.silent (by simp [TypeLabel.silent])
            (by simp [TypeLabel.silent]) hLeftTargets hRightTargets
            hLeftInitial hRightInitial
        refine hRootWitness.trans ((or_congr hLeftRoot.2
          hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | choice_left _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature left childState residual hChildRelated
      have hState : childState ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hStateCanonical
      have hChildCanonical := hLeft childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton leftFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    childState,
                  completed ∈ leftFragment.accepting ∨
                    completed ∈ leftFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftFragment,
          hLeftStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_left signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hLeftTargets childState hState).trans hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_left signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hLeftTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_left_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          ((sequenceExecutionAutomaton leftFragment).futureReachable
            childState)).trans hChild.2
  | choice_right _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature right childState residual hChildRelated
      have hState : childState ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hStateCanonical
      have hChildCanonical := hRight childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton rightFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    childState,
                  completed ∈ rightFragment.accepting ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightFragment,
          hRightStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_right signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hRightTargets childState hState).trans hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_right signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          hRightTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_right_iff signature
          leftFragment rightFragment TypeLabel.silent TypeLabel.silent
          ((sequenceExecutionAutomaton rightFragment).futureReachable
            childState)).trans hChild.2
theorem compilationSequenceExecutionCorrect_fairChoice
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right)
    (hLeftCanonical : left.EntryCanonical)
    (hRightCanonical : right.EntryCanonical) :
    CompilationSequenceExecutionCorrect signature
      (.fairChoice bid left right) := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let parentFragment := buildChoiceAutomaton signature leftFragment
    rightFragment (TypeLabel.fair bid true) (TypeLabel.fair bid false)
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.fairChoice bid left right))
        (.fairChoice bid left right) = parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hLeftRootCanonical := hLeft _ left
    (compileType_initial_relation_of_canonical signature left
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hLeftCanonical))
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation_of_canonical signature right
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical))
  have hLeftRoot :
      computeFuture (sequenceExecutionAutomaton leftFragment)
          leftFragment.initial = typeFutureOffers left ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton leftFragment).futureReachable
                leftFragment.initial,
              completed ∈ leftFragment.accepting ∨
                completed ∈ leftFragment.completing) ↔
          left.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, leftFragment, hLeftStable,
      compileType] using hLeftRootCanonical
  have hRightRoot :
      computeFuture (sequenceExecutionAutomaton rightFragment)
          rightFragment.initial = typeFutureOffers right ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton rightFragment).futureReachable
                rightFragment.initial,
              completed ∈ rightFragment.accepting ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightFragment, hRightStable,
      compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | fair_source =>
      constructor
      · rw [sequenceExecution_buildChoice_computeFuture_root signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) (by simp [TypeLabel.fair])
          (by simp [TypeLabel.fair]) hLeftTargets hRightTargets
          hLeftInitial hRightInitial,
        typeFutureOffers_fairChoice]
        exact congrArg₂ (fun first second => first ∪ second)
          hLeftRoot.1 hRightRoot.1
      · have hRootWitness :=
          sequenceExecution_buildChoice_completionWitness_root_iff
            signature leftFragment rightFragment (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (by simp [TypeLabel.fair])
            (by simp [TypeLabel.fair]) hLeftTargets hRightTargets
            hLeftInitial hRightInitial
        refine hRootWitness.trans ((or_congr hLeftRoot.2
          hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | fair_left _ _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature left childState residual hChildRelated
      have hState : childState ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hStateCanonical
      have hChildCanonical := hLeft childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton leftFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton leftFragment).futureReachable
                    childState,
                  completed ∈ leftFragment.accepting ∨
                    completed ∈ leftFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftFragment,
          hLeftStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_left signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hLeftTargets childState hState).trans
            hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_left signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hLeftTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_left_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false)
          ((sequenceExecutionAutomaton leftFragment).futureReachable
            childState)).trans hChild.2
  | fair_right _ _ _ _ childState hChildRelated =>
      have hStateCanonical := compilationStateCorrect_of_compilation
        signature right childState residual hChildRelated
      have hState : childState ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hStateCanonical
      have hChildCanonical := hRight childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton rightFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton rightFragment).futureReachable
                    childState,
                  completed ∈ rightFragment.accepting ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightFragment,
          hRightStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_buildChoice_computeFuture_right signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hRightTargets childState hState).trans
            hChild.1
      · rw [sequenceExecution_buildChoice_futureReachable_right signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false) hRightTargets childState hState]
        exact (buildChoiceAutomaton_completionWitness_right_iff signature
          leftFragment rightFragment (TypeLabel.fair bid true)
          (TypeLabel.fair bid false)
          ((sequenceExecutionAutomaton rightFragment).futureReachable
            childState)).trans hChild.2

theorem compilationSequenceExecutionCorrect_sequence
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationSequenceExecutionCorrect signature left)
    (hRight : CompilationSequenceExecutionCorrect signature right)
    (hRightCanonical : right.EntryCanonical) :
    CompilationSequenceExecutionCorrect signature (.seq left right) := by
  classical
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let rightExecutionFragment := sequenceExecutionFragment rightFragment
  let parentFragment := buildSequenceAutomaton signature leftFragment
    rightFragment
  let shadowFragment := buildSequenceAutomaton signature leftFragment
    rightExecutionFragment
  let parentExecution := sequenceExecutionAutomaton parentFragment
  let shadow : PendingAutomaton :=
    { states := shadowFragment.states, edges := shadowFragment.edges }
  let leftExecution := sequenceExecutionAutomaton leftFragment
  let rightExecution := sequenceExecutionAutomaton rightFragment
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hLeftTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hRightTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hRightExecutionTargets :
      rightExecutionFragment.FutureTargetsInStates :=
    sequenceExecutionFragment_futureTargetsInStates rightFragment
      hRightTargets
  have hLeftInitial : leftFragment.initial ∈ leftFragment.states :=
    compileTypeFuel_initial_mem signature fuel left hLeftFuel
  have hRightInitial : rightFragment.initial ∈ rightFragment.states :=
    compileTypeFuel_initial_mem signature fuel right hRightFuel
  have hRightExecutionInitial : rightExecutionFragment.initial ∈
      rightExecutionFragment.states := by
    exact Finset.mem_union_left _ hRightInitial
  have hParentTargets : parentFragment.FutureTargetsInStates :=
    buildSequenceAutomaton_futureTargetsInStates signature leftFragment
      rightFragment hLeftTargets hRightTargets hRightInitial
  have hShadowTargets : shadowFragment.FutureTargetsInStates :=
    buildSequenceAutomaton_futureTargetsInStates signature leftFragment
      rightExecutionFragment hLeftTargets hRightExecutionTargets
      hRightExecutionInitial
  have hParentClosed : parentExecution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed parentFragment hParentTargets
  have hShadowClosed : shadow.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates shadowFragment
      hShadowTargets
  have hEdges : parentExecution.edges = shadow.edges := by
    exact sequenceExecution_buildSequence_edges signature leftFragment
      rightFragment
  have hAccepting : parentFragment.accepting = shadowFragment.accepting := by
    rfl
  have hCompleting : parentFragment.completing = shadowFragment.completing := by
    rfl
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.seq left right)) (.seq left right) =
      parentFragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hRightRootCanonical := hRight _ right
    (compileType_initial_relation_of_canonical signature right
      (PactType.canonicalEntryResidual_eq_self_of_entryCanonical
        hRightCanonical))
  have hRightRoot :
      computeFuture rightExecution rightFragment.initial =
          typeFutureOffers right ∧
        ((∃ completed ∈ rightExecution.futureReachable
              rightFragment.initial,
              completed ∈ rightFragment.accepting ∨
                completed ∈ rightFragment.completing) ↔
          right.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, rightExecution,
      rightFragment, hRightStable, compileType] using hRightRootCanonical
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | sequence_left_entry _ _ childResidual childQ hEntry hChildRelated =>
      have hLeftStateCanonical := compilationStateCorrect_of_compilation
        signature left childQ childResidual hChildRelated
      have hLeftState : childQ ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hLeftStateCanonical
      have hEntryUnique : childQ = leftFragment.initial :=
        TypeEntry.unique hEntry
          (compileTypeFuel_initial_entry signature fuel left hLeftFuel)
      have hNotDeleted : childQ ∉ sequenceDeleted leftFragment := by
        rw [hEntryUnique]
        exact initial_not_mem_sequenceDeleted leftFragment
      have hChildCanonical := hLeft childQ childResidual hChildRelated
      have hChild :
          computeFuture leftExecution childQ =
              typeFutureOffers childResidual ∧
            ((∃ completed ∈ leftExecution.futureReachable childQ,
                  completed ∈ leftFragment.accepting ∨
                    completed ∈ leftFragment.completing) ↔
              childResidual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftExecution,
          leftFragment, hLeftStable] using hChildCanonical
      have hParentState : (.child 0 childQ : TypeAutomatonState) ∈
          parentExecution.states := by
        exact Finset.mem_union_left _ (by
          simp [parentFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState, hLeftState,
            hNotDeleted])
      have hShadowState : (.child 0 childQ : TypeAutomatonState) ∈
          shadow.states := by
        simp [shadow, shadowFragment, buildSequenceAutomaton,
          finishAutomatonFragment, childStates, childState, hLeftState,
          hNotDeleted]
      have hSameFuture := computeFuture_eq_of_same_edges parentExecution
        shadow hEdges hParentClosed hShadowClosed (.child 0 childQ)
          hParentState hShadowState
      have hSameReach := PendingAutomaton.futureReachable_eq_of_same_edges
        parentExecution shadow hEdges hParentClosed hShadowClosed
          (.child 0 childQ) hParentState hShadowState
      let canBridge := ∃ completed ∈ leftExecution.futureReachable childQ,
        completed ∈ leftFragment.accepting ∨
          completed ∈ leftFragment.completing
      have hBridgeIff : canBridge ↔
          childResidual.CanCompleteBeforeTock = true := by
        simpa [canBridge] using hChild.2
      have hFormula := buildSequenceAutomaton_computeFuture_left_formula
        signature leftFragment rightExecutionFragment childQ hLeftState
          hNotDeleted hLeftTargets hRightExecutionTargets
          hRightExecutionInitial
      have hShadowFuture : computeFuture shadow (.child 0 childQ) =
          typeFutureOffers (.seq childResidual right) := by
        have hFormula' : computeFuture shadow (.child 0 childQ) =
            computeFuture leftExecution childQ ∪
              if canBridge then
                computeFuture rightExecution rightFragment.initial else ∅ := by
          simpa [shadow, shadowFragment, rightExecutionFragment,
            leftExecution, rightExecution, canBridge,
            sequenceExecutionFragment] using hFormula
        rw [hFormula', hChild.1, hRightRoot.1,
          typeFutureOffers_sequence]
        by_cases hComplete : childResidual.CanCompleteBeforeTock = true
        · have hCanBridge := hBridgeIff.mpr hComplete
          simp [hComplete, hCanBridge]
        · have hCannotBridge : ¬ canBridge := fun h =>
            hComplete (hBridgeIff.mp h)
          simp [hComplete, hCannotBridge]
      constructor
      · exact hSameFuture.trans hShadowFuture
      · rw [hSameReach, hAccepting, hCompleting]
        have hWitness := buildSequenceAutomaton_completionWitness_left_iff
          signature leftFragment rightExecutionFragment childQ
            hLeftState hNotDeleted hLeftTargets hRightExecutionTargets
            hRightExecutionInitial
        refine hWitness.trans ((and_congr hChild.2 hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | sequence_left_progressed _ _ childResidual childQ hChildRelated
      hNotAccepting =>
      have hLeftStateCanonical := compilationStateCorrect_of_compilation
        signature left childQ childResidual hChildRelated
      have hLeftState : childQ ∈ leftFragment.states := by
        simpa [leftFragment, hLeftStable] using hLeftStateCanonical
      have hNotDeleted : childQ ∉ sequenceDeleted leftFragment := by
        apply not_mem_sequenceDeleted_of_not_accepting
        intro hAccepting
        have hAcceptingCanonical : childQ ∈ (compileTypeFuel signature
            (typeCompilationFuel left) left).accepting := by
          simpa [leftFragment, hLeftStable] using hAccepting
        exact hNotAccepting
          ((compilationAcceptingCorrect_of_compilation signature left)
            childQ childResidual hChildRelated |>.mp hAcceptingCanonical)
      have hChildCanonical := hLeft childQ childResidual hChildRelated
      have hChild :
          computeFuture leftExecution childQ =
              typeFutureOffers childResidual ∧
            ((∃ completed ∈ leftExecution.futureReachable childQ,
                  completed ∈ leftFragment.accepting ∨
                    completed ∈ leftFragment.completing) ↔
              childResidual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, leftExecution,
          leftFragment, hLeftStable] using hChildCanonical
      have hParentState : (.child 0 childQ : TypeAutomatonState) ∈
          parentExecution.states := by
        exact Finset.mem_union_left _ (by
          simp [parentFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState, hLeftState,
            hNotDeleted])
      have hShadowState : (.child 0 childQ : TypeAutomatonState) ∈
          shadow.states := by
        simp [shadow, shadowFragment, buildSequenceAutomaton,
          finishAutomatonFragment, childStates, childState, hLeftState,
          hNotDeleted]
      have hSameFuture := computeFuture_eq_of_same_edges parentExecution
        shadow hEdges hParentClosed hShadowClosed (.child 0 childQ)
          hParentState hShadowState
      have hSameReach := PendingAutomaton.futureReachable_eq_of_same_edges
        parentExecution shadow hEdges hParentClosed hShadowClosed
          (.child 0 childQ) hParentState hShadowState
      let canBridge := ∃ completed ∈ leftExecution.futureReachable childQ,
        completed ∈ leftFragment.accepting ∨
          completed ∈ leftFragment.completing
      have hBridgeIff : canBridge ↔
          childResidual.CanCompleteBeforeTock = true := by
        simpa [canBridge] using hChild.2
      have hFormula := buildSequenceAutomaton_computeFuture_left_formula
        signature leftFragment rightExecutionFragment childQ hLeftState
          hNotDeleted hLeftTargets hRightExecutionTargets
          hRightExecutionInitial
      have hShadowFuture : computeFuture shadow (.child 0 childQ) =
          typeFutureOffers (.seq childResidual right) := by
        have hFormula' : computeFuture shadow (.child 0 childQ) =
            computeFuture leftExecution childQ ∪
              if canBridge then
                computeFuture rightExecution rightFragment.initial else ∅ := by
          simpa [shadow, shadowFragment, rightExecutionFragment,
            leftExecution, rightExecution, canBridge,
            sequenceExecutionFragment] using hFormula
        rw [hFormula', hChild.1, hRightRoot.1,
          typeFutureOffers_sequence]
        by_cases hComplete : childResidual.CanCompleteBeforeTock = true
        · have hCanBridge := hBridgeIff.mpr hComplete
          simp [hComplete, hCanBridge]
        · have hCannotBridge : ¬ canBridge := fun h =>
            hComplete (hBridgeIff.mp h)
          simp [hComplete, hCannotBridge]
      constructor
      · exact hSameFuture.trans hShadowFuture
      · rw [hSameReach, hAccepting, hCompleting]
        have hWitness := buildSequenceAutomaton_completionWitness_left_iff
          signature leftFragment rightExecutionFragment childQ
            hLeftState hNotDeleted hLeftTargets hRightExecutionTargets
            hRightExecutionInitial
        refine hWitness.trans ((and_congr hChild.2 hRightRoot.2).trans ?_)
        simp [PactType.CanCompleteBeforeTock]
  | sequence_right _ _ _ childQ hChildRelated =>
      have hRightStateCanonical := compilationStateCorrect_of_compilation
        signature right childQ residual hChildRelated
      have hRightState : childQ ∈ rightFragment.states := by
        simpa [rightFragment, hRightStable] using hRightStateCanonical
      have hRightExecutionState : childQ ∈ rightExecution.states := by
        exact Finset.mem_union_left _ hRightState
      have hChildCanonical := hRight childQ residual hChildRelated
      have hChild :
          computeFuture rightExecution childQ =
              typeFutureOffers residual ∧
            ((∃ completed ∈ rightExecution.futureReachable childQ,
                  completed ∈ rightFragment.accepting ∨
                    completed ∈ rightFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, rightExecution,
          rightFragment, hRightStable] using hChildCanonical
      have hParentState : (.child 1 childQ : TypeAutomatonState) ∈
          parentExecution.states := by
        exact Finset.mem_union_left _ (by
          simp [parentFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState, hRightState])
      have hShadowState : (.child 1 childQ : TypeAutomatonState) ∈
          shadow.states := by
        simp [shadow, shadowFragment, rightExecutionFragment,
          sequenceExecutionFragment, buildSequenceAutomaton,
          finishAutomatonFragment, childStates, childState,
          rightExecution, hRightExecutionState]
      have hSameFuture := computeFuture_eq_of_same_edges parentExecution
        shadow hEdges hParentClosed hShadowClosed (.child 1 childQ)
          hParentState hShadowState
      have hSameReach := PendingAutomaton.futureReachable_eq_of_same_edges
        parentExecution shadow hEdges hParentClosed hShadowClosed
          (.child 1 childQ) hParentState hShadowState
      have hRightCard : rightExecution.states.card ≤ shadow.states.card := by
        have hSubset : rightExecution.states.image (.child 1) ⊆
            shadow.states := by
          intro tagged hTagged
          rcases Finset.mem_image.mp hTagged with ⟨child, hState, rfl⟩
          simp [shadow, shadowFragment, rightExecutionFragment,
            sequenceExecutionFragment, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState,
            rightExecution, hState]
        calc
          rightExecution.states.card =
              (rightExecution.states.image (.child 1)).card := by
            symm
            apply Finset.card_image_of_injective
            intro first second hEqual
            injection hEqual
          _ ≤ shadow.states.card := Finset.card_le_card hSubset
      have hShadowFuture : computeFuture shadow (.child 1 childQ) =
          computeFuture rightExecution childQ := by
        exact buildSequenceAutomaton_computeFuture_right signature
          leftFragment rightExecutionFragment childQ
            (sequenceExecutionAutomaton_referencesClosed rightFragment
              hRightTargets) hRightExecutionState hRightCard
      have hShadowReach : shadow.futureReachable (.child 1 childQ) =
          (rightExecution.futureReachable childQ).image (.child 1) := by
        exact PendingAutomaton.futureReachable_eq_of_embedding rightExecution
          shadow (.child 1)
            (buildSequenceAutomaton_referencedStates_right signature
              leftFragment rightExecutionFragment)
            (sequenceExecutionAutomaton_referencesClosed rightFragment
              hRightTargets) childQ hRightExecutionState hRightCard
      constructor
      · exact hSameFuture.trans (hShadowFuture.trans hChild.1)
      · rw [hSameReach, hShadowReach, hAccepting, hCompleting]
        exact (buildSequenceAutomaton_completionWitness_right_iff signature
          leftFragment rightExecutionFragment
            (rightExecution.futureReachable childQ)).trans hChild.2

end

end Pact
