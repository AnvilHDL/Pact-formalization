import Anvilpp.PactTypes.Correspondence.CorrespondenceSequenceExecutionLeaves

/-!
# CompilationFragmentStepCorrect leaves: skip/message/tock/progress/choice/fairChoice
-/

namespace Pact

noncomputable section

/- The following raw atomic/selection obligations are deliberately exposed as
small leaves.  Their public counterparts and all edge classifications are
already proved above; these leaves only remove the public alphabet filter. -/
theorem compilationFragmentStepCorrect_skip_leaf
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .skip := by
  intro _ residual residual' state env label offers hRelated hLocalEnvironment
  cases hRelated
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  rcases offers with ⟨current, future⟩
  constructor
  · rintro ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
        refine ⟨.root, ?_, TypeCompilationRelation.skip⟩
        refine ⟨
          { source := .root
            environment := env
            label := .visible TypeLabel.silent
            current := ∅
            future := .explicit ∅
            target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          hLocalEnvironment, conditions.2]
  · rintro ⟨state', hEdge, hTarget⟩
    cases hTarget
    rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
      hTarget⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hEdge
    obtain ⟨edgeEnv, ⟨hLocalMem, hClock⟩, rfl⟩ := hEdge
    simp only at hEnv hLabel hCurrent hFuture
    subst hEnv
    injection hLabel with hLabel
    subst hLabel
    subst hCurrent
    subst hFuture
    exact ⟨TypeTransition.skip edgeEnv ⟨hWellFormed, hClock⟩,
      TypeOffers.skip edgeEnv ⟨hWellFormed, hClock⟩⟩

theorem compilationFragmentStepCorrect_message_leaf
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFragmentStepCorrect signature (.message msg dir) := by
  intro _ residual residual' state env label offers hRelated hLocalEnvironment
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | message_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | action _ _ _ conditions =>
            have hFields : current = {(msg, dir)} ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.message msg dir = actualLabel
                at hOffers
              cases hOffers <;>
                simp_all [typeFutureOffers, typeFutureOffersFuel, Finset.ext_iff]
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible (TypeLabel.message msg dir)
                current := {(msg, dir)}
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment, conditions.2]
        | action_wait _ _ _ conditions =>
            have hFields : current = {(msg, dir)} ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
              cases hOffers <;>
                simp_all [typeFutureOffers, typeFutureOffersFuel, Finset.ext_iff]
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.root, ?_, TypeCompilationRelation.message_source msg dir⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.silent
                current := {(msg, dir)}
                future := .explicit ∅
                target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment, conditions.2.1, conditions.2.2]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
          at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · obtain ⟨edgeEnv, ⟨_, hNeed⟩, rfl⟩ := hFiring
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.action edgeEnv msg dir
              ⟨hWellFormed, hNeed⟩,
            by simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action edgeEnv msg dir ⟨hWellFormed, hNeed⟩⟩
        · obtain ⟨edgeEnv, ⟨_, hClock, hNoNeed⟩, rfl⟩ := hWaiting
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.action_wait edgeEnv msg dir
              ⟨hWellFormed, hNoNeed, hClock⟩,
            by simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action_wait edgeEnv msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩⟩
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource
          simp at hSource
  | message_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            cases hOffers with
            | skip _ _ =>
            refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment, conditions.2]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
          at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · obtain ⟨edgeEnv, ⟨_, hNeed⟩, rfl⟩ := hFiring
          simp only at hSource
          simp at hSource
        · obtain ⟨edgeEnv, ⟨_, hClock, hNoNeed⟩, rfl⟩ := hWaiting
          simp only at hSource
          simp at hSource
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock⟩⟩

theorem compilationFragmentStepCorrect_tock_leaf
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .tock := by
  intro _ residual residual' state env label offers hRelated hLocalEnvironment
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | cycle_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | cycle _ conditions =>
            have hFields : current = ∅ ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.tock = actualLabel at hOffers
              cases hOffers <;> simp_all
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.tock
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp only [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            left
            exact ⟨env, hLocalEnvironment, by simp [conditions.2]⟩
        | cycle_wait _ conditions =>
            have hFields : current = ∅ ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
              cases hOffers <;> simp_all
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.root, ?_, TypeCompilationRelation.cycle_source⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .root }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp only [typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
            left
            exact ⟨env, hLocalEnvironment, by simp [conditions.2]⟩
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with hAction | hFinal
        · obtain ⟨edgeEnv, hLocalMem, hEdgeEq⟩ := hAction
          by_cases hClock : edgeEnv.clock = true
          · rw [if_pos hClock] at hEdgeEq
            rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTargetField
            simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
            subst hEnv
            injection hLabel with hLabel
            subst hLabel
            subst hCurrent
            subst hFuture
            subst hTargetField
            cases hTarget
            exact ⟨TypeTransition.cycle edgeEnv ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle edgeEnv ⟨hWellFormed, hClock⟩⟩
          · rw [if_neg hClock] at hEdgeEq
            rw [← hEdgeEq] at hSource hEnv hLabel hCurrent hFuture hTargetField
            simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
            subst hEnv
            injection hLabel with hLabel
            subst hLabel
            subst hCurrent
            subst hFuture
            subst hTargetField
            cases hTarget
            exact ⟨TypeTransition.cycle_wait edgeEnv
                ⟨hWellFormed, by simpa using hClock⟩,
              TypeOffers.cycle_wait edgeEnv ⟨hWellFormed, by simpa using hClock⟩⟩
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource
          simp at hSource
  | cycle_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            have hFields : current = ∅ ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
              cases hOffers <;> simp_all
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment, conditions.2]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with hAction | hFinal
        · obtain ⟨edgeEnv, hLocalMem, hEdgeEq⟩ := hAction
          by_cases hClock : edgeEnv.clock = true
          · rw [if_pos hClock] at hEdgeEq
            rw [← hEdgeEq] at hSource
            simp at hSource
          · rw [if_neg hClock] at hEdgeEq
            rw [← hEdgeEq] at hSource
            simp at hSource
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock⟩⟩

theorem compilationFragmentStepCorrect_progress_leaf
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFragmentStepCorrect signature (.progress pid) := by
  intro _ residual residual' state env label offers hRelated hLocalEnvironment
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  rcases offers with ⟨current, future⟩
  cases hRelated with
  | progress_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | progress _ _ =>
            have hFields : current = ∅ ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.progress pid = actualLabel
                at hOffers
              cases hOffers <;> simp_all
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
            refine ⟨
              { source := .root
                environment := env
                label := .visible (TypeLabel.progress pid)
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with hAction | hFinal
        · obtain ⟨edgeEnv, hLocalMem, rfl⟩ := hAction
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.progress edgeEnv pid hWellFormed,
            TypeOffers.progress edgeEnv pid hWellFormed⟩
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource
          simp at hSource
  | progress_final =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | skip _ conditions =>
            have hFields : current = ∅ ∧ future = ∅ := by
              generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
              cases hOffers <;> simp_all
            obtain ⟨rfl, rfl⟩ := hFields
            refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
            refine ⟨
              { source := .final
                environment := env
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
            simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
              hLocalEnvironment, conditions.2]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with hAction | hFinal
        · obtain ⟨edgeEnv, hLocalMem, rfl⟩ := hAction
          simp only at hSource
          simp at hSource
        · obtain ⟨edgeEnv, ⟨_, hClock⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock⟩⟩

theorem compileTypeFuel_choiceLike_root_target_cases
    (signature : TypeAlphabet) (left right : PactType) (processType : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hEdge : AutomatonFragment.HasResolvedEdge signature processType
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      .root environment label offers target) :
    target = .child 0 (compileTypeFuel signature
        (typeCompilationFuel left) left).initial ∨
      target = .child 1 (compileTypeFuel signature
        (typeCompilationFuel right) right).initial := by
  sorry -- TODO(redevelopment): body called buildChoiceAutomaton_root_hasResolvedEdge_iff,
  -- deleted from CorrespondenceChoice.lean along with the old
  -- computeFuture-based classifier cluster; .

theorem compileTypeFuel_choiceLike_left_target_cases
    (signature : TypeAlphabet) (left right : PactType) (processType : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge signature processType
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 0 source) environment label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge signature left
          (compileTypeFuel signature (typeCompilationFuel left) left)
          source environment label offers childTarget := by
  sorry -- TODO(redevelopment): body called buildChoiceAutomaton_hasResolvedEdge_left_iff,
  -- deleted from CorrespondenceChoice.lean along with the old
  -- computeFuture-based classifier cluster; .

theorem compileTypeFuel_choiceLike_right_target_cases
    (signature : TypeAlphabet) (left right : PactType) (processType : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge signature processType
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 1 source) environment label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
        AutomatonFragment.HasResolvedEdge signature right
          (compileTypeFuel signature (typeCompilationFuel right) right)
          source environment label offers childTarget := by
  sorry -- TODO(redevelopment): body called buildChoiceAutomaton_hasResolvedEdge_right_iff,
  -- deleted from CorrespondenceChoice.lean along with the old
  -- computeFuture-based classifier cluster; .

theorem compilationFragmentStepCorrect_choice_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature (.choice left right) := by
  sorry -- TODO(redevelopment): body relied on the deleted
  -- buildChoiceAutomaton_*_hasResolvedEdge_* classifier cluster and old
  -- .HasResolvedEdge arities throughout; .
theorem compilationFragmentStepCorrect_fairChoice_leaf
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature
      (.fairChoice bid left right) := by
  sorry -- TODO(redevelopment): body relied on the deleted
  -- buildChoiceAutomaton_*_hasResolvedEdge_* classifier cluster and old
  -- .HasResolvedEdge arities throughout; .

end

end Pact
