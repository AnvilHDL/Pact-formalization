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
  intro residual residual' state env label offers hRelated hLocalEnvironment
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
          hLocalEnvironment, conditions.2.1, conditions.2.2]
  · rintro ⟨state', hEdge, hTarget⟩
    cases hTarget
    rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
      hTarget⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hEdge
    obtain ⟨edgeEnv, ⟨hLocalMem, hClock, hImmediate⟩, rfl⟩ := hEdge
    simp only at hEnv hLabel hCurrent hFuture
    subst hEnv
    injection hLabel with hLabel
    subst hLabel
    subst hCurrent
    subst hFuture
    exact ⟨TypeTransition.skip edgeEnv ⟨hWellFormed, hClock, hImmediate⟩,
      TypeOffers.skip edgeEnv ⟨hWellFormed, hClock, hImmediate⟩⟩

theorem compilationFragmentStepCorrect_message_leaf
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFragmentStepCorrect signature (.message msg dir) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
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
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
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
              hLocalEnvironment, conditions.2.1, conditions.2.2]
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
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock, hImmediate⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock, hImmediate⟩⟩

theorem compilationFragmentStepCorrect_tock_leaf
    (signature : TypeAlphabet) :
    CompilationFragmentStepCorrect signature .tock := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
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
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
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
              hLocalEnvironment, conditions.2.1, conditions.2.2]
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
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock, hImmediate⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock, hImmediate⟩⟩

theorem compilationFragmentStepCorrect_progress_leaf
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFragmentStepCorrect signature (.progress pid) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
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
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
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
              hLocalEnvironment, conditions.2.1, conditions.2.2]
      · rintro ⟨state', hEdge, hTarget⟩
        rcases hEdge with ⟨edge, hEdge, hSource, hEnv, hLabel, hCurrent, hFuture,
          hTargetField⟩
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with hAction | hFinal
        · obtain ⟨edgeEnv, hLocalMem, rfl⟩ := hAction
          simp only at hSource
          simp at hSource
        · obtain ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩ := hFinal
          simp only at hSource hEnv hLabel hCurrent hFuture hTargetField
          subst hEnv
          injection hLabel with hLabel
          subst hLabel
          subst hCurrent
          subst hFuture
          subst hTargetField
          cases hTarget
          exact ⟨TypeTransition.skip edgeEnv
              ⟨hWellFormed, hClock, hImmediate⟩,
            TypeOffers.skip edgeEnv ⟨hWellFormed, hClock, hImmediate⟩⟩

theorem compileTypeFuel_choiceLike_root_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState}
    (hEdge : AutomatonFragment.HasResolvedEdge
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
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
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
  have hFields :=
    (buildChoiceAutomaton_root_hasResolvedEdge_iff signature leftFragment
      rightFragment selectionLeft selectionRight environment label offers
      target).mp (by simpa [fuel, leftFragment, rightFragment] using hEdge)
  rcases hFields with hSelected | hSelected
  · left
    simpa [hLeftStable] using hSelected.2.2.2.2
  · right
    simpa [hRightStable] using hSelected.2.2.2.2

theorem compileTypeFuel_choiceLike_left_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 0 source) environment label offers target) :
    ∃ childTarget,
      target = .child 0 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel left) left)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hLeftStable : leftFragment = compileTypeFuel signature
      (typeCompilationFuel left) left :=
    compileTypeFuel_eq_of_sufficient signature left hLeftFuel
      (typeCompilationFuel_sufficient left)
  have hTargets : leftFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel left hLeftFuel
  have hParent : fragment.HasResolvedEdge (.child 0 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_left signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 0 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 0 source) environment label
      offers (.child 0 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 0 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_left_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hLeftStable] using hChild⟩

theorem compileTypeFuel_choiceLike_right_target_cases
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    {source target : TypeAutomatonState} {environment : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : AutomatonFragment.HasResolvedEdge
      (buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        selectionLeft selectionRight)
      (.child 1 source) environment label offers target) :
    ∃ childTarget,
      target = .child 1 childTarget ∧
        AutomatonFragment.HasResolvedEdge
          (compileTypeFuel signature (typeCompilationFuel right) right)
          source environment label offers childTarget := by
  let fuel := max (typeCompilationFuel left) (typeCompilationFuel right)
  let leftFragment := compileTypeFuel signature fuel left
  let rightFragment := compileTypeFuel signature fuel right
  let fragment := buildChoiceAutomaton signature leftFragment rightFragment
    selectionLeft selectionRight
  have hRightFuel : TypeCompilationFuelSufficient right fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hRightStable : rightFragment = compileTypeFuel signature
      (typeCompilationFuel right) right :=
    compileTypeFuel_eq_of_sufficient signature right hRightFuel
      (typeCompilationFuel_sufficient right)
  have hTargets : rightFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel right hRightFuel
  have hParent : fragment.HasResolvedEdge (.child 1 source) environment label
      offers target := by
    simpa [fragment, fuel, leftFragment, rightFragment] using hEdge
  rcases hParent with ⟨pending, hPending, hSource, hEnvironment, hLabel,
    hCurrent, hFuture, hTarget⟩
  rcases (buildChoiceAutomaton_outgoing_right signature leftFragment
      rightFragment selectionLeft selectionRight source pending).mp
      ⟨hPending, hSource⟩ with
    ⟨childEdge, hChildEdge, hChildSource, hPendingEq⟩
  have hTargetEq : target = .child 1 childEdge.target := by
    rw [hPendingEq] at hTarget
    simpa [childPendingEdge, childState] using hTarget.symm
  have hFixed : fragment.HasResolvedEdge (.child 1 source) environment label
      offers (.child 1 childEdge.target) := by
    simpa [hTargetEq] using (show fragment.HasResolvedEdge
      (.child 1 source) environment label offers target from
        ⟨pending, hPending, hSource, hEnvironment, hLabel, hCurrent,
          hFuture, hTarget⟩)
  have hChild :=
    (buildChoiceAutomaton_hasResolvedEdge_right_iff signature leftFragment
      rightFragment selectionLeft selectionRight source childEdge.target
      environment label offers hTargets).mp hFixed
  exact ⟨childEdge.target, hTargetEq, by simpa [hRightStable] using hChild⟩

theorem compilationFragmentStepCorrect_choice_leaf
    (signature : TypeAlphabet) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature (.choice left right) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsLeft : env.AvoidsInterface left.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  have hAvoidsRight : env.AvoidsInterface right.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  rcases offers with ⟨current, future⟩
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  have hChoiceFuture := choiceFutureCorrect_of_compilation signature left right
    hLeft.future hRight.future
  have hFragmentEq :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
          (.choice left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
          (compileTypeFuel signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
          TypeLabel.silent TypeLabel.silent := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  cases hRelated with
  | choice_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | choice_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_left_fields hOffers
            refine ⟨.child 0 (compileTypeFuel signature
                (typeCompilationFuel left) left).initial, ?_, ?_⟩
            · show AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature (typeCompilationFuel (.choice left right))
                  (.choice left right)) .root env TypeLabel.silent
                { current := ∅, future := typeFutureOffers left }
                (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                  left).initial)
              rw [hFragmentEq]
              apply (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                TypeLabel.silent TypeLabel.silent env TypeLabel.silent
                { current := ∅, future := typeFutureOffers left }
                (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                  left).initial)).mpr
              left
              have hFuel : TypeCompilationFuelSufficient left
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
                simp [TypeCompilationFuelSufficient]
              have hStable := compileTypeFuel_eq_of_sufficient signature left
                hFuel (typeCompilationFuel_sufficient left)
              exact ⟨hLocalEnvironment, rfl, rfl, hChoiceFuture.1, by rw [hStable]⟩
            · exact TypeCompilationRelation.choice_left left right left _
                (compileType_initial_relation signature left)
        | choice_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.choice_right_fields hOffers
            refine ⟨.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial, ?_, ?_⟩
            · show AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature (typeCompilationFuel (.choice left right))
                  (.choice left right)) .root env TypeLabel.silent
                { current := ∅, future := typeFutureOffers right }
                (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                  right).initial)
              rw [hFragmentEq]
              apply (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                TypeLabel.silent TypeLabel.silent env TypeLabel.silent
                { current := ∅, future := typeFutureOffers right }
                (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                  right).initial)).mpr
              right
              have hFuel : TypeCompilationFuelSufficient right
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
                simp [TypeCompilationFuelSufficient]
              have hStable := compileTypeFuel_eq_of_sufficient signature right
                hFuel (typeCompilationFuel_sufficient right)
              exact ⟨hLocalEnvironment, rfl, rfl, hChoiceFuture.2, by rw [hStable]⟩
            · exact TypeCompilationRelation.choice_right left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent)
            .root env label { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        have hFields := (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent env label
            { current := current, future := future } target).mp hEdge'
        rcases hFields with hLeftSel | hRightSel
        · obtain ⟨_, hLabel, hCurrent, hComputed, hTargetEq⟩ := hLeftSel

          subst hLabel
          subst hCurrent
          have hFuel : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature left
            hFuel (typeCompilationFuel_sufficient left)
          rw [hStable] at hTargetEq
          simp only at hComputed
          have hFutureEq : future = typeFutureOffers left := by
            rw [← hComputed]; simpa using hChoiceFuture.1
          subst hFutureEq
          subst hTargetEq
          cases hTarget with
          | choice_left _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.choice_left env left right hWellFormed,
                TypeOffers.choice_left env left right hWellFormed⟩
        · obtain ⟨_, hLabel, hCurrent, hComputed, hTargetEq⟩ := hRightSel
          subst hLabel
          subst hCurrent
          have hFuel : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature right
            hFuel (typeCompilationFuel_sufficient right)
          rw [hStable] at hTargetEq
          simp only at hComputed
          have hFutureEq : future = typeFutureOffers right := by
            rw [← hComputed]; simpa using hChoiceFuture.2
          subst hFutureEq
          subst hTargetEq
          cases hTarget with
          | choice_right _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.choice_right env left right hWellFormed,
                TypeOffers.choice_right env left right hWellFormed⟩
  | choice_left _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hLeft.scopedStep (residual' := residual') (label := label)
            (offers := { current := current, future := future })
            hChildRelated hLocalEnvironment hAvoidsLeft).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · show AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel (.choice left right))
              (.choice left right)) (.child 0 childState) env label
            { current := current, future := future } (.child 0 childTarget)
          rw [hFragmentEq]
          have hFuel : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hTargets := compileTypeFuel_futureTargetsInStates signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) left hFuel
          apply (buildChoiceAutomaton_hasResolvedEdge_left_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent childState childTarget env label
            { current := current, future := future } hTargets).mpr
          have hStable := compileTypeFuel_eq_of_sufficient signature left
            hFuel (typeCompilationFuel_sufficient left)
          rw [hStable]
          exact hChildEdge
        · exact TypeCompilationRelation.choice_left left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent)
            (.child 0 childState) env label
            { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        obtain ⟨childTarget, rfl, hChildEdge⟩ :=
          compileTypeFuel_choiceLike_left_target_cases signature left right
            TypeLabel.silent TypeLabel.silent hEdge'
        cases hTarget with
        | choice_left _ _ _ _ hChildTarget =>
            exact (hLeft.scopedStep (residual' := residual') (label := label)
              (offers := { current := current, future := future })
              hChildRelated hLocalEnvironment hAvoidsLeft).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | choice_right _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hRight.scopedStep (residual' := residual') (label := label)
            (offers := { current := current, future := future })
            hChildRelated hLocalEnvironment hAvoidsRight).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · show AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature (typeCompilationFuel (.choice left right))
              (.choice left right)) (.child 1 childState) env label
            { current := current, future := future } (.child 1 childTarget)
          rw [hFragmentEq]
          have hFuelR : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hTargets := compileTypeFuel_futureTargetsInStates signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) right hFuelR
          apply (buildChoiceAutomaton_hasResolvedEdge_right_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent childState childTarget env label
            { current := current, future := future } hTargets).mpr
          have hFuel : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature right
            hFuel (typeCompilationFuel_sufficient right)
          rw [hStable]
          exact hChildEdge
        · exact TypeCompilationRelation.choice_right left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              TypeLabel.silent TypeLabel.silent)
            (.child 1 childState) env label
            { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        obtain ⟨childTarget, rfl, hChildEdge⟩ :=
          compileTypeFuel_choiceLike_right_target_cases signature left right
            TypeLabel.silent TypeLabel.silent hEdge'
        cases hTarget with
        | choice_right _ _ _ _ hChildTarget =>
            exact (hRight.scopedStep (residual' := residual') (label := label)
              (offers := { current := current, future := future })
              hChildRelated hLocalEnvironment hAvoidsRight).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

theorem compilationFragmentStepCorrect_fairChoice_leaf
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeft : CompilationProofBundle signature left)
    (hRight : CompilationProofBundle signature right) :
    CompilationScopedFragmentStepCorrect signature
      (.fairChoice bid left right) := by
  intro residual residual' state env label offers hRelated hLocalEnvironment
    hAvoids
  have hAvoidsLeft : env.AvoidsInterface left.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  have hAvoidsRight : env.AvoidsInterface right.ParallelInterfaces :=
    hAvoids.mono (by simp [PactType.ParallelInterfaces])
  rcases offers with ⟨current, future⟩
  have hWellFormed := TypeAlphabet.localEnvironment_wellFormed hLocalEnvironment
  have hFairFuture := fairChoiceFutureCorrect_of_compilation signature bid left
    right hLeft.future hRight.future
  have hFragmentEq :
      compileTypeFuel signature
          (typeCompilationFuel (.fairChoice bid left right))
          (.fairChoice bid left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
          (compileTypeFuel signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
  cases hRelated with
  | fair_source =>
      constructor
      · rintro ⟨hTransition, hOffers⟩
        cases hTransition with
        | fair_left =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_left_fields hOffers
            refine ⟨.child 0 (compileTypeFuel signature
                (typeCompilationFuel left) left).initial, ?_, ?_⟩
            · show AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature
                  (typeCompilationFuel (.fairChoice bid left right))
                  (.fairChoice bid left right)) .root env (TypeLabel.fair bid true)
                { current := ∅, future := typeFutureOffers left }
                (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                  left).initial)
              rw [hFragmentEq]
              apply (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) env
                (TypeLabel.fair bid true)
                { current := ∅, future := typeFutureOffers left }
                (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                  left).initial)).mpr
              left
              have hFuel : TypeCompilationFuelSufficient left
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
                simp [TypeCompilationFuelSufficient]
              have hStable := compileTypeFuel_eq_of_sufficient signature left
                hFuel (typeCompilationFuel_sufficient left)
              exact ⟨hLocalEnvironment, rfl, rfl, hFairFuture.1, by rw [hStable]⟩
            · exact TypeCompilationRelation.fair_left bid left right left _
                (compileType_initial_relation signature left)
        | fair_right =>
            obtain ⟨rfl, rfl⟩ := TypeOffers.fair_right_fields hOffers
            refine ⟨.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial, ?_, ?_⟩
            · show AutomatonFragment.HasResolvedEdge
                (compileTypeFuel signature
                  (typeCompilationFuel (.fairChoice bid left right))
                  (.fairChoice bid left right)) .root env
                (TypeLabel.fair bid false)
                { current := ∅, future := typeFutureOffers right }
                (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                  right).initial)
              rw [hFragmentEq]
              apply (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
                (compileTypeFuel signature
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
                (TypeLabel.fair bid true) (TypeLabel.fair bid false) env
                (TypeLabel.fair bid false)
                { current := ∅, future := typeFutureOffers right }
                (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                  right).initial)).mpr
              right
              have hFuel : TypeCompilationFuelSufficient right
                  (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
                simp [TypeCompilationFuelSufficient]
              have hStable := compileTypeFuel_eq_of_sufficient signature right
                hFuel (typeCompilationFuel_sufficient right)
              exact ⟨hLocalEnvironment, rfl, rfl, hFairFuture.2, by rw [hStable]⟩
            · exact TypeCompilationRelation.fair_right bid left right right _
                (compileType_initial_relation signature right)
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false))
            .root env label { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        have hFields := (buildChoiceAutomaton_root_hasResolvedEdge_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) env label
            { current := current, future := future } target).mp hEdge'
        rcases hFields with hLeftSel | hRightSel
        · obtain ⟨_, hLabel, hCurrent, hComputed, hTargetEq⟩ := hLeftSel
          subst hLabel
          subst hCurrent
          have hFuel : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature left
            hFuel (typeCompilationFuel_sufficient left)
          rw [hStable] at hTargetEq
          simp only at hComputed
          have hFutureEq : future = typeFutureOffers left := by
            rw [← hComputed]; simpa using hFairFuture.1
          subst hFutureEq
          subst hTargetEq
          cases hTarget with
          | fair_left _ _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature left)
              cases hResidual
              exact ⟨TypeTransition.fair_left env bid left right hWellFormed,
                TypeOffers.fair_left env bid left right hWellFormed⟩
        · obtain ⟨_, hLabel, hCurrent, hComputed, hTargetEq⟩ := hRightSel
          subst hLabel
          subst hCurrent
          have hFuel : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature right
            hFuel (typeCompilationFuel_sufficient right)
          rw [hStable] at hTargetEq
          simp only at hComputed
          have hFutureEq : future = typeFutureOffers right := by
            rw [← hComputed]; simpa using hFairFuture.2
          subst hFutureEq
          subst hTargetEq
          cases hTarget with
          | fair_right _ _ _ _ _ hChildTarget =>
              have hResidual := TypeCompilationRelation.residual_unique
                hChildTarget (compileType_initial_relation signature right)
              cases hResidual
              exact ⟨TypeTransition.fair_right env bid left right hWellFormed,
                TypeOffers.fair_right env bid left right hWellFormed⟩
  | fair_left _ _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hLeft.scopedStep (residual' := residual') (label := label)
            (offers := { current := current, future := future })
            hChildRelated hLocalEnvironment hAvoidsLeft).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 0 childTarget, ?_, ?_⟩
        · show AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature
              (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right)) (.child 0 childState) env label
            { current := current, future := future } (.child 0 childTarget)
          rw [hFragmentEq]
          have hFuel : TypeCompilationFuelSufficient left
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hTargets := compileTypeFuel_futureTargetsInStates signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) left hFuel
          apply (buildChoiceAutomaton_hasResolvedEdge_left_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) childState
            childTarget env label
            { current := current, future := future } hTargets).mpr
          have hStable := compileTypeFuel_eq_of_sufficient signature left
            hFuel (typeCompilationFuel_sufficient left)
          rw [hStable]
          exact hChildEdge
        · exact TypeCompilationRelation.fair_left bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false))
            (.child 0 childState) env label
            { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        obtain ⟨childTarget, rfl, hChildEdge⟩ :=
          compileTypeFuel_choiceLike_left_target_cases signature left right
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) hEdge'
        cases hTarget with
        | fair_left _ _ _ _ _ hChildTarget =>
            exact (hLeft.scopedStep (residual' := residual') (label := label)
              (offers := { current := current, future := future })
              hChildRelated hLocalEnvironment hAvoidsLeft).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩
  | fair_right _ _ _ childResidual childState hChildRelated =>
      constructor
      · intro hStep
        rcases (hRight.scopedStep (residual' := residual') (label := label)
            (offers := { current := current, future := future })
            hChildRelated hLocalEnvironment hAvoidsRight).mp hStep with
          ⟨childTarget, hChildEdge, hChildTarget⟩
        refine ⟨.child 1 childTarget, ?_, ?_⟩
        · show AutomatonFragment.HasResolvedEdge
            (compileTypeFuel signature
              (typeCompilationFuel (.fairChoice bid left right))
              (.fairChoice bid left right)) (.child 1 childState) env label
            { current := current, future := future } (.child 1 childTarget)
          rw [hFragmentEq]
          have hFuelR : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hTargets := compileTypeFuel_futureTargetsInStates signature
            (max (typeCompilationFuel left) (typeCompilationFuel right)) right hFuelR
          apply (buildChoiceAutomaton_hasResolvedEdge_right_iff signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) childState
            childTarget env label
            { current := current, future := future } hTargets).mpr
          have hFuel : TypeCompilationFuelSufficient right
              (max (typeCompilationFuel left) (typeCompilationFuel right)) := by
            simp [TypeCompilationFuelSufficient]
          have hStable := compileTypeFuel_eq_of_sufficient signature right
            hFuel (typeCompilationFuel_sufficient right)
          rw [hStable]
          exact hChildEdge
        · exact TypeCompilationRelation.fair_right bid left right residual'
            childTarget hChildTarget
      · rintro ⟨target, hEdge, hTarget⟩
        have hEdge' : AutomatonFragment.HasResolvedEdge
            (buildChoiceAutomaton signature
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
              (compileTypeFuel signature
                (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false))
            (.child 1 childState) env label
            { current := current, future := future } target := by
          rw [← hFragmentEq]; exact hEdge
        obtain ⟨childTarget, rfl, hChildEdge⟩ :=
          compileTypeFuel_choiceLike_right_target_cases signature left right
            (TypeLabel.fair bid true) (TypeLabel.fair bid false) hEdge'
        cases hTarget with
        | fair_right _ _ _ _ _ hChildTarget =>
            exact (hRight.scopedStep (residual' := residual') (label := label)
              (offers := { current := current, future := future })
              hChildRelated hLocalEnvironment hAvoidsRight).mpr
              ⟨childTarget, hChildEdge, hChildTarget⟩

end

end Pact
