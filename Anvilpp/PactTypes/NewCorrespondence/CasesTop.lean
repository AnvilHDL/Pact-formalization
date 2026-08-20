import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers

namespace Pact

open Classical

noncomputable section
/-- Step correspondence for the `skip` constructor, stated for the new
relation-set presentation used by `PactSafety.type_automaton_correspondence`.

This is the Section 7.2/Lemma 4.5 base case: the compiled `skip` automaton
has exactly the non-clock silent self-loop that the operational `skip` type
has, and no clock step. -/
theorem correspondence_skip_stepIff
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet .skip (compileType signature .skip))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ (compileType signature .skip).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature .skip).HasEdge state env label offers state' ∧
        relationMembership
          (buildRelationSet .skip (compileType signature .skip))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases relationMembership_skip_cases signature hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases hStep with ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
            have hEdge := compileType_skip_edge signature hLocal
              conditions.2 hSignatureSymbol
            exact ⟨.root, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases relationMembership_skip_cases signature hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases compileType_skip_edge_cases signature hEdge with
      ⟨_hSource, hTarget, hLabel, hCurrent, hFuture, hClock⟩
    subst label
    subst current
    subst future
    subst state'
    have hResidualTarget : residual' = .skip :=
      (relationMembership_skip_cases signature hTargetRelated).1
    subst residual'
    exact ⟨TypeTransition.skip env ⟨hWellFormed, hClock⟩,
      TypeOffers.skip env ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for an atomic message type `a`.

PDF structure, Lemma 4.5 atomic action case:
* related states: `q0` represents `a`, `qf` represents `skip`;
* forward at `q0`: if `Need(a)` is immediate, use the fire family to `qf`;
  otherwise in a non-clock environment use the waiting self-loop at `q0`;
* forward at `qf`: reduce to the `skip` idle case;
* backward: every public edge is in the fire, wait, or final-idle family, and
  its guard reconstructs the corresponding semantic rule. -/
theorem correspondence_message_stepIff
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.message msg dir)
          (compileType signature (.message msg dir)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.message msg dir)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.message msg dir)).HasEdge state env label
          offers state' ∧
        relationMembership
          (buildRelationSet (.message msg dir)
            (compileType signature (.message msg dir)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases relationMembership_message_cases signature msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | action _ _ _ conditions =>
          have hFields : current = {(msg, dir)} ∧ future = ∅ := by
            generalize hLabelEq :
              TypeLabel.message msg dir = actualLabel at hOffers
            cases hOffers
            all_goals simp_all [Finset.ext_iff]
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.message msg dir)
                (TypeLabel.message msg dir)
                (TypeOfferSummary.mk {(msg, dir)} ∅) .skip :=
            ⟨TypeTransition.action env msg dir conditions,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := compileType_message_action_edge signature msg dir
            hLocal conditions.2 hSignatureSymbol
          exact ⟨.final, hEdge,
            relationMembership_of_step_edge_unique (.message msg dir)
              (compileType signature (.message msg dir)) hRelated hEdge
              decorated (by
                intro target hTarget
                exact decorated_message_action_target hTarget)⟩
      | action_wait _ _ _ conditions =>
          have hFields : current = {(msg, dir)} ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
            cases hOffers
            all_goals simp_all [typeFutureOffers, typeFutureOffersFuel,
              Finset.ext_iff]
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.message msg dir)
                TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅)
                (.message msg dir) :=
            ⟨TypeTransition.action_wait env msg dir conditions,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := compileType_message_wait_edge signature msg dir
            hLocal conditions.2.1 conditions.2.2 hSignatureSymbol
          exact ⟨.root, hEdge,
            relationMembership_of_step_edge_unique (.message msg dir)
              (compileType signature (.message msg dir)) hRelated hEdge
              decorated (by
                intro target hTarget
                exact decorated_message_wait_target hTarget)⟩
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := compileType_message_final_edge signature msg dir
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases relationMembership_message_cases signature msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_message_edge_cases signature msg dir hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_message_cases signature msg dir
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.action env msg dir ⟨hWellFormed, hNeed⟩,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩⟩
      · rcases hWait with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock, hNoNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .message msg dir := by
          rcases relationMembership_message_cases signature msg dir
              hTargetRelated with hTargetRoot | hTargetFinal
          · exact hTargetRoot.1
          · rcases hTargetFinal with ⟨_, hStateTarget⟩
            simp at hStateTarget
        subst residual'
        exact ⟨TypeTransition.action_wait env msg dir
            ⟨hWellFormed, hNoNeed, hClock⟩,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action_wait env msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_message_edge_cases signature msg dir hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨hSource, _⟩
        simp at hSource
      · rcases hWait with ⟨hSource, _⟩
        simp at hSource
      · rcases hIdle with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_message_cases signature msg dir
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for the clock type `#`.

PDF structure, Lemma 4.5 clock case:
* related states: `q0` represents `#`, `qf` represents `skip`;
* clock environment: the semantic type emits `#` and the compiler fire edge
  reaches `qf`, with empty offer pair;
* non-clock environment: both semantics and automaton wait silently at `q0`;
* final state: both presentations use the non-clock idle behavior of `skip`;
* backward: the fire, wait, and idle edge families are exhaustive. -/
theorem correspondence_tock_stepIff
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet .tock (compileType signature .tock))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ (compileType signature .tock).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature .tock).HasEdge state env label offers state' ∧
        relationMembership
          (buildRelationSet .tock (compileType signature .tock))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases relationMembership_tock_cases signature hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | cycle _ conditions =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.tock = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env .tock TypeLabel.tock
                (TypeOfferSummary.mk ∅ ∅) .skip :=
            ⟨TypeTransition.cycle env conditions,
              TypeOffers.cycle env conditions⟩
          have hEdge := compileType_tock_action_edge signature hLocal
            conditions.2 hSignatureSymbol
          exact ⟨.final, hEdge,
            relationMembership_of_step_edge_unique .tock
              (compileType signature .tock) hRelated hEdge decorated (by
                intro target hTarget
                exact decorated_tock_action_target hTarget)⟩
      | cycle_wait _ conditions =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env .tock TypeLabel.silent
                (TypeOfferSummary.mk ∅ ∅) .tock :=
            ⟨TypeTransition.cycle_wait env conditions,
              TypeOffers.cycle_wait env conditions⟩
          have hEdge := compileType_tock_wait_edge signature hLocal
            conditions.2 hSignatureSymbol
          exact ⟨.root, hEdge,
            relationMembership_of_step_edge_unique .tock
              (compileType signature .tock) hRelated hEdge decorated (by
                intro target hTarget
                exact decorated_tock_wait_target hTarget)⟩
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := compileType_tock_final_edge signature hLocal
                conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases relationMembership_tock_cases signature hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_tock_edge_cases signature hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_tock_cases signature
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.cycle env ⟨hWellFormed, hClock⟩,
          TypeOffers.cycle env ⟨hWellFormed, hClock⟩⟩
      · rcases hWait with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .tock := by
          rcases relationMembership_tock_cases signature
              hTargetRelated with hTargetRoot | hTargetFinal
          · exact hTargetRoot.1
          · rcases hTargetFinal with ⟨_, hStateTarget⟩
            simp at hStateTarget
        subst residual'
        exact ⟨TypeTransition.cycle_wait env ⟨hWellFormed, hClock⟩,
          TypeOffers.cycle_wait env ⟨hWellFormed, hClock⟩⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_tock_edge_cases signature hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨hSource, _⟩
        simp at hSource
      · rcases hWait with ⟨hSource, _⟩
        simp at hSource
      · rcases hIdle with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_tock_cases signature
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for a progress marker `$t`.

PDF structure, Lemma 4.5 progress case:
* related states: `q0` represents `$t`, `qf` represents `skip`;
* forward at `q0`: the semantic progress step reaches `skip` with empty
  current and future offers, matching the compiler progress edge to `qf`;
* forward at `qf`: reduce to the `skip` idle case;
* backward: every public edge is either the progress family or the final idle
  family, and reconstructs the corresponding semantic step. -/
theorem correspondence_progress_stepIff
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.progress pid) (compileType signature (.progress pid)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.progress pid)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.progress pid)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.progress pid)
            (compileType signature (.progress pid)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases relationMembership_progress_cases signature pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | progress _ _ =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq :
              TypeLabel.progress pid = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.progress pid)
                (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .skip :=
            ⟨TypeTransition.progress env pid hWellFormed,
              TypeOffers.progress env pid hWellFormed⟩
          have hEdge := compileType_progress_action_edge signature pid
            hLocal hSignatureSymbol
          exact ⟨.final, hEdge,
            relationMembership_of_step_edge_unique (.progress pid)
              (compileType signature (.progress pid)) hRelated hEdge
              decorated (by
                intro target hTarget
                exact decorated_progress_target hTarget)⟩
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := compileType_progress_final_edge signature pid
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases relationMembership_progress_cases signature pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_progress_edge_cases signature pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨_hSource, hTarget, hLabel, hCurrent,
          hFuture⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_progress_cases signature pid
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.progress env pid hWellFormed,
          TypeOffers.progress env pid hWellFormed⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := compileType_progress_edge_cases signature pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨hSource, _⟩
        simp at hSource
      · rcases hIdle with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .skip := by
          rcases relationMembership_progress_cases signature pid
              hTargetRelated with hTargetRoot | hTargetFinal
          · rcases hTargetRoot with ⟨_, hStateTarget⟩
            simp at hStateTarget
          · exact hTargetFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env ⟨hWellFormed, hClock⟩⟩

end

end Pact
