import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers
import Anvilpp.PactSafetyHelpers
import Anvilpp.PactAdditionalSafetyHelpers

namespace Pact

open Classical
open Pact.NewCorrespondence

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
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_skip_cases signature hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases hStep with ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
            have hEdge := NewCorrespondence.compileType_skip_edge signature hLocal
              conditions.2 hSignatureSymbol
            exact ⟨.root, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_skip_cases signature hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases NewCorrespondence.compileType_skip_edge_cases signature hEdge with
      ⟨_hSource, hTarget, hLabel, hCurrent, hFuture, hClock⟩
    subst label
    subst current
    subst future
    subst state'
    have hTargetAccepting :
        TypeAutomatonState.root ∈ (compileType signature .skip).accepting := by
      simp [compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
    have hResidualTarget : residual' = .skip :=
      (helper_h13_final_states_represent_completion signature
        hTargetRelated).mp hTargetAccepting
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
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_message_cases signature msg dir
      hRelated with
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
          have hEdge := NewCorrespondence.compileType_message_action_edge
            signature msg dir
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
          have hEdge := NewCorrespondence.compileType_message_wait_edge
            signature msg dir
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
              have hEdge := NewCorrespondence.compileType_message_final_edge
                signature msg dir
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_message_cases signature msg dir
      hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_message_edge_cases
        signature msg dir hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.message msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
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
          rcases NewCorrespondence.relationMembership_message_cases signature
              msg dir
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
      have hCases := NewCorrespondence.compileType_message_edge_cases
        signature msg dir hEdge
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
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.message msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
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
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_tock_cases signature hRelated with
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
          have hEdge := NewCorrespondence.compileType_tock_action_edge
            signature hLocal
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
          have hEdge := NewCorrespondence.compileType_tock_wait_edge
            signature hLocal
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
              have hEdge := NewCorrespondence.compileType_tock_final_edge
                signature hLocal
                conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_tock_cases signature hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_tock_edge_cases
        signature hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature .tock).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
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
          rcases NewCorrespondence.relationMembership_tock_cases signature
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
      have hCases := NewCorrespondence.compileType_tock_edge_cases
        signature hEdge
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
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature .tock).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
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
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := signature.environments_subset_localEnvironments hEnvironment
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_progress_cases signature pid
      hRelated with
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
          have hEdge := NewCorrespondence.compileType_progress_action_edge
            signature pid
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
              have hEdge := NewCorrespondence.compileType_progress_final_edge
                signature pid
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_progress_cases signature pid
      hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        signature pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨_hSource, hTarget, hLabel, hCurrent,
          hFuture⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.progress pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
        subst residual'
        exact ⟨TypeTransition.progress env pid hWellFormed,
          TypeOffers.progress env pid hWellFormed⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        signature pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨hSource, _⟩
        simp at hSource
      · rcases hIdle with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.progress pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip := by
          exact (helper_h13_final_states_represent_completion signature
            hTargetRelated).mp hTargetAccepting
        subst residual'
        exact ⟨TypeTransition.skip env ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env ⟨hWellFormed, hClock⟩⟩

/-- Defines the one-step correspondence proposition used by the Lemma 4.5 induction. -/
def StepIffStatement
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership
      (buildRelationSet processType (compileType signature processType))
      residual state →
    ({ environment := env, label := label, offers := offers } :
        TypeAutomatonSymbol) ∈ (compileType signature processType).alphabet →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature processType).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet processType (compileType signature processType))
          residual' state')

/-- Step correspondence for ordinary binary choice `τ1 + τ2`. -/
theorem correspondence_choice_stepIff
    (signature : TypeAlphabet) (left right : PactType)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.choice left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's selection edges match the
  -- choice rule, and `hLeftIH`/`hRightIH` handle everything below the root.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.choice left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
        (.choice left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent := by
    rw [hFuelEq]
    show buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent =
      buildChoiceAutomaton signature (compileTypeFuel signature
        (typeCompilationFuel left) left) (compileTypeFuel signature
        (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
  have hFuelLeft :
      typeCompilationFuel left + 1 ≤ typeCompilationFuel (.choice left right) := by
    simp only [typeCompilationFuel]; omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel (.choice left right) := by
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_choice_cases signature left right hRelated with
    hRoot | ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · -- root case: `residual` represents `τ1 + τ2` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureLeftEq : computeFutureOf signature (.choice left right)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel left) left).initial) =
        typeFutureOffers left := by
      rw [computeFutureOf_binaryChoice_left signature left right TypeLabel.silent
        TypeLabel.silent (.choice left right) hWhole hFuelLeft
        (compileTypeFuel signature (typeCompilationFuel left) left).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel left) left le_rfl)]
      show computeFutureOf signature left (compileType signature left).initial =
        typeFutureOffers left
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial left (compileType signature left))
    have hFutureRightEq : computeFutureOf signature (.choice left right)
        (.child 1 (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
        typeFutureOffers right := by
      rw [computeFutureOf_binaryChoice_right signature left right TypeLabel.silent
        TypeLabel.silent (.choice left right) hWhole hFuelRight
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      TypeAlphabet.environments_subset_localEnvironments signature
        (transitionAlphabet_environment_mem signature hSignatureSymbol)
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hLeftPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible TypeLabel.silent,
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 0 (compileTypeFuel signature
              (typeCompilationFuel left) left).initial) ∅,
            target := childState 0 (compileTypeFuel signature (typeCompilationFuel left)
              left).initial } : PendingAutomatonEdge) ∈
          (buildChoiceAutomaton signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            TypeLabel.silent TypeLabel.silent).edges := by
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr ⟨env, hEnvMem, Or.inl rfl⟩
    have hRightPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible TypeLabel.silent,
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) ∅,
            target := childState 1 (compileTypeFuel signature (typeCompilationFuel right)
              right).initial } : PendingAutomatonEdge) ∈
          (buildChoiceAutomaton signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            TypeLabel.silent TypeLabel.silent).edges := by
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr ⟨env, hEnvMem, Or.inr rfl⟩
    constructor
    · intro hStep
      obtain ⟨-, hOffers⟩ := hStep
      -- `TypeOffers`'s own constructors already pin the label and target the
      -- same way `TypeTransition`'s do, so casing on the offers judgment
      -- alone (with every one of its output positions kept opaque first)
      -- determines everything without a second, redundant case split.
      generalize hLabelEq : label = actualLabel at hOffers
      generalize hTargetEq : residual' = actualTarget at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers with
      | choice_left _ _ _ _ =>
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hEdgeFact : (compileType signature (.choice left right)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
              left).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
            TypeAutomatonState.root (.child 0 (compileTypeFuel signature
              (typeCompilationFuel left) left).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hLeftPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureLeftEq
        have hChoiceLeftStep : DecoratedTypeTransition env (.choice left right)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left :=
          ⟨TypeTransition.choice_left env left right hWF,
            TypeOffers.choice_left env left right hWF⟩
        refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel left)
          left).initial, hEdgeFact, ?_⟩
        exact relationMembership_of_step_edge_unique (.choice left right)
          (compileType signature (.choice left right)) hRelated hEdgeFact hChoiceLeftStep
          (fun target hTargetStep =>
            decoratedTypeTransition_target_unique hTargetStep hChoiceLeftStep)
      | choice_right _ _ _ _ =>
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hEdgeFact : (compileType signature (.choice left right)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right))
            (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
              right).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
            TypeAutomatonState.root (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hRightPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureRightEq
        have hChoiceRightStep : DecoratedTypeTransition env (.choice left right)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right :=
          ⟨TypeTransition.choice_right env left right hWF,
            TypeOffers.choice_right env left right hWF⟩
        refine ⟨.child 1 (compileTypeFuel signature (typeCompilationFuel right)
          right).initial, hEdgeFact, ?_⟩
        exact relationMembership_of_step_edge_unique (.choice left right)
          (compileType signature (.choice left right)) hRelated hEdgeFact hChoiceRightStep
          (fun target hTargetStep =>
            decoratedTypeTransition_target_unique hTargetStep hChoiceRightStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice left right) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice left right) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
        Finset.mem_image] at hPendingMem
      have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
      rcases hPendingMem with (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
        ⟨environment, hEnvironment, hEq | hEq⟩
      · exfalso; rw [← hEq] at hRootSource; simp [childPendingEdge, childState] at hRootSource
      · exfalso; rw [← hEq] at hRootSource; simp [childPendingEdge, childState] at hRootSource
      · subst hEq
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers left := by
          rw [← hPFuture, Finset.sdiff_empty]; exact hFutureLeftEq
        rcases relationMembership_choice_cases signature left right hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
            ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hLeftRelatedAgain
          have hResidualEq : residual' = left :=
            relationMembership_functional left (compileType signature left)
              hLeftRelatedAgain (buildRelationSet_initial left (compileType signature left))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.choice_left env left right hWF,
            TypeOffers.choice_left env left right hWF⟩
        · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) = 1) (by decide)
      · subst hEq
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 1
            (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers right := by
          rw [← hPFuture, Finset.sdiff_empty]; exact hFutureRightEq
        rcases relationMembership_choice_cases signature left right hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
            ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · exact absurd (by simpa [childState] using hStateEqAgain : (1 : Nat) = 0) (by decide)
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hRightRelatedAgain
          have hResidualEq : residual' = right :=
            relationMembership_functional right (compileType signature right)
              hRightRelatedAgain
              (buildRelationSet_initial right (compileType signature right))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.choice_right env left right hWF,
            TypeOffers.choice_right env left right hWF⟩
  · -- left-child case: `hLeftIH` reconstructs the step directly
    have hState' : state = .child 0 q := by simpa using hStateEq
    subst state
    have hLeftSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature left).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ := (hLeftIH hLeftRelated hLeftSymbol).mp hStep
      have hOuterEdge : (compileType signature (.choice left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hLeftSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature left q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature left hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
            Finset.mem_image]
          exact Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_left signature left right
                TypeLabel.silent TypeLabel.silent
                (.choice left right) hWhole hFuelLeft t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.choice left right)
        (compileType signature (.choice left right)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice left right) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice left right) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 0 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildChoiceAutomaton_outgoing_left signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature left).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature left q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.choice left right) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_left signature left right
                TypeLabel.silent TypeLabel.silent
                (.choice left right) hWhole hFuelLeft t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_choice_cases signature left right hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
        ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hLeftRelatedAgain
        exact (hLeftIH hLeftRelated hLeftSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hLeftRelatedAgain⟩
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) = 1) (by decide)
  · -- right-child case: symmetric to the left-child case
    have hState' : state = .child 1 q := by simpa using hStateEq
    subst state
    have hRightSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature right).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hRightIH hRightRelated hRightSymbol).mp hStep
      have hOuterEdge : (compileType signature (.choice left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice left right)
          (.child 1 q) (.child 1 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hRightSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature right q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature right hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 1 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
            Finset.mem_image]
          exact Or.inl (Or.inr ⟨childEdge, hChildEdgeMem, rfl⟩)
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_right signature left right
                TypeLabel.silent TypeLabel.silent
                (.choice left right) hWhole hFuelRight t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 1 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.choice left right)
        (compileType signature (.choice left right)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice left right) (.child 1 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice left right) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 1 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildChoiceAutomaton_outgoing_right signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature right).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature right q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.choice left right) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_right signature left right
                TypeLabel.silent TypeLabel.silent
                (.choice left right) hWhole hFuelRight t hStateMem]
      have hTargetEq : state' = .child 1 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_choice_cases signature left right hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
        ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · exact absurd (by simpa [childState] using hStateEqAgain : (1 : Nat) = 0) (by decide)
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hRightRelatedAgain
        exact (hRightIH hRightRelated hRightSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hRightRelatedAgain⟩

/-- Step correspondence for fair binary choice `τ1 ⧺η τ2`. -/
theorem correspondence_fairChoice_stepIff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.fairChoice bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's two selection edges match
  -- `fair_left`/`fair_right`, and `hLeftIH`/`hRightIH` handle the children.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
        (.fairChoice bid left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    show buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton signature (compileTypeFuel signature
        (typeCompilationFuel left) left) (compileTypeFuel signature
        (typeCompilationFuel right) right) (TypeLabel.fair bid true)
        (TypeLabel.fair bid false)
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
  have hFuelLeft :
      typeCompilationFuel left + 1 ≤ typeCompilationFuel (.fairChoice bid left right) := by
    simp only [typeCompilationFuel]; omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel (.fairChoice bid left right) := by
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_fairChoice_cases signature bid left right hRelated with
    hRoot | ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · -- root case: `residual` represents `τ1 ⧺η τ2` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureLeftEq : computeFutureOf signature (.fairChoice bid left right)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel left) left).initial) =
        typeFutureOffers left := by
      rw [computeFutureOf_binaryChoice_left signature left right (TypeLabel.fair bid true)
        (TypeLabel.fair bid false) (.fairChoice bid left right) hWhole hFuelLeft
        (compileTypeFuel signature (typeCompilationFuel left) left).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel left) left le_rfl)]
      show computeFutureOf signature left (compileType signature left).initial =
        typeFutureOffers left
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial left (compileType signature left))
    have hFutureRightEq : computeFutureOf signature (.fairChoice bid left right)
        (.child 1 (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
        typeFutureOffers right := by
      rw [computeFutureOf_binaryChoice_right signature left right (TypeLabel.fair bid true)
        (TypeLabel.fair bid false) (.fairChoice bid left right) hWhole hFuelRight
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      TypeAlphabet.environments_subset_localEnvironments signature
        (transitionAlphabet_environment_mem signature hSignatureSymbol)
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hLeftPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible (TypeLabel.fair bid true),
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 0 (compileTypeFuel signature
              (typeCompilationFuel left) left).initial) ∅,
            target := childState 0 (compileTypeFuel signature (typeCompilationFuel left)
              left).initial } : PendingAutomatonEdge) ∈
          (buildChoiceAutomaton signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)).edges := by
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr ⟨env, hEnvMem, Or.inl rfl⟩
    have hRightPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible (TypeLabel.fair bid false),
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) ∅,
            target := childState 1 (compileTypeFuel signature (typeCompilationFuel right)
              right).initial } : PendingAutomatonEdge) ∈
          (buildChoiceAutomaton signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)).edges := by
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr ⟨env, hEnvMem, Or.inr rfl⟩
    constructor
    · intro hStep
      obtain ⟨hTrans, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hTrans
      generalize hTargetEq : residual' = actualTarget at hTrans
      cases hTrans
      · rw [hLabelEq, hTargetEq] at hOffers
        generalize hLabel2Eq : TypeLabel.fair bid true = actualLabel2 at hOffers
        generalize hCurrentEq : current = actualCurrent at hOffers
        generalize hFutureEq : future = actualFuture at hOffers
        cases hOffers
        · have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env (TypeLabel.fair bid true)
                (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
                signature.transitionAlphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hEdgeFact : (compileType signature (.fairChoice bid left right)).HasEdge
              TypeAutomatonState.root env (TypeLabel.fair bid true)
              (TypeOfferSummary.mk ∅ (typeFutureOffers left))
              (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                left).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice bid left right)
              TypeAutomatonState.root (.child 0 (compileTypeFuel signature
                (typeCompilationFuel left) left).initial) env (TypeLabel.fair bid true)
              (TypeOfferSummary.mk ∅ (typeFutureOffers left)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hLeftPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureLeftEq
          have hFairLeftStep : DecoratedTypeTransition env (.fairChoice bid left right)
              (TypeLabel.fair bid true) (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left :=
            ⟨TypeTransition.fair_left env bid left right hWF,
              TypeOffers.fair_left env bid left right hWF⟩
          refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel left)
            left).initial, hEdgeFact, ?_⟩
          exact relationMembership_of_step_edge_unique (.fairChoice bid left right)
            (compileType signature (.fairChoice bid left right)) hRelated hEdgeFact
            hFairLeftStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hFairLeftStep)
        · simp [TypeLabel.fair, Finset.ext_iff] at hLabel2Eq
      · rw [hLabelEq, hTargetEq] at hOffers
        generalize hLabel2Eq : TypeLabel.fair bid false = actualLabel2 at hOffers
        generalize hCurrentEq : current = actualCurrent at hOffers
        generalize hFutureEq : future = actualFuture at hOffers
        cases hOffers
        · simp [TypeLabel.fair, Finset.ext_iff] at hLabel2Eq
        · have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env (TypeLabel.fair bid false)
                (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
                signature.transitionAlphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hEdgeFact : (compileType signature (.fairChoice bid left right)).HasEdge
              TypeAutomatonState.root env (TypeLabel.fair bid false)
              (TypeOfferSummary.mk ∅ (typeFutureOffers right))
              (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                right).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice bid left right)
              TypeAutomatonState.root (.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial) env (TypeLabel.fair bid false)
              (TypeOfferSummary.mk ∅ (typeFutureOffers right)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hRightPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureRightEq
          have hFairRightStep : DecoratedTypeTransition env (.fairChoice bid left right)
              (TypeLabel.fair bid false) (TypeOfferSummary.mk ∅ (typeFutureOffers right))
              right :=
            ⟨TypeTransition.fair_right env bid left right hWF,
              TypeOffers.fair_right env bid left right hWF⟩
          refine ⟨.child 1 (compileTypeFuel signature (typeCompilationFuel right)
            right).initial, hEdgeFact, ?_⟩
          exact relationMembership_of_step_edge_unique (.fairChoice bid left right)
            (compileType signature (.fairChoice bid left right)) hRelated hEdgeFact
            hFairRightStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hFairRightStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice bid left right) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice bid left right) hEdge)).mp
        hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
        Finset.mem_image] at hPendingMem
      have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
      rcases hPendingMem with (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
        ⟨environment, hEnvironment, hEq | hEq⟩
      · exfalso; rw [← hEq] at hRootSource; simp [childPendingEdge, childState] at hRootSource
      · exfalso; rw [← hEq] at hRootSource; simp [childPendingEdge, childState] at hRootSource
      · subst hEq
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.fair bid true := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers left := by
          rw [← hPFuture, Finset.sdiff_empty]; exact hFutureLeftEq
        rcases relationMembership_fairChoice_cases signature bid left right hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
            ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hLeftRelatedAgain
          have hResidualEq : residual' = left :=
            relationMembership_functional left (compileType signature left)
              hLeftRelatedAgain (buildRelationSet_initial left (compileType signature left))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.fair_left env bid left right hWF,
            TypeOffers.fair_left env bid left right hWF⟩
        · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) = 1) (by decide)
      · subst hEq
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.fair bid false := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 1
            (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers right := by
          rw [← hPFuture, Finset.sdiff_empty]; exact hFutureRightEq
        rcases relationMembership_fairChoice_cases signature bid left right hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
            ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · exact absurd (by simpa [childState] using hStateEqAgain : (1 : Nat) = 0) (by decide)
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hRightRelatedAgain
          have hResidualEq : residual' = right :=
            relationMembership_functional right (compileType signature right)
              hRightRelatedAgain
              (buildRelationSet_initial right (compileType signature right))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.fair_right env bid left right hWF,
            TypeOffers.fair_right env bid left right hWF⟩
  · -- left-child case: `hLeftIH` reconstructs the step directly
    have hState' : state = .child 0 q := by simpa using hStateEq
    subst state
    have hLeftSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature left).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ := (hLeftIH hLeftRelated hLeftSymbol).mp hStep
      have hOuterEdge : (compileType signature (.fairChoice bid left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice bid left right)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hLeftSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature left q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature left hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
            Finset.mem_image]
          exact Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_left signature left right
                (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                (.fairChoice bid left right) hWhole hFuelLeft t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.fairChoice bid left right)
        (compileType signature (.fairChoice bid left right)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice bid left right) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice bid left right) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 0 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildChoiceAutomaton_outgoing_left signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature left).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature left q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.fairChoice bid left right) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_left signature left right
                (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                (.fairChoice bid left right) hWhole hFuelLeft t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_fairChoice_cases signature bid left right hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
        ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hLeftRelatedAgain
        exact (hLeftIH hLeftRelated hLeftSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hLeftRelatedAgain⟩
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) = 1) (by decide)
  · -- right-child case: symmetric to the left-child case
    have hState' : state = .child 1 q := by simpa using hStateEq
    subst state
    have hRightSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature right).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hRightIH hRightRelated hRightSymbol).mp hStep
      have hOuterEdge : (compileType signature (.fairChoice bid left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice bid left right)
          (.child 1 q) (.child 1 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hRightSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature right q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature right hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 1 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, childPendingEdges,
            Finset.mem_image]
          exact Or.inl (Or.inr ⟨childEdge, hChildEdgeMem, rfl⟩)
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_right signature left right
                (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                (.fairChoice bid left right) hWhole hFuelRight t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 1 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.fairChoice bid left right)
        (compileType signature (.fairChoice bid left right)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice bid left right) (.child 1 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice bid left right) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 1 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildChoiceAutomaton_outgoing_right signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature right).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature right q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.fairChoice bid left right) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_binaryChoice_right signature left right
                (TypeLabel.fair bid true) (TypeLabel.fair bid false)
                (.fairChoice bid left right) hWhole hFuelRight t hStateMem]
      have hTargetEq : state' = .child 1 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_fairChoice_cases signature bid left right hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hLeftRelatedAgain⟩ |
        ⟨qAgain, hStateEqAgain, hRightRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · exact absurd (by simpa [childState] using hStateEqAgain : (1 : Nat) = 0) (by decide)
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hRightRelatedAgain
        exact (hRightIH hRightRelated hRightSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hRightRelatedAgain⟩

/-- Step correspondence for sequencing `τ1 ; τ2`. -/
theorem correspondence_seq_stepIff
    (signature : TypeAlphabet) (first second : PactType)
    (hFirstIH : StepIffStatement signature first)
    (hSecondIH : StepIffStatement signature second) :
    StepIffStatement signature (.seq first second) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove a `τ1`-step from `hFirstIH` matches
  -- `seq`/`seq_fuse` by its target, and `hSecondIH` handles a right state.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hLeftForward :
      ∀ {residual' : PactType} {q1 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet first (compileType signature first))
          residual' q1 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature first).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q1', (compileType signature first).HasEdge q1 env label offers q1' ∧
          relationMembership (buildRelationSet first (compileType signature first))
            target q1' :=
    fun hMem hSym hStep' => (hFirstIH hMem hSym).mp hStep'
  constructor
  · intro hStep
    rcases relationMembership_seq_cases signature first second
      (hLeftForward := hLeftForward) hRelated with
      hLeft | hRight
    · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated⟩
      cases hEntry
      cases decoratedTypeTransition_seq_cases hStep with
      | step leftTarget childFuture hTarget hNonFinal hChildStep hFuture =>
          subst residual'
          subst future
          have hChildSymbol :
              TypeAutomatonSymbol.mk env label
                  (TypeOfferSummary.mk current childFuture) ∈
                (compileType signature first).alphabet := by
            change TypeAutomatonSymbol.mk env label
                (TypeOfferSummary.mk current childFuture) ∈
              signature.transitionAlphabet
            exact transitionAlphabet_of_typeOffers_target_subset signature
              hSignatureSymbol hChildStep.2
              (typeFutureOffers_subset_sequence_left_sdiff_union
                leftTarget second current)
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 0 q', compileType_seq_lift_left_step signature first second
            hRelated hLeftRelated hChildTargetRelated hNonFinal hChildStep
            hSignatureSymbol hChildEdge⟩
      | fuse childFuture hTarget hChildStep hFuture =>
          subst residual'
          subst future
          have hChildSymbol :
              TypeAutomatonSymbol.mk env label
                  (TypeOfferSummary.mk current childFuture) ∈
                (compileType signature first).alphabet := by
            change TypeAutomatonSymbol.mk env label
                (TypeOfferSummary.mk current childFuture) ∈
              signature.transitionAlphabet
            exact transitionAlphabet_of_typeOffers_target_subset signature
              hSignatureSymbol hChildStep.2
              (by simp [typeFutureOffers, typeFutureOffersFuel])
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 1 (compileType signature second).initial,
            compileType_seq_lift_left_fuse signature first second
              hRelated hLeftRelated hChildTargetRelated hChildStep
              hSignatureSymbol hChildEdge⟩
    · rcases hRight with ⟨q, hState, hRightRelated⟩
      change relationMembership (buildRelationSet second
        (compileType signature second)) residual q at hRightRelated
      have hState' : state = .child 1 q := by
        simpa using hState
      subst state
      have hChildSymbol :
          TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
            (compileType signature second).alphabet := by
        change TypeAutomatonSymbol.mk env label
            (TypeOfferSummary.mk current future) ∈ signature.transitionAlphabet
        exact hSignatureSymbol
      rcases (hSecondIH hRightRelated hChildSymbol).mp hStep with
        ⟨q', hChildEdge, hChildTargetRelated⟩
      exact compileType_seq_lift_right_step signature first second hRelated
        hRightRelated hChildTargetRelated hStep hChildEdge
  · rintro ⟨state', hEdge, hTargetRelated⟩
    cases compileType_seq_edge_cases signature first second
        (hLeftForward := hLeftForward) hRelated hEdge hTargetRelated with
    | leftStep leftResidual leftTarget q q' childFuture hResidual hResidual'
        hState hState' hNonFinal hLeftRelated hLeftTargetRelated hChildEdge
        hFuture =>
        subst residual
        subst residual'
        subst state
        subst state'
        subst future
        have hChildSymbol :=
          NewCorrespondence.compileType_hasEdge_symbol_mem signature first
            hChildEdge
        have hChildStep :=
          (hFirstIH hLeftRelated hChildSymbol).mpr
            ⟨q', hChildEdge, hLeftTargetRelated⟩
        exact ⟨TypeTransition.seq env leftResidual leftTarget second label
            hChildStep.1 hNonFinal,
          TypeOffers.seq env leftResidual leftTarget second label current
            childFuture hChildStep.2 hNonFinal⟩
    | leftFuse leftResidual q q' childFuture hResidual hResidual' hState
        hLeftRelated hLeftTargetRelated hChildEdge hFuture =>
        subst residual
        subst residual'
        subst state
        subst future
        have hChildSymbol :=
          NewCorrespondence.compileType_hasEdge_symbol_mem signature first
            hChildEdge
        have hChildStep :=
          (hFirstIH hLeftRelated hChildSymbol).mpr
            ⟨q', hChildEdge, hLeftTargetRelated⟩
        exact ⟨TypeTransition.seq_fuse env leftResidual second label
            hChildStep.1,
          TypeOffers.seq_fuse env leftResidual second label current childFuture
            hChildStep.2⟩
    | entryFuse hResidual hResidual' hState hState' hLabel hCurrent hFuture
        hWellFormed hClock =>
        subst residual
        subst residual'
        subst state
        subst state'
        subst label
        subst current
        subst future
        exact ⟨TypeTransition.seq_fuse env .skip second TypeLabel.silent
            (TypeTransition.skip env ⟨hWellFormed, hClock⟩),
          by
            simpa using TypeOffers.seq_fuse env .skip second TypeLabel.silent
              ∅ ∅ (TypeOffers.skip env ⟨hWellFormed, hClock⟩)⟩
    | rightStep q q' hState hState' hRightRelated hRightTargetRelated
        hChildEdge =>
        subst state
        subst state'
        have hChildSymbol :=
          NewCorrespondence.compileType_hasEdge_symbol_mem signature second
            hChildEdge
        exact (hSecondIH hRightRelated hChildSymbol).mpr
          ⟨q', hChildEdge, hRightTargetRelated⟩

/-- Step correspondence for interleaved parallel composition `τ1 ‖_I τ2`. -/
theorem correspondence_par_stepIff
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.par left right interface) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove `hLeftIH`/`hRightIH` give two component
  -- edges that combine into the matching `par`/`par_fuse` product edge.
  sorry

/-- Step correspondence for recursion `μX.body`. -/
theorem correspondence_recur_stepIff
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (hBodyIH : StepIffStatement signature body) :
    StepIffStatement signature (.recur name body) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's unfolding step matches the
  -- header edge, and `hBodyIH` transported along substitution handles the
  -- rest of the body, including a marker turning into a backedge.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.recur name body) = typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
        (.recur name body) =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body) := by
    rw [hFuelEq]
    show buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body) =
      buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body)
    rfl
  rcases relationMembership_recur_cases signature name body hRelated with
    hRoot | ⟨q, bodyResidual, hEntryEq, hBodyRelated⟩
  · -- root case: `residual` represents `μX.body` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hEnvMem : env ∈ signature.localEnvironments :=
      TypeAlphabet.environments_subset_localEnvironments signature
        (transitionAlphabet_environment_mem signature hSignatureSymbol)
    have hHeaderPending :
        ({ source := TypeAutomatonState.root, environment := env,
            label := AutomatonConstructionLabel.visible TypeLabel.silent,
            current := (∅ : Finset BareMessage),
            future := FutureSpec.at (childState 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial) ∅,
            target := childState 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial } :
          PendingAutomatonEdge) ∈
          (buildRecursionAutomaton signature name
            (compileTypeFuel signature (typeCompilationFuel body) body)).edges := by
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image]
      exact Or.inl ⟨env, hEnvMem, rfl⟩
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRecurStep : DecoratedTypeTransition env (.recur name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers (body.replaceVar name (.recur name body))))
        (body.replaceVar name (.recur name body)) :=
      ⟨TypeTransition.recur env name body hWF, TypeOffers.recur env name body hWF⟩
    constructor
    · intro hStep
      obtain ⟨hTrans, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hTrans
      generalize hTargetEq : residual' = actualTarget at hTrans
      cases hTrans
      rw [hLabelEq, hTargetEq] at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers
      have hSignatureSymbol' :
          TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅
                (typeFutureOffers (body.replaceVar name (.recur name body)))) ∈
            (compileType signature (.recur name body)).alphabet := by
        rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
        exact hSignatureSymbol
      have hEdgeFact :
          (compileType signature (.recur name body)).HasEdge TypeAutomatonState.root
            env TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur name body))))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel body)
              body).initial) := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.recur name body)
          TypeAutomatonState.root (.child 0 (compileTypeFuel signature
            (typeCompilationFuel body) body).initial) env TypeLabel.silent
          (TypeOfferSummary.mk ∅
            (typeFutureOffers (body.replaceVar name (.recur name body))))
          hSignatureSymbol']
        rw [hWhole]
        refine ⟨_, hHeaderPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
        simp only [childState, Finset.sdiff_empty]
        exact helper_h15_recursion_future_offers_agree signature name body
          (buildRelationSet_initial body (compileType signature body))
      refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel body)
        body).initial, hEdgeFact, ?_⟩
      exact relationMembership_of_step_edge_unique (.recur name body)
        (compileType signature (.recur name body)) hRelated
        hEdgeFact hRecurStep
        (fun target hTargetStep =>
          decoratedTypeTransition_target_unique hTargetStep hRecurStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur name body)
        hEdge
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.recur name body) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future) hSymbolMem).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image] at hPendingMem
      rcases hPendingMem with ⟨environment, hEnvironment, hEq⟩ | ⟨bodyEdge, _, hEq⟩
      · subst hEq
        simp only [childState] at hPLabel hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        rcases relationMembership_recur_cases signature name body hTargetRelated with
          hRootAgain | ⟨qAgain, bodyResidualAgain, hEntryEqAgain, hBodyRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain)
            (by simp [childState])
        · simp only [Prod.mk.injEq] at hEntryEqAgain
          obtain ⟨hResidualEqAgain, hStateEqAgain⟩ := hEntryEqAgain
          have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hBodyRelatedAgain
          have hBodyEq : bodyResidualAgain = body :=
            relationMembership_functional body (compileType signature body)
              hBodyRelatedAgain (buildRelationSet_initial body (compileType signature body))
          rw [hBodyEq] at hResidualEqAgain
          have hPFuture' : computeFutureOf signature (.recur name body)
              (childState 0 (compileTypeFuel signature (typeCompilationFuel body)
                body).initial) \ (∅ : Finset BareMessage) = future := hPFuture
          have hFutureEq : future =
              typeFutureOffers (body.replaceVar name (.recur name body)) := by
            rw [← hPFuture', Finset.sdiff_empty, childState]
            exact helper_h15_recursion_future_offers_agree signature name body
              (buildRelationSet_initial body (compileType signature body))
          have hEnvironmentEq : environment = env := hPEnv
          rw [hResidualEqAgain, hLabelEq]
          refine ⟨TypeTransition.recur env name body
            (localEnvironment_wellFormed signature (hEnvironmentEq ▸ hEnvironment)), ?_⟩
          rw [hCurrentEq, hFutureEq]
          exact TypeOffers.recur env name body
            (localEnvironment_wellFormed signature (hEnvironmentEq ▸ hEnvironment))
      · exfalso
        have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
        rw [← hEq] at hRootSource
        split at hRootSource <;> simp [childState] at hRootSource
  · -- body case: `residual` represents `bodyResidual` substituted for the open variable
    simp only [Prod.mk.injEq] at hEntryEq
    obtain ⟨hResidualEq, hStateEq⟩ := hEntryEq
    subst hResidualEq; subst hStateEq
    have hBodySymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature body).alphabet := by
      simpa [compileType] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨residual0, hResidual'Eq, hBodyStep⟩ :=
        (decoratedTypeTransition_replaceVar_iff name body bodyResidual).mp hStep
      obtain ⟨q', hBodyEdge, hBodyTargetRelated⟩ :=
        (hBodyIH hBodyRelated hBodySymbol).mp hBodyStep
      have hChildSymbol := compileType_hasEdge_symbol_mem signature body hBodyEdge
      have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature body
        q q' env label (TypeOfferSummary.mk current future) hChildSymbol).mp hBodyEdge
      obtain ⟨nativeEdge, hNativeMem, hNSource, hNEnv, hNLabel, hNCurrent, hNFuture,
        hNTarget⟩ := hChildResolved
      have hNotMarker : nativeEdge.label ≠ .variable name := by
        rw [hNLabel]; simp
      have hOuterEdge : (compileType signature (.recur name body)).HasEdge
          (.child 0 q) env label
          (TypeOfferSummary.mk current future)
          (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.recur name body)
          (.child 0 q) (.child 0 q') env label
          (TypeOfferSummary.mk current future)
          hSymbol]
        rw [hWhole]
        refine ⟨childPendingEdge 0 nativeEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image]
          exact Or.inr ⟨nativeEdge, hNativeMem, by simp [hNotMarker, childPendingEdge]⟩
        · simp [childPendingEdge, childState, hNSource]
        · simp [childPendingEdge, hNEnv]
        · simp [childPendingEdge, hNLabel]
        · simp [childPendingEdge, hNCurrent]
        · cases hSpec : nativeEdge.future with
          | explicit offers =>
              simpa [childPendingEdge, childFutureSpec, hSpec] using hNFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel body) body le_rfl nativeEdge hNativeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_recursion_child signature name body (.recur name body)
                hWhole (by omega) t hStateMem]
              simpa [childFutureSpec, hSpec] using hNFuture
        · simp [childPendingEdge, childState, hNTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      rw [hResidual'Eq] at hStep
      rw [hResidual'Eq]
      exact relationMembership_of_step_edge_unique (.recur name body)
        (compileType signature (.recur name body)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur name body) hEdge
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature (.recur name body)
        (.child 0 q) state' env label (TypeOfferSummary.mk current future) hSymbolMem).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
        Finset.mem_image] at hPendingMem
      rcases hPendingMem with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdgeMem, hEq⟩
      · exfalso
        have hChildSource : pendingEdge.source = .child 0 q := hPSource
        rw [← hEq] at hChildSource
        simp [childState] at hChildSource
      · by_cases hMarker : bodyEdge.label = .variable name
        · -- Given a marker body edge, we need the same unfolding step the
          -- root case reconstructs, since the source represents the open
          -- variable and the compiler installs a backedge for it.
          simp only [hMarker, if_true] at hEq
          subst hEq
          simp only [childState] at hPSource hPTarget
          have hSourceEq : bodyEdge.source = q := by simpa [childState] using hPSource
          have hResidualEq : bodyResidual = .var name :=
            compileTypeFuel_marker_represents_var signature name body hBodyRelated
              hBodyEdgeMem hSourceEq hMarker
          have hTargetEq : state' = .child 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            rw [← hPTarget]
          rw [hTargetEq] at hTargetRelated
          rcases relationMembership_recur_cases signature name body hTargetRelated with
            hRootAgain | ⟨qAgain, bodyResidualAgain, hEntryEqAgain, hBodyRelatedAgain⟩
          · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
          · simp only [Prod.mk.injEq] at hEntryEqAgain
            obtain ⟨hResidualEqAgain, hStateEqAgain⟩ := hEntryEqAgain
            have hQAgainEq : qAgain =
                (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
              simpa [childState] using hStateEqAgain.symm
            rw [hQAgainEq] at hBodyRelatedAgain
            have hBodyEq : bodyResidualAgain = body :=
              relationMembership_functional body (compileType signature body)
                hBodyRelatedAgain (buildRelationSet_initial body (compileType signature body))
            rw [hBodyEq] at hResidualEqAgain
            have hLabelEq : label = TypeLabel.silent := by
              have h := hPLabel; simp [childState] at h; exact h.symm
            have hCurrentEq : current = ∅ := hPCurrent.symm
            have hPFuture' : computeFutureOf signature (.recur name body)
                (childState 0 (compileTypeFuel signature (typeCompilationFuel body)
                  body).initial) \ (∅ : Finset BareMessage) = future := hPFuture
            have hFutureEq : future =
                typeFutureOffers (body.replaceVar name (.recur name body)) := by
              rw [← hPFuture', Finset.sdiff_empty, childState]
              exact helper_h15_recursion_future_offers_agree signature name body
                (buildRelationSet_initial body (compileType signature body))
            have hEnvMem : env ∈ signature.localEnvironments :=
              TypeAlphabet.environments_subset_localEnvironments signature
                (transitionAlphabet_environment_mem signature hSignatureSymbol)
            have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
            rw [hResidualEqAgain, hLabelEq, hResidualEq]
            simp only [PactType.replaceVar]
            rw [hCurrentEq, hFutureEq]
            exact ⟨TypeTransition.recur env name body hWF, TypeOffers.recur env name body hWF⟩
        · -- Given a copied non-marker body edge, `hBodyIH` reconstructs the
          -- child step, and the substitution fact lifts it to the residual.
          simp only [hMarker, if_false] at hEq
          subst hEq
          simp only [childState] at hPSource hPTarget
          have hSourceEq : bodyEdge.source = q := by simpa [childState] using hPSource
          have hInnerEdgeMem : (compileType signature body).HasEdge q env label
              (TypeOfferSummary.mk current future) bodyEdge.target := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature body q bodyEdge.target
              env label (TypeOfferSummary.mk current future) hBodySymbol]
            refine ⟨bodyEdge, hBodyEdgeMem, hSourceEq, ?_, ?_, ?_, ?_, rfl⟩
            · rw [← hPEnv]
            · rw [← hPLabel]
            · rw [← hPCurrent]
            · rw [← hPFuture]
              cases hSpec : bodyEdge.future with
              | explicit offers => simp [childFutureSpec, hSpec]
              | «at» t r =>
                  have hStateMem := compileTypeFuel_futureTargetsInStates signature
                    (typeCompilationFuel body) body le_rfl bodyEdge hBodyEdgeMem t r hSpec
                  simp only [childFutureSpec, hSpec, childState]
                  rw [computeFutureOf_recursion_child signature name body
                    (.recur name body) hWhole (by omega) t hStateMem]
          have hTargetEq : state' = .child 0 bodyEdge.target := by rw [← hPTarget]
          rw [hTargetEq] at hTargetRelated
          rcases relationMembership_recur_cases signature name body hTargetRelated with
            hRootAgain | ⟨qAgain, bodyResidualAgain, hEntryEqAgain, hBodyRelatedAgain⟩
          · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
          · simp only [Prod.mk.injEq] at hEntryEqAgain
            obtain ⟨hResidualEqAgain, hStateEqAgain⟩ := hEntryEqAgain
            have hQAgainEq : qAgain = bodyEdge.target := by
              simpa [childState] using hStateEqAgain.symm
            rw [hQAgainEq] at hBodyRelatedAgain
            have hInnerStep : DecoratedTypeTransition env bodyResidual label
                (TypeOfferSummary.mk current future) bodyResidualAgain :=
              (hBodyIH hBodyRelated hBodySymbol).mpr
                ⟨bodyEdge.target, hInnerEdgeMem, hBodyRelatedAgain⟩
            rw [hResidualEqAgain]
            exact (decoratedTypeTransition_replaceVar_iff name body bodyResidual).mpr
              ⟨bodyResidualAgain, rfl, hInnerStep⟩

set_option maxHeartbeats 4000000 in
/-- Step correspondence for exclusive offer `⨁(τ0,B)`. -/
theorem correspondence_xoffer_stepIff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseIH : StepIffStatement signature elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) :
    StepIffStatement signature (.xoffer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's fire/else/wait edges match
  -- the three offer rules, and `hElseIH`/`hBranchesIH` handle the rest.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.xoffer elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.xoffer elseType branches))
        (.xoffer elseType branches) =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)) := by
    rw [hFuelEq]
    show buildExclusiveOfferAutomaton signature branches
        (compileTypeFuel signature
          (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) elseType)
        (branches.map fun branch => (branch.1, compileTypeFuel signature
          (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches))
          branch.2)) =
      buildExclusiveOfferAutomaton signature branches
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
        (branches.map fun branch => (branch.1, compileTypeFuel signature
          (typeCompilationFuel branch.2) branch.2))
    congr 1
    · exact compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl
    · apply List.map_congr_left
      intro branch hBranch
      congr 1
      exact compileTypeFuel_eq_of_sufficient signature branch.2
        (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
          (le_max_right _ _)) le_rfl
  have hElseFuelStrict : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.xoffer elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hBranchFuelStrict : ∀ branch ∈ branches, typeCompilationFuel branch.2 + 1 ≤
      typeCompilationFuel (.xoffer elseType branches) := by
    intro branch hBranch
    have h1 := typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_xoffer_cases signature elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, action, branchType, q, hBranchesEq, hStateEq, hBranchRelated⟩
  · -- root case: `residual` represents `⨁(τ0,B)` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureElseEq : computeFutureOf signature (.xoffer elseType branches)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial) = typeFutureOffers elseType := by
      rw [computeFutureOf_exclusiveOffer_else signature elseType branches
        (.xoffer elseType branches) hWhole hElseFuelStrict
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      TypeAlphabet.environments_subset_localEnvironments signature
        (transitionAlphabet_environment_mem signature hSignatureSymbol)
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRootRelated : relationMembership
        (buildRelationSet (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)))
        (.xoffer elseType branches) TypeAutomatonState.root := by
      simpa using hRelated
    have hRootFuture : computeFutureOf signature (.xoffer elseType branches)
        TypeAutomatonState.root = typeFutureOffers (.xoffer elseType branches) :=
      helper_h15_future_offers_agree signature hRootRelated
    constructor
    · intro hStep
      obtain ⟨-, hOffers⟩ := hStep
      -- `TypeOffers`'s own constructors already pin the label, target,
      -- current, and future offer, so casing on the offers judgment alone
      -- (with every one of its output positions kept opaque first)
      -- determines everything, mirroring the fix used for `choice`.
      generalize hLabelEq : label = actualLabel at hOffers
      generalize hTargetEq : residual' = actualTarget at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers with
      | xoffer_branch _ _ _ branchAction _ hPremise =>
        -- The `processType` slot is already pinned to `actualTarget` by
        -- unifying against `hOffers`'s own (generalized) target index, so
        -- the pattern names it `_` and the proof below refers to
        -- `actualTarget` directly rather than introducing a fresh name.
        obtain ⟨hWF', hBranchMem, hEnabled, hResolvedNeeds⟩ := hPremise
        obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hBranchMem
        have hFutureBranchEq : computeFutureOf signature (.xoffer elseType branches)
            (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) =
            typeFutureOffers actualTarget := by
          rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
            (.xoffer elseType branches) hWhole index branchAction actualTarget hBranchGet
            (hBranchFuelStrict (branchAction, actualTarget) hBranchMem)
            (compileTypeFuel signature (typeCompilationFuel actualTarget)
              actualTarget).initial (compileTypeFuel_initial_mem signature
              (typeCompilationFuel actualTarget) actualTarget le_rfl)]
          show computeFutureOf signature actualTarget (compileType signature
            actualTarget).initial = typeFutureOffers actualTarget
          exact helper_h15_future_offers_agree signature
            (buildRelationSet_initial actualTarget (compileType signature actualTarget))
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env (TypeLabel.message branchAction.1 branchAction.2)
              (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hBranchPending :
            ({ source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible
                  (TypeLabel.message branchAction.1 branchAction.2),
                current := {branchAction},
                future := FutureSpec.at (childState (index + 1)
                  (compileTypeFuel signature (typeCompilationFuel actualTarget)
                    actualTarget).initial) ∅,
                target := childState (index + 1) (compileTypeFuel signature
                  (typeCompilationFuel actualTarget) actualTarget).initial } :
              PendingAutomatonEdge) ∈
              (buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                (branches.map fun branch => (branch.1, compileTypeFuel signature
                  (typeCompilationFuel branch.2) branch.2))).edges := by
          simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
          refine Or.inl (Or.inl (Or.inr ?_))
          rw [mem_foldl_union_iff]
          refine Or.inr ⟨(⟨branchAction, compileTypeFuel signature
            (typeCompilationFuel actualTarget) actualTarget⟩, index), ?_, ?_⟩
          · exact List.mk_mem_zipIdx_iff_getElem?.mpr
              ((branches_map_getElem?_eq_some_iff signature branches index branchAction
                (compileTypeFuel signature (typeCompilationFuel actualTarget)
                  actualTarget)).mpr ⟨actualTarget, hBranchGet, rfl⟩)
          · simp only [Finset.mem_image, Finset.mem_filter]
            exact ⟨env, ⟨hEnvMem, hEnabled, hResolvedNeeds⟩, rfl⟩
        have hEdgeFact : (compileType signature (.xoffer elseType branches)).HasEdge
            TypeAutomatonState.root env (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer elseType branches)
            TypeAutomatonState.root (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) env
            (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hBranchPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureBranchEq
        have hBranchStep : DecoratedTypeTransition env (.xoffer elseType branches)
            (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            actualTarget :=
          ⟨TypeTransition.xoffer_branch env elseType branches branchAction actualTarget
            ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩,
            TypeOffers.xoffer_branch env elseType branches branchAction actualTarget
              ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩⟩
        refine ⟨.child (index + 1) (compileTypeFuel signature
          (typeCompilationFuel actualTarget) actualTarget).initial, hEdgeFact, ?_⟩
        exact relationMembership_of_step_edge_unique (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)) hRelated hEdgeFact hBranchStep
          (fun target hTargetStep =>
            decoratedTypeTransition_target_unique hTargetStep hBranchStep)
      | xoffer_else _ _ _ hPremise =>
        obtain ⟨hWF', hNoImmediate, hResolvedNeeds⟩ := hPremise
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers elseType)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hElsePending :
            ({ source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 0 (compileTypeFuel signature
                  (typeCompilationFuel elseType) elseType).initial) ∅,
                target := childState 0 (compileTypeFuel signature
                  (typeCompilationFuel elseType) elseType).initial } :
              PendingAutomatonEdge) ∈
              (buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                (branches.map fun branch => (branch.1, compileTypeFuel signature
                  (typeCompilationFuel branch.2) branch.2))).edges := by
          simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter]
          exact Or.inr ⟨env, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
        have hEdgeFact : (compileType signature (.xoffer elseType branches)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers elseType))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
              elseType).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer elseType branches)
            TypeAutomatonState.root (.child 0 (compileTypeFuel signature
              (typeCompilationFuel elseType) elseType).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers elseType)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hElsePending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureElseEq
        have hElseStep : DecoratedTypeTransition env (.xoffer elseType branches)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers elseType)) elseType :=
          ⟨TypeTransition.xoffer_else env elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.xoffer_else env elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
        refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial, hEdgeFact, ?_⟩
        exact relationMembership_of_step_edge_unique (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)) hRelated hEdgeFact hElseStep
          (fun target hTargetStep =>
            decoratedTypeTransition_target_unique hTargetStep hElseStep)
      | xoffer_wait _ _ _ hPremise =>
        obtain ⟨hWF', hUnresolved, hClock⟩ := hPremise
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.xoffer elseType branches) \
                  typeWaitingOffers env branches)) ∈ signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hWaitPending :
            ({ source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeWaitingOffers env branches,
                future := FutureSpec.at TypeAutomatonState.root
                  (typeWaitingOffers env branches),
                target := TypeAutomatonState.root } : PendingAutomatonEdge) ∈
              (buildExclusiveOfferAutomaton signature branches
                (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                (branches.map fun branch => (branch.1, compileTypeFuel signature
                  (typeCompilationFuel branch.2) branch.2))).edges := by
          simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter]
          refine Or.inl (Or.inr ⟨env, ⟨hEnvMem, hClock, hUnresolved⟩, ?_⟩)
          simp [typeWaitingOffers]
        have hEdgeFact : (compileType signature (.xoffer elseType branches)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches)) TypeAutomatonState.root := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer elseType branches)
            TypeAutomatonState.root TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hWaitPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          show computeFutureOf signature (.xoffer elseType branches) TypeAutomatonState.root \
            typeWaitingOffers env branches = typeFutureOffers (.xoffer elseType branches) \
              typeWaitingOffers env branches
          rw [hRootFuture]
        have hWaitStep : DecoratedTypeTransition env (.xoffer elseType branches)
            TypeLabel.silent (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer elseType branches) \
                typeWaitingOffers env branches)) (.xoffer elseType branches) :=
          ⟨TypeTransition.xoffer_wait env elseType branches
            ⟨hWF, hUnresolved, hClock⟩,
            TypeOffers.xoffer_wait env elseType branches
              ⟨hWF, hUnresolved, hClock⟩⟩
        refine ⟨TypeAutomatonState.root, hEdgeFact, ?_⟩
        exact relationMembership_of_step_edge_unique (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)) hRelated hEdgeFact hWaitStep
          (fun target hTargetStep =>
            decoratedTypeTransition_target_unique hTargetStep hWaitStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
        at hPendingMem
      rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved2)
      · exfalso
        simp only [childPendingEdges, Finset.mem_image] at hElse
        obtain ⟨childEdge, _, hEq⟩ := hElse
        rw [← hEq] at hRootSource
        simp [childPendingEdge, childState] at hRootSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hNewEdge⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hNewEdge
          obtain ⟨childEdge, _, hEq⟩ := hNewEdge
          rw [← hEq] at hRootSource
          simp [childPendingEdge, childState] at hRootSource
      · -- fire family: reconstructs `xoffer_branch`
        rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          obtain ⟨⟨branchAction, automaton⟩, index⟩ := indexed
          rcases hNewEdge with ⟨environment, ⟨hEnvMem, hEnabled, hResolvedNeeds⟩, rfl⟩
          have hEnvEq : environment = env := hPEnv
          subst environment
          have hIndexedGet :
              (branches.map fun branch => (branch.1, compileTypeFuel signature
                (typeCompilationFuel branch.2) branch.2))[index]? =
                some (branchAction, automaton) :=
            List.mk_mem_zipIdx_iff_getElem?.mp hIndexedEntry
          obtain ⟨branchType', hBranchGet, hAutEq⟩ :=
            (branches_map_getElem?_eq_some_iff signature branches index branchAction
              automaton).mp hIndexedGet
          have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
          have hBranchMem : (branchAction, branchType') ∈ branches :=
            List.mem_iff_getElem?.mpr ⟨index, hBranchGet⟩
          simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
          have hLabelEq : label = TypeLabel.message branchAction.1 branchAction.2 := by
            have h := hPLabel; simp at h; exact h.symm
          have hCurrentEq : current = {branchAction} := hPCurrent.symm
          have hTargetEq : state' = .child (index + 1)
              (compileTypeFuel signature (typeCompilationFuel branchType')
                branchType').initial := by
            rw [← hPTarget, ← hAutEq]
          rw [hTargetEq] at hTargetRelated
          have hFutureEq : future = typeFutureOffers branchType' := by
            rw [← hPFuture, Finset.sdiff_empty, ← hAutEq]
            rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
              (.xoffer elseType branches) hWhole index branchAction branchType' hBranchGet
              (hBranchFuelStrict (branchAction, branchType') hBranchMem)
              (compileTypeFuel signature (typeCompilationFuel branchType')
                branchType').initial (compileTypeFuel_initial_mem signature
                (typeCompilationFuel branchType') branchType' le_rfl)]
            show computeFutureOf signature branchType' (compileType signature
              branchType').initial = typeFutureOffers branchType'
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial branchType' (compileType signature branchType'))
          rcases relationMembership_xoffer_cases signature elseType branches hTargetRelated
            with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
              ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain,
                hStateEqAgain, hBranchRelatedAgain⟩
          · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
          · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
              index + 1) (by omega)
          · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
                .child (index + 1) (compileTypeFuel signature
                  (typeCompilationFuel branchType') branchType').initial := by
              simpa [childState] using hStateEqAgain.symm
            injection hSndEq with hIEq hQEq
            have hIAgainEq : iAgain = index := by omega
            subst hIAgainEq
            have hPairEq : (actionAgain, branchTypeAgain) = (branchAction, branchType') := by
              have h := hBranchesEqAgain.symm.trans hBranchGet
              simpa using h
            have hBranchTypeAgainEq : branchTypeAgain = branchType' :=
              congrArg Prod.snd hPairEq
            rw [hBranchTypeAgainEq, hQEq] at hBranchRelatedAgain
            have hResidualEq : residual' = branchType' :=
              relationMembership_functional branchType' (compileType signature branchType')
                hBranchRelatedAgain
                (buildRelationSet_initial branchType' (compileType signature branchType'))
            rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
            exact ⟨TypeTransition.xoffer_branch env elseType branches branchAction branchType'
              ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩,
              TypeOffers.xoffer_branch env elseType branches branchAction branchType'
                ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩⟩
      · -- wait family: reconstructs `xoffer_wait`
        simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, ⟨hEnvMem, hClock, hUnresolved⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = typeWaitingOffers env branches := hPCurrent.symm
        have hTargetEq : state' = TypeAutomatonState.root := by rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers (.xoffer elseType branches) \
            typeWaitingOffers env branches := by
          rw [← hPFuture, hRootFuture]
          rfl
        rcases relationMembership_xoffer_cases signature elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain,
              hStateEqAgain, hBranchRelatedAgain⟩
        · simp only [Prod.mk.injEq] at hRootAgain
          have hResidualEq : residual' = .xoffer elseType branches := hRootAgain.1
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.xoffer_wait env elseType branches
            ⟨hWF, hUnresolved, hClock⟩,
            TypeOffers.xoffer_wait env elseType branches
              ⟨hWF, hUnresolved, hClock⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child 0 qAgain) (by simp)
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child (iAgain + 1) qAgain)
            (by simp)
      · -- else family: reconstructs `xoffer_else`
        simp only [Finset.mem_image, Finset.mem_filter] at hResolved2
        rcases hResolved2 with ⟨environment, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers elseType := by
          rw [← hPFuture, Finset.sdiff_empty]
          rw [computeFutureOf_exclusiveOffer_else signature elseType branches
            (.xoffer elseType branches) hWhole hElseFuelStrict
            (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
            (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
              le_rfl)]
          show computeFutureOf signature elseType (compileType signature elseType).initial =
            typeFutureOffers elseType
          exact helper_h15_future_offers_agree signature
            (buildRelationSet_initial elseType (compileType signature elseType))
        rcases relationMembership_xoffer_cases signature elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain,
              hStateEqAgain, hBranchRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hElseRelatedAgain
          have hResidualEq : residual' = elseType :=
            relationMembership_functional elseType (compileType signature elseType)
              hElseRelatedAgain (buildRelationSet_initial elseType
                (compileType signature elseType))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.xoffer_else env elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.xoffer_else env elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
            iAgain + 1) (by omega)
  · -- else-child case: `hElseIH` reconstructs the step directly
    have hState' : state = .child 0 q := by simpa using hStateEq
    subst state
    have hElseSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature elseType).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hElseIH hElseRelated hElseSymbol).mp hStep
      have hOuterEdge : (compileType signature (.xoffer elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer elseType branches)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hElseSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature elseType q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature elseType hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union,
            childPendingEdges, Finset.mem_image]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_exclusiveOffer_else signature elseType branches
                (.xoffer elseType branches) hWhole hElseFuelStrict t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.xoffer elseType branches)
        (compileType signature (.xoffer elseType branches)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 0 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildExclusiveOfferAutomaton_outgoing_else signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)) q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature elseType).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature elseType q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.xoffer elseType branches) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_exclusiveOffer_else signature elseType branches
                (.xoffer elseType branches) hWhole hElseFuelStrict t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_xoffer_cases signature elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain, hStateEqAgain,
          hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hElseRelatedAgain
        exact (hElseIH hElseRelated hElseSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hElseRelatedAgain⟩
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
          iAgain + 1) (by omega)
  · -- branch-child case: `hBranchesIH` reconstructs the step directly
    have hState' : state = .child (i + 1) q := by simpa using hStateEq
    subst state
    have hBranchMem : (action, branchType) ∈ branches :=
      List.mem_iff_getElem?.mpr ⟨i, hBranchesEq⟩
    have hBranchSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature branchType).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hBranchesIH action branchType hBranchMem hBranchRelated hBranchSymbol).mp hStep
      have hAutomataGet :
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2))[i]? =
            some (action, compileTypeFuel signature (typeCompilationFuel branchType)
              branchType) :=
        (branches_map_getElem?_eq_some_iff signature branches i action
          (compileTypeFuel signature (typeCompilationFuel branchType) branchType)).mpr
          ⟨branchType, hBranchesEq, rfl⟩
      have hOuterEdge : (compileType signature (.xoffer elseType branches)).HasEdge
          (.child (i + 1) q) env label (TypeOfferSummary.mk current future)
          (.child (i + 1) q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer elseType branches)
          (.child (i + 1) q) (.child (i + 1) q') env label
          (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hBranchSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature branchType
          q q' env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature branchType hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
          refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
          rw [indexedFragmentEdges, mem_foldl_union_iff]
          refine Or.inr ⟨(⟨action, compileTypeFuel signature
            (typeCompilationFuel branchType) branchType⟩, i), ?_, ?_⟩
          · exact List.mk_mem_zipIdx_iff_getElem?.mpr hAutomataGet
          · simp only [childPendingEdges, Finset.mem_image]
            exact ⟨childEdge, hChildEdgeMem, rfl⟩
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel branchType) branchType le_rfl childEdge hChildEdgeMem t r
                hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
                (.xoffer elseType branches) hWhole i action branchType hBranchesEq
                (hBranchFuelStrict (action, branchType) hBranchMem) t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child (i + 1) q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.xoffer elseType branches)
        (compileType signature (.xoffer elseType branches)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hAutomataGet :
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2))[i]? =
            some (action, compileTypeFuel signature (typeCompilationFuel branchType)
              branchType) :=
        (branches_map_getElem?_eq_some_iff signature branches i action
          (compileTypeFuel signature (typeCompilationFuel branchType) branchType)).mpr
          ⟨branchType, hBranchesEq, rfl⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer elseType branches) (.child (i + 1) q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child (i + 1) q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildExclusiveOfferAutomaton_outgoing_branch signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2))
          i action (compileTypeFuel signature (typeCompilationFuel branchType) branchType)
          hAutomataGet q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature branchType).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature branchType q childEdge.target
          env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.xoffer elseType branches) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel branchType) branchType le_rfl childEdge hChildEdgeMem t r
                hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
                (.xoffer elseType branches) hWhole i action branchType hBranchesEq
                (hBranchFuelStrict (action, branchType) hBranchMem) t hStateMem]
      have hTargetEq : state' = .child (i + 1) childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_xoffer_cases signature elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain, hStateEqAgain,
          hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · exact absurd (by simpa [childState] using hStateEqAgain : (i + 1 : Nat) = 0)
          (by omega)
      · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
            .child (i + 1) childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        injection hSndEq with hIEq hQEq
        have hIAgainEq : iAgain = i := by omega
        subst hIAgainEq
        have hPairEq : (actionAgain, branchTypeAgain) = (action, branchType) := by
          have h := hBranchesEqAgain.symm.trans hBranchesEq
          simpa using h
        have hBranchTypeAgainEq : branchTypeAgain = branchType := congrArg Prod.snd hPairEq
        rw [hBranchTypeAgainEq, hQEq] at hBranchRelatedAgain
        exact (hBranchesIH action branchType hBranchMem hBranchRelated hBranchSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hBranchRelatedAgain⟩

/-- Step correspondence for the fully-unselected parallel singleton-offer product generated below a conjunctive offer, by induction on the finite branch list. -/
theorem correspondence_parallelTypeBranches_stepIff
    (signature : TypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) →
      StepIffStatement signature (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      exact correspondence_skip_stepIff signature
  | cons branch rest ih =>
      intro hBranchesIH
      rcases branch with ⟨action, processType⟩
      have hProcessTypeIH : StepIffStatement signature processType :=
        hBranchesIH action processType List.mem_cons_self
      have hSingletonIH : ∀ a b, (a, b) ∈ [(action, processType)] →
          StepIffStatement signature b := by
        intro a b hMem
        rw [List.mem_singleton] at hMem
        rw [show b = processType from congrArg Prod.snd hMem]
        exact hProcessTypeIH
      have hRestBranchesIH : ∀ a b, (a, b) ∈ rest → StepIffStatement signature b :=
        fun a b hMem => hBranchesIH a b (List.mem_cons_of_mem _ hMem)
      cases rest with
      | nil =>
          rw [show parallelTypeBranches [(action, processType)] =
            PactType.xoffer PactType.skip [(action, processType)] by
              simp [parallelTypeBranches, singletonTypeXOffer]]
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_xoffer_stepIff signature .skip [(action, processType)]
            (correspondence_skip_stepIff signature) hSingletonIH hRelated hSymbol
      | cons next tail =>
          have hRestIH : StepIffStatement signature (parallelTypeBranches (next :: tail)) :=
            ih hRestBranchesIH
          rw [show parallelTypeBranches ((action, processType) :: next :: tail) =
            .par (PactType.xoffer PactType.skip [(action, processType)])
              (parallelTypeBranches (next :: tail)) ∅ by
              simp [parallelTypeBranches, singletonTypeXOffer]]
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_par_stepIff signature (.xoffer .skip [(action, processType)])
            (parallelTypeBranches (next :: tail)) ∅
            (correspondence_xoffer_stepIff signature .skip [(action, processType)]
              (correspondence_skip_stepIff signature) hSingletonIH)
            hRestIH hRelated hSymbol

/-- Step correspondence for the parallel singleton-offer product generated for a
specific enabled branch below a conjunctive offer, by induction on the finite
branch list, reusing the exclusive-offer/sequence/parallel cases already proved. -/
theorem correspondence_parallelTypeBranchesSelecting_stepIff
    (signature : TypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) →
      ∀ selected ∈ branches,
        StepIffStatement signature (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil => intro _ selected hMem; exact absurd hMem List.not_mem_nil
  | cons branch rest ih =>
      intro hBranchesIH selected hMem
      rcases branch with ⟨action, processType⟩
      have hProcessTypeIH : StepIffStatement signature processType :=
        hBranchesIH action processType List.mem_cons_self
      have hSingletonIH : ∀ a b, (a, b) ∈ [(action, processType)] →
          StepIffStatement signature b := by
        intro a b hMem'
        rw [List.mem_singleton] at hMem'
        rw [show b = processType from congrArg Prod.snd hMem']
        exact hProcessTypeIH
      have hRestBranchesIH : ∀ a b, (a, b) ∈ rest → StepIffStatement signature b :=
        fun a b hMem' => hBranchesIH a b (List.mem_cons_of_mem _ hMem')
      rw [List.mem_cons] at hMem
      cases rest with
      | nil =>
          intro residual residual' state env label offers hRelated hSymbol
          rcases hMem with hEq | hMem
          · rw [show parallelTypeBranchesSelecting selected [(action, processType)] =
              .seq (.message action.1 action.2) processType by
                simp [parallelTypeBranchesSelecting, selectedTypeBranch, ← hEq]] at hRelated ⊢
            exact correspondence_seq_stepIff signature (.message action.1 action.2) processType
              (correspondence_message_stepIff signature action.1 action.2)
              hProcessTypeIH hRelated hSymbol
          · exact absurd hMem (List.not_mem_nil (a := selected))
      | cons next tail =>
          intro residual residual' state env label offers hRelated hSymbol
          by_cases hSelf : (action, processType) = selected
          · have hRestPlainIH : StepIffStatement signature (parallelTypeBranches (next :: tail)) :=
              correspondence_parallelTypeBranches_stepIff signature (next :: tail) hRestBranchesIH
            rw [show parallelTypeBranchesSelecting selected ((action, processType) :: next :: tail) =
              .par (.seq (.message action.1 action.2) processType)
                (parallelTypeBranches (next :: tail)) ∅ by
                simp [parallelTypeBranchesSelecting, selectedTypeBranch, hSelf]] at hRelated ⊢
            exact correspondence_par_stepIff signature
              (.seq (.message action.1 action.2) processType)
              (parallelTypeBranches (next :: tail)) ∅
              (correspondence_seq_stepIff signature (.message action.1 action.2) processType
                (correspondence_message_stepIff signature action.1 action.2)
                hProcessTypeIH)
              hRestPlainIH hRelated hSymbol
          · rcases hMem with hEq | hMemRest
            · exact absurd hEq.symm hSelf
            · have hRestIH : StepIffStatement signature
                  (parallelTypeBranchesSelecting selected (next :: tail)) :=
                ih hRestBranchesIH selected hMemRest
              rw [show parallelTypeBranchesSelecting selected ((action, processType) :: next :: tail) =
                .par (PactType.xoffer PactType.skip [(action, processType)])
                  (parallelTypeBranchesSelecting selected (next :: tail)) ∅ by
                  simp [parallelTypeBranchesSelecting, singletonTypeXOffer, hSelf]] at hRelated ⊢
              exact correspondence_par_stepIff signature (.xoffer .skip [(action, processType)])
                (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                (correspondence_xoffer_stepIff signature .skip [(action, processType)]
                  (correspondence_skip_stepIff signature) hSingletonIH)
                hRestIH hRelated hSymbol

set_option maxHeartbeats 4000000 in
/-- Step correspondence for conjunctive offer `⋀(τ0,B)`. -/
theorem correspondence_offer_stepIff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseIH : StepIffStatement signature elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) :
    StepIffStatement signature (.offer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- A generated branch commit is a finite parallel product already covered
  -- by the exclusive-offer/sequence/parallel cases, so a finite induction
  -- over the branch list gives it a correspondence the way `hElseIH` gives
  -- `τ0`'s. Given this, now we need to prove the root's fire/else/wait edges
  -- match the three offer rules.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hElseFuelStrict : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hBranchFuelStrict : ∀ selected : BareMessage × PactType,
      typeCompilationFuel (parallelTypeBranchesSelecting selected branches) + 1 ≤
        typeCompilationFuel (.offer elseType branches) := by
    intro selected
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hFuelEq : typeCompilationFuel (.offer elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches) =
        buildSelectedConjunctiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))) := by
    rw [hFuelEq]
    show buildSelectedConjunctiveOfferAutomaton signature branches
        (compileTypeFuel signature
          (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)) elseType)
        (branches.map fun selected => (selected.1, compileTypeFuel signature
          (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
          (parallelTypeBranchesSelecting selected branches))) =
      buildSelectedConjunctiveOfferAutomaton signature branches
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
        (branches.map fun selected => (selected.1, compileTypeFuel signature
          (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches)))
    congr 1
    · exact compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl
    · apply List.map_congr_left
      intro selected _
      congr 1
      exact compileTypeFuel_eq_of_sufficient signature
        (parallelTypeBranchesSelecting selected branches)
        (by
          show typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _)
        le_rfl
  rcases relationMembership_offer_cases signature elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, selected, q, hSelectedEq, hStateEq, hBranchRelated⟩
  · -- root case: `residual` represents `⋀(τ0,B)` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureElseEq : computeFutureOf signature (.offer elseType branches)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial) = typeFutureOffers elseType := by
      rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
        (.offer elseType branches) hWhole hElseFuelStrict
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      TypeAlphabet.environments_subset_localEnvironments signature
        (transitionAlphabet_environment_mem signature hSignatureSymbol)
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRootRelated : relationMembership
        (buildRelationSet (.offer elseType branches)
          (compileType signature (.offer elseType branches)))
        (.offer elseType branches) TypeAutomatonState.root := by
      simpa using hRelated
    have hRootFuture : computeFutureOf signature (.offer elseType branches)
        TypeAutomatonState.root = typeFutureOffers (.offer elseType branches) :=
      helper_h15_future_offers_agree signature hRootRelated
    constructor
    · intro hStep
      obtain ⟨-, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hOffers
      generalize hTargetEq : residual' = actualTarget at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers with
      | offer_some _ _ _ enabled hPremise =>
          obtain ⟨hWF', hEnabledMem, hEnabled⟩ := hPremise
          obtain ⟨index, hSelectedGet⟩ := List.mem_iff_getElem?.mp hEnabledMem
          have hFutureBranchEq : computeFutureOf signature (.offer elseType branches)
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) =
              typeFutureOffers (parallelTypeBranchesSelecting enabled branches) := by
            rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
              (.offer elseType branches) hWhole index enabled hSelectedGet
              (hBranchFuelStrict enabled)
              (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial
              (compileTypeFuel_initial_mem signature (typeCompilationFuel
                (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches) le_rfl)]
            show computeFutureOf signature (parallelTypeBranchesSelecting enabled branches)
              (compileType signature (parallelTypeBranchesSelecting enabled branches)).initial =
              typeFutureOffers (parallelTypeBranchesSelecting enabled branches)
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial (parallelTypeBranchesSelecting enabled branches)
                (compileType signature (parallelTypeBranchesSelecting enabled branches)))
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk ∅ (typeFutureOffers
                  (parallelTypeBranchesSelecting enabled branches))) ∈
                signature.transitionAlphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hEnabledPending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := (∅ : Finset BareMessage),
                  future := FutureSpec.at (childState (index + 1) (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches)).initial) ∅,
                  target := childState (index + 1) (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches)).initial } :
                PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union]
            refine Or.inl (Or.inl (Or.inr ?_))
            rw [mem_foldl_union_iff]
            refine Or.inr ⟨(⟨enabled.1, compileTypeFuel signature
              (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
              (parallelTypeBranchesSelecting enabled branches)⟩, index), ?_, ?_⟩
            · exact List.mk_mem_zipIdx_iff_getElem?.mpr
                ((branches_map_selecting_getElem?_eq_some_iff signature branches index enabled.1
                  (compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                    (parallelTypeBranchesSelecting enabled branches))).mpr
                  ⟨enabled.2, hSelectedGet, rfl⟩)
            · simp only [Finset.mem_image, Finset.mem_filter]
              exact ⟨env, ⟨hEnvMem, hEnabled⟩, rfl⟩
          have hEdgeFact : (compileType signature (.offer elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer elseType branches)
              TypeAutomatonState.root (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches))) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hEnabledPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureBranchEq
          have hEnabledStep : DecoratedTypeTransition env (.offer elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (parallelTypeBranchesSelecting enabled branches) :=
            ⟨TypeTransition.offer_some env elseType branches enabled
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env elseType branches enabled
                ⟨hWF, hEnabledMem, hEnabled⟩⟩
          refine ⟨.child (index + 1) (compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
            (parallelTypeBranchesSelecting enabled branches)).initial, hEdgeFact, ?_⟩
          exact relationMembership_of_step_edge_unique (.offer elseType branches)
            (compileType signature (.offer elseType branches)) hRelated hEdgeFact hEnabledStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hEnabledStep)
      | offer_else _ _ _ hPremise =>
          obtain ⟨hWF', hNoImmediate, hResolvedNeeds⟩ := hPremise
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType)) ∈
                signature.transitionAlphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hElsePending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := typeBranchActions branches,
                  future := FutureSpec.at (childState 0 (compileTypeFuel signature
                    (typeCompilationFuel elseType) elseType).initial) ∅,
                  target := childState 0 (compileTypeFuel signature
                    (typeCompilationFuel elseType) elseType).initial } :
                PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            exact Or.inr ⟨env, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
          have hEdgeFact : (compileType signature (.offer elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
                elseType).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer elseType branches)
              TypeAutomatonState.root (.child 0 (compileTypeFuel signature
                (typeCompilationFuel elseType) elseType).initial) env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hElsePending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureElseEq
          have hElseStep : DecoratedTypeTransition env (.offer elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeBranchActions branches)
                (typeFutureOffers elseType)) elseType :=
            ⟨TypeTransition.offer_else env elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
              TypeOffers.offer_else env elseType branches
                ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
          refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
            elseType).initial, hEdgeFact, ?_⟩
          exact relationMembership_of_step_edge_unique (.offer elseType branches)
            (compileType signature (.offer elseType branches)) hRelated hEdgeFact hElseStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hElseStep)
      | offer_wait _ _ _ hPremise =>
          obtain ⟨hWF', hNoImmediate, hUnresolved, hClock⟩ := hPremise
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk (typeWaitingOffers env branches)
                  (typeFutureOffers (.offer elseType branches) \
                    typeWaitingOffers env branches)) ∈ signature.transitionAlphabet := by
            rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
            exact hSignatureSymbol
          have hWaitPending :
              ({ source := TypeAutomatonState.root, environment := env,
                  label := AutomatonConstructionLabel.visible TypeLabel.silent,
                  current := typeWaitingOffers env branches,
                  future := FutureSpec.at TypeAutomatonState.root
                    (typeWaitingOffers env branches),
                  target := TypeAutomatonState.root } : PendingAutomatonEdge) ∈
                (buildSelectedConjunctiveOfferAutomaton signature branches
                  (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
                  (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                    (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                    (parallelTypeBranchesSelecting selected' branches)))).edges := by
            simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨env, ⟨hEnvMem, hClock, hNoImmediate, hUnresolved⟩, ?_⟩)
            simp [typeWaitingOffers]
          have hEdgeFact : (compileType signature (.offer elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer elseType branches) \
                  typeWaitingOffers env branches)) TypeAutomatonState.root := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer elseType branches)
              TypeAutomatonState.root TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer elseType branches) \
                  typeWaitingOffers env branches)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hWaitPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            show computeFutureOf signature (.offer elseType branches) TypeAutomatonState.root \
              typeWaitingOffers env branches = typeFutureOffers (.offer elseType branches) \
                typeWaitingOffers env branches
            rw [hRootFuture]
          have hWaitStep : DecoratedTypeTransition env (.offer elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer elseType branches) \
                  typeWaitingOffers env branches)) (.offer elseType branches) :=
            ⟨TypeTransition.offer_wait env elseType branches
              ⟨hWF, hNoImmediate, hUnresolved, hClock⟩,
              TypeOffers.offer_wait env elseType branches
                ⟨hWF, hNoImmediate, hUnresolved, hClock⟩⟩
          refine ⟨TypeAutomatonState.root, hEdgeFact, ?_⟩
          exact relationMembership_of_step_edge_unique (.offer elseType branches)
            (compileType signature (.offer elseType branches)) hRelated hEdgeFact hWaitStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hWaitStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer elseType branches) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hRootSource : pendingEdge.source = TypeAutomatonState.root := hPSource
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union] at hPendingMem
      rcases hPendingMem with ((((hElse | hIndexed) | hEnabledFamily) | hWait) | hResolved2)
      · exfalso
        simp only [childPendingEdges, Finset.mem_image] at hElse
        obtain ⟨childEdge, _, hEq⟩ := hElse
        rw [← hEq] at hRootSource
        simp [childPendingEdge, childState] at hRootSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, _, hNewEdge⟩
        · simp at hEmpty
        · simp only [childPendingEdges, Finset.mem_image] at hNewEdge
          obtain ⟨childEdge, _, hEq⟩ := hNewEdge
          rw [← hEq] at hRootSource
          simp [childPendingEdge, childState] at hRootSource
      · -- fire family: reconstructs `offer_some`
        rw [mem_foldl_union_iff] at hEnabledFamily
        rcases hEnabledFamily with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
        · simp at hEmpty
        · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
          obtain ⟨⟨branchAction, automaton⟩, index⟩ := indexed
          rcases hNewEdge with ⟨environment, ⟨hEnvMem, hEnabled⟩, rfl⟩
          have hEnvEq : environment = env := hPEnv
          subst environment
          have hIndexedGet :
              (branches.map fun selected' => (selected'.1, compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
                (parallelTypeBranchesSelecting selected' branches)))[index]? =
                some (branchAction, automaton) :=
            List.mk_mem_zipIdx_iff_getElem?.mp hIndexedEntry
          obtain ⟨branchType', hSelectedGet, hAutEq⟩ :=
            (branches_map_selecting_getElem?_eq_some_iff signature branches index branchAction
              automaton).mp hIndexedGet
          have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
          have hEnabledMem : (branchAction, branchType') ∈ branches :=
            List.mem_iff_getElem?.mpr ⟨index, hSelectedGet⟩
          simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
          have hLabelEq : label = TypeLabel.silent := by
            have h := hPLabel; simp at h; exact h.symm
          have hCurrentEq : current = ∅ := hPCurrent.symm
          have hTargetEq : state' = .child (index + 1)
              (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting (branchAction, branchType')
                  branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial := by
            rw [← hPTarget, ← hAutEq]
          rw [hTargetEq] at hTargetRelated
          have hFutureEq : future =
              typeFutureOffers (parallelTypeBranchesSelecting
                (branchAction, branchType') branches) := by
            rw [← hPFuture, Finset.sdiff_empty, ← hAutEq]
            rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
              (.offer elseType branches) hWhole index (branchAction, branchType') hSelectedGet
              (hBranchFuelStrict (branchAction, branchType'))
              (compileTypeFuel signature (typeCompilationFuel
                (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial
              (compileTypeFuel_initial_mem signature (typeCompilationFuel
                (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                (parallelTypeBranchesSelecting (branchAction, branchType') branches) le_rfl)]
            show computeFutureOf signature
              (parallelTypeBranchesSelecting (branchAction, branchType') branches)
              (compileType signature
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)).initial =
              typeFutureOffers (parallelTypeBranchesSelecting
                (branchAction, branchType') branches)
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                (compileType signature
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches)))
          rcases relationMembership_offer_cases signature elseType branches hTargetRelated
            with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
              ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
                hBranchRelatedAgain⟩
          · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
          · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
              index + 1) (by omega)
          · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
                .child (index + 1) (compileTypeFuel signature (typeCompilationFuel
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                  (parallelTypeBranchesSelecting (branchAction, branchType')
                    branches)).initial := by
              simpa [childState] using hStateEqAgain.symm
            injection hSndEq with hIEq hQEq
            have hIAgainEq : iAgain = index := by omega
            subst hIAgainEq
            have hPairEq : selectedAgain = (branchAction, branchType') := by
              have h := hSelectedEqAgain.symm.trans hSelectedGet
              simpa using h
            rw [hPairEq, hQEq] at hBranchRelatedAgain
            have hResidualEq : residual' =
                parallelTypeBranchesSelecting (branchAction, branchType') branches :=
              relationMembership_functional
                (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                (compileType signature
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches))
                hBranchRelatedAgain
                (buildRelationSet_initial
                  (parallelTypeBranchesSelecting (branchAction, branchType') branches)
                  (compileType signature
                    (parallelTypeBranchesSelecting (branchAction, branchType') branches)))
            rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
            exact ⟨TypeTransition.offer_some env elseType branches (branchAction, branchType')
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env elseType branches (branchAction, branchType')
                ⟨hWF, hEnabledMem, hEnabled⟩⟩
      · -- wait family: reconstructs `offer_wait`
        simp only [Finset.mem_image, Finset.mem_filter] at hWait
        rcases hWait with ⟨environment, ⟨hEnvMem, hClock, hNoImmediate, hUnresolved⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = typeWaitingOffers env branches := hPCurrent.symm
        have hTargetEq : state' = TypeAutomatonState.root := by rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers (.offer elseType branches) \
            typeWaitingOffers env branches := by
          rw [← hPFuture, hRootFuture]
          rfl
        rcases relationMembership_offer_cases signature elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
              hBranchRelatedAgain⟩
        · simp only [Prod.mk.injEq] at hRootAgain
          have hResidualEq : residual' = .offer elseType branches := hRootAgain.1
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.offer_wait env elseType branches
            ⟨hWF, hNoImmediate, hUnresolved, hClock⟩,
            TypeOffers.offer_wait env elseType branches
              ⟨hWF, hNoImmediate, hUnresolved, hClock⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child 0 qAgain) (by simp)
        · exact absurd (by simpa [childState] using hStateEqAgain :
            (TypeAutomatonState.root : TypeAutomatonState) = .child (iAgain + 1) qAgain)
            (by simp)
      · -- else family: reconstructs `offer_else`
        simp only [Finset.mem_image, Finset.mem_filter] at hResolved2
        rcases hResolved2 with ⟨environment, ⟨hEnvMem, hNoImmediate, hResolvedNeeds⟩, rfl⟩
        have hEnvEq : environment = env := hPEnv
        subst environment
        have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
        simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        have hTargetEq : state' = .child 0
            (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
          rw [← hPTarget]
        rw [hTargetEq] at hTargetRelated
        have hFutureEq : future = typeFutureOffers elseType := by
          rw [← hPFuture, Finset.sdiff_empty]
          exact hFutureElseEq ▸ rfl
        rcases relationMembership_offer_cases signature elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
              hBranchRelatedAgain⟩
        · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
        · have hQAgainEq : qAgain =
              (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial := by
            simpa [childState] using hStateEqAgain.symm
          rw [hQAgainEq] at hElseRelatedAgain
          have hResidualEq : residual' = elseType :=
            relationMembership_functional elseType (compileType signature elseType)
              hElseRelatedAgain (buildRelationSet_initial elseType
                (compileType signature elseType))
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.offer_else env elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.offer_else env elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
        · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
            iAgain + 1) (by omega)
  · -- else-child case: `hElseIH` reconstructs the step directly
    have hState' : state = .child 0 q := by simpa using hStateEq
    subst state
    have hElseSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈ (compileType signature elseType).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hElseIH hElseRelated hElseSymbol).mp hStep
      have hOuterEdge : (compileType signature (.offer elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer elseType branches)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hElseSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature elseType q q'
          env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature elseType hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union, childPendingEdges, Finset.mem_image]
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
                (.offer elseType branches) hWhole hElseFuelStrict t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.offer elseType branches)
        (compileType signature (.offer elseType branches)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer elseType branches) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child 0 q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches))) q pendingEdge).mp
          ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature elseType).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature elseType q childEdge.target env
          label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.offer elseType branches) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel elseType) elseType le_rfl childEdge hChildEdgeMem t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
                (.offer elseType branches) hWhole hElseFuelStrict t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain, hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · have hQAgainEq : qAgain = childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        rw [hQAgainEq] at hElseRelatedAgain
        exact (hElseIH hElseRelated hElseSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hElseRelatedAgain⟩
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
          iAgain + 1) (by omega)
  · -- branch-child case: the generated commit type's own correspondence (from
    -- the exclusive-offer/sequence/parallel cases) reconstructs the step directly
    have hState' : state = .child (i + 1) q := by simpa using hStateEq
    subst state
    have hSelectedMem : selected ∈ branches :=
      List.mem_iff_getElem?.mpr ⟨i, hSelectedEq⟩
    have hBranchIH : StepIffStatement signature
        (parallelTypeBranchesSelecting selected branches) :=
      correspondence_parallelTypeBranchesSelecting_stepIff signature branches hBranchesIH
        selected hSelectedMem
    have hBranchSymbol : TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current future) ∈
        (compileType signature (parallelTypeBranchesSelecting selected branches)).alphabet := by
      change TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet
      exact hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hBranchIH hBranchRelated hBranchSymbol).mp hStep
      have hAutomataGet :
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))[i]? =
            some (selected.1, compileTypeFuel signature (typeCompilationFuel
              (parallelTypeBranchesSelecting selected branches))
              (parallelTypeBranchesSelecting selected branches)) := by
        rw [List.getElem?_map, hSelectedEq]
        rfl
      have hOuterEdge : (compileType signature (.offer elseType branches)).HasEdge
          (.child (i + 1) q) env label (TypeOfferSummary.mk current future)
          (.child (i + 1) q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer elseType branches)
          (.child (i + 1) q) (.child (i + 1) q') env label
          (TypeOfferSummary.mk current future)
          (by simpa [compileType] using hBranchSymbol)]
        rw [hWhole]
        have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
          (parallelTypeBranchesSelecting selected branches)
          q q' env label (TypeOfferSummary.mk current future)
          (compileType_hasEdge_symbol_mem signature
            (parallelTypeBranchesSelecting selected branches) hChildEdge)).mp hChildEdge
        obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent, hCFuture,
          hCTarget⟩ := hChildResolved
        refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
            Finset.mem_union]
          refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
          rw [indexedFragmentEdges, mem_foldl_union_iff]
          refine Or.inr ⟨(⟨selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches)⟩, i), ?_, ?_⟩
          · exact List.mk_mem_zipIdx_iff_getElem?.mpr hAutomataGet
          · simp only [childPendingEdges, Finset.mem_image]
            exact ⟨childEdge, hChildEdgeMem, rfl⟩
        · simp [childPendingEdge, childState, hCSource]
        · simp [childPendingEdge, hCEnv]
        · simp [childPendingEdge, hCLabel]
        · simp [childPendingEdge, hCCurrent]
        · cases hSpec : childEdge.future with
          | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) le_rfl childEdge hChildEdgeMem
                t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
                (.offer elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child (i + 1) q', hOuterEdge, ?_⟩
      exact relationMembership_of_step_edge_unique (.offer elseType branches)
        (compileType signature (.offer elseType branches)) hRelated hOuterEdge hStep
        (fun target hTargetStep => decoratedTypeTransition_target_unique hTargetStep hStep)
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hAutomataGet :
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))[i]? =
            some (selected.1, compileTypeFuel signature (typeCompilationFuel
              (parallelTypeBranchesSelecting selected branches))
              (parallelTypeBranchesSelecting selected branches)) := by
        rw [List.getElem?_map, hSelectedEq]
        rfl
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer elseType branches) (.child (i + 1) q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer elseType branches) hEdge)).mp hEdge
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      have hChildSource : pendingEdge.source = .child (i + 1) q := hPSource
      obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
        (buildSelectedConjunctiveOfferAutomaton_outgoing_branch signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected' => (selected'.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected' branches))
            (parallelTypeBranchesSelecting selected' branches)))
          i selected.1 (compileTypeFuel signature (typeCompilationFuel
            (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))
          hAutomataGet q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
      have hInnerEdgeMem : (compileType signature
          (parallelTypeBranchesSelecting selected branches)).HasEdge q env label
          (TypeOfferSummary.mk current future) childEdge.target := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature
          (parallelTypeBranchesSelecting selected branches) q childEdge.target
          env label (TypeOfferSummary.mk current future)
          (by simpa [compileType] using
            compileType_hasEdge_symbol_mem signature (.offer elseType branches) hEdge)]
        refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
        · rw [← hPEnv, hChildEdgeEq]; rfl
        · rw [← hPLabel, hChildEdgeEq]; rfl
        · rw [← hPCurrent, hChildEdgeEq]; rfl
        · rw [← hPFuture, hChildEdgeEq]
          cases hSpec : childEdge.future with
          | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
          | «at» t r =>
              have hStateMem := compileTypeFuel_futureTargetsInStates signature
                (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
                (parallelTypeBranchesSelecting selected branches) le_rfl childEdge hChildEdgeMem
                t r hSpec
              simp only [childPendingEdge, childFutureSpec, hSpec, childState]
              rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
                (.offer elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) t hStateMem]
      have hTargetEq : state' = .child (i + 1) childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature elseType branches hTargetRelated with
        hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
        ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain, hBranchRelatedAgain⟩
      · exact absurd (congrArg Prod.snd hRootAgain) (by simp [childState])
      · exact absurd (by simpa [childState] using hStateEqAgain : (0 : Nat) =
          i + 1) (by omega)
      · have hSndEq : (TypeAutomatonState.child (iAgain + 1) qAgain) =
            .child (i + 1) childEdge.target := by
          simpa [childState] using hStateEqAgain.symm
        injection hSndEq with hIEq hQEq
        have hIAgainEq : iAgain = i := by omega
        subst hIAgainEq
        have hPairEq : selectedAgain = selected := by
          have h := hSelectedEqAgain.symm.trans hSelectedEq
          simpa using h
        rw [hPairEq, hQEq] at hBranchRelatedAgain
        exact (hBranchIH hBranchRelated hBranchSymbol).mpr
          ⟨childEdge.target, hInnerEdgeMem, hBranchRelatedAgain⟩

/-- Step correspondence for an open recursion-variable marker `X`, which never has a real step. -/
theorem correspondence_var_stepIff
    (signature : TypeAlphabet) (name : String) :
    StepIffStatement signature (.var name) := by
  intro residual residual' state env label offers hRelated hSymbol
  obtain ⟨hResidual, hState⟩ :=
    relationMembership_var_cases signature name hRelated
  subst hResidual
  subst hState
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label offers ∈ signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  constructor
  · intro hStep
    cases hStep.1
  · rintro ⟨state', hEdge, -⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge signature (.var name)
      TypeAutomatonState.root state' env label offers hSignatureSymbol] at hEdge
    obtain ⟨edge, hPending, -, -, hLabel, -, -, -⟩ := hEdge
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image] at hPending
    obtain ⟨environment, -, rfl⟩ := hPending
    simp at hLabel

/-- Step correspondence for all constructors, arranged as the Lemma 4.5 induction. -/
theorem correspondence_stepIff
    (signature : TypeAlphabet) :
    ∀ processType, StepIffStatement signature processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      cases processType with
      | message msg dir =>
          intro residual residual' state env label offers hRelated hSymbol
          -- Now prove the atomic action base case.
          exact correspondence_message_stepIff signature msg dir hRelated hSymbol
      | progress pid =>
          intro residual residual' state env label offers hRelated hSymbol
          -- Now prove the progress-marker base case.
          exact correspondence_progress_stepIff signature pid hRelated hSymbol
      | tock =>
          intro residual residual' state env label offers hRelated hSymbol
          -- Now prove the clock base case.
          exact correspondence_tock_stepIff signature hRelated hSymbol
      | skip =>
          intro residual residual' state env label offers hRelated hSymbol
          -- Now prove the skip base case.
          exact correspondence_skip_stepIff signature hRelated hSymbol
      | choice left right =>
          intro residual residual' state env label offers hRelated hSymbol
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right rfl hRelated hSymbol
          -- Now prove the ordinary-choice inductive case from both child hypotheses.
          exact correspondence_choice_stepIff signature left right hLeftIH
            hRightIH hRelated hSymbol
      | seq first second =>
          intro residual residual' state env label offers hRelated hSymbol
          have hFirstIH : StepIffStatement signature first := by
            have hFirstSize : sizeOf first < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf first) hFirstSize first rfl hRelated hSymbol
          have hSecondIH : StepIffStatement signature second := by
            have hSecondSize : sizeOf second < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf second) hSecondSize second rfl hRelated hSymbol
          -- Now prove the sequencing inductive case from both child hypotheses.
          exact correspondence_seq_stepIff signature first second hFirstIH
            hSecondIH hRelated hSymbol
      | par left right interface =>
          intro residual residual' state env label offers hRelated hSymbol
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right rfl hRelated hSymbol
          -- Now prove the parallel inductive case from both child hypotheses.
          exact correspondence_par_stepIff signature left right interface
            hLeftIH hRightIH hRelated hSymbol
      | var id =>
          intro residual residual' state env label offers hRelated hSymbol
          -- Now prove the variable marker case.
          exact correspondence_var_stepIff signature id hRelated hSymbol
      | recur id body =>
          intro residual residual' state env label offers hRelated hSymbol
          have hBodyIH : StepIffStatement signature body := by
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf body) hBodySize body rfl hRelated hSymbol
          -- Now prove the recursion inductive case from the body hypothesis.
          exact correspondence_recur_stepIff signature id body hBodyIH hRelated
            hSymbol
      | fairChoice id left right =>
          intro residual residual' state env label offers hRelated hSymbol
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right rfl hRelated hSymbol
          -- Now prove the fair-choice inductive case from both child hypotheses.
          exact correspondence_fairChoice_stepIff signature id left right
            hLeftIH hRightIH hRelated hSymbol
      | xoffer elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement signature branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType rfl hRelated
              hSymbol
          -- Now prove the external-offer inductive case from the else and branch hypotheses.
          exact correspondence_xoffer_stepIff signature elseType branches
            hElseIH hBranchesIH hRelated hSymbol
      | offer elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType rfl hRelated hSymbol
          have hBranchesIH :
              ∀ action branchType, (action, branchType) ∈ branches →
                StepIffStatement signature branchType := by
            intro action branchType hMember
            have hBranchSize : sizeOf branchType < n := by
              have hEntry : sizeOf (action, branchType) < sizeOf branches :=
                List.sizeOf_lt_of_mem hMember
              have hComponent : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              rw [← hSize]
              simp_wf
              omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType rfl hRelated
              hSymbol
          -- Now prove the internal-offer inductive case from the else and
          -- branch hypotheses; the per-branch generated-conjunction
          -- correspondence needs its own finite-branch induction, not this
          -- constructor's structural one (see `correspondence_offer_stepIff`).
          exact correspondence_offer_stepIff signature elseType branches
            hElseIH hBranchesIH hRelated hSymbol

end

end Pact
