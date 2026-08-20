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
  sorry

/-- Step correspondence for fair binary choice `τ1 ⧺η τ2`. -/
theorem correspondence_fairChoice_stepIff
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.fairChoice bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the same argument as ordinary choice,
  -- with the root edges reconstructing `fair_left`/`fair_right`.
  sorry

/-- Step correspondence for sequencing `τ1 ; τ2`. -/
theorem correspondence_seq_stepIff
    (signature : TypeAlphabet) (first second : PactType)
    (hFirstIH : StepIffStatement signature first)
    (hSecondIH : StepIffStatement signature second) :
    StepIffStatement signature (.seq first second) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove a `τ1`-step from `hFirstIH` matches
  -- `seq`/`seq_fuse` by its target, and `hSecondIH` handles a right state.
  sorry

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
  sorry

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
  sorry

/-- Step correspondence for conjunctive offer `⋀(τ0,B)`. -/
theorem correspondence_offer_stepIff
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseIH : StepIffStatement signature elseType) :
    StepIffStatement signature (.offer elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- A generated branch commit is a finite parallel product already covered
  -- by the exclusive-offer/sequence/parallel cases, so a finite induction
  -- over the branch list gives it a correspondence the way `hElseIH` gives
  -- `τ0`'s. Given this, now we need to prove the root's fire/else/wait edges
  -- match the three offer rules.
  sorry

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
          -- Now prove the internal-offer inductive case from the else
          -- hypothesis; the per-branch generated-conjunction correspondence
          -- needs its own finite-branch induction, not this constructor's
          -- structural one (see `correspondence_offer_stepIff`).
          exact correspondence_offer_stepIff signature elseType branches
            hElseIH hRelated hSymbol

end

end Pact
