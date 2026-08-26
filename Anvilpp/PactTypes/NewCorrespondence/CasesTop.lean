import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers
import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Top
import Anvilpp.PactTypes.NewCorrespondence.Helpers.AlphabetPreservation

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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.skip alphabet)
          (compileType signature (.skip alphabet)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.skip alphabet)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.skip alphabet)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.skip alphabet)
            (compileType signature (.skip alphabet)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := hEnvironment
  have hWellFormed := localEnvironment_wellFormed signature hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_skip_cases signature alphabet
      hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases hStep with ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ _ conditions =>
        cases hOffers with
        | skip _ _ =>
            have hEdge := NewCorrespondence.compileType_skip_edge signature
              (alphabet := alphabet) hLocal conditions.2 hSignatureSymbol
            exact ⟨.root, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_skip_cases signature alphabet
      hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases NewCorrespondence.compileType_skip_edge_cases signature
      (alphabet := alphabet) hEdge with
      ⟨_hSource, hTarget, hLabel, hCurrent, hFuture, hClock⟩
    subst label
    subst current
    subst future
    subst state'
    have hTargetAccepting :
        TypeAutomatonState.root ∈
          (compileType signature (.skip alphabet)).accepting := by
      simp [compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
    have hResidualTarget : residual' = .skip alphabet :=
      (NewCorrespondence.relationMembership_skip_cases signature alphabet
        hTargetRelated).1
    subst residual'
    exact ⟨TypeTransition.skip env alphabet ⟨hWellFormed, hClock⟩,
      TypeOffers.skip env alphabet ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for an atomic message type `a`.

PDF structure, Lemma 4.5 atomic action case:
* related states: `q0` represents `a`, `qf` represents `skip`;
* forward at `q0`: if `Need(a)` is immediate, use the fire family to `qf`;
  otherwise in a non-clock environment use the waiting self-loop at `q0`;
* forward at `qf`: reduce to the `skip` idle case;
* backward: every public edge is in the fire, wait, or final-idle family, and
  its guard reconstructs the corresponding semantic rule. -/
theorem correspondence_message_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.message alphabet msg dir)
          (compileType signature (.message alphabet msg dir)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.message alphabet msg dir)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.message alphabet msg dir)).HasEdge state env label
          offers state' ∧
        relationMembership
          (buildRelationSet (.message alphabet msg dir)
            (compileType signature (.message alphabet msg dir)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := hEnvironment
  have hWellFormed := localEnvironment_wellFormed signature hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_message_cases signature alphabet
      msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | action _ _ _ _ conditions =>
          have hFields : current = {(msg, dir)} ∧ future = ∅ := by
            generalize hLabelEq :
              TypeLabel.message msg dir = actualLabel at hOffers
            cases hOffers
            all_goals simp_all [Finset.ext_iff]
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.message alphabet msg dir)
                (TypeLabel.message msg dir)
                (TypeOfferSummary.mk {(msg, dir)} ∅) (.skip alphabet) :=
            ⟨TypeTransition.action env alphabet msg dir conditions,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := NewCorrespondence.compileType_message_action_edge
            signature (alphabet := alphabet) msg dir
            hLocal conditions.2 hSignatureSymbol
          refine ⟨.final, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
      | action_wait _ _ _ _ conditions =>
          have hFields : current = {(msg, dir)} ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
            cases hOffers
            all_goals simp_all [typeFutureOffers, typeFutureOffersFuel,
              Finset.ext_iff]
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.message alphabet msg dir)
                TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅)
                (.message alphabet msg dir) :=
            ⟨TypeTransition.action_wait env alphabet msg dir conditions,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := NewCorrespondence.compileType_message_wait_edge
            signature (alphabet := alphabet) msg dir
            hLocal conditions.2.1 conditions.2.2 hSignatureSymbol
          refine ⟨.root, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := NewCorrespondence.compileType_message_final_edge
                signature (alphabet := alphabet) msg dir
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_message_cases signature alphabet
      msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_message_edge_cases
        signature (alphabet := alphabet) msg dir hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.message alphabet msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_message_cases signature
              alphabet msg dir hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.action env alphabet msg dir
            ⟨hWellFormed, hNeed⟩,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env alphabet msg dir ⟨hWellFormed, hNeed⟩⟩
      · rcases hWait with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock, hNoNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .message alphabet msg dir := by
          rcases NewCorrespondence.relationMembership_message_cases signature
              alphabet msg dir
              hTargetRelated with hTargetRoot | hTargetFinal
          · exact hTargetRoot.1
          · rcases hTargetFinal with ⟨_, hStateTarget⟩
            simp at hStateTarget
        subst residual'
        exact ⟨TypeTransition.action_wait env alphabet msg dir
            ⟨hWellFormed, hNoNeed, hClock⟩,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action_wait env alphabet msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_message_edge_cases
        signature (alphabet := alphabet) msg dir hEdge
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
              (compileType signature (.message alphabet msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_message_cases signature
              alphabet msg dir hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env alphabet ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for the clock type `#`.

PDF structure, Lemma 4.5 clock case:
* related states: `q0` represents `#`, `qf` represents `skip`;
* clock environment: the semantic type emits `#` and the compiler fire edge
  reaches `qf`, with empty offer pair;
* non-clock environment: both semantics and automaton wait silently at `q0`;
* final state: both presentations use the non-clock idle behavior of `skip`;
* backward: the fire, wait, and idle edge families are exhaustive. -/
theorem correspondence_tock_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.tock alphabet)
          (compileType signature (.tock alphabet)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.tock alphabet)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.tock alphabet)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.tock alphabet)
            (compileType signature (.tock alphabet)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := hEnvironment
  have hWellFormed := localEnvironment_wellFormed signature hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_tock_cases signature alphabet
      hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | cycle _ _ conditions =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.tock = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.tock alphabet) TypeLabel.tock
                (TypeOfferSummary.mk ∅ ∅) (.skip alphabet) :=
            ⟨TypeTransition.cycle env alphabet conditions,
              TypeOffers.cycle env alphabet conditions⟩
          have hEdge := NewCorrespondence.compileType_tock_action_edge
            signature (alphabet := alphabet) hLocal
            conditions.2 hSignatureSymbol
          refine ⟨.final, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
      | cycle_wait _ _ conditions =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq : TypeLabel.silent = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.tock alphabet) TypeLabel.silent
                (TypeOfferSummary.mk ∅ ∅) (.tock alphabet) :=
            ⟨TypeTransition.cycle_wait env alphabet conditions,
              TypeOffers.cycle_wait env alphabet conditions⟩
          have hEdge := NewCorrespondence.compileType_tock_wait_edge
            signature (alphabet := alphabet) hLocal
            conditions.2 hSignatureSymbol
          refine ⟨.root, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := NewCorrespondence.compileType_tock_final_edge
                signature (alphabet := alphabet) hLocal
                conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_tock_cases signature alphabet
      hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_tock_edge_cases
        signature (alphabet := alphabet) hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.tock alphabet)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_tock_cases signature
              alphabet hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.cycle env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.cycle env alphabet ⟨hWellFormed, hClock⟩⟩
      · rcases hWait with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .tock alphabet := by
          rcases NewCorrespondence.relationMembership_tock_cases signature
              alphabet hTargetRelated with hTargetRoot | hTargetFinal
          · exact hTargetRoot.1
          · rcases hTargetFinal with ⟨_, hStateTarget⟩
            simp at hStateTarget
        subst residual'
        exact ⟨TypeTransition.cycle_wait env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.cycle_wait env alphabet ⟨hWellFormed, hClock⟩⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_tock_edge_cases
        signature (alphabet := alphabet) hEdge
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
              (compileType signature (.tock alphabet)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_tock_cases signature
              alphabet hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env alphabet ⟨hWellFormed, hClock⟩⟩

/-- Step correspondence for a progress marker `$t`.

PDF structure, Lemma 4.5 progress case:
* related states: `q0` represents `$t`, `qf` represents `skip`;
* forward at `q0`: the semantic progress step reaches `skip` with empty
  current and future offers, matching the compiler progress edge to `qf`;
* forward at `qf`: reduce to the `skip` idle case;
* backward: every public edge is either the progress family or the final idle
  family, and reconstructs the corresponding semantic step. -/
theorem correspondence_progress_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.progress alphabet pid) (compileType signature (.progress alphabet pid)))
        residual state)
    (hSymbol :
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈
        (compileType signature (.progress alphabet pid)).alphabet) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature (.progress alphabet pid)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.progress alphabet pid)
            (compileType signature (.progress alphabet pid)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabet_environment_mem signature hSignatureSymbol
  have hLocal := hEnvironment
  have hWellFormed := localEnvironment_wellFormed signature hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_progress_cases signature alphabet
      pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | progress _ _ _ _ =>
          have hFields : current = ∅ ∧ future = ∅ := by
            generalize hLabelEq :
              TypeLabel.progress pid = actualLabel at hOffers
            cases hOffers
            all_goals simp_all
          obtain ⟨rfl, rfl⟩ := hFields
          let decorated :
              DecoratedTypeTransition env (.progress alphabet pid)
                (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅)
                (.skip alphabet) :=
            ⟨TypeTransition.progress env alphabet pid hWellFormed,
              TypeOffers.progress env alphabet pid hWellFormed⟩
          have hEdge := NewCorrespondence.compileType_progress_action_edge
            signature (alphabet := alphabet) pid
            hLocal hSignatureSymbol
          refine ⟨.final, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | skip _ _ conditions =>
          cases hOffers with
          | skip _ _ =>
              have hEdge := NewCorrespondence.compileType_progress_final_edge
                signature (alphabet := alphabet) pid
                hLocal conditions.2 hSignatureSymbol
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_progress_cases signature alphabet
      pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        signature (alphabet := alphabet) pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨_hSource, hTarget, hLabel, hCurrent,
          hFuture⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType signature (.progress alphabet pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_progress_cases signature
              alphabet pid hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.progress env alphabet pid hWellFormed,
          TypeOffers.progress env alphabet pid hWellFormed⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        signature (alphabet := alphabet) pid hEdge
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
              (compileType signature (.progress alphabet pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_progress_cases signature
              alphabet pid hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env alphabet ⟨hWellFormed, hClock⟩⟩

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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.choice alphabet left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's selection edges match the
  -- choice rule, and `hLeftIH`/`hRightIH` handle everything below the root.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
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
      typeCompilationFuel left + 1 ≤ typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_choice_cases signature alphabet left right hRelated with
    hRoot | ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · -- root case: `residual` represents `τ1 + τ2` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureLeftEq : computeFutureOf signature (.choice alphabet left right)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel left) left).initial) =
        typeFutureOffers left := by
      rw [computeFutureOf_binaryChoice_left signature left right TypeLabel.silent
        TypeLabel.silent (.choice alphabet left right) hWhole hFuelLeft
        (compileTypeFuel signature (typeCompilationFuel left) left).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel left) left le_rfl)]
      show computeFutureOf signature left (compileType signature left).initial =
        typeFutureOffers left
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial left (compileType signature left))
    have hFutureRightEq : computeFutureOf signature (.choice alphabet left right)
        (.child 1 (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
        typeFutureOffers right := by
      rw [computeFutureOf_binaryChoice_right signature left right TypeLabel.silent
        TypeLabel.silent (.choice alphabet left right) hWhole hFuelRight
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSignatureSymbol
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
      | choice_left _ _ _ _ _ =>
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers left)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hEdgeFact : (compileType signature (.choice alphabet left right)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
              left).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
            TypeAutomatonState.root (.child 0 (compileTypeFuel signature
              (typeCompilationFuel left) left).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers left)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hLeftPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureLeftEq
        have hChoiceLeftStep : DecoratedTypeTransition env (.choice alphabet left right)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left :=
          ⟨TypeTransition.choice_left env alphabet left right hWF,
            TypeOffers.choice_left env alphabet left right hWF⟩
        refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel left)
          left).initial, hEdgeFact, ?_⟩
        exact relationMembership_choice_left signature alphabet left right left
          (buildRelationSet_initial left (compileType signature left))
      | choice_right _ _ _ _ _ =>
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers right)) ∈
              signature.transitionAlphabet := by
          rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
          exact hSignatureSymbol
        have hEdgeFact : (compileType signature (.choice alphabet left right)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right))
            (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
              right).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
            TypeAutomatonState.root (.child 1 (compileTypeFuel signature
              (typeCompilationFuel right) right).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers right)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hRightPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureRightEq
        have hChoiceRightStep : DecoratedTypeTransition env (.choice alphabet left right)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers right)) right :=
          ⟨TypeTransition.choice_right env alphabet left right hWF,
            TypeOffers.choice_right env alphabet left right hWF⟩
        refine ⟨.child 1 (compileTypeFuel signature (typeCompilationFuel right)
          right).initial, hEdgeFact, ?_⟩
        exact relationMembership_choice_right signature alphabet left right right
          (buildRelationSet_initial right (compileType signature right))
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice alphabet left right) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice alphabet left right) hEdge)).mp hEdge
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
        rcases relationMembership_choice_cases signature alphabet left right hTargetRelated
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
          exact ⟨TypeTransition.choice_left env alphabet left right hWF,
            TypeOffers.choice_left env alphabet left right hWF⟩
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
        rcases relationMembership_choice_cases signature alphabet left right hTargetRelated
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
          exact ⟨TypeTransition.choice_right env alphabet left right hWF,
            TypeOffers.choice_right env alphabet left right hWF⟩
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
      have hOuterEdge : (compileType signature (.choice alphabet left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
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
                (.choice alphabet left right) hWhole hFuelLeft t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_choice_left signature alphabet left right residual'
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice alphabet left right) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice alphabet left right) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.choice alphabet left right) hEdge)]
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
                (.choice alphabet left right) hWhole hFuelLeft t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_choice_cases signature alphabet left right hTargetRelated with
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
      have hOuterEdge : (compileType signature (.choice alphabet left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
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
                (.choice alphabet left right) hWhole hFuelRight t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 1 q', hOuterEdge, ?_⟩
      exact relationMembership_choice_right signature alphabet left right residual'
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.choice alphabet left right) (.child 1 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.choice alphabet left right) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.choice alphabet left right) hEdge)]
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
                (.choice alphabet left right) hWhole hFuelRight t hStateMem]
      have hTargetEq : state' = .child 1 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_choice_cases signature alphabet left right hTargetRelated with
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.fairChoice alphabet bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's two selection edges match
  -- `fair_left`/`fair_right`, and `hLeftIH`/`hRightIH` handle the children.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
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
      typeCompilationFuel left + 1 ≤ typeCompilationFuel (.fairChoice alphabet bid left right) := by
    simp only [typeCompilationFuel]; omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel (.fairChoice alphabet bid left right) := by
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_fairChoice_cases signature alphabet bid left right hRelated with
    hRoot | ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · -- root case: `residual` represents `τ1 ⧺η τ2` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureLeftEq : computeFutureOf signature (.fairChoice alphabet bid left right)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel left) left).initial) =
        typeFutureOffers left := by
      rw [computeFutureOf_binaryChoice_left signature left right (TypeLabel.fair bid true)
        (TypeLabel.fair bid false) (.fairChoice alphabet bid left right) hWhole hFuelLeft
        (compileTypeFuel signature (typeCompilationFuel left) left).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel left) left le_rfl)]
      show computeFutureOf signature left (compileType signature left).initial =
        typeFutureOffers left
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial left (compileType signature left))
    have hFutureRightEq : computeFutureOf signature (.fairChoice alphabet bid left right)
        (.child 1 (compileTypeFuel signature (typeCompilationFuel right) right).initial) =
        typeFutureOffers right := by
      rw [computeFutureOf_binaryChoice_right signature left right (TypeLabel.fair bid true)
        (TypeLabel.fair bid false) (.fairChoice alphabet bid left right) hWhole hFuelRight
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSignatureSymbol
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
          have hEdgeFact : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
              TypeAutomatonState.root env (TypeLabel.fair bid true)
              (TypeOfferSummary.mk ∅ (typeFutureOffers left))
              (.child 0 (compileTypeFuel signature (typeCompilationFuel left)
                left).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
              TypeAutomatonState.root (.child 0 (compileTypeFuel signature
                (typeCompilationFuel left) left).initial) env (TypeLabel.fair bid true)
              (TypeOfferSummary.mk ∅ (typeFutureOffers left)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hLeftPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureLeftEq
          have hFairLeftStep : DecoratedTypeTransition env (.fairChoice alphabet bid left right)
              (TypeLabel.fair bid true) (TypeOfferSummary.mk ∅ (typeFutureOffers left)) left :=
            ⟨TypeTransition.fair_left env alphabet bid left right hWF,
              TypeOffers.fair_left env alphabet bid left right hWF⟩
          refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel left)
            left).initial, hEdgeFact, ?_⟩
          exact relationMembership_fairChoice_left signature alphabet bid left right left
            (buildRelationSet_initial left (compileType signature left))
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
          have hEdgeFact : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
              TypeAutomatonState.root env (TypeLabel.fair bid false)
              (TypeOfferSummary.mk ∅ (typeFutureOffers right))
              (.child 1 (compileTypeFuel signature (typeCompilationFuel right)
                right).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
              TypeAutomatonState.root (.child 1 (compileTypeFuel signature
                (typeCompilationFuel right) right).initial) env (TypeLabel.fair bid false)
              (TypeOfferSummary.mk ∅ (typeFutureOffers right)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hRightPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureRightEq
          have hFairRightStep : DecoratedTypeTransition env (.fairChoice alphabet bid left right)
              (TypeLabel.fair bid false) (TypeOfferSummary.mk ∅ (typeFutureOffers right))
              right :=
            ⟨TypeTransition.fair_right env alphabet bid left right hWF,
              TypeOffers.fair_right env alphabet bid left right hWF⟩
          refine ⟨.child 1 (compileTypeFuel signature (typeCompilationFuel right)
            right).initial, hEdgeFact, ?_⟩
          exact relationMembership_fairChoice_right signature alphabet bid left right right
            (buildRelationSet_initial right (compileType signature right))
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice alphabet bid left right) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice alphabet bid left right) hEdge)).mp
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
        rcases relationMembership_fairChoice_cases signature alphabet bid left right hTargetRelated
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
          exact ⟨TypeTransition.fair_left env alphabet bid left right hWF,
            TypeOffers.fair_left env alphabet bid left right hWF⟩
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
        rcases relationMembership_fairChoice_cases signature alphabet bid left right hTargetRelated
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
          exact ⟨TypeTransition.fair_right env alphabet bid left right hWF,
            TypeOffers.fair_right env alphabet bid left right hWF⟩
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
      have hOuterEdge : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
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
                (.fairChoice alphabet bid left right) hWhole hFuelLeft t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_fairChoice_left signature alphabet bid left right residual'
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice alphabet bid left right) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice alphabet bid left right) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.fairChoice alphabet bid left right) hEdge)]
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
                (.fairChoice alphabet bid left right) hWhole hFuelLeft t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_fairChoice_cases signature alphabet bid left right hTargetRelated with
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
      have hOuterEdge : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
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
                (.fairChoice alphabet bid left right) hWhole hFuelRight t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 1 q', hOuterEdge, ?_⟩
      exact relationMembership_fairChoice_right signature alphabet bid left right residual'
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.fairChoice alphabet bid left right) (.child 1 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.fairChoice alphabet bid left right) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.fairChoice alphabet bid left right) hEdge)]
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
                (.fairChoice alphabet bid left right) hWhole hFuelRight t hStateMem]
      have hTargetEq : state' = .child 1 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_fairChoice_cases signature alphabet bid left right hTargetRelated with
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (first second : PactType)
    (hFirstIH : StepIffStatement signature first)
    (hSecondIH : StepIffStatement signature second) :
    StepIffStatement signature (.seq alphabet first second) := by
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
    rcases relationMembership_seq_cases signature alphabet first second hRelated with
      hLeft | hRight
    · rcases hLeft with ⟨q, leftResidual, hEntry, hLeftRelated, _hSurvives⟩
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
                alphabet leftTarget second current)
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 0 q', compileType_seq_lift_left_step signature alphabet
            first second
            hRelated hLeftRelated hChildTargetRelated hNonFinal hChildStep
            hSignatureSymbol hChildEdge⟩
      | fuse transitionSkipAlphabet offerSkipAlphabet childFuture hTarget
          hChildTransition hChildOffers hFuture =>
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
              hSignatureSymbol hChildOffers
              (by simp [typeFutureOffers, typeFutureOffersFuel])
          have hChildStep : DecoratedTypeTransition env leftResidual label
              (TypeOfferSummary.mk current childFuture)
              (.skip offerSkipAlphabet) :=
            ⟨hChildOffers.toTypeTransition, hChildOffers⟩
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 1 (compileType signature second).initial,
            compileType_seq_lift_left_fuse signature alphabet
              offerSkipAlphabet first second
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
      exact compileType_seq_lift_right_step signature alphabet first second hRelated
        hRightRelated hChildTargetRelated hStep hChildEdge
  · rintro ⟨state', hEdge, hTargetRelated⟩
    cases compileType_seq_edge_cases signature alphabet first second
        hRelated hEdge hTargetRelated with
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
        exact ⟨TypeTransition.seq env alphabet leftResidual leftTarget second label
            hChildStep.1 hNonFinal,
          TypeOffers.seq env alphabet leftResidual leftTarget second label current
            childFuture hChildStep.2 hNonFinal⟩
    | leftFuse leftResidual skipAlphabet q q' childFuture hResidual hResidual' hState
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
        exact ⟨TypeTransition.seq_fuse env alphabet skipAlphabet leftResidual
            second label
            hChildStep.1,
          TypeOffers.seq_fuse env alphabet skipAlphabet leftResidual second label
            current childFuture hChildStep.2⟩
    | entryFuse skipAlphabet hResidual hResidual' hState hState' hLabel hCurrent hFuture
        hWellFormed hClock =>
        subst residual
        subst residual'
        subst state
        subst state'
        subst label
        subst current
        subst future
        exact ⟨TypeTransition.seq_fuse env alphabet skipAlphabet
            (.skip skipAlphabet) second TypeLabel.silent
            (TypeTransition.skip env skipAlphabet ⟨hWellFormed, hClock⟩),
          by
            simpa using TypeOffers.seq_fuse env alphabet skipAlphabet
              (.skip skipAlphabet) second TypeLabel.silent ∅ ∅
              (TypeOffers.skip env skipAlphabet ⟨hWellFormed, hClock⟩)⟩
    | rightStep q q' hState hState' hRightRelated hRightTargetRelated
        hChildEdge =>
        subst state
        subst state'
        have hChildSymbol :=
          NewCorrespondence.compileType_hasEdge_symbol_mem signature second
            hChildEdge
        exact (hSecondIH hRightRelated hChildSymbol).mpr
          ⟨q', hChildEdge, hRightTargetRelated⟩

set_option maxHeartbeats 4000000 in
/-- Step correspondence for interleaved parallel composition `τ1 ‖_I τ2`. -/
theorem correspondence_par_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hAlphabetCoherent :
      (.par alphabet left right interface : PactType).AlphabetCoherent)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.par alphabet left right interface) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove `hLeftIH`/`hRightIH` give two component
  -- edges that combine into the matching `par`/`par_fuse` product edge.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  rcases relationMembership_par_cases signature alphabet left right interface
    hRelated with
    ⟨q1, q2, residualLeft, residualRight, hEntryEq, hLeftRelated,
      hRightRelated, hSourceReachable⟩ | hEntryEq
  · -- general product case: `residual` represents `residualLeft ‖_I residualRight`
    injection hEntryEq with hResidualEq hStateEq
    subst hResidualEq; subst hStateEq
    have hParCoherent := hAlphabetCoherent
    simp only [PactType.AlphabetCoherent] at hParCoherent
    have hResidualLeftAlphabet := relationMembership_alphabet_eq signature left
      residualLeft q1 hParCoherent.2.1 hLeftRelated
    have hResidualRightAlphabet := relationMembership_alphabet_eq signature right
      residualRight q2 hParCoherent.2.2 hRightRelated
    have hSourceAlphabet : alphabet = PactTypeAlphabet.mergeHidden
        residualLeft.alphabet residualRight.alphabet interface := by
      rw [hResidualLeftAlphabet, hResidualRightAlphabet]
      exact hParCoherent.1
    constructor
    · intro hStep
      cases decoratedTypeTransition_par_cases hStep with
      | step leftEnv rightEnv leftLabel rightLabel leftTarget rightTarget
          leftCurrent leftFuture rightCurrent rightFuture hTargetEq hNonFinal
          hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq hCurrentEq hFutureEq =>
          obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
            transitionAlphabet_of_par_component signature residualLeft residualRight
              interface hWF hInterface hLocal1 hLocal2 hSync hLabelEq
              (hCurrentEq ▸ hFutureEq ▸ hSignatureSymbol)
          have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel
              (TypeOfferSummary.mk leftCurrent leftFuture) ∈
              (compileType signature left).alphabet := by
            simpa [compileType] using hLeftSymbolMem0
          have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel
              (TypeOfferSummary.mk rightCurrent rightFuture) ∈
              (compileType signature right).alphabet := by
            simpa [compileType] using hRightSymbolMem0
          obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
            (hLeftIH hLeftRelated hLeftSymbolMem).mp hLeftStep
          obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
            (hRightIH hRightRelated hRightSymbolMem).mp hRightStep
          -- H13: a child remains (`hNonFinal`), so the compiler does not
          -- redirect this edge to `q_done`.
          have hNotBothAccept :
              ¬ (q1' ∈ (compileType signature left).accepting ∧
                 q2' ∈ (compileType signature right).accepting) := by
            rintro ⟨hAccept1, hAccept2⟩
            exact hNonFinal
              ⟨(helper_h13_final_states_represent_completion signature
                  hLeftTargetRelated).mp hAccept1,
                (helper_h13_final_states_represent_completion signature
                  hRightTargetRelated).mp hAccept2⟩
          have hEdgeFact : (compileType signature (.par alphabet left right interface)).HasEdge
              (.pair q1 q2) env label (TypeOfferSummary.mk current future)
              (.pair q1' q2') := by
            rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet]
            refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge, hLeftRelated, hRightRelated,
              hSourceReachable, hWF, hLocal1, hLocal2,
              hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
            simp [hNotBothAccept]
          have hTargetReachable :=
            compiledParallel_pair_edge_target_reachable signature alphabet left
              right interface
              hSignatureSymbol hEdgeFact
          refine ⟨.pair q1' q2', hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_pair signature alphabet left right interface
            hLeftTargetRelated hRightTargetRelated hTargetReachable
      | fuse leftEnv rightEnv leftLabel rightLabel leftCurrent leftFuture rightCurrent
          rightFuture hTargetEq hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq
          hCurrentEq hFutureEq =>
          obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
            transitionAlphabet_of_par_component signature residualLeft residualRight
              interface hWF hInterface hLocal1 hLocal2 hSync hLabelEq
              (hCurrentEq ▸ hFutureEq ▸ hSignatureSymbol)
          have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel
              (TypeOfferSummary.mk leftCurrent leftFuture) ∈
              (compileType signature left).alphabet := by
            simpa [compileType] using hLeftSymbolMem0
          have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel
              (TypeOfferSummary.mk rightCurrent rightFuture) ∈
              (compileType signature right).alphabet := by
            simpa [compileType] using hRightSymbolMem0
          obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
            (hLeftIH hLeftRelated hLeftSymbolMem).mp hLeftStep
          obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
            (hRightIH hRightRelated hRightSymbolMem).mp hRightStep
          -- H13: both children finish here, so the compiler redirects to `q_done`.
          have hBothAccept :
              q1' ∈ (compileType signature left).accepting ∧
              q2' ∈ (compileType signature right).accepting :=
            ⟨(helper_h13_final_states_represent_completion signature
                hLeftTargetRelated).mpr rfl,
              (helper_h13_final_states_represent_completion signature
                hRightTargetRelated).mpr rfl⟩
          have hEdgeFact : (compileType signature (.par alphabet left right interface)).HasEdge
              (.pair q1 q2) env label (TypeOfferSummary.mk current future)
              TypeAutomatonState.final := by
            rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet]
            refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge, hLeftRelated, hRightRelated,
              hSourceReachable, hWF, hLocal1, hLocal2,
              hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
            simp [hBothAccept]
          refine ⟨.final, hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_final signature alphabet left right interface
    · rintro ⟨state', hEdge, hTargetRelated⟩
      rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet] at hEdge
      obtain ⟨childLeft, childRight, leftEnv, rightEnv, leftLabel, rightLabel,
        leftOffers, rightOffers, q1', q2', hLeftEdge, hRightEdge,
        hChildLeftRelated, hChildRightRelated, _hEdgeSourceReachable,
        hWF, hLocal1, hLocal2, hSync, hLabelEq, hCurrentEq, hFutureEq,
        hRedirect⟩ := hEdge
      let leftCurrent := leftOffers.current
      let leftFuture := leftOffers.future
      let rightCurrent := rightOffers.current
      let rightFuture := rightOffers.future
      have hChildLeftEq : residualLeft = childLeft :=
        relationMembership_functional left (compileType signature left)
          hLeftRelated hChildLeftRelated
      have hChildRightEq : residualRight = childRight :=
        relationMembership_functional right (compileType signature right)
          hRightRelated hChildRightRelated
      subst hChildLeftEq; subst hChildRightEq
      have hSymbolMem' :
          TypeAutomatonSymbol.mk env label
              (TypeOfferSummary.mk
                (hideTypeOffers interface (leftOffers.current ∪ rightOffers.current))
                (hideTypeOffers interface (leftOffers.future ∪ rightOffers.future))) ∈
            signature.transitionAlphabet := by
        rw [← hCurrentEq, ← hFutureEq]; exact hSignatureSymbol
      obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
        transitionAlphabet_of_par_component signature residualLeft residualRight
          interface hWF hInterface hLocal1 hLocal2 hSync hLabelEq hSymbolMem'
      have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel leftOffers ∈
          (compileType signature left).alphabet := by
        change TypeAutomatonSymbol.mk leftEnv leftLabel leftOffers ∈
          signature.transitionAlphabet
        cases leftOffers
        exact hLeftSymbolMem0
      have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel rightOffers ∈
          (compileType signature right).alphabet := by
        change TypeAutomatonSymbol.mk rightEnv rightLabel rightOffers ∈
          signature.transitionAlphabet
        cases rightOffers
        exact hRightSymbolMem0
      by_cases hBothAccept : q1' ∈ (compileType signature left).accepting ∧
          q2' ∈ (compileType signature right).accepting
      · -- redirected edge: the compiler already sent this edge straight to
        -- `q_done`, so the reconstructed semantic step is `par_fuse`.
        rw [if_pos hBothAccept] at hRedirect
        subst hRedirect
        obtain ⟨leftSkipAlphabet, hLeftAcceptRelated⟩ :=
          relationMembership_of_accepting signature left hBothAccept.1
        obtain ⟨rightSkipAlphabet, hRightAcceptRelated⟩ :=
          relationMembership_of_accepting signature right hBothAccept.2
        have hLeftSkipAlphabet : leftSkipAlphabet = residualLeft.alphabet := by
          have hTargetAlphabet := relationMembership_alphabet_eq signature left
            (.skip leftSkipAlphabet) q1' hParCoherent.2.1 hLeftAcceptRelated
          simpa [PactType.alphabet] using
            hTargetAlphabet.trans hResidualLeftAlphabet.symm
        have hRightSkipAlphabet : rightSkipAlphabet = residualRight.alphabet := by
          have hTargetAlphabet := relationMembership_alphabet_eq signature right
            (.skip rightSkipAlphabet) q2' hParCoherent.2.2 hRightAcceptRelated
          simpa [PactType.alphabet] using
            hTargetAlphabet.trans hResidualRightAlphabet.symm
        subst leftSkipAlphabet
        subst rightSkipAlphabet
        have hLeftStep : DecoratedTypeTransition leftEnv residualLeft leftLabel
            leftOffers (.skip residualLeft.alphabet) :=
          (hLeftIH hLeftRelated hLeftSymbolMem).mpr
            ⟨q1', hLeftEdge, hLeftAcceptRelated⟩
        have hRightStep : DecoratedTypeTransition rightEnv residualRight rightLabel
            rightOffers (.skip residualRight.alphabet) :=
          (hRightIH hRightRelated hRightSymbolMem).mpr
            ⟨q2', hRightEdge, hRightAcceptRelated⟩
        rcases relationMembership_par_cases signature alphabet left right
          interface hTargetRelated with
          ⟨qq1, qq2, resL, resR, hEqAgain, _, _, _⟩ | hEqAgain
        · simp at hEqAgain
        · injection hEqAgain with hResidualEqAgain hStateEqAgain
          subst hResidualEqAgain
          simp only [] at hCurrentEq hFutureEq
          rw [hLabelEq, hCurrentEq, hFutureEq]
          simpa only [hSourceAlphabet] using
            (⟨TypeTransition.par_fuse env leftEnv rightEnv interface residualLeft
              residualRight leftLabel rightLabel hLeftStep.1 hRightStep.1
              ⟨hWF, hLocal1, hLocal2, hSync⟩,
            TypeOffers.par_fuse env leftEnv rightEnv interface residualLeft residualRight
              leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
              hLeftStep.2 hRightStep.2 hLocal1 hLocal2
              ⟨hWF, hSync⟩⟩ : DecoratedTypeTransition env
                (.par (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                  residualRight.alphabet interface) residualLeft residualRight
                  interface) (TypeLabel.combine interface leftLabel rightLabel)
                (TypeOfferSummary.mk
                  (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
                  (hideTypeOffers interface (leftFuture ∪ rightFuture)))
                (.skip (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                  residualRight.alphabet interface)))
      · -- kept edge: the raw target `.pair q1' q2'` survives as its own
        -- state, representing a genuine `.par` continuation.
        rw [if_neg hBothAccept] at hRedirect
        subst hRedirect
        rcases relationMembership_par_cases signature alphabet left right
          interface hTargetRelated with
          ⟨qq1, qq2, leftTarget, rightTarget, hEqAgain, hLeftTargetRelated,
            hRightTargetRelated, _hTargetReachable⟩ | hEqAgain
        · injection hEqAgain with hResidualEqAgain hPairEqAgain
          injection hPairEqAgain with hQ1EqAgain hQ2EqAgain
          subst hQ1EqAgain; subst hQ2EqAgain
          have hLeftStep : DecoratedTypeTransition leftEnv residualLeft leftLabel
              leftOffers leftTarget :=
            (hLeftIH hLeftRelated hLeftSymbolMem).mpr ⟨q1', hLeftEdge, hLeftTargetRelated⟩
          have hRightStep : DecoratedTypeTransition rightEnv residualRight rightLabel
              rightOffers rightTarget :=
            (hRightIH hRightRelated hRightSymbolMem).mpr ⟨q2', hRightEdge, hRightTargetRelated⟩
          have hNonFinal : ¬(leftTarget = .skip leftTarget.alphabet ∧
              rightTarget = .skip rightTarget.alphabet) := by
            rintro ⟨hL, hR⟩
            exact hBothAccept
              ⟨(helper_h13_final_states_represent_completion signature
                  hLeftTargetRelated).mpr hL,
                (helper_h13_final_states_represent_completion signature
                  hRightTargetRelated).mpr hR⟩
          simp only [] at hCurrentEq hFutureEq
          rw [hLabelEq, hCurrentEq, hFutureEq, hResidualEqAgain]
          simpa only [hSourceAlphabet] using
            (⟨TypeTransition.par env leftEnv rightEnv interface residualLeft leftTarget
              residualRight rightTarget leftLabel rightLabel hLeftStep.1 hRightStep.1
              hNonFinal ⟨hWF, hLocal1, hLocal2, hSync⟩,
            TypeOffers.par env leftEnv rightEnv interface residualLeft leftTarget
              residualRight rightTarget leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture
              hLeftStep.2 hRightStep.2 hNonFinal hLocal1 hLocal2 ⟨hWF, hSync⟩⟩ :
              DecoratedTypeTransition env
                (.par (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                  residualRight.alphabet interface) residualLeft residualRight
                  interface) (TypeLabel.combine interface leftLabel rightLabel)
                (TypeOfferSummary.mk
                  (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
                  (hideTypeOffers interface (leftFuture ∪ rightFuture)))
                (.par (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                  residualRight.alphabet interface) leftTarget rightTarget
                  interface))
        · simp at hEqAgain
  · -- `q_done` case: `residual` already represents literal `.skip`, whose
    -- only rule is `T-Skip`; matches `.final`'s own non-clock silent idle
    -- self-loop (paper's "Forward direction at the done state" / third
    -- backward-direction bullet).
    injection hEntryEq with hResidualEq hStateEq
    subst hResidualEq; subst hStateEq
    have hFinalAccepting : TypeAutomatonState.final ∈
        (compileType signature (.par alphabet left right interface)).accepting :=
      (helper_h13_final_states_represent_completion signature hRelated).mpr rfl
    constructor
    · intro hStep
      obtain ⟨hTransition, hOffers⟩ := hStep
      cases hTransition with
      | skip _ _ hSide =>
          obtain ⟨hWF, hClock⟩ := hSide
          cases hOffers with
          | skip _ _ =>
              have hEdge : (compileType signature (.par alphabet left right interface)).HasEdge
                  TypeAutomatonState.final env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)
                  TypeAutomatonState.final := by
                rw [buildParallelAutomaton_final_hasEdge_iff signature alphabet
                  left right
                  interface env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅)
                  TypeAutomatonState.final hSignatureSymbol]
                exact ⟨hWF, hClock, rfl, rfl, rfl⟩
              exact ⟨.final, hEdge, hRelated⟩
    · rintro ⟨state', hEdge, hTargetRelated⟩
      rw [buildParallelAutomaton_final_hasEdge_iff signature alphabet left right
        interface env label (TypeOfferSummary.mk current future) state'
        hSignatureSymbol] at hEdge
      obtain ⟨hWF, hClock, hLabelEq, hOffersEq, hTargetEq⟩ := hEdge
      subst hLabelEq
      injection hOffersEq with hCurrentEq hFutureEq
      subst hCurrentEq; subst hFutureEq
      subst hTargetEq
      have hResidualTarget0 : residual' = .skip residual'.alphabet :=
        (helper_h13_final_states_represent_completion signature hTargetRelated).mp
          hFinalAccepting
      have hTargetAlphabet := relationMembership_alphabet_eq signature
        (.par alphabet left right interface) residual' .final
        hAlphabetCoherent hTargetRelated
      have hResidualTarget : residual' = .skip alphabet := by
        simpa [hTargetAlphabet] using hResidualTarget0
      subst hResidualTarget
      exact ⟨TypeTransition.skip env alphabet ⟨hWF, hClock⟩,
        TypeOffers.skip env alphabet ⟨hWF, hClock⟩⟩

/-- Step correspondence for recursion `μX.body`. -/
theorem correspondence_recur_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hBodyIH : StepIffStatement signature body) :
    StepIffStatement signature (.recur alphabet name body) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's unfolding step matches the
  -- header edge, and `hBodyIH` transported along substitution handles the
  -- rest of the body, including a marker turning into a backedge.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) = typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
  rcases relationMembership_recur_cases signature alphabet name body hRelated with
    hRoot | ⟨q, bodyResidual, hEntryEq, hBodyRelated⟩
  · -- root case: `residual` represents `μX.body` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSignatureSymbol
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
    have hRecurStep : DecoratedTypeTransition env (.recur alphabet name body) TypeLabel.silent
        (TypeOfferSummary.mk ∅ (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
        (body.replaceVar name (.recur alphabet name body)) :=
      ⟨TypeTransition.recur env alphabet name body hWF, TypeOffers.recur env alphabet name body hWF⟩
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
                (typeFutureOffers (body.replaceVar name (.recur alphabet name body)))) ∈
            (compileType signature (.recur alphabet name body)).alphabet := by
        rw [hLabelEq, hCurrentEq, hFutureEq] at hSignatureSymbol
        exact hSignatureSymbol
      have hEdgeFact :
          (compileType signature (.recur alphabet name body)).HasEdge TypeAutomatonState.root
            env TypeLabel.silent
            (TypeOfferSummary.mk ∅
              (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel body)
              body).initial) := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.recur alphabet name body)
          TypeAutomatonState.root (.child 0 (compileTypeFuel signature
            (typeCompilationFuel body) body).initial) env TypeLabel.silent
          (TypeOfferSummary.mk ∅
            (typeFutureOffers (body.replaceVar name (.recur alphabet name body))))
          hSignatureSymbol']
        rw [hWhole]
        refine ⟨_, hHeaderPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
        simp only [childState, Finset.sdiff_empty]
        exact helper_h15_recursion_future_offers_agree signature alphabet name body
          (buildRelationSet_initial body (compileType signature body))
      refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel body)
        body).initial, hEdgeFact, ?_⟩
      exact relationMembership_recur_child signature alphabet name body body
        (buildRelationSet_initial body (compileType signature body))
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur alphabet name body)
        hEdge
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.recur alphabet name body) TypeAutomatonState.root state' env label
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
        rcases relationMembership_recur_cases signature alphabet name body hTargetRelated with
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
          have hPFuture' : computeFutureOf signature (.recur alphabet name body)
              (childState 0 (compileTypeFuel signature (typeCompilationFuel body)
                body).initial) \ (∅ : Finset BareMessage) = future := hPFuture
          have hFutureEq : future =
              typeFutureOffers (body.replaceVar name (.recur alphabet name body)) := by
            rw [← hPFuture', Finset.sdiff_empty, childState]
            exact helper_h15_recursion_future_offers_agree signature alphabet name body
              (buildRelationSet_initial body (compileType signature body))
          have hEnvironmentEq : environment = env := hPEnv
          rw [hResidualEqAgain, hLabelEq]
          refine ⟨TypeTransition.recur env alphabet name body
            (localEnvironment_wellFormed signature (hEnvironmentEq ▸ hEnvironment)), ?_⟩
          rw [hCurrentEq, hFutureEq]
          exact TypeOffers.recur env alphabet name body
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
        (decoratedTypeTransition_replaceVar_iff alphabet name body bodyResidual).mp hStep
      obtain ⟨q', hBodyEdge, hBodyTargetRelated⟩ :=
        (hBodyIH hBodyRelated hBodySymbol).mp hBodyStep
      have hChildSymbol := compileType_hasEdge_symbol_mem signature body hBodyEdge
      have hChildResolved := (compileType_hasEdge_iff_hasResolvedEdge signature body
        q q' env label (TypeOfferSummary.mk current future) hChildSymbol).mp hBodyEdge
      obtain ⟨nativeEdge, hNativeMem, hNSource, hNEnv, hNLabel, hNCurrent, hNFuture,
        hNTarget⟩ := hChildResolved
      have hNotMarker : nativeEdge.label ≠ .variable name := by
        rw [hNLabel]; simp
      have hOuterEdge : (compileType signature (.recur alphabet name body)).HasEdge
          (.child 0 q) env label
          (TypeOfferSummary.mk current future)
          (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.recur alphabet name body)
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
              rw [computeFutureOf_recursion_child signature name body (.recur alphabet name body)
                hWhole (by omega) t hStateMem]
              simpa [childFutureSpec, hSpec] using hNFuture
        · simp [childPendingEdge, childState, hNTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      rw [hResidual'Eq] at hStep
      rw [hResidual'Eq]
      exact relationMembership_recur_child signature alphabet name body residual0
        hBodyTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur alphabet name body) hEdge
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature (.recur alphabet name body)
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
          have hResidualEq : bodyResidual = .var bodyResidual.alphabet name :=
            compileTypeFuel_marker_represents_var signature name body hBodyRelated
              hBodyEdgeMem hSourceEq hMarker
          have hTargetEq : state' = .child 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            rw [← hPTarget]
          rw [hTargetEq] at hTargetRelated
          rcases relationMembership_recur_cases signature alphabet name body hTargetRelated with
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
            have hPFuture' : computeFutureOf signature (.recur alphabet name body)
                (childState 0 (compileTypeFuel signature (typeCompilationFuel body)
                  body).initial) \ (∅ : Finset BareMessage) = future := hPFuture
            have hFutureEq : future =
                typeFutureOffers (body.replaceVar name (.recur alphabet name body)) := by
              rw [← hPFuture', Finset.sdiff_empty, childState]
              exact helper_h15_recursion_future_offers_agree signature alphabet name body
                (buildRelationSet_initial body (compileType signature body))
            have hEnvMem : env ∈ signature.localEnvironments :=
              transitionAlphabet_environment_mem signature hSignatureSymbol
            have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
            rw [hResidualEqAgain, hLabelEq, hResidualEq]
            simp only [PactType.replaceVar]
            rw [hCurrentEq, hFutureEq]
            exact ⟨TypeTransition.recur env alphabet name body hWF, TypeOffers.recur env alphabet name body hWF⟩
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
                    (.recur alphabet name body) hWhole (by omega) t hStateMem]
          have hTargetEq : state' = .child 0 bodyEdge.target := by rw [← hPTarget]
          rw [hTargetEq] at hTargetRelated
          rcases relationMembership_recur_cases signature alphabet name body hTargetRelated with
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
            exact (decoratedTypeTransition_replaceVar_iff alphabet name body bodyResidual).mpr
              ⟨bodyResidualAgain, rfl, hInnerStep⟩

set_option maxHeartbeats 4000000 in
/-- Step correspondence for exclusive offer `⨁(τ0,B)`. -/
theorem correspondence_xoffer_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseIH : StepIffStatement signature elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) :
    StepIffStatement signature (.xoffer alphabet elseType branches) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's fire/else/wait edges match
  -- the three offer rules, and `hElseIH`/`hBranchesIH` handle the rest.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) =
        buildExclusiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun branch => (branch.1, compileTypeFuel signature
            (typeCompilationFuel branch.2) branch.2)) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
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
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hBranchFuelStrict : ∀ branch ∈ branches, typeCompilationFuel branch.2 + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    intro branch hBranch
    have h1 := typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch
    simp only [typeCompilationFuel]; omega
  rcases relationMembership_xoffer_cases signature alphabet elseType branches
    hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, action, branchType, q, hBranchesEq, hStateEq, hBranchRelated⟩
  · -- root case: `residual` represents `⨁(τ0,B)` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureElseEq : computeFutureOf signature (.xoffer alphabet elseType branches)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial) = typeFutureOffers elseType := by
      rw [computeFutureOf_exclusiveOffer_else signature elseType branches
        (.xoffer alphabet elseType branches) hWhole hElseFuelStrict
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSignatureSymbol
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRootRelated : relationMembership
        (buildRelationSet (.xoffer alphabet elseType branches)
          (compileType signature (.xoffer alphabet elseType branches)))
        (.xoffer alphabet elseType branches) TypeAutomatonState.root := by
      simpa using hRelated
    have hRootFuture : computeFutureOf signature (.xoffer alphabet elseType branches)
        TypeAutomatonState.root = typeFutureOffers (.xoffer alphabet elseType branches) :=
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
      | xoffer_branch _ _ _ _ branchAction _ hPremise =>
        -- The `processType` slot is already pinned to `actualTarget` by
        -- unifying against `hOffers`'s own (generalized) target index, so
        -- the pattern names it `_` and the proof below refers to
        -- `actualTarget` directly rather than introducing a fresh name.
        obtain ⟨hWF', hBranchMem, hEnabled, hResolvedNeeds⟩ := hPremise
        obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hBranchMem
        have hFutureBranchEq : computeFutureOf signature (.xoffer alphabet elseType branches)
            (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) =
            typeFutureOffers actualTarget := by
          rw [computeFutureOf_exclusiveOffer_branch signature elseType branches
            (.xoffer alphabet elseType branches) hWhole index branchAction actualTarget hBranchGet
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
        have hEdgeFact : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
            TypeAutomatonState.root env (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
            TypeAutomatonState.root (.child (index + 1) (compileTypeFuel signature
              (typeCompilationFuel actualTarget) actualTarget).initial) env
            (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hBranchPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureBranchEq
        have hBranchStep : DecoratedTypeTransition env (.xoffer alphabet elseType branches)
            (TypeLabel.message branchAction.1 branchAction.2)
            (TypeOfferSummary.mk {branchAction} (typeFutureOffers actualTarget))
            actualTarget :=
          ⟨TypeTransition.xoffer_branch env alphabet elseType branches branchAction actualTarget
            ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩,
            TypeOffers.xoffer_branch env alphabet elseType branches branchAction actualTarget
              ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩⟩
        refine ⟨.child (index + 1) (compileTypeFuel signature
          (typeCompilationFuel actualTarget) actualTarget).initial, hEdgeFact, ?_⟩
        exact relationMembership_xoffer_branch signature alphabet elseType branches
          hBranchGet
          (buildRelationSet_initial actualTarget (compileType signature actualTarget))
      | xoffer_else _ _ _ _ hPremise =>
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
        have hEdgeFact : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers elseType))
            (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
              elseType).initial) := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
            TypeAutomatonState.root (.child 0 (compileTypeFuel signature
              (typeCompilationFuel elseType) elseType).initial) env TypeLabel.silent
            (TypeOfferSummary.mk ∅ (typeFutureOffers elseType)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hElsePending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          simpa [childState] using hFutureElseEq
        have hElseStep : DecoratedTypeTransition env (.xoffer alphabet elseType branches)
            TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers elseType)) elseType :=
          ⟨TypeTransition.xoffer_else env alphabet elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.xoffer_else env alphabet elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
        refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial, hEdgeFact, ?_⟩
        exact relationMembership_xoffer_else signature alphabet elseType branches
          (buildRelationSet_initial elseType (compileType signature elseType))
      | xoffer_wait _ _ _ _ hPremise =>
        obtain ⟨hWF', hUnresolved, hClock⟩ := hPremise
        have hSignatureSymbol' :
            TypeAutomatonSymbol.mk env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.xoffer alphabet elseType branches) \
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
        have hEdgeFact : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
            TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer alphabet elseType branches) \
                typeWaitingOffers env branches)) TypeAutomatonState.root := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
            TypeAutomatonState.root TypeAutomatonState.root env TypeLabel.silent
            (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer alphabet elseType branches) \
                typeWaitingOffers env branches)) hSignatureSymbol']
          rw [hWhole]
          refine ⟨_, hWaitPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
          show computeFutureOf signature (.xoffer alphabet elseType branches) TypeAutomatonState.root \
            typeWaitingOffers env branches = typeFutureOffers (.xoffer alphabet elseType branches) \
              typeWaitingOffers env branches
          rw [hRootFuture]
        have hWaitStep : DecoratedTypeTransition env (.xoffer alphabet elseType branches)
            TypeLabel.silent (TypeOfferSummary.mk (typeWaitingOffers env branches)
              (typeFutureOffers (.xoffer alphabet elseType branches) \
                typeWaitingOffers env branches)) (.xoffer alphabet elseType branches) :=
          ⟨TypeTransition.xoffer_wait env alphabet elseType branches
            ⟨hWF, hUnresolved, hClock⟩,
            TypeOffers.xoffer_wait env alphabet elseType branches
              ⟨hWF, hUnresolved, hClock⟩⟩
        refine ⟨TypeAutomatonState.root, hEdgeFact, ?_⟩
        exact relationMembership_xoffer_root signature alphabet elseType branches
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer alphabet elseType branches) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer alphabet elseType branches) hEdge)).mp hEdge
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
              (.xoffer alphabet elseType branches) hWhole index branchAction branchType' hBranchGet
              (hBranchFuelStrict (branchAction, branchType') hBranchMem)
              (compileTypeFuel signature (typeCompilationFuel branchType')
                branchType').initial (compileTypeFuel_initial_mem signature
                (typeCompilationFuel branchType') branchType' le_rfl)]
            show computeFutureOf signature branchType' (compileType signature
              branchType').initial = typeFutureOffers branchType'
            exact helper_h15_future_offers_agree signature
              (buildRelationSet_initial branchType' (compileType signature branchType'))
          rcases relationMembership_xoffer_cases signature alphabet elseType branches hTargetRelated
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
            exact ⟨TypeTransition.xoffer_branch env alphabet elseType branches branchAction branchType'
              ⟨hWF, hBranchMem, hEnabled, hResolvedNeeds⟩,
              TypeOffers.xoffer_branch env alphabet elseType branches branchAction branchType'
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
        have hFutureEq : future = typeFutureOffers (.xoffer alphabet elseType branches) \
            typeWaitingOffers env branches := by
          rw [← hPFuture, hRootFuture]
          rfl
        rcases relationMembership_xoffer_cases signature alphabet elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, actionAgain, branchTypeAgain, qAgain, hBranchesEqAgain,
              hStateEqAgain, hBranchRelatedAgain⟩
        · simp only [Prod.mk.injEq] at hRootAgain
          have hResidualEq : residual' = .xoffer alphabet elseType branches := hRootAgain.1
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.xoffer_wait env alphabet elseType branches
            ⟨hWF, hUnresolved, hClock⟩,
            TypeOffers.xoffer_wait env alphabet elseType branches
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
            (.xoffer alphabet elseType branches) hWhole hElseFuelStrict
            (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
            (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
              le_rfl)]
          show computeFutureOf signature elseType (compileType signature elseType).initial =
            typeFutureOffers elseType
          exact helper_h15_future_offers_agree signature
            (buildRelationSet_initial elseType (compileType signature elseType))
        rcases relationMembership_xoffer_cases signature alphabet elseType branches hTargetRelated
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
          exact ⟨TypeTransition.xoffer_else env alphabet elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.xoffer_else env alphabet elseType branches
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
      have hOuterEdge : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
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
                (.xoffer alphabet elseType branches) hWhole hElseFuelStrict t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_xoffer_else signature alphabet elseType branches
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.xoffer alphabet elseType branches) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer alphabet elseType branches) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.xoffer alphabet elseType branches) hEdge)]
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
                (.xoffer alphabet elseType branches) hWhole hElseFuelStrict t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_xoffer_cases signature alphabet elseType branches hTargetRelated with
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
      have hOuterEdge : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
          (.child (i + 1) q) env label (TypeOfferSummary.mk current future)
          (.child (i + 1) q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
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
                (.xoffer alphabet elseType branches) hWhole i action branchType hBranchesEq
                (hBranchFuelStrict (action, branchType) hBranchMem) t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child (i + 1) q', hOuterEdge, ?_⟩
      exact relationMembership_xoffer_branch signature alphabet elseType branches
        hBranchesEq hChildTargetRelated
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
        (.xoffer alphabet elseType branches) (.child (i + 1) q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.xoffer alphabet elseType branches) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.xoffer alphabet elseType branches) hEdge)]
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
                (.xoffer alphabet elseType branches) hWhole i action branchType hBranchesEq
                (hBranchFuelStrict (action, branchType) hBranchMem) t hStateMem]
      have hTargetEq : state' = .child (i + 1) childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_xoffer_cases signature alphabet elseType branches hTargetRelated with
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
    ∀ (alphabet : PactTypeAlphabet)
      (branches : List (BareMessage × PactType)),
      PactType.BranchesAlphabetCoherent alphabet branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) →
      StepIffStatement signature (parallelTypeBranches branches) := by
  intro alphabet branches
  induction branches with
  | nil =>
      intro _ _
      change StepIffStatement signature (.skip PactTypeAlphabet.empty)
      exact correspondence_skip_stepIff signature PactTypeAlphabet.empty
  | cons branch rest ih =>
      intro hAlphabetBranches hBranchesIH
      rcases branch with ⟨action, processType⟩
      have hAllAlphabet := hAlphabetBranches
      simp only [PactType.BranchesAlphabetCoherent] at hAlphabetBranches
      have hProcessTypeIH : StepIffStatement signature processType := by
        intro residual residual' state env label offers hRelated hSymbol
        exact hBranchesIH action processType List.mem_cons_self hRelated hSymbol
      have hSingletonIH : ∀ a b, (a, b) ∈ [(action, processType)] →
          StepIffStatement signature b := by
        intro a b hMem
        rw [List.mem_singleton] at hMem
        rw [show b = processType from congrArg Prod.snd hMem]
        intro residual residual' state env label offers hRelated hSymbol
        exact hProcessTypeIH hRelated hSymbol
      have hRestBranchesIH : ∀ a b, (a, b) ∈ rest →
          StepIffStatement signature b := by
        intro a b hMem residual residual' state env label offers hRelated hSymbol
        exact hBranchesIH a b (List.mem_cons_of_mem _ hMem) hRelated hSymbol
      cases rest with
      | nil =>
          change StepIffStatement signature
            (.xoffer processType.alphabet (.skip processType.alphabet)
              [(action, processType)])
          exact correspondence_xoffer_stepIff signature processType.alphabet
            (.skip processType.alphabet) [(action, processType)]
            (correspondence_skip_stepIff signature processType.alphabet)
            hSingletonIH
      | cons next tail =>
          have hRestIH : StepIffStatement signature
              (parallelTypeBranches (next :: tail)) := by
            intro residual residual' state env label offers hRelated hSymbol
            exact ih hAlphabetBranches.2.2 hRestBranchesIH hRelated hSymbol
          have hWholeCoherent :=
            (parallelTypeBranches_alphabet_coherent
              (alphabet := alphabet) (branches :=
                (action, processType) :: next :: tail) (by simp)
              hAllAlphabet).2
          have hLeftIH : StepIffStatement signature
              (singletonTypeXOffer (action, processType)) := by
            intro residual residual' state env label offers hRelated hSymbol
            exact correspondence_xoffer_stepIff signature
              processType.alphabet (.skip processType.alphabet)
              [(action, processType)]
              (correspondence_skip_stepIff signature processType.alphabet)
              hSingletonIH hRelated hSymbol
          have hParIH : StepIffStatement signature
              (parallelType (singletonTypeXOffer (action, processType))
                (parallelTypeBranches (next :: tail)) ∅) := by
            intro residual residual' state env label offers hRelated hSymbol
            exact correspondence_par_stepIff signature
              (PactTypeAlphabet.mergeHidden
                (singletonTypeXOffer (action, processType)).alphabet
                (parallelTypeBranches (next :: tail)).alphabet ∅)
              (singletonTypeXOffer (action, processType))
              (parallelTypeBranches (next :: tail)) ∅ (by simp)
              (by simpa [parallelType] using hWholeCoherent)
              hLeftIH hRestIH hRelated hSymbol
          intro residual residual' state env label offers hRelated hSymbol
          simpa [parallelTypeBranches] using hParIH hRelated hSymbol

/-- Step correspondence for the parallel singleton-offer product generated for a
specific enabled branch below a conjunctive offer, by induction on the finite
branch list, reusing the exclusive-offer/sequence/parallel cases already proved. -/
theorem correspondence_parallelTypeBranchesSelecting_stepIff
    (signature : TypeAlphabet) :
    ∀ (alphabet : PactTypeAlphabet)
      (branches : List (BareMessage × PactType)),
      PactType.BranchesAlphabetCoherent alphabet branches →
      (∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) →
      ∀ selected ∈ branches,
        StepIffStatement signature (parallelTypeBranchesSelecting selected branches) := by
  intro alphabet branches
  induction branches with
  | nil =>
      intro _ _ selected hMem
      cases hMem
  | cons branch rest ih =>
      intro hAlphabetBranches hBranchesIH selected hMem
      rcases branch with ⟨action, processType⟩
      have hAllAlphabet := hAlphabetBranches
      simp only [PactType.BranchesAlphabetCoherent] at hAlphabetBranches
      have hProcessTypeIH : StepIffStatement signature processType := by
        intro residual residual' state env label offers hRelated hSymbol
        exact hBranchesIH action processType List.mem_cons_self hRelated hSymbol
      have hSingletonIH : ∀ a b, (a, b) ∈ [(action, processType)] →
          StepIffStatement signature b := by
        intro a b hMem'
        rw [List.mem_singleton] at hMem'
        rw [show b = processType from congrArg Prod.snd hMem']
        intro residual residual' state env label offers hRelated hSymbol
        exact hProcessTypeIH hRelated hSymbol
      have hRestBranchesIH : ∀ a b, (a, b) ∈ rest →
          StepIffStatement signature b := by
        intro a b hMem' residual residual' state env label offers hRelated hSymbol
        exact hBranchesIH a b (List.mem_cons_of_mem _ hMem') hRelated hSymbol
      rw [List.mem_cons] at hMem
      cases rest with
      | nil =>
          rcases hMem with hEq | hMem
          · have hSelectedEq : selected = (action, processType) := hEq
            subst selected
            have hSeqIH : StepIffStatement signature
              (.seq processType.alphabet
                (.message processType.alphabet action.1 action.2) processType) := by
              intro residual residual' state env label offers hRelated hSymbol
              exact correspondence_seq_stepIff signature processType.alphabet
                (.message processType.alphabet action.1 action.2) processType
                (correspondence_message_stepIff signature processType.alphabet
                  action.1 action.2) hProcessTypeIH hRelated hSymbol
            rw [parallelTypeBranchesSelecting_singleton_self]
            intro residual residual' state env label offers hRelated hSymbol
            exact hSeqIH hRelated hSymbol
          · cases hMem
      | cons next tail =>
          intro residual residual' state env label offers hRelated hSymbol
          by_cases hSelf : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting] at hRelated hSymbol ⊢
            have hRestPlainIH : StepIffStatement signature
                (parallelTypeBranches (next :: tail)) := by
              intro residual residual' state env label offers hRelated hSymbol
              exact correspondence_parallelTypeBranches_stepIff signature alphabet
                (next :: tail) hAlphabetBranches.2.2 hRestBranchesIH
                hRelated hSymbol
            have hWholeCoherent :=
                (parallelTypeBranchesSelecting_alphabet_coherent
                  (alphabet := alphabet) List.mem_cons_self hAllAlphabet).2
            have hHeadIH : StepIffStatement signature
                (selectedTypeBranch (action, processType)) := by
              intro residual residual' state env label offers hRelated hSymbol
              exact correspondence_seq_stepIff signature processType.alphabet
                (.message processType.alphabet action.1 action.2) processType
                (correspondence_message_stepIff signature processType.alphabet
                  action.1 action.2) hProcessTypeIH hRelated hSymbol
            have hParIH : StepIffStatement signature
                (parallelType (selectedTypeBranch (action, processType))
                  (parallelTypeBranches (next :: tail)) ∅) := by
              intro residual residual' state env label offers hRelated hSymbol
              exact correspondence_par_stepIff signature
                (PactTypeAlphabet.mergeHidden
                  (selectedTypeBranch (action, processType)).alphabet
                  (parallelTypeBranches (next :: tail)).alphabet ∅)
                (selectedTypeBranch (action, processType))
                (parallelTypeBranches (next :: tail)) ∅ (by simp)
                (by simpa [parallelTypeBranchesSelecting, parallelType]
                  using hWholeCoherent)
                hHeadIH hRestPlainIH hRelated hSymbol
            exact hParIH hRelated hSymbol
          · rcases hMem with hEq | hMemRest
            · exact absurd hEq.symm hSelf
            · simp [parallelTypeBranchesSelecting, hSelf] at hRelated hSymbol ⊢
              have hRestIH : StepIffStatement signature
                  (parallelTypeBranchesSelecting selected (next :: tail)) := by
                intro residual residual' state env label offers hRelated hSymbol
                exact ih hAlphabetBranches.2.2 hRestBranchesIH selected hMemRest
                  hRelated hSymbol
              have hWholeCoherent :=
                (parallelTypeBranchesSelecting_alphabet_coherent
                  (alphabet := alphabet)
                  (List.mem_cons_of_mem (action, processType) hMemRest)
                  hAllAlphabet).2
              have hHeadIH : StepIffStatement signature
                  (singletonTypeXOffer (action, processType)) := by
                intro residual residual' state env label offers hRelated hSymbol
                exact correspondence_xoffer_stepIff signature
                  processType.alphabet (.skip processType.alphabet)
                  [(action, processType)]
                  (correspondence_skip_stepIff signature processType.alphabet)
                  hSingletonIH hRelated hSymbol
              have hParIH : StepIffStatement signature
                  (parallelType (singletonTypeXOffer (action, processType))
                    (parallelTypeBranchesSelecting selected (next :: tail)) ∅) := by
                intro residual residual' state env label offers hRelated hSymbol
                exact correspondence_par_stepIff signature
                  (PactTypeAlphabet.mergeHidden
                    (singletonTypeXOffer (action, processType)).alphabet
                    (parallelTypeBranchesSelecting selected
                      (next :: tail)).alphabet ∅)
                  (singletonTypeXOffer (action, processType))
                  (parallelTypeBranchesSelecting selected (next :: tail)) ∅
                  (by simp)
                  (by simpa [parallelTypeBranchesSelecting, hSelf, parallelType]
                    using hWholeCoherent)
                  hHeadIH hRestIH hRelated hSymbol
              exact hParIH hRelated hSymbol

set_option maxHeartbeats 4000000 in
/-- Step correspondence for conjunctive offer `⋀(τ0,B)`. -/
theorem correspondence_offer_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hAlphabetBranches :
      PactType.BranchesAlphabetCoherent alphabet branches)
    (hElseIH : StepIffStatement signature elseType)
    (hBranchesIH :
      ∀ action branchType, (action, branchType) ∈ branches →
        StepIffStatement signature branchType) :
    StepIffStatement signature (.offer alphabet elseType branches) := by
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
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hBranchFuelStrict : ∀ selected : BareMessage × PactType,
      typeCompilationFuel (parallelTypeBranchesSelecting selected branches) + 1 ≤
        typeCompilationFuel (.offer alphabet elseType branches) := by
    intro selected
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
        buildSelectedConjunctiveOfferAutomaton signature branches
          (compileTypeFuel signature (typeCompilationFuel elseType) elseType)
          (branches.map fun selected => (selected.1, compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
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
  rcases relationMembership_offer_cases signature alphabet elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, selected, q, hSelectedEq, hStateEq, hBranchRelated⟩
  · -- root case: `residual` represents `⋀(τ0,B)` itself
    simp only [Prod.mk.injEq] at hRoot
    obtain ⟨hResidualEq, hStateEq⟩ := hRoot
    subst hResidualEq; subst hStateEq
    have hFutureElseEq : computeFutureOf signature (.offer alphabet elseType branches)
        (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
          elseType).initial) = typeFutureOffers elseType := by
      rw [computeFutureOf_selectedConjunctiveOffer_else signature elseType branches
        (.offer alphabet elseType branches) hWhole hElseFuelStrict
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSignatureSymbol
    have hWF : env.WellFormed := localEnvironment_wellFormed signature hEnvMem
    have hRootRelated : relationMembership
        (buildRelationSet (.offer alphabet elseType branches)
          (compileType signature (.offer alphabet elseType branches)))
        (.offer alphabet elseType branches) TypeAutomatonState.root := by
      simpa using hRelated
    have hRootFuture : computeFutureOf signature (.offer alphabet elseType branches)
        TypeAutomatonState.root = typeFutureOffers (.offer alphabet elseType branches) :=
      helper_h15_future_offers_agree signature hRootRelated
    constructor
    · intro hStep
      obtain ⟨-, hOffers⟩ := hStep
      generalize hLabelEq : label = actualLabel at hOffers
      generalize hTargetEq : residual' = actualTarget at hOffers
      generalize hCurrentEq : current = actualCurrent at hOffers
      generalize hFutureEq : future = actualFuture at hOffers
      cases hOffers with
      | offer_some _ _ _ _ enabled hPremise =>
          obtain ⟨hWF', hEnabledMem, hEnabled⟩ := hPremise
          obtain ⟨index, hSelectedGet⟩ := List.mem_iff_getElem?.mp hEnabledMem
          have hFutureBranchEq : computeFutureOf signature (.offer alphabet elseType branches)
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) =
              typeFutureOffers (parallelTypeBranchesSelecting enabled branches) := by
            rw [computeFutureOf_selectedConjunctiveOffer_branch signature elseType branches
              (.offer alphabet elseType branches) hWhole index enabled hSelectedGet
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
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root (.child (index + 1) (compileTypeFuel signature
                (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
                (parallelTypeBranchesSelecting enabled branches)).initial) env TypeLabel.silent
              (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches))) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hEnabledPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureBranchEq
          have hEnabledStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk ∅ (typeFutureOffers
                (parallelTypeBranchesSelecting enabled branches)))
              (parallelTypeBranchesSelecting enabled branches) :=
            ⟨TypeTransition.offer_some env alphabet elseType branches enabled
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env alphabet elseType branches enabled
                ⟨hWF, hEnabledMem, hEnabled⟩⟩
          refine ⟨.child (index + 1) (compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting enabled branches))
            (parallelTypeBranchesSelecting enabled branches)).initial, hEdgeFact, ?_⟩
          exact relationMembership_offer_selected signature alphabet elseType branches hSelectedGet
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting enabled branches)
              (compileType signature (parallelTypeBranchesSelecting enabled branches)))
      | offer_else _ _ _ _ hPremise =>
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
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              (.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
                elseType).initial) := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root (.child 0 (compileTypeFuel signature
                (typeCompilationFuel elseType) elseType).initial) env TypeLabel.silent
              (TypeOfferSummary.mk (typeBranchActions branches) (typeFutureOffers elseType))
              hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hElsePending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            simpa [childState] using hFutureElseEq
          have hElseStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeBranchActions branches)
                (typeFutureOffers elseType)) elseType :=
            ⟨TypeTransition.offer_else env alphabet elseType branches
              ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
              TypeOffers.offer_else env alphabet elseType branches
                ⟨hWF, hNoImmediate, hResolvedNeeds⟩⟩
          refine ⟨.child 0 (compileTypeFuel signature (typeCompilationFuel elseType)
            elseType).initial, hEdgeFact, ?_⟩
          exact relationMembership_offer_else signature alphabet elseType branches
            (buildRelationSet_initial elseType (compileType signature elseType))
      | offer_wait _ _ _ _ hPremise =>
          obtain ⟨hWF', hNoImmediate, hUnresolved, hClock⟩ := hPremise
          have hSignatureSymbol' :
              TypeAutomatonSymbol.mk env TypeLabel.silent
                (TypeOfferSummary.mk (typeWaitingOffers env branches)
                  (typeFutureOffers (.offer alphabet elseType branches) \
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
          have hEdgeFact : (compileType signature (.offer alphabet elseType branches)).HasEdge
              TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) TypeAutomatonState.root := by
            rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
              TypeAutomatonState.root TypeAutomatonState.root env TypeLabel.silent
              (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) hSignatureSymbol']
            rw [hWhole]
            refine ⟨_, hWaitPending, rfl, rfl, rfl, rfl, ?_, rfl⟩
            show computeFutureOf signature (.offer alphabet elseType branches) TypeAutomatonState.root \
              typeWaitingOffers env branches = typeFutureOffers (.offer alphabet elseType branches) \
                typeWaitingOffers env branches
            rw [hRootFuture]
          have hWaitStep : DecoratedTypeTransition env (.offer alphabet elseType branches)
              TypeLabel.silent (TypeOfferSummary.mk (typeWaitingOffers env branches)
                (typeFutureOffers (.offer alphabet elseType branches) \
                  typeWaitingOffers env branches)) (.offer alphabet elseType branches) :=
            ⟨TypeTransition.offer_wait env alphabet elseType branches
              ⟨hWF, hNoImmediate, hUnresolved, hClock⟩,
              TypeOffers.offer_wait env alphabet elseType branches
                ⟨hWF, hNoImmediate, hUnresolved, hClock⟩⟩
          refine ⟨TypeAutomatonState.root, hEdgeFact, ?_⟩
          exact relationMembership_offer_root signature alphabet elseType branches
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer alphabet elseType branches) TypeAutomatonState.root state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
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
              (.offer alphabet elseType branches) hWhole index (branchAction, branchType') hSelectedGet
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
          rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
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
            exact ⟨TypeTransition.offer_some env alphabet elseType branches
              (branchAction, branchType')
              ⟨hWF, hEnabledMem, hEnabled⟩,
              TypeOffers.offer_some env alphabet elseType branches
                (branchAction, branchType')
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
        have hFutureEq : future = typeFutureOffers (.offer alphabet elseType branches) \
            typeWaitingOffers env branches := by
          rw [← hPFuture, hRootFuture]
          rfl
        rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
          with hRootAgain | ⟨qAgain, hStateEqAgain, hElseRelatedAgain⟩ |
            ⟨iAgain, selectedAgain, qAgain, hSelectedEqAgain, hStateEqAgain,
              hBranchRelatedAgain⟩
        · simp only [Prod.mk.injEq] at hRootAgain
          have hResidualEq : residual' = .offer alphabet elseType branches := hRootAgain.1
          rw [hLabelEq, hResidualEq, hCurrentEq, hFutureEq]
          exact ⟨TypeTransition.offer_wait env alphabet elseType branches
            ⟨hWF, hNoImmediate, hUnresolved, hClock⟩,
            TypeOffers.offer_wait env alphabet elseType branches
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
        rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated
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
          exact ⟨TypeTransition.offer_else env alphabet elseType branches
            ⟨hWF, hNoImmediate, hResolvedNeeds⟩,
            TypeOffers.offer_else env alphabet elseType branches
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
      have hOuterEdge : (compileType signature (.offer alphabet elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
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
                (.offer alphabet elseType branches) hWhole hElseFuelStrict t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child 0 q', hOuterEdge, ?_⟩
      exact relationMembership_offer_else signature alphabet elseType branches
        hChildTargetRelated
    · rintro ⟨state', hEdge, hTargetRelated⟩
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.offer alphabet elseType branches) (.child 0 q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)]
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
                (.offer alphabet elseType branches) hWhole hElseFuelStrict t hStateMem]
      have hTargetEq : state' = .child 0 childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated with
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
      correspondence_parallelTypeBranchesSelecting_stepIff signature alphabet
        branches hAlphabetBranches hBranchesIH selected hSelectedMem
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
      have hOuterEdge : (compileType signature (.offer alphabet elseType branches)).HasEdge
          (.child (i + 1) q) env label (TypeOfferSummary.mk current future)
          (.child (i + 1) q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.offer alphabet elseType branches)
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
                (.offer alphabet elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) t hStateMem]
              simpa [childFutureSpec, hSpec] using hCFuture
        · simp [childPendingEdge, childState, hCTarget]
      refine ⟨.child (i + 1) q', hOuterEdge, ?_⟩
      exact relationMembership_offer_selected signature alphabet elseType branches
        hSelectedEq
        hChildTargetRelated
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
        (.offer alphabet elseType branches) (.child (i + 1) q) state' env label
        (TypeOfferSummary.mk current future)
        (compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)).mp hEdge
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
            compileType_hasEdge_symbol_mem signature (.offer alphabet elseType branches) hEdge)]
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
                (.offer alphabet elseType branches) hWhole i selected hSelectedEq
                (hBranchFuelStrict selected) t hStateMem]
      have hTargetEq : state' = .child (i + 1) childEdge.target := by
        rw [← hPTarget, hChildEdgeEq]; rfl
      rw [hTargetEq] at hTargetRelated
      rcases relationMembership_offer_cases signature alphabet elseType branches hTargetRelated with
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) (name : String) :
    StepIffStatement signature (.var alphabet name) := by
  intro residual residual' state env label offers hRelated hSymbol
  obtain ⟨hResidual, hState⟩ :=
    relationMembership_var_cases signature alphabet name hRelated
  subst hResidual
  subst hState
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label offers ∈ signature.transitionAlphabet := by
    simpa [compileType] using hSymbol
  constructor
  · intro hStep
    cases hStep.1
  · rintro ⟨state', hEdge, -⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge signature (.var alphabet name)
      TypeAutomatonState.root state' env label offers hSignatureSymbol] at hEdge
    obtain ⟨edge, hPending, -, -, hLabel, -, -, -⟩ := hEdge
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image] at hPending
    obtain ⟨environment, -, rfl⟩ := hPending
    simp at hLabel

private theorem supportsBranches_of_mem
    (signature : TypeAlphabet) {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : signature.SupportsBranches branches)
    (hMem : (action, branchType) ∈ branches) :
    signature.Supports branchType := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      have hAll :
          ((headAction ∈ signature.boundary ∨
              headAction.1 ∈ signature.interface) ∧
            signature.Supports headType ∧
            signature.SupportsBranches rest) := by
        simpa only [TypeAlphabet.SupportsBranches] using hBranches
      have hPieces : signature.Supports headType ∧
          signature.SupportsBranches rest := by
        exact hAll.2
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq; exact hPieces.1
      · exact ih hPieces.2 hMemRest

private theorem branchesAlphabetWellFormed_of_mem
    {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    branchType.AlphabetWellFormed := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMemRest
      · cases hEq
        exact hBranches.2.2.1
      · exact ih hBranches.2.2.2 hMemRest

/-- Step correspondence for all constructors, arranged as the Lemma 4.5 induction. -/
theorem correspondence_stepIff
    (signature : TypeAlphabet) (processType : PactType)
    (hAdmissible : AdmissibleType signature processType) :
    StepIffStatement signature processType := by
  rcases hAdmissible with
    ⟨hSignatureWF, hSupports, hAlphabetWF, hRegular⟩
  clear hSignatureWF hRegular
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType hSupports hAlphabetWF with
  | _ n ih =>
      cases processType with
      | message alphabet msg dir =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_message_stepIff signature alphabet msg dir
            hRelated hSymbol
      | progress alphabet pid =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_progress_stepIff signature alphabet pid
            hRelated hSymbol
      | tock alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_tock_stepIff signature alphabet hRelated hSymbol
      | skip alphabet =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_skip_stepIff signature alphabet hRelated hSymbol
      | choice alphabet left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.1
              hAlphabetWF.2.2.2.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2
              hAlphabetWF.2.2.2.2 rfl hRelated hSymbol
          exact correspondence_choice_stepIff signature alphabet left right
            hLeftIH hRightIH hRelated hSymbol
      | seq alphabet first second =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hFirstIH : StepIffStatement signature first := by
            have hFirstSize : sizeOf first < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf first) hFirstSize first hSupports.1
              hAlphabetWF.2.2.2.1 rfl hRelated hSymbol
          have hSecondIH : StepIffStatement signature second := by
            have hSecondSize : sizeOf second < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf second) hSecondSize second hSupports.2
              hAlphabetWF.2.2.2.2 rfl hRelated hSymbol
          exact correspondence_seq_stepIff signature alphabet first second
            hFirstIH hSecondIH hRelated hSymbol
      | par alphabet left right interface =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          have hParentCoherent :
              (.par alphabet left right interface : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.2.1
              hAlphabetWF.2.2.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2.2
              hAlphabetWF.2.2.2 rfl hRelated hSymbol
          exact correspondence_par_stepIff signature alphabet left right interface
            hSupports.1 hParentCoherent hLeftIH hRightIH hRelated hSymbol
      | var alphabet id =>
          intro residual residual' state env label offers hRelated hSymbol
          exact correspondence_var_stepIff signature alphabet id hRelated hSymbol
      | recur alphabet id body =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hBodyIH : StepIffStatement signature body := by
            have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf body) hBodySize body hSupports hAlphabetWF.2.2 rfl
              hRelated hSymbol
          exact correspondence_recur_stepIff signature alphabet id body hBodyIH
            hRelated hSymbol
      | fairChoice alphabet id left right =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hLeftIH : StepIffStatement signature left := by
            have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf left) hLeftSize left hSupports.2.1
              hAlphabetWF.2.2.2.2.1 rfl hRelated hSymbol
          have hRightIH : StepIffStatement signature right := by
            have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf right) hRightSize right hSupports.2.2
              hAlphabetWF.2.2.2.2.2 rfl hRelated hSymbol
          exact correspondence_fairChoice_stepIff signature alphabet id left right
            hLeftIH hRightIH hRelated hSymbol
      | xoffer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType hSupports.1
              hAlphabetWF.2.2.1 rfl hRelated hSymbol
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
            have hBranchSupports : signature.Supports branchType :=
              supportsBranches_of_mem signature hSupports.2 hMember
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType hBranchSupports
              hBranchAlphabetWF rfl hRelated hSymbol
          exact correspondence_xoffer_stepIff signature alphabet elseType branches
            hElseIH hBranchesIH hRelated hSymbol
      | offer alphabet elseType branches =>
          intro residual residual' state env label offers hRelated hSymbol
          have hOfferCoherent :
              (.offer alphabet elseType branches : PactType).AlphabetCoherent :=
            PactType.alphabetCoherent_of_wellFormed _ hAlphabetWF
          simp only [PactType.AlphabetCoherent] at hOfferCoherent
          simp only [TypeAlphabet.Supports] at hSupports
          simp only [PactType.AlphabetWellFormed] at hAlphabetWF
          have hElseIH : StepIffStatement signature elseType := by
            have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf elseType) hElseSize elseType hSupports.1
              hAlphabetWF.2.2.1 rfl hRelated hSymbol
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
            have hBranchSupports : signature.Supports branchType :=
              supportsBranches_of_mem signature hSupports.2 hMember
            have hBranchAlphabetWF : branchType.AlphabetWellFormed :=
              branchesAlphabetWellFormed_of_mem hAlphabetWF.2.2.2 hMember
            intro residual residual' state env label offers hRelated hSymbol
            exact ih (sizeOf branchType) hBranchSize branchType hBranchSupports
              hBranchAlphabetWF rfl hRelated hSymbol
          exact correspondence_offer_stepIff signature alphabet elseType branches
            hOfferCoherent.2.2 hElseIH hBranchesIH hRelated hSymbol

end

end Pact
