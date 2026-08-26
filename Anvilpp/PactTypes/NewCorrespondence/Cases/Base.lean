import Anvilpp.PactTypes.NewCorrespondence.TypeAutoRelCore
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers
import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.Top
import Anvilpp.PactTypes.NewCorrespondence.Helpers.AlphabetPreservation
import Anvilpp.PactTypes.NewCorrespondence.Helpers.EnvironmentAndAlphabet

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
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabetFor_environment_mem signature alphabet
      hSignatureSymbol
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
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabetFor_environment_mem signature alphabet
      hSignatureSymbol
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
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabetFor_environment_mem signature alphabet
      hSignatureSymbol
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
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  have hEnvironment :=
    NewCorrespondence.transitionAlphabetFor_environment_mem signature alphabet
      hSignatureSymbol
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

/-- Step correspondence for ordinary binary choice `τ1 + τ2`. -/
theorem correspondence_choice_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.choice alphabet left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's selection edges match the
  -- choice rule, and `hLeftIH`/`hRightIH` handle everything below the root.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor alphabet := by
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
  have hLeftProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 0 visited) =
        stateProductInfo left visited := by
    intro visited
    show stateProductInfoFuel (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) (.child 0 visited) =
      stateProductInfoFuel (typeCompilationFuel left) left visited
    rw [hFuelEq]
    exact stateProductInfoFuel_eq_of_sufficient' left visited
      (le_max_left _ _) le_rfl
  have hRightProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 1 visited) =
        stateProductInfo right visited := by
    intro visited
    show stateProductInfoFuel (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) (.child 1 visited) =
      stateProductInfoFuel (typeCompilationFuel right) right visited
    rw [hFuelEq]
    exact stateProductInfoFuel_eq_of_sufficient' right visited
      (le_max_right _ _) le_rfl
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
        hLeftProductInfo
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
        hRightProductInfo
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabetFor_environment_mem signature alphabet hSignatureSymbol
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
              signature.transitionAlphabetFor alphabet := by
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
              signature.transitionAlphabetFor alphabet := by
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
        signature.transitionAlphabetFor left.alphabet
      simpa [hLeftAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ := (hLeftIH hLeftRelated hLeftSymbol).mp hStep
      have hOuterEdge : (compileType signature (.choice alphabet left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
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
                (.choice alphabet left right) hWhole hFuelLeft hLeftProductInfo
                t hStateMem]
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
          (by simpa [compileType] using hLeftSymbol)]
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
                (.choice alphabet left right) hWhole hFuelLeft hLeftProductInfo
                t hStateMem]
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
        signature.transitionAlphabetFor right.alphabet
      simpa [hRightAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hRightIH hRightRelated hRightSymbol).mp hStep
      have hOuterEdge : (compileType signature (.choice alphabet left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.choice alphabet left right)
          (.child 1 q) (.child 1 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
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
                (.choice alphabet left right) hWhole hFuelRight hRightProductInfo
                t hStateMem]
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
          (by simpa [compileType] using hRightSymbol)]
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
                (.choice alphabet left right) hWhole hFuelRight hRightProductInfo
                t hStateMem]
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
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftIH : StepIffStatement signature left)
    (hRightIH : StepIffStatement signature right) :
    StepIffStatement signature (.fairChoice alphabet bid left right) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove the root's two selection edges match
  -- `fair_left`/`fair_right`, and `hLeftIH`/`hRightIH` handle the children.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor alphabet := by
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
  have hLeftProductInfo : ∀ visited,
      stateProductInfo (.fairChoice alphabet bid left right) (.child 0 visited) =
        stateProductInfo left visited := by
    intro visited
    show stateProductInfoFuel
        (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) (.child 0 visited) =
      stateProductInfoFuel (typeCompilationFuel left) left visited
    rw [hFuelEq]
    exact stateProductInfoFuel_eq_of_sufficient' left visited
      (le_max_left _ _) le_rfl
  have hRightProductInfo : ∀ visited,
      stateProductInfo (.fairChoice alphabet bid left right) (.child 1 visited) =
        stateProductInfo right visited := by
    intro visited
    show stateProductInfoFuel
        (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) (.child 1 visited) =
      stateProductInfoFuel (typeCompilationFuel right) right visited
    rw [hFuelEq]
    exact stateProductInfoFuel_eq_of_sufficient' right visited
      (le_max_right _ _) le_rfl
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
        hLeftProductInfo
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
        hRightProductInfo
        (compileTypeFuel signature (typeCompilationFuel right) right).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl)]
      show computeFutureOf signature right (compileType signature right).initial =
        typeFutureOffers right
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial right (compileType signature right))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabetFor_environment_mem signature alphabet hSignatureSymbol
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
                signature.transitionAlphabetFor alphabet := by
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
                signature.transitionAlphabetFor alphabet := by
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
        signature.transitionAlphabetFor left.alphabet
      simpa [hLeftAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ := (hLeftIH hLeftRelated hLeftSymbol).mp hStep
      have hOuterEdge : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
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
                (.fairChoice alphabet bid left right) hWhole hFuelLeft
                hLeftProductInfo t hStateMem]
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
          (by simpa [compileType] using hLeftSymbol)]
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
                (.fairChoice alphabet bid left right) hWhole hFuelLeft
                hLeftProductInfo t hStateMem]
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
        signature.transitionAlphabetFor right.alphabet
      simpa [hRightAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hRightIH hRightRelated hRightSymbol).mp hStep
      have hOuterEdge : (compileType signature (.fairChoice alphabet bid left right)).HasEdge
          (.child 1 q) env label (TypeOfferSummary.mk current future) (.child 1 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.fairChoice alphabet bid left right)
          (.child 1 q) (.child 1 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
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
                (.fairChoice alphabet bid left right) hWhole hFuelRight
                hRightProductInfo t hStateMem]
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
          (by simpa [compileType] using hRightSymbol)]
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
                (.fairChoice alphabet bid left right) hWhole hFuelRight
                hRightProductInfo t hStateMem]
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
    (hFirstAlphabet : first.alphabet = alphabet)
    (hSecondAlphabet : second.alphabet = alphabet)
    (hFirstIH : StepIffStatement signature first)
    (hSecondIH : StepIffStatement signature second) :
    StepIffStatement signature (.seq alphabet first second) := by
  intro residual residual' state env label offers hRelated hSymbol
  -- Given this, now we need to prove a `τ1`-step from `hFirstIH` matches
  -- `seq`/`seq_fuse` by its target, and `hSecondIH` handles a right state.
  rcases offers with ⟨current, future⟩
  have hSignatureSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabetFor alphabet := by
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
              signature.transitionAlphabetFor first.alphabet
            simpa [hFirstAlphabet] using
              transitionAlphabetFor_of_typeOffers_target_subset signature
                alphabet hSignatureSymbol hChildStep.2
                (typeFutureOffers_subset_sequence_left_sdiff_union
                  alphabet leftTarget second current)
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 0 q', compileType_seq_lift_left_step signature alphabet
            first second hRelated hLeftRelated hChildTargetRelated hNonFinal
            hChildStep hSignatureSymbol hChildEdge⟩
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
              signature.transitionAlphabetFor first.alphabet
            simpa [hFirstAlphabet] using
              transitionAlphabetFor_of_typeOffers_target_subset signature
                alphabet hSignatureSymbol hChildOffers
                (by simp [typeFutureOffers, typeFutureOffersFuel])
          have hChildStep : DecoratedTypeTransition env leftResidual label
              (TypeOfferSummary.mk current childFuture)
              (.skip offerSkipAlphabet) :=
            ⟨hChildOffers.toTypeTransition, hChildOffers⟩
          rcases (hFirstIH hLeftRelated hChildSymbol).mp hChildStep with
            ⟨q', hChildEdge, hChildTargetRelated⟩
          exact ⟨.child 1 (compileType signature second).initial,
            compileType_seq_lift_left_fuse signature alphabet
              offerSkipAlphabet first second hRelated hLeftRelated
              hChildTargetRelated hChildStep hSignatureSymbol hChildEdge⟩
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
            (TypeOfferSummary.mk current future) ∈
              signature.transitionAlphabetFor second.alphabet
        simpa [hSecondAlphabet] using hSignatureSymbol
      rcases (hSecondIH hRightRelated hChildSymbol).mp hStep with
        ⟨q', hChildEdge, hChildTargetRelated⟩
      exact compileType_seq_lift_right_step signature alphabet first second
        hSecondAlphabet hRelated hRightRelated hChildTargetRelated hStep
        hChildEdge
  · rintro ⟨state', hEdge, hTargetRelated⟩
    cases compileType_seq_edge_cases signature alphabet first second
        hFirstAlphabet hSecondAlphabet hRelated hEdge hTargetRelated with
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
/-- Step correspondence for exclusive offer `⨁(τ0,B)`. -/
theorem correspondence_xoffer_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hBranchAlphabet : ∀ action branchType,
      (action, branchType) ∈ branches → branchType.alphabet = alphabet)
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
        signature.transitionAlphabetFor alphabet := by
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
  have hElseProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited := by
    intro visited
    show stateProductInfoFuel
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) (.child 0 visited) =
      stateProductInfoFuel (typeCompilationFuel elseType) elseType visited
    rw [hFuelEq]
    exact stateProductInfoFuel_eq_of_sufficient' elseType visited
      (le_max_left _ _) le_rfl
  have hBranchProductInfo : ∀ i action branchType,
      branches[i]? = some (action, branchType) → ∀ visited,
        stateProductInfo (.xoffer alphabet elseType branches)
            (.child (i + 1) visited) =
          stateProductInfo branchType visited := by
    intro i action branchType hBranch visited
    show stateProductInfoFuel
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) (.child (i + 1) visited) =
      stateProductInfoFuel (typeCompilationFuel branchType) branchType visited
    rw [hFuelEq]
    simp only [stateProductInfoFuel, hBranch]
    exact stateProductInfoFuel_eq_of_sufficient' branchType visited
      (le_trans
        (typeCompilationFuel_le_typeBranchCompilationFuel branches
          (action, branchType) (List.mem_of_getElem? hBranch))
        (le_max_right _ _)) le_rfl
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
        hElseProductInfo
        (compileTypeFuel signature (typeCompilationFuel elseType) elseType).initial
        (compileTypeFuel_initial_mem signature (typeCompilationFuel elseType) elseType
          le_rfl)]
      show computeFutureOf signature elseType (compileType signature elseType).initial =
        typeFutureOffers elseType
      exact helper_h15_future_offers_agree signature
        (buildRelationSet_initial elseType (compileType signature elseType))
    have hEnvMem : env ∈ signature.localEnvironments :=
      transitionAlphabetFor_environment_mem signature alphabet hSignatureSymbol
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
            (hBranchProductInfo index branchAction actualTarget hBranchGet)
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
              signature.transitionAlphabetFor alphabet := by
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
              signature.transitionAlphabetFor alphabet := by
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
                  typeWaitingOffers env branches)) ∈
              signature.transitionAlphabetFor alphabet := by
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
              (hBranchProductInfo index branchAction branchType' hBranchGet)
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
            hElseProductInfo
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
        signature.transitionAlphabetFor elseType.alphabet
      simpa [hElseAlphabet] using hSignatureSymbol
    constructor
    · intro hStep
      obtain ⟨q', hChildEdge, hChildTargetRelated⟩ :=
        (hElseIH hElseRelated hElseSymbol).mp hStep
      have hOuterEdge : (compileType signature (.xoffer alphabet elseType branches)).HasEdge
          (.child 0 q) env label (TypeOfferSummary.mk current future) (.child 0 q') := by
        rw [compileType_hasEdge_iff_hasResolvedEdge signature (.xoffer alphabet elseType branches)
          (.child 0 q) (.child 0 q') env label (TypeOfferSummary.mk current future)
          hSignatureSymbol]
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
                (.xoffer alphabet elseType branches) hWhole hElseFuelStrict
                hElseProductInfo t hStateMem]
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
          (by simpa [compileType] using hElseSymbol)]
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
                (.xoffer alphabet elseType branches) hWhole hElseFuelStrict
                hElseProductInfo t hStateMem]
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
        signature.transitionAlphabetFor branchType.alphabet
      simpa [hBranchAlphabet action branchType hBranchMem] using hSignatureSymbol
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
          hSignatureSymbol]
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
                (hBranchFuelStrict (action, branchType) hBranchMem)
                (hBranchProductInfo i action branchType hBranchesEq) t hStateMem]
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
          (by simpa [compileType] using hBranchSymbol)]
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
                (hBranchFuelStrict (action, branchType) hBranchMem)
                (hBranchProductInfo i action branchType hBranchesEq) t hStateMem]
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
      TypeAutomatonSymbol.mk env label offers ∈
        signature.transitionAlphabetFor alphabet := by
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

end

end Pact
