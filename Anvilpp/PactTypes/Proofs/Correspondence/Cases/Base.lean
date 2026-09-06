import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Variables
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Sequence
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.RecursionFoundations
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MainHelpers
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.FutureClosure
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.ExclusiveOffer
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.ChoiceRelations
import Anvilpp.PactTypes.Proofs.Correspondence.TypeAutoRelCore
import Anvilpp.PactTypes.Proofs.Correspondence.CompileWFHelpers
import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.AlphabetPreservation
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.EnvironmentAndAlphabet

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section
/-- Step correspondence for the `skip` constructor, stated for the new
relation-set presentation used by `PactSafety.type_automaton_correspondence`.

The compiled `skip` automaton has exactly the non-clock silent self-loop
that the operational `skip` type has, and no clock step. -/
theorem correspondence_skip_stepIff
     (alphabet : PactTypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.skip alphabet)
          (compileType (.skip alphabet)))
        residual state)
    (hSymbol : SymbolGuard (.skip alphabet) env offers) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType (.skip alphabet)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.skip alphabet)
            (compileType (.skip alphabet)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hEnvironment := hSymbol.1
  have hLocal := hEnvironment
  have hWellFormed := PactTypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_skip_cases alphabet
      hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases hStep with ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ _ conditions =>
        cases hOffers with
        | skip _ _ =>
            have hEdge := NewCorrespondence.compileType_skip_edge
              (alphabet := alphabet) hLocal conditions.2
            exact ⟨.root, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_skip_cases alphabet
      hRelated with
      ⟨hResidual, hState⟩
    subst residual
    subst state
    rcases NewCorrespondence.compileType_skip_edge_cases
      (alphabet := alphabet) hEdge with
      ⟨_hSource, hTarget, hLabel, hCurrent, hFuture, hClock⟩
    subst label
    subst current
    subst future
    subst state'
    have hTargetAccepting :
        TypeAutomatonState.root ∈
          (compileType (.skip alphabet)).accepting := by
      simp [compileType, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment]
    have hResidualTarget : residual' = .skip alphabet :=
      (NewCorrespondence.relationMembership_skip_cases alphabet
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
     (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.message alphabet msg dir)
          (compileType (.message alphabet msg dir)))
        residual state)
    (hSymbol : SymbolGuard (.message alphabet msg dir) env offers) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType (.message alphabet msg dir)).HasEdge state env label
          offers state' ∧
        relationMembership
          (buildRelationSet (.message alphabet msg dir)
            (compileType (.message alphabet msg dir)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hEnvironment := hSymbol.1
  have hLocal := hEnvironment
  have hWellFormed := PactTypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_message_cases alphabet
      msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | action _ _ _ _ conditions hAction =>
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
            ⟨TypeTransition.action env alphabet msg dir conditions hAction,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := NewCorrespondence.compileType_message_action_edge
            (alphabet := alphabet) msg dir
            hLocal conditions.2 hAction
          refine ⟨.final, hEdge, ?_⟩
          unfold relationMembership buildRelationSet buildRelationSetCore
          simp [typeCompilationFuel, buildRelationSetCoreFuel]
      | action_wait _ _ _ _ conditions hAction =>
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
            ⟨TypeTransition.action_wait env alphabet msg dir conditions hAction,
              by
                simpa [typeFutureOffers, typeFutureOffersFuel] using
                  hOffers⟩
          have hEdge := NewCorrespondence.compileType_message_wait_edge
            (alphabet := alphabet) msg dir
            hLocal conditions.2.1 conditions.2.2 hAction
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
                (alphabet := alphabet) msg dir
                hLocal conditions.2
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_message_cases alphabet
      msg dir hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_message_edge_cases
        (alphabet := alphabet) msg dir hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType (.message alphabet msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_message_cases
              alphabet msg dir hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        -- The compiled symbol's offers are drawn from this type's own actions.
        have hAction : (msg, dir) ∈ alphabet.actions := by
          have h := hSymbol.2
          simp only [PactTypeAlphabet.mem_localOfferSummaries_iff] at h
          have hIn := h.1 (Finset.mem_singleton_self ((msg, dir) : BareMessage))
          simpa only [PactTypeAlphabet.actions] using hIn
        exact ⟨TypeTransition.action env alphabet msg dir
            ⟨hWellFormed, hNeed⟩ hAction,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env alphabet msg dir ⟨hWellFormed, hNeed⟩ hAction⟩
      · rcases hWait with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock, hNoNeed⟩
        subst label
        subst current
        subst future
        subst state'
        have hResidualTarget : residual' = .message alphabet msg dir := by
          rcases NewCorrespondence.relationMembership_message_cases
              alphabet msg dir
              hTargetRelated with hTargetRoot | hTargetFinal
          · exact hTargetRoot.1
          · rcases hTargetFinal with ⟨_, hStateTarget⟩
            simp at hStateTarget
        subst residual'
        -- The compiled symbol's offers are drawn from this type's own actions.
        have hAction : (msg, dir) ∈ alphabet.actions := by
          have h := hSymbol.2
          simp only [PactTypeAlphabet.mem_localOfferSummaries_iff] at h
          have hIn := h.1 (Finset.mem_singleton_self ((msg, dir) : BareMessage))
          simpa only [PactTypeAlphabet.actions] using hIn
        exact ⟨TypeTransition.action_wait env alphabet msg dir
            ⟨hWellFormed, hNoNeed, hClock⟩ hAction,
          by
            simpa [typeFutureOffers, typeFutureOffersFuel, hAction] using
              TypeOffers.action_wait env alphabet msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩ hAction⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_message_edge_cases
        (alphabet := alphabet) msg dir hEdge
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
              (compileType (.message alphabet msg dir)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_message_cases
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
     (alphabet : PactTypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.tock alphabet)
          (compileType (.tock alphabet)))
        residual state)
    (hSymbol : SymbolGuard (.tock alphabet) env offers) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType (.tock alphabet)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.tock alphabet)
            (compileType (.tock alphabet)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hEnvironment := hSymbol.1
  have hLocal := hEnvironment
  have hWellFormed := PactTypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_tock_cases alphabet
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
            (alphabet := alphabet) hLocal conditions.2
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
            (alphabet := alphabet) hLocal conditions.2
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
                (alphabet := alphabet) hLocal conditions.2
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_tock_cases alphabet
      hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_tock_edge_cases
        (alphabet := alphabet) hEdge
      rcases hCases with hFire | hWait | hIdle
      · rcases hFire with ⟨_hSource, hTarget, hLabel, hCurrent, hFuture,
          hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType (.tock alphabet)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_tock_cases
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
          rcases NewCorrespondence.relationMembership_tock_cases
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
        (alphabet := alphabet) hEdge
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
              (compileType (.tock alphabet)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_tock_cases
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
     (alphabet : PactTypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated :
      relationMembership
        (buildRelationSet (.progress alphabet pid) (compileType (.progress alphabet pid)))
        residual state)
    (hSymbol : SymbolGuard (.progress alphabet pid) env offers) :
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType (.progress alphabet pid)).HasEdge state env label offers
          state' ∧
        relationMembership
          (buildRelationSet (.progress alphabet pid)
            (compileType (.progress alphabet pid)))
          residual' state') := by
  rcases offers with ⟨current, future⟩
  have hEnvironment := hSymbol.1
  have hLocal := hEnvironment
  have hWellFormed := PactTypeAlphabet.environment_wellFormed hEnvironment
  constructor
  · intro hStep
    rcases NewCorrespondence.relationMembership_progress_cases alphabet
      pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      rcases hStep with ⟨hTransition, hOffers⟩
      cases hTransition with
      | progress _ _ _ _ hClock =>
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
            ⟨TypeTransition.progress env alphabet pid hWellFormed hClock,
              TypeOffers.progress env alphabet pid ⟨hWellFormed, hClock⟩⟩
          have hEdge := NewCorrespondence.compileType_progress_action_edge
            (alphabet := alphabet) pid hLocal hClock
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
                (alphabet := alphabet) pid hLocal conditions.2
              exact ⟨.final, hEdge, hRelated⟩
  · rintro ⟨state', hEdge, hTargetRelated⟩
    rcases NewCorrespondence.relationMembership_progress_cases alphabet
      pid hRelated with
      hRoot | hFinal
    · rcases hRoot with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        (alphabet := alphabet) pid hEdge
      rcases hCases with hProgress | hIdle
      · rcases hProgress with ⟨_hSource, hTarget, hLabel, hCurrent,
          hFuture, hClock⟩
        subst label
        subst current
        subst future
        subst state'
        have hTargetAccepting :
            TypeAutomatonState.final ∈
              (compileType (.progress alphabet pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_progress_cases
              alphabet pid hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.progress env alphabet pid hWellFormed hClock,
          TypeOffers.progress env alphabet pid ⟨hWellFormed, hClock⟩⟩
      · rcases hIdle with ⟨hSource, _⟩
        simp at hSource
    · rcases hFinal with ⟨hResidual, hState⟩
      subst residual
      subst state
      have hCases := NewCorrespondence.compileType_progress_edge_cases
        (alphabet := alphabet) pid hEdge
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
              (compileType (.progress alphabet pid)).accepting := by
          simp [compileType, typeCompilationFuel, compileTypeFuel,
            finishAutomatonFragment]
        have hResidualTarget : residual' = .skip alphabet := by
          rcases NewCorrespondence.relationMembership_progress_cases
              alphabet pid hTargetRelated with hRoot | hFinal
          · simp at hRoot
          · exact hFinal.1
        subst residual'
        exact ⟨TypeTransition.skip env alphabet ⟨hWellFormed, hClock⟩,
          TypeOffers.skip env alphabet ⟨hWellFormed, hClock⟩⟩

set_option maxHeartbeats 4000000 in
/-- Step correspondence for an open recursion-variable marker `X`, which never has a real step. -/
theorem correspondence_var_stepIff
     (alphabet : PactTypeAlphabet) (name : String) :
    StepIffStatement (.var alphabet name) := by
  intro residual residual' state env label offers hRelated hSymbol
  obtain ⟨hResidual, hState⟩ :=
    relationMembership_var_cases alphabet name hRelated
  subst hResidual
  subst hState
  constructor
  · intro hStep
    cases hStep.1
  · rintro ⟨state', hEdge, -⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge (.var alphabet name)
      TypeAutomatonState.root state' env label offers] at hEdge
    obtain ⟨edge, hPending, -, -, hLabel, -, -, -⟩ := hEdge
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image] at hPending
    obtain ⟨environment, -, rfl⟩ := hPending
    simp at hLabel

end

end Pact
