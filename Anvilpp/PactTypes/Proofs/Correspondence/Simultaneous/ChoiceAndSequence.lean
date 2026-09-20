import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Base
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.SequenceCurrent

/-!
Choice, fair choice and sequence: their edge lift/restrict families, the
current-offer correspondence and the menu equation at each.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Current-offer correspondence at a binary choice.  Following the paper: the
root's guards, labels, current offers and targets are identical in the semantic
rule and the selection edge family, and copied states use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (_hWF : (PactType.choice alphabet left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.choice alphabet left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.choice alphabet left right).alphabet)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence (.choice alphabet left right) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: invert the choice rule and take its own selection edge.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_choice_eq alphabet left right
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | choice_left cEnv cAlpha cLeft cRight hChoiceEnv =>
          refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel left)
            left).initial, computeFutureOf (.choice alphabet left right)
              TypeAutomatonState.root, ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.choice alphabet left right) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at TypeAutomatonState.root ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inl rfl⟩
            · simp
          · exact relationMembership_choice_left alphabet left right left
              (buildRelationSet_initial left (compileType left))
      | choice_right cEnv cAlpha cLeft cRight hChoiceEnv =>
          refine ⟨.child 1 (compileTypeFuel (typeCompilationFuel right)
            right).initial, computeFutureOf (.choice alphabet left right)
              TypeAutomatonState.root, ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.choice alphabet left right) TypeAutomatonState.root
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at TypeAutomatonState.root ∅,
                target := childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inr rfl⟩
            · simp
          · exact relationMembership_choice_right alphabet left right right
              (buildRelationSet_initial right (compileType right))
    · -- Copied left state: the lower-rank hypothesis, lifted.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hLeft.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        choice_child0_edge_lift alphabet left right hLeftDisjoint hLeftAlphabet
          hChildEdge,
        relationMembership_choice_left alphabet left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      exact ⟨.child 1 q', future',
        choice_child1_edge_lift alphabet left right hRightDisjoint hRightAlphabet
          hChildEdge,
        relationMembership_choice_right alphabet left right residual' hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: the only root edges are the two selection edges.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_choice_eq alphabet left right
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
          TypeAutomatonState.root state' env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      obtain ⟨environment, hEnvFilter, hEq | hEq⟩ :=
        (buildChoiceAutomaton_outgoing_root alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent pendingEdge).mp
          ⟨hPendingMem, hPSource⟩ <;>
        rw [Finset.mem_filter] at hEnvFilter <;>
        subst hEq <;>
        simp only [childState] at hPEnv hPLabel hPCurrent hPTarget
      · have hLabelEq : label = TypeLabel.silent := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨left, typeFutureOffers (.choice alphabet left right), ?_, ?_⟩
        · exact ⟨TypeTransition.choice_left _ alphabet left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.choice_left _ alphabet left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_choice_left alphabet left right left
            (buildRelationSet_initial left (compileType left))
      · have hLabelEq : label = TypeLabel.silent := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨right, typeFutureOffers (.choice alphabet left right), ?_, ?_⟩
        · exact ⟨TypeTransition.choice_right _ alphabet left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.choice_right _ alphabet left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_choice_right alphabet left right right
            (buildRelationSet_initial right (compileType right))
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        choice_child0_edge_restrict alphabet left right hLeftDisjoint
          hLeftAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hLeft.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_choice_left alphabet left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        choice_child1_edge_restrict alphabet left right hRightDisjoint
          hRightAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hRight.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_choice_right alphabet left right residual' hChildTarget⟩

/- Superseded by SequenceCurrent: retained for comparison until cleanup.
Current-offer correspondence at a sequence.  Following the paper: apply the
lower-rank hypothesis to the left step, let completion decide whether its target
is retained or redirected to the right entry, and copy right states unchanged.
theorem currentOfferCorrespondence_seq (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    {seqBound : List String}
    (hSeqWF : TypeWellFormedIn seqBound (.seq alphabet left right))
    (hResign : ∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target))
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftResidualWF : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType left))
        residual state → residual.AlphabetWellFormed)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence (.seq alphabet left right) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨q, leftResidual, hEntry, hChildRelated, -⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Left phase: the residual is `leftResidual; right`.
      rw [Prod.ext_iff] at hEntry
      obtain ⟨hResEq, hStateEq⟩ := hEntry
      simp only at hResEq hStateEq
      subst hResEq; subst hStateEq
      rcases decoratedTypeTransition_seq_cases hTransition with
        ⟨leftTarget, childFuture, hTargetEq, hNonFinal, hChildStep, hNotTock,
          hFutureEq⟩ |
        ⟨leftTarget, childCurrent, childFuture, hTargetEq, hNonFinal, hTock,
          hChildStep, hFutureEq⟩ |
        ⟨tSkip, oSkip, childFuture, hTargetEq, hChildTrans, hChildOffers,
          hNotTock, hFutureEq⟩ |
        ⟨tSkip, oSkip, childCurrent, childFuture, hTargetEq, hTock,
          hChildTrans, hChildOffers, hFutureEq⟩
      · -- Retained: apply the lower-rank hypothesis to the left step.
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated hChildStep
        subst hTargetEq
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_step alphabet left right hRelated
            hChildRelated hChildTarget hNonFinal
            hChildStep hNotTock hChildEdge
        exact ⟨.child 0 q', _, hParentEdge, hParentTarget⟩
      · -- Retained under a clock: a clock step offers nothing now.
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated hChildStep
        subst hTargetEq; subst hTock
        have hCurrentEmpty : current = ∅ := by
          simpa using
            TypeOffers.current_eq_empty_of_label_tock hTransition.2 rfl
        subst hCurrentEmpty
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_step_tock alphabet left right hRelated
            hChildRelated hChildTarget hNonFinal hChildStep hChildEdge
        exact ⟨.child 0 q', _, hParentEdge, hParentTarget⟩
      · -- Redirected: the left operand completes, so the edge enters the right
        -- entry.
        -- Both judgments preserve the alphabet, so the two skip annotations
        -- the inversion produced are the same one.
        have hResWF := hLeftResidualWF hChildRelated
        have hSkipEq : oSkip = tSkip := by
          have hT := TypeTransition.preserves_alphabet hResWF hChildTrans
          have hO := TypeOffers.preserves_alphabet hResWF hChildOffers
          exact hO.trans hT.symm
        rw [hSkipEq] at hChildOffers
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated ⟨hChildTrans, hChildOffers⟩
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_fuse alphabet tSkip left right
            hRightDisjoint hRightAlphabet hRelated hChildRelated hChildTarget
            ⟨hChildTrans, hChildOffers⟩ hNotTock hChildEdge
        exact ⟨_, _, hParentEdge, hTargetEq ▸ hParentTarget⟩
      · -- Redirected under a clock: the parent offers nothing now either.
        subst hTock
        have hCurrentEmpty : current = ∅ := by
          simpa using
            TypeOffers.current_eq_empty_of_label_tock hTransition.2 rfl
        have hChildCurrentEmpty : childCurrent = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildOffers rfl
        subst hCurrentEmpty; subst hChildCurrentEmpty
        have hResWF := hLeftResidualWF hChildRelated
        have hSkipEq : oSkip = tSkip := by
          have hT := TypeTransition.preserves_alphabet hResWF hChildTrans
          have hO := TypeOffers.preserves_alphabet hResWF hChildOffers
          exact hO.trans hT.symm
        rw [hSkipEq] at hChildOffers
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated ⟨hChildTrans, hChildOffers⟩
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_fuse_tock alphabet tSkip left right
            hRelated hChildRelated hChildTarget
            ⟨hChildTrans, hChildOffers⟩ hChildEdge
        subst hTargetEq
        exact ⟨_, _, hParentEdge, hParentTarget⟩
    · -- Right phase: copied unchanged.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      -- The right component copies its edges unchanged.
      obtain ⟨state', hParentEdge, hParentTarget⟩ :=
        compileType_seq_lift_right_step alphabet left right hRightDisjoint
          hRightAlphabet hRelated hChildRelated hChildTarget
          (offers := TypeOfferSummary.mk current future')
          (rightTarget := residual') hChildEdge
      exact ⟨state', future', hParentEdge, hParentTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    -- The same case split, read off the edge instead of the step.
    obtain ⟨residual', hTargetRelated⟩ :=
      targetsRelated _ hSeqWF hResign hRelated hEdge
    cases compileType_seq_edge_cases alphabet left right hLeftDisjoint hResign
        hRightDisjoint
        hRightAlphabet hRelated hEdge hTargetRelated with
    | leftStep leftResidual leftTarget q q' childFuture hRes hRes' hState
        hState' hNonFinal hLeftRelated hLeftTargetRelated hChildEdge hNotTock
        hFuture =>
        subst hRes; subst hRes'; subst hState; subst hState'; subst hFuture
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        -- `final-states-completion`: the edge's target is not accepting, so the
        -- residual it represents is not `skip`.
        have hNotAccepting : q' ∉ (compileType left).accepting := by
          intro hAccept
          obtain ⟨skipAlpha, hSkip⟩ :=
            (final_states_completion left hLeftTargetRelated).mp hAccept
          exact hNonFinal (by rw [hSkip]; rfl)
        have hNonFinal'' : leftTarget'' ≠ .skip leftTarget''.alphabet := by
          intro hSkip
          exact hNotAccepting
            ((final_states_completion left hChildTarget'').mpr
              ⟨leftTarget''.alphabet, hSkip⟩)
        exact ⟨_, _,
          ⟨TypeTransition.seq env alphabet leftResidual leftTarget'' right label
              hChildStep.1 hNonFinal'',
            TypeOffers.seq env alphabet leftResidual leftTarget'' right label
              current childFuture'' hChildStep.2 hNonFinal'' hNotTock⟩,
          relationMembership_seq_left alphabet left right leftTarget''
            hChildTarget'' hNotAccepting⟩
    | leftStepTock leftResidual leftTarget q q' childFuture hRes hRes' hState
        hState' hNonFinal hLeftRelated hLeftTargetRelated hChildEdge hTock
        hFuture =>
        subst hRes; subst hRes'; subst hState; subst hState'; subst hFuture
        subst hTock
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        have hNotAccepting : q' ∉ (compileType left).accepting := by
          intro hAccept
          obtain ⟨skipAlpha, hSkip⟩ :=
            (final_states_completion left hLeftTargetRelated).mp hAccept
          exact hNonFinal (by rw [hSkip]; rfl)
        have hNonFinal'' : leftTarget'' ≠ .skip leftTarget''.alphabet := by
          intro hSkip
          exact hNotAccepting
            ((final_states_completion left hChildTarget'').mpr
              ⟨leftTarget''.alphabet, hSkip⟩)
        have hCurrentEmpty : current = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildStep.2 rfl
        exact ⟨_, _,
          ⟨TypeTransition.seq env alphabet leftResidual leftTarget'' right
              TypeLabel.tock hChildStep.1 hNonFinal'',
            hCurrentEmpty ▸ TypeOffers.seq_tock env alphabet leftResidual
              leftTarget'' right current childFuture'' hChildStep.2
              hNonFinal''⟩,
          relationMembership_seq_left alphabet left right leftTarget''
            hChildTarget'' hNotAccepting⟩
    | leftFuse leftResidual skipAlphabet q q' childFuture hRes hRes' hState
        hLeftRelated hLeftTargetRelated hChildEdge hNotTock hFuture =>
        subst hRes; subst hState; subst hFuture
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        -- The edge's target is accepting, so its residual completes the left
        -- operand and the step fuses into the right entry.
        have hAccept : q' ∈ (compileType left).accepting :=
          (final_states_completion left hLeftTargetRelated).mpr
            ⟨skipAlphabet, rfl⟩
        obtain ⟨skipAlpha'', hSkip''⟩ :=
          (final_states_completion left hChildTarget'').mp hAccept
        subst hSkip''
        exact ⟨_, _,
          ⟨TypeTransition.seq_fuse env alphabet skipAlpha'' leftResidual right
              label hChildStep.1,
            TypeOffers.seq_fuse env alphabet skipAlpha'' leftResidual right
              label current childFuture'' hChildStep.2 hNotTock⟩,
          hRes' ▸ hTargetRelated⟩
    | leftFuseTock leftResidual skipAlphabet q q' childFuture hRes hRes' hState
        hLeftRelated hLeftTargetRelated hChildEdge hTock hFuture =>
        subst hRes; subst hState; subst hFuture; subst hTock
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        have hAccept : q' ∈ (compileType left).accepting :=
          (final_states_completion left hLeftTargetRelated).mpr
            ⟨skipAlphabet, rfl⟩
        obtain ⟨skipAlpha'', hSkip''⟩ :=
          (final_states_completion left hChildTarget'').mp hAccept
        subst hSkip''
        have hCurrentEmpty : current = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildStep.2 rfl
        exact ⟨_, _,
          ⟨TypeTransition.seq_fuse env alphabet skipAlpha'' leftResidual right
              TypeLabel.tock hChildStep.1,
            hCurrentEmpty ▸ TypeOffers.seq_fuse_tock env alphabet skipAlpha''
              leftResidual right current childFuture'' hChildStep.2⟩,
          hRes' ▸ hTargetRelated⟩
    | rightStep q q' hState hState' hRightRelated hRightTargetRelated
        hChildEdge =>
        subst hState; subst hState'
        obtain ⟨residual'', future'', hChildStep, hChildTarget''⟩ :=
          hRight.2 hRightRelated hChildEdge
        exact ⟨residual'', future'', hChildStep,
          relationMembership_seq_right alphabet left right residual''
            hChildTarget''⟩

-/

/-- Menus agree at a binary choice: the root reaches exactly its two copied
child entries, and their menus agree by the child hypotheses. -/
theorem futureOffersAgree_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right) :
    FutureOffersAgree (.choice alphabet left right) := by
  classical
  set whole : PactType := .choice alphabet left right with hWholeDef
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hProductLeft : ∀ visited,
      stateProductInfo whole (.child 0 visited) = stateProductInfo left visited :=
    stateProductInfo_choice_child_left alphabet left right
  have hProductRight : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_choice_child_right alphabet left right
  -- A copied child state has its child's own menu.
  have hTransportLeft : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left)
      left).states, computeFutureOf whole (.child 0 q) = computeFutureOf left q :=
    fun q hq => computeFutureOf_binaryChoice_left alphabet left right
      TypeLabel.silent TypeLabel.silent whole hWhole hFuelLeft hLeftDisjoint
      (by rw [hLeftAlphabet, hWholeDef]; rfl) hProductLeft q hq
  have hTransportRight : ∀ q ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states,
      computeFutureOf whole (.child 1 q) = computeFutureOf right q :=
    fun q hq => computeFutureOf_binaryChoice_right alphabet left right
      TypeLabel.silent TypeLabel.silent whole hWhole hFuelRight hRightDisjoint
      (by rw [hRightAlphabet, hWholeDef]; rfl) hProductRight q hq
  intro residual state hRelated
  rcases relationMembership_choice_cases alphabet left right hRelated with
    hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
  · -- Root: split the menu across the two selection edges.
    injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    have hWholeDisjoint : whole.OfferBranchesDisjoint := by
      simp only [hWholeDef, PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩
    have hEnv : ∃ environment ∈ alphabet.localEnvironments,
        environment.clock = false :=
      ⟨TypeEnvironment.empty, empty_mem_localEnvironments alphabet, rfl⟩
    have hOffers :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).offersAt
          TypeAutomatonState.root = ∅ := by
      rw [hWhole]
      exact buildChoiceAutomaton_offersAt_root alphabet _ _ _ _
    have hRefs :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).menuStep
          TypeAutomatonState.root =
        {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
          childState 1
            (compileTypeFuel (typeCompilationFuel right) right).initial} := by
      rw [hWhole]
      exact buildChoiceAutomaton_menuStep_root alphabet _ _ _ _
        (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent]) hEnv
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
        childState 1
          (compileTypeFuel (typeCompilationFuel right) right).initial}
      _ rfl
      (compileTypeFuel_menuClosed (typeCompilationFuel whole) whole
        (Nat.le_refl _) hWholeDisjoint)
      (by
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildChoiceAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hRefs]
        simp)
      (by rw [hRefs]; exact Finset.subset_union_left)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_choice_root alphabet left right)
      (by
        intro action hIn
        rw [hOffers] at hIn
        exact absurd hIn (Finset.notMem_empty _))
    rw [hDecomp, hOffers, Finset.empty_union, Finset.biUnion_insert,
      Finset.singleton_biUnion]
    simp only [childState]
    have hLeftMenu : computeFutureOf left
        (compileTypeFuel (typeCompilationFuel left) left).initial =
          typeFutureOffers left :=
      hLeft (buildRelationSet_initial left _ rfl)
    have hRightMenu : computeFutureOf right
        (compileTypeFuel (typeCompilationFuel right) right).initial =
          typeFutureOffers right :=
      hRight (buildRelationSet_initial right _ rfl)
    rw [hTransportLeft _ (compileTypeFuel_initial_mem _ left (Nat.le_refl _)),
      hTransportRight _ (compileTypeFuel_initial_mem _ right (Nat.le_refl _)),
      hLeftMenu, hRightMenu]
    exact (typeFutureOffers_choice alphabet left right).symm
  · subst hState
    rw [hTransportLeft q
      (relationMembership_state_mem left _ q hLeftDisjoint hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q
      (relationMembership_state_mem right _ q hRightDisjoint hChild)]
    exact hRight hChild

/-- Compiling a fair choice at its own budget builds the same sum automaton,
with observable selection labels. -/
theorem compileTypeFuel_fairChoice_eq (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) :
    compileTypeFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
      buildChoiceAutomaton alphabet
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  rw [compileTypeFuel_eq_of_sufficient left (Nat.le_max_left _ _)
      (Nat.le_refl _),
    compileTypeFuel_eq_of_sufficient right (Nat.le_max_right _ _)
      (Nat.le_refl _)]

lemma edgeLocal_fairChoice (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeEnvironmentsLocal left ∧ EdgeOffersLocal left)
    (hRight : EdgeEnvironmentsLocal right ∧ EdgeOffersLocal right) :
    EdgeEnvironmentsLocal (.fairChoice alphabet bid left right) ∧
      EdgeOffersLocal (.fairChoice alphabet bid left right) := by
  refine ⟨fun edge hEdge => ?_, fun edge hEdge => ?_⟩ <;>
    rw [compileTypeFuel_fairChoice_eq alphabet bid left right] at hEdge
  · exact sumBuilder_edge_families alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.1 hRight.1 edge hEdge
  · exact sumBuilder_edge_offers alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.2 hRight.2 edge hEdge

/-- A copied left-child edge of a fair choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem fairChoice_child0_edge_restrict (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType left).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_left alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge left q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    have hResolve := resolve_childFutureSpec 0 childEdge.future
      (computeFutureOf (.fairChoice alphabet bid left right)) (computeFutureOf left) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_left alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          (.fairChoice alphabet bid left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem)
    exact hResolve.symm

/-- The forward direction of `fairChoice_child0_edge_restrict`: a left-child edge
lifts to the copied edge of the fair choice. -/
theorem fairChoice_child0_edge_lift (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType left).HasEdge q env label ⟨current, future⟩ q') :
    (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · have hResolve := resolve_childFutureSpec 0 childEdge.future
      (computeFutureOf (.fairChoice alphabet bid left right)) (computeFutureOf left) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_left alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          (.fairChoice alphabet bid left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem)
    exact hResolve.trans hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- The forward direction of `fairChoice_child1_edge_restrict`: a left-child edge
lifts to the copied edge of the fair choice. -/
theorem fairChoice_child1_edge_lift (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType right).HasEdge q env label ⟨current, future⟩ q') :
    (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 1 q) env label ⟨current, future⟩ (.child 1 q') := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
    (.child 1 q) (.child 1 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 1 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inr ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · have hResolve := resolve_childFutureSpec 1 childEdge.future
      (computeFutureOf (.fairChoice alphabet bid left right)) (computeFutureOf right) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_right alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          (.fairChoice alphabet bid left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem)
    exact hResolve.trans hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- A copied right-child edge of a fair choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem fairChoice_child1_edge_restrict (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 1 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 1 q' ∧
      (compileType right).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
      (.child 1 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_right alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge right q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    have hResolve := resolve_childFutureSpec 1 childEdge.future
      (computeFutureOf (.fairChoice alphabet bid left right)) (computeFutureOf right) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_right alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          (.fairChoice alphabet bid left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem)
    exact hResolve.symm

/-- Current-offer correspondence at a fair choice.  Following the paper: the
root's guards, labels, current offers and targets are identical in the semantic
rule and the selection edge family, and copied states use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_fairChoice (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (_hWF : (PactType.fairChoice alphabet bid left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence ((.fairChoice alphabet bid left right)) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: invert the choice rule and take its own selection edge.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | fair_left cEnv cAlpha cBid cLeft cRight hChoiceEnv =>
          refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel left)
            left).initial, computeFutureOf ((.fairChoice alphabet bid left right))
              TypeAutomatonState.root, ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              ((.fairChoice alphabet bid left right)) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial) env (TypeLabel.fair bid true) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible (TypeLabel.fair bid true),
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at TypeAutomatonState.root ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inl rfl⟩
            · simp
          · exact relationMembership_fairChoice_left alphabet bid left right left
              (buildRelationSet_initial left (compileType left))
      | fair_right cEnv cAlpha cBid cLeft cRight hChoiceEnv =>
          refine ⟨.child 1 (compileTypeFuel (typeCompilationFuel right)
            right).initial, computeFutureOf ((.fairChoice alphabet bid left right))
              TypeAutomatonState.root, ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              ((.fairChoice alphabet bid left right)) TypeAutomatonState.root
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial) env (TypeLabel.fair bid false) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible (TypeLabel.fair bid false),
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at TypeAutomatonState.root ∅,
                target := childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inr rfl⟩
            · simp
          · exact relationMembership_fairChoice_right alphabet bid left right right
              (buildRelationSet_initial right (compileType right))
    · -- Copied left state: the lower-rank hypothesis, lifted.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hLeft.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        fairChoice_child0_edge_lift alphabet bid left right hLeftDisjoint hLeftAlphabet
          hChildEdge,
        relationMembership_fairChoice_left alphabet bid left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      exact ⟨.child 1 q', future',
        fairChoice_child1_edge_lift alphabet bid left right hRightDisjoint hRightAlphabet
          hChildEdge,
        relationMembership_fairChoice_right alphabet bid left right residual' hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: the only root edges are the two selection edges.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
          TypeAutomatonState.root state' env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      obtain ⟨environment, hEnvFilter, hEq | hEq⟩ :=
        (buildChoiceAutomaton_outgoing_root alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) pendingEdge).mp
          ⟨hPendingMem, hPSource⟩ <;>
        rw [Finset.mem_filter] at hEnvFilter <;>
        subst hEq <;>
        simp only [childState] at hPEnv hPLabel hPCurrent hPTarget
      · have hLabelEq : label = TypeLabel.fair bid true := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨left, typeFutureOffers (.fairChoice alphabet bid left right), ?_, ?_⟩
        · exact ⟨TypeTransition.fair_left _ alphabet bid left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.fair_left _ alphabet bid left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_fairChoice_left alphabet bid left right left
            (buildRelationSet_initial left (compileType left))
      · have hLabelEq : label = TypeLabel.fair bid false := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨right, typeFutureOffers (.fairChoice alphabet bid left right), ?_, ?_⟩
        · exact ⟨TypeTransition.fair_right _ alphabet bid left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.fair_right _ alphabet bid left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_fairChoice_right alphabet bid left right right
            (buildRelationSet_initial right (compileType right))
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        fairChoice_child0_edge_restrict alphabet bid left right hLeftDisjoint
          hLeftAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hLeft.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_fairChoice_left alphabet bid left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        fairChoice_child1_edge_restrict alphabet bid left right hRightDisjoint
          hRightAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hRight.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_fairChoice_right alphabet bid left right residual' hChildTarget⟩

/-- Menus agree at a fair choice.  The construction is the same sum as an
ordinary choice, with observable selection labels. -/
theorem futureOffersAgree_fairChoice (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right) :
    FutureOffersAgree (.fairChoice alphabet bid left right) := by
  classical
  set whole : PactType := .fairChoice alphabet bid left right with hWholeDef
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hProductLeft : ∀ visited,
      stateProductInfo whole (.child 0 visited) = stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  have hProductRight : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  -- A copied child state has its child's own menu.
  have hTransportLeft : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left)
      left).states, computeFutureOf whole (.child 0 q) = computeFutureOf left q :=
    fun q hq => computeFutureOf_binaryChoice_left alphabet left right
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) whole hWhole hFuelLeft hLeftDisjoint
      (by rw [hLeftAlphabet, hWholeDef]; rfl) hProductLeft q hq
  have hTransportRight : ∀ q ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states,
      computeFutureOf whole (.child 1 q) = computeFutureOf right q :=
    fun q hq => computeFutureOf_binaryChoice_right alphabet left right
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) whole hWhole hFuelRight hRightDisjoint
      (by rw [hRightAlphabet, hWholeDef]; rfl) hProductRight q hq
  intro residual state hRelated
  rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
    hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
  · -- Root: split the menu across the two selection edges.
    injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    have hWholeDisjoint : whole.OfferBranchesDisjoint := by
      simp only [hWholeDef, PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩
    have hEnv : ∃ environment ∈ alphabet.localEnvironments,
        environment.clock = false :=
      ⟨TypeEnvironment.empty, empty_mem_localEnvironments alphabet, rfl⟩
    have hOffers :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).offersAt
          TypeAutomatonState.root = ∅ := by
      rw [hWhole]
      exact buildChoiceAutomaton_offersAt_root alphabet _ _ _ _
    have hRefs :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).menuStep
          TypeAutomatonState.root =
        {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
          childState 1
            (compileTypeFuel (typeCompilationFuel right) right).initial} := by
      rw [hWhole]
      exact buildChoiceAutomaton_menuStep_root alphabet _ _ _ _
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair]) hEnv
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
        childState 1
          (compileTypeFuel (typeCompilationFuel right) right).initial}
      _ rfl
      (compileTypeFuel_menuClosed (typeCompilationFuel whole) whole
        (Nat.le_refl _) hWholeDisjoint)
      (by
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildChoiceAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hRefs]
        simp)
      (by rw [hRefs]; exact Finset.subset_union_left)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_fairChoice_root alphabet bid left right)
      (by
        intro action hIn
        rw [hOffers] at hIn
        exact absurd hIn (Finset.notMem_empty _))
    rw [hDecomp, hOffers, Finset.empty_union, Finset.biUnion_insert,
      Finset.singleton_biUnion]
    simp only [childState]
    have hLeftMenu : computeFutureOf left
        (compileTypeFuel (typeCompilationFuel left) left).initial =
          typeFutureOffers left :=
      hLeft (buildRelationSet_initial left _ rfl)
    have hRightMenu : computeFutureOf right
        (compileTypeFuel (typeCompilationFuel right) right).initial =
          typeFutureOffers right :=
      hRight (buildRelationSet_initial right _ rfl)
    rw [hTransportLeft _ (compileTypeFuel_initial_mem _ left (Nat.le_refl _)),
      hTransportRight _ (compileTypeFuel_initial_mem _ right (Nat.le_refl _)),
      hLeftMenu, hRightMenu]
    exact (typeFutureOffers_fairChoice alphabet bid left right).symm
  · subst hState
    rw [hTransportLeft q
      (relationMembership_state_mem left _ q hLeftDisjoint hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q
      (relationMembership_state_mem right _ q hRightDisjoint hChild)]
    exact hRight hChild

/-- Both selection edges read the choice source, independently of their targets. -/
theorem binaryChoice_root_future (whole : PactType) (alphabet : PactTypeAlphabet)
    (left right : AutomatonFragment) (selectionLeft selectionRight : TypeLabel)
    (hCompile : compileTypeFuel (typeCompilationFuel whole) whole =
      buildChoiceAutomaton alphabet left right selectionLeft selectionRight)
    {env : TypeEnvironment} {label : TypeLabel} {current future : Finset BareMessage}
    {target : TypeAutomatonState}
    (hEdge : (compileType whole).HasEdge .root env label ⟨current, future⟩ target) :
    future = computeFutureOf whole .root := by
  obtain ⟨edge, hMem, hSource, _, _, _, hFuture, _⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge _ _ _ _ _ _).mp hEdge
  rw [hCompile] at hMem
  obtain ⟨environment, _, rfl | rfl⟩ :=
    (buildChoiceAutomaton_outgoing_root alphabet left right selectionLeft selectionRight
      edge).mp ⟨hMem, hSource⟩ <;>
    simpa using hFuture.symm

/-- After menu agreement, selection roots and full child hypotheses identify both fields. -/
theorem offerCorrespondence_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hWF : (PactType.choice alphabet left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.choice alphabet left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.choice alphabet left right).alphabet)
    (hMenus : FutureOffersAgree (PactType.choice alphabet left right))
    (hLeft : TypeAutomatonStepCorrespondence left)
    (hRight : TypeAutomatonStepCorrespondence right) :
    TypeAutomatonStepCorrespondence (PactType.choice alphabet left right) := by
  have hCurrent := currentOfferCorrespondence_choice alphabet left right hWF
    hLeftDisjoint hRightDisjoint hLeftAlphabet hRightAlphabet hLeft.toCurrent hRight.toCurrent
  have hRootFuture : ∀ {env label current future target},
      (compileType (.choice alphabet left right)).HasEdge .root env label
        ⟨current, future⟩ target →
      future = computeFutureOf (.choice alphabet left right) .root :=
    binaryChoice_root_future (PactType.choice alphabet left right) alphabet
    (compileTypeFuel (typeCompilationFuel left) left)
    (compileTypeFuel (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
    (compileTypeFuel_choice_eq alphabet left right)
  constructor
  · intro rho rho' q env label offers hRelated hStep
    rcases offers with ⟨current, future⟩
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨child, rfl, hChild⟩ | ⟨child, rfl, hChild⟩
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hRoot
      obtain ⟨q', edgeFuture, hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
      have hSemantic : future = typeFutureOffers (PactType.choice alphabet left right) := by
        cases hStep.2 <;> rfl
      have hEqual : edgeFuture = future :=
        (hRootFuture hEdge).trans ((hMenus hRelated).trans hSemantic.symm)
      exact ⟨q', hEqual ▸ hEdge, hTarget⟩
    · obtain ⟨child', hEdge, hTarget⟩ := hLeft.1 hChild hStep
      exact ⟨.child 0 child',
        choice_child0_edge_lift alphabet left right hLeftDisjoint hLeftAlphabet hEdge,
        relationMembership_choice_left alphabet left right rho' hTarget⟩
    · obtain ⟨child', hEdge, hTarget⟩ := hRight.1 hChild hStep
      exact ⟨.child 1 child',
        choice_child1_edge_lift alphabet left right hRightDisjoint hRightAlphabet hEdge,
        relationMembership_choice_right alphabet left right rho' hTarget⟩
  · intro rho q q' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨child, rfl, hChild⟩ | ⟨child, rfl, hChild⟩
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hRoot
      obtain ⟨rho', semanticFuture, hStep, hTarget⟩ := hCurrent.2 hRelated hEdge
      have hSemantic : semanticFuture = typeFutureOffers (PactType.choice alphabet left right) := by
        cases hStep.2 <;> rfl
      have hEqual : semanticFuture = future :=
        hSemantic.trans ((hMenus hRelated).symm.trans (hRootFuture hEdge).symm)
      exact ⟨rho', hEqual ▸ hStep, hTarget⟩
    · obtain ⟨child', rfl, hChildEdge⟩ :=
        choice_child0_edge_restrict alphabet left right hLeftDisjoint hLeftAlphabet hEdge
      obtain ⟨rho', hStep, hTarget⟩ := hLeft.2 hChild hChildEdge
      exact ⟨rho', hStep, relationMembership_choice_left alphabet left right rho' hTarget⟩
    · obtain ⟨child', rfl, hChildEdge⟩ :=
        choice_child1_edge_restrict alphabet left right hRightDisjoint hRightAlphabet hEdge
      obtain ⟨rho', hStep, hTarget⟩ := hRight.2 hChild hChildEdge
      exact ⟨rho', hStep, relationMembership_choice_right alphabet left right rho' hTarget⟩

/-- After menu agreement, selection roots and full child hypotheses identify both fields. -/
theorem offerCorrespondence_fairChoice (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hWF : (PactType.fairChoice alphabet bid left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hMenus : FutureOffersAgree (PactType.fairChoice alphabet bid left right))
    (hLeft : TypeAutomatonStepCorrespondence left)
    (hRight : TypeAutomatonStepCorrespondence right) :
    TypeAutomatonStepCorrespondence (PactType.fairChoice alphabet bid left right) := by
  have hCurrent := currentOfferCorrespondence_fairChoice alphabet bid left right hWF
    hLeftDisjoint hRightDisjoint hLeftAlphabet hRightAlphabet hLeft.toCurrent hRight.toCurrent
  have hRootFuture : ∀ {env label current future target},
      (compileType (.fairChoice alphabet bid left right)).HasEdge .root env label
        ⟨current, future⟩ target →
      future = computeFutureOf (.fairChoice alphabet bid left right) .root :=
    binaryChoice_root_future (PactType.fairChoice alphabet bid left right) alphabet
    (compileTypeFuel (typeCompilationFuel left) left)
    (compileTypeFuel (typeCompilationFuel right) right) (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    (compileTypeFuel_fairChoice_eq alphabet bid left right)
  constructor
  · intro rho rho' q env label offers hRelated hStep
    rcases offers with ⟨current, future⟩
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨child, rfl, hChild⟩ | ⟨child, rfl, hChild⟩
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hRoot
      obtain ⟨q', edgeFuture, hEdge, hTarget⟩ := hCurrent.1 hRelated hStep
      have hSemantic : future = typeFutureOffers (PactType.fairChoice alphabet bid left right) := by
        cases hStep.2 <;> rfl
      have hEqual : edgeFuture = future :=
        (hRootFuture hEdge).trans ((hMenus hRelated).trans hSemantic.symm)
      exact ⟨q', hEqual ▸ hEdge, hTarget⟩
    · obtain ⟨child', hEdge, hTarget⟩ := hLeft.1 hChild hStep
      exact ⟨.child 0 child',
        fairChoice_child0_edge_lift alphabet bid left right hLeftDisjoint hLeftAlphabet hEdge,
        relationMembership_fairChoice_left alphabet bid left right rho' hTarget⟩
    · obtain ⟨child', hEdge, hTarget⟩ := hRight.1 hChild hStep
      exact ⟨.child 1 child',
        fairChoice_child1_edge_lift alphabet bid left right hRightDisjoint hRightAlphabet hEdge,
        relationMembership_fairChoice_right alphabet bid left right rho' hTarget⟩
  · intro rho q q' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨child, rfl, hChild⟩ | ⟨child, rfl, hChild⟩
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hRoot
      obtain ⟨rho', semanticFuture, hStep, hTarget⟩ := hCurrent.2 hRelated hEdge
      have hSemantic : semanticFuture = typeFutureOffers (PactType.fairChoice alphabet bid left right) := by
        cases hStep.2 <;> rfl
      have hEqual : semanticFuture = future :=
        hSemantic.trans ((hMenus hRelated).symm.trans (hRootFuture hEdge).symm)
      exact ⟨rho', hEqual ▸ hStep, hTarget⟩
    · obtain ⟨child', rfl, hChildEdge⟩ :=
        fairChoice_child0_edge_restrict alphabet bid left right hLeftDisjoint hLeftAlphabet hEdge
      obtain ⟨rho', hStep, hTarget⟩ := hLeft.2 hChild hChildEdge
      exact ⟨rho', hStep, relationMembership_fairChoice_left alphabet bid left right rho' hTarget⟩
    · obtain ⟨child', rfl, hChildEdge⟩ :=
        fairChoice_child1_edge_restrict alphabet bid left right hRightDisjoint hRightAlphabet hEdge
      obtain ⟨rho', hStep, hTarget⟩ := hRight.2 hChild hChildEdge
      exact ⟨rho', hStep, relationMembership_fairChoice_right alphabet bid left right rho' hTarget⟩


end

end Pact
