import Anvilpp.PactTypes.NewCorrespondence.Cases.Base

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section
set_option maxHeartbeats 40000000 in
/-- Step correspondence for interleaved parallel composition `τ1 ‖_I τ2`. -/
theorem correspondence_par_stepIff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hInterface : interface ⊆ signature.interface)
    (hParentAlphabet : alphabet =
      PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    (hParallelCompatible : PactTypeAlphabet.ParallelCompatible alphabet
      left.alphabet right.alphabet interface)
    (hLeftResidual : left.ResidualInvariant)
    (hRightResidual : right.ResidualInvariant)
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
        signature.transitionAlphabetFor alphabet := by
    simpa [compileType] using hSymbol
  rcases relationMembership_par_cases signature alphabet left right interface
    hRelated with
    ⟨q1, q2, residualLeft, residualRight, hEntryEq, hLeftRelated,
      hRightRelated, hSourceReachable⟩ | hSurvivorLeft | hSurvivorRight |
      hEntryEq
  · -- general product case: `residual` represents `residualLeft ‖_I residualRight`
    injection hEntryEq with hResidualEq hStateEq
    subst hResidualEq; subst hStateEq
    have hParCoherent := hAlphabetCoherent
    simp only [PactType.AlphabetCoherent] at hParCoherent
    have hResidualLeftAlphabet := relationMembership_alphabet_eq signature left
      residualLeft q1 hParCoherent.1 hLeftRelated
    have hResidualRightAlphabet := relationMembership_alphabet_eq signature right
      residualRight q2 hParCoherent.2 hRightRelated
    have hSourceAlphabet : alphabet = PactTypeAlphabet.mergeHidden
        residualLeft.alphabet residualRight.alphabet interface := by
      rw [hResidualLeftAlphabet, hResidualRightAlphabet]
      exact hParentAlphabet
    -- A residual keeps the fixed alphabet of the component it came from, so
    -- it still satisfies the residual invariant and its offers stay inside it.
    have hResidualLeftInvariant : residualLeft.ResidualInvariant :=
      relationMembership_residualInvariant signature left residualLeft q1
        hLeftResidual hLeftRelated
    have hResidualRightInvariant : residualRight.ResidualInvariant :=
      relationMembership_residualInvariant signature right residualRight q2
        hRightResidual hRightRelated
    have hResidualLeftWellFormed : residualLeft.AlphabetWellFormed :=
      hResidualLeftInvariant.1
    have hResidualRightWellFormed : residualRight.AlphabetWellFormed :=
      hResidualRightInvariant.1
    -- The future offers of a step lie in the alphabet of its target, and a
    -- step keeps both the target's alphabet and its well-formedness.
    have hFutureBound : ∀ {env : TypeEnvironment} {source target : PactType}
        {label : TypeLabel} {current future : Finset BareMessage},
        source.ResidualInvariant →
        DecoratedTypeTransition env source label
          (TypeOfferSummary.mk current future) target →
        future ⊆ source.alphabet.actions := by
      intro env source target label current future hSource hStep
      exact typeOffers_future_subset_fixedAlphabet hSource.1
        (TypeTransition.preserves_alphabet hSource.1 hStep.1)
        (TypeTransition.preserves_alphabetWellFormed hStep.1 hSource.1
          hSource.2.1 hSource.2.2.2)
        hStep.2
    constructor
    · intro hStep
      cases decoratedTypeTransition_par_cases hStep with
      | step leftEnv rightEnv leftLabel rightLabel leftTarget rightTarget
          leftCurrent leftFuture rightCurrent rightFuture hTargetEq hNonFinal
          hLeftSrcNotSkip hRightSrcNotSkip
          hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq hCurrentEq hFutureEq =>
          have hLeftCurrentAlphabet : leftCurrent ⊆ residualLeft.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualLeftWellFormed
              hLeftStep.2
          have hRightCurrentAlphabet : rightCurrent ⊆ residualRight.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualRightWellFormed
              hRightStep.2
          have hLeftFutureAlphabet : leftFuture ⊆ residualLeft.alphabet.actions :=
            hFutureBound hResidualLeftInvariant hLeftStep
          have hRightFutureAlphabet :
              rightFuture ⊆ residualRight.alphabet.actions :=
            hFutureBound hResidualRightInvariant hRightStep
          have hResidualParallelCompatible :
              PactTypeAlphabet.ParallelCompatible alphabet residualLeft.alphabet
                residualRight.alphabet interface :=
            hResidualLeftAlphabet ▸ hResidualRightAlphabet ▸ hParallelCompatible
          obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
            transitionAlphabet_of_par_component
              (leftCurrent := leftCurrent) (leftFuture := leftFuture)
              (rightCurrent := rightCurrent) (rightFuture := rightFuture)
              signature alphabet residualLeft residualRight interface hWF hInterface
              hResidualLeftWellFormed hResidualRightWellFormed
              hResidualParallelCompatible
              hLeftCurrentAlphabet hLeftFutureAlphabet
              hRightCurrentAlphabet hRightFutureAlphabet
              hLocal1 hLocal2 hSync hLabelEq
              (hCurrentEq ▸ hFutureEq ▸ hSignatureSymbol)
          have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel
              (TypeOfferSummary.mk leftCurrent leftFuture) ∈
              (compileType signature left).alphabet := by
            simpa [compileType, hResidualLeftAlphabet] using hLeftSymbolMem0
          have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel
              (TypeOfferSummary.mk rightCurrent rightFuture) ∈
              (compileType signature right).alphabet := by
            simpa [compileType, hResidualRightAlphabet] using hRightSymbolMem0
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
            rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet left right
              interface q1 q2 (.pair q1' q2') env label
              (TypeOfferSummary.mk current future)
              (hParallelCompatible := hParallelCompatible) (hSymbol := hSignatureSymbol)
              (hChildLeftRelated := hLeftRelated) (hChildRightRelated := hRightRelated)]
            refine Or.inl ⟨leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge,
              hLeftSymbolMem, hRightSymbolMem,
              hSourceReachable,
              -- The ordinary rule's source guard transports through H13.
              (fun _ =>
                ⟨fun hAcc => hLeftSrcNotSkip
                    ((helper_h13_final_states_represent_completion signature
                      hLeftRelated).mp hAcc),
                  fun hAcc => hRightSrcNotSkip
                    ((helper_h13_final_states_represent_completion signature
                      hRightRelated).mp hAcc)⟩),
              hWF,
              hLocal1.congrLocalType hResidualLeftAlphabet.symm,
              hLocal2.congrLocalType hResidualRightAlphabet.symm,
              hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
            simp [hNotBothAccept]
          have hTargetReachable :=
            compiledParallel_pair_edge_target_reachable signature alphabet left
              right interface hEdgeFact
          refine ⟨.pair q1' q2', hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_pair signature alphabet left right interface
            hLeftTargetRelated hRightTargetRelated hTargetReachable
      | fuse_tock leftEnv rightEnv leftLabel rightLabel leftCurrent leftFuture
          rightCurrent rightFuture hTargetEq hLeftStep hRightStep hWF hLocal1
          hLocal2 hSync hTock hLabelEq hCurrentEq hFutureEq =>
          have hLeftCurrentAlphabet : leftCurrent ⊆ residualLeft.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualLeftWellFormed
              hLeftStep.2
          have hRightCurrentAlphabet : rightCurrent ⊆ residualRight.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualRightWellFormed
              hRightStep.2
          have hLeftFutureAlphabet : leftFuture ⊆ residualLeft.alphabet.actions :=
            hFutureBound hResidualLeftInvariant hLeftStep
          have hRightFutureAlphabet :
              rightFuture ⊆ residualRight.alphabet.actions :=
            hFutureBound hResidualRightInvariant hRightStep
          have hResidualParallelCompatible :
              PactTypeAlphabet.ParallelCompatible alphabet residualLeft.alphabet
                residualRight.alphabet interface :=
            hResidualLeftAlphabet ▸ hResidualRightAlphabet ▸ hParallelCompatible
          have hLeftFutureEmpty : leftFuture = ∅ :=
            TypeOffers.future_eq_empty_of_target_skip hLeftStep.2 rfl
          have hRightFutureEmpty : rightFuture = ∅ :=
            TypeOffers.future_eq_empty_of_target_skip hRightStep.2 rfl
          have hHiddenFutureEmpty :
              hideTypeOffers interface (leftFuture ∪ rightFuture) = ∅ := by
            rw [hLeftFutureEmpty, hRightFutureEmpty]
            simp [hideTypeOffers]
          have hFutureHidden :
              future = hideTypeOffers interface (leftFuture ∪ rightFuture) := by
            rw [hFutureEq, hHiddenFutureEmpty]
          have hParentSymbol :
              TypeAutomatonSymbol.mk env
                (TypeLabel.combine interface leftLabel rightLabel)
                (TypeOfferSummary.mk
                  (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
                  (hideTypeOffers interface (leftFuture ∪ rightFuture))) ∈
                signature.transitionAlphabetFor alphabet := by
            simpa [hLabelEq, hCurrentEq, hFutureEq, hHiddenFutureEmpty]
              using hSignatureSymbol
          obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
            transitionAlphabet_of_par_component
              (leftCurrent := leftCurrent) (leftFuture := leftFuture)
              (rightCurrent := rightCurrent) (rightFuture := rightFuture)
              signature alphabet residualLeft residualRight interface hWF hInterface
              hResidualLeftWellFormed hResidualRightWellFormed
              hResidualParallelCompatible
              hLeftCurrentAlphabet hLeftFutureAlphabet
              hRightCurrentAlphabet hRightFutureAlphabet
              hLocal1 hLocal2 hSync rfl hParentSymbol
          have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel
              (TypeOfferSummary.mk leftCurrent leftFuture) ∈
              (compileType signature left).alphabet := by
            simpa [compileType, hResidualLeftAlphabet] using hLeftSymbolMem0
          have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel
              (TypeOfferSummary.mk rightCurrent rightFuture) ∈
              (compileType signature right).alphabet := by
            simpa [compileType, hResidualRightAlphabet] using hRightSymbolMem0
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
            rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet left right
              interface q1 q2 TypeAutomatonState.final env label
              (TypeOfferSummary.mk current future)
              (hParallelCompatible := hParallelCompatible) (hSymbol := hSignatureSymbol)
              (hChildLeftRelated := hLeftRelated) (hChildRightRelated := hRightRelated)]
            refine Or.inl ⟨leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge,
              hLeftSymbolMem, hRightSymbolMem,
              hSourceReachable,
              -- This edge redirects to `q_done`, so it realizes the fusing
              -- rule and carries no source guard.
              (fun hNotBoth => absurd hBothAccept hNotBoth), hWF,
              hLocal1.congrLocalType hResidualLeftAlphabet.symm,
              hLocal2.congrLocalType hResidualRightAlphabet.symm,
              hSync, hLabelEq, hCurrentEq, hFutureHidden, ?_⟩
            simp [hBothAccept]
          refine ⟨.final, hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_final signature alphabet left right interface
      | fuse leftEnv rightEnv leftLabel rightLabel leftCurrent leftFuture rightCurrent
          rightFuture hTargetEq hLeftStep hRightStep hWF hLocal1 hLocal2 hSync
          hNotTock hLabelEq hCurrentEq hFutureEq =>
          have hLeftCurrentAlphabet : leftCurrent ⊆ residualLeft.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualLeftWellFormed
              hLeftStep.2
          have hRightCurrentAlphabet : rightCurrent ⊆ residualRight.alphabet.actions :=
            typeOffers_current_subset_fixedAlphabet hResidualRightWellFormed
              hRightStep.2
          have hLeftFutureAlphabet : leftFuture ⊆ residualLeft.alphabet.actions :=
            hFutureBound hResidualLeftInvariant hLeftStep
          have hRightFutureAlphabet :
              rightFuture ⊆ residualRight.alphabet.actions :=
            hFutureBound hResidualRightInvariant hRightStep
          have hResidualParallelCompatible :
              PactTypeAlphabet.ParallelCompatible alphabet residualLeft.alphabet
                residualRight.alphabet interface :=
            hResidualLeftAlphabet ▸ hResidualRightAlphabet ▸ hParallelCompatible
          obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
            transitionAlphabet_of_par_component
              (leftCurrent := leftCurrent) (leftFuture := leftFuture)
              (rightCurrent := rightCurrent) (rightFuture := rightFuture)
              signature alphabet residualLeft residualRight interface hWF hInterface
              hResidualLeftWellFormed hResidualRightWellFormed
              hResidualParallelCompatible
              hLeftCurrentAlphabet hLeftFutureAlphabet
              hRightCurrentAlphabet hRightFutureAlphabet
              hLocal1 hLocal2 hSync hLabelEq
              (hCurrentEq ▸ hFutureEq ▸ hSignatureSymbol)
          have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel
              (TypeOfferSummary.mk leftCurrent leftFuture) ∈
              (compileType signature left).alphabet := by
            simpa [compileType, hResidualLeftAlphabet] using hLeftSymbolMem0
          have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel
              (TypeOfferSummary.mk rightCurrent rightFuture) ∈
              (compileType signature right).alphabet := by
            simpa [compileType, hResidualRightAlphabet] using hRightSymbolMem0
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
            rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet left right
              interface q1 q2 TypeAutomatonState.final env label
              (TypeOfferSummary.mk current future)
              (hParallelCompatible := hParallelCompatible) (hSymbol := hSignatureSymbol)
              (hChildLeftRelated := hLeftRelated) (hChildRightRelated := hRightRelated)]
            refine Or.inl ⟨leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge,
              hLeftSymbolMem, hRightSymbolMem,
              hSourceReachable,
              -- As in `fuse_tock`: a redirecting edge carries no source guard.
              (fun hNotBoth => absurd hBothAccept hNotBoth), hWF,
              hLocal1.congrLocalType hResidualLeftAlphabet.symm,
              hLocal2.congrLocalType hResidualRightAlphabet.symm,
              hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
            simp [hBothAccept]
          refine ⟨.final, hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_final signature alphabet left right interface
      -- Survivor steps leave a single child re-stamped with the parent alphabet;
      -- the sibling is already `skip` at the source, so its state is accepting.
      -- The label and offers now line up with the survivor edge, and H13 turns
      -- the `skip` sibling into the accepting state the edge needs.  What is
      -- still missing is purely automaton-side: the survivor edge carries the
      -- product environment unprojected, so `parallelComponentEdgeAllowed`
      -- demands the parent symbol be legal for the CHILD alphabet, and
      -- `q1 ∈ states` for the finished sibling.  Neither transports from the
      -- parent symbol, since `mergeHidden` keeps the other side's actions.
      | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          sorry -- OPEN: parent symbol does not transport to the child alphabet
      | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          sorry -- OPEN: parent symbol does not transport to the child alphabet
      | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          sorry -- OPEN: parent symbol does not transport to the child alphabet
      | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          sorry -- OPEN: parent symbol does not transport to the child alphabet
    · rintro ⟨state', hEdge, hTargetRelated⟩
      rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet left right
        interface q1 q2 state' env label (TypeOfferSummary.mk current future)
        (hParallelCompatible := hParallelCompatible) (hSymbol := hSignatureSymbol)
        (hChildLeftRelated := hLeftRelated) (hChildRightRelated := hRightRelated)] at hEdge
      -- survivor edge: one component already rests at an accepting state.
      rcases hEdge with hEdge | hSurvivorEdge
      on_goal 2 => sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
      obtain ⟨leftEnv, rightEnv, leftLabel, rightLabel,
        leftOffers, rightOffers, q1', q2', hLeftEdge, hRightEdge,
        hLeftSync, hRightSync,
        _hEdgeSourceReachable, _hEdgeSourceLive,
        hWF, hLocal1, hLocal2, hSync, hLabelEq, hCurrentEq, hFutureEq,
        hRedirect⟩ := hEdge
      let leftCurrent := leftOffers.current
      let leftFuture := leftOffers.future
      let rightCurrent := rightOffers.current
      let rightFuture := rightOffers.future
      -- `SyncEdges_I` already carried each component symbol's own alphabet.
      have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel leftOffers ∈
          (compileType signature left).alphabet := hLeftSync
      have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel rightOffers ∈
          (compileType signature right).alphabet := hRightSync
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
            (.skip leftSkipAlphabet) q1' hParCoherent.1 hLeftAcceptRelated
          simpa [PactType.alphabet] using
            hTargetAlphabet.trans hResidualLeftAlphabet.symm
        have hRightSkipAlphabet : rightSkipAlphabet = residualRight.alphabet := by
          have hTargetAlphabet := relationMembership_alphabet_eq signature right
            (.skip rightSkipAlphabet) q2' hParCoherent.2 hRightAcceptRelated
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
          ⟨qq1, qq2, resL, resR, hEqAgain, _, _, _⟩ |
            ⟨qq, resL, hEqAgain, _, _⟩ | ⟨qq, resR, hEqAgain, _, _⟩ | hEqAgain
        · simp at hEqAgain
        · simp at hEqAgain
        · simp at hEqAgain
        · injection hEqAgain with hResidualEqAgain hStateEqAgain
          subst hResidualEqAgain
          simp only [] at hCurrentEq hFutureEq
          have hLeftFutureEmpty : leftFuture = ∅ := by
            have hLeftFuture :=
              helper_h15_edge_future_offers_agree signature hLeftRelated
                hLeftAcceptRelated hLeftEdge
            change leftOffers.future = ∅
            simpa [typeFutureOffers, typeFutureOffersFuel, PactType.alphabet]
              using hLeftFuture
          have hRightFutureEmpty : rightFuture = ∅ := by
            have hRightFuture :=
              helper_h15_edge_future_offers_agree signature hRightRelated
                hRightAcceptRelated hRightEdge
            change rightOffers.future = ∅
            simpa [typeFutureOffers, typeFutureOffersFuel, PactType.alphabet]
              using hRightFuture
          have hHiddenFutureEmpty :
              hideTypeOffers interface (leftFuture ∪ rightFuture) = ∅ := by
            rw [hLeftFutureEmpty, hRightFutureEmpty]
            simp [hideTypeOffers]
          have hFutureEmpty : future = ∅ := by
            rw [hFutureEq, hHiddenFutureEmpty]
          by_cases hTock :
              TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
          · rw [hLabelEq, hCurrentEq, hFutureEmpty]
            simpa only [hSourceAlphabet] using
              (⟨TypeTransition.par_fuse env leftEnv rightEnv interface residualLeft
                residualRight leftLabel rightLabel leftCurrent leftFuture rightCurrent
                rightFuture hLeftStep.1 hLeftStep.2 hRightStep.1 hRightStep.2
                ⟨hWF, hLocal1.congrLocalType hResidualLeftAlphabet,
                  hLocal2.congrLocalType hResidualRightAlphabet, hSync⟩,
              TypeOffers.par_fuse_tock env leftEnv rightEnv interface residualLeft
                residualRight leftLabel rightLabel leftCurrent leftFuture rightCurrent
                rightFuture hLeftStep.2 hRightStep.2
                (hLocal1.congrLocalType hResidualLeftAlphabet)
                (hLocal2.congrLocalType hResidualRightAlphabet)
                ⟨hWF, hSync⟩ hTock⟩ : DecoratedTypeTransition env
                  (.par (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                    residualRight.alphabet interface) residualLeft residualRight
                    interface) (TypeLabel.combine interface leftLabel rightLabel)
                  (TypeOfferSummary.mk
                    (hideTypeOffers interface (leftCurrent ∪ rightCurrent)) ∅)
                  (.skip (PactTypeAlphabet.mergeHidden residualLeft.alphabet
                    residualRight.alphabet interface)))
          · rw [hLabelEq, hCurrentEq, hFutureEq]
            simpa only [hSourceAlphabet] using
              (⟨TypeTransition.par_fuse env leftEnv rightEnv interface residualLeft
                residualRight leftLabel rightLabel leftCurrent leftFuture rightCurrent
                rightFuture hLeftStep.1 hLeftStep.2 hRightStep.1 hRightStep.2
                ⟨hWF, hLocal1.congrLocalType hResidualLeftAlphabet,
                  hLocal2.congrLocalType hResidualRightAlphabet, hSync⟩,
              TypeOffers.par_fuse env leftEnv rightEnv interface residualLeft
                residualRight leftLabel rightLabel leftCurrent leftFuture
                rightCurrent rightFuture hLeftStep.2 hRightStep.2
                (hLocal1.congrLocalType hResidualLeftAlphabet)
                (hLocal2.congrLocalType hResidualRightAlphabet)
                ⟨hWF, hSync⟩ hTock⟩ : DecoratedTypeTransition env
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
            hRightTargetRelated, _hTargetReachable⟩ |
            ⟨qq, resL, hEqAgain, _, _⟩ | ⟨qq, resR, hEqAgain, _, _⟩ | hEqAgain
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
          -- A `skip` source only steps to `skip`, so `hNonFinal` bounds the
          -- targets but not the sources.
          have hLeftSourceSkip : residualLeft = .skip residualLeft.alphabet →
              leftTarget = .skip leftTarget.alphabet := by
            intro hSkip
            rw [hSkip] at hLeftStep
            cases hLeftStep.1
            simp [PactType.alphabet]
          have hRightSourceSkip : residualRight = .skip residualRight.alphabet →
              rightTarget = .skip rightTarget.alphabet := by
            intro hSkip
            rw [hSkip] at hRightStep
            cases hRightStep.1
            simp [PactType.alphabet]
          by_cases hLeftSkip : residualLeft = .skip residualLeft.alphabet
          · -- Left source is `skip`, so `left_complete` is the only applicable
            -- rule; its target is `rightTarget.reannotate`, not the `.par` node
            -- the `.pair` state forces here.
            by_cases hRightSkip : residualRight = .skip residualRight.alphabet
            · exact absurd ⟨hLeftSourceSkip hLeftSkip, hRightSourceSkip hRightSkip⟩
                hNonFinal
            · sorry -- OPEN: `left_complete` targets `reannotate`, not `.par`
          by_cases hRightSkip : residualRight = .skip residualRight.alphabet
          · -- Mirror: `right_complete` targets `leftTarget.reannotate`.
            sorry -- OPEN: `right_complete` targets `reannotate`, not `.par`
          have hLeftNotSkip : residualLeft ≠ .skip residualLeft.alphabet := hLeftSkip
          have hRightNotSkip : residualRight ≠ .skip residualRight.alphabet := hRightSkip
          simp only [] at hCurrentEq hFutureEq
          rw [hLabelEq, hCurrentEq, hFutureEq, hResidualEqAgain]
          simpa only [hSourceAlphabet] using
            (⟨TypeTransition.par env leftEnv rightEnv interface residualLeft leftTarget
              residualRight rightTarget leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture hLeftNotSkip hRightNotSkip
              hLeftStep.1 hLeftStep.2 hRightStep.1 hRightStep.2
              hNonFinal ⟨hWF, hLocal1.congrLocalType hResidualLeftAlphabet,
                hLocal2.congrLocalType hResidualRightAlphabet, hSync⟩,
            TypeOffers.par env leftEnv rightEnv interface residualLeft leftTarget
              residualRight rightTarget leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture hLeftNotSkip hRightNotSkip
              hLeftStep.2 hRightStep.2 hNonFinal
              (hLocal1.congrLocalType hResidualLeftAlphabet)
              (hLocal2.congrLocalType hResidualRightAlphabet) ⟨hWF, hSync⟩⟩ :
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
        · simp at hEqAgain
        · simp at hEqAgain
  · -- survivor-left: the parent alphabet is stamped onto a left child residual.
    sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
  · -- survivor-right: the parent alphabet is stamped onto a right child residual.
    sorry -- BLOCKED(pending-issues.md#1): needs `ReannotationSafe`
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

end

end Pact
