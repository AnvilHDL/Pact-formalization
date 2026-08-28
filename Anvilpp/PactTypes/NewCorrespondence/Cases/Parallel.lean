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
    (hLeftWellFormed : left.AlphabetWellFormed)
    (hRightWellFormed : right.AlphabetWellFormed)
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
      hRightRelated, hSourceReachable⟩ | hEntryEq
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
    constructor
    · intro hStep
      cases decoratedTypeTransition_par_cases hStep with
      | step leftEnv rightEnv leftLabel rightLabel leftTarget rightTarget
          leftCurrent leftFuture rightCurrent rightFuture hTargetEq hNonFinal
          hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq hCurrentEq hFutureEq =>
          -- TODO(parallel-alphabet-gap): the offers a residual type exposes
          -- on one step must lie within that type's own fixed alphabet — a
          -- basic well-typedness fact the paper takes for granted.  Here the
          -- residual is `τ1`/`τ2` *after* the steps that got us to `q1`/`q2`,
          -- not literally the original `τ1`/`τ2` from the `‖_I` term, so this
          -- needs "well-formedness of the fixed alphabet is preserved as a
          -- type steps/unfolds," which is not yet proved anywhere. For plain
          -- recursive unfolding it should be routine, but the offer/choice
          -- construct `τ&{...}`'s selected-branch compilation reassigns
          -- alphabets in a way that needs its own side-proof first (the same
          -- gap that blocks the `AlphabetCoherent`-style argument used
          -- elsewhere from being strengthened to full well-formedness).
          -- Genuine, separate proof debt in the offer-branch machinery, not
          -- specific to parallel composition.  Left as `sorry` pending that
          -- development.
          have hLeftCurrentAlphabet : leftCurrent ⊆ residualLeft.alphabet.actions := by
            sorry
          have hLeftFutureAlphabet : leftFuture ⊆ residualLeft.alphabet.actions := by
            sorry
          have hRightCurrentAlphabet : rightCurrent ⊆ residualRight.alphabet.actions := by
            sorry
          have hRightFutureAlphabet : rightFuture ⊆ residualRight.alphabet.actions := by
            sorry
          have hResidualLeftWellFormed : residualLeft.AlphabetWellFormed := by
            sorry
          have hResidualRightWellFormed : residualRight.AlphabetWellFormed := by
            sorry
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
            refine ⟨leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge,
              hSourceReachable, hWF,
              hLocal1.congrLocalType hResidualLeftAlphabet.symm,
              hLocal2.congrLocalType hResidualRightAlphabet.symm,
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
          -- TODO(parallel-alphabet-gap): see the matching comment in the
          -- `step` case above.
          have hLeftCurrentAlphabet : leftCurrent ⊆ residualLeft.alphabet.actions := by
            sorry
          have hLeftFutureAlphabet : leftFuture ⊆ residualLeft.alphabet.actions := by
            sorry
          have hRightCurrentAlphabet : rightCurrent ⊆ residualRight.alphabet.actions := by
            sorry
          have hRightFutureAlphabet : rightFuture ⊆ residualRight.alphabet.actions := by
            sorry
          have hResidualLeftWellFormed : residualLeft.AlphabetWellFormed := by
            sorry
          have hResidualRightWellFormed : residualRight.AlphabetWellFormed := by
            sorry
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
            refine ⟨leftEnv, rightEnv, leftLabel, rightLabel,
              TypeOfferSummary.mk leftCurrent leftFuture,
              TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
              hLeftEdge, hRightEdge,
              hSourceReachable, hWF,
              hLocal1.congrLocalType hResidualLeftAlphabet.symm,
              hLocal2.congrLocalType hResidualRightAlphabet.symm,
              hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
            simp [hBothAccept]
          refine ⟨.final, hEdgeFact, ?_⟩
          rw [hTargetEq]
          exact relationMembership_par_final signature alphabet left right interface
    · rintro ⟨state', hEdge, hTargetRelated⟩
      rw [buildParallelAutomaton_pair_hasEdge_iff signature alphabet left right
        interface q1 q2 state' env label (TypeOfferSummary.mk current future)
        (hParallelCompatible := hParallelCompatible) (hSymbol := hSignatureSymbol)
        (hChildLeftRelated := hLeftRelated) (hChildRightRelated := hRightRelated)] at hEdge
      obtain ⟨leftEnv, rightEnv, leftLabel, rightLabel,
        leftOffers, rightOffers, q1', q2', hLeftEdge, hRightEdge,
        _hEdgeSourceReachable,
        hWF, hLocal1, hLocal2, hSync, hLabelEq, hCurrentEq, hFutureEq,
        hRedirect⟩ := hEdge
      let leftCurrent := leftOffers.current
      let leftFuture := leftOffers.future
      let rightCurrent := rightOffers.current
      let rightFuture := rightOffers.future
      have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEnv leftLabel leftOffers ∈
          (compileType signature left).alphabet :=
        compileType_hasEdge_symbol_mem signature left hLeftEdge
      have hRightSymbolMem : TypeAutomatonSymbol.mk rightEnv rightLabel rightOffers ∈
          (compileType signature right).alphabet :=
        compileType_hasEdge_symbol_mem signature right hRightEdge
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
          ⟨qq1, qq2, resL, resR, hEqAgain, _, _, _⟩ | hEqAgain
        · simp at hEqAgain
        · injection hEqAgain with hResidualEqAgain hStateEqAgain
          subst hResidualEqAgain
          simp only [] at hCurrentEq hFutureEq
          rw [hLabelEq, hCurrentEq, hFutureEq]
          simpa only [hSourceAlphabet] using
            (⟨TypeTransition.par_fuse env leftEnv rightEnv interface residualLeft
              residualRight leftLabel rightLabel leftCurrent leftFuture rightCurrent
              rightFuture hLeftStep.1 hLeftStep.2 hRightStep.1 hRightStep.2
              ⟨hWF, hLocal1.congrLocalType hResidualLeftAlphabet,
                hLocal2.congrLocalType hResidualRightAlphabet, hSync⟩,
            TypeOffers.par_fuse env leftEnv rightEnv interface residualLeft residualRight
              leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
              hLeftStep.2 hRightStep.2
              (hLocal1.congrLocalType hResidualLeftAlphabet)
              (hLocal2.congrLocalType hResidualRightAlphabet)
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
              residualRight rightTarget leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture hLeftStep.1 hLeftStep.2 hRightStep.1 hRightStep.2
              hNonFinal ⟨hWF, hLocal1.congrLocalType hResidualLeftAlphabet,
                hLocal2.congrLocalType hResidualRightAlphabet, hSync⟩,
            TypeOffers.par env leftEnv rightEnv interface residualLeft leftTarget
              residualRight rightTarget leftLabel rightLabel leftCurrent leftFuture
              rightCurrent rightFuture
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
