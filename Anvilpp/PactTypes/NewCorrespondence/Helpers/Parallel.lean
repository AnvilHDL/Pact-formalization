import Anvilpp.PactTypes.NewCorrespondence.Helpers.Sequence
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Describes the two semantic forms of a decorated parallel step. -/
inductive ParDecoratedStepCase
    (parentAlphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface) (target : PactType)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | step (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftTarget rightTarget : PactType)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .par parentAlphabet leftTarget rightTarget interface →
      ¬ (leftTarget = .skip leftTarget.alphabet ∧
        rightTarget = .skip rightTarget.alphabet) →
      -- The ordinary rule's own source guard: both components still live.
      left ≠ .skip left.alphabet →
      right ≠ .skip right.alphabet →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      env.WellFormed →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | fuse_tock (leftEnv rightEnv : TypeEnvironment)
      (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .skip parentAlphabet →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) (.skip left.alphabet) →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) (.skip right.alphabet) →
      env.WellFormed →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = ∅ →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | fuse (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .skip parentAlphabet →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) (.skip left.alphabet) →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) (.skip right.alphabet) →
      env.WellFormed →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      TypeLabel.combine interface leftLabel rightLabel ≠ TypeLabel.tock →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  -- The left side is already `skip`, so the right survives with its own label.
  | left_complete (rightTarget : PactType)
      (rightCurrent rightFuture : Finset BareMessage) :
      target = rightTarget.reannotate parentAlphabet →
      left = .skip left.alphabet →
      rightTarget ≠ .skip rightTarget.alphabet →
      DecoratedTypeTransition env right label
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      restrictTypeOffers interface rightCurrent = ∅ →
      restrictTypeOffers interface rightFuture = ∅ →
      env.WellFormed →
      label ≠ TypeLabel.tock →
      current = hideTypeOffers interface rightCurrent →
      future = hideTypeOffers interface rightFuture →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | left_complete_tock (rightTarget : PactType)
      (rightCurrent rightFuture : Finset BareMessage) :
      target = rightTarget.reannotate parentAlphabet →
      left = .skip left.alphabet →
      rightTarget ≠ .skip rightTarget.alphabet →
      DecoratedTypeTransition env right label
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      restrictTypeOffers interface rightCurrent = ∅ →
      restrictTypeOffers interface rightFuture = ∅ →
      env.WellFormed →
      label = TypeLabel.tock →
      current = hideTypeOffers interface rightCurrent →
      future = ∅ →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  -- Mirror of `left_complete`: the right side is already `skip`.
  | right_complete (leftTarget : PactType)
      (leftCurrent leftFuture : Finset BareMessage) :
      target = leftTarget.reannotate parentAlphabet →
      right = .skip right.alphabet →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition env left label
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      restrictTypeOffers interface leftCurrent = ∅ →
      restrictTypeOffers interface leftFuture = ∅ →
      env.WellFormed →
      label ≠ TypeLabel.tock →
      current = hideTypeOffers interface leftCurrent →
      future = hideTypeOffers interface leftFuture →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | right_complete_tock (leftTarget : PactType)
      (leftCurrent leftFuture : Finset BareMessage) :
      target = leftTarget.reannotate parentAlphabet →
      right = .skip right.alphabet →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition env left label
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      restrictTypeOffers interface leftCurrent = ∅ →
      restrictTypeOffers interface leftFuture = ∅ →
      env.WellFormed →
      label = TypeLabel.tock →
      current = hideTypeOffers interface leftCurrent →
      future = ∅ →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future

/-- The offer judgment repeats the side conditions of the transition
judgment. Forgetting the two offer sets therefore leaves a semantic step under
the same environment. -/
theorem TypeOffers.toTypeTransition
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    TypeTransition env source label target := by
  induction hOffers using TypeOffers.rec with
  | action env alphabet msg dir hConditions hAlphabet =>
      exact TypeTransition.action env alphabet msg dir hConditions hAlphabet
  | action_wait env alphabet msg dir hConditions hAlphabet =>
      exact TypeTransition.action_wait env alphabet msg dir hConditions hAlphabet
  | choice_left env alphabet left right hEnv =>
      exact TypeTransition.choice_left env alphabet left right hEnv.1 hEnv.2
  | choice_right env alphabet left right hEnv =>
      exact TypeTransition.choice_right env alphabet left right hEnv.1 hEnv.2
  | fair_left env alphabet bid left right hEnv =>
      exact TypeTransition.fair_left env alphabet bid left right hEnv.1 hEnv.2
  | fair_right env alphabet bid left right hEnv =>
      exact TypeTransition.fair_right env alphabet bid left right hEnv.1 hEnv.2
  | cycle env alphabet hConditions =>
      exact TypeTransition.cycle env alphabet hConditions
  | cycle_wait env alphabet hConditions =>
      exact TypeTransition.cycle_wait env alphabet hConditions
  | skip env alphabet hConditions =>
      exact TypeTransition.skip env alphabet hConditions
  | progress env alphabet pid hEnv =>
      exact TypeTransition.progress env alphabet pid hEnv.1 hEnv.2
  | recur env alphabet name body hEnv =>
      exact TypeTransition.recur env alphabet name body hEnv.1 hEnv.2
  | seq env alphabet left leftTarget right label current childFuture hOffers
      hNotSkip hNotTock ih =>
      exact TypeTransition.seq env alphabet left leftTarget right label ih
        hNotSkip
  | seq_tock env alphabet left leftTarget right current childFuture hOffers
      hNotSkip ih =>
      exact TypeTransition.seq env alphabet left leftTarget right
        TypeLabel.tock ih hNotSkip
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hOffers hNotTock ih =>
      exact TypeTransition.seq_fuse env alphabet skipAlphabet left right label ih
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hOffers ih =>
      exact TypeTransition.seq_fuse env alphabet skipAlphabet left right
        TypeLabel.tock ih
  | xoffer_branch env alphabet elseType branches action processType hConditions
      hAlphabet =>
      exact TypeTransition.xoffer_branch env alphabet elseType branches action
        processType hConditions hAlphabet
  | xoffer_else env alphabet elseType branches hConditions hAlphabet =>
      exact TypeTransition.xoffer_else env alphabet elseType branches hConditions
        hAlphabet
  | xoffer_wait env alphabet elseType branches hConditions hAlphabet =>
      exact TypeTransition.xoffer_wait env alphabet elseType branches hConditions
        hAlphabet
  | offer_some env alphabet elseType branches enabled hConditions hAlphabet =>
      exact TypeTransition.offer_some env alphabet elseType branches enabled
        hConditions hAlphabet
  | offer_else env alphabet elseType branches hConditions hAlphabet =>
      exact TypeTransition.offer_else env alphabet elseType branches hConditions
        hAlphabet
  | offer_wait env alphabet elseType branches hConditions hAlphabet =>
      exact TypeTransition.offer_wait env alphabet elseType branches hConditions
        hAlphabet
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip
      hLeftOffers hRightOffers hNotFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      exact TypeTransition.par outer leftEnv rightEnv interface left leftTarget
        right rightTarget leftLabel rightLabel leftCurrent leftFuture
        rightCurrent rightFuture hLeftNotSkip hRightNotSkip
        ihLeft hLeftOffers ihRight hRightOffers hNotFinal
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide hNotTock ihLeft ihRight =>
      exact TypeTransition.par_fuse outer leftEnv rightEnv interface left right
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
        ihLeft hLeftOffers ihRight hRightOffers
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      exact TypeTransition.par_fuse outer leftEnv rightEnv interface left right
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
        ihLeft hLeftOffers ihRight hRightOffers
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | left_complete outer interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip hRightNotSkip hRightOffers hNotSkip hRC hRF hWF
      hNotTock ihRight
  | left_complete_tock outer interface left right right' rightLabel rightCurrent
      rightFuture hLeftSkip hRightNotSkip hRightOffers hNotSkip hRC hRF hWF
      hNotTock ihRight =>
      exact TypeTransition.left_complete outer interface left right right'
        rightLabel rightCurrent rightFuture hLeftSkip hRightNotSkip ihRight
        hRightOffers
        hNotSkip hRC hRF hWF
  | right_complete outer interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip hLeftNotSkip hLeftOffers hNotSkip hLC hLF hWF
      hNotTock ihLeft
  | right_complete_tock outer interface left left' right leftLabel leftCurrent
      leftFuture hRightSkip hLeftNotSkip hLeftOffers hNotSkip hLC hLF hWF
      hNotTock ihLeft =>
      exact TypeTransition.right_complete outer interface left left' right
        leftLabel leftCurrent leftFuture hRightSkip hLeftNotSkip ihLeft
        hLeftOffers
        hNotSkip hLC hLF hWF



/--
Proves that every decorated parallel step either retains both components or
fuses them once both complete.
 -/
theorem decoratedTypeTransition_par_cases
    {env : TypeEnvironment} {label : TypeLabel}
    {alphabet : PactTypeAlphabet} {left right target : PactType}
    {interface : Interface}
    {current future : Finset BareMessage}
    (hStep :
      DecoratedTypeTransition env
        (.par alphabet left right interface) label
        (TypeOfferSummary.mk current future) target) :
    ParDecoratedStepCase alphabet left right interface target env label current
      future := by
  rcases hStep with ⟨_, hOffers⟩
  cases hOffers with
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeftOffers hRightOffers hNonFinal hLocal1
      hLocal2 hSide =>
      exact ParDecoratedStepCase.step leftEnv rightEnv leftLabel rightLabel
        leftTarget rightTarget leftCurrent leftFuture rightCurrent rightFuture
        rfl hNonFinal hLeftNotSkip hRightNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 rfl rfl rfl
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide hNotTock =>
      exact ParDecoratedStepCase.fuse leftEnv rightEnv leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture rfl
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 hNotTock rfl rfl rfl
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocal1 hLocal2 hSide hTock =>
      exact ParDecoratedStepCase.fuse_tock leftEnv rightEnv leftLabel
        rightLabel
        leftCurrent leftFuture rightCurrent rightFuture rfl
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 hTock rfl rfl rfl
  | left_complete outer interface left right rightTarget rightLabel rightCurrent
      rightFuture hLeftSkip _ hRightOffers hNotSkip hRC hRF hWF hNotTock =>
      exact ParDecoratedStepCase.left_complete rightTarget rightCurrent
        rightFuture rfl hLeftSkip hNotSkip
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hRC hRF hWF hNotTock rfl rfl
  | left_complete_tock outer interface left right rightTarget rightLabel
      rightCurrent rightFuture hLeftSkip _ hRightOffers hNotSkip hRC hRF hWF
      hTock =>
      exact ParDecoratedStepCase.left_complete_tock rightTarget rightCurrent
        rightFuture rfl hLeftSkip hNotSkip
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hRC hRF hWF hTock rfl rfl
  | right_complete outer interface left leftTarget right leftLabel leftCurrent
      leftFuture hRightSkip _ hLeftOffers hNotSkip hLC hLF hWF hNotTock =>
      exact ParDecoratedStepCase.right_complete leftTarget leftCurrent
        leftFuture rfl hRightSkip hNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        hLC hLF hWF hNotTock rfl rfl
  | right_complete_tock outer interface left leftTarget right leftLabel
      leftCurrent leftFuture hRightSkip _ hLeftOffers hNotSkip hLC hLF hWF
      hTock =>
      exact ParDecoratedStepCase.right_complete_tock leftTarget leftCurrent
        leftFuture rfl hRightSkip hNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        hLC hLF hWF hTock rfl rfl


set_option maxHeartbeats 1000000 in
/-- High-level proof idea:

Unfold the construction of the parallel automaton. The `.final` state is the
fresh completed (`q_done`) state introduced by the parallel construction.

The only edges whose source is this state are the idle edges inserted by the
parallel compiler. By construction, such an edge exists exactly when the
environment is well-formed and non-clock; its label is silent, both offer
components are empty, and its target is `.final` itself.

For the forward direction, invert an edge out of `.final`; since no other
parallel edge family has `.final` as its source, it must be this idle
self-loop, giving all the required conditions.

For the reverse direction, given these conditions, the compiler's idle-edge
construction directly supplies the required self-loop at `.final`.
-/
theorem buildParallelAutomaton_final_hasEdge_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (env : TypeEnvironment) (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabetFor alphabet) :
    (compileType signature (.par alphabet left right interface)).HasEdge
        TypeAutomatonState.final env label offers target ↔
      env.WellFormed ∧ env.clock = false ∧ label = TypeLabel.silent ∧
      offers = TypeOfferSummary.mk ∅ ∅ ∧ target = TypeAutomatonState.final := by
  classical
  constructor
  · intro hEdge
    have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
      (.par alphabet left right interface) TypeAutomatonState.final target env
      label offers
      hSymbol).mp hEdge
    obtain ⟨edge, hPending, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ := hResolved
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    have hWhole : compileTypeFuel signature
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
        buildParallelAutomaton signature alphabet left.alphabet right.alphabet
          interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right) := by
      rw [hFuelEq]
      rw [compileTypeFuel.eq_def]
      show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (compiledChildFutureFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compiledChildFutureFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
      rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
        compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
      rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
          (le_max_left _ _),
        compiledChildFutureFuel_eq_computeFutureOf signature _ right
          (le_max_right _ _)]
      rfl
    rw [hWhole] at hPending
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
      parallelRightCompleteSurvivorEdges, parallelDoneEdges, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image,
      Finset.mem_inter] at hPending
    rcases hPending with
        ⟨⟨⟨⟨⟨leftEdge, -, rightEdge, -, hEq⟩ |
          ⟨leftState, -, rightEdge, -, hEq⟩⟩ |
          ⟨rightState, -, leftEdge, -, hEq⟩⟩ |
          ⟨rightEdge, -, hEq⟩⟩ |
          ⟨leftEdge, -, hEq⟩, -⟩ |
        ⟨environment, hEnvironment, hEq⟩
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · rw [← hEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget
      subst env
      injection hLabel with hLabelEq
      subst hLabelEq
      refine ⟨localEnvironment_wellFormed signature
          (TypeAlphabet.localEnvironmentsFor_subset_localEnvironments
            signature alphabet hEnvironment.1),
        hEnvironment.2, rfl, ?_,
        hTarget.symm⟩
      · cases offers with
        | mk current future => simp_all
  · rintro ⟨hWF, hClock, hLabel, hOffers, hTarget⟩
    subst hLabel; subst hOffers; subst hTarget
    rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.par alphabet left right interface) TypeAutomatonState.final
      TypeAutomatonState.final
      env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
    have hLocal : env ∈ signature.localEnvironmentsFor alphabet :=
      transitionAlphabetFor_localEnvironment_mem signature alphabet hSymbol
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    have hWhole : compileTypeFuel signature
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
        buildParallelAutomaton signature alphabet left.alphabet right.alphabet
          interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right) := by
      rw [hFuelEq]
      rw [compileTypeFuel.eq_def]
      show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (compiledChildFutureFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compiledChildFutureFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
      rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
        compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
      rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
          (le_max_left _ _),
        compiledChildFutureFuel_eq_computeFutureOf signature _ right
          (le_max_right _ _)]
      rfl
    refine ⟨
      { source := TypeAutomatonState.final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := TypeAutomatonState.final }, ?_, rfl, rfl, rfl, rfl, by simp, rfl⟩
    rw [hWhole]
    simp [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelDoneEdges, hLocal, hClock]

/-- Every public edge leaving a parallel product state extends the paper's
joint `Reach` path to its target. -/
theorem compiledParallel_pair_edge_target_reachable
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {q1 q2 target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.par alphabet left right interface)).alphabet)
    (hEdge : (compileType signature (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label offers target) :
    ParallelReachable signature alphabet left.alphabet right.alphabet interface
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      (computeFutureOf signature left)
      (computeFutureOf signature right) target := by
  have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
    (.par alphabet left right interface) (.pair q1 q2) target env label offers
    hSymbol).mp hEdge
  obtain ⟨edge, hPending, hSource, _, _, _, _, hTarget⟩ := hResolved
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole : compileTypeFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface) =
      buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
    rw [compileTypeFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
    rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
        (le_max_left _ _),
      compiledChildFutureFuel_eq_computeFutureOf signature _ right
        (le_max_right _ _)]
    rfl
  rw [hWhole] at hPending
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_filter] at hPending
  rcases hPending with ⟨hRawEdge, hReachable⟩ | hDone
  · -- Every transition family extends the joint reachability of its source.
    have hTargetReachable :
        ParallelReachable signature alphabet left.alphabet right.alphabet
          interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left) (computeFutureOf signature right)
          edge.target :=
      hReachable.tail_raw
        ⟨edge, by simp only [Finset.mem_union]; exact Or.inl hRawEdge,
          rfl, rfl⟩
    rw [hTarget] at hTargetReachable
    exact hTargetReachable
  · have hDoneSource : edge.source = TypeAutomatonState.final := by
      simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
      obtain ⟨environment, _, hEq⟩ := hDone
      rw [← hEq]
    rw [hDoneSource] at hSource
    exact nomatch hSource

private theorem interface_action_mem_localActions
    (signature : TypeAlphabet) {interface : Interface}
    (hInterface : interface ⊆ signature.interface)
    {action : BareMessage} (hAction : action.1 ∈ interface) :
    action ∈ signature.localActions := by
  rcases action with ⟨msg, dir⟩
  simp only [TypeAlphabet.localActions, Finset.mem_union]
  right
  simp only [TypeAlphabet.interfaceActions, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  exact ⟨msg, hInterface hAction, by cases dir <;> simp⟩

private theorem interface_action_mem_localEnvironmentActions
    (signature : TypeAlphabet) {interface : Interface}
    (hInterface : interface ⊆ signature.interface)
    {action : BareMessage} (hAction : action.1 ∈ interface) :
    action ∈ signature.localEnvironmentActions := by
  rcases action with ⟨msg, dir⟩
  simp only [TypeAlphabet.localEnvironmentActions, Finset.mem_image]
  refine ⟨(msg, dir.invert), ?_, ?_⟩
  · exact interface_action_mem_localActions signature hInterface hAction
  · cases dir <;> rfl

/-- The syntactic future menu never invents an action that is absent from the
source syntax.  This is the small footprint fact needed when a parallel
component is checked against its own fixed alphabet. -/
private theorem typeFutureOffersFuel_subset_messageActions :
    ∀ fuel processType,
      typeFutureOffersFuel fuel processType ⊆ processType.MessageActions := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType
      simp [typeFutureOffersFuel]
  | succ fuel ih =>
      intro processType
      cases processType with
      | message alphabet msg dir =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | progress alphabet pid =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | tock alphabet =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | skip alphabet =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | var alphabet name =>
          simp [typeFutureOffersFuel, PactType.MessageActions]
      | recur alphabet name body =>
          simpa [typeFutureOffersFuel, PactType.MessageActions] using ih body
      | choice alphabet left right | fairChoice alphabet _ left right =>
          simpa [typeFutureOffersFuel, PactType.MessageActions] using
            Finset.union_subset_union (ih left) (ih right)
      | seq alphabet left right =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          split
          · exact Finset.union_subset_union (ih left) (ih right)
          · exact (ih left).trans Finset.subset_union_left
      | par alphabet left right interface =>
          intro action hAction
          simp only [typeFutureOffersFuel, hideTypeOffers,
            Finset.mem_filter, Finset.mem_union, PactType.MessageActions] at hAction ⊢
          rcases hAction.1 with hLeft | hRight
          · exact Or.inl (ih left hLeft)
          · exact Or.inr (ih right hRight)
      | xoffer alphabet elseType branches | offer alphabet elseType branches =>
          simp only [typeFutureOffersFuel, PactType.MessageActions]
          have hHeadSubsetAll : ∀ (bs : List (BareMessage × PactType))
              branch, branch ∈ bs →
                {branch.1} ⊆ PactType.BranchMessageActions bs := by
            intro bs
            induction bs with
            | nil =>
                intro branch hBranch
                cases hBranch
            | cons head rest restIH =>
                intro branch hBranch
                simp only [List.mem_cons] at hBranch
                rw [PactType.BranchMessageActions.eq_def]
                rcases hBranch with rfl | hBranch
                · exact Finset.subset_union_left.trans Finset.subset_union_left
                · exact (restIH branch hBranch).trans Finset.subset_union_right
          have hBodySubsetAll : ∀ (bs : List (BareMessage × PactType))
              branch, branch ∈ bs →
                branch.2.MessageActions ⊆
                  PactType.BranchMessageActions bs := by
            intro bs
            induction bs with
            | nil =>
                intro branch hBranch
                cases hBranch
            | cons head rest restIH =>
                intro branch hBranch
                simp only [List.mem_cons] at hBranch
                rw [PactType.BranchMessageActions.eq_def]
                rcases hBranch with rfl | hBranch
                · intro action hAction
                  exact Finset.mem_union.mpr
                    (Or.inl (Finset.mem_union.mpr (Or.inr hAction)))
                · exact (restIH branch hBranch).trans Finset.subset_union_right
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              initial ⊆ elseType.MessageActions ∪
                  PactType.BranchMessageActions branches →
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                  initial ⊆
                elseType.MessageActions ∪
                  PactType.BranchMessageActions branches := by
            intro rest
            induction rest with
            | nil =>
                intro initial hInitial _
                simpa using hInitial
            | cons branch tail tailIH =>
                intro initial hInitial hRest
                apply tailIH
                · apply Finset.union_subset
                  · apply Finset.union_subset
                    · exact hInitial
                    · intro action hAction
                      have hBranch : branch ∈ branches := hRest branch (by simp)
                      exact Finset.mem_union.mpr
                        (Or.inr (hHeadSubsetAll branches branch hBranch hAction))
                  · intro action hAction
                    have hBranch : branch ∈ branches := hRest branch (by simp)
                    have hInBranch : action ∈ branch.2.MessageActions :=
                      ih branch.2 hAction
                    exact Finset.mem_union.mpr
                      (Or.inr (hBodySubsetAll branches branch hBranch hInBranch))
                · intro other hOther
                  exact hRest other (by simp [hOther])
          apply hFold branches (typeFutureOffersFuel fuel elseType)
          · exact (ih elseType).trans Finset.subset_union_left
          · simp

private theorem typeFutureOffers_subset_messageActions
    (processType : PactType) :
    typeFutureOffers processType ⊆ processType.MessageActions := by
  exact typeFutureOffersFuel_subset_messageActions _ processType

private theorem branch_body_alphabetWellFormed_of_mem
    {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    branchType.AlphabetWellFormed := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hBranches.2.2.1
      · exact ih hBranches.2.2.2 hMem

private theorem branch_action_mem_fixedAlphabet_of_mem
    {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hBranches : PactType.BranchesAlphabetWellFormed alphabet branches)
    (hMem : (action, branchType) ∈ branches) :
    action ∈ alphabet.actions := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.BranchesAlphabetWellFormed] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hBranches.1
      · exact ih hBranches.2.2.2 hMem

/-- For alphabet-well-formed syntax, its future menu is contained in the
fixed alphabet carried by that syntax node. -/
private theorem typeFutureOffersFuel_subset_fixedAlphabet :
    ∀ fuel processType, processType.AlphabetWellFormed →
      typeFutureOffersFuel fuel processType ⊆ processType.alphabet.actions := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hWF
      simp [typeFutureOffersFuel]
  | succ fuel ih =>
      intro processType hWF
      cases processType with
      | message alphabet msg dir =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simpa [typeFutureOffersFuel, PactType.alphabet] using hWF.2
      | progress alphabet pid =>
          simp [typeFutureOffersFuel]
      | tock alphabet =>
          simp [typeFutureOffersFuel]
      | skip alphabet =>
          simp [typeFutureOffersFuel]
      | var alphabet name =>
          simp [typeFutureOffersFuel]
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          change typeFutureOffersFuel fuel body ⊆ alphabet.actions
          have hBody := ih body hWF.2.2
          rw [hWF.2.1] at hBody
          exact hBody
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          exact Finset.union_subset
            ((ih left hWF.2.2.2.1).trans (by simpa [hWF.2.1]))
            ((ih right hWF.2.2.2.2).trans (by simpa [hWF.2.2.1]))
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          split
          · exact Finset.union_subset
              ((ih left hWF.2.2.2.1).trans (by simpa [hWF.2.1]))
              ((ih right hWF.2.2.2.2).trans (by simpa [hWF.2.2.1]))
          · exact (ih left hWF.2.2.2.1).trans (by simpa [hWF.2.1])
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          exact Finset.union_subset
            ((ih left hWF.2.2.2.2.1).trans (by simpa [hWF.2.2.1]))
            ((ih right hWF.2.2.2.2.2).trans (by simpa [hWF.2.2.2.1]))
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          intro action hAction
          simp only [typeFutureOffersFuel, hideTypeOffers,
            Finset.mem_filter, Finset.mem_union, PactType.alphabet] at hAction ⊢
          have hCompatible := hWF.2.1
          rw [hCompatible.parent_eq]
          simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
            Finset.mem_union]
          refine ⟨?_, hAction.2⟩
          rcases hAction.1 with hLeft | hRight
          · exact Or.inl (ih left hWF.2.2.1 hLeft)
          · exact Or.inr (ih right hWF.2.2.2 hRight)
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          have hBranchFuture : ∀ branch ∈ branches,
              typeFutureOffersFuel fuel branch.2 ⊆ alphabet.actions := by
            intro branch hBranch
            have hBranchWF := PactType.branch_alphabet_eq_of_mem
              hWF.2.2.2 hBranch
            rcases branch with ⟨branchAction, branchType⟩
            have hEntryWF : branchType.AlphabetWellFormed :=
              branch_body_alphabetWellFormed_of_mem hWF.2.2.2 hBranch
            exact (ih branchType hEntryWF).trans (by simpa [hBranchWF])
          have hBranchHead : ∀ branch ∈ branches,
              branch.1 ∈ alphabet.actions := by
            intro branch hBranch
            rcases branch with ⟨branchAction, branchType⟩
            exact branch_action_mem_fixedAlphabet_of_mem hWF.2.2.2 hBranch
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              initial ⊆ alphabet.actions →
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                  initial ⊆ alphabet.actions := by
            intro rest
            induction rest with
            | nil =>
                intro initial hInitial _
                simpa using hInitial
            | cons branch tail tailIH =>
                intro initial hInitial hRest
                apply tailIH
                · exact Finset.union_subset
                    (Finset.union_subset hInitial (by
                      intro action hAction
                      have hEq : action = branch.1 := by simpa using hAction
                      subst action
                      exact hBranchHead branch (hRest branch (by simp))))
                    (hBranchFuture branch (hRest branch (by simp)))
                · intro other hOther
                  exact hRest other (by simp [hOther])
          apply hFold branches (typeFutureOffersFuel fuel elseType)
          · exact (ih elseType hWF.2.2.1).trans (by simpa [hWF.2.1])
          · simp
      | offer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [typeFutureOffersFuel, PactType.alphabet]
          have hBranchFuture : ∀ branch ∈ branches,
              typeFutureOffersFuel fuel branch.2 ⊆ alphabet.actions := by
            intro branch hBranch
            have hBranchAlphabet := PactType.branch_alphabet_eq_of_mem
              hWF.2.2.2 hBranch
            rcases branch with ⟨branchAction, branchType⟩
            have hBranchWF : branchType.AlphabetWellFormed :=
              branch_body_alphabetWellFormed_of_mem hWF.2.2.2 hBranch
            exact (ih branchType hBranchWF).trans
              (by simpa [hBranchAlphabet])
          have hBranchHead : ∀ branch ∈ branches,
              branch.1 ∈ alphabet.actions := by
            intro branch hBranch
            rcases branch with ⟨branchAction, branchType⟩
            exact branch_action_mem_fixedAlphabet_of_mem hWF.2.2.2 hBranch
          have hFold : ∀ (rest : List (BareMessage × PactType)) initial,
              initial ⊆ alphabet.actions →
              (∀ branch ∈ rest, branch ∈ branches) →
              rest.foldl (fun offers branch =>
                  offers ∪ {branch.1} ∪ typeFutureOffersFuel fuel branch.2)
                  initial ⊆ alphabet.actions := by
            intro rest
            induction rest with
            | nil =>
                intro initial hInitial _
                simpa using hInitial
            | cons branch tail tailIH =>
                intro initial hInitial hRest
                apply tailIH
                · exact Finset.union_subset
                    (Finset.union_subset hInitial (by
                      intro action hAction
                      have hEq : action = branch.1 := by simpa using hAction
                      subst action
                      exact hBranchHead branch (hRest branch (by simp))))
                    (hBranchFuture branch (hRest branch (by simp)))
                · intro other hOther
                  exact hRest other (by simp [hOther])
          apply hFold branches (typeFutureOffersFuel fuel elseType)
          · exact (ih elseType hWF.2.2.1).trans (by simpa [hWF.2.1])
          · simp

private theorem typeFutureOffers_subset_fixedAlphabet
    (processType : PactType) (hWF : processType.AlphabetWellFormed) :
    typeFutureOffers processType ⊆ processType.alphabet.actions := by
  exact typeFutureOffersFuel_subset_fixedAlphabet _ processType hWF

private theorem typeBranchActions_subset_fixedAlphabet
    {alphabet : PactTypeAlphabet} :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchesAlphabetWellFormed alphabet branches →
        typeBranchActions branches ⊆ alphabet.actions
  | [], _ => by
      simp [typeBranchActions]
  | (action, processType) :: rest, hWF => by
      intro offered hOffered
      simp only [typeBranchActions, List.map_cons, List.toFinset_cons,
        Finset.mem_insert] at hOffered
      simp only [PactType.BranchesAlphabetWellFormed] at hWF
      rcases hOffered with rfl | hRest
      · exact hWF.1
      · exact typeBranchActions_subset_fixedAlphabet rest hWF.2.2.2 hRest

private theorem typeWaitingOffers_subset_fixedAlphabet
    {alphabet : PactTypeAlphabet} {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)}
    (hWF : PactType.BranchesAlphabetWellFormed alphabet branches) :
    typeWaitingOffers env branches ⊆ alphabet.actions := by
  intro action hAction
  simp only [typeWaitingOffers, Finset.mem_inter] at hAction
  exact typeBranchActions_subset_fixedAlphabet branches hWF hAction.2

/-- Under a clock environment, a step's current offer is always empty: every
rule with a nonempty current offer either needs an immediate need `tock`
cannot supply (`action`, `xoffer_branch`) or now carries an explicit
`env.clock = false` premise. -/
private theorem typeOffers_current_empty_of_clock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hClock : env.clock = true)
    (hOffers : TypeOffers env source label target current future) :
    current = ∅ := by
  induction hOffers using TypeOffers.rec with
  | action env alphabet msg dir hConditions =>
      exfalso
      have hImmEmpty : env.immediate = ∅ := (hConditions.1.1 hClock).1
      have hHasNeed := hConditions.2
      simp only [TypeEnvironment.hasNeed, hImmEmpty] at hHasNeed
      exact absurd hHasNeed (by simp)
  | action_wait env alphabet msg dir hConditions =>
      exact absurd hConditions.2.2 (by simp [hClock])
  | choice_left env alphabet left right hConditions => simp
  | choice_right env alphabet left right hConditions => simp
  | fair_left env alphabet bid left right hConditions => simp
  | fair_right env alphabet bid left right hConditions => simp
  | cycle | cycle_wait | skip | progress | recur | offer_some => simp
  | seq env alphabet left leftTarget right label current childFuture
      hChild hNotSkip hNotTock ih => exact ih hClock
  | seq_tock env alphabet left leftTarget right current childFuture
      hChild hNotSkip ih => exact ih hClock
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih => exact ih hClock
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih => exact ih hClock
  | xoffer_branch env alphabet elseType branches action processType hConditions =>
      exfalso
      have hImmEmpty : env.immediate = ∅ := (hConditions.1.1 hClock).1
      have hEnabled := hConditions.2.2.1
      simp only [TypeBranchEnabled, hImmEmpty] at hEnabled
      exact absurd hEnabled (by simp)
  | xoffer_else env alphabet elseType branches hConditions => simp
  | xoffer_wait env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.2 (by simp [hClock])
  | offer_else env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.1 (by simp [hClock])
  | offer_wait env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.1 (by simp [hClock])
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hRight hNonFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      cases hLocal1 with
      | clock _ =>
          rw [ihLeft (by simp [TypeEnvironment.tock]),
            ihRight (by simp [TypeEnvironment.tock])]
          simp [hideTypeOffers]
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock _ _ _ _
        exact absurd hClock (by simp [hOuterClock])
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocal1
      hLocal2 hSide hNotTock ihLeft ihRight =>
      cases hLocal1 with
      | clock _ =>
          rw [ihLeft (by simp [TypeEnvironment.tock]),
            ihRight (by simp [TypeEnvironment.tock])]
          simp [hideTypeOffers]
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock _ _ _ _
        exact absurd hClock (by simp [hOuterClock])
  -- The survivor steps under the very same environment, so its own offers are
  -- already empty under a clock.
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight =>
      rw [ihRight hClock]
      simp [hideTypeOffers]
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      cases hLocal1 with
      | clock _ =>
          rw [ihLeft (by simp [TypeEnvironment.tock]),
            ihRight (by simp [TypeEnvironment.tock])]
          simp [hideTypeOffers]
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock _ _ _ _
        exact absurd hClock (by simp [hOuterClock])

/-- Under a clock environment, a step's label is always exactly `tock`: every
rule with a non-tock label either needs an immediate need `tock` cannot
supply (`action`, `xoffer_branch`) or now carries an explicit
`env.clock = false` premise, so only `cycle` (and constructors that inherit
its label through fusion/synchronization) can fire. -/
private theorem typeOffers_label_eq_tock_of_clock
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hClock : env.clock = true)
    (hOffers : TypeOffers env source label target current future) :
    label = TypeLabel.tock := by
  induction hOffers using TypeOffers.rec with
  | action env alphabet msg dir hConditions =>
      exfalso
      have hImmEmpty : env.immediate = ∅ := (hConditions.1.1 hClock).1
      have hHasNeed := hConditions.2
      simp only [TypeEnvironment.hasNeed, hImmEmpty] at hHasNeed
      exact absurd hHasNeed (by simp)
  | action_wait env alphabet msg dir hConditions =>
      exact absurd hConditions.2.2 (by simp [hClock])
  | choice_left env alphabet left right hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | choice_right env alphabet left right hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | fair_left env alphabet bid left right hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | fair_right env alphabet bid left right hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | cycle => rfl
  | cycle_wait env alphabet hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | skip env alphabet hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | progress env alphabet pid hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | recur env alphabet name body hConditions =>
      exact absurd hConditions.2 (by simp [hClock])
  | seq env alphabet left leftTarget right label current childFuture
      hChild hNotSkip hNotTock ih => exact ih hClock
  | seq_tock env alphabet left leftTarget right current childFuture
      hChild hNotSkip ih => rfl
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih => exact ih hClock
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih => rfl
  | xoffer_branch env alphabet elseType branches action processType hConditions =>
      exfalso
      have hImmEmpty : env.immediate = ∅ := (hConditions.1.1 hClock).1
      have hEnabled := hConditions.2.2.1
      simp only [TypeBranchEnabled, hImmEmpty] at hEnabled
      exact absurd hEnabled (by simp)
  | xoffer_else env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.1 (by simp [hClock])
  | xoffer_wait env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.2 (by simp [hClock])
  | offer_some env alphabet elseType branches enabled hConditions =>
      exfalso
      have hImmEmpty : env.immediate = ∅ := (hConditions.1.1 hClock).1
      have hEnabled := hConditions.2.2
      simp only [TypeBranchEnabled, hImmEmpty] at hEnabled
      exact absurd hEnabled (by simp)
  | offer_else env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.1 (by simp [hClock])
  | offer_wait env alphabet elseType branches hConditions =>
      exact absurd hConditions.2.1 (by simp [hClock])
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hRight hNonFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      cases hLocal1 with
      | clock _ =>
          rw [ihLeft (by simp [TypeEnvironment.tock]),
            ihRight (by simp [TypeEnvironment.tock])]
          simp [TypeLabel.combine]
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock _ _ _ _
        exact absurd hClock (by simp [hOuterClock])
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocal1
      hLocal2 hSide hNotTock ihLeft ihRight =>
      cases hLocal1 with
      | clock _ =>
          rw [ihLeft (by simp [TypeEnvironment.tock]),
            ihRight (by simp [TypeEnvironment.tock])] at hNotTock
          exact absurd rfl hNotTock
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock _ _ _ _
        exact absurd hClock (by simp [hOuterClock])
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock ihRight
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNotTock ihRight =>
      exact absurd (ihRight hClock) hNotTock
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTock _ =>
      exact hTock
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      exact hTock

theorem typeOffers_current_subset_fixedAlphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource : source.AlphabetWellFormed)
    (hOffers : TypeOffers env source label target current future) :
    current ⊆ source.alphabet.actions := by
  induction hOffers using TypeOffers.rec with
  | action env alphabet msg dir hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using
        (Finset.singleton_subset_iff.mpr hSource.2)
  | action_wait env alphabet msg dir hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simpa [PactType.alphabet] using
        (Finset.singleton_subset_iff.mpr hSource.2)
  | choice_left | choice_right | fair_left | fair_right |
      cycle | cycle_wait | skip | progress | recur | offer_some =>
      simp [PactType.alphabet]
  | seq env alphabet left leftTarget right label current childFuture
      hChild hNotSkip hNotTock ih =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact (ih hSource.2.2.2.1).trans (by
        change left.alphabet.actions ⊆ alphabet.actions
        rw [hSource.2.1])
  | seq_tock env alphabet left leftTarget right current childFuture
      hChild hNotSkip ih =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact (ih hSource.2.2.2.1).trans (by
        change left.alphabet.actions ⊆ alphabet.actions
        rw [hSource.2.1])
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact (ih hSource.2.2.2.1).trans (by
        change left.alphabet.actions ⊆ alphabet.actions
        rw [hSource.2.1])
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact (ih hSource.2.2.2.1).trans (by
        change left.alphabet.actions ⊆ alphabet.actions
        rw [hSource.2.1])
  | xoffer_branch env alphabet elseType branches action processType hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro offered hOffered
      simp only [Finset.mem_singleton] at hOffered
      subst offered
      exact branch_action_mem_fixedAlphabet_of_mem hSource.2.2.2
        hConditions.2.1
  | xoffer_else env alphabet elseType branches hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      simp
  | xoffer_wait env alphabet elseType branches hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact typeWaitingOffers_subset_fixedAlphabet hSource.2.2.2
  | offer_else env alphabet elseType branches hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact typeBranchActions_subset_fixedAlphabet branches hSource.2.2.2
  | offer_wait env alphabet elseType branches hConditions =>
      simp only [PactType.AlphabetWellFormed] at hSource
      exact typeWaitingOffers_subset_fixedAlphabet hSource.2.2.2
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hRight hNonFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.alphabet] at hAction ⊢
      change action ∈
        (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface).actions
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
        Finset.mem_union]
      refine ⟨?_, hAction.2⟩
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hSource.2.2.1 hLeftAction)
      · exact Or.inr (ihRight hSource.2.2.2 hRightAction)
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocal1
      hLocal2 hSide hNotTock ihLeft ihRight =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.alphabet] at hAction ⊢
      change action ∈
        (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface).actions
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
        Finset.mem_union]
      refine ⟨?_, hAction.2⟩
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hSource.2.2.1 hLeftAction)
      · exact Or.inr (ihRight hSource.2.2.2 hRightAction)
  | left_complete _ _ leftT rightT _ _ _ _ _ _ _ _ _ _ _ _ ihRight
  | left_complete_tock _ _ leftT rightT _ _ _ _ _ _ _ _ _ _ _ _ ihRight =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.alphabet] at hAction ⊢
      change action ∈
        (PactTypeAlphabet.mergeHidden leftT.alphabet rightT.alphabet _).actions
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
        Finset.mem_union]
      exact ⟨Or.inr (ihRight hSource.2.2.2 hAction.1), hAction.2⟩
  | right_complete _ _ leftT _ rightT _ _ _ _ _ _ _ _ _ _ _ ihLeft
  | right_complete_tock _ _ leftT _ rightT _ _ _ _ _ _ _ _ _ _ _ ihLeft =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.alphabet] at hAction ⊢
      change action ∈
        (PactTypeAlphabet.mergeHidden leftT.alphabet rightT.alphabet _).actions
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
        Finset.mem_union]
      exact ⟨Or.inl (ihLeft hSource.2.2.1 hAction.1), hAction.2⟩
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      simp only [PactType.AlphabetWellFormed] at hSource
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.alphabet] at hAction ⊢
      change action ∈
        (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface).actions
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
        Finset.mem_union]
      refine ⟨?_, hAction.2⟩
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hSource.2.2.1 hLeftAction)
      · exact Or.inr (ihRight hSource.2.2.2 hRightAction)

theorem typeOffers_future_subset_fixedAlphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource : source.AlphabetWellFormed)
    (hTargetAlphabet : target.alphabet = source.alphabet)
    (hTargetWF : target.AlphabetWellFormed)
    (hOffers : TypeOffers env source label target current future) :
    future ⊆ source.alphabet.actions := by
  intro action hAction
  have hFuture :=
    typeOffers_future_subset_target_union_current hOffers hAction
  rw [Finset.mem_union] at hFuture
  rcases hFuture with hFuture | hCurrent
  · have hSubset := typeFutureOffers_subset_fixedAlphabet target hTargetWF
    simpa [hTargetAlphabet] using hSubset hFuture
  · exact typeOffers_current_subset_fixedAlphabet hSource hOffers hCurrent

private theorem typeFutureOffers_branchFold_subset_branchPrefixMessageIds
    (branches : List (BareMessage × PactType))
    (ihBranches : ∀ branch ∈ branches, ∀ action : BareMessage,
      action ∈ typeFutureOffers branch.2 → action.1 ∈ PactType.PrefixMessageIds branch.2) :
    ∀ (rest : List (BareMessage × PactType)) initial action,
      (∀ branch ∈ rest, branch ∈ branches) →
      action ∈ rest.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) initial →
      action ∈ initial ∨
        action.1 ∈ PactType.BranchPrefixMessageIds rest := by
  intro rest
  induction rest with
  | nil =>
      intro initial action _ hMem
      exact Or.inl (by simpa using hMem)
  | cons branch tail tailIH =>
      rcases branch with ⟨bAction, bType⟩
      intro initial action hSubset hMem
      have hTail := tailIH (initial ∪ {bAction} ∪ typeFutureOffers bType) action
        (fun other hOther => hSubset other (by simp [hOther])) hMem
      rcases hTail with hInitialOrHead | hRest
      · simp only [Finset.mem_union, Finset.mem_singleton] at hInitialOrHead
        rcases hInitialOrHead with (hInitial | hHead) | hFuture
        · exact Or.inl hInitial
        · refine Or.inr ?_
          simp only [PactType.BranchPrefixMessageIds]
          rw [Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (Or.inl (congrArg Prod.fst hHead))
        · refine Or.inr ?_
          simp only [PactType.BranchPrefixMessageIds]
          rw [Finset.mem_union, Finset.mem_union]
          exact Or.inl (Or.inr (ihBranches (bAction, bType)
            (hSubset (bAction, bType) (by simp)) action hFuture))
      · refine Or.inr ?_
        simp only [PactType.BranchPrefixMessageIds]
        rw [Finset.mem_union, Finset.mem_union]
        exact Or.inr hRest

/-- Every syntactic future offer's bare message id was already reachable
before the next clock, per `PrefixMessageIds`. -/
theorem typeFutureOffers_subset_prefixMessageIds :
    ∀ processType : PactType, ∀ action : BareMessage,
      action ∈ typeFutureOffers processType →
      action.1 ∈ PactType.PrefixMessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      subst hSize
      cases processType with
      | message alphabet msg dir =>
          intro action hAction
          simp only [typeFutureOffers, typeFutureOffersFuel, Finset.mem_singleton] at hAction
          simp [PactType.PrefixMessageIds, hAction]
      | progress alphabet pid =>
          intro action hAction
          simp [typeFutureOffers, typeFutureOffersFuel] at hAction
      | tock alphabet =>
          intro action hAction
          simp [typeFutureOffers, typeFutureOffersFuel] at hAction
      | skip alphabet =>
          intro action hAction
          simp [typeFutureOffers, typeFutureOffersFuel] at hAction
      | var alphabet name =>
          intro action hAction
          simp [typeFutureOffers, typeFutureOffersFuel] at hAction
      | recur alphabet name body =>
          intro action hAction
          rw [typeFutureOffers_recur] at hAction
          have hBodySize : sizeOf body < sizeOf (PactType.recur alphabet name body) := by
            simp_wf; omega
          simpa [PactType.PrefixMessageIds] using
            ih (sizeOf body) hBodySize body rfl action hAction
      | choice alphabet left right =>
          intro action hAction
          rw [typeFutureOffers_choice, Finset.mem_union] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hLeftSize : sizeOf left < sizeOf (PactType.choice alphabet left right) := by
            simp_wf; omega
          have hRightSize : sizeOf right < sizeOf (PactType.choice alphabet left right) := by
            simp_wf; omega
          rcases hAction with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left rfl action hLeft)
          · exact Or.inr (ih (sizeOf right) hRightSize right rfl action hRight)
      | fairChoice alphabet bid left right =>
          intro action hAction
          rw [typeFutureOffers_fairChoice, Finset.mem_union] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hLeftSize : sizeOf left <
              sizeOf (PactType.fairChoice alphabet bid left right) := by
            simp_wf; omega
          have hRightSize : sizeOf right <
              sizeOf (PactType.fairChoice alphabet bid left right) := by
            simp_wf; omega
          rcases hAction with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left rfl action hLeft)
          · exact Or.inr (ih (sizeOf right) hRightSize right rfl action hRight)
      | seq alphabet left right =>
          intro action hAction
          rw [typeFutureOffers_sequence] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hLeftSize : sizeOf left < sizeOf (PactType.seq alphabet left right) := by
            simp_wf; omega
          have hRightSize : sizeOf right < sizeOf (PactType.seq alphabet left right) := by
            simp_wf; omega
          by_cases hComplete : left.CanCompleteBeforeTock
          · rw [if_pos hComplete] at hAction
            rw [if_pos hComplete]
            rcases Finset.mem_union.mp hAction with hLeft | hRight
            · exact Or.inl (ih (sizeOf left) hLeftSize left rfl action hLeft)
            · exact Or.inr (ih (sizeOf right) hRightSize right rfl action hRight)
          · rw [if_neg hComplete] at hAction
            exact Or.inl (ih (sizeOf left) hLeftSize left rfl action hAction)
      | par alphabet left right interface =>
          intro action hAction
          rw [typeFutureOffers_parallel] at hAction
          simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hLeftSize : sizeOf left <
              sizeOf (PactType.par alphabet left right interface) := by
            simp_wf; omega
          have hRightSize : sizeOf right <
              sizeOf (PactType.par alphabet left right interface) := by
            simp_wf; omega
          rcases hAction.1 with hLeft | hRight
          · exact Or.inl (ih (sizeOf left) hLeftSize left rfl action hLeft)
          · exact Or.inr (ih (sizeOf right) hRightSize right rfl action hRight)
      | xoffer alphabet elseType branches =>
          intro action hAction
          rw [typeFutureOffers_xoffer] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hElseSize : sizeOf elseType <
              sizeOf (PactType.xoffer alphabet elseType branches) := by
            simp_wf; omega
          have hBranchSize : ∀ branch ∈ branches,
              sizeOf branch.2 < sizeOf (PactType.xoffer alphabet elseType branches) := by
            intro branch hBranch
            have hPairSize := List.sizeOf_lt_of_mem hBranch
            have hComponentSize : sizeOf branch.2 < sizeOf branch := by
              rcases branch; simp_wf; omega
            have hListSize : sizeOf branches <
                sizeOf (PactType.xoffer alphabet elseType branches) := by
              simp_wf; omega
            omega
          have hResult := typeFutureOffers_branchFold_subset_branchPrefixMessageIds
            branches
            (fun branch hBranch action' hAction' =>
              ih (sizeOf branch.2) (hBranchSize branch hBranch) branch.2 rfl action' hAction')
            branches (typeFutureOffers elseType) action (fun _ h => h) hAction
          rcases hResult with hElse | hBranches
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType rfl action hElse)
          · exact Or.inr hBranches
      | offer alphabet elseType branches =>
          intro action hAction
          rw [typeFutureOffers_offer] at hAction
          simp only [PactType.PrefixMessageIds, Finset.mem_union]
          have hElseSize : sizeOf elseType <
              sizeOf (PactType.offer alphabet elseType branches) := by
            simp_wf; omega
          have hBranchSize : ∀ branch ∈ branches,
              sizeOf branch.2 < sizeOf (PactType.offer alphabet elseType branches) := by
            intro branch hBranch
            have hPairSize := List.sizeOf_lt_of_mem hBranch
            have hComponentSize : sizeOf branch.2 < sizeOf branch := by
              rcases branch; simp_wf; omega
            have hListSize : sizeOf branches <
                sizeOf (PactType.offer alphabet elseType branches) := by
              simp_wf; omega
            omega
          have hResult := typeFutureOffers_branchFold_subset_branchPrefixMessageIds
            branches
            (fun branch hBranch action' hAction' =>
              ih (sizeOf branch.2) (hBranchSize branch hBranch) branch.2 rfl action' hAction')
            branches (typeFutureOffers elseType) action (fun _ h => h) hAction
          rcases hResult with hElse | hBranches
          · exact Or.inl (ih (sizeOf elseType) hElseSize elseType rfl action hElse)
          · exact Or.inr hBranches

/-- A branch's own head action never recurs among its own continuation's
same-cycle future offers, for a regular (`SameCycleMessageLinear`) offer
list. -/
private theorem sameCycleMessageLinearBranches_head_notMem_of_mem
    {branches : List (BareMessage × PactType)}
    (hBranches : PactType.SameCycleMessageLinearBranches branches)
    {action : BareMessage} {processType : PactType}
    (hMem : (action, processType) ∈ branches) :
    action.1 ∉ PactType.PrefixMessageIds processType := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [PactType.SameCycleMessageLinearBranches] at hBranches
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        exact hBranches.2.1
      · exact ih hBranches.2.2 hMem

/-- Under `SameCycleMessageLinear`, no conjunctive/exclusive-offer branch head
recurs among the else type's own same-cycle future offers. -/
private theorem sameCycleMessageLinear_branchHead_notMem_elseFuture
    {elseType : PactType} {branches : List (BareMessage × PactType)}
    (hSafe : ∀ branch ∈ branches, branch.1.1 ∉ PactType.PrefixMessageIds elseType)
    {action : BareMessage} {processType : PactType}
    (hMem : (action, processType) ∈ branches)
    {future : BareMessage} (hFuture : future ∈ typeFutureOffers elseType) :
    future ≠ action := by
  intro heq
  exact hSafe (action, processType) hMem
    (heq ▸ typeFutureOffers_subset_prefixMessageIds elseType future hFuture)

private theorem alphabet_wellFormed_of_type
    {processType : PactType} (hWF : processType.AlphabetWellFormed) :
    processType.alphabet.WellFormed := by
  cases processType <;> simp [PactType.AlphabetWellFormed, PactType.alphabet] at hWF ⊢
  all_goals tauto

private theorem typeNeed_injective : Function.Injective typeNeed := by
  intro left right hEq
  rcases left with ⟨leftMsg, leftDir⟩
  rcases right with ⟨rightMsg, rightDir⟩
  cases leftDir <;> cases rightDir <;>
    simp [typeNeed, MessageDir.invert] at hEq ⊢
  all_goals exact hEq

private theorem typeNeed_typeNeed (action : BareMessage) :
    typeNeed (typeNeed action) = action := by
  rcases action with ⟨msg, dir⟩
  cases dir <;> simp [typeNeed, MessageDir.invert]

private theorem typeNeed_mem_left_of_right_interface
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hLeftWF : left.WellFormed) (hRightWF : right.WellFormed)
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface)
    {action : BareMessage}
    (hAction : action ∈ right.actions) (hInterface : action.1 ∈ interface) :
    typeNeed action ∈ left.actions := by
  rcases action with ⟨msg, dir⟩
  have hComp := hCompatible.complementary msg hInterface
  cases dir
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact False.elim (hRightWF msg ⟨hAction, hSendRecv.2⟩)
    · exact hRecvSend.1
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact hSendRecv.1
    · exact False.elim (hRightWF msg ⟨hRecvSend.2, hAction⟩)

private theorem typeNeed_mem_right_of_left_interface
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hLeftWF : left.WellFormed) (hRightWF : right.WellFormed)
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right interface)
    {action : BareMessage}
    (hAction : action ∈ left.actions) (hInterface : action.1 ∈ interface) :
    typeNeed action ∈ right.actions := by
  rcases action with ⟨msg, dir⟩
  have hComp := hCompatible.complementary msg hInterface
  cases dir
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact hSendRecv.2
    · exact False.elim (hLeftWF msg ⟨hAction, hRecvSend.1⟩)
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact False.elim (hLeftWF msg ⟨hSendRecv.1, hAction⟩)
    · exact hRecvSend.2

private theorem projected_environment_action_mem_for
    (signature : TypeAlphabet)
    {parent localAlphabet : PactTypeAlphabet} {action : BareMessage}
    (hOuter :
      action ∈ signature.localEnvironmentActionsFor parent)
    (hProjected : action ∈ localAlphabet.actions.image typeNeed) :
    action ∈ signature.localEnvironmentActionsFor localAlphabet := by
  simp only [TypeAlphabet.localEnvironmentActionsFor,
    TypeAlphabet.localActionsFor, Finset.mem_image, Finset.mem_inter]
    at hOuter hProjected ⊢
  rcases hOuter with ⟨outerAction, hOuterAction, hOuterEq⟩
  rcases hProjected with ⟨localAction, hLocalAction, hLocalEq⟩
  have hSameNeed : typeNeed localAction = typeNeed outerAction := by
    rw [hLocalEq, hOuterEq]
  have hActionEq : localAction = outerAction :=
    typeNeed_injective hSameNeed
  subst outerAction
  exact ⟨localAction, ⟨hOuterAction.1, hLocalAction⟩, hLocalEq⟩

private theorem interface_offer_mem_localEnvironmentActionsFor
    (signature : TypeAlphabet) {interface : Interface}
    {localAlphabet sibling : PactTypeAlphabet} {action : BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hSiblingAction : action ∈ signature.localActionsFor sibling)
    (hActionInterface : action.1 ∈ interface)
    (hNeed : typeNeed action ∈ localAlphabet.actions) :
    action ∈ signature.localEnvironmentActionsFor localAlphabet := by
  simp only [TypeAlphabet.localEnvironmentActionsFor,
    TypeAlphabet.localActionsFor, Finset.mem_image, Finset.mem_inter] at hSiblingAction ⊢
  refine ⟨typeNeed action, ⟨?_, hNeed⟩, ?_⟩
  · exact interface_action_mem_localActions signature hInterface (by
      rcases action with ⟨msg, dir⟩
      simpa [typeNeed] using hActionInterface)
  · rw [typeNeed_typeNeed]

private theorem localEnvironmentFor_mem_of_localTypeOfferEnvironment
    (signature : TypeAlphabet) {parentAlphabet siblingAlphabet : PactTypeAlphabet}
    {outer localEnv siblingEnv : TypeEnvironment}
    {interface : Interface} {localType : PactType}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironmentsFor parentAlphabet)
    (hCurrent : current ⊆ signature.localActionsFor siblingAlphabet)
    (hFuture : future ⊆ signature.localActionsFor siblingAlphabet)
    (hNeed : ∀ action,
      action ∈ siblingAlphabet.actions → action.1 ∈ interface →
        typeNeed action ∈ localType.alphabet.actions)
    (hLocal :
      LocalTypeOfferEnvironment outer interface localType siblingEnv current
        future localEnv) :
    localEnv ∈ signature.localEnvironmentsFor localType.alphabet := by
  cases hLocal with
  | clock outer interface localType current hClock =>
      simp [TypeAlphabet.localEnvironmentsFor, TypeEnvironment.tock]
  | ordinary outer siblingEnv localEnv interface localType current
      hOuterClock hSiblingClock hLocalClock hImmediate hFutureEq =>
      simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter ⊢
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuterEq⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        rcases localEnv with ⟨localImmediate, localFuture, localClock⟩
        simp only at hLocalClock hImmediate hFutureEq
        subst localClock
        right
        refine ⟨localImmediate, ?_, localFuture, ?_, rfl⟩
        · intro action hAction
          rw [hImmediate] at hAction
          simp only [Finset.mem_union, restrictTypeOffers,
            projectTypeEnvironmentOffers, Finset.mem_filter] at hAction
          rcases hAction with ⟨hOuterAction, hProjected⟩ |
              ⟨hCurrentAction, hInterfaceAction⟩
          · exact projected_environment_action_mem_for signature
              (hOuterImmediate hOuterAction) hProjected
          · exact interface_offer_mem_localEnvironmentActionsFor signature
              hInterface (hCurrent hCurrentAction) hInterfaceAction
              (hNeed action
                ((Finset.mem_inter.mp (hCurrent hCurrentAction)).2)
                hInterfaceAction)
        · intro action hAction
          rw [hFutureEq] at hAction
          simp only [Finset.mem_sdiff, Finset.mem_union, restrictTypeOffers,
            projectTypeEnvironmentOffers, Finset.mem_filter] at hAction ⊢
          rcases hAction.1 with ⟨hOuterAction, hProjected⟩ |
              ⟨hFutureAction, hInterfaceAction⟩
          · exact ⟨projected_environment_action_mem_for signature
              (Finset.mem_sdiff.mp (hOuterFuture hOuterAction)).1 hProjected,
              hAction.2⟩
          · exact ⟨interface_offer_mem_localEnvironmentActionsFor signature
              hInterface (hFuture hFutureAction) hInterfaceAction
              (hNeed action
                ((Finset.mem_inter.mp (hFuture hFutureAction)).2)
                hInterfaceAction), hAction.2⟩

private theorem localEnvironment_mem_of_localTypeOfferEnvironment
    (signature : TypeAlphabet) {outer localEnv siblingEnv : TypeEnvironment}
    {interface : Interface} {localType : PactType}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hLocal :
      LocalTypeOfferEnvironment outer interface localType siblingEnv current
        future localEnv) :
    localEnv ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface localType current hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnv localEnv interface localType current
      hOuterClock hSiblingClock hLocalClock
      hImmediate hFuture =>
      simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hOuter ⊢
      rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
        outerFuture, hOuterFuture, hOuterEq⟩
      · subst outer
        simp [TypeEnvironment.tock] at hOuterClock
      · subst outer
        rcases localEnv with ⟨localImmediate, localFuture, localClock⟩
        simp only at hLocalClock hImmediate hFuture
        subst localClock
        right
        refine ⟨localImmediate, ?_, localFuture, ?_, rfl⟩
        · intro action hAction
          rw [hImmediate] at hAction
          simp only [Finset.mem_union, restrictTypeOffers,
            projectTypeEnvironmentOffers,
            Finset.mem_filter] at hAction
          rcases hAction with ⟨hOuterAction, _⟩ | ⟨_, hInterfaceAction⟩
          · exact hOuterImmediate hOuterAction
          · exact interface_action_mem_localEnvironmentActions signature
              hInterface hInterfaceAction
        · intro action hAction
          rw [hFuture] at hAction
          simp only [Finset.mem_sdiff, Finset.mem_union, restrictTypeOffers,
            projectTypeEnvironmentOffers, Finset.mem_filter] at hAction ⊢
          rcases hAction.1 with ⟨hOuterAction, _⟩ | ⟨_, hInterfaceAction⟩
          · exact ⟨(Finset.mem_sdiff.mp (hOuterFuture hOuterAction)).1,
              hAction.2⟩
          · exact ⟨interface_action_mem_localEnvironmentActions signature
              hInterface hInterfaceAction, hAction.2⟩

private theorem componentOffers_mem_localOfferSummaries
    (signature : TypeAlphabet) {interface : Interface}
    (hInterface : interface ⊆ signature.interface)
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hParent :
      TypeOfferSummary.mk
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (hideTypeOffers interface (leftFuture ∪ rightFuture)) ∈
          signature.localOfferSummaries) :
    TypeOfferSummary.mk leftCurrent leftFuture ∈
        signature.localOfferSummaries ∧
      TypeOfferSummary.mk rightCurrent rightFuture ∈
        signature.localOfferSummaries := by
  rw [localOfferSummaries_mk_mem_iff] at hParent
  have liftComponent : ∀ {component sibling : Finset BareMessage},
      hideTypeOffers interface (component ∪ sibling) ⊆
          signature.localActions →
      component ⊆ signature.localActions := by
    intro component sibling hHidden action hAction
    by_cases hInternal : action.1 ∈ interface
    · exact interface_action_mem_localActions signature hInterface hInternal
    · apply hHidden
      simp [hideTypeOffers, hAction, hInternal]
  constructor
  · rw [localOfferSummaries_mk_mem_iff]
    exact ⟨liftComponent hParent.1, liftComponent hParent.2⟩
  · rw [localOfferSummaries_mk_mem_iff]
    exact ⟨
      liftComponent (component := rightCurrent) (sibling := leftCurrent)
        (by simpa [Finset.union_comm] using hParent.1),
      liftComponent (component := rightFuture) (sibling := leftFuture)
        (by simpa [Finset.union_comm] using hParent.2)⟩

private theorem componentOffers_mem_localOfferSummariesFor
    (signature : TypeAlphabet) {interface : Interface}
    {left right : PactType}
    (hInterface : interface ⊆ signature.interface)
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hLeftCurrent : leftCurrent ⊆ left.alphabet.actions)
    (hLeftFuture : leftFuture ⊆ left.alphabet.actions)
    (hRightCurrent : rightCurrent ⊆ right.alphabet.actions)
    (hRightFuture : rightFuture ⊆ right.alphabet.actions)
    (hParent :
      TypeOfferSummary.mk
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (hideTypeOffers interface (leftFuture ∪ rightFuture)) ∈
          signature.localOfferSummaries) :
    TypeOfferSummary.mk leftCurrent leftFuture ∈
        signature.localOfferSummariesFor left.alphabet ∧
      TypeOfferSummary.mk rightCurrent rightFuture ∈
        signature.localOfferSummariesFor right.alphabet := by
  obtain ⟨hUnrestrictedLeft, hUnrestrictedRight⟩ :=
    componentOffers_mem_localOfferSummaries signature hInterface hParent
  rw [localOfferSummaries_mk_mem_iff] at hUnrestrictedLeft hUnrestrictedRight
  refine ⟨?_, ?_⟩
  · rw [localOfferSummariesFor_mk_mem_iff]
    exact ⟨Finset.subset_inter hUnrestrictedLeft.1 hLeftCurrent,
      Finset.subset_inter hUnrestrictedLeft.2 hLeftFuture⟩
  · rw [localOfferSummariesFor_mk_mem_iff]
    exact ⟨Finset.subset_inter hUnrestrictedRight.1 hRightCurrent,
      Finset.subset_inter hUnrestrictedRight.2 hRightFuture⟩

private theorem componentLabels_mem_localLabels
    (signature : TypeAlphabet) {interface : Interface}
    (hInterface : interface ⊆ signature.interface)
    {leftLabel rightLabel label : TypeLabel}
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
    (hParent : label ∈ signature.localLabels) :
    leftLabel ∈ signature.localLabels ∧
      rightLabel ∈ signature.localLabels := by
  subst label
  cases leftLabel with
  | tock =>
      cases rightLabel with
      | tock => simp [TypeAlphabet.localLabels]
      | actions observations =>
          simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
  | actions leftObservations =>
      cases rightLabel with
      | tock =>
          simp [TypeLabel.Sync, TypeLabel.isTock] at hSync
      | actions rightObservations =>
          simp only [TypeAlphabet.localLabels, Finset.mem_union,
            Finset.mem_image, Finset.mem_singleton] at hParent ⊢
          rcases hParent with ⟨parentObservations, hParentSubset, hParentEq⟩ | hImpossible
          · injection hParentEq with hCombinedEq
            have hParentSubset' : parentObservations ⊆
                signature.localObservations :=
              Finset.mem_powerset.mp hParentSubset
            have componentSubset : ∀ {component : Finset TypeObservation},
                component ⊆ leftObservations ∪ rightObservations →
                component ⊆ signature.localObservations := by
              intro component hComponent observation hObservation
              by_cases hHidden : TypeLabel.isRawSyncedMessage
                  (TypeLabel.synced interface (.actions leftObservations)
                    (.actions rightObservations)) observation
              · cases observation with
                | message msg dir =>
                    have hSynced : msg ∈ TypeLabel.synced interface
                        (.actions leftObservations) (.actions rightObservations) := by
                      simpa [TypeLabel.isRawSyncedMessage] using hHidden
                    have hMsg : msg ∈ interface := by
                      rcases Finset.mem_union.mp hSynced with hLeft | hRight
                      · exact (Finset.mem_inter.mp hLeft).1
                      · exact (Finset.mem_inter.mp hRight).1
                    have hAction : (msg, dir) ∈ signature.localActions :=
                      interface_action_mem_localActions signature hInterface hMsg
                    simp only [TypeAlphabet.localObservations, Finset.mem_union,
                      Finset.mem_image]
                    exact Or.inl (Or.inl (Or.inl ⟨(msg, dir), hAction, rfl⟩))
                | resolved msg => simp [TypeLabel.isRawSyncedMessage] at hHidden
                | fair bid taken => simp [TypeLabel.isRawSyncedMessage] at hHidden
                | progress pid => simp [TypeLabel.isRawSyncedMessage] at hHidden
              · apply hParentSubset'
                rw [hCombinedEq]
                simp [TypeLabel.combine, hComponent hObservation, hHidden]
            exact ⟨
              Or.inl ⟨leftObservations,
                Finset.mem_powerset.mpr
                  (componentSubset (component := leftObservations)
                    Finset.subset_union_left), rfl⟩,
              Or.inl ⟨rightObservations,
                Finset.mem_powerset.mpr
                  (componentSubset (component := rightObservations)
                    Finset.subset_union_right), rfl⟩⟩
          · simp [TypeLabel.combine] at hImpossible

/-- `LocalTypeOfferEnvironment` only depends on `localType` through its
alphabet, so it transports along any alphabet-preserving substitution of the
local type (e.g. a residual `residualLeft` reached from `left` by steps). -/
theorem LocalTypeOfferEnvironment.congrLocalType
    {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
    {localType localType' : PactType} {current future : Finset BareMessage}
    (hAlphabet : localType'.alphabet = localType.alphabet)
    (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
      current future localEnv) :
    LocalTypeOfferEnvironment outer interface localType' siblingEnv
      current future localEnv := by
  cases hLocal with
  | clock _ =>
      rename_i hClock
      exact LocalTypeOfferEnvironment.clock outer interface localType' current
        future hClock
  | ordinary _ _ _ _ _ =>
      rename_i hOuterClock hSiblingClock hLocalClock hImmediate hFuture
      exact LocalTypeOfferEnvironment.ordinary outer siblingEnv localEnv
        interface localType' current future hOuterClock hSiblingClock
        hLocalClock (hAlphabet ▸ hImmediate) (hAlphabet ▸ hFuture)

/-- Each component symbol of a parallel step belongs to that component's own
fixed-alphabet transition alphabet.  The enclosing product may hide interface
actions, but those actions remain declared local actions while either child
is compiled, and the offer/environment contents stay within each child's own
declared alphabet. -/
theorem transitionAlphabet_of_par_component
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {leftEnv rightEnv : TypeEnvironment} {leftLabel rightLabel : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    {env : TypeEnvironment} {label : TypeLabel}
    (hWF : env.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hLeftWellFormed : left.AlphabetWellFormed)
    (hRightWellFormed : right.AlphabetWellFormed)
    (hParallelCompatible :
      PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
        right.alphabet interface)
    (hLeftCurrent : leftCurrent ⊆ left.alphabet.actions)
    (hLeftFuture : leftFuture ⊆ left.alphabet.actions)
    (hRightCurrent : rightCurrent ⊆ right.alphabet.actions)
    (hRightFuture : rightFuture ⊆ right.alphabet.actions)
    (hLocal1 :
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv)
    (hLocal2 :
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
    (hSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))) ∈
        signature.transitionAlphabetFor alphabet) :
    TypeAutomatonSymbol.mk leftEnv leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) ∈
      signature.transitionAlphabetFor left.alphabet ∧
    TypeAutomatonSymbol.mk rightEnv rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) ∈
      signature.transitionAlphabetFor right.alphabet := by
  rw [transitionAlphabetFor_mk_mem_iff] at hSymbol
  obtain ⟨hEnv, hParentLabel, hParentOffers⟩ := hSymbol
  have hLeftWF := alphabet_wellFormed_of_type hLeftWellFormed
  have hRightWF := alphabet_wellFormed_of_type hRightWellFormed
  have hParentOffersUnrestricted :
      TypeOfferSummary.mk
        (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
        (hideTypeOffers interface (leftFuture ∪ rightFuture)) ∈
          signature.localOfferSummaries := by
    rw [localOfferSummariesFor_mk_mem_iff] at hParentOffers
    rw [localOfferSummaries_mk_mem_iff]
    exact ⟨hParentOffers.1.trans (TypeAlphabet.localActionsFor_subset_localActions signature
        alphabet),
      hParentOffers.2.trans (TypeAlphabet.localActionsFor_subset_localActions signature
        alphabet)⟩
  obtain ⟨hUnrestrictedLeft, hUnrestrictedRight⟩ :=
    componentOffers_mem_localOfferSummaries signature hInterface
      hParentOffersUnrestricted
  rw [localOfferSummaries_mk_mem_iff] at hUnrestrictedLeft hUnrestrictedRight
  have hLeftEnv := localEnvironmentFor_mem_of_localTypeOfferEnvironment signature
    (parentAlphabet := alphabet) (siblingAlphabet := right.alphabet)
    hInterface hEnv
    (Finset.subset_inter hUnrestrictedRight.1 hRightCurrent)
    (Finset.subset_inter hUnrestrictedRight.2 hRightFuture)
    (fun action hAction hInterfaceAction =>
      typeNeed_mem_left_of_right_interface hLeftWF hRightWF
        hParallelCompatible hAction hInterfaceAction)
    hLocal1
  have hRightEnv := localEnvironmentFor_mem_of_localTypeOfferEnvironment signature
    (parentAlphabet := alphabet) (siblingAlphabet := left.alphabet)
    hInterface hEnv
    (Finset.subset_inter hUnrestrictedLeft.1 hLeftCurrent)
    (Finset.subset_inter hUnrestrictedLeft.2 hLeftFuture)
    (fun action hAction hInterfaceAction =>
      typeNeed_mem_right_of_left_interface hLeftWF hRightWF
        hParallelCompatible hAction hInterfaceAction)
    hLocal2
  have hLabels := componentLabels_mem_localLabels signature hInterface hSync
    hLabelEq hParentLabel
  have hOffers := componentOffers_mem_localOfferSummariesFor signature
    hInterface hLeftCurrent hLeftFuture hRightCurrent hRightFuture
    hParentOffersUnrestricted
  constructor
  · rw [transitionAlphabetFor_mk_mem_iff]
    exact ⟨hLeftEnv, hLabels.1, hOffers.1⟩
  · rw [transitionAlphabetFor_mk_mem_iff]
    exact ⟨hRightEnv, hLabels.2, hOffers.2⟩

/-- Lift a pair of child relation states into the product relation. -/
lemma relationMembership_par_pair
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {leftResidual rightResidual : PactType}
    {leftState rightState : TypeAutomatonState}
    (hLeft : relationMembership
      (buildRelationSet left (compileType signature left))
      leftResidual leftState)
    (hRight : relationMembership
      (buildRelationSet right (compileType signature right))
      rightResidual rightState)
    (hReachable : ParallelReachable signature alphabet left.alphabet
      right.alphabet interface
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      (computeFutureOf signature left)
      (computeFutureOf signature right)
      (.pair leftState rightState)) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface)))
      (.par alphabet leftResidual rightResidual interface)
      (.pair leftState rightState) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.par alphabet leftResidual rightResidual interface : PactType),
      .pair leftState rightState) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨((leftResidual, leftState), (rightResidual, rightState)), ?_, rfl⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · rw [buildRelationSetCoreFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl]
      exact hLeft
    · rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
      exact hRight
  · change ParallelReachable signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (.pair leftState rightState)
    rw [compileTypeFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
    simpa [compiledChildFutureFuel, computeFutureOf,
      Nat.min_eq_right (le_max_left _ _),
      Nat.min_eq_right (le_max_right _ _)] using hReachable

/-- The dedicated completed state of a parallel product represents `skip`. -/
lemma relationMembership_par_final
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface)))
      (.skip alphabet) .final := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.skip alphabet : PactType), .final) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp [buildRelationSetCoreFuel]

/-- Every accepting state of a compiled fragment is related to `skip` — the
converse direction of H13's characterization. Needed when a `.par` redirect
edge's target is already pinned (by the compiler's own construction) to a
pair of accepting states, without any pre-existing `relationMembership`
witness at that specific pair to read H13 off of directly.

High-level proof idea:

Proceed by structural induction on `processType`, following the construction
of `compileType` and `buildRelationSet`.

For each constructor, inspect how accepting states are formed.

In the atomic cases, the accepting `.final` state is explicitly related to
`skip` by the relation construction.

For constructors built from child automata (choice, fair choice, offers, and
recursion), an accepting state comes from an accepting state of an appropriate
child. Apply the induction hypothesis to obtain that the child state is related
to `skip`, then use the corresponding embedding clause of `buildRelationSet`
to lift this relation membership to the parent.

For sequencing, accepting states come from the right-hand automaton, so apply
the induction hypothesis to the right child and lift its relation membership.

For parallel composition, the compiler introduces the dedicated `.final`
(`q_done`) accepting state, and `buildRelationSet` explicitly contains
`(skip, .final)`.

Thus every accepting state introduced by the compiler is related to `skip`.

-/
theorem relationMembership_of_accepting
    (signature : TypeAlphabet) (processType : PactType) {state : TypeAutomatonState}
    (hAccept : state ∈ (compileType signature processType).accepting) :
    ∃ skipAlphabet,
      relationMembership
        (buildRelationSet processType (compileType signature processType))
        (.skip skipAlphabet) state := by
  induction hSize : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType state with
  | _ n ih =>
    cases processType with
    | skip alphabet =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.skip alphabet)) (.skip alphabet)
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.skip alphabet))
              (.skip alphabet)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | message alphabet msg dir =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.message alphabet msg dir))
            (.message alphabet msg dir)
        have hAccept' : state ∈
            (compileTypeFuel signature
              (typeCompilationFuel (.message alphabet msg dir))
              (.message alphabet msg dir)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | tock alphabet =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.tock alphabet)) (.tock alphabet)
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.tock alphabet))
              (.tock alphabet)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | progress alphabet pid =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.progress alphabet pid))
            (.progress alphabet pid)
        have hAccept' : state ∈
            (compileTypeFuel signature
              (typeCompilationFuel (.progress alphabet pid))
              (.progress alphabet pid)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | var alphabet name =>
        exfalso
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.var alphabet name))
              (.var alphabet name)).accepting := hAccept
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment] at hAccept'
    | choice alphabet left right =>
        have hLeftSize : typeCompilationFuel left < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType signature (.choice alphabet left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.choice alphabet left right))
            (.choice alphabet left right)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildChoiceAutomaton signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_union, Finset.mem_image] at hAccept
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel left) hLeftSize left hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl]
          exact hRelated
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel right) hRightSize right hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inr
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
            (le_max_right _ _) le_rfl]
          exact hRelated
    | fairChoice alphabet bid left right =>
        have hLeftSize : typeCompilationFuel left < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType signature (.fairChoice alphabet bid left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.fairChoice alphabet bid left right))
            (.fairChoice alphabet bid left right)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildChoiceAutomaton signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_union, Finset.mem_image] at hAccept
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel left) hLeftSize left hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl]
          exact hRelated
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel right) hRightSize right hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inr
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
            (le_max_right _ _) le_rfl]
          exact hRelated
    | seq alphabet left right =>
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType signature (.seq alphabet left right)).accepting =
            childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.seq alphabet left right))
            (.seq alphabet left right)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildSequenceAutomaton signature
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
          simp [buildSequenceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_image] at hAccept
        obtain ⟨q, hq, hEq⟩ := hAccept
        obtain ⟨skipAlphabet, hRelated⟩ :=
          ih (typeCompilationFuel right) hRightSize right hq rfl
        refine ⟨skipAlphabet, ?_⟩
        change ((.skip skipAlphabet, state)) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.seq alphabet left right))
            (.seq alphabet left right)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image]
        refine Or.inr ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩
        rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
          (le_max_right _ _) le_rfl]
        exact hRelated
    | par alphabet left right interface =>
        have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType signature (.par alphabet left right interface)).accepting =
            {TypeAutomatonState.final} := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.par alphabet left right interface))
            (.par alphabet left right interface)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildParallelAutomaton signature alphabet left.alphabet
            right.alphabet interface
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (compiledChildFutureFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compiledChildFutureFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
          simp [buildParallelAutomaton, finishAutomatonFragment]
        rw [hAcceptEq, Finset.mem_singleton] at hAccept
        subst hAccept
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, TypeAutomatonState.final) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.par alphabet left right interface))
            (.par alphabet left right interface)
        rw [hFuelEq]
        simp [buildRelationSetCoreFuel]
    | recur alphabet name body =>
        have hBodySize : typeCompilationFuel body < n := by
          rw [← hSize]
          simp [typeCompilationFuel]
        have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
            typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType signature (.recur alphabet name body)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel body) body) := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.recur alphabet name body))
            (.recur alphabet name body)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildRecursionAutomaton signature name
            (compileTypeFuel signature (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_image] at hAccept
        obtain ⟨q, hq, hEq⟩ := hAccept
        obtain ⟨skipAlphabet, hRelated⟩ :=
          ih (typeCompilationFuel body) hBodySize body hq rfl
        refine ⟨skipAlphabet, ?_⟩
        show (.skip skipAlphabet, state) ∈
          buildRelationSetCoreFuel signature
            (typeCompilationFuel (.recur alphabet name body))
            (.recur alphabet name body)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image]
        refine Or.inr ⟨(.skip skipAlphabet, q), hRelated, ?_⟩
        have hReplace :
            (PactType.skip skipAlphabet).replaceVar name
                (.recur alphabet name body) =
              PactType.skip skipAlphabet := by simp [PactType.replaceVar]
        exact Prod.ext hReplace hEq
    | xoffer alphabet elseType branches =>
        have hElseSize : typeCompilationFuel elseType < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq :
            typeCompilationFuel (.xoffer alphabet elseType branches) =
            max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        let branchAutomata := List.map (fun branch => (branch.1,
          compileTypeFuel signature (typeCompilationFuel branch.2) branch.2)) branches
        have hMapEq :
            List.map (fun branch => (branch.1,
              compileTypeFuel signature (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches = branchAutomata := by
          dsimp [branchAutomata]
          apply List.map_congr_left
          intro branch hMem
          have hLeBranch : typeCompilationFuel branch.2 ≤ typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
          rw [compileTypeFuel_eq_of_sufficient signature branch.2
            (le_trans hLeBranch (le_max_right _ _)) le_rfl]
        have hAcceptEq :
            (compileType signature (.xoffer alphabet elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting branchAutomata := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.xoffer alphabet elseType branches))
            (.xoffer alphabet elseType branches)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildExclusiveOfferAutomaton signature alphabet branches
            (compileTypeFuel signature (max (typeCompilationFuel elseType)
              (typeBranchCompilationFuel branches)) elseType)
            (List.map (fun branch => (branch.1,
              compileTypeFuel signature (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature elseType (le_max_left _ _) le_rfl]
          rw [hMapEq]
          simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, branchAutomata]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, indexedFragmentAccepting, Finset.mem_union,
          Finset.mem_image] at hAccept
        rcases hAccept with hElse | hBranch
        · rcases hElse with ⟨q, hq, hEq⟩
          obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel elseType) hElseSize elseType hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.xoffer alphabet elseType branches))
              (.xoffer alphabet elseType branches)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature elseType
            (le_max_left _ _) le_rfl]
          exact hRelated
        · rw [mem_foldl_union_iff] at hBranch
          rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hStateMem⟩
          · simp at hEmpty
          · rcases indexed with ⟨branchAutomaton, index⟩
            rcases branchAutomaton with ⟨action, automaton⟩
            rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexedMem
            rw [branches_map_getElem?_eq_some_iff signature branches index action automaton]
              at hIndexedMem
            rcases hIndexedMem with ⟨branchType, hGet, hAutomatonEq⟩
            have hBranchMem : (action, branchType) ∈ branches := by
              exact List.mem_of_getElem? hGet
            have hBranchSize : typeCompilationFuel branchType < n := by
              have hLeBranch : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel branches :=
                typeCompilationFuel_le_typeBranchCompilationFuel branches
                  (action, branchType) hBranchMem
              rw [← hSize]
              simp only [typeCompilationFuel]
              omega
            rw [← hAutomatonEq] at hStateMem
            simp only [Finset.mem_image] at hStateMem
            rcases hStateMem with ⟨q, hq, hEq⟩
            obtain ⟨skipAlphabet, hRelated⟩ :=
              ih (typeCompilationFuel branchType) hBranchSize branchType hq rfl
            refine ⟨skipAlphabet, ?_⟩
            change ((.skip skipAlphabet, state)) ∈
              buildRelationSetCoreFuel signature
                (typeCompilationFuel (.xoffer alphabet elseType branches))
                (.xoffer alphabet elseType branches)
            rw [hFuelEq]
            simp only [buildRelationSetCoreFuel, Finset.mem_insert,
              Finset.mem_union, Finset.mem_image]
            refine Or.inr (Or.inr ?_)
            rw [mem_foldl_union_iff]
            refine Or.inr ⟨((action, branchType), index), ?_, ?_⟩
            · rw [List.mk_mem_zipIdx_iff_getElem?]
              exact hGet
            · simp only [Finset.mem_image]
              refine ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩
              rw [buildRelationSetCoreFuel_eq_of_sufficient signature branchType ?_ le_rfl]
              · exact hRelated
              · have hLeBranch : typeCompilationFuel branchType ≤ typeBranchCompilationFuel branches :=
                  typeCompilationFuel_le_typeBranchCompilationFuel branches (action, branchType) hBranchMem
                exact le_trans hLeBranch (le_max_right _ _)
    | offer alphabet elseType branches =>
        have hElseSize : typeCompilationFuel elseType < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
          simp only [typeCompilationFuel]; omega
        let selectedConjunctions := List.map (fun selected => (selected.1,
          compileTypeFuel signature
            (typeCompilationFuel (parallelTypeBranchesSelecting selected branches))
            (parallelTypeBranchesSelecting selected branches))) branches
        have hMapEq :
            List.map (fun selected => (selected.1,
              compileTypeFuel signature
                (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting selected branches))) branches =
              selectedConjunctions := by
          dsimp [selectedConjunctions]
          apply List.map_congr_left
          intro selected hSelected
          rw [compileTypeFuel_eq_of_sufficient signature
            (parallelTypeBranchesSelecting selected branches) ?_ le_rfl]
          show typeCompilationFuel (parallelTypeBranchesSelecting selected branches) ≤
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _
        have hAcceptEq :
            (compileType signature (.offer alphabet elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel signature
              (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting selectedConjunctions := by
          show (compileTypeFuel signature
            (typeCompilationFuel (.offer alphabet elseType branches))
            (.offer alphabet elseType branches)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildSelectedConjunctiveOfferAutomaton signature alphabet branches
            (compileTypeFuel signature
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
              elseType)
            (List.map (fun selected => (selected.1,
              compileTypeFuel signature
                (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting selected branches))) branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient signature elseType
            (le_max_left _ _) le_rfl, hMapEq]
          simp [buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, selectedConjunctions]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, indexedFragmentAccepting, Finset.mem_union,
          Finset.mem_image] at hAccept
        rcases hAccept with hElse | hSelected
        · rcases hElse with ⟨q, hq, hEq⟩
          obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel elseType) hElseSize elseType hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel signature
              (typeCompilationFuel (.offer alphabet elseType branches))
              (.offer alphabet elseType branches)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature elseType
            (le_max_left _ _) le_rfl]
          exact hRelated
        · rw [mem_foldl_union_iff] at hSelected
          rcases hSelected with hEmpty | ⟨indexed, hIndexedMem, hStateMem⟩
          · simp at hEmpty
          · rcases indexed with ⟨selectedAutomaton, index⟩
            rcases selectedAutomaton with ⟨action, automaton⟩
            rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexedMem
            dsimp [selectedConjunctions] at hIndexedMem
            rw [List.getElem?_map, Option.map_eq_some_iff] at hIndexedMem
            rcases hIndexedMem with
              ⟨⟨branchAction, branchType⟩, hGet, hMappedEq⟩
            simp only [Prod.mk.injEq] at hMappedEq
            rcases hMappedEq with ⟨hActionEq, hAutomatonEq⟩
            subst branchAction
            let selectedType :=
              parallelTypeBranchesSelecting (action, branchType) branches
            have hSelectedSize : typeCompilationFuel selectedType < n := by
              dsimp [selectedType]
              rw [typeCompilationFuel_parallelTypeBranchesSelecting, ← hSize]
              simp only [typeCompilationFuel]
              omega
            rw [← hAutomatonEq] at hStateMem
            simp only [Finset.mem_image] at hStateMem
            rcases hStateMem with ⟨q, hq, hEq⟩
            obtain ⟨skipAlphabet, hRelated⟩ :=
              ih (typeCompilationFuel selectedType) hSelectedSize selectedType
                hq rfl
            refine ⟨skipAlphabet, ?_⟩
            change ((.skip skipAlphabet, state)) ∈
              buildRelationSetCoreFuel signature
                (typeCompilationFuel (.offer alphabet elseType branches))
                (.offer alphabet elseType branches)
            rw [hFuelEq]
            simp only [buildRelationSetCoreFuel, Finset.mem_insert,
              Finset.mem_union, Finset.mem_image]
            refine Or.inr (Or.inr ?_)
            rw [mem_foldl_union_iff]
            refine Or.inr ⟨((action, branchType), index), ?_, ?_⟩
            · rw [List.mk_mem_zipIdx_iff_getElem?]
              exact hGet
            · simp only [Finset.mem_image]
              refine ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩
              rw [buildRelationSetCoreFuel_eq_of_sufficient signature selectedType ?_ le_rfl]
              · exact hRelated
              · show typeCompilationFuel selectedType ≤
                  max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
                dsimp [selectedType]
                rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                exact le_max_right _ _

private def footprintWithinReplacement
    (result original replacement : PactType) : Prop :=
  result.MessageIds ⊆ original.MessageIds ∪ replacement.MessageIds ∧
  result.MessageActions ⊆ original.MessageActions ∪ replacement.MessageActions ∧
  result.ProgressIds ⊆ original.ProgressIds ∪ replacement.ProgressIds ∧
  result.FairChoiceIds ⊆ original.FairChoiceIds ∪ replacement.FairChoiceIds

private def branchFootprintWithinReplacement
    (result original : List (BareMessage × PactType))
    (replacement : PactType) : Prop :=
  PactType.BranchMessageIds result ⊆
      PactType.BranchMessageIds original ∪ replacement.MessageIds ∧
  PactType.BranchMessageActions result ⊆
      PactType.BranchMessageActions original ∪ replacement.MessageActions ∧
  PactType.BranchProgressIds result ⊆
      PactType.BranchProgressIds original ∪ replacement.ProgressIds ∧
  PactType.BranchFairChoiceIds result ⊆
      PactType.BranchFairChoiceIds original ∪ replacement.FairChoiceIds

/-- The compiled fragment and the public automaton share accepting states. -/
theorem compileType_accepting_eq
    (signature : TypeAlphabet) (ty : PactType) :
    (compileTypeFuel signature (typeCompilationFuel ty) ty).accepting
      = (compileType signature ty).accepting := by
  simp [compileType]

/-- A non-accepting right-child state represents the reannotated survivor. -/
theorem survivorRight_relationMembership
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hChild : relationMembership
      (buildRelationSet right (compileType signature right)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel signature
      (typeCompilationFuel right) right).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface)))
      (residual.reannotate alphabet) (.survivor 1 q) := by
  classical
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  show (residual.reannotate alphabet, TypeAutomatonState.survivor 1 q) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter]
  refine Or.inr (Or.inr ⟨(residual, q), ⟨?_, ?_⟩, rfl⟩)
  · show (residual, q) ∈ buildRelationSetCoreFuel signature
      (max (typeCompilationFuel left) (typeCompilationFuel right)) right
    rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
      (le_max_right _ _) le_rfl]
    exact hChild
  · rw [compileTypeFuel_eq_of_sufficient signature right
      (le_max_right _ _) le_rfl]
    exact hNotAcc

/-- A non-accepting left-child state represents the reannotated survivor. -/
theorem survivorLeft_relationMembership
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hChild : relationMembership
      (buildRelationSet left (compileType signature left)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel signature
      (typeCompilationFuel left) left).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface)))
      (residual.reannotate alphabet) (.survivor 0 q) := by
  classical
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  show (residual.reannotate alphabet, TypeAutomatonState.survivor 0 q) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter]
  refine Or.inr (Or.inl (Or.inr ⟨(residual, q), ⟨?_, ?_⟩, rfl⟩))
  · show (residual, q) ∈ buildRelationSetCoreFuel signature
      (max (typeCompilationFuel left) (typeCompilationFuel right)) left
    rw [buildRelationSetCoreFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl]
    exact hChild
  · rw [compileTypeFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl]
    exact hNotAcc


/-- A reachable pair of related child states represents the parallel pair. -/
theorem pair_relationMembership
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residualLeft residualRight : PactType} {q1 q2 : TypeAutomatonState}
    (hLeft : relationMembership
      (buildRelationSet left (compileType signature left)) residualLeft q1)
    (hRight : relationMembership
      (buildRelationSet right (compileType signature right)) residualRight q2)
    (hReach : ParallelReachable signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      (computeFutureOf signature left) (computeFutureOf signature right)
      (.pair q1 q2)) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType signature (.par alphabet left right interface)))
      (.par alphabet residualLeft residualRight interface) (.pair q1 q2) := by
  classical
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  show (PactType.par alphabet residualLeft residualRight interface,
      TypeAutomatonState.pair q1 q2) ∈
    buildRelationSetCoreFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter]
  refine Or.inr (Or.inl (Or.inl ⟨((residualLeft, q1), (residualRight, q2)),
    ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩))
  · rw [buildRelationSetCoreFuel_eq_of_sufficient signature left
      (le_max_left _ _) le_rfl]
    exact hLeft
  · rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
      (le_max_right _ _) le_rfl]
    exact hRight
  · rw [compileTypeFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl,
      compiledChildFutureFuel_eq_computeFutureOf signature _ left
        (le_max_left _ _),
      compiledChildFutureFuel_eq_computeFutureOf signature _ right
        (le_max_right _ _)]
    exact hReach


/-- H15's future agreement at a surviving right-component state. -/
theorem computeFutureOf_survivorRight_related
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hChild : relationMembership
      (buildRelationSet right (compileType signature right)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel signature
      (typeCompilationFuel right) right).accepting) :
    computeFutureOf signature (.par alphabet left right interface)
        (.survivor 1 q) = typeFutureOffers (residual.reannotate alphabet) :=
  helper_h15_future_offers_agree signature
    (survivorRight_relationMembership signature alphabet left right interface
      hChild hNotAcc)

/-- H15's future agreement at a surviving left-component state. -/
theorem computeFutureOf_survivorLeft_related
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hChild : relationMembership
      (buildRelationSet left (compileType signature left)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel signature
      (typeCompilationFuel left) left).accepting) :
    computeFutureOf signature (.par alphabet left right interface)
        (.survivor 0 q) = typeFutureOffers (residual.reannotate alphabet) :=
  helper_h15_future_offers_agree signature
    (survivorLeft_relationMembership signature alphabet left right interface
      hChild hNotAcc)


/-- A lone edge of the surviving right component is a product edge. -/
theorem survivorRight_mem_edges
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 q' : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (childOffers : TypeOfferSummary)
    (hSymbolResolved : TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 1 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed)) ∈
      signature.transitionAlphabetFor alphabet)
    (hReach : ParallelReachable signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      (computeFutureOf signature left) (computeFutureOf signature right)
      (.pair q1 q2))
    (hOffCur : restrictTypeOffers interface childOffers.current = ∅)
    (hOffFut : restrictTypeOffers interface childOffers.future = ∅)
    (hEdge : (compileType signature right).HasEdge q2 env label childOffers q')
    (hQ1Acc : q1 ∈ (compileType signature left).accepting)
    (hQ1St : q1 ∈ (compileTypeFuel signature (typeCompilationFuel left) left).states)
    (hQ'NotAcc : q' ∉ (compileType signature right).accepting)
    (hQ'NotAccFuel : q' ∉ (compileTypeFuel signature
      (typeCompilationFuel right) right).accepting)
    {q2Residual : PactType}
    (hQ2Rel : relationMembership
      (buildRelationSet right (compileType signature right)) q2Residual q2) :
    (compileType signature (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 1 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed))
      (.survivor 1 q') := by
  classical
  have hWhole : compileTypeFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface) =
      buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right) := by
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
    rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
        (le_max_left _ _),
      compiledChildFutureFuel_eq_computeFutureOf signature _ right
        (le_max_right _ _)]
    rfl
  have hSymbol' : TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 1 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed)) ∈
      signature.transitionAlphabetFor
        (PactType.par alphabet left right interface).alphabet := by
    simpa [PactType.alphabet] using hSymbolResolved
  have hAcceptEqLeft :
      (compileTypeFuel signature (typeCompilationFuel left) left).accepting
        = (compileType signature left).accepting := by simp [compileType]
  have hAcceptEqRight :
      (compileTypeFuel signature (typeCompilationFuel right) right).accepting
        = (compileType signature right).accepting := by simp [compileType]
  rw [compileType_hasEdge_iff_resolvedEdge_mem signature
    (.par alphabet left right interface) (.pair q1 q2) (.survivor 1 q') env
    label _ hSymbol']
  rw [hWhole]
  simp only [resolveAutomatonEdgesWith, Finset.mem_image]
  have hSymbolRight := compileType_hasEdge_symbol_mem signature right hEdge
  have hChildMem :=
    (compileType_hasEdge_iff_resolvedEdge_mem signature right q2 q' env label
      childOffers hSymbolRight).mp hEdge
  refine ⟨{ source := .pair q1 q2
            environment := env
            label := .visible label
            current := childOffers.current
            future := parallelFutureSpec (.visible label)
              (.survivor 1 q') childOffers.current
            target := .survivor 1 q' }, ?_, ?_⟩
  · simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    left
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))), hReach⟩
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter]
    refine ⟨q1, ⟨hAcceptEqLeft ▸ hQ1Acc, hQ1St⟩, _,
      ⟨hChildMem, ?_, ?_, hOffCur, hOffFut⟩, rfl⟩
    · simp only [parallelComponentEdgeAllowed]
      exact hSymbolRight
    · exact hAcceptEqRight ▸ hQ'NotAcc
  · simp only [parallelFutureSpec]
    split_ifs with hTock
    · simp only [AutomatonConstructionLabel.semantic] at hTock
      obtain ⟨childResidual, hChildRel⟩ :
          ∃ residual, relationMembership
            (buildRelationSet right (compileType signature right)) residual q' := by
        have hSym := compileType_hasEdge_symbol_mem signature right hEdge
        have hMem :=
          (compileType_hasEdge_iff_resolvedEdge_mem signature right q2 q' env
            label childOffers hSym).mp hEdge
        simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hMem
        obtain ⟨raw, hRawMem, hRawEq⟩ := hMem
        have hRawTarget : raw.target = q' :=
          congrArg AutomatonFragmentEdge.target hRawEq
        rcases buildRelationSetCoreFuel_edge_target_mem signature
            (typeCompilationFuel right) right le_rfl raw hRawMem with
            ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
        · exact ⟨residual, hRawTarget ▸ hResidual⟩
        · exfalso
          have hRawLabel : raw.label = .visible label :=
            congrArg AutomatonFragmentEdge.label hRawEq
          rw [hRawLabel] at hMarkerLabel
          cases hMarkerLabel
      -- A tock step's menu is empty; H15's general form pins the survivor's.
      have hTockFut : childOffers.future = ∅ :=
        helper_h15_edge_future_offers_agree_of_tock signature hQ2Rel hChildRel
          hEdge hTock
      simp [hTockFut]
    · -- The target represents some residual, so H15 pins the future menu.
      obtain ⟨childResidual, hChildRel⟩ :
          ∃ residual, relationMembership
            (buildRelationSet right (compileType signature right)) residual q' := by
        have hSym := compileType_hasEdge_symbol_mem signature right hEdge
        have hMem :=
          (compileType_hasEdge_iff_resolvedEdge_mem signature right q2 q' env
            label childOffers hSym).mp hEdge
        simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hMem
        obtain ⟨raw, hRawMem, hRawEq⟩ := hMem
        have hRawTarget : raw.target = q' :=
          congrArg AutomatonFragmentEdge.target hRawEq
        rcases buildRelationSetCoreFuel_edge_target_mem signature
            (typeCompilationFuel right) right le_rfl raw hRawMem with
            ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
        · exact ⟨residual, hRawTarget ▸ hResidual⟩
        · exfalso
          have hRawLabel : raw.label = .visible label :=
            congrArg AutomatonFragmentEdge.label hRawEq
          rw [hRawLabel] at hMarkerLabel
          cases hMarkerLabel
      -- The child edge's own H15 pins the same menu, modulo reannotation.
      have hChildH15 : childOffers.future =
          typeFutureOffers childResidual \ childOffers.current :=
        helper_h15_edge_future_offers_agree_of_not_tock signature hQ2Rel
          hChildRel hEdge (by
            intro hEq
            exact hTock (by simp [AutomatonConstructionLabel.semantic, hEq]))
      simp only [computeFutureOf_survivorRight_related signature alphabet left
        right interface hChildRel hQ'NotAccFuel, typeFutureOffers_reannotate,
        ← hChildH15]

/-- A lone edge of the surviving left component is a product edge. -/
theorem survivorLeft_mem_edges
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 q' : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (childOffers : TypeOfferSummary)
    (hSymbolResolved : TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 0 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed)) ∈
      signature.transitionAlphabetFor alphabet)
    (hReach : ParallelReachable signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature (typeCompilationFuel left) left)
      (compileTypeFuel signature (typeCompilationFuel right) right)
      (computeFutureOf signature left) (computeFutureOf signature right)
      (.pair q1 q2))
    (hOffCur : restrictTypeOffers interface childOffers.current = ∅)
    (hOffFut : restrictTypeOffers interface childOffers.future = ∅)
    (hEdge : (compileType signature left).HasEdge q1 env label childOffers q')
    (hQ2Acc : q2 ∈ (compileType signature right).accepting)
    (hQ2St : q2 ∈ (compileTypeFuel signature (typeCompilationFuel right) right).states)
    (hQ'NotAcc : q' ∉ (compileType signature left).accepting)
    (hQ'NotAccFuel : q' ∉ (compileTypeFuel signature
      (typeCompilationFuel left) left).accepting)
    {q1Residual : PactType}
    (hQ1Rel : relationMembership
      (buildRelationSet left (compileType signature left)) q1Residual q1) :
    (compileType signature (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 0 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed))
      (.survivor 0 q') := by
  classical
  have hWhole : compileTypeFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface) =
      buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right) := by
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
    rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
        (le_max_left _ _),
      compiledChildFutureFuel_eq_computeFutureOf signature _ right
        (le_max_right _ _)]
    rfl
  have hSymbol' : TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 0 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed)) ∈
      signature.transitionAlphabetFor
        (PactType.par alphabet left right interface).alphabet := by
    simpa [PactType.alphabet] using hSymbolResolved
  have hAcceptEqLeft :
      (compileTypeFuel signature (typeCompilationFuel left) left).accepting
        = (compileType signature left).accepting := by simp [compileType]
  have hAcceptEqRight :
      (compileTypeFuel signature (typeCompilationFuel right) right).accepting
        = (compileType signature right).accepting := by simp [compileType]
  rw [compileType_hasEdge_iff_resolvedEdge_mem signature
    (.par alphabet left right interface) (.pair q1 q2) (.survivor 0 q') env
    label _ hSymbol']
  rw [hWhole]
  simp only [resolveAutomatonEdgesWith, Finset.mem_image]
  have hSymbolLeft := compileType_hasEdge_symbol_mem signature left hEdge
  have hChildMem :=
    (compileType_hasEdge_iff_resolvedEdge_mem signature left q1 q' env label
      childOffers hSymbolLeft).mp hEdge
  refine ⟨{ source := .pair q1 q2
            environment := env
            label := .visible label
            current := childOffers.current
            future := parallelFutureSpec (.visible label)
              (.survivor 0 q') childOffers.current
            target := .survivor 0 q' }, ?_, ?_⟩
  · simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
    left
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_)), hReach⟩
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_filter, Finset.mem_inter]
    refine ⟨q2, ⟨hAcceptEqRight ▸ hQ2Acc, hQ2St⟩, _,
      ⟨hChildMem, ?_, ?_, hOffCur, hOffFut⟩, rfl⟩
    · simp only [parallelComponentEdgeAllowed]
      exact hSymbolLeft
    · exact hAcceptEqLeft ▸ hQ'NotAcc
  · simp only [parallelFutureSpec]
    split_ifs with hTock
    · simp only [AutomatonConstructionLabel.semantic] at hTock
      obtain ⟨childResidual, hChildRel⟩ :
          ∃ residual, relationMembership
            (buildRelationSet left (compileType signature left)) residual q' := by
        have hSym := compileType_hasEdge_symbol_mem signature left hEdge
        have hMem :=
          (compileType_hasEdge_iff_resolvedEdge_mem signature left q1 q' env
            label childOffers hSym).mp hEdge
        simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hMem
        obtain ⟨raw, hRawMem, hRawEq⟩ := hMem
        have hRawTarget : raw.target = q' :=
          congrArg AutomatonFragmentEdge.target hRawEq
        rcases buildRelationSetCoreFuel_edge_target_mem signature
            (typeCompilationFuel left) left le_rfl raw hRawMem with
            ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
        · exact ⟨residual, hRawTarget ▸ hResidual⟩
        · exfalso
          have hRawLabel : raw.label = .visible label :=
            congrArg AutomatonFragmentEdge.label hRawEq
          rw [hRawLabel] at hMarkerLabel
          cases hMarkerLabel
      -- A tock step's menu is empty; H15's general form pins the survivor's.
      have hTockFut : childOffers.future = ∅ :=
        helper_h15_edge_future_offers_agree_of_tock signature hQ1Rel hChildRel
          hEdge hTock
      simp [hTockFut]
    · -- The target represents some residual, so H15 pins the future menu.
      obtain ⟨childResidual, hChildRel⟩ :
          ∃ residual, relationMembership
            (buildRelationSet left (compileType signature left)) residual q' := by
        have hSym := compileType_hasEdge_symbol_mem signature left hEdge
        have hMem :=
          (compileType_hasEdge_iff_resolvedEdge_mem signature left q1 q' env
            label childOffers hSym).mp hEdge
        simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hMem
        obtain ⟨raw, hRawMem, hRawEq⟩ := hMem
        have hRawTarget : raw.target = q' :=
          congrArg AutomatonFragmentEdge.target hRawEq
        rcases buildRelationSetCoreFuel_edge_target_mem signature
            (typeCompilationFuel left) left le_rfl raw hRawMem with
            ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
        · exact ⟨residual, hRawTarget ▸ hResidual⟩
        · exfalso
          have hRawLabel : raw.label = .visible label :=
            congrArg AutomatonFragmentEdge.label hRawEq
          rw [hRawLabel] at hMarkerLabel
          cases hMarkerLabel
      have hChildH15 : childOffers.future =
          typeFutureOffers childResidual \ childOffers.current :=
        helper_h15_edge_future_offers_agree_of_not_tock signature hQ1Rel
          hChildRel hEdge (by
            intro hEq
            exact hTock (by simp [AutomatonConstructionLabel.semantic, hEq]))
      simp only [computeFutureOf_survivorLeft_related signature alphabet left
        right interface hChildRel hQ'NotAccFuel, typeFutureOffers_reannotate,
        ← hChildH15]

set_option maxHeartbeats 4000000 in
/-- Two families of edge leave a product state.

Forward direction: a product edge is either a pair of component edges meeting
the `SyncEdges` condition, or a lone edge of one component whose sibling
already rests at an accepting state and whose interface offers are empty.

Backward direction: either family is by construction a parallel edge.

Both call sites in `correspondence_par_stepIff` already have a relation
witness for `q1`/`q2` in hand (from `relationMembership_par_cases`) before
they ever invoke this lemma, so `childLeft`/`childRight` are threaded in as
fixed hypotheses here rather than re-derived from bare automaton data. -/
theorem buildParallelAutomaton_pair_hasEdge_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    {childLeft childRight : PactType}
    (hParallelCompatible :
      PactTypeAlphabet.ParallelCompatible alphabet left.alphabet right.alphabet
        interface)
    (hSymbol :
      TypeAutomatonSymbol.mk env label offers ∈
        signature.transitionAlphabetFor alphabet)
    (hChildLeftRelated :
      relationMembership (buildRelationSet left (compileType signature left))
        childLeft q1)
    (hChildRightRelated :
      relationMembership (buildRelationSet right (compileType signature right))
        childRight q2) :
    (compileType signature (.par alphabet left right interface)).HasEdge
        (.pair q1 q2) env label offers target ↔
      (∃ (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
        (leftOffers rightOffers : TypeOfferSummary) (q1' q2' : TypeAutomatonState),
        (compileType signature left).HasEdge q1 leftEnv leftLabel leftOffers q1' ∧
        (compileType signature right).HasEdge q2 rightEnv rightLabel rightOffers q2' ∧
        ParallelReachable signature alphabet left.alphabet right.alphabet
          interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right)
          (.pair q1 q2) ∧
        -- A non-redirecting edge realizes the ordinary rule, which fires only
        -- from a live pair.  A redirecting one realizes the fusing rule, whose
        -- sources are unconstrained.
        (¬ (q1' ∈ (compileType signature left).accepting ∧
              q2' ∈ (compileType signature right).accepting) →
          q1 ∉ (compileType signature left).accepting ∧
          q2 ∉ (compileType signature right).accepting) ∧
        env.WellFormed ∧
        LocalTypeOfferEnvironment env interface left rightEnv
          rightOffers.current rightOffers.future leftEnv ∧
        LocalTypeOfferEnvironment env interface right leftEnv
          leftOffers.current leftOffers.future rightEnv ∧
        TypeLabel.Sync interface leftLabel rightLabel ∧
        label = TypeLabel.combine interface leftLabel rightLabel ∧
        offers.current =
          hideTypeOffers interface (leftOffers.current ∪ rightOffers.current) ∧
        offers.future =
          hideTypeOffers interface (leftOffers.future ∪ rightOffers.future) ∧
        -- Mirrors the compiler's own redirect: a raw target whose both sides
        -- are accepting (H13: exactly when both children finish) is placed
        -- in `q_done`, never left as its own separate `.pair` state.
        (if q1' ∈ (compileType signature left).accepting ∧
            q2' ∈ (compileType signature right).accepting then
          target = TypeAutomatonState.final
        else target = .pair q1' q2')) ∨
      -- The sibling already rests at an accepting state, so the survivor
      -- steps alone and the product node disappears.
      (∃ q' : TypeAutomatonState,
        ParallelReachable signature alphabet left.alphabet right.alphabet
          interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right)
          (.pair q1 q2) ∧
        ((∃ childOffers : TypeOfferSummary,
            (compileType signature left).HasEdge q1 env label childOffers q' ∧
            restrictTypeOffers interface childOffers.current = ∅ ∧
            restrictTypeOffers interface childOffers.future = ∅ ∧
            offers = TypeOfferSummary.mk childOffers.current
              (match parallelFutureSpec (.visible label) (.survivor 0 q')
                  childOffers.current with
                | .explicit o => o
                | .at state removed =>
                    computeFutureOf signature
                      (.par alphabet left right interface) state \ removed) ∧
            q2 ∈ (compileType signature right).accepting ∧
            q2 ∈ (compileTypeFuel signature
              (typeCompilationFuel right) right).states ∧
            q' ∉ (compileType signature left).accepting ∧
            q' ∉ (compileTypeFuel signature
              (typeCompilationFuel left) left).accepting ∧
            target = .survivor 0 q') ∨
          (∃ childOffers : TypeOfferSummary,
            (compileType signature right).HasEdge q2 env label childOffers q' ∧
            restrictTypeOffers interface childOffers.current = ∅ ∧
            restrictTypeOffers interface childOffers.future = ∅ ∧
            offers = TypeOfferSummary.mk childOffers.current
              (match parallelFutureSpec (.visible label) (.survivor 1 q')
                  childOffers.current with
                | .explicit o => o
                | .at state removed =>
                    computeFutureOf signature
                      (.par alphabet left right interface) state \ removed) ∧
            q1 ∈ (compileType signature left).accepting ∧
            q1 ∈ (compileTypeFuel signature
              (typeCompilationFuel left) left).states ∧
            q' ∉ (compileType signature right).accepting ∧
            q' ∉ (compileTypeFuel signature
              (typeCompilationFuel right) right).accepting ∧
            target = .survivor 1 q'))) := by
  classical
  have hWhole : compileTypeFuel signature
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface) =
      buildParallelAutomaton signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right) := by
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildParallelAutomaton signature alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compileTypeFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
      (compiledChildFutureFuel signature
        (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
    rw [compiledChildFutureFuel_eq_computeFutureOf signature _ left
        (le_max_left _ _),
      compiledChildFutureFuel_eq_computeFutureOf signature _ right
        (le_max_right _ _)]
    rfl
  constructor
  · intro hEdge
    have hSymbol := compileType_hasEdge_symbol_mem signature
      (.par alphabet left right interface) hEdge
    have hSymbol' : TypeAutomatonSymbol.mk env label offers ∈
        signature.transitionAlphabetFor alphabet := by
      simpa [PactType.alphabet] using hSymbol
    have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
      (.par alphabet left right interface) (.pair q1 q2) target env label offers
      hSymbol').mp hEdge
    obtain ⟨edge, hPending, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
      hResolved
    rw [hWhole] at hPending
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      parallelRawTransitionEdges, parallelLeftCompleteEdges,
      parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
      parallelRightCompleteSurvivorEdges, parallelDoneEdges, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image,
      Finset.mem_inter] at hPending
    rcases hPending with ⟨hTransition, hReach⟩ | hDoneEdge
    swap
    · exfalso
      obtain ⟨environment, hEnvironment, hEq⟩ := hDoneEdge
      rw [← hEq] at hSource
      simp at hSource
    -- The two survivor-region families source from `.survivor`, never a pair.
    rcases hTransition with hTransition | hLeftSurvivorCont
    swap
    · exfalso
      obtain ⟨leftEdge, -, hEq⟩ := hLeftSurvivorCont
      rw [← hEq] at hSource
      simp at hSource
    rcases hTransition with hTransition | hRightSurvivorCont
    swap
    · exfalso
      obtain ⟨rightEdge, -, hEq⟩ := hRightSurvivorCont
      rw [← hEq] at hSource
      simp at hSource
    rcases hTransition with hSynced | hRightFinished
    swap
    · -- The right component rests at an accepting state, so the surviving
      -- left component carries the edge alone.
      obtain ⟨rightState, ⟨hRightAcc, hRightSt⟩, leftEdge,
        ⟨hLeftMem, hLeftAllowed, hLeftNotAcc, hLeftCur, hLeftFut⟩,
        hEq⟩ := hRightFinished
      rw [← hEq] at hSource hEnv hLabel hCurrent hFuture hTarget hReach
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget hReach
      injection hSource with hQ1Eq hQ2Eq
      cases hLabelForm : leftEdge.label with
      | «variable» name =>
          exfalso
          rw [hLabelForm] at hLabel
          simp at hLabel
      | visible leftVisible =>
          have hSymbolMem : TypeAutomatonSymbol.mk leftEdge.environment
              leftVisible
              (TypeOfferSummary.mk leftEdge.current leftEdge.future) ∈
              signature.transitionAlphabetFor left.alphabet := by
            simp only [parallelComponentEdgeAllowed, hLabelForm] at hLeftAllowed
            exact hLeftAllowed
          have hHasEdge : (compileType signature left).HasEdge leftEdge.source
              leftEdge.environment leftVisible
              (TypeOfferSummary.mk leftEdge.current leftEdge.future)
              leftEdge.target := by
            rw [compileType_hasEdge_iff_resolvedEdge_mem signature left
              leftEdge.source leftEdge.target leftEdge.environment leftVisible
              (TypeOfferSummary.mk leftEdge.current leftEdge.future) hSymbolMem]
            have hEdgeEq :
                AutomatonFragmentEdge.mk leftEdge.source leftEdge.environment
                  (AutomatonConstructionLabel.visible leftVisible)
                  leftEdge.current leftEdge.future leftEdge.target = leftEdge := by
              rw [← hLabelForm]
            rw [hEdgeEq]
            exact hLeftMem
          have hLabelVis : leftVisible = label := by
            rw [hLabelForm] at hLabel
            injection hLabel
          refine Or.inr ⟨leftEdge.target, ?_,
            Or.inl ⟨TypeOfferSummary.mk leftEdge.current leftEdge.future,
              hQ1Eq ▸ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              hTarget.symm⟩⟩
          · rw [← hQ1Eq, ← hQ2Eq]; exact hReach
          · rw [← hLabelVis, ← hEnv]
            exact hHasEdge
          · exact hLeftCur
          · exact hLeftFut
          · -- Both components come straight from the resolved product edge.
            rw [← hLabelVis, ← hLabelForm]
            cases offers
            simp only [TypeOfferSummary.mk.injEq]
            exact ⟨hCurrent.symm, hFuture.symm⟩
          · exact hQ2Eq ▸ hRightAcc
          · exact hQ2Eq ▸ hRightSt
          · rw [← compileType_accepting_eq signature left]; exact hLeftNotAcc
          · exact hLeftNotAcc
    rcases hSynced with
        ⟨leftEdge, hLeftMem, rightEdge,
          ⟨hRightMem, hSync0, hSrcLive⟩, hEq⟩ |
        hLeftFinished
    swap
    · -- The mirror case: the left component has finished and the right
      -- component survives.
      obtain ⟨leftState, ⟨hLeftAcc, hLeftSt⟩, rightEdge,
        ⟨hRightMem, hRightAllowed, hRightNotAcc, hRightCur, hRightFut⟩,
        hEq⟩ := hLeftFinished
      rw [← hEq] at hSource hEnv hLabel hCurrent hFuture hTarget hReach
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget hReach
      injection hSource with hQ1Eq hQ2Eq
      cases hLabelForm : rightEdge.label with
      | «variable» name =>
          exfalso
          rw [hLabelForm] at hLabel
          simp at hLabel
      | visible rightVisible =>
          have hSymbolMem : TypeAutomatonSymbol.mk rightEdge.environment
              rightVisible
              (TypeOfferSummary.mk rightEdge.current rightEdge.future) ∈
              signature.transitionAlphabetFor right.alphabet := by
            simp only [parallelComponentEdgeAllowed, hLabelForm] at hRightAllowed
            exact hRightAllowed
          have hHasEdge : (compileType signature right).HasEdge rightEdge.source
              rightEdge.environment rightVisible
              (TypeOfferSummary.mk rightEdge.current rightEdge.future)
              rightEdge.target := by
            rw [compileType_hasEdge_iff_resolvedEdge_mem signature right
              rightEdge.source rightEdge.target rightEdge.environment
              rightVisible
              (TypeOfferSummary.mk rightEdge.current rightEdge.future)
              hSymbolMem]
            have hEdgeEq :
                AutomatonFragmentEdge.mk rightEdge.source rightEdge.environment
                  (AutomatonConstructionLabel.visible rightVisible)
                  rightEdge.current rightEdge.future rightEdge.target =
                  rightEdge := by
              rw [← hLabelForm]
            rw [hEdgeEq]
            exact hRightMem
          have hLabelVis : rightVisible = label := by
            rw [hLabelForm] at hLabel
            injection hLabel
          refine Or.inr ⟨rightEdge.target, ?_,
            Or.inr ⟨TypeOfferSummary.mk rightEdge.current rightEdge.future,
              hQ2Eq ▸ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              hTarget.symm⟩⟩
          · rw [← hQ1Eq, ← hQ2Eq]; exact hReach
          · rw [← hLabelVis, ← hEnv]
            exact hHasEdge
          · exact hRightCur
          · exact hRightFut
          · -- Both components come straight from the resolved product edge.
            rw [← hLabelVis, ← hLabelForm]
            cases offers
            simp only [TypeOfferSummary.mk.injEq]
            exact ⟨hCurrent.symm, hFuture.symm⟩
          · exact hQ1Eq ▸ hLeftAcc
          · exact hQ1Eq ▸ hLeftSt
          · have hAcceptEq :
                (compileTypeFuel signature (typeCompilationFuel right)
                  right).accepting =
                (compileType signature right).accepting := compileType_accepting_eq signature _
            rw [← hAcceptEq]; exact hRightNotAcc
          · exact hRightNotAcc
    rw [← hEq] at hSource hEnv hLabel hCurrent hFuture hTarget hReach
    simp only at hSource hEnv hLabel hCurrent hFuture hTarget hReach
    injection hSource with hQ1Eq hQ2Eq
    cases hLabelForm : leftEdge.label with
    | «variable» name =>
        exfalso
        rw [hLabelForm] at hLabel
        simp [AutomatonConstructionLabel.combine] at hLabel
    | visible leftVisible =>
    cases hRightLabelForm : rightEdge.label with
    | «variable» name =>
        exfalso
        rw [hLabelForm, hRightLabelForm] at hLabel
        simp [AutomatonConstructionLabel.combine] at hLabel
    | visible rightVisible =>
    have hSyncFull : syncAutomatonEdges signature left.alphabet right.alphabet
        interface leftEdge rightEdge := hSync0
    simp only [syncAutomatonEdges, parallelComponentEdgeAllowed, hLabelForm,
      hRightLabelForm] at hSyncFull
    obtain ⟨hLeftAllowed, hRightAllowed, hAutoLocal1, hAutoLocal2, hSameCurLeft,
      hSameCurRight, hSameFutLeft, hSameFutRight, hSyncCond⟩ := hSyncFull
    rw [hEnv] at hAutoLocal1 hAutoLocal2
    have hLeftSymbolMem : TypeAutomatonSymbol.mk leftEdge.environment
        leftVisible (TypeOfferSummary.mk leftEdge.current leftEdge.future) ∈
        signature.transitionAlphabetFor left.alphabet := by
      simpa [hLabelForm] using hLeftAllowed
    have hRightSymbolMem : TypeAutomatonSymbol.mk rightEdge.environment
        rightVisible (TypeOfferSummary.mk rightEdge.current rightEdge.future) ∈
        signature.transitionAlphabetFor right.alphabet := by
      simpa [hRightLabelForm] using hRightAllowed
    have hLeftHasEdge : (compileType signature left).HasEdge leftEdge.source
        leftEdge.environment leftVisible
        (TypeOfferSummary.mk leftEdge.current leftEdge.future) leftEdge.target := by
      rw [compileType_hasEdge_iff_resolvedEdge_mem signature left leftEdge.source
        leftEdge.target leftEdge.environment leftVisible
        (TypeOfferSummary.mk leftEdge.current leftEdge.future) hLeftSymbolMem]
      have hEdgeEq :
          AutomatonFragmentEdge.mk leftEdge.source leftEdge.environment
            (AutomatonConstructionLabel.visible leftVisible) leftEdge.current
            leftEdge.future leftEdge.target = leftEdge := by
        rw [← hLabelForm]
      rw [hEdgeEq]
      exact hLeftMem
    have hRightHasEdge : (compileType signature right).HasEdge rightEdge.source
        rightEdge.environment rightVisible
        (TypeOfferSummary.mk rightEdge.current rightEdge.future) rightEdge.target := by
      rw [compileType_hasEdge_iff_resolvedEdge_mem signature right rightEdge.source
        rightEdge.target rightEdge.environment rightVisible
        (TypeOfferSummary.mk rightEdge.current rightEdge.future) hRightSymbolMem]
      have hEdgeEq :
          AutomatonFragmentEdge.mk rightEdge.source rightEdge.environment
            (AutomatonConstructionLabel.visible rightVisible) rightEdge.current
            rightEdge.future rightEdge.target = rightEdge := by
        rw [← hRightLabelForm]
      rw [hEdgeEq]
      exact hRightMem
    have hEnvWF : env.WellFormed :=
      localEnvironment_wellFormed signature
        (TypeAlphabet.localEnvironmentsFor_subset_localEnvironments
          signature alphabet
          (transitionAlphabetFor_localEnvironment_mem signature alphabet
            hSymbol'))
    have hLocal1 : LocalTypeOfferEnvironment env interface left
        rightEdge.environment rightEdge.current rightEdge.future
        leftEdge.environment := by
      rcases hAutoLocal1 with
        ⟨hOuterClock, hSiblingClock, hLocalClock⟩ |
        ⟨hOuterClock, hSiblingClock, hLocalClock, hImmediate, hFuture⟩
      · exact hSiblingClock ▸ hLocalClock ▸
          LocalTypeOfferEnvironment.clock env interface left
            rightEdge.current rightEdge.future hOuterClock
      · exact LocalTypeOfferEnvironment.ordinary env rightEdge.environment
          leftEdge.environment interface left rightEdge.current
          rightEdge.future hOuterClock hSiblingClock hLocalClock hImmediate
          hFuture
    have hLocal2 : LocalTypeOfferEnvironment env interface right
        leftEdge.environment leftEdge.current leftEdge.future
        rightEdge.environment := by
      rcases hAutoLocal2 with
        ⟨hOuterClock, hSiblingClock, hLocalClock⟩ |
        ⟨hOuterClock, hSiblingClock, hLocalClock, hImmediate, hFuture⟩
      · exact hSiblingClock ▸ hLocalClock ▸
          LocalTypeOfferEnvironment.clock env interface right
            leftEdge.current leftEdge.future hOuterClock
      · exact LocalTypeOfferEnvironment.ordinary env leftEdge.environment
          rightEdge.environment interface right leftEdge.current
          leftEdge.future hOuterClock hSiblingClock hLocalClock hImmediate
          hFuture
    have hAcceptEqLeft := compileType_accepting_eq signature left
    have hAcceptEqRight := compileType_accepting_eq signature right
    -- Residual witnesses at the two child targets, needed for H15.
    obtain ⟨leftTargetResidual, hLeftTargetRelated⟩ :
        ∃ residual, relationMembership
          (buildRelationSet left (compileType signature left)) residual
          leftEdge.target := by
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftMem
      obtain ⟨rawLeft, hRawLeftMem, hRawLeftEq⟩ := hLeftMem
      have hRawLeftTarget : rawLeft.target = leftEdge.target := by
        rw [← hRawLeftEq]
      rcases buildRelationSetCoreFuel_edge_target_mem signature
          (typeCompilationFuel left) left le_rfl rawLeft hRawLeftMem with
          ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
      · exact ⟨residual, hRawLeftTarget ▸ hResidual⟩
      · exfalso
        have hRawLeftLabel : rawLeft.label = .visible leftVisible := by
          rw [← hRawLeftEq] at hLabelForm; exact hLabelForm
        rw [hRawLeftLabel] at hMarkerLabel
        cases hMarkerLabel
    obtain ⟨rightTargetResidual, hRightTargetRelated⟩ :
        ∃ residual, relationMembership
          (buildRelationSet right (compileType signature right)) residual
          rightEdge.target := by
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightMem
      obtain ⟨rawRight, hRawRightMem, hRawRightEq⟩ := hRightMem
      have hRawRightTarget : rawRight.target = rightEdge.target := by
        rw [← hRawRightEq]
      rcases buildRelationSetCoreFuel_edge_target_mem signature
          (typeCompilationFuel right) right le_rfl rawRight hRawRightMem with
          ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
      · exact ⟨residual, hRawRightTarget ▸ hResidual⟩
      · exfalso
        have hRawRightLabel : rawRight.label = .visible rightVisible := by
          rw [← hRawRightEq] at hRightLabelForm; exact hRightLabelForm
        rw [hRawRightLabel] at hMarkerLabel
        cases hMarkerLabel
    have hLeftFutureEqIf : leftEdge.future =
        if leftVisible = TypeLabel.tock then ∅
        else typeFutureOffers leftTargetResidual \ leftEdge.current :=
      helper_h15_edge_future_offers_agree signature hChildLeftRelated
        hLeftTargetRelated (hQ1Eq ▸ hLeftHasEdge)
    have hRightFutureEqIf : rightEdge.future =
        if rightVisible = TypeLabel.tock then ∅
        else typeFutureOffers rightTargetResidual \ rightEdge.current :=
      helper_h15_edge_future_offers_agree signature hChildRightRelated
        hRightTargetRelated (hQ2Eq ▸ hRightHasEdge)
    -- `Sync` forces the two component labels to agree on tock-ness, so the
    -- two `if`s above are governed by a single case distinction.
    have hTockIff : leftVisible = TypeLabel.tock ↔ rightVisible = TypeLabel.tock := by
      have hIsTock := hSyncCond.2.2
      constructor
      · intro hL
        cases hRightVis : rightVisible with
        | tock => rfl
        | actions obs =>
            exact absurd (hIsTock.mp (by rw [hL]; trivial))
              (by rw [hRightVis]; exact id)
      · intro hR
        cases hLeftVis : leftVisible with
        | tock => rfl
        | actions obs =>
            exact absurd (hIsTock.mpr (by rw [hR]; trivial))
              (by rw [hLeftVis]; exact id)
    have hParFutureEq : computeFutureOf signature (.par alphabet left right interface)
        (if leftEdge.target ∈ (compileType signature left).accepting ∧
            rightEdge.target ∈ (compileType signature right).accepting then
          TypeAutomatonState.final
        else leftEdge.target.pair rightEdge.target) =
        hideTypeOffers interface
          (typeFutureOffers leftTargetResidual ∪ typeFutureOffers rightTargetResidual) := by
      split_ifs with hAccept
      · have hParTargetRelated := relationMembership_par_final signature alphabet
          left right interface
        rw [helper_h15_future_offers_agree signature hParTargetRelated]
        obtain ⟨leftAlph, hLeftMem'⟩ :=
          relationMembership_of_accepting signature left hAccept.1
        obtain ⟨rightAlph, hRightMem'⟩ :=
          relationMembership_of_accepting signature right hAccept.2
        have hLeftSkip : leftTargetResidual = .skip leftAlph :=
          relationMembership_functional left (compileType signature left)
            hLeftTargetRelated hLeftMem'
        have hRightSkip : rightTargetResidual = .skip rightAlph :=
          relationMembership_functional right (compileType signature right)
            hRightTargetRelated hRightMem'
        rw [hLeftSkip, hRightSkip]
        simp [typeFutureOffers, typeFutureOffersFuel, hideTypeOffers, PactType.alphabet]
      · have hReachTarget :
            ParallelReachable signature alphabet left.alphabet right.alphabet
              interface
              (compileTypeFuel signature (typeCompilationFuel left) left)
              (compileTypeFuel signature (typeCompilationFuel right) right)
              (computeFutureOf signature left) (computeFutureOf signature right)
              (.pair leftEdge.target rightEdge.target) := by
          have hRaw := compiledParallel_pair_edge_target_reachable signature alphabet
            left right interface hSymbol hEdge
          rw [← hTarget] at hRaw
          rwa [if_neg (hAcceptEqLeft ▸ hAcceptEqRight ▸ hAccept)] at hRaw
        have hParTargetRelated := relationMembership_par_pair signature alphabet
          left right interface hLeftTargetRelated hRightTargetRelated hReachTarget
        rw [helper_h15_future_offers_agree signature hParTargetRelated,
          typeFutureOffers_parallel]
    have hRightCurrentSubset : rightEdge.current ⊆ right.alphabet.actions := by
      rw [transitionAlphabetFor_mk_mem_iff] at hRightSymbolMem
      have := hRightSymbolMem.2.2
      rw [localOfferSummariesFor_mk_mem_iff] at this
      exact this.1.trans Finset.inter_subset_right
    have hLeftCurrentSubset : leftEdge.current ⊆ left.alphabet.actions := by
      rw [transitionAlphabetFor_mk_mem_iff] at hLeftSymbolMem
      have := hLeftSymbolMem.2.2
      rw [localOfferSummariesFor_mk_mem_iff] at this
      exact this.1.trans Finset.inter_subset_right
    have hActionsDisjoint : Disjoint left.alphabet.actions right.alphabet.actions :=
      hParallelCompatible.actions_disjoint
    have hFutureEq : offers.future =
        hideTypeOffers interface (leftEdge.future ∪ rightEdge.future) := by
      by_cases hTockL : leftVisible = TypeLabel.tock
      · -- Tock edges carry an explicit empty future on both the component
        -- edges and the compiled product edge.
        have hTockR : rightVisible = TypeLabel.tock := hTockIff.mp hTockL
        have hLeftEmpty : leftEdge.future = ∅ := by
          rw [hLeftFutureEqIf, if_pos hTockL]
        have hRightEmpty : rightEdge.future = ∅ := by
          rw [hRightFutureEqIf, if_pos hTockR]
        have hCombineTock :
            (AutomatonConstructionLabel.combine interface leftEdge.label
              rightEdge.label).semantic = TypeLabel.tock := by
          rw [hLabelForm, hRightLabelForm, hTockL, hTockR]
          simp [AutomatonConstructionLabel.combine,
            AutomatonConstructionLabel.semantic, TypeLabel.combine]
        rw [← hFuture]
        simp [parallelFutureSpec, hCombineTock, hLeftEmpty, hRightEmpty,
          hideTypeOffers, hideOffers]
      have hLeftFutureEq : leftEdge.future =
          typeFutureOffers leftTargetResidual \ leftEdge.current := by
        rw [hLeftFutureEqIf, if_neg hTockL]
      have hRightFutureEq : rightEdge.future =
          typeFutureOffers rightTargetResidual \ rightEdge.current := by
        rw [hRightFutureEqIf, if_neg (fun h => hTockL (hTockIff.mpr h))]
      -- An action in `left`'s future menu but not its own current offer is
      -- exactly an action of the resolved edge `leftEdge.future`, which stays
      -- within `left`'s own fixed alphabet; the two children's fixed
      -- alphabets are disjoint (`ParallelCompatible`), so it can never sit in
      -- `right`'s current offer, and symmetrically.
      have hLeftFutureRightCurrentDisjoint :
          ∀ action, action ∈ typeFutureOffers leftTargetResidual →
            action ∉ leftEdge.current → action ∉ rightEdge.current := by
        intro action hLeftFuture hNotLeftCurrent hRightCurrent
        have hLeftAlph : action ∈ left.alphabet.actions := by
          rw [transitionAlphabetFor_mk_mem_iff] at hLeftSymbolMem
          rw [localOfferSummariesFor_mk_mem_iff] at hLeftSymbolMem
          refine (hLeftSymbolMem.2.2.2.trans Finset.inter_subset_right) ?_
          rw [hLeftFutureEq]
          exact Finset.mem_sdiff.mpr ⟨hLeftFuture, hNotLeftCurrent⟩
        exact Finset.disjoint_left.mp hActionsDisjoint hLeftAlph
          (hRightCurrentSubset hRightCurrent)
      have hRightFutureLeftCurrentDisjoint :
          ∀ action, action ∈ typeFutureOffers rightTargetResidual →
            action ∉ rightEdge.current → action ∉ leftEdge.current := by
        intro action hRightFuture hNotRightCurrent hLeftCurrent
        have hRightAlph : action ∈ right.alphabet.actions := by
          rw [transitionAlphabetFor_mk_mem_iff] at hRightSymbolMem
          rw [localOfferSummariesFor_mk_mem_iff] at hRightSymbolMem
          refine (hRightSymbolMem.2.2.2.trans Finset.inter_subset_right) ?_
          rw [hRightFutureEq]
          exact Finset.mem_sdiff.mpr ⟨hRightFuture, hNotRightCurrent⟩
        exact Finset.disjoint_right.mp hActionsDisjoint hRightAlph
          (hLeftCurrentSubset hLeftCurrent)
      have hCombineNotTock :
          ¬ (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock := by
        rw [hLabelForm, hRightLabelForm]
        cases hLeftVis : leftVisible with
        | tock => exact absurd hLeftVis hTockL
        | actions leftObs =>
            cases hRightVis : rightVisible with
            | tock =>
                exact absurd (hTockIff.mpr hRightVis) hTockL
            | actions rightObs =>
                simp [AutomatonConstructionLabel.combine,
                  AutomatonConstructionLabel.semantic, TypeLabel.combine]
      have hFuture' := hFuture
      rw [hAcceptEqLeft, hAcceptEqRight] at hFuture'
      rw [← hFuture']
      simp [parallelFutureSpec, hCombineNotTock]
      rw [hParFutureEq]
      rw [hLeftFutureEq, hRightFutureEq]
      apply Finset.ext
      intro action
      simp only [hideTypeOffers, hideOffers, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨⟨(hL | hR), hInterface⟩, hNotCur⟩
        · refine ⟨Or.inl ⟨hL, ?_⟩, hInterface⟩
          intro hLCur
          exact hNotCur ⟨Or.inl hLCur, hInterface⟩
        · refine ⟨Or.inr ⟨hR, ?_⟩, hInterface⟩
          intro hRCur
          exact hNotCur ⟨Or.inr hRCur, hInterface⟩
      · rintro ⟨(⟨hL, hLNotCur⟩ | ⟨hR, hRNotCur⟩), hInterface⟩
        · refine ⟨⟨Or.inl hL, hInterface⟩, ?_⟩
          rintro ⟨hCur | hCur, -⟩
          · exact hLNotCur hCur
          · exact hLeftFutureRightCurrentDisjoint action hL hLNotCur hCur
        · refine ⟨⟨Or.inr hR, hInterface⟩, ?_⟩
          rintro ⟨hCur | hCur, -⟩
          · exact hRightFutureLeftCurrentDisjoint action hR hRNotCur hCur
          · exact hRNotCur hCur
    refine Or.inl ⟨leftEdge.environment, rightEdge.environment, leftVisible,
      rightVisible,
      TypeOfferSummary.mk leftEdge.current leftEdge.future,
      TypeOfferSummary.mk rightEdge.current rightEdge.future,
      leftEdge.target, rightEdge.target, hQ1Eq ▸ hLeftHasEdge, hQ2Eq ▸ hRightHasEdge,
      hQ1Eq ▸ hQ2Eq ▸ hReach, ?_, hEnvWF, hLocal1, hLocal2, hSyncCond,
      ?_, ?_, ?_, ?_⟩
    · intro hNotBoth
      rw [← hAcceptEqLeft, ← hAcceptEqRight, ← hQ1Eq, ← hQ2Eq]
      exact hSrcLive (by rw [hAcceptEqLeft, hAcceptEqRight]; exact hNotBoth)
    · rw [hLabelForm, hRightLabelForm, AutomatonConstructionLabel.combine] at hLabel
      injection hLabel with hLabelEq
      exact hLabelEq.symm
    · exact hCurrent.symm
    · exact hFutureEq
    · rw [← hAcceptEqLeft, ← hAcceptEqRight]
      split_ifs with hAccept
      · rw [← hTarget, if_pos hAccept]
      · rw [← hTarget, if_neg hAccept]
  -- Backward direction: given two edges and a reachable pair of targets, we
  -- can reconstruct a parallel edge.
  · rintro (⟨leftEnv, rightEnv, leftLabel, rightLabel, leftOffers, rightOffers, q1', q2',
      hLeftEdge, hRightEdge, hReach, hSrcLive, hEnvWF, hLocal1, hLocal2,
      hSyncCond, hLabelEq, hCurrentEq, hFutureEq, hRedirect⟩ | hSurvivorCase)
    case inr =>
      -- A survivor edge is already one of the product's own edge families.
      obtain ⟨q', hReachSurv, hSide⟩ := hSurvivorCase
      rcases hSide with
          ⟨childOffers, hEdge, hOffCur, hOffFut,
            hOffEq, hQ2Acc, hQ2St, hQ'NotAcc, hQ'NotAccFuel, hTargetEq⟩ |
          ⟨childOffers, hEdge, hOffCur, hOffFut,
            hOffEq, hQ1Acc, hQ1St, hQ'NotAcc, hQ'NotAccFuel, hTargetEq⟩
      all_goals subst hOffEq
      · rw [hTargetEq]
        exact survivorLeft_mem_edges signature alphabet left right interface
          q1 q2 q' env label childOffers hSymbol hReachSurv hOffCur
          hOffFut hEdge hQ2Acc hQ2St hQ'NotAcc
          hQ'NotAccFuel hChildLeftRelated
      · rw [hTargetEq]
        exact survivorRight_mem_edges signature alphabet left right interface
          q1 q2 q' env label childOffers hSymbol hReachSurv hOffCur
          hOffFut hEdge hQ1Acc hQ1St hQ'NotAcc
          hQ'NotAccFuel hChildRightRelated
    have hLeftSymbol := compileType_hasEdge_symbol_mem signature left hLeftEdge
    have hRightSymbol := compileType_hasEdge_symbol_mem signature right hRightEdge
    have hLeftResolvedMem :=
      (compileType_hasEdge_iff_resolvedEdge_mem signature left q1 q1' leftEnv leftLabel
        leftOffers hLeftSymbol).mp hLeftEdge
    have hRightResolvedMem :=
      (compileType_hasEdge_iff_resolvedEdge_mem signature right q2 q2' rightEnv rightLabel
        rightOffers hRightSymbol).mp hRightEdge
    -- Reconstruct the parent environment from the two consistent local
    -- views: `env` is well-formed over the merged, interface-hidden
    -- alphabet, so it can only mention actions coming from `left`/`right`,
    -- and `LocalTypeOfferEnvironment`'s own projection equations recover
    -- exactly that combination.
    have hAlphabetEq : alphabet = PactTypeAlphabet.mergeHidden left.alphabet
        right.alphabet interface := hParallelCompatible.parent_eq
    have hEnvMem : env ∈ signature.localEnvironmentsFor alphabet :=
      transitionAlphabetFor_localEnvironment_mem signature alphabet hSymbol
    -- A single non-interface action ends up in `env`'s menu (immediate or
    -- future) iff the matching sibling-projected offer, drawn from `left`
    -- or `right`, put it there; this is the common core of both halves of
    -- the reconstruction below.
    have hMemChar : ∀ (envSet leftEnvSet rightEnvSet leftSibling rightSibling
        : Finset BareMessage) (action : BareMessage),
        envSet ⊆ signature.localEnvironmentActionsFor alphabet →
        leftEnvSet = projectTypeEnvironmentOffers left.alphabet envSet ∪
          restrictTypeOffers interface rightSibling →
        rightEnvSet = projectTypeEnvironmentOffers right.alphabet envSet ∪
          restrictTypeOffers interface leftSibling →
        (action ∈ envSet ∧ action.1 ∉ interface ↔
          (action ∈ leftEnvSet ∨ action ∈ rightEnvSet) ∧ action.1 ∉ interface) := by
      intro envSet leftEnvSet rightEnvSet leftSibling rightSibling action hEnvSetMem
        hLeftEnvSet hRightEnvSet
      constructor
      · rintro ⟨hAction, hNotInterface⟩
        refine ⟨?_, hNotInterface⟩
        have hActionMem := hEnvSetMem hAction
        simp only [TypeAlphabet.localEnvironmentActionsFor,
          TypeAlphabet.localActionsFor, Finset.mem_image, Finset.mem_inter]
          at hActionMem
        obtain ⟨localAction, ⟨_, hLocalActionAlph⟩, hNeedEq⟩ := hActionMem
        rw [hAlphabetEq] at hLocalActionAlph
        simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter,
          Finset.mem_union] at hLocalActionAlph
        rcases hLocalActionAlph.1 with hL | hR
        · left; rw [hLeftEnvSet]
          exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨hAction,
              Finset.mem_image.mpr ⟨localAction, hL, hNeedEq⟩⟩))
        · right; rw [hRightEnvSet]
          exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_filter.mpr ⟨hAction,
              Finset.mem_image.mpr ⟨localAction, hR, hNeedEq⟩⟩))
      · rintro ⟨hLR, hNotInterface⟩
        refine ⟨?_, hNotInterface⟩
        rcases hLR with hL | hR
        · rw [hLeftEnvSet] at hL
          simp only [Finset.mem_union, projectTypeEnvironmentOffers,
            Finset.mem_filter, restrictTypeOffers] at hL
          rcases hL with ⟨hAction, _⟩ | ⟨_, hInterfaceMem⟩
          · exact hAction
          · exact absurd hInterfaceMem hNotInterface
        · rw [hRightEnvSet] at hR
          simp only [Finset.mem_union, projectTypeEnvironmentOffers,
            Finset.mem_filter, restrictTypeOffers] at hR
          rcases hR with ⟨hAction, _⟩ | ⟨_, hInterfaceMem⟩
          · exact hAction
          · exact absurd hInterfaceMem hNotInterface
    have hEnvMemSet : env.immediate ⊆ signature.localEnvironmentActionsFor alphabet ∧
        env.future ⊆ signature.localEnvironmentActionsFor alphabet := by
      simp only [TypeAlphabet.localEnvironmentsFor, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
        Finset.mem_image] at hEnvMem
      rcases hEnvMem with hTock | ⟨imm, hImm, fut, hFut, hEq⟩
      · rw [hTock]; simp [TypeEnvironment.tock]
      · rw [← hEq]
        exact ⟨hImm, hFut.trans (Finset.sdiff_subset)⟩
    -- Every action `env` itself carries already avoids the interface,
    -- since `alphabet = mergeHidden ...` filters it out at the root.
    have hEnvNotInterface : ∀ action ∈ signature.localEnvironmentActionsFor
        alphabet, action.1 ∉ interface := by
      intro action hAction
      simp only [TypeAlphabet.localEnvironmentActionsFor,
        TypeAlphabet.localActionsFor, Finset.mem_image, Finset.mem_inter]
        at hAction
      obtain ⟨localAction, ⟨_, hLocalActionAlph⟩, hNeedEq⟩ := hAction
      rw [hAlphabetEq] at hLocalActionAlph
      simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter] at hLocalActionAlph
      have hMsgEq : localAction.1 = action.1 := by
        rw [← hNeedEq]; simp [typeNeed]
      rw [← hMsgEq]
      exact hLocalActionAlph.2
    have hEnvEq : env = combineAutomatonEnvironment interface leftEnv rightEnv := by
      cases hLocal1 with
      | clock _ =>
        rename_i hOuterClockA
        cases hLocal2 with
        | clock _ =>
          rename_i hOuterClockC
          show env = combineAutomatonEnvironment interface TypeEnvironment.tock
            TypeEnvironment.tock
          rw [combineAutomatonEnvironment]
          simp only [TypeEnvironment.tock, if_pos rfl]
          have hOuterClock1' : env.clock = true := hOuterClockA
          have hEnvWF' := hEnvWF.1 hOuterClock1'
          obtain ⟨immediate, future, clock⟩ := env
          simp only [TypeEnvironment.clock] at hOuterClock1'
          simp only [hOuterClock1', if_pos rfl]
          simp only [TypeEnvironment.immediate] at hEnvWF'
          rw [hEnvWF'.1, hEnvWF'.2]
          simp
        | ordinary _ _ _ _ _ =>
          rename_i hOuterClockD _ _ _ _
          rw [hOuterClockA] at hOuterClockD
          exact absurd hOuterClockD (by simp)
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClockB hSiblingClock1 hLocalClock1 hImmediate1 hFuture1
        cases hLocal2 with
        | clock _ =>
          rename_i hOuterClockE
          rw [hOuterClockE] at hOuterClockB
          exact absurd hOuterClockB (by simp)
        | ordinary _ _ _ _ _ =>
          rename_i hOuterClockF hSiblingClock2 hLocalClock2 hImmediate2 hFuture2
          simp only [combineAutomatonEnvironment, hSiblingClock2, hSiblingClock1,
            Bool.and_self, Bool.false_eq_true, if_neg, Bool.and_false]
          have hOuterClock1' : env.clock = false := hOuterClockB
          -- Every action `env` itself carries already avoids the interface,
          -- since `alphabet = mergeHidden ...` filters it out at the root.
          have hEnvNotInterface : ∀ action ∈ signature.localEnvironmentActionsFor
              alphabet, action.1 ∉ interface := by
            intro action hAction
            simp only [TypeAlphabet.localEnvironmentActionsFor,
              TypeAlphabet.localActionsFor, Finset.mem_image, Finset.mem_inter]
              at hAction
            obtain ⟨localAction, ⟨_, hLocalActionAlph⟩, hNeedEq⟩ := hAction
            rw [hAlphabetEq] at hLocalActionAlph
            simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter] at hLocalActionAlph
            have hMsgEq : localAction.1 = action.1 := by
              rw [← hNeedEq]; simp [typeNeed]
            rw [← hMsgEq]
            exact hLocalActionAlph.2
          have hImmEq : env.immediate = hideOffers interface (leftEnv.immediate ∪
              rightEnv.immediate) := by
            apply Finset.ext
            intro action
            have hChar := hMemChar env.immediate leftEnv.immediate rightEnv.immediate
              leftOffers.current rightOffers.current action hEnvMemSet.1 hImmediate1
              hImmediate2
            simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hChar ⊢
            rw [show (action ∈ env.immediate ↔
                (action ∈ env.immediate ∧ action.1 ∉ interface))
              from ⟨fun h => ⟨h, hEnvNotInterface action (hEnvMemSet.1 h)⟩, fun h => h.1⟩]
            exact hChar
          have hFutEq : env.future = hideOffers interface (leftEnv.future ∪
              rightEnv.future) := by
            -- `env`'s own immediate/future menus are disjoint (well-formedness),
            -- so the `\ localEnv.immediate` subtraction each side's future
            -- equation never removes a non-interface action relevant here:
            -- such an action, if it were in `leftEnv.immediate`/
            -- `rightEnv.immediate`, would (via `hImmEq`, restricted away from
            -- the interface) already sit in `env.immediate`, contradicting
            -- `env.future`'s disjointness from `env.immediate`.
            have hNotImmediate : ∀ action, action ∈ env.future → action.1 ∉ interface →
                action ∉ leftEnv.immediate ∧ action ∉ rightEnv.immediate := by
              intro action hActionFuture hActionInterface
              have hDisjoint : env.immediate ∩ env.future = ∅ := hEnvWF.2 hOuterClock1'
              have hNotEnvImmediate : action ∉ env.immediate := by
                intro hMem
                have hMemInter : action ∈ env.immediate ∩ env.future :=
                  Finset.mem_inter.mpr ⟨hMem, hActionFuture⟩
                rw [hDisjoint] at hMemInter
                simp at hMemInter
              rw [hImmEq] at hNotEnvImmediate
              simp only [hideOffers, Finset.mem_filter, not_and] at hNotEnvImmediate
              have hNotUnion : action ∉ leftEnv.immediate ∪ rightEnv.immediate :=
                fun hMem => absurd hActionInterface (hNotEnvImmediate hMem)
              simp only [Finset.mem_union, not_or] at hNotUnion
              exact hNotUnion
            apply Finset.ext
            intro action
            have hEnvFutureIff : action ∈ env.future ↔
                (action ∈ leftEnv.future ∨ action ∈ rightEnv.future) ∧
                  action.1 ∉ interface := by
              have hChar := hMemChar env.future
                (projectTypeEnvironmentOffers left.alphabet env.future ∪
                  restrictTypeOffers interface rightOffers.future)
                (projectTypeEnvironmentOffers right.alphabet env.future ∪
                  restrictTypeOffers interface leftOffers.future)
                leftOffers.future rightOffers.future action hEnvMemSet.2 rfl rfl
              simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hChar
              constructor
              · intro hActionFuture
                have hActionInterface := hEnvNotInterface action (hEnvMemSet.2 hActionFuture)
                have hOr := (hChar.mp ⟨hActionFuture, hActionInterface⟩).1
                refine ⟨?_, hActionInterface⟩
                rcases hOr with hL | hR
                · left; rw [hFuture1]
                  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr hL,
                    (hNotImmediate action hActionFuture hActionInterface).1⟩
                · right; rw [hFuture2]
                  exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr hR,
                    (hNotImmediate action hActionFuture hActionInterface).2⟩
              · rintro ⟨hOr, hNI⟩
                have hEnvChar := hChar.mpr (by
                  refine ⟨?_, hNI⟩
                  rcases hOr with hL | hR
                  · left; rw [hFuture1] at hL
                    exact Finset.mem_union.mp (Finset.mem_sdiff.mp hL).1
                  · right; rw [hFuture2] at hR
                    exact Finset.mem_union.mp (Finset.mem_sdiff.mp hR).1)
                exact hEnvChar.1
            simp only [hideOffers, Finset.mem_filter, Finset.mem_union]
            exact hEnvFutureIff
          obtain ⟨immediate, future, clock⟩ := env
          simp only [TypeEnvironment.clock] at hOuterClock1'
          subst hOuterClock1'
          simp only at hImmEq hFutEq
          congr 1
    have hAutoLocal1 : AutomatonLocalEnvironment
        (combineAutomatonEnvironment interface leftEnv rightEnv) interface left.alphabet
        ({ source := q2, environment := rightEnv, label := .visible rightLabel,
            current := rightOffers.current, future := rightOffers.future,
            target := q2' } : AutomatonFragmentEdge)
        ({ source := q1, environment := leftEnv, label := .visible leftLabel,
            current := leftOffers.current, future := leftOffers.future,
            target := q1' } : AutomatonFragmentEdge) := by
      rw [← hEnvEq]
      cases hLocal1 with
      | clock _ =>
        rename_i hOuterClock
        exact AutomatonLocalEnvironment.clock hOuterClock rfl rfl
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock hSiblingClock hLocalClock hImmediate hFuture
        exact AutomatonLocalEnvironment.ordinary hOuterClock hSiblingClock hLocalClock
          hImmediate hFuture
    have hAutoLocal2 : AutomatonLocalEnvironment
        (combineAutomatonEnvironment interface leftEnv rightEnv) interface right.alphabet
        ({ source := q1, environment := leftEnv, label := .visible leftLabel,
            current := leftOffers.current, future := leftOffers.future,
            target := q1' } : AutomatonFragmentEdge)
        ({ source := q2, environment := rightEnv, label := .visible rightLabel,
            current := rightOffers.current, future := rightOffers.future,
            target := q2' } : AutomatonFragmentEdge) := by
      rw [← hEnvEq]
      cases hLocal2 with
      | clock _ =>
        rename_i hOuterClock
        exact AutomatonLocalEnvironment.clock hOuterClock rfl rfl
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock hSiblingClock hLocalClock hImmediate hFuture
        exact AutomatonLocalEnvironment.ordinary hOuterClock hSiblingClock hLocalClock
          hImmediate hFuture
    -- A non-interface action of `env`'s own menu can never itself sit on the
    -- interface once projected into a child alphabet, so restricting the
    -- projected summand to the interface always drops it.
    have hProjectDrop : ∀ (childAlphabet : PactTypeAlphabet) (envSet : Finset BareMessage),
        envSet ⊆ signature.localEnvironmentActionsFor alphabet →
        restrictTypeOffers interface
          (projectTypeEnvironmentOffers childAlphabet envSet) = ∅ := by
      intro childAlphabet envSet hEnvSet
      unfold restrictTypeOffers
      rw [Finset.filter_eq_empty_iff]
      intro action hAction hInterface
      simp only [projectTypeEnvironmentOffers, Finset.mem_filter] at hAction
      exact hEnvNotInterface action (hEnvSet hAction.1) hInterface
    have hRestrictIdem : ∀ s : Finset BareMessage,
        restrictTypeOffers interface (restrictTypeOffers interface s) =
          restrictTypeOffers interface s := by
      intro s
      apply Finset.ext
      intro action
      simp only [restrictTypeOffers, Finset.mem_filter]
      tauto
    have hRestrictSdiff : ∀ s t : Finset BareMessage,
        restrictTypeOffers interface (s \ t) =
          restrictTypeOffers interface s \ restrictTypeOffers interface t := by
      intro s t
      apply Finset.ext
      intro action
      simp only [restrictTypeOffers, Finset.mem_filter, Finset.mem_sdiff]
      tauto
    have hRestrictUnion : ∀ s t : Finset BareMessage,
        restrictTypeOffers interface (s ∪ t) =
          restrictTypeOffers interface s ∪ restrictTypeOffers interface t := by
      intro s t
      apply Finset.ext
      intro action
      simp only [restrictTypeOffers, Finset.mem_filter, Finset.mem_union]
      tauto
    obtain ⟨leftTargetResidual, hLeftTargetRelated⟩ :
        ∃ residual, relationMembership
          (buildRelationSet left (compileType signature left)) residual q1' := by
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftResolvedMem
      obtain ⟨rawLeft, hRawLeftMem, hRawLeftEq⟩ := hLeftResolvedMem
      have hRawLeftTarget : rawLeft.target = q1' := congrArg AutomatonFragmentEdge.target
        hRawLeftEq
      rcases buildRelationSetCoreFuel_edge_target_mem signature
          (typeCompilationFuel left) left le_rfl rawLeft hRawLeftMem with
          ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
      · exact ⟨residual, hRawLeftTarget ▸ hResidual⟩
      · exfalso
        have hRawLeftLabel : rawLeft.label = .visible leftLabel :=
          congrArg AutomatonFragmentEdge.label hRawLeftEq
        rw [hRawLeftLabel] at hMarkerLabel
        cases hMarkerLabel
    obtain ⟨rightTargetResidual, hRightTargetRelated⟩ :
        ∃ residual, relationMembership
          (buildRelationSet right (compileType signature right)) residual q2' := by
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightResolvedMem
      obtain ⟨rawRight, hRawRightMem, hRawRightEq⟩ := hRightResolvedMem
      have hRawRightTarget : rawRight.target = q2' := congrArg AutomatonFragmentEdge.target
        hRawRightEq
      rcases buildRelationSetCoreFuel_edge_target_mem signature
          (typeCompilationFuel right) right le_rfl rawRight hRawRightMem with
          ⟨residual, hResidual⟩ | ⟨markerName, hMarkerLabel⟩
      · exact ⟨residual, hRawRightTarget ▸ hResidual⟩
      · exfalso
        have hRawRightLabel : rawRight.label = .visible rightLabel :=
          congrArg AutomatonFragmentEdge.label hRawRightEq
        rw [hRawRightLabel] at hMarkerLabel
        cases hMarkerLabel
    have hLeftFutureEqIf : leftOffers.future =
        if leftLabel = TypeLabel.tock then ∅
        else typeFutureOffers leftTargetResidual \ leftOffers.current :=
      helper_h15_edge_future_offers_agree signature hChildLeftRelated
        hLeftTargetRelated hLeftEdge
    have hRightFutureEqIf : rightOffers.future =
        if rightLabel = TypeLabel.tock then ∅
        else typeFutureOffers rightTargetResidual \ rightOffers.current :=
      helper_h15_edge_future_offers_agree signature hChildRightRelated
        hRightTargetRelated hRightEdge
    -- `Sync` forces the two component labels to agree on tock-ness, so the
    -- two `if`s above are governed by a single case distinction.
    have hTockIff : leftLabel = TypeLabel.tock ↔ rightLabel = TypeLabel.tock := by
      have hIsTock := hSyncCond.2.2
      constructor
      · intro hL
        cases hRightVis : rightLabel with
        | tock => rfl
        | actions obs =>
            exact absurd (hIsTock.mp (by rw [hL]; trivial))
              (by rw [hRightVis]; exact id)
      · intro hR
        cases hLeftVis : leftLabel with
        | tock => rfl
        | actions obs =>
            exact absurd (hIsTock.mpr (by rw [hR]; trivial))
              (by rw [hLeftVis]; exact id)
    -- Holds in both branches of the `if`: `∅` is disjoint from everything.
    have hLeftFutureCurrentDisjoint :
        Disjoint leftOffers.future leftOffers.current := by
      rw [hLeftFutureEqIf]
      split_ifs with hTock
      · exact Finset.disjoint_empty_left _
      · exact Finset.sdiff_disjoint
    have hRightFutureCurrentDisjoint :
        Disjoint rightOffers.future rightOffers.current := by
      rw [hRightFutureEqIf]
      split_ifs with hTock
      · exact Finset.disjoint_empty_left _
      · exact Finset.sdiff_disjoint
    have hRightCurrentSubset : rightOffers.current ⊆ right.alphabet.actions := by
      rw [transitionAlphabetFor_mk_mem_iff] at hRightSymbol
      have := hRightSymbol.2.2
      rw [localOfferSummariesFor_mk_mem_iff] at this
      exact this.1.trans Finset.inter_subset_right
    have hLeftCurrentSubset : leftOffers.current ⊆ left.alphabet.actions := by
      rw [transitionAlphabetFor_mk_mem_iff] at hLeftSymbol
      have := hLeftSymbol.2.2
      rw [localOfferSummariesFor_mk_mem_iff] at this
      exact this.1.trans Finset.inter_subset_right
    have hActionsDisjoint : Disjoint left.alphabet.actions right.alphabet.actions :=
      hParallelCompatible.actions_disjoint
    -- Mirrors the forward direction's identically named facts: a future
    -- action outside a child's own current offer stays in that child's fixed
    -- alphabet, disjoint from the sibling's, so it can't be the sibling's
    -- current offer either.
    have hLeftFutureRightCurrentDisjoint : leftLabel ≠ TypeLabel.tock →
        ∀ action, action ∈ typeFutureOffers leftTargetResidual →
          action ∉ leftOffers.current → action ∉ rightOffers.current := by
      intro hNotTock action hLeftFuture hNotLeftCurrent hRightCurrent
      have hLeftAlph : action ∈ left.alphabet.actions := by
        rw [transitionAlphabetFor_mk_mem_iff] at hLeftSymbol
        rw [localOfferSummariesFor_mk_mem_iff] at hLeftSymbol
        refine (hLeftSymbol.2.2.2.trans Finset.inter_subset_right) ?_
        rw [hLeftFutureEqIf, if_neg hNotTock]
        exact Finset.mem_sdiff.mpr ⟨hLeftFuture, hNotLeftCurrent⟩
      exact Finset.disjoint_left.mp hActionsDisjoint hLeftAlph
        (hRightCurrentSubset hRightCurrent)
    have hRightFutureLeftCurrentDisjoint : rightLabel ≠ TypeLabel.tock →
        ∀ action, action ∈ typeFutureOffers rightTargetResidual →
          action ∉ rightOffers.current → action ∉ leftOffers.current := by
      intro hNotTock action hRightFuture hNotRightCurrent hLeftCurrent
      have hRightAlph : action ∈ right.alphabet.actions := by
        rw [transitionAlphabetFor_mk_mem_iff] at hRightSymbol
        rw [localOfferSummariesFor_mk_mem_iff] at hRightSymbol
        refine (hRightSymbol.2.2.2.trans Finset.inter_subset_right) ?_
        rw [hRightFutureEqIf, if_neg hNotTock]
        exact Finset.mem_sdiff.mpr ⟨hRightFuture, hNotRightCurrent⟩
      exact Finset.disjoint_right.mp hActionsDisjoint hRightAlph
        (hLeftCurrentSubset hLeftCurrent)
    have hSameOnInterface :
        sameOnInterface interface leftOffers.current rightEnv.immediate ∧
        sameOnInterface interface rightOffers.current leftEnv.immediate ∧
        sameOnInterface interface leftOffers.future rightEnv.future ∧
        sameOnInterface interface rightOffers.future leftEnv.future := by
      cases hLocal1 with
      | clock _ =>
        rename_i hOuterClock1
        cases hLocal2 with
        | clock _ =>
          -- `LocalTypeOfferEnvironment.clock` pins both child environments to
          -- `TypeEnvironment.tock`, so all four goals reduce to
          -- `restrictTypeOffers interface c = ∅` for the two children's
          -- `current` and `future`.  `compileTypeFuel_clockEdgesAreTock` is
          -- the automaton-side mirror of `typeOffers_current_empty_of_clock` /
          -- `typeOffers_label_eq_tock_of_clock`: it gives `current = ∅`
          -- directly and `label = tock`, and the latter yields `future = ∅`
          -- through `helper_h15_edge_future_offers_agree_of_tock`.
          have hClockEdges : ∀ (child : PactType) (pending : PendingAutomatonEdge),
              pending ∈ (compileTypeFuel signature
                (typeCompilationFuel child) child).edges →
              pending.environment.clock = true →
                pending.label.semantic = TypeLabel.tock ∧ pending.current = ∅ :=
            fun child => compileTypeFuel_clockEdgesAreTock signature
              (typeCompilationFuel child) child le_rfl
          -- Pull each public child edge back to its pending fragment edge;
          -- resolution preserves environment, label, and current offers.
          have hChildCurrentEmpty : ∀ (child : PactType)
              (q q' : TypeAutomatonState) (childLabel : TypeLabel)
              (childOffers : TypeOfferSummary),
              (compileType signature child).HasEdge q TypeEnvironment.tock
                childLabel childOffers q' →
              childLabel = TypeLabel.tock ∧ childOffers.current = ∅ := by
            intro child q q' childLabel childOffers hChildEdge
            have hChildSymbol :=
              compileType_hasEdge_symbol_mem signature child hChildEdge
            have hResolvedMem :=
              (compileType_hasEdge_iff_resolvedEdge_mem signature child q q'
                TypeEnvironment.tock childLabel childOffers hChildSymbol).mp
                hChildEdge
            simp only [resolveAutomatonEdgesWith, Finset.mem_image]
              at hResolvedMem
            obtain ⟨raw, hRawMem, hRawEq⟩ := hResolvedMem
            have hRawEnv : raw.environment = TypeEnvironment.tock :=
              congrArg AutomatonFragmentEdge.environment hRawEq
            have hRawLabel : raw.label = .visible childLabel :=
              congrArg AutomatonFragmentEdge.label hRawEq
            have hRawCurrent : raw.current = childOffers.current :=
              congrArg AutomatonFragmentEdge.current hRawEq
            obtain ⟨hTock, hEmpty⟩ := hClockEdges child raw hRawMem
              (by rw [hRawEnv]; rfl)
            rw [hRawLabel] at hTock
            rw [hRawCurrent] at hEmpty
            exact ⟨hTock, hEmpty⟩
          obtain ⟨hLeftTock, hLeftCurrentEmpty⟩ :=
            hChildCurrentEmpty left q1 q1' leftLabel leftOffers hLeftEdge
          obtain ⟨hRightTock, hRightCurrentEmpty⟩ :=
            hChildCurrentEmpty right q2 q2' rightLabel rightOffers hRightEdge
          -- A tock-labelled step exposes no future menu.
          have hLeftFutureEmpty : leftOffers.future = ∅ :=
            helper_h15_edge_future_offers_agree_of_tock signature
              hChildLeftRelated hLeftTargetRelated hLeftEdge hLeftTock
          have hRightFutureEmpty : rightOffers.future = ∅ :=
            helper_h15_edge_future_offers_agree_of_tock signature
              hChildRightRelated hRightTargetRelated hRightEdge hRightTock
          refine ⟨?_, ?_, ?_, ?_⟩ <;>
            · show restrictTypeOffers interface _ = restrictTypeOffers interface _
              simp [hLeftCurrentEmpty, hRightCurrentEmpty, hLeftFutureEmpty,
                hRightFutureEmpty, restrictTypeOffers, TypeEnvironment.tock]
        | ordinary _ _ _ _ _ =>
          rename_i hOuterClock2 _ _ _ _
          rw [hOuterClock1] at hOuterClock2
          exact absurd hOuterClock2 (by simp)
      | ordinary _ _ _ _ _ =>
        rename_i hOuterClock1 hSiblingClock1 hLocalClock1 hImmediate1 hFuture1
        cases hLocal2 with
        | clock _ =>
          rename_i hOuterClock2
          rw [hOuterClock2] at hOuterClock1
          exact absurd hOuterClock1 (by simp)
        | ordinary _ _ _ _ _ =>
          rename_i hOuterClock2 hSiblingClock2 hLocalClock2 hImmediate2 hFuture2
          have hCur1 : sameOnInterface interface leftOffers.current rightEnv.immediate := by
            show restrictTypeOffers interface leftOffers.current =
              restrictTypeOffers interface rightEnv.immediate
            rw [hImmediate2, hRestrictUnion,
              hProjectDrop right.alphabet env.immediate hEnvMemSet.1, Finset.empty_union,
              hRestrictIdem]
          have hCur2 : sameOnInterface interface rightOffers.current leftEnv.immediate := by
            show restrictTypeOffers interface rightOffers.current =
              restrictTypeOffers interface leftEnv.immediate
            rw [hImmediate1, hRestrictUnion,
              hProjectDrop left.alphabet env.immediate hEnvMemSet.1, Finset.empty_union,
              hRestrictIdem]
          have hCur1' : restrictTypeOffers interface leftOffers.current =
              restrictTypeOffers interface rightEnv.immediate := hCur1
          have hCur2' : restrictTypeOffers interface rightOffers.current =
              restrictTypeOffers interface leftEnv.immediate := hCur2
          refine ⟨hCur1, hCur2, ?_, ?_⟩
          · show restrictTypeOffers interface leftOffers.future =
              restrictTypeOffers interface rightEnv.future
            have hDisjoint : Disjoint (restrictTypeOffers interface leftOffers.future)
                (restrictTypeOffers interface leftOffers.current) := by
              have hFull : Disjoint leftOffers.future leftOffers.current :=
                hLeftFutureCurrentDisjoint
              exact (hFull.mono_left (Finset.filter_subset _ _)).mono_right
                (Finset.filter_subset _ _)
            rw [hFuture2, hRestrictSdiff, hRestrictUnion,
              hProjectDrop right.alphabet env.future hEnvMemSet.2, Finset.empty_union,
              hRestrictIdem, ← hCur1', Finset.sdiff_eq_self_of_disjoint hDisjoint]
          · show restrictTypeOffers interface rightOffers.future =
              restrictTypeOffers interface leftEnv.future
            have hDisjoint : Disjoint (restrictTypeOffers interface rightOffers.future)
                (restrictTypeOffers interface rightOffers.current) := by
              have hFull : Disjoint rightOffers.future rightOffers.current :=
                hRightFutureCurrentDisjoint
              exact (hFull.mono_left (Finset.filter_subset _ _)).mono_right
                (Finset.filter_subset _ _)
            rw [hFuture1, hRestrictSdiff, hRestrictUnion,
              hProjectDrop left.alphabet env.future hEnvMemSet.2, Finset.empty_union,
              hRestrictIdem, ← hCur2', Finset.sdiff_eq_self_of_disjoint hDisjoint]
    obtain ⟨hSame1, hSame2, hSame3, hSame4⟩ := hSameOnInterface
    have hSyncEdges : syncAutomatonEdges signature left.alphabet right.alphabet interface
        ({ source := q1, environment := leftEnv, label := .visible leftLabel,
            current := leftOffers.current, future := leftOffers.future,
            target := q1' } : AutomatonFragmentEdge)
        ({ source := q2, environment := rightEnv, label := .visible rightLabel,
            current := rightOffers.current, future := rightOffers.future,
            target := q2' } : AutomatonFragmentEdge) := by
      exact ⟨hLeftSymbol, hRightSymbol, hEnvEq ▸ hAutoLocal1, hEnvEq ▸ hAutoLocal2,
        hSame1, hSame2, hSame3, hSame4, hSyncCond⟩
    set leftEdge' : AutomatonFragmentEdge :=
      { source := q1, environment := leftEnv,
        label := AutomatonConstructionLabel.visible leftLabel, current := leftOffers.current,
        future := leftOffers.future, target := q1' } with hLeftEdgeDef
    set rightEdge' : AutomatonFragmentEdge :=
      { source := q2, environment := rightEnv,
        label := AutomatonConstructionLabel.visible rightLabel, current := rightOffers.current,
        future := rightOffers.future, target := q2' } with hRightEdgeDef
    have hLeftEdgeMem : leftEdge' ∈
        resolveAutomatonEdgesWith (compileTypeFuel signature (typeCompilationFuel left) left)
          (computeFutureOf signature left) := hLeftResolvedMem
    have hRightEdgeMem : rightEdge' ∈
        resolveAutomatonEdgesWith (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature right) := hRightResolvedMem
    have hBothAccept :
        q1' ∈ (compileType signature left).accepting ∧
          q2' ∈ (compileType signature right).accepting ↔
        target = TypeAutomatonState.final := by
      by_cases hAccept : q1' ∈ (compileType signature left).accepting ∧
          q2' ∈ (compileType signature right).accepting
      · rw [if_pos hAccept] at hRedirect
        simp [hAccept, hRedirect]
      · rw [if_neg hAccept] at hRedirect
        simp only [hAccept, false_iff]
        rw [hRedirect]
        intro hEq
        cases hEq
    let combinedLabel := AutomatonConstructionLabel.combine interface
      (AutomatonConstructionLabel.visible leftLabel)
      (AutomatonConstructionLabel.visible rightLabel)
    let combinedCurrent :=
      hideOffers interface (leftOffers.current ∪ rightOffers.current)
    set rawEdge : PendingAutomatonEdge :=
      { source := TypeAutomatonState.pair q1 q2
        environment := combineAutomatonEnvironment interface leftEnv rightEnv
        label := combinedLabel
        current := combinedCurrent
        future := parallelFutureSpec combinedLabel target combinedCurrent
        target := target } with hRawEdgeDef
    have hRawMem : rawEdge ∈
        parallelRawTransitionEdges signature left.alphabet right.alphabet interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left) (computeFutureOf signature right) := by
      rw [hRawEdgeDef]
      simp only [parallelRawTransitionEdges, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_filter]
      have hAcceptEqLeft : (compileTypeFuel signature (typeCompilationFuel left) left).accepting
          = (compileType signature left).accepting := compileType_accepting_eq signature _
      have hAcceptEqRight :
          (compileTypeFuel signature (typeCompilationFuel right) right).accepting
            = (compileType signature right).accepting := compileType_accepting_eq signature _
      refine ⟨_, hLeftEdgeMem, _, ⟨hRightEdgeMem, hSyncEdges, ?_⟩, ?_⟩
      · intro hNotBoth
        rw [hAcceptEqLeft, hAcceptEqRight]
        exact hSrcLive (by rw [← hAcceptEqLeft, ← hAcceptEqRight]; exact hNotBoth)
      by_cases hAccept : q1' ∈ (compileType signature left).accepting ∧
          q2' ∈ (compileType signature right).accepting
      · rw [← (hBothAccept.mp hAccept)]
        simp [combinedLabel, combinedCurrent, hAccept, hLeftEdgeDef,
          hRightEdgeDef, hAcceptEqLeft, hAcceptEqRight]
      · have hTargetEq : target = TypeAutomatonState.pair q1' q2' := by
          rw [if_neg hAccept] at hRedirect; exact hRedirect
        rw [← hTargetEq]
        simp [combinedLabel, combinedCurrent, hLeftEdgeDef, hRightEdgeDef,
          hAcceptEqLeft, hAcceptEqRight, hAccept]
    have hTransitionMem : rawEdge ∈
        (buildParallelAutomaton signature alphabet left.alphabet right.alphabet interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left) (computeFutureOf signature right)).edges := by
      simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union]
      left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hRawMem))), hReach⟩
    rw [compileType_hasEdge_iff_resolvedEdge_mem signature (.par alphabet left right interface)
      (.pair q1 q2) target env label offers hSymbol]
    rw [hWhole]
    simp only [resolveAutomatonEdgesWith, Finset.mem_image]
    refine ⟨_, hTransitionMem, ?_⟩
    have hEnvCombine : env = combineAutomatonEnvironment interface leftEnv rightEnv := hEnvEq
    have hLabelCombine : label = TypeLabel.combine interface leftLabel rightLabel := hLabelEq
    have hCurrentCombine : offers.current =
        hideOffers interface (leftOffers.current ∪ rightOffers.current) := by
      rw [hCurrentEq]; rfl
    by_cases hTockL : leftLabel = TypeLabel.tock
    · -- Tock edges carry an explicit empty future on both the component
      -- edges and the compiled product edge.
      have hTockR : rightLabel = TypeLabel.tock := hTockIff.mp hTockL
      have hLeftEmpty : leftOffers.future = ∅ := by
        rw [hLeftFutureEqIf, if_pos hTockL]
      have hRightEmpty : rightOffers.future = ∅ := by
        rw [hRightFutureEqIf, if_pos hTockR]
      have hOffersEmpty : offers.future = ∅ := by
        rw [hFutureEq, hLeftEmpty, hRightEmpty]
        simp [hideTypeOffers, hideOffers]
      have hVisibleTock :
          (AutomatonConstructionLabel.visible
            (TypeLabel.combine interface leftLabel rightLabel)).semantic =
            TypeLabel.tock := by
        rw [hTockL, hTockR]
        simp [AutomatonConstructionLabel.semantic, TypeLabel.combine]
      rw [hRawEdgeDef]
      simp only [hEnvCombine, hLabelCombine, hCurrentCombine]
      simp [parallelFutureSpec, hVisibleTock, hOffersEmpty, combinedLabel,
        combinedCurrent, AutomatonConstructionLabel.combine]
    have hTockR : ¬ rightLabel = TypeLabel.tock := fun h => hTockL (hTockIff.mpr h)
    have hLeftFutureEq : leftOffers.future =
        typeFutureOffers leftTargetResidual \ leftOffers.current := by
      rw [hLeftFutureEqIf, if_neg hTockL]
    have hRightFutureEq : rightOffers.future =
        typeFutureOffers rightTargetResidual \ rightOffers.current := by
      rw [hRightFutureEqIf, if_neg hTockR]
    have hVisibleNotTock :
        ¬ (AutomatonConstructionLabel.visible
          (TypeLabel.combine interface leftLabel rightLabel)).semantic =
          TypeLabel.tock := by
      cases hLeftVis : leftLabel with
      | tock => exact absurd hLeftVis hTockL
      | actions leftObs =>
          cases hRightVis : rightLabel with
          | tock => exact absurd hRightVis hTockR
          | actions rightObs =>
              simp [AutomatonConstructionLabel.semantic, TypeLabel.combine]
    have hFutureResolved :
        computeFutureOf signature (.par alphabet left right interface) target \
          hideOffers interface (leftOffers.current ∪ rightOffers.current) = offers.future := by
      rw [hFutureEq]
      have hParFutureEq :
          computeFutureOf signature (.par alphabet left right interface) target =
          hideTypeOffers interface
            (typeFutureOffers leftTargetResidual ∪ typeFutureOffers rightTargetResidual) := by
        by_cases hAccept : q1' ∈ (compileType signature left).accepting ∧
            q2' ∈ (compileType signature right).accepting
        · have hParTargetRelated := relationMembership_par_final signature alphabet
            left right interface
          rw [hBothAccept.mp hAccept]
          rw [helper_h15_future_offers_agree signature hParTargetRelated]
          obtain ⟨leftAlph, hLeftMem'⟩ :=
            relationMembership_of_accepting signature left hAccept.1
          obtain ⟨rightAlph, hRightMem'⟩ :=
            relationMembership_of_accepting signature right hAccept.2
          have hLeftSkip : leftTargetResidual = .skip leftAlph :=
            relationMembership_functional left (compileType signature left)
              hLeftTargetRelated hLeftMem'
          have hRightSkip : rightTargetResidual = .skip rightAlph :=
            relationMembership_functional right (compileType signature right)
              hRightTargetRelated hRightMem'
          rw [hLeftSkip, hRightSkip]
          simp [typeFutureOffers, typeFutureOffersFuel, hideTypeOffers, PactType.alphabet]
        · have hTargetEq : target = TypeAutomatonState.pair q1' q2' := by
            rw [if_neg hAccept] at hRedirect; exact hRedirect
          have hReachTarget :
              ParallelReachable signature alphabet left.alphabet right.alphabet interface
                (compileTypeFuel signature (typeCompilationFuel left) left)
                (compileTypeFuel signature (typeCompilationFuel right) right)
                (computeFutureOf signature left) (computeFutureOf signature right)
                (.pair q1' q2') := by
            rw [← hTargetEq]
            exact hReach.target_of_rawTransition hRawMem
          have hParTargetRelated := relationMembership_par_pair signature alphabet
            left right interface hLeftTargetRelated hRightTargetRelated hReachTarget
          rw [hTargetEq,
            helper_h15_future_offers_agree signature hParTargetRelated,
            typeFutureOffers_parallel]
      rw [hParFutureEq]
      apply Finset.ext
      intro action
      simp only [hideTypeOffers, hideOffers, Finset.mem_filter, Finset.mem_sdiff,
        Finset.mem_union]
      rw [hLeftFutureEq, hRightFutureEq]
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨⟨(hL | hR), hInterface⟩, hNotCur⟩
        · refine ⟨Or.inl ⟨hL, ?_⟩, hInterface⟩
          intro hLCur
          exact hNotCur ⟨Or.inl hLCur, hInterface⟩
        · refine ⟨Or.inr ⟨hR, ?_⟩, hInterface⟩
          intro hRCur
          exact hNotCur ⟨Or.inr hRCur, hInterface⟩
      · rintro ⟨(⟨hL, hLNotCur⟩ | ⟨hR, hRNotCur⟩), hInterface⟩
        · refine ⟨⟨Or.inl hL, hInterface⟩, ?_⟩
          rintro ⟨hCur | hCur, -⟩
          · exact hLNotCur hCur
          · exact hLeftFutureRightCurrentDisjoint hTockL action hL hLNotCur hCur
        · refine ⟨⟨Or.inr hR, hInterface⟩, ?_⟩
          rintro ⟨hCur | hCur, -⟩
          · exact hRightFutureLeftCurrentDisjoint hTockR action hR hRNotCur hCur
          · exact hRNotCur hCur
    rw [hRawEdgeDef]
    simp only [hEnvCombine, hLabelCombine, hCurrentCombine]
    have hResolved :
        (match parallelFutureSpec combinedLabel target combinedCurrent with
          | FutureSpec.explicit offers => offers
          | FutureSpec.at state removed =>
              computeFutureOf signature (.par alphabet left right interface)
                state \ removed) = offers.future := by
      simp only [parallelFutureSpec, combinedLabel,
        AutomatonConstructionLabel.combine, if_neg hVisibleNotTock]
      simpa [combinedCurrent] using hFutureResolved
    simpa [combinedLabel, combinedCurrent,
      AutomatonConstructionLabel.combine] using hResolved

private theorem union_subset_union_union
    {alpha : Type} [DecidableEq alpha]
    {left' right' left right replacement : Finset alpha}
    (hLeft : left' ⊆ left ∪ replacement)
    (hRight : right' ⊆ right ∪ replacement) :
    left' ∪ right' ⊆ (left ∪ right) ∪ replacement := by
  intro item hItem
  simp only [Finset.mem_union] at hItem ⊢
  rcases hItem with hItem | hItem
  · rcases Finset.mem_union.mp (hLeft hItem) with hItem | hItem
    · exact Or.inl (Or.inl hItem)
    · exact Or.inr hItem
  · rcases Finset.mem_union.mp (hRight hItem) with hItem | hItem
    · exact Or.inl (Or.inr hItem)
    · exact Or.inr hItem

private theorem insert_union_subset_insert_union_union
    {alpha : Type} [DecidableEq alpha]
    (head : alpha) {left' right' left right replacement : Finset alpha}
    (hLeft : left' ⊆ left ∪ replacement)
    (hRight : right' ⊆ right ∪ replacement) :
    {head} ∪ left' ∪ right' ⊆
      {head} ∪ left ∪ right ∪ replacement := by
  intro item hItem
  simp only [Finset.mem_singleton, Finset.mem_union] at hItem ⊢
  rcases hItem with (rfl | hItem) | hItem
  · exact Or.inl (Or.inl (Or.inl rfl))
  · rcases Finset.mem_union.mp (hLeft hItem) with hItem | hItem
    · exact Or.inl (Or.inl (Or.inr hItem))
    · exact Or.inr hItem
  · rcases Finset.mem_union.mp (hRight hItem) with hItem | hItem
    · exact Or.inl (Or.inr hItem)
    · exact Or.inr hItem

/-- Substitution can introduce only observables already present in the
substituted syntax or in the replacement. -/
private theorem replaceVar_footprintWithinReplacement
    (name : String) (replacement : PactType) :
    ∀ processType,
      footprintWithinReplacement
        (processType.replaceVar name replacement) processType replacement := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          branchFootprintWithinReplacement
            (PactType.replaceBranches branches name replacement)
            branches replacement := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            simp [branchFootprintWithinReplacement, PactType.replaceBranches,
              PactType.BranchMessageIds, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have hTail : sizeOf rest < sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hBranch := ih (sizeOf branchType) hBranchSize branchType rfl
            have hRest := restIH hRestSize
            simp only [PactType.replaceBranches, branchFootprintWithinReplacement,
              PactType.BranchMessageIds,
              PactType.BranchMessageActions, PactType.BranchProgressIds,
              PactType.BranchFairChoiceIds] at hRest ⊢
            exact ⟨insert_union_subset_insert_union_union action.1
                hBranch.1 hRest.1,
              insert_union_subset_insert_union_union action
                hBranch.2.1 hRest.2.1,
              union_subset_union_union hBranch.2.2.1 hRest.2.2.1,
              union_subset_union_union hBranch.2.2.2 hRest.2.2.2⟩
      cases processType with
      | message _ msg dir | progress _ msg | tock _ | skip _ =>
          simp [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds]
      | var _ other =>
          by_cases hName : name = other
          · subst other
            simp [footprintWithinReplacement, PactType.replaceVar,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
          · simp [footprintWithinReplacement, PactType.replaceVar, hName,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
      | recur _ binder body =>
          by_cases hName : name = binder
          · subst binder
            simp [footprintWithinReplacement, PactType.replaceVar,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
          · have hBodySize : sizeOf body < n := by
              rw [← hSize]; simp_wf; omega
            simpa [footprintWithinReplacement, PactType.replaceVar, hName,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using
              ih (sizeOf body) hBodySize body rfl
      | choice _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hLeftSize left rfl
          have hRight := ih (sizeOf right) hRightSize right rfl
          simp only [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds] at hLeft hRight ⊢
          exact ⟨union_subset_union_union hLeft.1 hRight.1,
            union_subset_union_union hLeft.2.1 hRight.2.1,
            union_subset_union_union hLeft.2.2.1 hRight.2.2.1,
            union_subset_union_union hLeft.2.2.2 hRight.2.2.2⟩
      | fairChoice _ bid left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hLeftSize left rfl
          have hRight := ih (sizeOf right) hRightSize right rfl
          simp only [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds] at hLeft hRight ⊢
          exact ⟨union_subset_union_union hLeft.1 hRight.1,
            union_subset_union_union hLeft.2.1 hRight.2.1,
            union_subset_union_union hLeft.2.2.1 hRight.2.2.1,
            insert_union_subset_insert_union_union bid
              hLeft.2.2.2 hRight.2.2.2⟩
      | seq _ left right =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hLeftSize left rfl
          have hRight := ih (sizeOf right) hRightSize right rfl
          simp only [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds] at hLeft hRight ⊢
          exact ⟨union_subset_union_union hLeft.1 hRight.1,
            union_subset_union_union hLeft.2.1 hRight.2.1,
            union_subset_union_union hLeft.2.2.1 hRight.2.2.1,
            union_subset_union_union hLeft.2.2.2 hRight.2.2.2⟩
      | par _ left right interface =>
          have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          have hLeft := ih (sizeOf left) hLeftSize left rfl
          have hRight := ih (sizeOf right) hRightSize right rfl
          simp only [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds] at hLeft hRight ⊢
          exact ⟨union_subset_union_union hLeft.1 hRight.1,
            union_subset_union_union hLeft.2.1 hRight.2.1,
            union_subset_union_union hLeft.2.2.1 hRight.2.2.1,
            union_subset_union_union hLeft.2.2.2 hRight.2.2.2⟩
      | xoffer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          have hElse := ih (sizeOf elseType) hElseSize elseType rfl
          have hBranch := hBranches branches hBranchesSize
          simp only [footprintWithinReplacement, branchFootprintWithinReplacement,
            PactType.replaceVar, PactType.MessageIds, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds] at hElse hBranch ⊢
          exact ⟨union_subset_union_union hElse.1 hBranch.1,
            union_subset_union_union hElse.2.1 hBranch.2.1,
            union_subset_union_union hElse.2.2.1 hBranch.2.2.1,
            union_subset_union_union hElse.2.2.2 hBranch.2.2.2⟩
      | offer _ elseType branches =>
          have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchesSize : sizeOf branches < n := by rw [← hSize]; simp_wf; omega
          have hElse := ih (sizeOf elseType) hElseSize elseType rfl
          have hBranch := hBranches branches hBranchesSize
          simp only [footprintWithinReplacement, branchFootprintWithinReplacement,
            PactType.replaceVar, PactType.MessageIds, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds] at hElse hBranch ⊢
          exact ⟨union_subset_union_union hElse.1 hBranch.1,
            union_subset_union_union hElse.2.1 hBranch.2.1,
            union_subset_union_union hElse.2.2.1 hBranch.2.2.1,
            union_subset_union_union hElse.2.2.2 hBranch.2.2.2⟩

private def footprintSubset (result original : PactType) : Prop :=
  result.MessageIds ⊆ original.MessageIds ∧
  result.MessageActions ⊆ original.MessageActions ∧
  result.ProgressIds ⊆ original.ProgressIds ∧
  result.FairChoiceIds ⊆ original.FairChoiceIds

private theorem branchType_footprintSubset
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hMem : (action, branchType) ∈ branches) :
    branchType.MessageIds ⊆ PactType.BranchMessageIds branches ∧
    branchType.MessageActions ⊆ PactType.BranchMessageActions branches ∧
    branchType.ProgressIds ⊆ PactType.BranchProgressIds branches ∧
    branchType.FairChoiceIds ⊆ PactType.BranchFairChoiceIds branches := by
  induction branches with
  | nil => cases hMem
  | cons head rest ih =>
      rcases head with ⟨headAction, headType⟩
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hMem
      · cases hEq
        simp only [PactType.BranchMessageIds, PactType.BranchMessageActions,
          PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
        constructor
        · exact fun item hItem => by simp [hItem]
        constructor
        · exact fun item hItem => by simp [hItem]
        constructor <;> exact fun item hItem => by simp [hItem]
      · obtain ⟨hIds, hActions, hProgress, hFair⟩ := ih hMem
        simp only [PactType.BranchMessageIds, PactType.BranchMessageActions,
          PactType.BranchProgressIds, PactType.BranchFairChoiceIds]
        exact ⟨hIds.trans Finset.subset_union_right,
          hActions.trans Finset.subset_union_right,
          hProgress.trans Finset.subset_union_right,
          hFair.trans Finset.subset_union_right⟩

private theorem footprintSubset_left
    {result left right : PactType}
    (h : footprintSubset result left) :
    result.MessageIds ⊆ left.MessageIds ∪ right.MessageIds ∧
    result.MessageActions ⊆ left.MessageActions ∪ right.MessageActions ∧
    result.ProgressIds ⊆ left.ProgressIds ∪ right.ProgressIds ∧
    result.FairChoiceIds ⊆ left.FairChoiceIds ∪ right.FairChoiceIds :=
  ⟨h.1.trans Finset.subset_union_left,
    h.2.1.trans Finset.subset_union_left,
    h.2.2.1.trans Finset.subset_union_left,
    h.2.2.2.trans Finset.subset_union_left⟩

private theorem footprintSubset_right
    {result left right : PactType}
    (h : footprintSubset result right) :
    result.MessageIds ⊆ left.MessageIds ∪ right.MessageIds ∧
    result.MessageActions ⊆ left.MessageActions ∪ right.MessageActions ∧
    result.ProgressIds ⊆ left.ProgressIds ∪ right.ProgressIds ∧
    result.FairChoiceIds ⊆ left.FairChoiceIds ∪ right.FairChoiceIds :=
  ⟨h.1.trans Finset.subset_union_right,
    h.2.1.trans Finset.subset_union_right,
    h.2.2.1.trans Finset.subset_union_right,
    h.2.2.2.trans Finset.subset_union_right⟩

/-- A relation residual contains no observable identifier absent from its
source type. -/
private theorem buildRelationSetCoreFuel_footprintSubset
    (signature : TypeAlphabet) :
    ∀ fuel source residual state,
      (residual, state) ∈ buildRelationSetCoreFuel signature fuel source →
      footprintSubset residual source := by
  intro fuel
  induction fuel with
  | zero =>
      intro source residual state hMem
      simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
        Prod.mk.injEq] at hMem
      rw [hMem.1]
      exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
        Finset.Subset.rfl, Finset.Subset.rfl⟩
  | succ fuel ih =>
      intro source residual state hMem
      cases source with
      | skip _ | var _ _ =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at hMem
          rw [hMem.1]
          exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
            Finset.Subset.rfl, Finset.Subset.rfl⟩
      | message _ msg dir | progress _ msg | tock _ =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · simp [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
      | choice _ left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩ |
              ⟨entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · simpa [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using
              footprintSubset_left (right := right) (ih left entry.1 entry.2 hEntry)
          · simpa [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using
              footprintSubset_right (left := left) (ih right entry.1 entry.2 hEntry)
      | fairChoice _ bid left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩ |
              ⟨entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · have h := footprintSubset_left (right := right)
                (ih left entry.1 entry.2 hEntry)
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at h ⊢
            exact ⟨h.1, h.2.1, h.2.2.1,
              h.2.2.2.trans (by simp)⟩
          · have h := footprintSubset_right (left := left)
                (ih right entry.1 entry.2 hEntry)
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at h ⊢
            exact ⟨h.1, h.2.1, h.2.2.1,
              h.2.2.2.trans (by simp)⟩
      | seq _ left right =>
          simp only [buildRelationSetCoreFuel, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hMem
          rcases hMem with ⟨entry, ⟨hEntry, -⟩, rfl, -⟩ |
              ⟨entry, hEntry, rfl, -⟩
          · have h := ih left entry.1 entry.2 hEntry
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at h ⊢
            exact ⟨Finset.union_subset_union h.1 Finset.Subset.rfl,
              Finset.union_subset_union h.2.1 Finset.Subset.rfl,
              Finset.union_subset_union h.2.2.1 Finset.Subset.rfl,
              Finset.union_subset_union h.2.2.2 Finset.Subset.rfl⟩
          · simpa [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using
              footprintSubset_right (left := left) (ih right entry.1 entry.2 hEntry)
      | par _ left right interface =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | (⟨entry, hEntry, rfl, -⟩ |
              ⟨entry, hEntry, rfl, -⟩) | ⟨entry, hEntry, rfl, -⟩
          · simp [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
          · obtain ⟨hProduct, _hReachable⟩ := hEntry
            obtain ⟨hLeftEntry, hRightEntry⟩ := Finset.mem_product.mp hProduct
            have hLeft := ih left entry.1.1 entry.1.2 hLeftEntry
            have hRight := ih right entry.2.1 entry.2.2 hRightEntry
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at hLeft hRight ⊢
            exact ⟨Finset.union_subset_union hLeft.1 hRight.1,
              Finset.union_subset_union hLeft.2.1 hRight.2.1,
              Finset.union_subset_union hLeft.2.2.1 hRight.2.2.1,
              Finset.union_subset_union hLeft.2.2.2 hRight.2.2.2⟩
          · -- A surviving left residual keeps its own footprint under
            -- reannotation.
            have hLeft := ih left entry.1 entry.2 hEntry.1
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.messageIds_reannotate,
              PactType.messageActions_reannotate,
              PactType.progressIds_reannotate,
              PactType.fairChoiceIds_reannotate] at hLeft ⊢
            exact ⟨hLeft.1.trans Finset.subset_union_left,
              hLeft.2.1.trans Finset.subset_union_left,
              hLeft.2.2.1.trans Finset.subset_union_left,
              hLeft.2.2.2.trans Finset.subset_union_left⟩
          · have hRight := ih right entry.1 entry.2 hEntry.1
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.messageIds_reannotate,
              PactType.messageActions_reannotate,
              PactType.progressIds_reannotate,
              PactType.fairChoiceIds_reannotate] at hRight ⊢
            exact ⟨hRight.1.trans Finset.subset_union_right,
              hRight.2.1.trans Finset.subset_union_right,
              hRight.2.2.1.trans Finset.subset_union_right,
              hRight.2.2.2.trans Finset.subset_union_right⟩
      | recur alphabet name body =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · have hChild := ih body entry.1 entry.2 hEntry
            have hReplace := replaceVar_footprintWithinReplacement
              name (.recur alphabet name body) entry.1
            simp only [footprintSubset, footprintWithinReplacement,
              PactType.MessageIds, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds] at hChild hReplace ⊢
            exact ⟨hReplace.1.trans
                (Finset.union_subset hChild.1 Finset.Subset.rfl),
              hReplace.2.1.trans
                (Finset.union_subset hChild.2.1 Finset.Subset.rfl),
              hReplace.2.2.1.trans
                (Finset.union_subset hChild.2.2.1 Finset.Subset.rfl),
              hReplace.2.2.2.trans
                (Finset.union_subset hChild.2.2.2 Finset.Subset.rfl)⟩
      | xoffer alphabet elseType branches =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, mem_foldl_union_iff, Finset.notMem_empty,
            false_or, Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩ |
              ⟨item, hItem, entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · simpa [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using footprintSubset_left
                (right := PactType.offer alphabet (.skip alphabet) branches)
                (ih elseType entry.1 entry.2 hEntry)
          · have hFields := List.mem_zipIdx hItem
            simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
            obtain ⟨hBound, hValue⟩ := hFields
            have hBranchMem : item.1 ∈ branches := by
              have h := List.getElem_mem hBound
              simpa [hValue] using h
            have hBranch := branchType_footprintSubset hBranchMem
            have hChild := ih item.1.2 entry.1 entry.2 hEntry
            simp only [footprintSubset] at hChild
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at ⊢
            exact ⟨(hChild.1.trans hBranch.1).trans Finset.subset_union_right,
              (hChild.2.1.trans hBranch.2.1).trans Finset.subset_union_right,
              (hChild.2.2.1.trans hBranch.2.2.1).trans Finset.subset_union_right,
              (hChild.2.2.2.trans hBranch.2.2.2).trans Finset.subset_union_right⟩
      | offer alphabet elseType branches =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, mem_foldl_union_iff, Finset.notMem_empty,
            false_or, Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩ |
              ⟨item, hItem, entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · simpa [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] using footprintSubset_left
                (right := PactType.offer alphabet (.skip alphabet) branches)
                (ih elseType entry.1 entry.2 hEntry)
          · have hChild := ih (parallelTypeBranchesSelecting item.1 branches)
                entry.1 entry.2 hEntry
            simp only [footprintSubset,
              parallelTypeBranchesSelecting_messageIds,
              parallelTypeBranchesSelecting_messageActions,
              parallelTypeBranchesSelecting_progressIds,
              parallelTypeBranchesSelecting_fairChoiceIds] at hChild
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at ⊢
            exact ⟨hChild.1.trans Finset.subset_union_right,
              hChild.2.1.trans Finset.subset_union_right,
              hChild.2.2.1.trans Finset.subset_union_right,
              hChild.2.2.2.trans Finset.subset_union_right⟩

/-- A residual related to a compiled state cannot introduce a message action
absent from the source type. -/
theorem relationMembership_messageActions_subset
    (signature : TypeAlphabet) (source : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet source (compileType signature source)) residual state) :
    residual.MessageActions ⊆ source.MessageActions := by
  exact (buildRelationSetCoreFuel_footprintSubset signature
    (typeCompilationFuel source) source residual state hRelated).2.1

/-- One semantic step cannot introduce a polarized message action that was
absent from its source syntax. -/
private theorem typeTransition_target_messageActions_subset
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    (hTransition : TypeTransition env source label target) :
    target.MessageActions ⊆ source.MessageActions := by
  induction hTransition with
  | action | action_wait | cycle | cycle_wait | skip | progress =>
      simp [PactType.MessageActions]
  | choice_left | choice_right | fair_left | fair_right =>
      simp [PactType.MessageActions]
  | recur env alphabet name body hWF =>
      have hReplace := replaceVar_footprintWithinReplacement name
        (.recur alphabet name body) body
      simp only [footprintWithinReplacement, PactType.MessageActions] at hReplace
      simpa [PactType.MessageActions] using
        hReplace.2.1.trans (Finset.union_subset Finset.Subset.rfl
          Finset.Subset.rfl)
  | seq_fuse env alphabet skipAlphabet left right label hChild ih =>
      simpa [PactType.MessageActions] using
        (Finset.subset_union_right :
          right.MessageActions ⊆ left.MessageActions ∪ right.MessageActions)
  | seq env alphabet left leftTarget right label hChild hNotSkip ih =>
      simpa [PactType.MessageActions] using
        Finset.union_subset_union ih Finset.Subset.rfl
  | xoffer_branch env alphabet elseType branches action branchType hConditions =>
      have hBranch := branchType_footprintSubset hConditions.2.1
      simpa [PactType.MessageActions] using
        hBranch.2.1.trans Finset.subset_union_right
  | xoffer_else env alphabet elseType branches hConditions =>
      simpa [PactType.MessageActions] using
        (Finset.subset_union_left : elseType.MessageActions ⊆
          elseType.MessageActions ∪ PactType.BranchMessageActions branches)
  | offer_else env alphabet elseType branches hConditions =>
      simpa [PactType.MessageActions] using
        (Finset.subset_union_left : elseType.MessageActions ⊆
          elseType.MessageActions ∪ PactType.BranchMessageActions branches)
  | xoffer_wait | offer_wait =>
      exact Finset.Subset.rfl
  | offer_some env alphabet elseType branches enabled hConditions =>
      rw [parallelTypeBranchesSelecting_messageActions]
      simpa [PactType.MessageActions] using
        (Finset.subset_union_right : PactType.BranchMessageActions branches ⊆
          elseType.MessageActions ∪ PactType.BranchMessageActions branches)
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hLeftOffers hRight hRightOffers hNonFinal hSide hLeftIH
      hRightIH =>
      simpa [PactType.MessageActions] using
        Finset.union_subset_union hLeftIH hRightIH
  | left_complete outer interface leftT rightT survivor rightLabel rightCurrent
      rightFuture hLeftSkip _ hRightTrans hRightOffers hNotSkip hRC hRF hWF
      ihRight =>
      intro action hAction
      rw [PactType.messageActions_reannotate] at hAction
      simp only [PactType.MessageActions]
      exact Finset.mem_union.mpr (Or.inr (ihRight hAction))
  | right_complete outer interface leftT survivor rightT leftLabel leftCurrent
      leftFuture hRightSkip _ hLeftTrans hLeftOffers hNotSkip hLC hLF hWF
      ihLeft =>
      intro action hAction
      rw [PactType.messageActions_reannotate] at hAction
      simp only [PactType.MessageActions]
      exact Finset.mem_union.mpr (Or.inl (ihLeft hAction))
  | par_fuse =>
      simp [PactType.MessageActions]

private theorem typeBranchActions_subset_branchMessageActions
    (branches : List (BareMessage × PactType)) :
    typeBranchActions branches ⊆ PactType.BranchMessageActions branches := by
  induction branches with
  | nil => simp [typeBranchActions, PactType.BranchMessageActions]
  | cons head rest ih =>
      intro action hAction
      simp only [typeBranchActions, List.map_cons, List.toFinset_cons,
        Finset.mem_insert] at hAction
      rw [PactType.BranchMessageActions.eq_def]
      rcases hAction with hHead | hRest
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl (by simpa [hHead]))))
      · exact Finset.mem_union.mpr (Or.inr (ih hRest))

private theorem branchAction_mem_branchMessageActions
    {branches : List (BareMessage × PactType)}
    {action : BareMessage} {branchType : PactType}
    (hMem : (action, branchType) ∈ branches) :
    action ∈ PactType.BranchMessageActions branches := by
  apply typeBranchActions_subset_branchMessageActions branches
  simp only [typeBranchActions, List.mem_toFinset, List.mem_map]
  exact ⟨(action, branchType), hMem, rfl⟩

/-- The current offer of a semantic step is owned by the step's source
syntax. -/
private theorem typeOffers_current_subset_messageActions
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    current ⊆ source.MessageActions := by
  induction hOffers using TypeOffers.rec with
  | action => simp [PactType.MessageActions]
  | action_wait => simp [PactType.MessageActions]
  | choice_left | choice_right | fair_left | fair_right |
      cycle | cycle_wait | skip | progress | recur | offer_some =>
      simp [PactType.MessageActions]
  | seq env alphabet left leftTarget right label current childFuture
      hChild hNotSkip hNotTock ih =>
      simpa [PactType.MessageActions] using
        ih.trans (Finset.subset_union_left :
          left.MessageActions ⊆ left.MessageActions ∪ right.MessageActions)
  | seq_tock env alphabet left leftTarget right current childFuture
      hChild hNotSkip ih =>
      simpa [PactType.MessageActions] using
        ih.trans (Finset.subset_union_left :
          left.MessageActions ⊆ left.MessageActions ∪ right.MessageActions)
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hChild hNotTock ih =>
      simpa [PactType.MessageActions] using
        ih.trans (Finset.subset_union_left :
          left.MessageActions ⊆ left.MessageActions ∪ right.MessageActions)
  | seq_fuse_tock env alphabet skipAlphabet left right current childFuture
      hChild ih =>
      simpa [PactType.MessageActions] using
        ih.trans (Finset.subset_union_left :
          left.MessageActions ⊆ left.MessageActions ∪ right.MessageActions)
  | xoffer_branch env alphabet elseType branches action branchType hConditions =>
      intro offered hOffered
      simp only [Finset.mem_singleton] at hOffered
      subst offered
      simp only [PactType.MessageActions, Finset.mem_union]
      exact Or.inr (branchAction_mem_branchMessageActions hConditions.2.1)
  | xoffer_else => simp [PactType.MessageActions]
  | xoffer_wait env alphabet elseType branches hConditions =>
      intro action hAction
      simp only [typeWaitingOffers, Finset.mem_inter] at hAction
      rw [PactType.MessageActions.eq_def]
      exact Finset.mem_union.mpr
        (Or.inr (typeBranchActions_subset_branchMessageActions branches hAction.2))
  | offer_else env alphabet elseType branches hConditions =>
      intro action hAction
      rw [PactType.MessageActions.eq_def]
      exact Finset.mem_union.mpr
        (Or.inr (typeBranchActions_subset_branchMessageActions branches hAction))
  | offer_wait env alphabet elseType branches hConditions =>
      intro action hAction
      simp only [typeWaitingOffers, Finset.mem_inter] at hAction
      rw [PactType.MessageActions.eq_def]
      exact Finset.mem_union.mpr
        (Or.inr (typeBranchActions_subset_branchMessageActions branches hAction.2))
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hRight hNonFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.MessageActions] at hAction ⊢
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hLeftAction)
      · exact Or.inr (ihRight hRightAction)
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeft hRight hLocal1
      hLocal2 hSide hNotTock ihLeft ihRight =>
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.MessageActions] at hAction ⊢
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hLeftAction)
      · exact Or.inr (ihRight hRightAction)
  | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight
  | left_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihRight =>
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.MessageActions] at hAction ⊢
      exact Or.inr (ihRight hAction.1)
  | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft
  | right_complete_tock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihLeft =>
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.MessageActions] at hAction ⊢
      exact Or.inl (ihLeft hAction.1)
  | par_fuse_tock outer leftEnv rightEnv interface left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeft hRight
      hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      intro action hAction
      simp only [hideTypeOffers, Finset.mem_filter, Finset.mem_union,
        PactType.MessageActions] at hAction ⊢
      rcases hAction.1 with hLeftAction | hRightAction
      · exact Or.inl (ihLeft hLeftAction)
      · exact Or.inr (ihRight hRightAction)

/-- Defines the related-state shape for a compiled parallel product,
mirroring `pactproofs.typ`'s own "Related states" bullets verbatim: a
product state represents the pointwise composition, or the dedicated
`q_done` state (`.final`) represents `skip` once both components finish. -/
def parRelationShape
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par alphabet residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2 ∧
      ParallelReachable signature alphabet left.alphabet right.alphabet
        interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right)
        (.pair q1 q2)) ∨
    (∃ q1 residualLeft,
      entry = (residualLeft.reannotate alphabet, .survivor 0 q1) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      q1 ∉ (compileType signature left).accepting) ∨
    (∃ q2 residualRight,
      entry = (residualRight.reannotate alphabet, .survivor 1 q2) ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2 ∧
      q2 ∉ (compileType signature right).accepting) ∨
    entry = (PactType.skip alphabet, TypeAutomatonState.final)

/-- Proves every related parallel pair has the parallel shape.

High-level proof idea:

Invert `hRelated` using the structural construction of the parallel relation.

A pair in the parallel relation can arise in only two ways. Either it is the
distinguished completed pair `(skip, .final)`, which immediately gives the
completed case of `parRelationShape`; or it comes from the product of the left
and right relation sets. In the latter case, unpack the product membership to
obtain child residuals `ρ₁`, `ρ₂` and states `q₁`, `q₂`, together with
`ρ₁ ~ q₁` and `ρ₂ ~ q₂`. The parent pair is then
`(ρ₁ ‖_I ρ₂, .pair q₁ q₂)`, which gives the product case.

The observable-footprint invariant below shows that each child residual uses
only identifiers from its source child. Therefore the three sibling
disjointness conditions also hold for the two residuals.

-/
lemma relationMembership_par_cases
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par alphabet left right interface)
          (compileType signature (.par alphabet left right interface)))
        residual state) :
    parRelationShape signature alphabet left right interface
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ | (hProd | hSurvLeft) | hSurvRight
  · exact Or.inr (Or.inr (Or.inr (Prod.ext hResidual hState)))
  rotate_left
  · -- A surviving left residual, reannotated to the parent alphabet.
    obtain ⟨entry, hEntry, hResidual, hState⟩ := hSurvLeft
    refine Or.inr (Or.inl ⟨entry.2, entry.1, Prod.ext hResidual.symm hState.symm,
      ?_, ?_⟩)
    · show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel left) left
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl]
      exact hEntry.1
    · show entry.2 ∉
        (compileTypeFuel signature (typeCompilationFuel left) left).accepting
      rw [← compileTypeFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl]
      exact hEntry.2
  · -- The mirror case for a surviving right residual.
    obtain ⟨entry, hEntry, hResidual, hState⟩ := hSurvRight
    refine Or.inr (Or.inr (Or.inl ⟨entry.2, entry.1,
      Prod.ext hResidual.symm hState.symm, ?_, ?_⟩))
    · show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel right) right
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
      exact hEntry.1
    · show entry.2 ∉
        (compileTypeFuel signature (typeCompilationFuel right) right).accepting
      rw [← compileTypeFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
      exact hEntry.2
  · obtain ⟨entry, hEntry, hResidual, hState⟩ := hProd
    obtain ⟨hProduct, hReachable⟩ := hEntry
    obtain ⟨hLeftEntry, hRightEntry⟩ := Finset.mem_product.mp hProduct
    have hLeftRelated : relationMembership
        (buildRelationSet left (compileType signature left))
        entry.1.1 entry.1.2 := by
      show (entry.1.1, entry.1.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel left) left
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature left
        (le_max_left _ _) le_rfl]
      exact hLeftEntry
    have hRightRelated : relationMembership
        (buildRelationSet right (compileType signature right))
        entry.2.1 entry.2.2 := by
      show (entry.2.1, entry.2.2) ∈
        buildRelationSetCoreFuel signature (typeCompilationFuel right) right
      rw [← buildRelationSetCoreFuel_eq_of_sufficient signature right
        (le_max_right _ _) le_rfl]
      exact hRightEntry
    have hPublicReachable : ParallelReachable signature alphabet left.alphabet
        right.alphabet interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right)
        (.pair entry.1.2 entry.2.2) := by
      rw [← compileTypeFuel_eq_of_sufficient signature left
          (le_max_left _ _) le_rfl,
        ← compileTypeFuel_eq_of_sufficient signature right
          (le_max_right _ _) le_rfl]
      simpa [compiledChildFutureFuel, computeFutureOf,
        Nat.min_eq_right (le_max_left _ _),
        Nat.min_eq_right (le_max_right _ _)] using hReachable
    refine Or.inl ⟨entry.1.2, entry.2.2, entry.1.1, entry.2.1,
      Prod.ext hResidual.symm hState.symm, hLeftRelated, hRightRelated,
      hPublicReachable⟩

end

end Pact
