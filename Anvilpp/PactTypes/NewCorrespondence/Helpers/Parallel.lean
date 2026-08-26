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
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      env.WellFormed →
      LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
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
      LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
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
  induction hOffers using TypeOffers.rec
    (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | action env alphabet msg dir hConditions =>
      exact TypeTransition.action env alphabet msg dir hConditions
  | action_wait env alphabet msg dir hConditions =>
      exact TypeTransition.action_wait env alphabet msg dir hConditions
  | choice_left env alphabet left right hEnv =>
      exact TypeTransition.choice_left env alphabet left right hEnv
  | choice_right env alphabet left right hEnv =>
      exact TypeTransition.choice_right env alphabet left right hEnv
  | fair_left env alphabet bid left right hEnv =>
      exact TypeTransition.fair_left env alphabet bid left right hEnv
  | fair_right env alphabet bid left right hEnv =>
      exact TypeTransition.fair_right env alphabet bid left right hEnv
  | cycle env alphabet hConditions =>
      exact TypeTransition.cycle env alphabet hConditions
  | cycle_wait env alphabet hConditions =>
      exact TypeTransition.cycle_wait env alphabet hConditions
  | skip env alphabet hConditions =>
      exact TypeTransition.skip env alphabet hConditions
  | progress env alphabet pid hEnv =>
      exact TypeTransition.progress env alphabet pid hEnv
  | recur env alphabet name body hEnv =>
      exact TypeTransition.recur env alphabet name body hEnv
  | seq env alphabet left leftTarget right label current childFuture hOffers
      hNotSkip ih =>
      exact TypeTransition.seq env alphabet left leftTarget right label ih
        hNotSkip
  | seq_fuse env alphabet skipAlphabet left right label current childFuture
      hOffers ih =>
      exact TypeTransition.seq_fuse env alphabet skipAlphabet left right label ih
  | xoffer_branch env alphabet elseType branches action processType hConditions =>
      exact TypeTransition.xoffer_branch env alphabet elseType branches action
        processType hConditions
  | xoffer_else env alphabet elseType branches hConditions =>
      exact TypeTransition.xoffer_else env alphabet elseType branches hConditions
  | xoffer_wait env alphabet elseType branches hConditions =>
      exact TypeTransition.xoffer_wait env alphabet elseType branches hConditions
  | offer_some env alphabet elseType branches enabled hConditions =>
      exact TypeTransition.offer_some env alphabet elseType branches enabled
        hConditions
  | offer_else env alphabet elseType branches hConditions =>
      exact TypeTransition.offer_else env alphabet elseType branches hConditions
  | offer_wait env alphabet elseType branches hConditions =>
      exact TypeTransition.offer_wait env alphabet elseType branches hConditions
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftOffers hRightOffers hNotFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      exact TypeTransition.par outer leftEnv rightEnv interface left leftTarget
        right rightTarget leftLabel rightLabel ihLeft ihRight hNotFinal
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide ihLeft ihRight =>
      exact TypeTransition.par_fuse outer leftEnv rightEnv interface left right
        leftLabel rightLabel ihLeft ihRight
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | clock => trivial
  | ordinary => trivial



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
      hLeftOffers hRightOffers hNonFinal hLocal1 hLocal2 hSide =>
      exact ParDecoratedStepCase.step leftEnv rightEnv leftLabel rightLabel
        leftTarget rightTarget leftCurrent leftFuture rightCurrent rightFuture
        rfl hNonFinal
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 rfl rfl rfl
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide =>
      exact ParDecoratedStepCase.fuse leftEnv rightEnv leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture rfl
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 rfl rfl rfl


/--
High-level proof idea:


Unfold the construction of the parallel automaton.


(→) Given an edge out of `.pair q1 q2`, invert the parallel compiler's
synchronized-edge construction. This yields the two child edges together with
the local-environment, synchronization, combined-label, and combined-offer
conditions used to construct the edge. The compiler's redirect rule determines
whether the target is `.final` (both child targets accepting) or
`.pair q1' q2'`.


(←) Conversely, given child edges satisfying these synchronization conditions,
the parallel compiler constructs the corresponding synchronized edge, redirecting
it to `.final` exactly when both child targets are accepting.
-/
theorem buildParallelAutomaton_pair_hasEdge_iff
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileType signature (.par alphabet left right interface)).HasEdge
        (.pair q1 q2) env label offers target ↔
      ∃ (childLeft childRight : PactType)
        (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
        (leftOffers rightOffers : TypeOfferSummary) (q1' q2' : TypeAutomatonState),
        (compileType signature left).HasEdge q1 leftEnv leftLabel leftOffers q1' ∧
        (compileType signature right).HasEdge q2 rightEnv rightLabel rightOffers q2' ∧
        relationMembership (buildRelationSet left (compileType signature left))
          childLeft q1 ∧
        relationMembership (buildRelationSet right (compileType signature right))
          childRight q2 ∧
        ParallelReachable signature interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right)
          (.pair q1 q2) ∧
        env.WellFormed ∧
        LocalTypeEnvironment env interface rightEnv childRight rightLabel leftEnv ∧
        LocalTypeEnvironment env interface leftEnv childLeft leftLabel rightEnv ∧
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
        else target = .pair q1' q2') := by
  sorry

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
      signature.transitionAlphabet) :
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
        buildParallelAutomaton signature interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right) := by
      rw [hFuelEq]
      rw [compileTypeFuel.eq_def]
      show buildParallelAutomaton signature interface
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
      parallelRawTransitionEdges, parallelDoneEdges, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hPending
    rcases hPending with ⟨⟨leftEdge, -, rightEdge, -, hEq⟩, -⟩ | ⟨environment, hEnvironment, hEq⟩
    · exfalso
      rw [← hEq] at hSource
      simp at hSource
    · rw [← hEq] at hSource hEnv hLabel hCurrent hFuture hTarget
      simp only at hSource hEnv hLabel hCurrent hFuture hTarget
      subst env
      injection hLabel with hLabelEq
      subst hLabelEq
      refine ⟨localEnvironment_wellFormed signature hEnvironment.1, hEnvironment.2, rfl, ?_,
        hTarget.symm⟩
      · cases offers with
        | mk current future => simp_all
  · rintro ⟨hWF, hClock, hLabel, hOffers, hTarget⟩
    subst hLabel; subst hOffers; subst hTarget
    rw [compileType_hasEdge_iff_hasResolvedEdge signature
      (.par alphabet left right interface) TypeAutomatonState.final
      TypeAutomatonState.final
      env TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) hSymbol]
    have hLocal : env ∈ signature.localEnvironments :=
      transitionAlphabet_environment_mem signature hSymbol
    have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    have hWhole : compileTypeFuel signature
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
        buildParallelAutomaton signature interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (computeFutureOf signature left)
          (computeFutureOf signature right) := by
      rw [hFuelEq]
      rw [compileTypeFuel.eq_def]
      show buildParallelAutomaton signature interface
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
    ParallelReachable signature interface
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
      buildParallelAutomaton signature interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildParallelAutomaton signature interface
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
  · have hTargetReachable := hReachable.target_of_rawTransition hRawEdge
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

private theorem localEnvironment_mem_of_localTypeEnvironment
    (signature : TypeAlphabet) {outer localEnv siblingEnv : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {label : TypeLabel}
    (hInterface : interface ⊆ signature.interface)
    (hOuter : outer ∈ signature.localEnvironments)
    (hLocal : LocalTypeEnvironment outer interface siblingEnv sibling label localEnv) :
    localEnv ∈ signature.localEnvironments := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      simp [TypeAlphabet.localEnvironments, TypeEnvironment.tock]
  | ordinary outer siblingEnv localEnv interface sibling siblingTarget label
      current future hOuterClock hSiblingClock hOffers hLocalClock
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
            Finset.mem_filter] at hAction
          rcases hAction with hOuterAction | ⟨_, hInterfaceAction⟩
          · exact hOuterImmediate hOuterAction
          · exact interface_action_mem_localEnvironmentActions signature
              hInterface hInterfaceAction
        · intro action hAction
          rw [hFuture] at hAction
          simp only [Finset.mem_sdiff, Finset.mem_union, restrictTypeOffers,
            Finset.mem_filter] at hAction ⊢
          rcases hAction.1 with hOuterAction | ⟨_, hInterfaceAction⟩
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

/-- Each component symbol of a parallel step belongs to the same local
transition alphabet.  The enclosing product may hide interface actions, but
those actions remain declared local actions while either child is compiled. -/
theorem transitionAlphabet_of_par_component
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {leftEnv rightEnv : TypeEnvironment} {leftLabel rightLabel : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    {env : TypeEnvironment} {label : TypeLabel}
    (hWF : env.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hLocal1 : LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv)
    (hLocal2 : LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
    (hSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
          (hideTypeOffers interface (leftFuture ∪ rightFuture))) ∈
        signature.transitionAlphabet) :
    TypeAutomatonSymbol.mk leftEnv leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) ∈
      signature.transitionAlphabet ∧
    TypeAutomatonSymbol.mk rightEnv rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) ∈
      signature.transitionAlphabet := by
  rw [transitionAlphabet_mk_mem_iff] at hSymbol
  obtain ⟨hEnv, hParentLabel, hParentOffers⟩ := hSymbol
  have hLeftEnv := localEnvironment_mem_of_localTypeEnvironment signature
    hInterface hEnv hLocal1
  have hRightEnv := localEnvironment_mem_of_localTypeEnvironment signature
    hInterface hEnv hLocal2
  have hLabels := componentLabels_mem_localLabels signature hInterface hSync
    hLabelEq hParentLabel
  have hOffers := componentOffers_mem_localOfferSummaries signature hInterface
    hParentOffers
  constructor
  · rw [transitionAlphabet_mk_mem_iff]
    exact ⟨hLeftEnv, hLabels.1, hOffers.1⟩
  · rw [transitionAlphabet_mk_mem_iff]
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
    (hReachable : ParallelReachable signature interface
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
  · change ParallelReachable signature interface
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
          show (buildParallelAutomaton signature interface
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
          show (buildExclusiveOfferAutomaton signature branches
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
          show (buildSelectedConjunctiveOfferAutomaton signature branches
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
            Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩
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
      ParallelReachable signature interface
        (compileTypeFuel signature (typeCompilationFuel left) left)
        (compileTypeFuel signature (typeCompilationFuel right) right)
        (computeFutureOf signature left)
        (computeFutureOf signature right)
        (.pair q1 q2)) ∨
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
  simp only [buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_image, Finset.mem_filter, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩
  · exact Or.inr (Prod.ext hResidual hState)
  · obtain ⟨hProduct, hReachable⟩ := hEntry
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
    have hPublicReachable : ParallelReachable signature interface
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
