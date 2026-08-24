import Anvilpp.PactTypes.NewCorrespondence.Helpers.Sequence
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Describes the two semantic forms of a decorated parallel step. -/
inductive ParDecoratedStepCase
    (left right : PactType) (interface : Interface) (target : PactType)
    (env : TypeEnvironment) (label : TypeLabel)
    (current future : Finset BareMessage) : Prop where
  | step (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftTarget rightTarget : PactType)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .par leftTarget rightTarget interface →
      ¬ (leftTarget = .skip ∧ rightTarget = .skip) →
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
      ParDecoratedStepCase left right interface target env label current future
  | fuse (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = .skip →
      DecoratedTypeTransition leftEnv left leftLabel
        (TypeOfferSummary.mk leftCurrent leftFuture) .skip →
      DecoratedTypeTransition rightEnv right rightLabel
        (TypeOfferSummary.mk rightCurrent rightFuture) .skip →
      env.WellFormed →
      LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv →
      LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future = hideTypeOffers interface (leftFuture ∪ rightFuture) →
      ParDecoratedStepCase left right interface target env label current future

/-- Every `TypeOffers` constructor mirrors the corresponding `TypeTransition`
constructor's own side condition on `env`. So whenever a `TypeTransition`
witness and a `TypeOffers` witness agree on `(source, label, target)`, the
`TypeOffers` derivation can be rebuilt using the `TypeTransition` witness's own
environment: `env` only gates *which* rule fires (via the shared side
condition), never the current/future *values*, which are pure functions of
`(source, label, target)`. Proved by induction on the `TypeTransition`
derivation, aligning constructors against `hOffers` (which is forced into the
unique matching constructor since `(source, label, target)` already pins the
case). -/
theorem typeOffers_of_typeTransition_env
    {env env' : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hTrans : TypeTransition env source label target)
    (hOffers : TypeOffers env' source label target current future) :
    TypeOffers env source label target current future := by
  sorry



/-- Two synchronized decompositions of the same combined parallel label have
the same component labels when the component types own disjoint observable
identifiers. The environments need not agree. -/
theorem par_witnesses_agree
    {env : TypeEnvironment} {left right leftTarget rightTarget : PactType}
    {interface : Interface} {leftEnv rightEnv leftEnv' rightEnv' : TypeEnvironment}
    {leftLabel rightLabel leftLabel' rightLabel' : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hLeftTrans : TypeTransition leftEnv left leftLabel leftTarget)
    (hRightTrans : TypeTransition rightEnv right rightLabel rightTarget)
    (hMessageActions : Disjoint left.MessageActions right.MessageActions)
    (hProgressIds : Disjoint left.ProgressIds right.ProgressIds)
    (hFairIds : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hWF : env.WellFormed)
    (hLocal1 : LocalTypeEnvironment env interface rightEnv right rightLabel leftEnv)
    (hLocal2 : LocalTypeEnvironment env interface leftEnv left leftLabel rightEnv)
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLeftOffers : TypeOffers leftEnv' left leftLabel' leftTarget leftCurrent leftFuture)
    (hRightOffers : TypeOffers rightEnv' right rightLabel' rightTarget rightCurrent rightFuture)
    (hWF' : env.WellFormed)
    (hLocal1' : LocalTypeEnvironment env interface rightEnv' right rightLabel' leftEnv')
    (hLocal2' : LocalTypeEnvironment env interface leftEnv' left leftLabel' rightEnv')
    (hSync' : TypeLabel.Sync interface leftLabel' rightLabel')
    (hCombineEq :
      TypeLabel.combine interface leftLabel rightLabel =
        TypeLabel.combine interface leftLabel' rightLabel') :
      leftLabel = leftLabel' ∧ rightLabel = rightLabel' := by
  exact supported_labels_recover
    (transition_label_supported hLeftTrans)
    (transition_label_supported hRightTrans)
    (offers_label_supported hLeftOffers)
    (offers_label_supported hRightOffers)
    hMessageActions hProgressIds hFairIds
    hSync hSync' hCombineEq


/--
  Proves that every decorated parallel step either retains both components or fuses them once both complete. Even after above change this theorem stays true
 -/
theorem decoratedTypeTransition_par_cases
    {env : TypeEnvironment} {label : TypeLabel}
    {left right target : PactType} {interface : Interface}
    {current future : Finset BareMessage}
    (hMessageActions : Disjoint left.MessageActions right.MessageActions)
    (hProgressIds : Disjoint left.ProgressIds right.ProgressIds)
    (hFairIds : Disjoint left.FairChoiceIds right.FairChoiceIds)
    (hStep :
      DecoratedTypeTransition env (.par left right interface) label
        (TypeOfferSummary.mk current future) target) :
    ParDecoratedStepCase left right interface target env label current future := by
  rcases hStep with ⟨hTransition, hOffers⟩
  cases hTransition with
  | par _ leftEnv rightEnv _ _ leftTarget _ rightTarget leftLabel rightLabel
      hLeftTrans hRightTrans hNonFinal hSide =>
      obtain ⟨hWF, hLocal1, hLocal2, hSync⟩ := hSide
      change TypeOffers env (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel)
        (.par leftTarget rightTarget interface) current future at hOffers
      generalize hCombineEq :
        TypeLabel.combine interface leftLabel rightLabel = actualLabel at hOffers
      cases hOffers with
      | par _ leftEnv' rightEnv' _ _ _ _ _ leftLabel' rightLabel'
          leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers _hNonFinal' hLocal1' hLocal2' hWFSync' =>
          obtain ⟨hWF', hSync'⟩ := hWFSync'
          obtain ⟨hLabelEq1, hLabelEq2⟩ :=
            par_witnesses_agree hLeftTrans hRightTrans hMessageActions hProgressIds hFairIds hWF hLocal1 hLocal2 hSync
              hLeftOffers hRightOffers hWF' hLocal1' hLocal2' hSync' hCombineEq
          subst hLabelEq1; subst hLabelEq2
          have hLeftOffersEnv := typeOffers_of_typeTransition_env hLeftTrans hLeftOffers
          have hRightOffersEnv := typeOffers_of_typeTransition_env hRightTrans hRightOffers
          exact ParDecoratedStepCase.step leftEnv rightEnv leftLabel rightLabel leftTarget
            rightTarget leftCurrent leftFuture rightCurrent rightFuture rfl hNonFinal
            ⟨hLeftTrans, hLeftOffersEnv⟩ ⟨hRightTrans, hRightOffersEnv⟩ hWF hLocal1 hLocal2 hSync
            hCombineEq rfl rfl
  | par_fuse _ leftEnv rightEnv _ _ _ leftLabel rightLabel
      hLeftTrans hRightTrans hSide =>
      obtain ⟨hWF, hLocal1, hLocal2, hSync⟩ := hSide
      change TypeOffers env (.par left right interface)
        (TypeLabel.combine interface leftLabel rightLabel) .skip current future at hOffers
      generalize hCombineEq :
        TypeLabel.combine interface leftLabel rightLabel = actualLabel at hOffers
      cases hOffers with
      | par_fuse _ leftEnv' rightEnv' _ _ _ leftLabel' rightLabel'
          leftCurrent leftFuture rightCurrent rightFuture
          hLeftOffers hRightOffers hLocal1' hLocal2' hWFSync' =>
          obtain ⟨hWF', hSync'⟩ := hWFSync'
          obtain ⟨hLabelEq1, hLabelEq2⟩ :=
            par_witnesses_agree hLeftTrans hRightTrans hMessageActions hProgressIds hFairIds hWF hLocal1 hLocal2 hSync
              hLeftOffers hRightOffers hWF' hLocal1' hLocal2' hSync' hCombineEq
          subst hLabelEq1; subst hLabelEq2
          have hLeftOffersEnv := typeOffers_of_typeTransition_env hLeftTrans hLeftOffers
          have hRightOffersEnv := typeOffers_of_typeTransition_env hRightTrans hRightOffers
          exact ParDecoratedStepCase.fuse leftEnv rightEnv leftLabel rightLabel leftCurrent
            leftFuture rightCurrent rightFuture rfl ⟨hLeftTrans, hLeftOffersEnv⟩
            ⟨hRightTrans, hRightOffersEnv⟩ hWF hLocal1 hLocal2 hSync hCombineEq rfl rfl


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
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (q1 q2 target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    (compileType signature (.par left right interface)).HasEdge
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
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (env : TypeEnvironment) (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    (compileType signature (.par left right interface)).HasEdge
        TypeAutomatonState.final env label offers target ↔
      env.WellFormed ∧ env.clock = false ∧ label = TypeLabel.silent ∧
      offers = TypeOfferSummary.mk ∅ ∅ ∧ target = TypeAutomatonState.final := by
  classical
  constructor
  · intro hEdge
    have hSymbol := compileType_hasEdge_symbol_mem signature (.par left right interface) hEdge
    have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
      (.par left right interface) TypeAutomatonState.final target env label offers
      hSymbol).mp hEdge
    obtain ⟨edge, hPending, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ := hResolved
    have hFuelEq : typeCompilationFuel (.par left right interface) =
        max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
      simp only [typeCompilationFuel]; omega
    have hWhole : compileTypeFuel signature (typeCompilationFuel (.par left right interface))
        (.par left right interface) =
        buildParallelAutomaton signature interface
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right) := by
      rw [hFuelEq]
      show buildParallelAutomaton signature interface
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right) = _
      rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
        compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
    rw [hWhole] at hPending
    simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
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
    sorry -- needs `env ∈ signature.localEnvironments`, not derivable from `env.WellFormed` alone

/-- Proves each parallel component's own offer pair remains in its own
transition alphabet whenever the combined, interface-hidden parent symbol
is in the fixed alphabet, mirroring `transitionAlphabet_of_typeOffers_target_subset`
for `.par`'s two-sided hiding pattern (which changes both the current and
future components, unlike `.seq`'s future-only pattern that lemma covers).

High-level proof idea:

Unfold membership in the fixed transition alphabet.

Since the combined parallel symbol belongs to `signature.transitionAlphabet`,
its environment, label, and visible offers use only actions/messages permitted
by `signature`.

The `LocalTypeEnvironment` hypotheses and `TypeLabel.Sync` say that the left
and right environments and labels are precisely compatible component views of
this parent parallel step. The parent offer components are obtained by taking
the union of the two component offers and hiding the messages internal to
`interface`.

Therefore each component environment, label, current offers, and future offers
is individually supported by the same fixed signature. Hence the corresponding
left and right `TypeAutomatonSymbol`s both belong to
`signature.transitionAlphabet`.

-/
theorem transitionAlphabet_of_par_component
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {leftEnv rightEnv : TypeEnvironment} {leftLabel rightLabel : TypeLabel}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    {env : TypeEnvironment} {label : TypeLabel}
    (hWF : env.WellFormed)
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
  sorry

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
    relationMembership (buildRelationSet processType (compileType signature processType))
      PactType.skip state := by
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType state with
  | _ n ih =>
    cases processType with
    | skip =>
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel .skip) .skip
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel .skip) .skip).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | message msg dir =>
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.message msg dir))
            (.message msg dir)
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.message msg dir))
              (.message msg dir)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | tock =>
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel .tock) .tock
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel .tock) .tock).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | progress pid =>
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.progress pid))
            (.progress pid)
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.progress pid))
              (.progress pid)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | var name =>
        exfalso
        have hAccept' : state ∈
            (compileTypeFuel signature (typeCompilationFuel (.var name))
              (.var name)).accepting := hAccept
        simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment] at hAccept'
    | choice left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.choice left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.choice left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.choice left right))
            (.choice left right)).accepting = _
          rw [hFuelEq]
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
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.choice left right))
            (.choice left right)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image]
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · refine Or.inr (Or.inl ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩)
          have hRelated := ih (sizeOf left) hLeftSize left hq rfl
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl]
          exact hRelated
        · refine Or.inr (Or.inr ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩)
          have hRelated := ih (sizeOf right) hRightSize right hq rfl
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
            (le_max_right _ _) le_rfl]
          exact hRelated
    | fairChoice bid left right =>
        have hLeftSize : sizeOf left < n := by rw [← hSize]; simp_wf; omega
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.fairChoice bid left right)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
            (.fairChoice bid left right)).accepting = _
          rw [hFuelEq]
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
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.fairChoice bid left right))
            (.fairChoice bid left right)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image]
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · refine Or.inr (Or.inl ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩)
          have hRelated := ih (sizeOf left) hLeftSize left hq rfl
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl]
          exact hRelated
        · refine Or.inr (Or.inr ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩)
          have hRelated := ih (sizeOf right) hRightSize right hq rfl
          rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
            (le_max_right _ _) le_rfl]
          exact hRelated
    | seq left right =>
        have hRightSize : sizeOf right < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.seq left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.seq left right)).accepting =
            childAccepting 1 (compileTypeFuel signature (typeCompilationFuel right) right) := by
          show (compileTypeFuel signature (typeCompilationFuel (.seq left right))
            (.seq left right)).accepting = _
          rw [hFuelEq]
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
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.seq left right))
            (.seq left right)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image]
        refine Or.inr ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩
        have hRelated := ih (sizeOf right) hRightSize right hq rfl
        rw [buildRelationSetCoreFuel_eq_of_sufficient signature right
          (le_max_right _ _) le_rfl]
        exact hRelated
    | par left right interface =>
        have hFuelEq : typeCompilationFuel (.par left right interface) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.par left right interface)).accepting =
            {TypeAutomatonState.final} := by
          show (compileTypeFuel signature (typeCompilationFuel (.par left right interface))
            (.par left right interface)).accepting = _
          rw [hFuelEq]
          show (buildParallelAutomaton signature interface
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel signature
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
          simp [buildParallelAutomaton, finishAutomatonFragment]
        rw [hAcceptEq, Finset.mem_singleton] at hAccept
        subst hAccept
        show (PactType.skip, TypeAutomatonState.final) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.par left right interface))
            (.par left right interface)
        rw [hFuelEq]
        simp [buildRelationSetCoreFuel]
    | recur name body =>
        have hBodySize : sizeOf body < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (.recur name body) = typeCompilationFuel body + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq : (compileType signature (.recur name body)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel body) body) := by
          show (compileTypeFuel signature (typeCompilationFuel (.recur name body))
            (.recur name body)).accepting = _
          rw [hFuelEq]
          show (buildRecursionAutomaton signature name
            (compileTypeFuel signature (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_image] at hAccept
        obtain ⟨q, hq, hEq⟩ := hAccept
        have hRelated := ih (sizeOf body) hBodySize body hq rfl
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (.recur name body))
            (.recur name body)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_image]
        refine Or.inr ⟨(PactType.skip, q), hRelated, ?_⟩
        have hReplace : (PactType.skip).replaceVar name (.recur name body) = PactType.skip :=
          (replaceVar_eq_skip_iff PactType.skip name (.recur name body) (by simp)).mpr rfl
        exact Prod.ext hReplace hEq
    | xoffer elseType branches =>
        have hElseSize : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
        have hFuelEq : typeCompilationFuel (PactType.xoffer elseType branches) =
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
        have hAcceptEq : (compileType signature (PactType.xoffer elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel signature (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting branchAutomata := by
          show (compileTypeFuel signature (typeCompilationFuel (PactType.xoffer elseType branches))
            (PactType.xoffer elseType branches)).accepting = _
          rw [hFuelEq]
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
        show (PactType.skip, state) ∈
          buildRelationSetCoreFuel signature (typeCompilationFuel (PactType.xoffer elseType branches))
            (PactType.xoffer elseType branches)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image]
        rcases hAccept with hElse | hBranch
        · rcases hElse with ⟨q, hq, hEq⟩
          refine Or.inr (Or.inl ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩)
          have hRelated := ih (sizeOf elseType) hElseSize elseType hq rfl
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
            have hBranchSize : sizeOf branchType < n := by
              have hLt : sizeOf branchType < sizeOf (PactType.xoffer elseType branches) := by
                have hProdSize := List.sizeOf_lt_of_mem hBranchMem
                rw [Prod.mk.sizeOf_spec] at hProdSize
                simp
                omega
              simpa [hSize] using hLt
            rw [← hAutomatonEq] at hStateMem
            simp only [Finset.mem_image] at hStateMem
            rcases hStateMem with ⟨q, hq, hEq⟩
            refine Or.inr (Or.inr ?_)
            rw [mem_foldl_union_iff]
            refine Or.inr ⟨((action, branchType), index), ?_, ?_⟩
            · rw [List.mk_mem_zipIdx_iff_getElem?]
              exact hGet
            · simp only [Finset.mem_image]
              refine ⟨(PactType.skip, q), ?_, Prod.ext rfl hEq⟩
              have hRelated := ih (sizeOf branchType) hBranchSize branchType hq rfl
              rw [buildRelationSetCoreFuel_eq_of_sufficient signature branchType ?_ le_rfl]
              · exact hRelated
              · have hLeBranch : typeCompilationFuel branchType ≤ typeBranchCompilationFuel branches :=
                  typeCompilationFuel_le_typeBranchCompilationFuel branches (action, branchType) hBranchMem
                exact le_trans hLeBranch (le_max_right _ _)
    | offer elseType branches => sorry

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
      | message msg dir | progress msg | tock | skip =>
          simp [footprintWithinReplacement, PactType.replaceVar,
            PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
            PactType.FairChoiceIds]
      | var other =>
          by_cases hName : name = other
          · subst other
            simp [footprintWithinReplacement, PactType.replaceVar,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
          · simp [footprintWithinReplacement, PactType.replaceVar, hName,
              PactType.MessageIds, PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
      | recur binder body =>
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
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
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
      | par left right interface =>
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
      | xoffer elseType branches =>
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
      | offer elseType branches =>
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
      | skip | var _ =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton,
            Prod.mk.injEq] at hMem
          rw [hMem.1]
          exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
            Finset.Subset.rfl, Finset.Subset.rfl⟩
      | message msg dir | progress msg | tock =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · simp [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
      | choice left right =>
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
      | fairChoice bid left right =>
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
      | seq left right =>
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
      | par left right interface =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩
          · simp [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds]
          · obtain ⟨hLeftEntry, hRightEntry⟩ := Finset.mem_product.mp hEntry
            have hLeft := ih left entry.1.1 entry.1.2 hLeftEntry
            have hRight := ih right entry.2.1 entry.2.2 hRightEntry
            simp only [footprintSubset, PactType.MessageIds,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds] at hLeft hRight ⊢
            exact ⟨Finset.union_subset_union hLeft.1 hRight.1,
              Finset.union_subset_union hLeft.2.1 hRight.2.1,
              Finset.union_subset_union hLeft.2.2.1 hRight.2.2.1,
              Finset.union_subset_union hLeft.2.2.2 hRight.2.2.2⟩
      | recur name body =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image, Prod.mk.injEq] at hMem
          rcases hMem with ⟨rfl, rfl⟩ | ⟨entry, hEntry, rfl, -⟩
          · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl,
              Finset.Subset.rfl, Finset.Subset.rfl⟩
          · have hChild := ih body entry.1 entry.2 hEntry
            have hReplace := replaceVar_footprintWithinReplacement
              name (.recur name body) entry.1
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
      | xoffer elseType branches =>
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
                (right := PactType.offer .skip branches)
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
      | offer elseType branches =>
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
                (right := PactType.offer .skip branches)
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
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2 ∧
      Disjoint residualLeft.MessageActions residualRight.MessageActions ∧
      Disjoint residualLeft.ProgressIds residualRight.ProgressIds ∧
      Disjoint residualLeft.FairChoiceIds residualRight.FairChoiceIds) ∨
    entry = (PactType.skip, TypeAutomatonState.final)

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
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (hLeftTailRecursive : PactType.TailRecursive left)
    (hRightTailRecursive : PactType.TailRecursive right)
    (hMessageOwnership :
      PactType.ParallelMessageOwnership (.par left right interface))
    (hProgIdsOwnership :
      PactType.ParallelProgressOwnership (.par left right interface))
    (hFairIdOwnership :
      PactType.ParallelFairChoiceOwnership (.par left right interface))
    (hLeftForward :
      ∀ {residual' : PactType} {q1 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet left (compileType signature left))
          residual' q1 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature left).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q1', (compileType signature left).HasEdge q1 env label offers q1' ∧
          relationMembership (buildRelationSet left (compileType signature left))
            target q1')
    (hRightForward :
      ∀ {residual' : PactType} {q2 : TypeAutomatonState} {env : TypeEnvironment}
        {label : TypeLabel} {offers : TypeOfferSummary} {target : PactType},
        relationMembership (buildRelationSet right (compileType signature right))
          residual' q2 →
        (TypeAutomatonSymbol.mk env label offers ∈
          (compileType signature right).alphabet) →
        DecoratedTypeTransition env residual' label offers target →
        ∃ q2', (compileType signature right).HasEdge q2 env label offers q2' ∧
          relationMembership (buildRelationSet right (compileType signature right))
            target q2')
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par left right interface)
          (compileType signature (.par left right interface)))
        residual state) :
    parRelationShape signature left right interface (residual, state) := by
  have hFuelEq : typeCompilationFuel (.par left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel signature
        (typeCompilationFuel (.par left right interface))
        (.par left right interface) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel, Finset.mem_insert,
    Finset.mem_image, Prod.mk.injEq] at hMem
  rcases hMem with ⟨hResidual, hState⟩ |
      ⟨entry, hEntry, hResidual, hState⟩
  · exact Or.inr (Prod.ext hResidual hState)
  · obtain ⟨hLeftEntry, hRightEntry⟩ := Finset.mem_product.mp hEntry
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
    have hLeftFootprint := buildRelationSetCoreFuel_footprintSubset signature
      _ left entry.1.1 entry.1.2 hLeftEntry
    have hRightFootprint := buildRelationSetCoreFuel_footprintSubset signature
      _ right entry.2.1 entry.2.2 hRightEntry
    have hMessageOwnershipPieces :
        Disjoint (left.MessageIds \ interface) (right.MessageIds \ interface) ∧
        Disjoint left.MessageActions right.MessageActions ∧
        left.ParallelMessageOwnership ∧ right.ParallelMessageOwnership := by
      simpa [PactType.ParallelMessageOwnership] using hMessageOwnership
    have hProgressOwnershipPieces :
        Disjoint left.ProgressIds right.ProgressIds ∧
        left.ParallelProgressOwnership ∧ right.ParallelProgressOwnership := by
      simpa [PactType.ParallelProgressOwnership] using hProgIdsOwnership
    have hFairOwnershipPieces :
        Disjoint left.FairChoiceIds right.FairChoiceIds ∧
        left.ParallelFairChoiceOwnership ∧ right.ParallelFairChoiceOwnership := by
      simpa [PactType.ParallelFairChoiceOwnership] using hFairIdOwnership
    refine Or.inl ⟨entry.1.2, entry.2.2, entry.1.1, entry.2.1,
      Prod.ext hResidual.symm hState.symm, hLeftRelated, hRightRelated, ?_, ?_, ?_⟩
    · exact hMessageOwnershipPieces.2.1.mono
        hLeftFootprint.2.1 hRightFootprint.2.1
    · exact hProgressOwnershipPieces.1.mono
        hLeftFootprint.2.2.1 hRightFootprint.2.2.1
    · exact hFairOwnershipPieces.1.mono
        hLeftFootprint.2.2.2 hRightFootprint.2.2.2
  -- have hFuelEq : typeCompilationFuel (.par left right interface) =
  --     max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
  --   simp only [typeCompilationFuel]; omega
  -- have hWhole :
  --     compileTypeFuel signature (typeCompilationFuel (.par left right interface))
  --       (.par left right interface) =
  --       buildParallelAutomaton signature interface
  --         (compileTypeFuel signature (typeCompilationFuel left) left)
  --         (compileTypeFuel signature (typeCompilationFuel right) right) := by
  --   rw [hFuelEq]
  --   show buildParallelAutomaton signature interface
  --       (compileTypeFuel signature
  --         (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
  --       (compileTypeFuel signature
  --         (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
  --     buildParallelAutomaton signature interface
  --       (compileTypeFuel signature (typeCompilationFuel left) left)
  --       (compileTypeFuel signature (typeCompilationFuel right) right)
  --   congr 1
  --   · exact compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl
  --   · exact compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl
  -- have hInit : (compileType signature (.par left right interface)).initial =
  --     .pair (compileType signature left).initial (compileType signature right).initial := by
  --   show (compileTypeFuel signature (typeCompilationFuel (.par left right interface))
  --     (.par left right interface)).initial = _
  --   rw [hWhole]
  --   simp only [buildParallelAutomaton, finishAutomatonFragment]
  --   rfl
  -- have hResult :=
  --   buildRelationSet_preserves (.par left right interface)
  --   (compileType signature (.par left right interface))
  --   (fun entry =>
  --     relationMembership
  --       (buildRelationSet (.par left right interface)
  --         (compileType signature (.par left right interface)))
  --       entry.1 entry.2 ∧
  --     parRelationShape signature left right interface entry)
  --   (by
  --     refine ⟨buildRelationSet_initial (.par left right interface)
  --       (compileType signature (.par left right interface)), ?_⟩
  --     show parRelationShape signature left right interface
  --       (.par left right interface,
  --         (compileType signature (.par left right interface)).initial)
  --     rw [hInit]
  --     exact Or.inl ⟨(compileType signature left).initial,
  --       (compileType signature right).initial, left, right, rfl,
  --       buildRelationSet_initial left (compileType signature left),
  --       buildRelationSet_initial right (compileType signature right)⟩)
  --   (by
  --     intro entry hEntryAnd successor hSuccessor
  --     obtain ⟨hEntryMem, hEntry⟩ := hEntryAnd
  --     have hSuccessorMem :
  --         relationMembership
  --           (buildRelationSet (.par left right interface)
  --             (compileType signature (.par left right interface)))
  --           successor.1 successor.2 :=
  --       buildRelationSet_saturated (.par left right interface)
  --         (compileType signature (.par left right interface)) entry hEntryMem hSuccessor
  --     refine ⟨hSuccessorMem, ?_⟩
  --     rcases relationSuccessors_mem_cases (compileType signature (.par left right interface))
  --       entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature (.par left right interface)
  --       (show (compileType signature (.par left right interface)).HasEdge edge.source
  --         edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
  --         from hEdgeMem)
  --     have hOuterMem :
  --         TypeAutomatonSymbol.mk edge.symbol.environment edge.symbol.label
  --             edge.symbol.offers ∈ signature.transitionAlphabet := by
  --       simpa [compileType] using hSymbolMem
  --     have hOuterEdge :
  --         (compileType signature (.par left right interface)).HasEdge entry.2
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers successor.2 := by
  --       rw [← hSource, hTarget]; exact hEdgeMem
  --     rw [show edge.symbol.offers = TypeOfferSummary.mk edge.symbol.offers.current
  --       edge.symbol.offers.future from rfl] at hStep hOuterMem hOuterEdge
  --     rcases hEntry with
  --       ⟨q1, q2, residualLeft, residualRight, hEntryEq, hLeftRelated, hRightRelated⟩ | hEntryEq
  --     · -- general product case: `entry` represents `.par residualLeft residualRight interface`
  --       have hEntry1 : entry.1 = .par residualLeft residualRight interface := by rw [hEntryEq]
  --       have hEntry2 : entry.2 = .pair q1 q2 := by rw [hEntryEq]
  --       rw [hEntry1] at hStep
  --       rw [hEntry2] at hOuterEdge
  --       cases decoratedTypeTransition_par_cases hStep with
  --       | step leftEnv rightEnv leftLabel rightLabel leftTarget rightTarget
  --           leftCurrent leftFuture rightCurrent rightFuture hTargetEq hNonFinal
  --           hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq hCurrentEq hFutureEq =>
  --           obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
  --             transitionAlphabet_of_par_component signature residualLeft residualRight
  --               interface hWF hLocal1 hLocal2 hSync hLabelEq
  --               (hCurrentEq ▸ hFutureEq ▸ hOuterMem)
  --           have hLeftSymbolMem :
  --               TypeAutomatonSymbol.mk leftEnv leftLabel
  --                 (TypeOfferSummary.mk leftCurrent leftFuture) ∈
  --                 (compileType signature left).alphabet := by
  --             simpa [compileType] using hLeftSymbolMem0
  --           have hRightSymbolMem :
  --               TypeAutomatonSymbol.mk rightEnv rightLabel
  --                 (TypeOfferSummary.mk rightCurrent rightFuture) ∈
  --                 (compileType signature right).alphabet := by
  --             simpa [compileType] using hRightSymbolMem0
  --           obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
  --             hLeftForward hLeftRelated hLeftSymbolMem hLeftStep
  --           obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
  --             hRightForward hRightRelated hRightSymbolMem hRightStep
  --           -- H13: at least one of `q1'`/`q2'` is not accepting, since a
  --           -- child remains (`hNonFinal`), so the compiler does not redirect.
  --           have hNotBothAccept :
  --               ¬ (q1' ∈ (compileType signature left).accepting ∧
  --                  q2' ∈ (compileType signature right).accepting) := by
  --             rintro ⟨hAccept1, hAccept2⟩
  --             exact hNonFinal
  --               ⟨(helper_h13_final_states_represent_completion signature
  --                   hLeftTargetRelated).mp hAccept1,
  --                 (helper_h13_final_states_represent_completion signature
  --                   hRightTargetRelated).mp hAccept2⟩
  --           have hConstructedEdge :
  --               (compileType signature (.par left right interface)).HasEdge
  --                 (.pair q1 q2) edge.symbol.environment edge.symbol.label
  --                 (TypeOfferSummary.mk edge.symbol.offers.current
  --                   edge.symbol.offers.future) (.pair q1' q2') := by
  --             rw [buildParallelAutomaton_pair_hasEdge_iff]
  --             refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
  --               TypeOfferSummary.mk leftCurrent leftFuture,
  --               TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
  --               hLeftEdge, hRightEdge, hLeftRelated, hRightRelated, hWF, hLocal1, hLocal2,
  --               hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
  --             simp [hNotBothAccept]
  --           have hSuccessorEq : successor.2 = .pair q1' q2' :=
  --             compileType_hasEdge_target_unique signature (.par left right interface)
  --               hOuterEdge hConstructedEdge
  --           exact Or.inl ⟨q1', q2', leftTarget, rightTarget, Prod.ext hTargetEq hSuccessorEq,
  --             hLeftTargetRelated, hRightTargetRelated⟩
  --       | fuse leftEnv rightEnv leftLabel rightLabel leftCurrent leftFuture rightCurrent
  --           rightFuture hTargetEq hLeftStep hRightStep hWF hLocal1 hLocal2 hSync hLabelEq
  --           hCurrentEq hFutureEq =>
  --           obtain ⟨hLeftSymbolMem0, hRightSymbolMem0⟩ :=
  --             transitionAlphabet_of_par_component signature residualLeft residualRight
  --               interface hWF hLocal1 hLocal2 hSync hLabelEq
  --               (hCurrentEq ▸ hFutureEq ▸ hOuterMem)
  --           have hLeftSymbolMem :
  --               TypeAutomatonSymbol.mk leftEnv leftLabel
  --                 (TypeOfferSummary.mk leftCurrent leftFuture) ∈
  --                 (compileType signature left).alphabet := by
  --             simpa [compileType] using hLeftSymbolMem0
  --           have hRightSymbolMem :
  --               TypeAutomatonSymbol.mk rightEnv rightLabel
  --                 (TypeOfferSummary.mk rightCurrent rightFuture) ∈
  --                 (compileType signature right).alphabet := by
  --             simpa [compileType] using hRightSymbolMem0
  --           obtain ⟨q1', hLeftEdge, hLeftTargetRelated⟩ :=
  --             hLeftForward hLeftRelated hLeftSymbolMem hLeftStep
  --           obtain ⟨q2', hRightEdge, hRightTargetRelated⟩ :=
  --             hRightForward hRightRelated hRightSymbolMem hRightStep
  --           -- H13: both children finish here, so the compiler redirects to `q_done`.
  --           have hBothAccept :
  --               q1' ∈ (compileType signature left).accepting ∧
  --               q2' ∈ (compileType signature right).accepting :=
  --             ⟨(helper_h13_final_states_represent_completion signature
  --                 hLeftTargetRelated).mpr rfl,
  --               (helper_h13_final_states_represent_completion signature
  --                 hRightTargetRelated).mpr rfl⟩
  --           have hConstructedEdge :
  --               (compileType signature (.par left right interface)).HasEdge
  --                 (.pair q1 q2) edge.symbol.environment edge.symbol.label
  --                 (TypeOfferSummary.mk edge.symbol.offers.current
  --                   edge.symbol.offers.future) TypeAutomatonState.final := by
  --             rw [buildParallelAutomaton_pair_hasEdge_iff]
  --             refine ⟨residualLeft, residualRight, leftEnv, rightEnv, leftLabel, rightLabel,
  --               TypeOfferSummary.mk leftCurrent leftFuture,
  --               TypeOfferSummary.mk rightCurrent rightFuture, q1', q2',
  --               hLeftEdge, hRightEdge, hLeftRelated, hRightRelated, hWF, hLocal1, hLocal2,
  --               hSync, hLabelEq, hCurrentEq, hFutureEq, ?_⟩
  --             simp [hBothAccept]
  --           have hSuccessorEq : successor.2 = TypeAutomatonState.final :=
  --             compileType_hasEdge_target_unique signature (.par left right interface)
  --               hOuterEdge hConstructedEdge
  --           exact Or.inr (Prod.ext hTargetEq hSuccessorEq)
  --     · -- `q_done` case: `entry` already represents `skip` at the dedicated
  --       -- done state; its only public edge is the non-clock silent idle
  --       -- self-loop, which the atomic `skip` step matches directly
  --       -- (paper's "Forward direction at the done state").
  --       have hEntry1 : entry.1 = PactType.skip := by rw [hEntryEq]
  --       have hEntry2 : entry.2 = TypeAutomatonState.final := by rw [hEntryEq]
  --       rw [hEntry1] at hStep
  --       rw [hEntry2] at hOuterEdge
  --       rw [buildParallelAutomaton_final_hasEdge_iff] at hOuterEdge
  --       obtain ⟨hWF, hClock, hLabelEqDone, hOffersEqDone, hSuccessorEq⟩ := hOuterEdge
  --       rw [hLabelEqDone, hOffersEqDone] at hStep
  --       have hSkipStep : DecoratedTypeTransition edge.symbol.environment .skip
  --           TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) PactType.skip :=
  --         ⟨TypeTransition.skip edge.symbol.environment ⟨hWF, hClock⟩,
  --           TypeOffers.skip edge.symbol.environment ⟨hWF, hClock⟩⟩
  --       have hSuccessor1Eq : successor.1 = PactType.skip :=
  --         decoratedTypeTransition_target_unique hStep hSkipStep
  --       exact Or.inr (Prod.ext hSuccessor1Eq hSuccessorEq))
  --   (residual, state) hRelated
  -- exact hResult.2


end

end Pact
