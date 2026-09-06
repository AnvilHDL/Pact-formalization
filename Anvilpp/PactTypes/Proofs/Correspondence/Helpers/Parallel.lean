import Anvilpp.PactTypes.Spec.Syntax.PactTypeFutureOffersDefs
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.Sequence
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.MainHelpers

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
      env.WellFormed parentAlphabet →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = hideTypeOffers interface (leftCurrent ∪ rightCurrent) →
      future =
        (if TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock
          then ∅
          else hideTypeOffers interface (leftFuture ∪ rightFuture)) →
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
      env.WellFormed parentAlphabet →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      TypeLabel.Sync interface leftLabel rightLabel →
      TypeLabel.combine interface leftLabel rightLabel = TypeLabel.tock →
      label = TypeLabel.combine interface leftLabel rightLabel →
      current = ∅ →
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
      env.WellFormed parentAlphabet →
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
  | left_complete (leftEnv rightEnv : TypeEnvironment) (rightTarget : PactType)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = rightTarget.reannotate parentAlphabet →
      left = .skip left.alphabet →
      right ≠ .skip right.alphabet →
      rightTarget ≠ .skip rightTarget.alphabet →
      DecoratedTypeTransition leftEnv left TypeLabel.silent
        (TypeOfferSummary.mk leftCurrent leftFuture) left →
      DecoratedTypeTransition rightEnv right label
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      env.WellFormed parentAlphabet →
      TypeLabel.Sync interface TypeLabel.silent label →
      current = hideTypeOffers interface rightCurrent →
      future = hideTypeOffers interface rightFuture →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  -- Mirror of `left_complete`: the right side is already `skip`.
  | right_complete (leftEnv rightEnv : TypeEnvironment) (leftTarget : PactType)
      (leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage) :
      target = leftTarget.reannotate parentAlphabet →
      right = .skip right.alphabet →
      left ≠ .skip left.alphabet →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition rightEnv right TypeLabel.silent
        (TypeOfferSummary.mk rightCurrent rightFuture) right →
      DecoratedTypeTransition leftEnv left label
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
        rightFuture leftEnv →
      LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
        leftFuture rightEnv →
      env.WellFormed parentAlphabet →
      TypeLabel.Sync interface label TypeLabel.silent →
      current = hideTypeOffers interface leftCurrent →
      future = hideTypeOffers interface leftFuture →
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
  | par outer leftEnv rightEnv interface alphabet left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip
      hLeftOffers hRightOffers hNotFinal hLocal1 hLocal2 hSide ihLeft ihRight =>
      exact TypeTransition.par outer leftEnv rightEnv interface alphabet left leftTarget
        right rightTarget leftLabel rightLabel leftCurrent leftFuture
        rightCurrent rightFuture hLeftNotSkip hRightNotSkip
        ihLeft hLeftOffers ihRight hRightOffers hNotFinal
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide hNotTock ihLeft ihRight =>
      exact TypeTransition.par_fuse outer leftEnv rightEnv interface alphabet left right
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
        ihLeft hLeftOffers ihRight hRightOffers
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocal1 hLocal2 hSide hTock ihLeft ihRight =>
      exact TypeTransition.par_fuse outer leftEnv rightEnv interface alphabet left right
        leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
        ihLeft hLeftOffers ihRight hRightOffers
        ⟨hSide.1, hLocal1, hLocal2, hSide.2⟩
  | left_complete outer leftEnv rightEnv interface alphabet left right right'
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightNotSkip hLeftOffers hRightOffers hNotSkip hLocalLeft hLocalRight
      hWF hSync ihLeft ihRight =>
      exact TypeTransition.left_complete outer leftEnv rightEnv interface alphabet
        left right right' rightLabel leftCurrent leftFuture rightCurrent
        rightFuture hLeftSkip hRightNotSkip ihLeft hLeftOffers ihRight
        hRightOffers hNotSkip hLocalLeft hLocalRight hWF hSync
  | right_complete outer leftEnv rightEnv interface alphabet left left' right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftNotSkip hRightOffers hLeftOffers hNotSkip hLocalLeft hLocalRight
      hWF hSync ihRight ihLeft =>
      exact TypeTransition.right_complete outer leftEnv rightEnv interface alphabet
        left left' right leftLabel leftCurrent leftFuture rightCurrent
        rightFuture hRightSkip hLeftNotSkip ihRight hRightOffers ihLeft
        hLeftOffers hNotSkip hLocalLeft hLocalRight hWF hSync


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
  | par outer leftEnv rightEnv interface alphabet left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      hLeftNotSkip hRightNotSkip hLeftOffers hRightOffers hNonFinal hLocal1
      hLocal2 hSide =>
      exact ParDecoratedStepCase.step leftEnv rightEnv leftLabel rightLabel
        leftTarget rightTarget leftCurrent leftFuture rightCurrent rightFuture
        rfl hNonFinal hLeftNotSkip hRightNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 rfl rfl rfl
  | par_fuse outer leftEnv rightEnv interface alphabet left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide hNotTock =>
      exact ParDecoratedStepCase.fuse leftEnv rightEnv leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture rfl
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 hNotTock rfl rfl rfl
  | par_fuse_tock outer leftEnv rightEnv interface alphabet left right leftLabel
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftOffers
      hRightOffers hLocal1 hLocal2 hSide hTock =>
      exact ParDecoratedStepCase.fuse_tock leftEnv rightEnv leftLabel
        rightLabel
        leftCurrent leftFuture rightCurrent rightFuture rfl
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hSide.1 hLocal1 hLocal2 hSide.2 hTock rfl rfl rfl
  | left_complete outer leftEnv rightEnv interface alphabet left right rightTarget
      rightLabel leftCurrent leftFuture rightCurrent rightFuture hLeftSkip
      hRightLive hLeftOffers hRightOffers hNotSkip hLocalLeft hLocalRight hWF hSync =>
      exact ParDecoratedStepCase.left_complete leftEnv rightEnv rightTarget
        leftCurrent leftFuture rightCurrent rightFuture rfl hLeftSkip hRightLive
        hNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hLocalLeft hLocalRight hWF hSync rfl rfl
  | right_complete outer leftEnv rightEnv interface alphabet left leftTarget right
      leftLabel leftCurrent leftFuture rightCurrent rightFuture hRightSkip
      hLeftLive hRightOffers hLeftOffers hNotSkip hLocalLeft hLocalRight hWF hSync =>
      exact ParDecoratedStepCase.right_complete leftEnv rightEnv leftTarget
        leftCurrent leftFuture rightCurrent rightFuture rfl hRightSkip hLeftLive
        hNotSkip
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        hLocalLeft hLocalRight hWF hSync rfl rfl


set_option maxHeartbeats 1000000 in
/-- The dedicated completed state of a parallel product represents `skip`. -/
lemma relationMembership_par_final
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (.skip alphabet) .final := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]
    omega
  show ((.skip alphabet : PactType), .final) ∈
    buildRelationSetCoreFuel
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
     (processType : PactType) {state : TypeAutomatonState}
    (hAccept : state ∈ (compileType processType).accepting) :
    ∃ skipAlphabet,
      relationMembership
        (buildRelationSet processType (compileType processType))
        (.skip skipAlphabet) state := by
  induction hSize : typeCompilationFuel processType using Nat.strong_induction_on
      generalizing processType state with
  | _ n ih =>
    cases processType with
    | skip alphabet =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (.skip alphabet)) (.skip alphabet)
        have hAccept' : state ∈
            (compileTypeFuel (typeCompilationFuel (.skip alphabet))
              (.skip alphabet)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | message alphabet msg dir =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (.message alphabet msg dir))
            (.message alphabet msg dir)
        have hAccept' : state ∈
            (compileTypeFuel
              (typeCompilationFuel (.message alphabet msg dir))
              (.message alphabet msg dir)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | tock alphabet =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (.tock alphabet)) (.tock alphabet)
        have hAccept' : state ∈
            (compileTypeFuel (typeCompilationFuel (.tock alphabet))
              (.tock alphabet)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | progress alphabet pid =>
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, state) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (.progress alphabet pid))
            (.progress alphabet pid)
        have hAccept' : state ∈
            (compileTypeFuel
              (typeCompilationFuel (.progress alphabet pid))
              (.progress alphabet pid)).accepting := hAccept
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_singleton] at hAccept'
        subst hAccept'
        simp [typeCompilationFuel, buildRelationSetCoreFuel]
    | var alphabet name =>
        exfalso
        have hAccept' : state ∈
            (compileTypeFuel (typeCompilationFuel (.var alphabet name))
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
            (compileType (.choice alphabet left right)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.choice alphabet left right))
            (.choice alphabet left right)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            TypeLabel.silent TypeLabel.silent).accepting = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_union, Finset.mem_image] at hAccept
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel left) hLeftSize left hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel
              (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
          exact hRelated
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel right) hRightSize right hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel
              (typeCompilationFuel (.choice alphabet left right))
              (.choice alphabet left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inr
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient right
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
            (compileType (.fairChoice alphabet bid left right)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel left) left) ∪
              childAccepting 1 (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.fairChoice alphabet bid left right))
            (.fairChoice alphabet bid left right)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildChoiceAutomaton alphabet
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
            compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildChoiceAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_union, Finset.mem_image] at hAccept
        rcases hAccept with ⟨q, hq, hEq⟩ | ⟨q, hq, hEq⟩
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel left) hLeftSize left hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel
              (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient left (le_max_left _ _) le_rfl]
          exact hRelated
        · obtain ⟨skipAlphabet, hRelated⟩ :=
            ih (typeCompilationFuel right) hRightSize right hq rfl
          refine ⟨skipAlphabet, ?_⟩
          change ((.skip skipAlphabet, state)) ∈
            buildRelationSetCoreFuel
              (typeCompilationFuel (.fairChoice alphabet bid left right))
              (.fairChoice alphabet bid left right)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inr
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient right
            (le_max_right _ _) le_rfl]
          exact hRelated
    | seq alphabet left right =>
        have hRightSize : typeCompilationFuel right < n := by
          rw [← hSize]; simp [typeCompilationFuel]; omega
        have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.seq alphabet left right)).accepting =
            childAccepting 1 (compileTypeFuel (typeCompilationFuel right) right) := by
          show (compileTypeFuel
            (typeCompilationFuel (.seq alphabet left right))
            (.seq alphabet left right)).accepting = _
          rw [compileTypeFuel_sequence_eq_build]
          rfl

        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_image] at hAccept
        obtain ⟨q, hq, hEq⟩ := hAccept
        obtain ⟨skipAlphabet, hRelated⟩ :=
          ih (typeCompilationFuel right) hRightSize right hq rfl
        refine ⟨skipAlphabet, ?_⟩
        change ((.skip skipAlphabet, state)) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (.seq alphabet left right))
            (.seq alphabet left right)
        rw [hFuelEq]
        simp only [buildRelationSetCoreFuel, Finset.mem_union, Finset.mem_image]
        refine Or.inr ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩
        rw [buildRelationSetCoreFuel_eq_of_sufficient right
          (le_max_right _ _) le_rfl]
        exact hRelated
    | par alphabet left right interface =>
        have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
            max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
          simp only [typeCompilationFuel]; omega
        have hAcceptEq :
            (compileType (.par alphabet left right interface)).accepting =
            {TypeAutomatonState.final} := by
          show (compileTypeFuel
            (typeCompilationFuel (.par alphabet left right interface))
            (.par alphabet left right interface)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildParallelAutomaton alphabet left.alphabet
            right.alphabet interface
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (left.reannotate alphabet))
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (right.reannotate alphabet))
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (left.reannotate alphabet))
            (compiledChildFutureFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right))
              (right.reannotate alphabet))).accepting = _
          simp [buildParallelAutomaton, finishAutomatonFragment]
        rw [hAcceptEq, Finset.mem_singleton] at hAccept
        subst hAccept
        refine ⟨alphabet, ?_⟩
        show (.skip alphabet, TypeAutomatonState.final) ∈
          buildRelationSetCoreFuel
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
            (compileType (.recur alphabet name body)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel body) body) := by
          show (compileTypeFuel
            (typeCompilationFuel (.recur alphabet name body))
            (.recur alphabet name body)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildRecursionAutomaton alphabet name
            (compileTypeFuel (typeCompilationFuel body) body)).accepting = _
          simp [buildRecursionAutomaton, finishAutomatonFragment]
        rw [hAcceptEq] at hAccept
        simp only [childAccepting, Finset.mem_image] at hAccept
        obtain ⟨q, hq, hEq⟩ := hAccept
        obtain ⟨skipAlphabet, hRelated⟩ :=
          ih (typeCompilationFuel body) hBodySize body hq rfl
        refine ⟨skipAlphabet, ?_⟩
        show (.skip skipAlphabet, state) ∈
          buildRelationSetCoreFuel
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
          compileTypeFuel (typeCompilationFuel branch.2) branch.2)) branches
        have hMapEq :
            List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches = branchAutomata := by
          dsimp [branchAutomata]
          apply List.map_congr_left
          intro branch hMem
          have hLeBranch : typeCompilationFuel branch.2 ≤ typeBranchCompilationFuel branches :=
            typeCompilationFuel_le_typeBranchCompilationFuel branches branch hMem
          rw [compileTypeFuel_eq_of_sufficient branch.2
            (le_trans hLeBranch (le_max_right _ _)) le_rfl]
        have hAcceptEq :
            (compileType (.xoffer alphabet elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting branchAutomata := by
          show (compileTypeFuel
            (typeCompilationFuel (.xoffer alphabet elseType branches))
            (.xoffer alphabet elseType branches)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildExclusiveOfferAutomaton alphabet branches
            (compileTypeFuel (max (typeCompilationFuel elseType)
              (typeBranchCompilationFuel branches)) elseType)
            (List.map (fun branch => (branch.1,
              compileTypeFuel (max (typeCompilationFuel elseType)
                (typeBranchCompilationFuel branches)) branch.2)) branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl]
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
            buildRelationSetCoreFuel
              (typeCompilationFuel (.xoffer alphabet elseType branches))
              (.xoffer alphabet elseType branches)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient elseType
            (le_max_left _ _) le_rfl]
          exact hRelated
        · rw [mem_foldl_union_iff] at hBranch
          rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hStateMem⟩
          · simp at hEmpty
          · rcases indexed with ⟨branchAutomaton, index⟩
            rcases branchAutomaton with ⟨action, automaton⟩
            rw [List.mk_mem_zipIdx_iff_getElem?] at hIndexedMem
            rw [branches_map_getElem?_eq_some_iff branches index action automaton]
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
              buildRelationSetCoreFuel
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
              rw [buildRelationSetCoreFuel_eq_of_sufficient branchType ?_ le_rfl]
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
          compileTypeFuel
            (typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))) branches
        have hMapEq :
            List.map (fun selected => (selected.1,
              compileTypeFuel
                (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches))) branches =
              selectedConjunctions := by
          dsimp [selectedConjunctions]
          apply List.map_congr_left
          intro selected hSelected
          rw [compileTypeFuel_eq_of_sufficient
            (parallelTypeBranchesSelecting alphabet selected branches) ?_ le_rfl]
          show typeCompilationFuel (parallelTypeBranchesSelecting alphabet selected branches) ≤
            max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          exact le_max_right _ _
        have hAcceptEq :
            (compileType (.offer alphabet elseType branches)).accepting =
            childAccepting 0 (compileTypeFuel
              (typeCompilationFuel elseType) elseType) ∪
              indexedFragmentAccepting selectedConjunctions := by
          show (compileTypeFuel
            (typeCompilationFuel (.offer alphabet elseType branches))
            (.offer alphabet elseType branches)).accepting = _
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildSelectedConjunctiveOfferAutomaton alphabet branches
            (compileTypeFuel
              (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
              elseType)
            (List.map (fun selected => (selected.1,
              compileTypeFuel
                (max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches))
                (parallelTypeBranchesSelecting alphabet selected branches))) branches)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient elseType
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
            buildRelationSetCoreFuel
              (typeCompilationFuel (.offer alphabet elseType branches))
              (.offer alphabet elseType branches)
          rw [hFuelEq]
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image]
          refine Or.inr (Or.inl
            ⟨(.skip skipAlphabet, q), ?_, Prod.ext rfl hEq⟩)
          rw [buildRelationSetCoreFuel_eq_of_sufficient elseType
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
              parallelTypeBranchesSelecting alphabet (action, branchType) branches
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
              buildRelationSetCoreFuel
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
              rw [buildRelationSetCoreFuel_eq_of_sufficient selectedType ?_ le_rfl]
              · exact hRelated
              · show typeCompilationFuel selectedType ≤
                  max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches)
                dsimp [selectedType]
                rw [typeCompilationFuel_parallelTypeBranchesSelecting]
                exact le_max_right _ _

/-- The right survivor region is the compiled re-signed right component tagged
by `survivor 1`, so a state the re-signed component's own relation pairs with a
residual keeps that residual there.  Re-signing moves no accepting state, so the
completion edge's non-accepting target still passes the survivor filter. -/
theorem survivorRight_relationMembership
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : right.OfferBranchesDisjoint)
    (hChild : relationMembership
      (buildRelationSet (right.reannotate alphabet)
        (compileType (right.reannotate alphabet))) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel right) right).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      residual (.survivor 1 q) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hRightFuel : typeCompilationFuel right ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) :=
    le_max_right _ _
  have hRightReFuel : typeCompilationFuel (right.reannotate alphabet) ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) := by
    rw [typeCompilationFuel_reannotate]; exact hRightFuel
  -- The survivor clause reads the re-signed component's relation at the
  -- parent's own budget, which the child's budget already saturates.
  have hMem : (residual, q) ∈
      buildRelationSetCoreFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right))
        (right.reannotate alphabet) := by
    rw [buildRelationSetCoreFuel_eq_of_sufficient (right.reannotate alphabet)
      hRightReFuel le_rfl]
    exact hChild
  -- Re-signing preserves the accepting set, so `q` is non-accepting there too.
  have hAcc : (compileTypeFuel
      (max (typeCompilationFuel left) (typeCompilationFuel right))
      (right.reannotate alphabet)).accepting =
      (compileTypeFuel (typeCompilationFuel right) right).accepting := by
    rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
      (max (typeCompilationFuel left) (typeCompilationFuel right)) right
      hDisjoint alphabet).2.2,
      compileTypeFuel_eq_of_sufficient right hRightFuel le_rfl]
  show (residual, TypeAutomatonState.survivor 1 q) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
  refine Finset.mem_image.mpr
    ⟨(residual, q), Finset.mem_filter.mpr ⟨hMem, ?_⟩, rfl⟩
  rw [hAcc]
  exact hNotAcc

/-- The mirror of `survivorRight_relationMembership` for the left survivor
region, tagged by `survivor 0`. -/
theorem survivorLeft_relationMembership
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : left.OfferBranchesDisjoint)
    (hChild : relationMembership
      (buildRelationSet (left.reannotate alphabet)
        (compileType (left.reannotate alphabet))) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel left) left).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      residual (.survivor 0 q) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hLeftFuel : typeCompilationFuel left ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) :=
    le_max_left _ _
  have hLeftReFuel : typeCompilationFuel (left.reannotate alphabet) ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) := by
    rw [typeCompilationFuel_reannotate]; exact hLeftFuel
  have hMem : (residual, q) ∈
      buildRelationSetCoreFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right))
        (left.reannotate alphabet) := by
    rw [buildRelationSetCoreFuel_eq_of_sufficient (left.reannotate alphabet)
      hLeftReFuel le_rfl]
    exact hChild
  have hAcc : (compileTypeFuel
      (max (typeCompilationFuel left) (typeCompilationFuel right))
      (left.reannotate alphabet)).accepting =
      (compileTypeFuel (typeCompilationFuel left) left).accepting := by
    rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
      (max (typeCompilationFuel left) (typeCompilationFuel right)) left
      hDisjoint alphabet).2.2,
      compileTypeFuel_eq_of_sufficient left hLeftFuel le_rfl]
  show (residual, TypeAutomatonState.survivor 0 q) ∈
    buildRelationSetCoreFuel
      (typeCompilationFuel (.par alphabet left right interface))
      (.par alphabet left right interface)
  rw [hFuelEq]
  simp only [buildRelationSetCoreFuel]
  refine Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  refine Finset.mem_image.mpr
    ⟨(residual, q), Finset.mem_filter.mpr ⟨hMem, ?_⟩, rfl⟩
  rw [hAcc]
  exact hNotAcc


set_option maxHeartbeats 4000000 in
def parRelationShape
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par alphabet residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType right))
        residualRight q2) ∨
    (∃ q1 residualLeft,
      entry = (residualLeft, .survivor 0 q1) ∧
      relationMembership
        (buildRelationSet (left.reannotate alphabet)
          (compileType (left.reannotate alphabet)))
        residualLeft q1 ∧
      q1 ∉ (compileType (left.reannotate alphabet)).accepting) ∨
    (∃ q2 residualRight,
      entry = (residualRight, .survivor 1 q2) ∧
      relationMembership
        (buildRelationSet (right.reannotate alphabet)
          (compileType (right.reannotate alphabet)))
        residualRight q2 ∧
      q2 ∉ (compileType (right.reannotate alphabet)).accepting) ∨
    entry = (PactType.skip alphabet, TypeAutomatonState.final)

/-- Proves every related parallel pair has the parallel shape, by inverting the
four families of the relation's `.par` clause at the parent's own fuel. -/
lemma relationMembership_par_cases
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par alphabet left right interface)
          (compileType (.par alphabet left right interface)))
        residual state) :
    parRelationShape alphabet left right interface
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hLeftFuel : typeCompilationFuel left ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) :=
    le_max_left _ _
  have hRightFuel : typeCompilationFuel right ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) :=
    le_max_right _ _
  have hLeftReFuel : typeCompilationFuel (left.reannotate alphabet) ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) := by
    rw [typeCompilationFuel_reannotate]; exact hLeftFuel
  have hRightReFuel : typeCompilationFuel (right.reannotate alphabet) ≤
      max (typeCompilationFuel left) (typeCompilationFuel right) := by
    rw [typeCompilationFuel_reannotate]; exact hRightFuel
  have hMem : (residual, state) ∈
      buildRelationSetCoreFuel
        (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) := hRelated
  rw [hFuelEq] at hMem
  simp only [buildRelationSetCoreFuel] at hMem
  rcases Finset.mem_insert.mp hMem with hFinal | hRest
  · exact Or.inr (Or.inr (Or.inr hFinal))
  rcases Finset.mem_union.mp hRest with hProductOrLeft | hSurvivorRight
  · rcases Finset.mem_union.mp hProductOrLeft with hProduct | hSurvivorLeft
    · rcases Finset.mem_image.mp hProduct with ⟨entry, hEntry, hEq⟩
      have hPair := Finset.mem_product.mp hEntry
      injection hEq with hResidual hState
      refine Or.inl ⟨entry.1.2, entry.2.2, entry.1.1, entry.2.1,
        by rw [← hResidual, ← hState], ?_, ?_⟩
      · show (entry.1.1, entry.1.2) ∈
          buildRelationSetCoreFuel (typeCompilationFuel left) left
        rw [← buildRelationSetCoreFuel_eq_of_sufficient left hLeftFuel le_rfl]
        exact hPair.1
      · show (entry.2.1, entry.2.2) ∈
          buildRelationSetCoreFuel (typeCompilationFuel right) right
        rw [← buildRelationSetCoreFuel_eq_of_sufficient right hRightFuel le_rfl]
        exact hPair.2
    · rcases Finset.mem_image.mp hSurvivorLeft with ⟨entry, hEntry, hEq⟩
      have hEntryMem := (Finset.mem_filter.mp hEntry).1
      have hNotAccepting := (Finset.mem_filter.mp hEntry).2
      injection hEq with hResidual hState
      refine Or.inr (Or.inl ⟨entry.2, entry.1,
        by rw [← hResidual, ← hState], ?_, ?_⟩)
      · show (entry.1, entry.2) ∈
          buildRelationSetCoreFuel
            (typeCompilationFuel (left.reannotate alphabet))
            (left.reannotate alphabet)
        rw [← buildRelationSetCoreFuel_eq_of_sufficient
          (left.reannotate alphabet) hLeftReFuel le_rfl]
        exact hEntryMem
      · show entry.2 ∉ (compileTypeFuel
          (typeCompilationFuel (left.reannotate alphabet))
          (left.reannotate alphabet)).accepting
        rw [← compileTypeFuel_eq_of_sufficient (left.reannotate alphabet)
          hLeftReFuel le_rfl]
        exact hNotAccepting
  · rcases Finset.mem_image.mp hSurvivorRight with ⟨entry, hEntry, hEq⟩
    have hEntryMem := (Finset.mem_filter.mp hEntry).1
    have hNotAccepting := (Finset.mem_filter.mp hEntry).2
    injection hEq with hResidual hState
    refine Or.inr (Or.inr (Or.inl ⟨entry.2, entry.1,
      by rw [← hResidual, ← hState], ?_, ?_⟩))
    · show (entry.1, entry.2) ∈
        buildRelationSetCoreFuel
          (typeCompilationFuel (right.reannotate alphabet))
          (right.reannotate alphabet)
      rw [← buildRelationSetCoreFuel_eq_of_sufficient
        (right.reannotate alphabet) hRightReFuel le_rfl]
      exact hEntryMem
    · show entry.2 ∉ (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet)).accepting
      rw [← compileTypeFuel_eq_of_sufficient (right.reannotate alphabet)
        hRightReFuel le_rfl]
      exact hNotAccepting

end


/-- The survivor image of a re-stamped component edge: it keeps source, label
and current offers, and redirects a completing target to the done state. -/
def survivorLeftEdge (restampedLeft : AutomatonFragment)
    (edge : AutomatonFragmentEdge) : PendingAutomatonEdge :=
  if edge.target ∈ restampedLeft.accepting then
    { source := .survivor 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := parallelFutureSpec edge.label edge.future
      target := .final }
  else
    { source := .survivor 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := parallelFutureSpec edge.label edge.future
      target := .survivor 0 edge.target }


/-- Exactly the re-stamped left component's edges leave a surviving-left
state, each carried by `survivorLeftEdge`. -/
theorem buildParallelAutomaton_outgoing_survivorLeft
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges ∧
      edge.source = .survivor 0 q) ↔
      ∃ childEdge ∈ resolveAutomatonEdgesWith restampedLeft restampedLeftFuture,
        childEdge.source = q ∧ edge = survivorLeftEdge restampedLeft childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with
      ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
        hRightSurvivor) | hLeftDone) | hRightDone) | hDone
    · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hRaw
      obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
      simp at hSource
    · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hLeftComplete
      obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ := hLeftComplete
      simp at hSource
    · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hRightComplete
      obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ := hRightComplete
      simp at hSource
    · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
        Finset.mem_image] at hLeftSurvivor
      obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
      simp at hSource
    · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
        Finset.mem_image] at hRightSurvivor
      obtain ⟨leftEdge, ⟨hMem, hNotAcc⟩, rfl⟩ := hRightSurvivor
      refine ⟨leftEdge, hMem, ?_, ?_⟩
      · simpa using hSource
      · simp [survivorLeftEdge, hNotAcc]
    · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
        Finset.mem_image] at hLeftDone
      obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
      simp at hSource
    · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
        Finset.mem_image] at hRightDone
      obtain ⟨leftEdge, ⟨hMem, hAcc⟩, rfl⟩ := hRightDone
      refine ⟨leftEdge, hMem, ?_, ?_⟩
      · simpa using hSource
      · simp [survivorLeftEdge, hAcc]
    · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
      obtain ⟨environment, -, rfl⟩ := hDone
      simp at hSource
  · rintro ⟨childEdge, hMem, hSource, rfl⟩
    by_cases hAcc : childEdge.target ∈ restampedLeft.accepting
    · refine ⟨?_, by simp [survivorLeftEdge, hAcc, hSource]⟩
      simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inr ?_)
      simp only [parallelRightCompleteDoneEdges, Finset.mem_image,
        Finset.mem_filter]
      exact ⟨childEdge, ⟨hMem, hAcc⟩, by simp [survivorLeftEdge, hAcc]⟩
    · refine ⟨?_, by simp [survivorLeftEdge, hAcc, hSource]⟩
      simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      simp only [parallelRightCompleteSurvivorEdges, Finset.mem_image,
        Finset.mem_filter]
      exact ⟨childEdge, ⟨hMem, hAcc⟩, by simp [survivorLeftEdge, hAcc]⟩

/-- Where a surviving-left state sends a component target: a completing one
enters the done state, any other stays in the survivor copy. -/
def survivorRedirect (restampedLeft : AutomatonFragment)
    (state : TypeAutomatonState) : TypeAutomatonState :=
  if state ∈ restampedLeft.accepting then .final else .survivor 0 state

/-- A surviving-left state publishes exactly its component's offers. -/
theorem survivorLeft_offersAt
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).offersAt (.survivor 0 q) =
      (⟨restampedLeft.states, restampedLeft.edges⟩ :
        PendingAutomaton).offersAt q := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    obtain ⟨childEdge, hChildMem, hChildSource, rfl⟩ :=
      (buildParallelAutomaton_outgoing_survivorLeft parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        edge).mp ⟨hEdge, hSource⟩
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hChildMem
    obtain ⟨original, hOriginal, rfl⟩ := hChildMem
    refine ⟨original, ⟨hOriginal, by simpa using hChildSource⟩, ?_⟩
    by_cases hAcc : original.target ∈ restampedLeft.accepting <;>
      simpa [survivorLeftEdge, hAcc] using hAction
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    let resolved : AutomatonFragmentEdge :=
      { source := edge.source, environment := edge.environment,
        label := edge.label, current := edge.current,
        future := resolveFutureSpec restampedLeftFuture edge.future,
        target := edge.target }
    have hResolved : resolved ∈ resolveAutomatonEdgesWith restampedLeft restampedLeftFuture :=
      Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    refine ⟨survivorLeftEdge restampedLeft resolved,
      (buildParallelAutomaton_outgoing_survivorLeft parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        _).mpr ⟨resolved, hResolved, hSource, rfl⟩, ?_⟩
    by_cases hAcc : edge.target ∈ restampedLeft.accepting <;>
      simpa [survivorLeftEdge, resolved, hAcc] using hAction


/-- A surviving-left state's same-cycle references are its component's,
redirected: a completing target becomes the done state. -/
theorem survivorLeft_menuStep
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).menuStep (.survivor 0 q) =
      ((⟨restampedLeft.states, restampedLeft.edges⟩ :
        PendingAutomaton).menuStep q).image
        (survivorRedirect restampedLeft) := by
  classical
  ext target
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    obtain ⟨childEdge, hChildMem, hChildSource, rfl⟩ :=
      (buildParallelAutomaton_outgoing_survivorLeft parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        _).mp ⟨hEdge, hSource⟩
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hChildMem
    obtain ⟨original, hOriginal, rfl⟩ := hChildMem
    by_cases hTock : original.label.semantic = TypeLabel.tock
    · by_cases hAcc : original.target ∈ restampedLeft.accepting <;>
        simp [survivorLeftEdge, hAcc, hTock] at hTarget
    · refine ⟨original.target,
        ⟨original, ⟨hOriginal, hChildSource⟩, by simp [hTock]⟩, ?_⟩
      by_cases hAcc : original.target ∈ restampedLeft.accepting <;>
        simpa [survivorLeftEdge, survivorRedirect, hAcc, hTock,
          eq_comm] using hTarget
  · rintro ⟨childTarget, ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩, rfl⟩
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · simp [hTock] at hTarget
    · have hEq : childTarget = edge.target := by simpa [hTock] using hTarget
      subst childTarget
      let resolved : AutomatonFragmentEdge :=
        { source := edge.source, environment := edge.environment,
          label := edge.label, current := edge.current,
          future := resolveFutureSpec restampedLeftFuture edge.future,
          target := edge.target }
      have hResolved : resolved ∈ resolveAutomatonEdgesWith restampedLeft restampedLeftFuture :=
        Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
      refine ⟨survivorLeftEdge restampedLeft resolved,
        (buildParallelAutomaton_outgoing_survivorLeft parentAlphabet leftAlphabet
          rightAlphabet interface left right restampedLeft restampedRight
          leftFuture rightFuture restampedLeftFuture restampedRightFuture q
          _).mpr ⟨resolved, hResolved, hSource, rfl⟩, ?_⟩
      by_cases hAcc : edge.target ∈ restampedLeft.accepting <;>
        simp [survivorLeftEdge, survivorRedirect, resolved, hAcc, hTock]



/-- An accepting component state offers nothing and cannot leave the accepting
set, so its whole same-cycle reach is inert. -/
theorem acceptingInert_offersAt_empty (fragment : AutomatonFragment)
    (hInert : fragment.AcceptingInert)
    (q : TypeAutomatonState) (hq : q ∈ fragment.accepting) :
    (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).offersAt q = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro action hAction
  rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
  obtain ⟨edge, hEdge, hMem⟩ := hAction
  have hEdgeMem := (Finset.mem_filter.mp hEdge).1
  have hSource := (Finset.mem_filter.mp hEdge).2
  obtain ⟨hCurrent, -, -⟩ := hInert edge hEdgeMem (hSource ▸ hq)
  by_cases hTock : edge.label.semantic = TypeLabel.tock <;>
    simp [hTock, hCurrent] at hMem


/-- The accepting set is closed under same-cycle references. -/
theorem acceptingInert_menuStep_subset (fragment : AutomatonFragment)
    (hInert : fragment.AcceptingInert)
    (q : TypeAutomatonState) (hq : q ∈ fragment.accepting) :
    (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).menuStep q ⊆
      fragment.accepting := by
  classical
  intro target hTarget
  rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hTarget
  obtain ⟨edge, hEdge, hMem⟩ := hTarget
  have hEdgeMem := (Finset.mem_filter.mp hEdge).1
  have hSource := (Finset.mem_filter.mp hEdge).2
  obtain ⟨-, hTargetAcc, -⟩ := hInert edge hEdgeMem (hSource ▸ hq)
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · simp [hTock] at hMem
  · have hEq : target = edge.target := by simpa [hTock] using hMem
    simpa [hEq] using hTargetAcc


/-- Only the idle self-loops leave the done state, and they carry no offers
and name no further state. -/
theorem buildParallelAutomaton_final_edge_shape
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges)
    (hSource : edge.source = TypeAutomatonState.final) :
    edge.current = ∅ ∧ edge.future = .explicit ∅ := by
  classical
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
    simp at hSource
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hLeftComplete
    obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ := hLeftComplete
    simp at hSource
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRightComplete
    obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ := hRightComplete
    simp at hSource
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftSurvivor
    obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
    simp at hSource
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hRightSurvivor
    obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
    simp at hSource
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftDone
    obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
    simp at hSource
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hRightDone
    obtain ⟨leftEdge, -, rfl⟩ := hRightDone
    simp at hSource
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter]
      at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    exact ⟨rfl, rfl⟩

/-- Every edge leaving the done state returns to it. -/
theorem buildParallelAutomaton_final_edge_target
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges)
    (hSource : edge.source = TypeAutomatonState.final) :
    edge.target = TypeAutomatonState.final := by
  classical
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
    simp at hSource
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hLeftComplete
    obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ := hLeftComplete
    simp at hSource
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRightComplete
    obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ := hRightComplete
    simp at hSource
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftSurvivor
    obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
    simp at hSource
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hRightSurvivor
    obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
    simp at hSource
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftDone
    obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
    simp at hSource
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hRightDone
    obtain ⟨leftEdge, -, rfl⟩ := hRightDone
    simp at hSource
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter]
      at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    rfl



variable (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
  (interface : Interface)
  (left right restampedLeft restampedRight : AutomatonFragment)
  (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
    TypeAutomatonState → Finset BareMessage)

/- The same-cycle reach of a surviving-left state is its component's reach,
redirected: states past a completion collapse onto the done state. -/
/- Superseded by the menu-graph transport below, which also includes L.
theorem survivorLeft_futureReachable
    (hTargets : ∀ edge ∈ restampedLeft.edges, ∀ target removed,
      edge.future = FutureSpec.at target removed → target = edge.target)
    (hExplicit : ∀ edge ∈ restampedLeft.edges,
      edge.label.semantic ≠ TypeLabel.tock →
      ∀ offers, edge.future = FutureSpec.explicit offers →
        edge.source ∈ restampedLeft.accepting)
    (hInert : restampedLeft.AcceptingInert)
    (hClosed : (⟨restampedLeft.states, restampedLeft.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (q : TypeAutomatonState) (hqStates : q ∈ restampedLeft.states)
    (hq : q ∉ restampedLeft.accepting) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).futureReachable (.survivor 0 q) ⊆
      ((⟨restampedLeft.states, restampedLeft.edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRedirect restampedLeft) := by
  classical
  set child : PendingAutomaton :=
    ⟨restampedLeft.states, restampedLeft.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ with hParent
  refine PendingAutomaton.futureReachable_subset_of_reference_closed parent _ _
    (Finset.mem_image.mpr ⟨q, PendingAutomaton.mem_futureReachable_self child q,
      by simp [survivorRedirect, hq]⟩) ?_
  intro state hState
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hState
  by_cases hAcc : p ∈ restampedLeft.accepting
  · -- past a completion the parent sits at the done state, which refers nowhere
    have hDone : survivorRedirect restampedLeft p = .final := by
      simp [survivorRedirect, hAcc]
    rw [hDone]
    have hEmpty : parent.referencedStates TypeAutomatonState.final = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro target hTarget
      rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at hTarget
      obtain ⟨edge, hEdge, hMem⟩ := hTarget
      have hEdgeMem := (Finset.mem_filter.mp hEdge).1
      have hSource := (Finset.mem_filter.mp hEdge).2
      obtain ⟨-, hFuture⟩ := buildParallelAutomaton_final_edge_shape
        parentAlphabet leftAlphabet rightAlphabet interface left right
        restampedLeft restampedRight leftFuture rightFuture restampedLeftFuture
        restampedRightFuture edge hEdgeMem hSource
      rw [hFuture] at hMem
      simp at hMem
    rw [hEmpty]
    exact Finset.empty_subset _
  · rw [survivorRedirect, if_neg hAcc,
      survivorLeft_referencedStates parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture hTargets hExplicit p hAcc]
    intro target hTarget
    obtain ⟨childTarget, hChildTarget, rfl⟩ := Finset.mem_image.mp hTarget
    have hqChild : q ∈ child.states := by simpa [hChild] using hqStates
    have hReachStates : child.futureReachable q ⊆ child.states :=
      PendingAutomaton.futureReachable_subset_of_reference_closed child q
        child.states hqChild (fun s hs => hClosed s hs)
    have hpStates : p ∈ child.states := hReachStates hp
    exact Finset.mem_image.mpr ⟨childTarget,
      PendingAutomaton.futureReachable_subset_of_mem child hClosed hqChild hp
        (PendingAutomaton.referencedStates_subset_futureReachable child p
          hClosed hpStates hChildTarget), rfl⟩


/-- The converse inclusion: every state the component reaches has its redirect
reached by the product. -/
theorem survivorLeft_futureReachable_ge
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hTargets : ∀ edge ∈ restampedLeft.edges, ∀ target removed,
      edge.future = FutureSpec.at target removed → target = edge.target)
    (hExplicit : ∀ edge ∈ restampedLeft.edges,
      edge.label.semantic ≠ TypeLabel.tock →
      ∀ offers, edge.future = FutureSpec.explicit offers →
        edge.source ∈ restampedLeft.accepting)
    (hInert : restampedLeft.AcceptingInert)
    (hChildClosed : (⟨restampedLeft.states, restampedLeft.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hParentClosed : (⟨(buildParallelAutomaton parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (q : TypeAutomatonState) (hqStates : q ∈ restampedLeft.states)
    (hq : q ∉ restampedLeft.accepting)
    (hSurvivorState : (TypeAutomatonState.survivor 0 q) ∈
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states) :
    ((⟨restampedLeft.states, restampedLeft.edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRedirect restampedLeft) ⊆
      (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
          interface left right restampedLeft restampedRight leftFuture
          rightFuture restampedLeftFuture restampedRightFuture).states,
        (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
          interface left right restampedLeft restampedRight leftFuture
          rightFuture restampedLeftFuture restampedRightFuture).edges⟩ :
        PendingAutomaton).futureReachable (.survivor 0 q) := by
  classical
  set child : PendingAutomaton :=
    ⟨restampedLeft.states, restampedLeft.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ with hParent
  have hAllowed : child.futureReachable q ⊆
      child.states.filter (fun p =>
        survivorRedirect restampedLeft p ∈ parent.futureReachable
          (.survivor 0 q)) := by
    refine PendingAutomaton.futureReachable_subset_of_reference_closed child q _
      (Finset.mem_filter.mpr ⟨by simpa [hChild] using hqStates, ?_⟩) ?_
    · simp only [survivorRedirect, if_neg hq]
      exact PendingAutomaton.mem_futureReachable_self parent _
    · intro p hp
      obtain ⟨hpStates, hpReach⟩ := Finset.mem_filter.mp hp
      intro t ht
      have htStates : t ∈ child.states := hChildClosed p hpStates ht
      refine Finset.mem_filter.mpr ⟨htStates, ?_⟩
      by_cases hAcc : p ∈ restampedLeft.accepting
      · have htAcc : t ∈ restampedLeft.accepting :=
          acceptingInert_referencedStates_subset restampedLeft hInert hTargets p
            hAcc ht
        simp only [survivorRedirect, if_pos htAcc]
        simpa [survivorRedirect, if_pos hAcc] using hpReach
      · have hRefEq := survivorLeft_referencedStates parentAlphabet leftAlphabet
          rightAlphabet interface left right restampedLeft restampedRight
          leftFuture rightFuture restampedLeftFuture restampedRightFuture
          hTargets hExplicit p hAcc
        have hParentRef : survivorRedirect restampedLeft t ∈
            parent.referencedStates (.survivor 0 p) := by
          rw [hRefEq]
          exact Finset.mem_image_of_mem _ ht
        have hSurvivorP : (TypeAutomatonState.survivor 0 p) ∈ parent.states := by
          have := PendingAutomaton.futureReachable_subset_of_reference_closed
            parent (.survivor 0 q) parent.states hSurvivorState
            (fun s hs => hParentClosed s hs)
          exact this (by simpa [survivorRedirect, if_neg hAcc] using hpReach)
        exact PendingAutomaton.futureReachable_subset_of_mem parent
          hParentClosed hSurvivorState
          (by simpa [survivorRedirect, if_neg hAcc] using hpReach)
          (PendingAutomaton.referencedStates_subset_futureReachable parent
            (.survivor 0 p) hParentClosed hSurvivorP hParentRef)
  intro target hTarget
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hTarget
  exact (Finset.mem_filter.mp (hAllowed hp)).2


-/


/-- A surviving-left state has the re-signed component's own menu.  Its edges
are the component's, its references are the component's redirected, and every
contribution the redirect drops is already empty. -/
theorem computeFutureOf_par_survivorLeft
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (q : TypeAutomatonState)
    (hq : q ∈ (compileTypeFuel (typeCompilationFuel (left.reannotate alphabet))
      (left.reannotate alphabet)).states)
    (hqAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel (left.reannotate alphabet))
      (left.reannotate alphabet)).accepting) :
    computeFutureOf (.par alphabet left right interface) (.survivor 0 q) =
      computeFutureOf (left.reannotate alphabet) q := by
  classical
  set childType : PactType := left.reannotate alphabet with hChildType
  set N : Nat := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hN
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      N + 1 := by simp only [hN, typeCompilationFuel]; omega
  have hChildFuel : typeCompilationFuel childType = typeCompilationFuel left := by
    rw [hChildType, typeCompilationFuel_reannotate]
  have hChildLe : typeCompilationFuel childType ≤ N := by
    rw [hChildFuel, hN]; exact le_max_left _ _
  obtain ⟨childFuel, hChildSucc⟩ :
      ∃ fuel, typeCompilationFuel childType = fuel + 1 := by
    have hPositive := typeCompilationFuel_positive childType
    exact ⟨typeCompilationFuel childType - 1, by omega⟩
  have hFragEq : compileTypeFuel N childType =
      compileTypeFuel (typeCompilationFuel childType) childType :=
    compileTypeFuel_eq_of_sufficient childType hChildLe le_rfl
  have hChildDisjoint : childType.OfferBranchesDisjoint := by
    rw [hChildType]
    exact reannotate_offerBranchesDisjoint left alphabet hLeftDisjoint
  -- the compiled component the product actually embeds
  have hqStates : q ∈ (compileTypeFuel N childType).states := by
    rw [hFragEq]; exact hq
  have hqNotAcc : q ∉ (compileTypeFuel N childType).accepting := by
    rw [hFragEq]; exact hqAcc
  have hInert := compileTypeFuel_acceptingInert N childType
  have hClosed := compileTypeFuel_menuClosed N childType hChildLe
    hChildDisjoint
  have hParEq : compileTypeFuel (N + 1) (.par alphabet left right interface) =
      buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N childType)
        (compileTypeFuel N (right.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
        (computeFutureOfFuel (min N (typeCompilationFuel right))
          (right.reannotate alphabet)) := by
    simp only [compileTypeFuel, hChildType]
  have hParentClosed := compileTypeFuel_menuClosed (N + 1)
    (.par alphabet left right interface) (by
      simp only [TypeCompilationFuelSufficient, hFuel]
      exact le_rfl) (by
      simp only [PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩)
  rw [hParEq] at hParentClosed
  have hSurvivorState : (TypeAutomatonState.survivor 0 q) ∈
      (buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N childType)
        (compileTypeFuel N (right.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
        (computeFutureOfFuel (min N (typeCompilationFuel right))
          (right.reannotate alphabet))).states := by
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_insert, Finset.mem_union]
    have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate N left
      hLeftDisjoint alphabet
    refine Or.inr (Or.inl (Or.inr (Finset.mem_image_of_mem _ ?_)))
    rw [← hShape.1, ← hChildType]
    exact hqStates
  /- Superseded raw-reach calculation; the proof below uses the graph with L.
  have hReachEq :
      (⟨(buildParallelAutomaton alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N childType)
          (compileTypeFuel N (right.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
          (computeFutureOfFuel (min N (typeCompilationFuel right))
            (right.reannotate alphabet))).states,
        (buildParallelAutomaton alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N childType)
          (compileTypeFuel N (right.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
          (computeFutureOfFuel (min N (typeCompilationFuel right))
            (right.reannotate alphabet))).edges⟩ :
        PendingAutomaton).futureReachable (.survivor 0 q) =
      ((⟨(compileTypeFuel N childType).states,
        (compileTypeFuel N childType).edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRedirect (compileTypeFuel N childType)) :=
    Finset.Subset.antisymm
      (survivorLeft_futureReachable _ _ _ _ _ _ _ _ _ _ _ _
        hTargets hExplicit hInert hClosed q hqStates hqNotAcc)
      (survivorLeft_futureReachable_ge _ _ _ _ _ _ _ _ _ _ _ _
        hTargets hExplicit hInert hClosed hParentClosed q hqStates hqNotAcc
        hSurvivorState)
  -/
  let childMenu := compiledMenuGraphFuel N childType
  let parentMenu := compiledMenuGraphFuel (N + 1) (.par alphabet left right interface)
  have hChildMenuClosed : childMenu.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed N childType hChildLe hChildDisjoint
  have hParentMenuClosed : parentMenu.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed (N + 1) (.par alphabet left right interface)
      (by change typeCompilationFuel _ ≤ N + 1; rw [hFuel])
      (by simpa only [PactType.OfferBranchesDisjoint] using And.intro hLeftDisjoint hRightDisjoint)
  have hChildLinks : compileTypeMenuLinksFuel (min N (typeCompilationFuel childType)) childType =
      compileTypeMenuLinksFuel N childType := by
    rw [Nat.min_eq_right hChildLe]
    exact (compileTypeMenuLinksFuel_eq_of_sufficient childType hChildLe le_rfl).symm
  have hParentMin : min (N + 1) (typeCompilationFuel (.par alphabet left right interface)) =
      N + 1 := by rw [hFuel]; exact Nat.min_self _
  have hDoneRefs : parentMenu.referencedStates .final ⊆ {TypeAutomatonState.final} := by
    simp only [parentMenu, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      compileTypeMenuLinksFuel_final, Finset.union_empty, hParEq]
    intro target hTarget
    rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hMem⟩ := hTarget
    have hFinal := buildParallelAutomaton_final_edge_target
      _ _ _ _ _ _ _ _ _ _ _ _ edge (Finset.mem_filter.mp hEdge).1
        (Finset.mem_filter.mp hEdge).2
    by_cases hClock : edge.label.semantic = TypeLabel.tock
    · simp [hClock] at hMem
    · simpa [hClock, hFinal] using hMem
  have hReferences : ∀ p, p ∉ (compileTypeFuel N childType).accepting →
      parentMenu.referencedStates (.survivor 0 p) =
        (childMenu.referencedStates p).image (survivorRedirect (compileTypeFuel N childType)) := by
    intro p hp
    simp only [parentMenu, childMenu, compiledMenuGraphFuel,
      PendingAutomaton.withMenuDependencies, hParentMin, hChildLinks, hParEq]
    rw [survivorLeft_menuStep _ _ _ _ _ _ _ _ _ _ _ _ p,
      menuDependencyTargets_par_survivorLeft N alphabet left right interface p hp,
      Finset.image_union]
    rfl
  have hAcceptingRefs : ∀ p ∈ (compileTypeFuel N childType).accepting,
      childMenu.referencedStates p ⊆ (compileTypeFuel N childType).accepting := by
    intro p hp
    simp only [childMenu, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      hChildLinks, compileTypeMenuLinksFuel_accepting N childType p hp, Finset.union_empty]
    exact acceptingInert_menuStep_subset _ hInert p hp
  have hCarrier : ∀ p ∈ childMenu.states,
      survivorRedirect (compileTypeFuel N childType) p ∈ parentMenu.states := by
    intro p hp
    change p ∈ (compileTypeFuel N childType).states at hp
    change survivorRedirect (compileTypeFuel N childType) p ∈
      (compileTypeFuel (N + 1) (.par alphabet left right interface)).states
    rw [hParEq]
    simp only [survivorRedirect]
    split_ifs with hAcc
    · simp [buildParallelAutomaton, finishAutomatonFragment]
    · simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_insert, Finset.mem_union]
      have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate N left
        hLeftDisjoint alphabet
      have hpOriginal : p ∈ (compileTypeFuel N left).states := by
        rw [← hShape.1, ← hChildType]
        exact hp
      exact Or.inr (Or.inl (Or.inr (Finset.mem_image_of_mem _ hpOriginal)))
  have hMenuReachEq := FiniteMenuGraph.futureReachable_eq_image_of_stuttering
    childMenu parentMenu (survivorRedirect (compileTypeFuel N childType))
    hChildMenuClosed hParentMenuClosed hCarrier
    (by
      intro p hp
      by_cases hAcc : p ∈ (compileTypeFuel N childType).accepting
      · simp only [survivorRedirect, if_pos hAcc]
        intro target hTarget
        have hEq : target = .final := Finset.mem_singleton.mp (hDoneRefs hTarget)
        subst target
        exact Finset.mem_image.mpr ⟨p, Finset.mem_insert_self _ _,
          by simp [survivorRedirect, hAcc]⟩
      · rw [show survivorRedirect (compileTypeFuel N childType) p = .survivor 0 p by
          simp [survivorRedirect, hAcc], hReferences p hAcc]
        exact Finset.image_subset_image (Finset.subset_insert _ _))
    (by
      intro p hp target hTarget
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hTarget
      by_cases hAcc : p ∈ (compileTypeFuel N childType).accepting
      · have htAcc := hAcceptingRefs p hAcc ht
        simp [survivorRedirect, hAcc, htAcc]
      · rw [show survivorRedirect (compileTypeFuel N childType) p = .survivor 0 p by
          simp [survivorRedirect, hAcc]]
        apply Finset.mem_insert_of_mem
        rw [hReferences p hAcc]
        exact Finset.mem_image_of_mem _ ht)
    q hqStates
  simp only [survivorRedirect, if_neg hqNotAcc] at hMenuReachEq
  change parentMenu.futureReachable (.survivor 0 q) =
    (childMenu.futureReachable q).image (survivorRedirect (compileTypeFuel N childType)) at hMenuReachEq
  simp only [parentMenu, childMenu, compiledMenuGraphFuel, hParEq] at hMenuReachEq
  have hFragEq' : compileTypeFuel (childFuel + 1) childType =
      compileTypeFuel N childType := by rw [← hChildSucc, ← hFragEq]
  have hAlphabet : childType.alphabet =
      (PactType.par alphabet left right interface).alphabet := by
    rw [hChildType, PactType.reannotate_alphabet]
    simp [PactType.alphabet]
  rw [computeFutureOf, computeFutureOf, hFuel, hChildSucc]
  rw [computeFutureOfFuel, computeFutureOfFuel, hParEq, hFragEq', hAlphabet]
  refine congrArg (Finset.filter _) ?_
  have hSmallLinks : min (childFuel + 1) (typeCompilationFuel childType) =
      min N (typeCompilationFuel childType) := by
    rw [← hChildSucc, Nat.min_self, Nat.min_eq_right hChildLe]
  rw [hSmallLinks, hMenuReachEq, Finset.image_biUnion]
  refine Finset.biUnion_congr rfl ?_
  intro visited _hVisited
  by_cases hAcc : visited ∈ (compileTypeFuel N childType).accepting
  · -- past a completion the parent sits at the inert done state
    have hParentOffers :
        (⟨(buildParallelAutomaton alphabet left.alphabet right.alphabet
            interface (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N childType)
            (compileTypeFuel N (right.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
            (computeFutureOfFuel (min N (typeCompilationFuel right))
              (right.reannotate alphabet))).states,
          (buildParallelAutomaton alphabet left.alphabet right.alphabet
            interface (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N childType)
            (compileTypeFuel N (right.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left)) childType)
            (computeFutureOfFuel (min N (typeCompilationFuel right))
              (right.reannotate alphabet))).edges⟩ :
          PendingAutomaton).offersAt TypeAutomatonState.final = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro action hAction
      rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
      obtain ⟨edge, hEdge, hMem⟩ := hAction
      obtain ⟨hCurrent, hFuture⟩ := buildParallelAutomaton_final_edge_shape
        _ _ _ _ _ _ _ _ _ _ _ _ edge (Finset.mem_filter.mp hEdge).1
        (Finset.mem_filter.mp hEdge).2
      rw [hCurrent] at hMem
      simp at hMem
    have hInfoFinal : stateProductInfo
        (PactType.par alphabet left right interface)
        TypeAutomatonState.final = none := by
      simp only [stateProductInfo, hFuel, stateProductInfoFuel]
    have hChildOffers :
        (⟨(compileTypeFuel N childType).states,
          (compileTypeFuel N childType).edges⟩ :
          PendingAutomaton).offersAt visited = ∅ :=
      acceptingInert_offersAt_empty _ hInert visited hAcc
    have hChildInfo : stateProductInfo childType visited = none := by
      rw [stateProductInfo]
      exact compileTypeFuel_accepting_stateProductInfoFuel_none
        (typeCompilationFuel childType) childType visited (hFragEq ▸ hAcc)
    rw [survivorRedirect, if_pos hAcc, hParentOffers, hInfoFinal, hChildOffers,
      hChildInfo]
  · -- a live survivor state publishes exactly the component's offers
    rw [survivorRedirect, if_neg hAcc,
      survivorLeft_offersAt _ _ _ _ _ _ _ _ _ _ _ _ visited]
    have hInfo : stateProductInfo (PactType.par alphabet left right interface)
        (.survivor 0 visited) = stateProductInfo childType visited := by
      simp only [stateProductInfo, hFuel, stateProductInfoFuel, ← hChildType]
      exact stateProductInfoFuel_eq_of_sufficient childType visited hChildLe
        le_rfl
    rw [hInfo]
    cases hProduct : stateProductInfo childType visited with
    | none => rfl
    | some info =>
        obtain ⟨productInterface, productLeft, productRight, q1, q2⟩ := info
        have hProductFuel :
            stateProductInfoFuel (typeCompilationFuel childType) childType
                visited =
              some (productInterface, productLeft, productRight, q1, q2) := by
          simpa [stateProductInfo] using hProduct
        obtain ⟨hLeftLt, hRightLt⟩ :=
          stateProductInfoFuel_component_fuel_lt
            (typeCompilationFuel childType) childType visited productInterface
            productLeft productRight q1 q2
            (typeCompilationFuel_sufficient childType) hProductFuel
        have hLeftSmall : TypeCompilationFuelSufficient productLeft childFuel := by
          simp only [TypeCompilationFuelSufficient] at hLeftLt ⊢
          omega
        have hRightSmall :
            TypeCompilationFuelSufficient productRight childFuel := by
          simp only [TypeCompilationFuelSufficient] at hRightLt ⊢
          omega
        have hLeftLarge : TypeCompilationFuelSufficient productLeft N := by
          simp only [TypeCompilationFuelSufficient] at hLeftSmall ⊢
          omega
        have hRightLarge : TypeCompilationFuelSufficient productRight N := by
          simp only [TypeCompilationFuelSufficient] at hRightSmall ⊢
          omega
        simp only
        rw [computeFutureOfFuel_eq_of_sufficient productLeft q1 hLeftLarge
            hLeftSmall,
          computeFutureOfFuel_eq_of_sufficient productRight q2 hRightLarge
            hRightSmall]



/-- The survivor image of a re-stamped component edge: it keeps source, label
and current offers, and redirects a completing target to the done state. -/
def survivorRightEdge (restampedRight : AutomatonFragment)
    (edge : AutomatonFragmentEdge) : PendingAutomatonEdge :=
  if edge.target ∈ restampedRight.accepting then
    { source := .survivor 1 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := parallelFutureSpec edge.label edge.future
      target := .final }
  else
    { source := .survivor 1 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := parallelFutureSpec edge.label edge.future
      target := .survivor 1 edge.target }


/-- Exactly the re-stamped right component's edges leave a surviving-right
state, each carried by `survivorRightEdge`. -/
theorem buildParallelAutomaton_outgoing_survivorRight
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges ∧
      edge.source = .survivor 1 q) ↔
      ∃ childEdge ∈ resolveAutomatonEdgesWith restampedRight
        restampedRightFuture,
        childEdge.source = q ∧
          edge = survivorRightEdge restampedRight childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with
      ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
        hRightSurvivor) | hLeftDone) | hRightDone) | hDone
    · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hRaw
      obtain ⟨leftEdge, -, rightEdge, -, rfl⟩ := hRaw
      simp at hSource
    · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hLeftComplete
      obtain ⟨leftState, -, rightEdge, -, survivorEnv, -, rfl⟩ := hLeftComplete
      simp at hSource
    · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image] at hRightComplete
      obtain ⟨rightState, -, leftEdge, -, survivorEnv, -, rfl⟩ := hRightComplete
      simp at hSource
    · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
        Finset.mem_image] at hLeftSurvivor
      obtain ⟨rightEdge, ⟨hMem, hNotAcc⟩, rfl⟩ := hLeftSurvivor
      refine ⟨rightEdge, hMem, ?_, ?_⟩
      · simpa using hSource
      · simp [survivorRightEdge, hNotAcc]
    · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
        Finset.mem_image] at hRightSurvivor
      obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
      simp at hSource
    · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
        Finset.mem_image] at hLeftDone
      obtain ⟨rightEdge, ⟨hMem, hAcc⟩, rfl⟩ := hLeftDone
      refine ⟨rightEdge, hMem, ?_, ?_⟩
      · simpa using hSource
      · simp [survivorRightEdge, hAcc]
    · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
        Finset.mem_image] at hRightDone
      obtain ⟨leftEdge, -, rfl⟩ := hRightDone
      simp at hSource
    · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
      obtain ⟨environment, -, rfl⟩ := hDone
      simp at hSource
  · rintro ⟨childEdge, hMem, hSource, rfl⟩
    by_cases hAcc : childEdge.target ∈ restampedRight.accepting
    · refine ⟨?_, by simp [survivorRightEdge, hAcc, hSource]⟩
      simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      simp only [parallelLeftCompleteDoneEdges, Finset.mem_image,
        Finset.mem_filter]
      exact ⟨childEdge, ⟨hMem, hAcc⟩, by simp [survivorRightEdge, hAcc]⟩
    · refine ⟨?_, by simp [survivorRightEdge, hAcc, hSource]⟩
      simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))
      simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_image,
        Finset.mem_filter]
      exact ⟨childEdge, ⟨hMem, hAcc⟩, by simp [survivorRightEdge, hAcc]⟩

/-- Where a surviving-right state sends a component target: a completing one
enters the done state, any other stays in the survivor copy. -/
def survivorRightRedirect (restampedRight : AutomatonFragment)
    (state : TypeAutomatonState) : TypeAutomatonState :=
  if state ∈ restampedRight.accepting then .final else .survivor 1 state

/-- A surviving-right state publishes exactly its component's offers. -/
theorem survivorRight_offersAt
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).offersAt (.survivor 1 q) =
      (⟨restampedRight.states, restampedRight.edges⟩ :
        PendingAutomaton).offersAt q := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    obtain ⟨childEdge, hChildMem, hChildSource, rfl⟩ :=
      (buildParallelAutomaton_outgoing_survivorRight parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        edge).mp ⟨hEdge, hSource⟩
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hChildMem
    obtain ⟨original, hOriginal, rfl⟩ := hChildMem
    refine ⟨original, ⟨hOriginal, by simpa using hChildSource⟩, ?_⟩
    by_cases hAcc : original.target ∈ restampedRight.accepting <;>
      simpa [survivorRightEdge, hAcc] using hAction
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    let resolved : AutomatonFragmentEdge :=
      { source := edge.source, environment := edge.environment,
        label := edge.label, current := edge.current,
        future := resolveFutureSpec restampedRightFuture edge.future,
        target := edge.target }
    have hResolved : resolved ∈ resolveAutomatonEdgesWith restampedRight restampedRightFuture :=
      Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    refine ⟨survivorRightEdge restampedRight resolved,
      (buildParallelAutomaton_outgoing_survivorRight parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        _).mpr ⟨resolved, hResolved, hSource, rfl⟩, ?_⟩
    by_cases hAcc : edge.target ∈ restampedRight.accepting <;>
      simpa [survivorRightEdge, resolved, hAcc] using hAction


/-- A surviving-right state's same-cycle references are its component's,
redirected: a completing target becomes the done state. -/
theorem survivorRight_menuStep
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (q : TypeAutomatonState) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).menuStep (.survivor 1 q) =
      ((⟨restampedRight.states, restampedRight.edges⟩ :
        PendingAutomaton).menuStep q).image
        (survivorRightRedirect restampedRight) := by
  classical
  ext target
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    obtain ⟨childEdge, hChildMem, hChildSource, rfl⟩ :=
      (buildParallelAutomaton_outgoing_survivorRight parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture q
        _).mp ⟨hEdge, hSource⟩
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hChildMem
    obtain ⟨original, hOriginal, rfl⟩ := hChildMem
    by_cases hTock : original.label.semantic = TypeLabel.tock
    · by_cases hAcc : original.target ∈ restampedRight.accepting <;>
        simp [survivorRightEdge, hAcc, hTock] at hTarget
    · refine ⟨original.target,
        ⟨original, ⟨hOriginal, hChildSource⟩, by simp [hTock]⟩, ?_⟩
      by_cases hAcc : original.target ∈ restampedRight.accepting <;>
        simpa [survivorRightEdge, survivorRightRedirect, hAcc, hTock,
          eq_comm] using hTarget
  · rintro ⟨childTarget, ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩, rfl⟩
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · simp [hTock] at hTarget
    · have hEq : childTarget = edge.target := by simpa [hTock] using hTarget
      subst childTarget
      let resolved : AutomatonFragmentEdge :=
        { source := edge.source, environment := edge.environment,
          label := edge.label, current := edge.current,
          future := resolveFutureSpec restampedRightFuture edge.future,
          target := edge.target }
      have hResolved : resolved ∈ resolveAutomatonEdgesWith restampedRight restampedRightFuture :=
        Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
      refine ⟨survivorRightEdge restampedRight resolved,
        (buildParallelAutomaton_outgoing_survivorRight parentAlphabet leftAlphabet
          rightAlphabet interface left right restampedLeft restampedRight
          leftFuture rightFuture restampedLeftFuture restampedRightFuture q
          _).mpr ⟨resolved, hResolved, hSource, rfl⟩, ?_⟩
      by_cases hAcc : edge.target ∈ restampedRight.accepting <;>
        simp [survivorRightEdge, survivorRightRedirect, resolved, hAcc, hTock]



/- The same-cycle reach of a surviving-right state is its component's reach,
redirected: states past a completion collapse onto the done state. -/
/- Superseded by the menu-graph transport below, which also includes L.
theorem survivorRight_futureReachable
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hTargets : ∀ edge ∈ restampedRight.edges, ∀ target removed,
      edge.future = FutureSpec.at target removed → target = edge.target)
    (hExplicit : ∀ edge ∈ restampedRight.edges,
      edge.label.semantic ≠ TypeLabel.tock →
      ∀ offers, edge.future = FutureSpec.explicit offers →
        edge.source ∈ restampedRight.accepting)
    (hInert : restampedRight.AcceptingInert)
    (hClosed : (⟨restampedRight.states, restampedRight.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (q : TypeAutomatonState) (hqStates : q ∈ restampedRight.states)
    (hq : q ∉ restampedRight.accepting) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).futureReachable (.survivor 1 q) ⊆
      ((⟨restampedRight.states, restampedRight.edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRightRedirect restampedRight) := by
  classical
  set child : PendingAutomaton :=
    ⟨restampedRight.states, restampedRight.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ with hParent
  refine PendingAutomaton.futureReachable_subset_of_reference_closed parent _ _
    (Finset.mem_image.mpr ⟨q, PendingAutomaton.mem_futureReachable_self child q,
      by simp [survivorRightRedirect, hq]⟩) ?_
  intro state hState
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hState
  by_cases hAcc : p ∈ restampedRight.accepting
  · -- past a completion the parent sits at the done state, which refers nowhere
    have hDone : survivorRightRedirect restampedRight p = .final := by
      simp [survivorRightRedirect, hAcc]
    rw [hDone]
    have hEmpty : parent.referencedStates TypeAutomatonState.final = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro target hTarget
      rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at hTarget
      obtain ⟨edge, hEdge, hMem⟩ := hTarget
      have hEdgeMem := (Finset.mem_filter.mp hEdge).1
      have hSource := (Finset.mem_filter.mp hEdge).2
      obtain ⟨-, hFuture⟩ := buildParallelAutomaton_final_edge_shape
        parentAlphabet leftAlphabet rightAlphabet interface left right
        restampedLeft restampedRight leftFuture rightFuture restampedLeftFuture
        restampedRightFuture edge hEdgeMem hSource
      rw [hFuture] at hMem
      simp at hMem
    rw [hEmpty]
    exact Finset.empty_subset _
  · rw [survivorRightRedirect, if_neg hAcc,
      survivorRight_referencedStates parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture hTargets hExplicit p hAcc]
    intro target hTarget
    obtain ⟨childTarget, hChildTarget, rfl⟩ := Finset.mem_image.mp hTarget
    have hqChild : q ∈ child.states := by simpa [hChild] using hqStates
    have hReachStates : child.futureReachable q ⊆ child.states :=
      PendingAutomaton.futureReachable_subset_of_reference_closed child q
        child.states hqChild (fun s hs => hClosed s hs)
    have hpStates : p ∈ child.states := hReachStates hp
    exact Finset.mem_image.mpr ⟨childTarget,
      PendingAutomaton.futureReachable_subset_of_mem child hClosed hqChild hp
        (PendingAutomaton.referencedStates_subset_futureReachable child p
          hClosed hpStates hChildTarget), rfl⟩


/-- The converse inclusion: every state the component reaches has its redirect
reached by the product. -/
theorem survivorRight_futureReachable_ge
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hTargets : ∀ edge ∈ restampedRight.edges, ∀ target removed,
      edge.future = FutureSpec.at target removed → target = edge.target)
    (hExplicit : ∀ edge ∈ restampedRight.edges,
      edge.label.semantic ≠ TypeLabel.tock →
      ∀ offers, edge.future = FutureSpec.explicit offers →
        edge.source ∈ restampedRight.accepting)
    (hInert : restampedRight.AcceptingInert)
    (hChildClosed : (⟨restampedRight.states, restampedRight.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hParentClosed : (⟨(buildParallelAutomaton parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (q : TypeAutomatonState) (hqStates : q ∈ restampedRight.states)
    (hq : q ∉ restampedRight.accepting)
    (hSurvivorState : (TypeAutomatonState.survivor 1 q) ∈
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states) :
    ((⟨restampedRight.states, restampedRight.edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRightRedirect restampedRight) ⊆
      (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
          interface left right restampedLeft restampedRight leftFuture
          rightFuture restampedLeftFuture restampedRightFuture).states,
        (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
          interface left right restampedLeft restampedRight leftFuture
          rightFuture restampedLeftFuture restampedRightFuture).edges⟩ :
        PendingAutomaton).futureReachable (.survivor 1 q) := by
  classical
  set child : PendingAutomaton :=
    ⟨restampedRight.states, restampedRight.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ with hParent
  have hAllowed : child.futureReachable q ⊆
      child.states.filter (fun p =>
        survivorRightRedirect restampedRight p ∈ parent.futureReachable
          (.survivor 1 q)) := by
    refine PendingAutomaton.futureReachable_subset_of_reference_closed child q _
      (Finset.mem_filter.mpr ⟨by simpa [hChild] using hqStates, ?_⟩) ?_
    · simp only [survivorRightRedirect, if_neg hq]
      exact PendingAutomaton.mem_futureReachable_self parent _
    · intro p hp
      obtain ⟨hpStates, hpReach⟩ := Finset.mem_filter.mp hp
      intro t ht
      have htStates : t ∈ child.states := hChildClosed p hpStates ht
      refine Finset.mem_filter.mpr ⟨htStates, ?_⟩
      by_cases hAcc : p ∈ restampedRight.accepting
      · have htAcc : t ∈ restampedRight.accepting :=
          acceptingInert_referencedStates_subset restampedRight hInert hTargets p
            hAcc ht
        simp only [survivorRightRedirect, if_pos htAcc]
        simpa [survivorRightRedirect, if_pos hAcc] using hpReach
      · have hRefEq := survivorRight_referencedStates parentAlphabet leftAlphabet
          rightAlphabet interface left right restampedLeft restampedRight
          leftFuture rightFuture restampedLeftFuture restampedRightFuture
          hTargets hExplicit p hAcc
        have hParentRef : survivorRightRedirect restampedRight t ∈
            parent.referencedStates (.survivor 1 p) := by
          rw [hRefEq]
          exact Finset.mem_image_of_mem _ ht
        have hSurvivorP : (TypeAutomatonState.survivor 1 p) ∈ parent.states := by
          have := PendingAutomaton.futureReachable_subset_of_reference_closed
            parent (.survivor 1 q) parent.states hSurvivorState
            (fun s hs => hParentClosed s hs)
          exact this (by simpa [survivorRightRedirect, if_neg hAcc] using hpReach)
        exact PendingAutomaton.futureReachable_subset_of_mem parent
          hParentClosed hSurvivorState
          (by simpa [survivorRightRedirect, if_neg hAcc] using hpReach)
          (PendingAutomaton.referencedStates_subset_futureReachable parent
            (.survivor 1 p) hParentClosed hSurvivorP hParentRef)
  intro target hTarget
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hTarget
  exact (Finset.mem_filter.mp (hAllowed hp)).2


-/


/-- A surviving-right state has the re-signed component's own menu.  Its edges
are the component's, its references are the component's redirected, and every
contribution the redirect drops is already empty. -/
theorem computeFutureOf_par_survivorRight
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (q : TypeAutomatonState)
    (hq : q ∈ (compileTypeFuel (typeCompilationFuel (right.reannotate alphabet))
      (right.reannotate alphabet)).states)
    (hqAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel (right.reannotate alphabet))
      (right.reannotate alphabet)).accepting) :
    computeFutureOf (.par alphabet left right interface) (.survivor 1 q) =
      computeFutureOf (right.reannotate alphabet) q := by
  classical
  set childType : PactType := right.reannotate alphabet with hChildType
  set N : Nat := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hN
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      N + 1 := by simp only [hN, typeCompilationFuel]; omega
  have hChildFuel : typeCompilationFuel childType = typeCompilationFuel right := by
    rw [hChildType, typeCompilationFuel_reannotate]
  have hChildLe : typeCompilationFuel childType ≤ N := by
    rw [hChildFuel, hN]; exact le_max_right _ _
  obtain ⟨childFuel, hChildSucc⟩ :
      ∃ fuel, typeCompilationFuel childType = fuel + 1 := by
    have hPositive := typeCompilationFuel_positive childType
    exact ⟨typeCompilationFuel childType - 1, by omega⟩
  have hFragEq : compileTypeFuel N childType =
      compileTypeFuel (typeCompilationFuel childType) childType :=
    compileTypeFuel_eq_of_sufficient childType hChildLe le_rfl
  have hChildDisjoint : childType.OfferBranchesDisjoint := by
    rw [hChildType]
    exact reannotate_offerBranchesDisjoint right alphabet hRightDisjoint
  -- the compiled component the product actually embeds
  have hqStates : q ∈ (compileTypeFuel N childType).states := by
    rw [hFragEq]; exact hq
  have hqNotAcc : q ∉ (compileTypeFuel N childType).accepting := by
    rw [hFragEq]; exact hqAcc
  have hInert := compileTypeFuel_acceptingInert N childType
  have hClosed := compileTypeFuel_menuClosed N childType hChildLe
    hChildDisjoint
  have hParEq : compileTypeFuel (N + 1) (.par alphabet left right interface) =
      buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N (left.reannotate alphabet))
        (compileTypeFuel N childType)
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left))
          (left.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel right)) childType) := by
    simp only [compileTypeFuel, hChildType]
  have hParentClosed := compileTypeFuel_menuClosed (N + 1)
    (.par alphabet left right interface) (by
      simp only [TypeCompilationFuelSufficient, hFuel]
      exact le_rfl) (by
      simp only [PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩)
  rw [hParEq] at hParentClosed
  have hSurvivorState : (TypeAutomatonState.survivor 1 q) ∈
      (buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N (left.reannotate alphabet))
        (compileTypeFuel N childType)
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left))
          (left.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel right)) childType)).states := by
    simp only [buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_insert, Finset.mem_union]
    have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate N right
      hRightDisjoint alphabet
    refine Or.inr (Or.inr (Finset.mem_image_of_mem _ ?_))
    rw [← hShape.1, ← hChildType]
    exact hqStates
  /- Superseded raw-reach calculation; the proof below uses the graph with L.
  have hReachEq :
      (⟨(buildParallelAutomaton alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N (left.reannotate alphabet))
          (compileTypeFuel N childType)
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left))
            (left.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel right)) childType)).states,
        (buildParallelAutomaton alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N (left.reannotate alphabet))
          (compileTypeFuel N childType)
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left))
            (left.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel right)) childType)).edges⟩ :
        PendingAutomaton).futureReachable (.survivor 1 q) =
      ((⟨(compileTypeFuel N childType).states,
        (compileTypeFuel N childType).edges⟩ :
        PendingAutomaton).futureReachable q).image
        (survivorRightRedirect (compileTypeFuel N childType)) :=
    Finset.Subset.antisymm
      (survivorRight_futureReachable _ _ _ _ _ _ _ _ _ _ _ _
        hTargets hExplicit hInert hClosed q hqStates hqNotAcc)
      (survivorRight_futureReachable_ge _ _ _ _ _ _ _ _ _ _ _ _
        hTargets hExplicit hInert hClosed hParentClosed q hqStates hqNotAcc
        hSurvivorState)
  -/
  let childMenu := compiledMenuGraphFuel N childType
  let parentMenu := compiledMenuGraphFuel (N + 1) (.par alphabet left right interface)
  have hChildMenuClosed : childMenu.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed N childType hChildLe hChildDisjoint
  have hParentMenuClosed : parentMenu.ReferencesClosed :=
    compiledMenuGraphFuel_referencesClosed (N + 1) (.par alphabet left right interface)
      (by change typeCompilationFuel _ ≤ N + 1; rw [hFuel])
      (by simpa only [PactType.OfferBranchesDisjoint] using And.intro hLeftDisjoint hRightDisjoint)
  have hChildLinks : compileTypeMenuLinksFuel (min N (typeCompilationFuel childType)) childType =
      compileTypeMenuLinksFuel N childType := by
    rw [Nat.min_eq_right hChildLe]
    exact (compileTypeMenuLinksFuel_eq_of_sufficient childType hChildLe le_rfl).symm
  have hParentMin : min (N + 1) (typeCompilationFuel (.par alphabet left right interface)) =
      N + 1 := by rw [hFuel]; exact Nat.min_self _
  have hDoneRefs : parentMenu.referencedStates .final ⊆ {TypeAutomatonState.final} := by
    simp only [parentMenu, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      compileTypeMenuLinksFuel_final, Finset.union_empty, hParEq]
    intro target hTarget
    rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hMem⟩ := hTarget
    have hFinal := buildParallelAutomaton_final_edge_target
      _ _ _ _ _ _ _ _ _ _ _ _ edge (Finset.mem_filter.mp hEdge).1
        (Finset.mem_filter.mp hEdge).2
    by_cases hClock : edge.label.semantic = TypeLabel.tock
    · simp [hClock] at hMem
    · simpa [hClock, hFinal] using hMem
  have hReferences : ∀ p, p ∉ (compileTypeFuel N childType).accepting →
      parentMenu.referencedStates (.survivor 1 p) =
        (childMenu.referencedStates p).image (survivorRightRedirect (compileTypeFuel N childType)) := by
    intro p hp
    simp only [parentMenu, childMenu, compiledMenuGraphFuel,
      PendingAutomaton.withMenuDependencies, hParentMin, hChildLinks, hParEq]
    rw [survivorRight_menuStep _ _ _ _ _ _ _ _ _ _ _ _ p,
      menuDependencyTargets_par_survivorRight N alphabet left right interface p hp,
      Finset.image_union]
    rfl
  have hAcceptingRefs : ∀ p ∈ (compileTypeFuel N childType).accepting,
      childMenu.referencedStates p ⊆ (compileTypeFuel N childType).accepting := by
    intro p hp
    simp only [childMenu, compiledMenuGraphFuel, PendingAutomaton.withMenuDependencies,
      hChildLinks, compileTypeMenuLinksFuel_accepting N childType p hp, Finset.union_empty]
    exact acceptingInert_menuStep_subset _ hInert p hp
  have hCarrier : ∀ p ∈ childMenu.states,
      survivorRightRedirect (compileTypeFuel N childType) p ∈ parentMenu.states := by
    intro p hp
    change p ∈ (compileTypeFuel N childType).states at hp
    change survivorRightRedirect (compileTypeFuel N childType) p ∈
      (compileTypeFuel (N + 1) (.par alphabet left right interface)).states
    rw [hParEq]
    simp only [survivorRightRedirect]
    split_ifs with hAcc
    · simp [buildParallelAutomaton, finishAutomatonFragment]
    · simp only [buildParallelAutomaton, finishAutomatonFragment,
        Finset.mem_insert, Finset.mem_union]
      have hShape := CompiledShape.compileTypeFuel_shapeEq_reannotate N right
        hRightDisjoint alphabet
      have hpOriginal : p ∈ (compileTypeFuel N right).states := by
        rw [← hShape.1, ← hChildType]
        exact hp
      exact Or.inr (Or.inr (Finset.mem_image_of_mem _ hpOriginal))
  have hMenuReachEq := FiniteMenuGraph.futureReachable_eq_image_of_stuttering
    childMenu parentMenu (survivorRightRedirect (compileTypeFuel N childType))
    hChildMenuClosed hParentMenuClosed hCarrier
    (by
      intro p hp
      by_cases hAcc : p ∈ (compileTypeFuel N childType).accepting
      · simp only [survivorRightRedirect, if_pos hAcc]
        intro target hTarget
        have hEq : target = .final := Finset.mem_singleton.mp (hDoneRefs hTarget)
        subst target
        exact Finset.mem_image.mpr ⟨p, Finset.mem_insert_self _ _,
          by simp [survivorRightRedirect, hAcc]⟩
      · rw [show survivorRightRedirect (compileTypeFuel N childType) p = .survivor 1 p by
          simp [survivorRightRedirect, hAcc], hReferences p hAcc]
        exact Finset.image_subset_image (Finset.subset_insert _ _))
    (by
      intro p hp target hTarget
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hTarget
      by_cases hAcc : p ∈ (compileTypeFuel N childType).accepting
      · have htAcc := hAcceptingRefs p hAcc ht
        simp [survivorRightRedirect, hAcc, htAcc]
      · rw [show survivorRightRedirect (compileTypeFuel N childType) p = .survivor 1 p by
          simp [survivorRightRedirect, hAcc]]
        apply Finset.mem_insert_of_mem
        rw [hReferences p hAcc]
        exact Finset.mem_image_of_mem _ ht)
    q hqStates
  simp only [survivorRightRedirect, if_neg hqNotAcc] at hMenuReachEq
  change parentMenu.futureReachable (.survivor 1 q) =
    (childMenu.futureReachable q).image (survivorRightRedirect (compileTypeFuel N childType)) at hMenuReachEq
  simp only [parentMenu, childMenu, compiledMenuGraphFuel, hParEq] at hMenuReachEq
  have hFragEq' : compileTypeFuel (childFuel + 1) childType =
      compileTypeFuel N childType := by rw [← hChildSucc, ← hFragEq]
  have hAlphabet : childType.alphabet =
      (PactType.par alphabet left right interface).alphabet := by
    rw [hChildType, PactType.reannotate_alphabet]
    simp [PactType.alphabet]
  rw [computeFutureOf, computeFutureOf, hFuel, hChildSucc]
  rw [computeFutureOfFuel, computeFutureOfFuel, hParEq, hFragEq', hAlphabet]
  refine congrArg (Finset.filter _) ?_
  have hSmallLinks : min (childFuel + 1) (typeCompilationFuel childType) =
      min N (typeCompilationFuel childType) := by
    rw [← hChildSucc, Nat.min_self, Nat.min_eq_right hChildLe]
  rw [hSmallLinks, hMenuReachEq, Finset.image_biUnion]
  refine Finset.biUnion_congr rfl ?_
  intro visited _hVisited
  by_cases hAcc : visited ∈ (compileTypeFuel N childType).accepting
  · -- past a completion the parent sits at the inert done state
    have hParentOffers :
        (⟨(buildParallelAutomaton alphabet left.alphabet right.alphabet
            interface (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N (left.reannotate alphabet))
            (compileTypeFuel N childType)
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel right)) childType)).states,
          (buildParallelAutomaton alphabet left.alphabet right.alphabet
            interface (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N (left.reannotate alphabet))
            (compileTypeFuel N childType)
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel right)) childType)).edges⟩ :
          PendingAutomaton).offersAt TypeAutomatonState.final = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro action hAction
      rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
      obtain ⟨edge, hEdge, hMem⟩ := hAction
      obtain ⟨hCurrent, hFuture⟩ := buildParallelAutomaton_final_edge_shape
        _ _ _ _ _ _ _ _ _ _ _ _ edge (Finset.mem_filter.mp hEdge).1
        (Finset.mem_filter.mp hEdge).2
      rw [hCurrent] at hMem
      simp at hMem
    have hInfoFinal : stateProductInfo
        (PactType.par alphabet left right interface)
        TypeAutomatonState.final = none := by
      simp only [stateProductInfo, hFuel, stateProductInfoFuel]
    have hChildOffers :
        (⟨(compileTypeFuel N childType).states,
          (compileTypeFuel N childType).edges⟩ :
          PendingAutomaton).offersAt visited = ∅ :=
      acceptingInert_offersAt_empty _ hInert visited hAcc
    have hChildInfo : stateProductInfo childType visited = none := by
      rw [stateProductInfo]
      exact compileTypeFuel_accepting_stateProductInfoFuel_none
        (typeCompilationFuel childType) childType visited (hFragEq ▸ hAcc)
    rw [survivorRightRedirect, if_pos hAcc, hParentOffers, hInfoFinal, hChildOffers,
      hChildInfo]
  · -- a live survivor state publishes exactly the component's offers
    rw [survivorRightRedirect, if_neg hAcc,
      survivorRight_offersAt _ _ _ _ _ _ _ _ _ _ _ _ visited]
    have hInfo : stateProductInfo (PactType.par alphabet left right interface)
        (.survivor 1 visited) = stateProductInfo childType visited := by
      simp only [stateProductInfo, hFuel, stateProductInfoFuel, ← hChildType]
      exact stateProductInfoFuel_eq_of_sufficient childType visited hChildLe
        le_rfl
    rw [hInfo]
    cases hProduct : stateProductInfo childType visited with
    | none => rfl
    | some info =>
        obtain ⟨productInterface, productLeft, productRight, q1, q2⟩ := info
        have hProductFuel :
            stateProductInfoFuel (typeCompilationFuel childType) childType
                visited =
              some (productInterface, productLeft, productRight, q1, q2) := by
          simpa [stateProductInfo] using hProduct
        obtain ⟨hLeftLt, hRightLt⟩ :=
          stateProductInfoFuel_component_fuel_lt
            (typeCompilationFuel childType) childType visited productInterface
            productLeft productRight q1 q2
            (typeCompilationFuel_sufficient childType) hProductFuel
        have hLeftSmall : TypeCompilationFuelSufficient productLeft childFuel := by
          simp only [TypeCompilationFuelSufficient] at hLeftLt ⊢
          omega
        have hRightSmall :
            TypeCompilationFuelSufficient productRight childFuel := by
          simp only [TypeCompilationFuelSufficient] at hRightLt ⊢
          omega
        have hLeftLarge : TypeCompilationFuelSufficient productLeft N := by
          simp only [TypeCompilationFuelSufficient] at hLeftSmall ⊢
          omega
        have hRightLarge : TypeCompilationFuelSufficient productRight N := by
          simp only [TypeCompilationFuelSufficient] at hRightSmall ⊢
          omega
        simp only
        rw [computeFutureOfFuel_eq_of_sufficient productLeft q1 hLeftLarge
            hLeftSmall,
          computeFutureOfFuel_eq_of_sufficient productRight q2 hRightLarge
            hRightSmall]


/-! ### Survivor alphabet projection, in the form the parallel menu uses it -/

/-- The parent of a compatible parallel node declares no interface action. -/
theorem parent_no_interface
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right
      interface)
    {action : BareMessage} (hAction : action ∈ parent.actions) :
    action.1 ∉ interface :=
  hCompatible.parent_hides_interface action hAction

/-- Every non-interface action of the left child is declared by the parent. -/
theorem child_noninterface_subset_left
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right
      interface)
    {action : BareMessage} (hAction : action ∈ left.actions)
    (hInterface : action.1 ∉ interface) :
    action ∈ parent.actions := by
  rw [← hCompatible.parent_eq_left]
  simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
  exact ⟨hAction, hInterface⟩

/-- The mirror for the right child. -/
theorem child_noninterface_subset_right
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right
      interface)
    {action : BareMessage} (hAction : action ∈ right.actions)
    (hInterface : action.1 ∉ interface) :
    action ∈ parent.actions := by
  rw [← hCompatible.parent_eq_right]
  simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
  exact ⟨hAction, hInterface⟩

/-- Gating by the parent alphabet is exactly hiding the interface, on any
menu the two children can publish. -/
theorem filter_parent_actions_eq_hide
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : PactTypeAlphabet.ParallelCompatible parent left right
      interface)
    (menu : Finset BareMessage)
    (hMenu : menu ⊆ left.actions ∪ right.actions) :
    menu.filter (fun action => action ∈ parent.actions) =
      hideTypeOffers interface menu := by
  classical
  ext action
  simp only [hideTypeOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hMem, hParent⟩
    exact ⟨hMem, parent_no_interface hCompatible hParent⟩
  · rintro ⟨hMem, hInterface⟩
    refine ⟨hMem, ?_⟩
    rcases Finset.mem_union.mp (hMenu hMem) with hLeft | hRight
    · exact child_noninterface_subset_left hCompatible hLeft hInterface
    · exact child_noninterface_subset_right hCompatible hRight hInterface

/-! ### Same-cycle menus shrink along the same-cycle reach -/

/-- A state reached before the next clock offers no more than its source: both
menus are the same union over reaches, and the reach of the target is contained
in the reach of the source. -/
theorem computeFutureOf_mono_of_futureReachable
    (processType : PactType) (hDisjoint : processType.OfferBranchesDisjoint)
    {source target : TypeAutomatonState}
    (hSource : source ∈ (compileTypeFuel
      (typeCompilationFuel processType) processType).states)
    (hTarget : target ∈
      (⟨(compileTypeFuel (typeCompilationFuel processType)
          processType).states,
        (compileTypeFuel (typeCompilationFuel processType)
          processType).edges⟩ : PendingAutomaton).futureReachable source) :
    computeFutureOf processType target ⊆ computeFutureOf processType source := by
  classical
  obtain ⟨fuel, hFuel⟩ : ∃ fuel, typeCompilationFuel processType = fuel + 1 :=
    ⟨typeCompilationFuel processType - 1, by
      have := typeCompilationFuel_positive processType; omega⟩
  have hClosed := compiledMenuGraphFuel_referencesClosed
    (typeCompilationFuel processType) processType le_rfl hDisjoint
  simp only [compiledMenuGraphFuel, Nat.min_self] at hClosed
  have hTargetMenu := PendingAutomaton.futureReachable_subset_withMenuDependencies
    (⟨(compileTypeFuel (typeCompilationFuel processType) processType).states,
      (compileTypeFuel (typeCompilationFuel processType) processType).edges⟩ :
      PendingAutomaton)
    (compileTypeMenuLinksFuel (typeCompilationFuel processType) processType)
    hClosed source hSource hTarget
  have hReach := FiniteMenuGraph.futureReachable_subset_of_mem
    _ hClosed hSource hTargetMenu
  rw [hFuel] at hReach
  rw [computeFutureOf, computeFutureOf, hFuel]
  rw [computeFutureOfFuel, computeFutureOfFuel]
  simp only [hFuel, Nat.min_self]
  exact Finset.filter_subset_filter _ (Finset.biUnion_subset_biUnion_of_subset_left _ hReach)

/-! ### Re-signing narrows a same-cycle menu

The menu half of `<re-signing-invariance>`.  The paper leaves it implicit: at a
product state the entry families leave for a survivor state, whose menu is the
re-signed component's.  Re-signing a child by the parent alphabet only narrows
the `.message` gate, because `ParallelCompatible` puts the parent's actions
inside the child's. -/

/-- Re-signing branches rewrites each branch type and keeps the action. -/
private theorem reannotateBranches_eq_map (target : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.reannotateBranches target branches =
        branches.map (fun b => (b.1, b.2.reannotate target)) := by
  intro branches
  induction branches with
  | nil => simp
  | cons hd tl ih => rcases hd with ⟨a, p⟩; simp [ih]

/-- The `seen` set threads through unused, so offer branches re-sign the same
way ordinary branches do. -/
private theorem reannotateOfferBranches_eq_map (target : PactTypeAlphabet)
    (seen : Finset BareMessage) :
    ∀ branches : List (BareMessage × PactType),
      PactType.reannotateOfferBranches target seen branches =
        branches.map (fun b => (b.1, b.2.reannotate target)) := by
  intro branches
  induction branches with
  | nil => simp [PactType.reannotateOfferBranches_nil]
  | cons hd tl ih =>
      rcases hd with ⟨a, p⟩
      simp [PactType.reannotateOfferBranches_cons, ih]

/-- The offer fold is monotone in its seed and in the per-branch menu. -/
private theorem foldl_offers_mono
    (f g : (BareMessage × PactType) → Finset BareMessage) :
    ∀ (branches : List (BareMessage × PactType))
      (a b : Finset BareMessage), a ⊆ b →
      (∀ x ∈ branches, f x ⊆ g x) →
      branches.foldl (fun offers br => offers ∪ {br.1} ∪ f br) a ⊆
        branches.foldl (fun offers br => offers ∪ {br.1} ∪ g br) b := by
  intro branches
  induction branches with
  | nil => intro a b h _; exact h
  | cons hd tl ih =>
      intro a b h hf
      simp only [List.foldl_cons]
      apply ih
      · exact Finset.union_subset_union
          (Finset.union_subset_union h (Finset.Subset.refl _))
          (hf hd (List.mem_cons_self ..))
      · intro x hx; exact hf x (List.mem_cons_of_mem _ hx)

/-- Every branch of a well-formed disjunctive offer carries the node alphabet. -/
theorem branchesWF_mem {alphabet : PactTypeAlphabet} :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.BranchesAlphabetWellFormed alphabet branches →
      ∀ b ∈ branches, b.2.alphabet = alphabet ∧ b.2.AlphabetWellFormed := by
  intro branches
  induction branches with
  | nil => intro _ b hb; cases hb
  | cons hd tl ih =>
      rcases hd with ⟨a, p⟩
      intro hWF b hb
      rw [PactType.BranchesAlphabetWellFormed] at hWF
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hWF.1, hWF.2.1⟩
      · exact ih hWF.2.2 b hb

/-- Mirror for conjunctive offers. -/
theorem offerBranchesWF_mem {alphabet : PactTypeAlphabet}
    {seen : Finset BareMessage} :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.OfferBranchesWellFormed alphabet seen branches →
      ∀ b ∈ branches, b.2.alphabet = alphabet ∧ b.2.AlphabetWellFormed := by
  intro branches
  induction branches with
  | nil => intro _ b hb; cases hb
  | cons hd tl ih =>
      rcases hd with ⟨a, p⟩
      intro hWF b hb
      rw [PactType.OfferBranchesWellFormed] at hWF
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hWF.1, hWF.2.1⟩
      · exact ih hWF.2.2 b hb

/-- Narrowing declarations cannot enable optimistic completion. -/
theorem typeCanCompleteThisCycle_reannotate_subset
    (processType : PactType) (target : PactTypeAlphabet)
    (hWF : processType.AlphabetWellFormed)
    (hActions : target.actions ⊆ processType.alphabet.actions) :
    ∀ fuel : Nat,
      typeCanCompleteThisCycleFuel fuel (processType.reannotate target) = true →
        typeCanCompleteThisCycleFuel fuel processType = true := by
  intro fuel
  induction fuel generalizing processType target with
  | zero => simp [typeCanCompleteThisCycleFuel]
  | succ fuel ih =>
      cases processType with
      | message alphabet msg dir =>
          simpa only [PactType.reannotate, typeCanCompleteThisCycleFuel, decide_eq_true_eq]
            using (fun h => hActions h : (msg, dir) ∈ target.actions → (msg, dir) ∈ alphabet.actions)
      | progress _ _ | skip _ | tock _ | var _ _ =>
          simp [PactType.reannotate, typeCanCompleteThisCycleFuel]
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel]
          exact ih body target hWF.2.2 (by rw [hWF.2.1]; exact hActions)
      | choice alphabet left right | fairChoice alphabet bid left right
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          have hL := ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hActions)
          have hR := ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hActions)
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel,
            Bool.or_eq_true, Bool.and_eq_true]
          first | exact Or.imp hL hR | exact fun h => ⟨hL h.1, hR h.2⟩
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          obtain ⟨_, hCompat, hL, hR⟩ := hWF
          have hSubL : (PactTypeAlphabet.projectParallel target left.alphabet interface).actions ⊆
              left.alphabet.actions := by
            intro a ha
            rcases Finset.mem_union.mp ha with ha | ha
            · exact (Finset.mem_filter.mp ha).1
            · exact PactTypeAlphabet.parent_actions_subset_left hCompat (hActions ha)
          have hSubR : (PactTypeAlphabet.projectParallel target right.alphabet interface).actions ⊆
              right.alphabet.actions := by
            intro a ha
            rcases Finset.mem_union.mp ha with ha | ha
            · exact (Finset.mem_filter.mp ha).1
            · exact PactTypeAlphabet.parent_actions_subset_right hCompat (hActions ha)
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel, Bool.and_eq_true]
          exact fun h => ⟨ih left _ hL hSubL h.1, ih right _ hR hSubR h.2⟩
      | xoffer alphabet other branches | offer alphabet other branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          obtain ⟨_, hOtherA, hOther, hBranches⟩ := hWF
          have hEvery : ∀ b ∈ branches, b.2.alphabet = alphabet ∧ b.2.AlphabetWellFormed := by
            first | exact branchesWF_mem branches hBranches | exact offerBranchesWF_mem branches hBranches
          simp only [PactType.reannotate, typeCanCompleteThisCycleFuel,
            reannotateBranches_eq_map, reannotateOfferBranches_eq_map,
            Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
          rintro ⟨hGate, hElse | ⟨b, hMem, hComplete⟩⟩
          · refine ⟨?_, Or.inl (ih other target hOther (by rw [hOtherA]; exact hActions) hElse)⟩
            intro b hb
            exact hActions (hGate (b.1, b.2.reannotate target) (List.mem_map_of_mem hb))
          · obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hMem
            refine ⟨?_, Or.inr ⟨original, hOriginal, ?_⟩⟩
            · intro b hb
              exact hActions (hGate (b.1, b.2.reannotate target) (List.mem_map_of_mem hb))
            · obtain ⟨hA, hW⟩ := hEvery original hOriginal
              exact ih original.2 target hW (by rw [hA]; exact hActions) hComplete

/-- Fuel-indexed form of the menu bound. -/
private theorem typeFutureOffersFuel_reannotate_subset :
    ∀ (fuel : Nat) (processType : PactType) (target : PactTypeAlphabet),
      processType.AlphabetWellFormed →
      target.actions ⊆ processType.alphabet.actions →
      typeFutureOffersFuel fuel (processType.reannotate target) ⊆
        typeFutureOffersFuel fuel processType := by
  intro fuel
  induction fuel with
  | zero => intro p t _ _; simp [typeFutureOffersFuel]
  | succ fuel ih =>
      intro processType target hWF hActions
      cases processType with
      | message alphabet msg dir =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          by_cases hg : (msg, dir) ∈ target.actions
          · have : (msg, dir) ∈ alphabet.actions := by
              apply hActions; exact hg
            simp [hg, this]
          · rw [if_neg hg]
            exact Finset.empty_subset _
      | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, typeFutureOffersFuel]
      | recur alphabet name body =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          apply ih body target hWF.2.2
          rw [hWF.2.1]
          simpa [PactType.alphabet] using hActions
      | choice alphabet left right =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          exact Finset.union_subset_union
            (ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hActions))
            (ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hActions))
      | fairChoice alphabet bid left right =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          exact Finset.union_subset_union
            (ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hActions))
            (ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hActions))
      | seq alphabet left right =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          have hL := ih left target hWF.2.2.2.1 (by rw [hWF.2.1]; exact hActions)
          have hR := ih right target hWF.2.2.2.2 (by rw [hWF.2.2.1]; exact hActions)
          by_cases hc : typeCanCompleteThisCycleFuel fuel (left.reannotate target) = true
          · have hc' := typeCanCompleteThisCycle_reannotate_subset left target hWF.2.2.2.1
              (by rw [hWF.2.1]; exact hActions) fuel hc
            simp only [hc, hc', if_true]
            exact Finset.union_subset_union hL hR
          · simp only [hc, Bool.false_eq_true, if_false]
            split_ifs
            · exact Finset.Subset.trans hL (Finset.subset_union_left)
            · exact hL
      | par alphabet left right interface =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          obtain ⟨hAWF, hCompat, hWFL, hWFR⟩ := hWF
          have hSubL : (PactTypeAlphabet.projectParallel target left.alphabet
              interface).actions ⊆ left.alphabet.actions := by
            intro a ha
            simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
              Finset.mem_filter] at ha
            rcases ha with h | h
            · exact h.1
            · exact PactTypeAlphabet.parent_actions_subset_left hCompat (hActions h)
          have hSubR : (PactTypeAlphabet.projectParallel target right.alphabet
              interface).actions ⊆ right.alphabet.actions := by
            intro a ha
            simp only [PactTypeAlphabet.projectParallel, Finset.mem_union,
              Finset.mem_filter] at ha
            rcases ha with h | h
            · exact h.1
            · exact PactTypeAlphabet.parent_actions_subset_right hCompat (hActions h)
          apply Finset.filter_subset_filter
          exact Finset.union_subset_union (ih left _ hWFL hSubL) (ih right _ hWFR hSubR)
      | xoffer alphabet elseType branches =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          obtain ⟨hAWF, hElseA, hWFE, hWFB⟩ := hWF
          rw [reannotateBranches_eq_map]
          by_cases hg : ∀ b ∈ branches.map (fun b => (b.1, b.2.reannotate target)),
              b.1 ∈ target.actions
          · have hg' : ∀ b ∈ branches, b.1 ∈ alphabet.actions := by
              intro b hb
              refine hActions (hg (b.1, b.2.reannotate target) ?_)
              exact List.mem_map_of_mem hb
            rw [if_pos hg, if_pos hg', List.foldl_map]
            refine foldl_offers_mono _ _ branches _ _
              (ih elseType target hWFE (by rw [hElseA]; exact hActions)) ?_
            intro x hx
            obtain ⟨hxA, hxW⟩ := branchesWF_mem branches hWFB x hx
            exact ih x.2 target hxW (by rw [hxA]; exact hActions)
          · rw [if_neg hg]
            exact Finset.empty_subset _
      | offer alphabet elseType branches =>
          simp only [PactType.reannotate, typeFutureOffersFuel]
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.alphabet] at hActions
          obtain ⟨hAWF, hElseA, hWFE, hWFB⟩ := hWF
          rw [reannotateOfferBranches_eq_map]
          by_cases hg : ∀ b ∈ branches.map (fun b => (b.1, b.2.reannotate target)),
              b.1 ∈ target.actions
          · have hg' : ∀ b ∈ branches, b.1 ∈ alphabet.actions := by
              intro b hb
              refine hActions (hg (b.1, b.2.reannotate target) ?_)
              exact List.mem_map_of_mem hb
            rw [if_pos hg, if_pos hg', List.foldl_map]
            refine foldl_offers_mono _ _ branches _ _
              (ih elseType target hWFE (by rw [hElseA]; exact hActions)) ?_
            intro x hx
            obtain ⟨hxA, hxW⟩ := offerBranchesWF_mem branches hWFB x hx
            exact ih x.2 target hxW (by rw [hxA]; exact hActions)
          · rw [if_neg hg]
            exact Finset.empty_subset _

/-- Re-signing a type by an alphabet it already covers can only shrink its
same-cycle menu. -/
theorem typeFutureOffers_reannotate_subset
    (processType : PactType) (target : PactTypeAlphabet)
    (hWF : processType.AlphabetWellFormed)
    (hActions : target.actions ⊆ processType.alphabet.actions) :
    typeFutureOffers (processType.reannotate target) ⊆
      typeFutureOffers processType := by
  unfold typeFutureOffers
  rw [PactType.reannotate_sizeOf processType target]
  exact typeFutureOffersFuel_reannotate_subset _ processType target hWF hActions

/-! ### What leaves a product state -/

/-- Every edge out of a product state is a synchronized product edge, or one of
the two entry families that fire once a component has completed.  Only the
forward direction is needed: the menu bound reads the shapes off, and the
product term supplies the other inclusion on its own. -/
theorem buildParallelAutomaton_outgoing_pair
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (p1 p2 : TypeAutomatonState) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges)
    (hSource : edge.source = .pair p1 p2) :
    (∃ leftEdge ∈ resolveAutomatonEdgesWith left leftFuture,
        ∃ rightEdge ∈ resolveAutomatonEdgesWith right rightFuture,
          leftEdge.source = p1 ∧ rightEdge.source = p2 ∧
            edge.current =
              hideOffers interface (leftEdge.current ∪ rightEdge.current) ∧
            edge.label = AutomatonConstructionLabel.combine interface
              leftEdge.label rightEdge.label ∧
            syncAutomatonEdges leftAlphabet rightAlphabet interface leftEdge
              rightEdge ∧
            (edge.target = .final ∨
              edge.target = .pair leftEdge.target rightEdge.target)) ∨
      (∃ leftEdge ∈ resolveAutomatonEdgesWith left leftFuture,
        ∃ rightEdge ∈ resolveAutomatonEdgesWith right rightFuture,
          leftEdge.source = p1 ∧ rightEdge.source = p2 ∧
            edge.current =
              hideOffers interface (leftEdge.current ∪ rightEdge.current) ∧
            edge.label = AutomatonConstructionLabel.combine interface
              leftEdge.label rightEdge.label ∧
            syncAutomatonEdges leftAlphabet rightAlphabet interface leftEdge
              rightEdge ∧
            edge.target = .survivor 1 rightEdge.target) ∨
      (∃ leftEdge ∈ resolveAutomatonEdgesWith left leftFuture,
        ∃ rightEdge ∈ resolveAutomatonEdgesWith right rightFuture,
          leftEdge.source = p1 ∧ rightEdge.source = p2 ∧
            edge.current =
              hideOffers interface (leftEdge.current ∪ rightEdge.current) ∧
            edge.label = AutomatonConstructionLabel.combine interface
              leftEdge.label rightEdge.label ∧
            syncAutomatonEdges leftAlphabet rightAlphabet interface leftEdge
              rightEdge ∧
            edge.target = .survivor 0 leftEdge.target) := by
  classical
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, -⟩, rfl⟩ := hRaw
    simp only at hSource
    injection hSource with hLeftSource hRightSource
    refine Or.inl ⟨leftEdge, hLeftMem, rightEdge, hRightMem, hLeftSource,
      hRightSource, rfl, rfl, hSync, ?_⟩
    · by_cases hBoth : leftEdge.target ∈ left.accepting ∧
        rightEdge.target ∈ right.accepting
      · exact Or.inl (by simp [hBoth])
      · exact Or.inr (by simp [hBoth])
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hLeftComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, -⟩, rfl⟩ :=
      hLeftComplete
    simp only at hSource
    injection hSource with hLeftSource hRightSource
    exact Or.inr (Or.inl ⟨leftEdge, hLeftMem, rightEdge, hRightMem, hLeftSource,
      hRightSource, rfl, rfl, hSync, rfl⟩)
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRightComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, -⟩, rfl⟩ :=
      hRightComplete
    simp only at hSource
    injection hSource with hLeftSource hRightSource
    exact Or.inr (Or.inr ⟨leftEdge, hLeftMem, rightEdge, hRightMem, hLeftSource,
      hRightSource, rfl, rfl, hSync, rfl⟩)
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftSurvivor
    obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
    simp at hSource
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hRightSurvivor
    obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
    simp at hSource
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftDone
    obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
    simp at hSource
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hRightDone
    obtain ⟨leftEdge, -, rfl⟩ := hRightDone
    simp at hSource
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    simp at hSource


/-- A resolved non-clock edge contributes its execution target to the menu graph. -/
theorem resolved_target_mem_menuStep
    (fragment : AutomatonFragment)
    (future : TypeAutomatonState → Finset BareMessage)
    {resolved : AutomatonFragmentEdge}
    (hResolved : resolved ∈ resolveAutomatonEdgesWith fragment future)
    {p : TypeAutomatonState} (hSource : resolved.source = p)
    (hTock : resolved.label.semantic ≠ TypeLabel.tock) :
    resolved.target ∈
      (⟨fragment.states, fragment.edges⟩ :
        PendingAutomaton).menuStep p := by
  classical
  simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hResolved
  obtain ⟨original, hOriginal, rfl⟩ := hResolved
  rw [PendingAutomaton.menuStep, Finset.mem_biUnion]
  exact ⟨original, Finset.mem_filter.mpr ⟨hOriginal, hSource⟩, by simp [hTock]⟩

/-- A synchronized product edge is a clock edge exactly when both its component
edges are, so a non-clock product edge has two non-clock components. -/
theorem sync_components_not_tock
    (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    {leftEdge rightEdge : AutomatonFragmentEdge}
    (hSync : syncAutomatonEdges leftAlphabet rightAlphabet interface leftEdge
      rightEdge)
    (hCombined : (AutomatonConstructionLabel.combine interface leftEdge.label
      rightEdge.label).semantic ≠ TypeLabel.tock) :
    leftEdge.label.semantic ≠ TypeLabel.tock ∧
      rightEdge.label.semantic ≠ TypeLabel.tock := by
  classical
  obtain ⟨-, -, -, -, -, -, hLabels⟩ := hSync
  obtain ⟨-, -, hTockIff⟩ := hLabels
  constructor
  · intro hLeft
    refine hCombined ?_
    have hRight : rightEdge.label.semantic = TypeLabel.tock := by
      have : TypeLabel.isTock rightEdge.label.semantic :=
        hTockIff.mp (by rw [hLeft]; trivial)
      cases hForm : rightEdge.label.semantic with
      | tock => rfl
      | actions _ =>
          rw [hForm] at this; exact absurd this (by simp [TypeLabel.isTock])
    cases hLeftForm : leftEdge.label with
    | «variable» name =>
        rw [hLeftForm] at hLeft
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hLeft
    | visible leftLabel =>
        cases hRightForm : rightEdge.label with
        | «variable» name =>
            rw [hRightForm] at hRight
            simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
              at hRight
        | visible rightLabel =>
            rw [hLeftForm] at hLeft
            rw [hRightForm] at hRight
            simp only [AutomatonConstructionLabel.semantic] at hLeft hRight
            simp only [AutomatonConstructionLabel.combine,
              AutomatonConstructionLabel.semantic, hLeft, hRight,
              TypeLabel.combine]
  · intro hRight
    refine hCombined ?_
    have hLeft : leftEdge.label.semantic = TypeLabel.tock := by
      have : TypeLabel.isTock leftEdge.label.semantic :=
        hTockIff.mpr (by rw [hRight]; trivial)
      cases hForm : leftEdge.label.semantic with
      | tock => rfl
      | actions _ =>
          rw [hForm] at this; exact absurd this (by simp [TypeLabel.isTock])
    cases hLeftForm : leftEdge.label with
    | «variable» name =>
        rw [hLeftForm] at hLeft
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hLeft
    | visible leftLabel =>
        cases hRightForm : rightEdge.label with
        | «variable» name =>
            rw [hRightForm] at hRight
            simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
              at hRight
        | visible rightLabel =>
            rw [hLeftForm] at hLeft
            rw [hRightForm] at hRight
            simp only [AutomatonConstructionLabel.semantic] at hLeft hRight
            simp only [AutomatonConstructionLabel.combine,
              AutomatonConstructionLabel.semantic, hLeft, hRight,
              TypeLabel.combine]

/-- What a product state can name before the next clock: another product state
built from the two components' own references, a survivor entered once one
component has completed, or the done state. -/
theorem buildParallelAutomaton_pair_menuStep_subset
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (p1 p2 : TypeAutomatonState) :
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).menuStep (.pair p1 p2) ⊆
      insert TypeAutomatonState.final
        ((((⟨left.states, left.edges⟩ :
              PendingAutomaton).menuStep p1) ×ˢ
            ((⟨right.states, right.edges⟩ :
              PendingAutomaton).menuStep p2)).image
            (fun pair => TypeAutomatonState.pair pair.1 pair.2) ∪
          ((((⟨right.states, right.edges⟩ :
              PendingAutomaton).menuStep p2).filter
              (fun t => t ∉ right.accepting)).image
            (TypeAutomatonState.survivor 1)) ∪
          ((((⟨left.states, left.edges⟩ :
              PendingAutomaton).menuStep p1).filter
              (fun s => s ∉ left.accepting)).image
            (TypeAutomatonState.survivor 0))) := by
  classical
  intro reference hReference
  rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hReference
  obtain ⟨edge, hEdge, hMem⟩ := hReference
  have hEdgeMem := (Finset.mem_filter.mp hEdge).1
  have hSource := (Finset.mem_filter.mp hEdge).2
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · rw [if_pos hTock] at hMem; simp at hMem
  rw [if_neg hTock] at hMem
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdgeMem
  rcases hEdgeMem with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · -- a synchronized product edge
    simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, hLive⟩, rfl⟩ := hRaw
    simp only at hSource hTock hMem
    injection hSource with hLeftSource hRightSource
    by_cases hBoth : leftEdge.target ∈ left.accepting ∧
        rightEdge.target ∈ right.accepting
    · rw [if_pos hBoth] at hMem
      simp only [Finset.mem_singleton] at hMem
      exact hMem ▸ Finset.mem_insert_self _ _
    · rw [if_neg hBoth] at hMem
      simp only [Finset.mem_singleton] at hMem
      obtain ⟨hLeftLive, hRightLive⟩ := hLive hBoth
      obtain ⟨hLeftTock, hRightTock⟩ :=
        sync_components_not_tock leftAlphabet rightAlphabet interface hSync
          (by simpa using hTock)
      refine Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_left _ ?_))
      rw [hMem]
      refine Finset.mem_image.mpr ⟨(leftEdge.target, rightEdge.target), ?_, rfl⟩
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact resolved_target_mem_menuStep left leftFuture hLeftMem hLeftSource hLeftTock
      · exact resolved_target_mem_menuStep right rightFuture hRightMem hRightSource hRightTock
  · -- the left component has completed: enter the right survivor copy
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hLeftComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, hFilter⟩, rfl⟩ :=
      hLeftComplete
    simp only at hSource hTock hMem
    injection hSource with hLeftSource hRightSource
    simp only [parallelFutureSpec, if_neg hTock, Finset.mem_singleton] at hMem
    obtain ⟨-, hRightTock⟩ :=
      sync_components_not_tock leftAlphabet rightAlphabet interface hSync
        (by simpa using hTock)
    refine Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_right _ ?_))
    rw [hMem]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
      ⟨resolved_target_mem_menuStep right rightFuture hRightMem hRightSource hRightTock,
        hFilter.2.2.2⟩)
  · -- the right component has completed: enter the left survivor copy
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRightComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, hFilter⟩, rfl⟩ :=
      hRightComplete
    simp only at hSource hTock hMem
    injection hSource with hLeftSource hRightSource
    simp only [parallelFutureSpec, if_neg hTock, Finset.mem_singleton] at hMem
    obtain ⟨hLeftTock, -⟩ :=
      sync_components_not_tock leftAlphabet rightAlphabet interface hSync
        (by simpa using hTock)
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
    rw [hMem]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
      ⟨resolved_target_mem_menuStep left leftFuture hLeftMem hLeftSource hLeftTock,
        hFilter.2.2.2⟩)
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftSurvivor
    obtain ⟨rightEdge, -, rfl⟩ := hLeftSurvivor
    simp at hSource
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image] at hRightSurvivor
    obtain ⟨leftEdge, -, rfl⟩ := hRightSurvivor
    simp at hSource
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hLeftDone
    obtain ⟨rightEdge, -, rfl⟩ := hLeftDone
    simp at hSource
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image] at hRightDone
    obtain ⟨leftEdge, -, rfl⟩ := hRightDone
    simp at hSource
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    simp at hSource

/-- The same-cycle reach of a product state: product states built from the two
component reaches, the sub-reach of every survivor it can enter, and the done
state.  Each survivor entry carries its whole sub-reach, which is exactly what
the two survivor transports collapse. -/
theorem buildParallelAutomaton_pair_futureReachable_subset
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hLeftClosed : (⟨left.states, left.edges⟩ :
      PendingAutomaton).MenuClosed)
    (hRightClosed : (⟨right.states, right.edges⟩ :
      PendingAutomaton).MenuClosed)
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (hNoPair : ∀ s t, menuDependencyTargets dependencies (.pair s t) = ∅)
    (hNoFinal : menuDependencyTargets dependencies .final = ∅)
    (hParentClosed : ((⟨(buildParallelAutomaton parentAlphabet leftAlphabet
        rightAlphabet interface left right restampedLeft restampedRight
        leftFuture rightFuture restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).withMenuDependencies dependencies).ReferencesClosed)
    (p1 p2 : TypeAutomatonState)
    (hp1 : p1 ∈ left.states) (hp2 : p2 ∈ right.states) :
    ((⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ :
      PendingAutomaton).withMenuDependencies dependencies).futureReachable (.pair p1 p2) ⊆
      insert TypeAutomatonState.final
        ((((⟨left.states, left.edges⟩ :
              PendingAutomaton).futureReachable p1) ×ˢ
            ((⟨right.states, right.edges⟩ :
              PendingAutomaton).futureReachable p2)).image
            (fun pair => TypeAutomatonState.pair pair.1 pair.2) ∪
          ((((⟨right.states, right.edges⟩ :
              PendingAutomaton).futureReachable p2).filter
              (fun t => t ∉ right.accepting)).biUnion fun t =>
            ((⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
                interface left right restampedLeft restampedRight leftFuture
                rightFuture restampedLeftFuture restampedRightFuture).states,
              (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
                interface left right restampedLeft restampedRight leftFuture
                rightFuture restampedLeftFuture
                restampedRightFuture).edges⟩ :
              PendingAutomaton).withMenuDependencies dependencies).futureReachable (.survivor 1 t)) ∪
          ((((⟨left.states, left.edges⟩ :
              PendingAutomaton).futureReachable p1).filter
              (fun s => s ∉ left.accepting)).biUnion fun s =>
            ((⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
                interface left right restampedLeft restampedRight leftFuture
                rightFuture restampedLeftFuture restampedRightFuture).states,
              (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
                interface left right restampedLeft restampedRight leftFuture
                rightFuture restampedLeftFuture
                restampedRightFuture).edges⟩ :
              PendingAutomaton).withMenuDependencies dependencies).futureReachable (.survivor 0 s))) := by
  classical
  set leftPending : PendingAutomaton := ⟨left.states, left.edges⟩
    with hLeftPending
  set rightPending : PendingAutomaton := ⟨right.states, right.edges⟩
    with hRightPending
  set parent : FiniteMenuGraph :=
    (⟨(buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).states,
      (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
        interface left right restampedLeft restampedRight leftFuture rightFuture
        restampedLeftFuture restampedRightFuture).edges⟩ : PendingAutomaton).withMenuDependencies
          dependencies with hParent
  have hLeftReachStates : leftPending.futureReachable p1 ⊆ left.states :=
    PendingAutomaton.futureReachable_subset_of_menu_closed leftPending p1
      left.states hp1 (fun s hs => hLeftClosed s hs)
  have hRightReachStates : rightPending.futureReachable p2 ⊆ right.states :=
    PendingAutomaton.futureReachable_subset_of_menu_closed rightPending p2
      right.states hp2 (fun s hs => hRightClosed s hs)
  have hSurvivorRightState : ∀ t ∈ right.states,
      (TypeAutomatonState.survivor 1 t) ∈ parent.states := by
    intro t ht
    simp only [hParent, PendingAutomaton.withMenuDependencies, buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inr (Finset.mem_image_of_mem _ ht))
  have hSurvivorLeftState : ∀ s ∈ left.states,
      (TypeAutomatonState.survivor 0 s) ∈ parent.states := by
    intro s hs
    simp only [hParent, PendingAutomaton.withMenuDependencies, buildParallelAutomaton, finishAutomatonFragment,
      Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl (Or.inr (Finset.mem_image_of_mem _ hs)))
  refine FiniteMenuGraph.futureReachable_subset_of_reference_closed parent _ _
    ?_ ?_
  · refine Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_left _ ?_))
    exact Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_product.mpr
      ⟨PendingAutomaton.mem_futureReachable_self _ _,
        PendingAutomaton.mem_futureReachable_self _ _⟩, rfl⟩
  · intro state hState
    rcases Finset.mem_insert.mp hState with rfl | hRest
    · intro target hTarget
      simp only [hParent, PendingAutomaton.withMenuDependencies, hNoFinal,
        Finset.union_empty] at hTarget
      rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hTarget
      obtain ⟨edge, hEdge, hMem⟩ := hTarget
      have hFinal := buildParallelAutomaton_final_edge_target
        parentAlphabet leftAlphabet rightAlphabet interface left right
        restampedLeft restampedRight leftFuture rightFuture restampedLeftFuture
        restampedRightFuture edge (Finset.mem_filter.mp hEdge).1
        (Finset.mem_filter.mp hEdge).2
      by_cases hClock : edge.label.semantic = TypeLabel.tock
      · simp [hClock] at hMem
      · have hEq : target = .final := by simpa [hClock, hFinal] using hMem
        subst target
        exact Finset.mem_insert_self _ _
    rcases Finset.mem_union.mp hRest with hPairOrRight | hLeftSurvivor
    · rcases Finset.mem_union.mp hPairOrRight with hPair | hRightSurvivor
      · obtain ⟨components, hComponents, rfl⟩ := Finset.mem_image.mp hPair
        obtain ⟨hFirst, hSecond⟩ := Finset.mem_product.mp hComponents
        have hLeftStep : leftPending.menuStep components.1 ⊆
            leftPending.futureReachable p1 :=
          subset_trans
            (PendingAutomaton.menuStep_subset_futureReachable leftPending
              components.1 hLeftClosed (hLeftReachStates hFirst))
            (PendingAutomaton.futureReachable_subset_of_mem leftPending
              hLeftClosed hp1 hFirst)
        have hRightStep : rightPending.menuStep components.2 ⊆
            rightPending.futureReachable p2 :=
          subset_trans
            (PendingAutomaton.menuStep_subset_futureReachable
              rightPending components.2 hRightClosed
              (hRightReachStates hSecond))
            (PendingAutomaton.futureReachable_subset_of_mem rightPending
              hRightClosed hp2 hSecond)
        simp only [hParent, PendingAutomaton.withMenuDependencies, hNoPair,
          Finset.union_empty]
        refine subset_trans
          (buildParallelAutomaton_pair_menuStep_subset parentAlphabet
            leftAlphabet rightAlphabet interface left right restampedLeft
            restampedRight leftFuture rightFuture restampedLeftFuture
            restampedRightFuture components.1 components.2) ?_
        refine Finset.insert_subset_insert _ ?_
        intro named hNamed
        rcases Finset.mem_union.mp hNamed with hPairOrSurvRight | hSurvLeft
        · rcases Finset.mem_union.mp hPairOrSurvRight with hNamedPair | hSurvRight
          · obtain ⟨inner, hInner, rfl⟩ := Finset.mem_image.mp hNamedPair
            obtain ⟨hInnerLeft, hInnerRight⟩ := Finset.mem_product.mp hInner
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨inner, Finset.mem_product.mpr
                ⟨hLeftStep hInnerLeft, hRightStep hInnerRight⟩, rfl⟩))
          · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hSurvRight
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            obtain ⟨htRef, htAcc⟩ := Finset.mem_filter.mp ht
            exact Finset.mem_biUnion.mpr ⟨t,
              Finset.mem_filter.mpr ⟨hRightStep htRef, htAcc⟩,
              FiniteMenuGraph.mem_futureReachable_self _ _⟩
        · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hSurvLeft
          refine Finset.mem_union_right _ ?_
          obtain ⟨hsRef, hsAcc⟩ := Finset.mem_filter.mp hs
          exact Finset.mem_biUnion.mpr ⟨s,
            Finset.mem_filter.mpr ⟨hLeftStep hsRef, hsAcc⟩,
            FiniteMenuGraph.mem_futureReachable_self _ _⟩
      · obtain ⟨t, ht, hInReach⟩ := Finset.mem_biUnion.mp hRightSurvivor
        have htRef := (Finset.mem_filter.mp ht).1
        have hEntry : (TypeAutomatonState.survivor 1 t) ∈ parent.states :=
          hSurvivorRightState t (hRightReachStates htRef)
        have hStates : parent.futureReachable (.survivor 1 t) ⊆ parent.states :=
          FiniteMenuGraph.futureReachable_subset_of_reference_closed parent _
            parent.states hEntry (fun s hs => hParentClosed s hs)
        refine subset_trans
          (subset_trans
            (FiniteMenuGraph.referencedStates_subset_futureReachable parent
              state hParentClosed (hStates hInReach))
            (FiniteMenuGraph.futureReachable_subset_of_mem parent hParentClosed
              hEntry hInReach)) ?_
        intro u hu
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, ht, hu⟩)))
    · obtain ⟨s, hs, hInReach⟩ := Finset.mem_biUnion.mp hLeftSurvivor
      have hsRef := (Finset.mem_filter.mp hs).1
      have hEntry : (TypeAutomatonState.survivor 0 s) ∈ parent.states :=
        hSurvivorLeftState s (hLeftReachStates hsRef)
      have hStates : parent.futureReachable (.survivor 0 s) ⊆ parent.states :=
        FiniteMenuGraph.futureReachable_subset_of_reference_closed parent _
          parent.states hEntry (fun x hx => hParentClosed x hx)
      refine subset_trans
        (subset_trans
          (FiniteMenuGraph.referencedStates_subset_futureReachable parent
            state hParentClosed (hStates hInReach))
          (FiniteMenuGraph.futureReachable_subset_of_mem parent hParentClosed
            hEntry hInReach)) ?_
      intro u hu
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨s, hs, hu⟩))


/-- A state's own published offers are part of its same-cycle menu, once they
pass the type's alphabet gate: the state is the first term of its own reach. -/
theorem offersAt_subset_computeFutureOf (processType : PactType)
    (state : TypeAutomatonState) :
    ((⟨(compileTypeFuel (typeCompilationFuel processType) processType).states,
        (compileTypeFuel (typeCompilationFuel processType)
          processType).edges⟩ : PendingAutomaton).offersAt state).filter
        (fun action => action ∈ processType.alphabet.actions) ⊆
      computeFutureOf processType state := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel processType = k + 1 :=
    ⟨typeCompilationFuel processType - 1, by
      have := typeCompilationFuel_positive processType; omega⟩
  intro action hAction
  obtain ⟨hOffers, hGate⟩ := Finset.mem_filter.mp hAction
  rw [computeFutureOf, hk, computeFutureOfFuel]
  refine Finset.mem_filter.mpr ⟨?_, hGate⟩
  refine Finset.mem_biUnion.mpr ⟨state,
    FiniteMenuGraph.mem_futureReachable_self _ _, ?_⟩
  refine Finset.mem_union_left _ ?_
  rw [← hk]
  exact hOffers


end Pact
