import Anvilpp.PactTypes.NewCorrespondence.Helpers.Sequence
import Anvilpp.PactTypes.NewCorrespondence.Helpers.MainHelpers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.OfferAlphabetLemmas

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
          else typeFutureOffers
              (.par parentAlphabet leftTarget rightTarget interface) \
            hideTypeOffers interface (leftCurrent ∪ rightCurrent)) →
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
  | left_complete (rightEnv : TypeEnvironment) (rightTarget : PactType)
      (rightCurrent rightFuture : Finset BareMessage) :
      target = rightTarget.reannotate parentAlphabet →
      left = .skip left.alphabet →
      rightTarget ≠ .skip rightTarget.alphabet →
      DecoratedTypeTransition rightEnv right label
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      restrictTypeOffers interface rightCurrent = ∅ →
      restrictTypeOffers interface rightFuture = ∅ →
      LocalTypeOfferEnvironment env interface right rightEnv ∅ ∅ rightEnv →
      env.WellFormed parentAlphabet →
      label ≠ TypeLabel.tock →
      current = hideTypeOffers interface rightCurrent →
      future = typeFutureOffers (rightTarget.reannotate parentAlphabet) \
        hideTypeOffers interface rightCurrent →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | left_complete_tock (rightEnv : TypeEnvironment) (rightTarget : PactType)
      (rightCurrent rightFuture : Finset BareMessage) :
      target = rightTarget.reannotate parentAlphabet →
      left = .skip left.alphabet →
      rightTarget ≠ .skip rightTarget.alphabet →
      DecoratedTypeTransition rightEnv right label
        (TypeOfferSummary.mk rightCurrent rightFuture) rightTarget →
      restrictTypeOffers interface rightCurrent = ∅ →
      restrictTypeOffers interface rightFuture = ∅ →
      LocalTypeOfferEnvironment env interface right rightEnv ∅ ∅ rightEnv →
      env.WellFormed parentAlphabet →
      label = TypeLabel.tock →
      current = ∅ →
      future = ∅ →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  -- Mirror of `left_complete`: the right side is already `skip`.
  | right_complete (leftEnv : TypeEnvironment) (leftTarget : PactType)
      (leftCurrent leftFuture : Finset BareMessage) :
      target = leftTarget.reannotate parentAlphabet →
      right = .skip right.alphabet →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition leftEnv left label
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      restrictTypeOffers interface leftCurrent = ∅ →
      restrictTypeOffers interface leftFuture = ∅ →
      LocalTypeOfferEnvironment env interface left leftEnv ∅ ∅ leftEnv →
      env.WellFormed parentAlphabet →
      label ≠ TypeLabel.tock →
      current = hideTypeOffers interface leftCurrent →
      future = typeFutureOffers (leftTarget.reannotate parentAlphabet) \
        hideTypeOffers interface leftCurrent →
      ParDecoratedStepCase parentAlphabet left right interface target env label
        current future
  | right_complete_tock (leftEnv : TypeEnvironment) (leftTarget : PactType)
      (leftCurrent leftFuture : Finset BareMessage) :
      target = leftTarget.reannotate parentAlphabet →
      right = .skip right.alphabet →
      leftTarget ≠ .skip leftTarget.alphabet →
      DecoratedTypeTransition leftEnv left label
        (TypeOfferSummary.mk leftCurrent leftFuture) leftTarget →
      restrictTypeOffers interface leftCurrent = ∅ →
      restrictTypeOffers interface leftFuture = ∅ →
      LocalTypeOfferEnvironment env interface left leftEnv ∅ ∅ leftEnv →
      env.WellFormed parentAlphabet →
      label = TypeLabel.tock →
      current = ∅ →
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
  | left_complete outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hRightOffers hNotSkip
      hRC hRF hLocal hWF hNotTock ihRight
  | left_complete_tock outer rightEnv interface alphabet left right right' rightLabel
      rightCurrent rightFuture hLeftSkip hRightNotSkip hRightOffers hNotSkip
      hRC hRF hLocal hWF hNotTock ihRight =>
      exact TypeTransition.left_complete outer rightEnv interface alphabet left right
        right' rightLabel rightCurrent rightFuture hLeftSkip hRightNotSkip
        ihRight hRightOffers
        hNotSkip hRC hRF hLocal hWF
  | right_complete outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hLeftOffers hNotSkip
      hLC hLF hLocal hWF hNotTock ihLeft
  | right_complete_tock outer leftEnv interface alphabet left left' right leftLabel
      leftCurrent leftFuture hRightSkip hLeftNotSkip hLeftOffers hNotSkip
      hLC hLF hLocal hWF hNotTock ihLeft =>
      exact TypeTransition.right_complete outer leftEnv interface alphabet left left'
        right leftLabel leftCurrent leftFuture hRightSkip hLeftNotSkip ihLeft
        hLeftOffers
        hNotSkip hLC hLF hLocal hWF



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
  | left_complete outer rightEnv interface alphabet left right rightTarget rightLabel
      rightCurrent rightFuture hLeftSkip _ hRightOffers hNotSkip hRC hRF hLocal
      hWF hNotTock =>
      exact ParDecoratedStepCase.left_complete rightEnv rightTarget rightCurrent
        rightFuture rfl hLeftSkip hNotSkip
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hRC hRF hLocal hWF hNotTock rfl rfl
  | left_complete_tock outer rightEnv interface alphabet left right rightTarget
      rightLabel rightCurrent rightFuture hLeftSkip _ hRightOffers hNotSkip
      hRC hRF hLocal hWF hTock =>
      exact ParDecoratedStepCase.left_complete_tock rightEnv rightTarget
        rightCurrent rightFuture rfl hLeftSkip hNotSkip
        ⟨hRightOffers.toTypeTransition, hRightOffers⟩
        hRC hRF hLocal hWF hTock rfl rfl
  | right_complete outer leftEnv interface alphabet left leftTarget right leftLabel
      leftCurrent leftFuture hRightSkip _ hLeftOffers hNotSkip hLC hLF hLocal
      hWF hNotTock =>
      exact ParDecoratedStepCase.right_complete leftEnv leftTarget leftCurrent
        leftFuture rfl hRightSkip hNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        hLC hLF hLocal hWF hNotTock rfl rfl
  | right_complete_tock outer leftEnv interface alphabet left leftTarget right leftLabel
      leftCurrent leftFuture hRightSkip _ hLeftOffers hNotSkip hLC hLF hLocal
      hWF hTock =>
      exact ParDecoratedStepCase.right_complete_tock leftEnv leftTarget
        leftCurrent leftFuture rfl hRightSkip hNotSkip
        ⟨hLeftOffers.toTypeTransition, hLeftOffers⟩
        hLC hLF hLocal hWF hTock rfl rfl


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
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (env : TypeEnvironment) (label : TypeLabel) (offers : TypeOfferSummary)
    (target : TypeAutomatonState)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (PactType.par alphabet left right interface).transitionAlphabet) :
    (compileType (.par alphabet left right interface)).HasEdge
        TypeAutomatonState.final env label offers target ↔
      env.WellFormed alphabet ∧ env.clock = false ∧ label = TypeLabel.silent ∧
      offers = TypeOfferSummary.mk ∅ ∅ ∧ target = TypeAutomatonState.final := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

/-- Every public edge leaving a parallel product state extends the joint
reachability path to its target. -/
theorem compiledParallel_pair_edge_target_reachable
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {q1 q2 target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label offers target) :
    ParallelReachable alphabet left.alphabet right.alphabet interface
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (computeFutureOf left)
      (computeFutureOf right)
      (computeFutureOfFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (computeFutureOfFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet)) target := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

private theorem interface_action_mem_localActions
    (parentType : PactType)
     {interface : Interface}
    (hInterface : interface ⊆ PactType.ParallelInterfaces parentType)
    {action : BareMessage} (hAction : action.1 ∈ interface) :
    action ∈ parentType.localActionsWithInterface := by
  rcases action with ⟨msg, dir⟩
  simp only [PactType.localActionsWithInterface, Finset.mem_union]
  right
  simp only [PactType.interfaceActions, Finset.mem_biUnion,
    Finset.mem_insert, Finset.mem_singleton]
  exact ⟨msg, hInterface hAction, by cases dir <;> simp⟩

private theorem interface_action_mem_localEnvironmentActions
    (parentType : PactType)
     {interface : Interface}
    (hInterface : interface ⊆ PactType.ParallelInterfaces parentType)
    {action : BareMessage} (hAction : action.1 ∈ interface) :
    action ∈ parentType.alphabet.localEnvironmentActions := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

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
          by_cases hDeclared : (msg, dir) ∈ alphabet.actions <;>
            simp [typeFutureOffersFuel, PactType.MessageActions, hDeclared]
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
          split
          · apply hFold branches (typeFutureOffersFuel fuel elseType)
            · exact (ih elseType).trans Finset.subset_union_left
            · simp
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
        exact hBranches.2.1
      · exact ih hBranches.2.2 hMem

/-- For alphabet-well-formed syntax, its future menu is contained in the
fixed alphabet carried by that syntax node. -/
private theorem typeFutureOffersFuel_subset_fixedAlphabet :
    ∀ fuel processType, processType.AlphabetWellFormed →
      typeFutureOffersFuel fuel processType ⊆ processType.alphabet.actions := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

private theorem typeFutureOffers_subset_fixedAlphabet
    (processType : PactType) (hWF : processType.AlphabetWellFormed) :
    typeFutureOffers processType ⊆ processType.alphabet.actions := by
  exact typeFutureOffersFuel_subset_fixedAlphabet _ processType hWF

private theorem typeBranchActions_subset_fixedAlphabet
    {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
    (hActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    typeBranchActions branches ⊆ alphabet.actions := by
  intro offered hOffered
  simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hOffered
  obtain ⟨branch, hBranch, rfl⟩ := hOffered
  exact hActions branch hBranch

private theorem typeWaitingOffers_subset_fixedAlphabet
    {alphabet : PactTypeAlphabet} {env : TypeEnvironment}
    {branches : List (BareMessage × PactType)}
    (hActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    typeWaitingOffers env branches ⊆ alphabet.actions := by
  intro action hAction
  simp only [typeWaitingOffers, Finset.mem_inter] at hAction
  exact typeBranchActions_subset_fixedAlphabet hActions hAction.2

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
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

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
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

theorem typeOffers_current_subset_fixedAlphabet
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hSource : source.AlphabetWellFormed)
    (hOffers : TypeOffers env source label target current future) :
    current ⊆ source.alphabet.actions :=
  typeOffers_current_subset_alphabet hSource hOffers

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
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

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

private theorem typeNeed_typeNeed (action : BareMessage) :
    typeNeed (typeNeed action) = action := by
  rcases action with ⟨msg, dir⟩
  cases dir <;> simp [typeNeed, MessageDir.invert]

private theorem typeNeed_mem_left_of_right_interface
    {left right : PactTypeAlphabet} {interface : Interface}
    (hLeftWF : left.WellFormed) (hRightWF : right.WellFormed)
    (hComplementary : PactTypeAlphabet.ComplementaryOn left right interface)
    {action : BareMessage}
    (hAction : action ∈ right.actions) (hInterface : action.1 ∈ interface) :
    typeNeed action ∈ left.actions := by
  rcases action with ⟨msg, dir⟩
  have hComp := hComplementary msg hInterface
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
    {left right : PactTypeAlphabet} {interface : Interface}
    (hLeftWF : left.WellFormed) (hRightWF : right.WellFormed)
    (hComplementary : PactTypeAlphabet.ComplementaryOn left right interface)
    {action : BareMessage}
    (hAction : action ∈ left.actions) (hInterface : action.1 ∈ interface) :
    typeNeed action ∈ right.actions := by
  rcases action with ⟨msg, dir⟩
  have hComp := hComplementary msg hInterface
  cases dir
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact hSendRecv.2
    · exact False.elim (hLeftWF msg ⟨hAction, hRecvSend.1⟩)
  · simp only [typeNeed, MessageDir.invert]
    rcases hComp with hSendRecv | hRecvSend
    · exact False.elim (hLeftWF msg ⟨hSendRecv.1, hAction⟩)
    · exact hRecvSend.2

/-- A type declaring an action's complement admits that action in its
environments. -/
private theorem mem_localEnvironmentActionsFor_of_need

    {localAlphabet : PactTypeAlphabet} {action : BareMessage}
    (hNeed : typeNeed action ∈ localAlphabet.actions) :
    action ∈ localAlphabet.localEnvironmentActions := by
  simp only [PactTypeAlphabet.localEnvironmentActions,
    PactTypeAlphabet.actions, Finset.mem_image]
  exact ⟨typeNeed action, hNeed, typeNeed_typeNeed action⟩

-- private theorem localEnvironmentFor_mem_of_localTypeOfferEnvironment
--      {parentAlphabet siblingAlphabet : PactTypeAlphabet}
--     {outer localEnv siblingEnv : TypeEnvironment}
--     {interface : Interface} {localType : PactType}
--     {current future : Finset BareMessage}
--     (hOuter : outer ∈ parentAlphabet.localEnvironments)
--     (hCurrent : current ⊆ siblingAlphabet.actions)
--     (hFuture : future ⊆ siblingAlphabet.actions)
--     (hNeed : ∀ action,
--       action ∈ siblingAlphabet.actions → action.1 ∈ interface →
--         typeNeed action ∈ localType.alphabet.actions)
--     (hLocal :
--       LocalTypeOfferEnvironment outer interface localType siblingEnv current
--         future localEnv) :
--     localEnv ∈ localType.alphabet.localEnvironments := by
--   cases hLocal with
--   | clock outer interface localType current hClock =>
--       simp [PactTypeAlphabet.localEnvironments, TypeEnvironment.tock]
--   | ordinary outer siblingEnv localEnv interface localType current
--       hOuterClock hSiblingClock hLocalClock hImmediate hFutureEq =>
--       simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
--         Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
--         Finset.mem_image] at hOuter ⊢
--       rcases hOuter with hTock | ⟨outerImmediate, hOuterImmediate,
--         outerFuture, hOuterFuture, hOuterEq⟩
--       · subst outer
--         simp [TypeEnvironment.tock] at hOuterClock
--       · subst outer
--         rcases localEnv with ⟨localImmediate, localFuture, localClock⟩
--         simp only at hLocalClock hImmediate hFutureEq
--         subst localClock
--         right
--         refine ⟨localImmediate, ?_, localFuture, ?_, rfl⟩
--         · intro action hAction
--           rw [hImmediate] at hAction
--           simp only [Finset.mem_union, restrictTypeOffers,
--             projectTypeEnvironmentOffers, Finset.mem_filter] at hAction
--           rcases hAction with ⟨hOuterAction, hProjected⟩ |
--               ⟨hCurrentAction, hInterfaceAction⟩
--           · simpa [PactTypeAlphabet.localEnvironmentActions,
--               PactTypeAlphabet.actions] using hProjected
--           · exact mem_localEnvironmentActionsFor_of_need
--               (hNeed action (hCurrent hCurrentAction) hInterfaceAction)
--         · intro action hAction
--           rw [hFutureEq] at hAction
--           simp only [Finset.mem_sdiff, Finset.mem_union, restrictTypeOffers,
--             projectTypeEnvironmentOffers, Finset.mem_filter] at hAction ⊢
--           rcases hAction.1 with ⟨hOuterAction, hProjected⟩ |
--               ⟨hFutureAction, hInterfaceAction⟩
--           · exact ⟨by
--               simpa [PactTypeAlphabet.localEnvironmentActions,
--                 PactTypeAlphabet.actions] using hProjected,
--               hAction.2⟩
--           · exact ⟨mem_localEnvironmentActionsFor_of_need
--               (hNeed action (hFuture hFutureAction) hInterfaceAction),
--               hAction.2⟩

private theorem localEnvironment_mem_of_localTypeOfferEnvironment
    (parentType : PactType)
     {outer localEnv siblingEnv : TypeEnvironment}
    {interface : Interface} {localType : PactType}
    {current future : Finset BareMessage}
    (hInterface : interface ⊆ PactType.ParallelInterfaces parentType)
    (hOuter : outer ∈ parentType.alphabet.localEnvironments)
    (hLocal :
      LocalTypeOfferEnvironment outer interface localType siblingEnv current
        future localEnv) :
    localEnv ∈ parentType.alphabet.localEnvironments := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

private theorem componentLabels_mem_localLabels
    (parentType : PactType)
     {interface : Interface}
    (hInterface : interface ⊆ PactType.ParallelInterfaces parentType)
    {leftLabel rightLabel label : TypeLabel}
    (hSync : TypeLabel.Sync interface leftLabel rightLabel)
    (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
    (hParent : label ∈ parentType.labels) :
    leftLabel ∈ parentType.labels ∧
      rightLabel ∈ parentType.labels := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

-- /-- `LocalTypeOfferEnvironment` only depends on `localType` through its
-- alphabet, so it transports along any alphabet-preserving substitution of the
-- local type (e.g. a residual `residualLeft` reached from `left` by steps). -/
-- theorem LocalTypeOfferEnvironment.congrLocalType
--     {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
--     {localType localType' : PactType} {current future : Finset BareMessage}
--     (hAlphabet : localType'.alphabet = localType.alphabet)
--     (hLocal : LocalTypeOfferEnvironment outer interface localType siblingEnv
--       current future localEnv) :
--     LocalTypeOfferEnvironment outer interface localType' siblingEnv
--       current future localEnv := by
--   cases hLocal with
--   | clock _ =>
--       rename_i hClock
--       exact LocalTypeOfferEnvironment.clock outer interface localType' current
--         future hClock
--   | ordinary _ _ _ _ _ =>
--       rename_i hOuterClock hSiblingClock hLocalClock hImmediate hFuture
--       exact LocalTypeOfferEnvironment.ordinary outer siblingEnv localEnv
--         interface localType' current future hOuterClock hSiblingClock
--         hLocalClock (hAlphabet ▸ hImmediate) (hAlphabet ▸ hFuture)

-- /-- Each component symbol of a parallel step belongs to that component's own
-- fixed-alphabet transition alphabet.  The enclosing product may hide interface
-- actions, but those actions remain declared local actions while either child
-- is compiled, and the offer/environment contents stay within each child's own
-- declared alphabet. -/
-- theorem transitionAlphabet_of_par_component
--      (alphabet : PactTypeAlphabet)
--     (left right : PactType) (interface : Interface)
--     {leftEnv rightEnv : TypeEnvironment} {leftLabel rightLabel : TypeLabel}
--     {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
--     {env : TypeEnvironment} {label : TypeLabel}
--     (hWF : env.WellFormed alphabet)
--     (hInterface : interface ⊆ PactType.ParallelInterfaces parentType)
--     (hLeftWellFormed : left.AlphabetWellFormed)
--     (hRightWellFormed : right.AlphabetWellFormed)
--     (hParallelCompatible :
--       PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
--         right.alphabet left right interface)
--     (hLeftCurrent : leftCurrent ⊆ left.alphabet.actions)
--     (hLeftFuture : leftFuture ⊆ left.alphabet.actions)
--     (hRightCurrent : rightCurrent ⊆ right.alphabet.actions)
--     (hRightFuture : rightFuture ⊆ right.alphabet.actions)
--     (hLocal1 :
--       LocalTypeOfferEnvironment env interface left rightEnv rightCurrent
--         rightFuture leftEnv)
--     (hLocal2 :
--       LocalTypeOfferEnvironment env interface right leftEnv leftCurrent
--         leftFuture rightEnv)
--     (hSync : TypeLabel.Sync interface leftLabel rightLabel)
--     (hLabelEq : label = TypeLabel.combine interface leftLabel rightLabel)
--     (hSymbol :
--       TypeAutomatonSymbol.mk env label
--         (TypeOfferSummary.mk (hideTypeOffers interface (leftCurrent ∪ rightCurrent))
--           (hideTypeOffers interface (leftFuture ∪ rightFuture))) ∈
--         (PactType.par alphabet left right interface).transitionAlphabet) :
--     TypeAutomatonSymbol.mk leftEnv leftLabel
--         (TypeOfferSummary.mk leftCurrent leftFuture) ∈
--       left.transitionAlphabet ∧
--     TypeAutomatonSymbol.mk rightEnv rightLabel
--         (TypeOfferSummary.mk rightCurrent rightFuture) ∈
--       right.transitionAlphabet := by
--   -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
--   sorry

-- /-- Lift a pair of child relation states into the product relation. -/
lemma relationMembership_par_pair
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {leftResidual rightResidual : PactType}
    {leftState rightState : TypeAutomatonState}
    (hLeft : relationMembership
      (buildRelationSet left (compileType left))
      leftResidual leftState)
    (hRight : relationMembership
      (buildRelationSet right (compileType right))
      rightResidual rightState)
    (hReachable : ParallelReachable alphabet left.alphabet
      right.alphabet interface
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (computeFutureOf left)
      (computeFutureOf right)
      (computeFutureOfFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (computeFutureOfFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (.pair leftState rightState)) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (.par alphabet leftResidual rightResidual interface)
      (.pair leftState rightState) := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

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
          rw [hFuelEq]
          rw [compileTypeFuel.eq_def]
          show (buildSequenceAutomaton
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
            (compileTypeFuel
              (max (typeCompilationFuel left) (typeCompilationFuel right)) right)).accepting = _
          rw [compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
          simp [buildSequenceAutomaton, finishAutomatonFragment]
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
     (ty : PactType) :
    (compileTypeFuel (typeCompilationFuel ty) ty).accepting
      = (compileType ty).accepting := by
  simp [compileType]

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


/-- `<survivor-entry>` as the paper states it, from the component's own
relation.  Re-signing rewrites the gates, so carrying a residual from
`right`'s relation to `right.reannotate alphabet`'s is a separate obligation:
it is the paper's first conclusion, taken here as `hTransport`.  Everything
after it is discharged. -/
theorem survivorRight_relationMembership_of_transport
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : right.OfferBranchesDisjoint)
    (hTransport : ∀ {childResidual : PactType} {childState : TypeAutomatonState},
      relationMembership (buildRelationSet right (compileType right))
        childResidual childState →
      relationMembership
        (buildRelationSet (right.reannotate alphabet)
          (compileType (right.reannotate alphabet)))
        (childResidual.reannotate alphabet) childState)
    (hChild : relationMembership
      (buildRelationSet right (compileType right)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel right) right).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (residual.reannotate alphabet) (.survivor 1 q) :=
  survivorRight_relationMembership alphabet left right interface hDisjoint
    (hTransport hChild) hNotAcc

/-- The mirror of `survivorRight_relationMembership_of_transport`. -/
theorem survivorLeft_relationMembership_of_transport
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : left.OfferBranchesDisjoint)
    (hTransport : ∀ {childResidual : PactType} {childState : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType left))
        childResidual childState →
      relationMembership
        (buildRelationSet (left.reannotate alphabet)
          (compileType (left.reannotate alphabet)))
        (childResidual.reannotate alphabet) childState)
    (hChild : relationMembership
      (buildRelationSet left (compileType left)) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel left) left).accepting) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (residual.reannotate alphabet) (.survivor 0 q) :=
  survivorLeft_relationMembership alphabet left right interface hDisjoint
    (hTransport hChild) hNotAcc

/-- A reachable pair of related child states represents the parallel pair. -/
theorem pair_relationMembership
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residualLeft residualRight : PactType} {q1 q2 : TypeAutomatonState}
    (hLeft : relationMembership
      (buildRelationSet left (compileType left)) residualLeft q1)
    (hRight : relationMembership
      (buildRelationSet right (compileType right)) residualRight q2)
    (hReach : ParallelReachable alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (computeFutureOf left) (computeFutureOf right)
      (computeFutureOfFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (computeFutureOfFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (.pair q1 q2)) :
    relationMembership
      (buildRelationSet (.par alphabet left right interface)
        (compileType (.par alphabet left right interface)))
      (.par alphabet residualLeft residualRight interface) (.pair q1 q2) := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry


/-- H15's future agreement at a surviving right-component state. -/
theorem computeFutureOf_survivorRight_related
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : right.OfferBranchesDisjoint)
    (hChild : relationMembership
      (buildRelationSet (right.reannotate alphabet)
        (compileType (right.reannotate alphabet))) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel right) right).accepting) :
    computeFutureOf (.par alphabet left right interface)
        (.survivor 1 q) = typeFutureOffers residual :=
  helper_h15_future_offers_agree
    (survivorRight_relationMembership alphabet left right interface
      hDisjoint hChild hNotAcc)

/-- H15's future agreement at a surviving left-component state. -/
theorem computeFutureOf_survivorLeft_related
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    {residual : PactType} {q : TypeAutomatonState}
    (hDisjoint : left.OfferBranchesDisjoint)
    (hChild : relationMembership
      (buildRelationSet (left.reannotate alphabet)
        (compileType (left.reannotate alphabet))) residual q)
    (hNotAcc : q ∉ (compileTypeFuel
      (typeCompilationFuel left) left).accepting) :
    computeFutureOf (.par alphabet left right interface)
        (.survivor 0 q) = typeFutureOffers residual :=
  helper_h15_future_offers_agree
    (survivorLeft_relationMembership alphabet left right interface
      hDisjoint hChild hNotAcc)


/-- A lone edge of the surviving right component is a product edge. -/
theorem survivorRight_mem_edges
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 q' : TypeAutomatonState) (env childEnv : TypeEnvironment)
    (label : TypeLabel) (childOffers : TypeOfferSummary)
    (hReach : ParallelReachable alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (computeFutureOf left) (computeFutureOf right)
      (computeFutureOfFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (computeFutureOfFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (.pair q1 q2))
    (hOffCur : restrictTypeOffers interface childOffers.current = ∅)
    (hOffFut : restrictTypeOffers interface childOffers.future = ∅)
    -- The survivor is the child re-stamped with the merged alphabet, so the
    -- product edge carries `env` while the child's own edge carries its
    -- projection.
    (hEnvMem : env ∈ alphabet.localEnvironments)
    (hProject : projectAutomatonEnvironment right.alphabet env = childEnv)
    (hEdge : (compileType right).HasEdge q2 childEnv label childOffers q')
    (hQ1Acc : q1 ∈ (compileType left).accepting)
    (hQ1St : q1 ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hQ'NotAcc : q' ∉ (compileType right).accepting)
    (hQ'NotAccFuel : q' ∉ (compileTypeFuel
      (typeCompilationFuel right) right).accepting)
    {q2Residual : PactType}
    (hQ2Rel : relationMembership
      (buildRelationSet right (compileType right)) q2Residual q2) :
    (compileType (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 1 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf (.par alphabet left right interface)
                state \ removed))
      (.survivor 1 q') := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

/-- A lone edge of the surviving left component is a product edge. -/
theorem survivorLeft_mem_edges
     (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 q' : TypeAutomatonState) (env childEnv : TypeEnvironment)
    (label : TypeLabel) (childOffers : TypeOfferSummary)
    (hReach : ParallelReachable alphabet left.alphabet right.alphabet
      interface
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (compileTypeFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (compileTypeFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (computeFutureOf left) (computeFutureOf right)
      (computeFutureOfFuel
        (typeCompilationFuel (left.reannotate alphabet))
        (left.reannotate alphabet))
      (computeFutureOfFuel
        (typeCompilationFuel (right.reannotate alphabet))
        (right.reannotate alphabet))
      (.pair q1 q2))
    (hOffCur : restrictTypeOffers interface childOffers.current = ∅)
    (hOffFut : restrictTypeOffers interface childOffers.future = ∅)
    (hEnvMem : env ∈ alphabet.localEnvironments)
    (hProject : projectAutomatonEnvironment left.alphabet env = childEnv)
    (hEdge : (compileType left).HasEdge q1 childEnv label childOffers q')
    (hQ2Acc : q2 ∈ (compileType right).accepting)
    (hQ2St : q2 ∈ (compileTypeFuel (typeCompilationFuel right) right).states)
    (hQ'NotAcc : q' ∉ (compileType left).accepting)
    (hQ'NotAccFuel : q' ∉ (compileTypeFuel
      (typeCompilationFuel left) left).accepting)
    {q1Residual : PactType}
    (hQ1Rel : relationMembership
      (buildRelationSet left (compileType left)) q1Residual q1) :
    (compileType (.par alphabet left right interface)).HasEdge
      (.pair q1 q2) env label
      (TypeOfferSummary.mk childOffers.current
        (match parallelFutureSpec (.visible label) (.survivor 0 q')
            childOffers.current with
          | .explicit offers => offers
          | .at state removed =>
              computeFutureOf (.par alphabet left right interface)
                state \ removed))
      (.survivor 0 q') := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

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
     :
    ∀ fuel source residual state,
      (residual, state) ∈ buildRelationSetCoreFuel fuel source →
      footprintSubset residual source := by
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

/-- A residual related to a compiled state cannot introduce a message action
absent from the source type. -/
theorem relationMembership_messageActions_subset
     (source : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet source (compileType source)) residual state) :
    residual.MessageActions ⊆ source.MessageActions := by
  exact (buildRelationSetCoreFuel_footprintSubset
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
  | par outer leftEnv rightEnv interface alphabet left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeft hLeftOffers hRight hRightOffers hNonFinal hSide hLeftIH
      hRightIH =>
      simpa [PactType.MessageActions] using
        Finset.union_subset_union hLeftIH hRightIH
  | left_complete outer rightEnv interface alphabet leftT rightT survivor rightLabel
      rightCurrent rightFuture hLeftSkip _ hRightTrans hRightOffers hNotSkip
      hRC hRF hLocal hWF ihRight =>
      intro action hAction
      rw [PactType.messageActions_reannotate] at hAction
      simp only [PactType.MessageActions]
      exact Finset.mem_union.mpr (Or.inr (ihRight hAction))
  | right_complete outer leftEnv interface alphabet leftT survivor rightT leftLabel
      leftCurrent leftFuture hRightSkip _ hLeftTrans hLeftOffers hNotSkip
      hLC hLF hLocal hWF ihLeft =>
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
  -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
  sorry

/-- The current offer of a compiled edge is owned by its source type: the
step correspondence turns the edge into a semantic step, whose current offer
`typeOffers_current_subset_messageActions` bounds by the source residual. -/
private theorem compiledEdge_current_subset_messageActions
     {processType residual residual' : PactType}
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hStepIff : StepIffStatement processType)
    (hSource : relationMembership
      (buildRelationSet processType (compileType processType))
      residual source)
    (hTarget : relationMembership
      (buildRelationSet processType (compileType processType))
      residual' target)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      processType.transitionAlphabet)
    (hEdge : (compileType processType).HasEdge source env label
      offers target) :
    offers.current ⊆ processType.MessageActions :=
  (typeOffers_current_subset_messageActions
      ((hStepIff hSource (by simpa [compileType] using hSymbol)).mpr
        ⟨target, hEdge, hTarget⟩).2).trans
    (relationMembership_messageActions_subset processType hSource)

set_option maxHeartbeats 4000000 in
-- /-- Two families of edge leave a product state.

-- Forward direction: a product edge is either a pair of component edges meeting
-- the `SyncEdges` condition, or a lone edge of one component whose sibling
-- already rests at an accepting state and whose interface offers are empty.

-- Backward direction: either family is by construction a parallel edge.

-- Both call sites in `correspondence_par_stepIff` already have a relation
-- witness for `q1`/`q2` in hand (from `relationMembership_par_cases`) before
-- they ever invoke this lemma, so `childLeft`/`childRight` are threaded in as
-- fixed hypotheses here rather than re-derived from bare automaton data. -/
-- theorem buildParallelAutomaton_pair_hasEdge_iff
--      (alphabet : PactTypeAlphabet)
--     (left right : PactType) (interface : Interface)
--     (q1 q2 target : TypeAutomatonState) (env : TypeEnvironment)
--     (label : TypeLabel) (offers : TypeOfferSummary)
--     {childLeft childRight : PactType}
--     (hParallelCompatible :
--       PactTypeAlphabet.ParallelCompatible alphabet left.alphabet right.alphabet
--         left right interface)
--     -- Declared alphabets may overlap; what the two bodies perform may not.
--     (hMessageDisjoint :
--       Disjoint (PactType.MessageActions left) (PactType.MessageActions right))
--     (hLeftStepIff : StepIffStatement left)
--     (hRightStepIff : StepIffStatement right)
--     (hSymbol :
--       TypeAutomatonSymbol.mk env label offers ∈
--         (PactType.par alphabet left right interface).transitionAlphabet)
--     (hChildLeftRelated :
--       relationMembership (buildRelationSet left (compileType left))
--         childLeft q1)
--     (hChildRightRelated :
--       relationMembership (buildRelationSet right (compileType right))
--         childRight q2) :
--     (compileType (.par alphabet left right interface)).HasEdge
--         (.pair q1 q2) env label offers target ↔
--       (∃ (leftEnv rightEnv : TypeEnvironment) (leftLabel rightLabel : TypeLabel)
--         (leftOffers rightOffers : TypeOfferSummary) (q1' q2' : TypeAutomatonState),
--         (compileType left).HasEdge q1 leftEnv leftLabel leftOffers q1' ∧
--         (compileType right).HasEdge q2 rightEnv rightLabel rightOffers q2' ∧
--         -- `SyncEdges_I` gates each component edge on its own fixed alphabet.
--         TypeAutomatonSymbol.mk leftEnv leftLabel leftOffers ∈
--           left.transitionAlphabet ∧
--         TypeAutomatonSymbol.mk rightEnv rightLabel rightOffers ∈
--           right.transitionAlphabet ∧
--         ParallelReachable alphabet left.alphabet right.alphabet
--           interface
--           (compileTypeFuel (typeCompilationFuel left) left)
--           (compileTypeFuel (typeCompilationFuel right) right)
--           (compileTypeFuel
--             (typeCompilationFuel (left.reannotate alphabet))
--             (left.reannotate alphabet))
--           (compileTypeFuel
--             (typeCompilationFuel (right.reannotate alphabet))
--             (right.reannotate alphabet))
--           (computeFutureOf left)
--           (computeFutureOf right)
--           (computeFutureOfFuel
--             (typeCompilationFuel (left.reannotate alphabet))
--             (left.reannotate alphabet))
--           (computeFutureOfFuel
--             (typeCompilationFuel (right.reannotate alphabet))
--             (right.reannotate alphabet))
--           (.pair q1 q2) ∧
--         -- A non-redirecting edge realizes the ordinary rule, which fires only
--         -- from a live pair.  A redirecting one realizes the fusing rule, whose
--         -- sources are unconstrained.
--         (¬ (q1' ∈ (compileType left).accepting ∧
--               q2' ∈ (compileType right).accepting) →
--           q1 ∉ (compileType left).accepting ∧
--           q2 ∉ (compileType right).accepting) ∧
--         env.WellFormed alphabet ∧
--         LocalTypeOfferEnvironment env interface left rightEnv
--           rightOffers.current rightOffers.future leftEnv ∧
--         LocalTypeOfferEnvironment env interface right leftEnv
--           leftOffers.current leftOffers.future rightEnv ∧
--         TypeLabel.Sync interface leftLabel rightLabel ∧
--         label = TypeLabel.combine interface leftLabel rightLabel ∧
--         offers.current =
--           hideTypeOffers interface (leftOffers.current ∪ rightOffers.current) ∧
--         offers.future =
--           hideTypeOffers interface (leftOffers.future ∪ rightOffers.future) ∧
--         -- Mirrors the compiler's own redirect: a raw target whose both sides
--         -- are accepting (H13: exactly when both children finish) is placed
--         -- in `q_done`, never left as its own separate `.pair` state.
--         (if q1' ∈ (compileType left).accepting ∧
--             q2' ∈ (compileType right).accepting then
--           target = TypeAutomatonState.final
--         else target = .pair q1' q2')) ∨
--       -- The sibling already rests at an accepting state, so the survivor
--       -- steps alone and the product node disappears.
--       (∃ q' : TypeAutomatonState,
--         ParallelReachable alphabet left.alphabet right.alphabet
--           interface
--           (compileTypeFuel (typeCompilationFuel left) left)
--           (compileTypeFuel (typeCompilationFuel right) right)
--           (compileTypeFuel
--             (typeCompilationFuel (left.reannotate alphabet))
--             (left.reannotate alphabet))
--           (compileTypeFuel
--             (typeCompilationFuel (right.reannotate alphabet))
--             (right.reannotate alphabet))
--           (computeFutureOf left)
--           (computeFutureOf right)
--           (computeFutureOfFuel
--             (typeCompilationFuel (left.reannotate alphabet))
--             (left.reannotate alphabet))
--           (computeFutureOfFuel
--             (typeCompilationFuel (right.reannotate alphabet))
--             (right.reannotate alphabet))
--           (.pair q1 q2) ∧
--         ((∃ childOffers : TypeOfferSummary,
--             -- The survivor stands for the child re-stamped with the merged
--             -- alphabet, so its own edge carries the projected environment.
--             (compileType left).HasEdge q1
--               (projectAutomatonEnvironment left.alphabet env) label
--               childOffers q' ∧
--             restrictTypeOffers interface childOffers.current = ∅ ∧
--             restrictTypeOffers interface childOffers.future = ∅ ∧
--             offers = TypeOfferSummary.mk childOffers.current
--               (match parallelFutureSpec (.visible label) (.survivor 0 q')
--                   childOffers.current with
--                 | .explicit o => o
--                 | .at state removed =>
--                     computeFutureOf
--                       (.par alphabet left right interface) state \ removed) ∧
--             q2 ∈ (compileType right).accepting ∧
--             q2 ∈ (compileTypeFuel
--               (typeCompilationFuel right) right).states ∧
--             q' ∉ (compileType left).accepting ∧
--             q' ∉ (compileTypeFuel
--               (typeCompilationFuel left) left).accepting ∧
--             target = .survivor 0 q') ∨
--           (∃ childOffers : TypeOfferSummary,
--             (compileType right).HasEdge q2
--               (projectAutomatonEnvironment right.alphabet env) label
--               childOffers q' ∧
--             restrictTypeOffers interface childOffers.current = ∅ ∧
--             restrictTypeOffers interface childOffers.future = ∅ ∧
--             offers = TypeOfferSummary.mk childOffers.current
--               (match parallelFutureSpec (.visible label) (.survivor 1 q')
--                   childOffers.current with
--                 | .explicit o => o
--                 | .at state removed =>
--                     computeFutureOf
--                       (.par alphabet left right interface) state \ removed) ∧
--             q1 ∈ (compileType left).accepting ∧
--             q1 ∈ (compileTypeFuel
--               (typeCompilationFuel left) left).states ∧
--             q' ∉ (compileType right).accepting ∧
--             q' ∉ (compileTypeFuel
--               (typeCompilationFuel right) right).accepting ∧
--             target = .survivor 1 q'))) := by
--   -- TODO: proof invalidated by the 2026-09-01 spec change (re-stamped parallel children / new offer law).
--   sorry

-- /-- The related-state shape for a compiled parallel product: a product state
-- represents the pointwise composition, a survivor state represents a residual of
-- the re-signed component it survives in, and `.final` represents `skip` once both
-- components finish. -/
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

end Pact
