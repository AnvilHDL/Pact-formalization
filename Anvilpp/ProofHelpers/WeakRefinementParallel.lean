import Anvilpp.ProofHelpers.WeakRefinementEnvironments
import Anvilpp.PactTypes.Proofs.Syntax.TypeTransitionSystemLemmas
import Anvilpp.ProofHelpers.Inference.DecoratedLifting

namespace Pact

noncomputable section

open Classical

namespace WeakRefinement

private theorem local_empty_interface {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) (hClock : env.clock = false)
    (source : PactType) (current future : Finset BareMessage) :
    LocalTypeOfferEnvironment env ∅ source env current future env := by
  have hDisjoint : Disjoint env.future env.immediate :=
    (Finset.disjoint_iff_inter_eq_empty.mpr (hWF.2.1 hClock)).symm
  apply LocalTypeOfferEnvironment.ordinary <;>
    simp [hClock, restrictTypeOffers, Finset.sdiff_eq_self_of_disjoint hDisjoint]

private theorem local_empty_interface_iff {env localEnv sibling : TypeEnvironment}
    {alphabet : PactTypeAlphabet} (hWF : env.WellFormed alphabet) (hClock : env.clock = false)
    {source : PactType} {current future : Finset BareMessage} :
    LocalTypeOfferEnvironment env ∅ source sibling current future localEnv ↔
      sibling.clock = false ∧ localEnv = env := by
  have hDisjoint : Disjoint env.future env.immediate :=
    (Finset.disjoint_iff_inter_eq_empty.mpr (hWF.2.1 hClock)).symm
  constructor
  · intro hLocal
    have hEq := localTypeOfferEnvironment_eq hLocal hClock
    have hEnv : TypeEnvironment.mk env.immediate env.future false = env := by
      cases env
      simp only at hClock
      subst hClock
      rfl
    have hLocalEq : localEnv = env := by
      rw [hEq]
      simpa [restrictTypeOffers, Finset.sdiff_eq_self_of_disjoint hDisjoint] using hEnv
    refine ⟨?_, hLocalEq⟩
    cases hLocal with
    | clock _ _ _ _ hOuter => exact absurd hOuter (by rw [hClock]; simp)
    | ordinary => assumption
  · rintro ⟨hSibling, rfl⟩
    apply LocalTypeOfferEnvironment.ordinary <;>
      simp [hClock, hSibling, restrictTypeOffers, Finset.sdiff_eq_self_of_disjoint hDisjoint]

/-- A leading skip takes one silent step to its continuation and has no other response. -/
theorem skip_prefix_transition_iff {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {source target : PactType} {label : TypeLabel} :
    TypeTransition env (.seq alphabet (.skip alphabet) source) label target ↔
      env.WellFormed alphabet ∧ env.clock = false ∧
      label = TypeLabel.silent ∧ target = source := by
  constructor
  · intro hStep
    cases hStep with
    | seq_fuse _ _ _ _ _ _ hSkip =>
        cases hSkip with
        | skip _ _ hPrem => exact ⟨hPrem.1, hPrem.2, rfl, rfl⟩
    | seq _ _ _ _ _ _ hSkip hNotSkip =>
        cases hSkip
        exact (hNotSkip rfl).elim
  · rintro ⟨hWF, hClock, rfl, rfl⟩
    exact .seq_fuse _ _ _ _ _ _ (.skip _ _ ⟨hWF, hClock⟩)

/-- An enabled message prefix must communicate and finish. -/
theorem enabled_message_transition_iff {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {label : TypeLabel} {target : PactType}
    (hNeed : env.hasNeed action) :
    TypeTransition env (.message alphabet action.1 action.2) label target ↔
      env.WellFormed alphabet ∧ label = TypeLabel.message action.1 action.2 ∧
      target = .skip alphabet := by
  constructor
  · intro hStep
    cases hStep with
    | action _ _ _ _ hPrem => exact ⟨hPrem.1, rfl, rfl⟩
    | action_wait _ _ _ _ hPrem => exact (hPrem.2.1 hNeed).elim
  · rintro ⟨hWF, rfl, rfl⟩
    exact .action _ _ _ _ ⟨hWF, hNeed⟩

private theorem skip_transition_iff {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {label : TypeLabel} {target : PactType} :
    TypeTransition env (.skip alphabet) label target ↔
      env.WellFormed alphabet ∧ env.clock = false ∧
      label = TypeLabel.silent ∧ target = .skip alphabet := by
  constructor
  · intro hStep
    cases hStep with
    | skip _ _ hPrem => exact ⟨hPrem.1, hPrem.2, rfl, rfl⟩
  · rintro ⟨hWF, hClock, rfl, rfl⟩
    exact .skip _ _ ⟨hWF, hClock⟩

/-- Every first response of the delayed independent pair communicates only on the right. -/
theorem independent_messages_delayed_first {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {left right : BareMessage} {label : TypeLabel} {target : PactType}
    (hWF : env.WellFormed alphabet) (hClock : env.clock = false) (hRight : env.hasNeed right)
    (hStep : TypeTransition env
      (.par alphabet (.seq alphabet (.skip alphabet) (.message alphabet left.1 left.2))
        (.message alphabet right.1 right.2) ∅) label target) :
    label = TypeLabel.message right.1 right.2 ∧
      target = .par alphabet (.message alphabet left.1 left.2) (.skip alphabet) ∅ := by
  cases hStep <;>
    simp_all [local_empty_interface_iff hWF hClock, skip_prefix_transition_iff,
      enabled_message_transition_iff hRight, PactType.alphabet,
      TypeLabel.combine, TypeLabel.synced, TypeLabel.silent, TypeLabel.message,
      TypeLabel.isRawSyncedMessage]

/-- Every response of the final independent pair communicates on the left and finishes. -/
theorem independent_messages_delayed_last {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {left : BareMessage} {label : TypeLabel} {target : PactType}
    (hWF : env.WellFormed alphabet) (hClock : env.clock = false) (hLeft : env.hasNeed left)
    (hStep : TypeTransition env
      (.par alphabet (.message alphabet left.1 left.2) (.skip alphabet) ∅) label target) :
    label = TypeLabel.message left.1 left.2 ∧ target = .skip alphabet := by
  cases hStep <;>
    simp_all [local_empty_interface_iff hWF hClock, skip_transition_iff,
      enabled_message_transition_iff hLeft, PactType.alphabet,
      TypeLabel.combine, TypeLabel.synced, TypeLabel.silent, TypeLabel.message,
      TypeLabel.isRawSyncedMessage]

/-- Independent enabled messages finish in two honest rounds when the left prefix is delayed. -/
theorem independent_messages_skip_delay {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {left right : BareMessage} (hWF : env.WellFormed alphabet) (hClock : env.clock = false)
    (hNames : left.1 ≠ right.1) (hLeft : env.hasNeed left) (hRight : env.hasNeed right) :
    let leftType := PactType.message alphabet left.1 left.2
    let rightType := PactType.message alphabet right.1 right.2
    let leftLabel := TypeLabel.message left.1 left.2
    let rightLabel := TypeLabel.message right.1 right.2
    let residual := PactType.par alphabet leftType (.skip alphabet) ∅
    TypeTransition env (.par alphabet (.seq alphabet (.skip alphabet) leftType) rightType ∅)
        rightLabel residual ∧
      TypeTransition (env.afterNonclock rightLabel) residual leftLabel (.skip alphabet) ∧
      TypeTransition env (.par alphabet leftType rightType ∅)
        (TypeLabel.combine ∅ leftLabel rightLabel) (.skip alphabet) := by
  dsimp only
  have hLeftStep := TypeTransition.action env alphabet left.1 left.2 ⟨hWF, hLeft⟩
  have hRightStep := TypeTransition.action env alphabet right.1 right.2 ⟨hWF, hRight⟩
  have hDelayStep := (skip_prefix_transition_iff (source := .message alphabet left.1 left.2)).mpr
    ⟨hWF, hClock, rfl, rfl⟩
  obtain ⟨leftOffers, hLeftDecorated⟩ := hLeftStep.exists_decorated
  obtain ⟨rightOffers, hRightDecorated⟩ := hRightStep.exists_decorated
  obtain ⟨delayOffers, hDelayDecorated⟩ := hDelayStep.exists_decorated
  have hSyncDelay : TypeLabel.Sync ∅ TypeLabel.silent (TypeLabel.message right.1 right.2) := by
    simp [TypeLabel.Sync, TypeLabel.silent, TypeLabel.message, TypeLabel.isTock]
  have hFirst := TypeTransition.par env env env ∅ alphabet
    (.seq alphabet (.skip alphabet) (.message alphabet left.1 left.2))
    (.message alphabet left.1 left.2) (.message alphabet right.1 right.2) (.skip alphabet)
    TypeLabel.silent (TypeLabel.message right.1 right.2)
    delayOffers.current delayOffers.future rightOffers.current rightOffers.future
    (by simp) (by simp) hDelayStep hDelayDecorated.2 hRightStep hRightDecorated.2
    (by simp) ⟨hWF, local_empty_interface hWF hClock _ _ _,
      local_empty_interface hWF hClock _ _ _, hSyncDelay⟩
  have hNextWF := TypeEnvironment.afterNonclock_wellFormed hWF
    (TypeLabel.message right.1 right.2)
  have hNextClock : (env.afterNonclock (TypeLabel.message right.1 right.2)).clock = false := hClock
  have hNextLeft : (env.afterNonclock (TypeLabel.message right.1 right.2)).hasNeed left := by
    simpa [TypeEnvironment.afterNonclock, TypeEnvironment.hasNeed, hNames] using hLeft
  have hNextLeftStep := TypeTransition.action _ alphabet left.1 left.2 ⟨hNextWF, hNextLeft⟩
  have hNextRightStep := TypeTransition.skip _ alphabet ⟨hNextWF, hNextClock⟩
  obtain ⟨nextLeftOffers, hNextLeftDecorated⟩ := hNextLeftStep.exists_decorated
  obtain ⟨nextRightOffers, hNextRightDecorated⟩ := hNextRightStep.exists_decorated
  have hSyncNext : TypeLabel.Sync ∅ (TypeLabel.message left.1 left.2) TypeLabel.silent := by
    simp [TypeLabel.Sync, TypeLabel.silent, TypeLabel.message, TypeLabel.isTock]
  have hSecond := TypeTransition.par_fuse _ _ _ ∅ alphabet
    (.message alphabet left.1 left.2) (.skip alphabet)
    (TypeLabel.message left.1 left.2) TypeLabel.silent
    nextLeftOffers.current nextLeftOffers.future nextRightOffers.current nextRightOffers.future
    hNextLeftStep hNextLeftDecorated.2 hNextRightStep hNextRightDecorated.2
    ⟨hNextWF, local_empty_interface hNextWF hNextClock _ _ _,
      local_empty_interface hNextWF hNextClock _ _ _, hSyncNext⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [TypeLabel.combine_silent_left _ _ hSyncDelay] using hFirst
  · simpa only [TypeLabel.combine_silent_right _ _ hSyncNext] using hSecond
  · exact TypeTransition.par_fuse env env env ∅ alphabet
      (.message alphabet left.1 left.2) (.message alphabet right.1 right.2)
      (TypeLabel.message left.1 left.2) (TypeLabel.message right.1 right.2)
      leftOffers.current leftOffers.future rightOffers.current rightOffers.future
      hLeftStep hLeftDecorated.2 hRightStep hRightDecorated.2
      ⟨hWF, local_empty_interface hWF hClock _ _ _,
        local_empty_interface hWF hClock _ _ _, by
          simp [TypeLabel.Sync, TypeLabel.message, TypeLabel.isTock]⟩

/-- The split independent-message block leaves the same remainder as the joint response. -/
theorem independent_messages_block_remainder (env : TypeEnvironment) (left right : BareMessage) :
    typeAvailable ((env.afterNonclock (TypeLabel.message right.1 right.2)).afterNonclock
      (TypeLabel.message left.1 left.2)) =
      env.honestyRemainder
        (TypeLabel.combine ∅ (TypeLabel.message left.1 left.2) (TypeLabel.message right.1 right.2)) := by
  have hUsed := TypeLabel.blockUsed_eq_of_observations
    (labels := [TypeLabel.message right.1 right.2, TypeLabel.message left.1 left.2])
    (label := TypeLabel.combine ∅ (TypeLabel.message left.1 left.2) (TypeLabel.message right.1 right.2))
    (by simp [TypeLabel.message])
    (by simp [TypeLabel.combine, TypeLabel.message])
    (by
      intro observation
      cases observation <;>
        simp [TypeLabel.contains, TypeLabel.combine, TypeLabel.synced, TypeLabel.message,
          TypeLabel.isRawSyncedMessage, Finset.filter_insert, Finset.filter_singleton,
          or_comm])
  simpa only [TypeEnvironment.afterBlock] using
    (TypeEnvironment.available_afterBlock_of_same_used (env := env) hUsed)

end WeakRefinement

end

end Pact
