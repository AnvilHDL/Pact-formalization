import Anvilpp.Examples.WeakRefinementStrategies
import Anvilpp.ProofHelpers.RefinementLifting

namespace Pact.WeakRefinement

noncomputable section

open Classical

/-- Local availability combines the outer availability with the sibling's interface offers. -/
theorem local_environment_available
    {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
    {source : PactType} {current future : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface source siblingEnv current future localEnv)
    (hClock : outer.clock = false) :
    typeAvailable localEnv = typeAvailable outer ∪ restrictTypeOffers interface (current ∪ future) := by
  rw [localTypeOfferEnvironment_eq hLocal hClock]
  ext action
  simp only [typeAvailable, restrictTypeOffers, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_filter]
  tauto

/-- Retiming a sibling's offers preserves local availability when their total is unchanged. -/
theorem local_environment_available_agree
    {outer outer' siblingEnv siblingEnv' localEnv localEnv' : TypeEnvironment}
    {interface : Interface} {source source' : PactType}
    {current future current' future' : Finset BareMessage}
    (hLocal : LocalTypeOfferEnvironment outer interface source siblingEnv current future localEnv)
    (hLocal' : LocalTypeOfferEnvironment outer' interface source' siblingEnv' current' future' localEnv')
    (hClock : outer.clock = false) (hClock' : outer'.clock = false)
    (hOuter : typeAvailable outer = typeAvailable outer')
    (hOffers : restrictTypeOffers interface (current ∪ future) =
      restrictTypeOffers interface (current' ∪ future')) :
    typeAvailable localEnv = typeAvailable localEnv' := by
  rw [local_environment_available hLocal hClock, local_environment_available hLocal' hClock',
    hOuter, hOffers]

private theorem projectParallel_eq_of_hidden {parent child : PactTypeAlphabet} {interface : Interface}
    (hHidden : PactTypeAlphabet.hideInterface child interface = parent) :
    PactTypeAlphabet.projectParallel parent child interface = child := by
  rw [← hHidden]
  apply congrArg PactTypeAlphabet.mk
  ext action
  simp only [PactTypeAlphabet.hideInterface,
    Finset.mem_union, Finset.mem_filter]
  tauto

private theorem local_wellFormed {outer siblingEnv localEnv : TypeEnvironment}
    {interface : Interface} {source : PactType} {current future : Finset BareMessage}
    {parent child sibling : PactTypeAlphabet}
    (hLocal : LocalTypeOfferEnvironment outer interface source siblingEnv current future localEnv)
    (hOuter : outer.WellFormed parent)
    (hCompat : PactTypeAlphabet.ParallelCompatible parent child sibling interface)
    (hSibling : sibling.WellFormed) (hCurrent : current ⊆ sibling.actions)
    (hFuture : future ⊆ sibling.actions) : localEnv.WellFormed child := by
  have h := localTypeOfferEnvironment_wellFormed hLocal hOuter hCompat.complementary
    hSibling hCurrent hFuture
  rwa [projectParallel_eq_of_hidden hCompat.parent_eq_left] at h

private theorem shared_not_enabled {outer : TypeEnvironment} {parent left right : PactTypeAlphabet}
    {interface : Interface} {action : BareMessage}
    (hWF : outer.WellFormed parent)
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left right interface)
    (hShared : action.1 ∈ interface) : ¬ outer.hasNeed action := by
  intro hNeed
  exact hCompat.parent_hides_interface action (mem_actions_of_hasNeed hWF hNeed) hShared

private theorem shared_message_wait_shape
    {outer leftEnv rightEnv : TypeEnvironment} {parent leftAlphabet rightAlphabet : PactTypeAlphabet}
    {interface : Interface} {action : BareMessage} {future : Finset BareMessage}
    {target : PactType} {label : TypeLabel} {current rightFuture : Finset BareMessage}
    (hCompat : PactTypeAlphabet.ParallelCompatible parent leftAlphabet rightAlphabet interface)
    (hShared : action.1 ∈ interface) (hOuter : outer.WellFormed parent)
    (hLocal : LocalTypeOfferEnvironment outer interface
      (.message rightAlphabet action.1 action.2) leftEnv ∅ future rightEnv)
    (hStep : TypeOffers rightEnv (.message rightAlphabet action.1 action.2)
      label target current rightFuture) :
    label = TypeLabel.silent ∧ target = .message rightAlphabet action.1 action.2 ∧
      current = {action} ∩ rightAlphabet.actions ∧ rightFuture = ∅ := by
  have hNotNeed : ¬ rightEnv.hasNeed action := by
    intro hNeed
    cases hLocal with
    | clock _ _ _ _ _ => simp [TypeEnvironment.hasNeed, TypeEnvironment.tock] at hNeed
    | ordinary _ _ _ _ _ _ _ _ _ hImmediate _ =>
        apply shared_not_enabled hOuter hCompat hShared
        simpa [TypeEnvironment.hasNeed, hImmediate, restrictTypeOffers] using hNeed
  cases hStep with
  | action _ _ _ _ hPrem => exact (hNotNeed hPrem.2).elim
  | action_wait =>
      by_cases hDeclared : action ∈ rightAlphabet.actions <;>
        simp [typeFutureOffers_message, hDeclared]

/-- A shared message waits during a sibling's leading skip; the next state is the original product. -/
theorem shared_message_skip_offers_iff
    {parent rightAlphabet : PactTypeAlphabet} {left target : PactType} {interface : Interface}
    {action : BareMessage} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hLeft : left.AlphabetWellFormed) (hRight : rightAlphabet.WellFormed)
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left.alphabet rightAlphabet interface)
    (hShared : action.1 ∈ interface) :
    TypeOffers env (.par parent (skipPrefix left) (.message rightAlphabet action.1 action.2) interface)
        label target current future ↔
      env.WellFormed parent ∧ env.clock = false ∧ label = TypeLabel.silent ∧
        target = .par parent left (.message rightAlphabet action.1 action.2) interface ∧
        current = ∅ ∧ future = hideTypeOffers interface (typeFutureOffers left) := by
  constructor
  · intro hStep
    cases hStep with
    | par _ leftEnv rightEnv _ _ _ left' _ right' leftLabel rightLabel
        leftCurrent leftFuture rightCurrent rightFuture _ _ hLS hRS _ hLL hLR hPrem =>
        obtain ⟨_, hClock, rfl, rfl, rfl, rfl⟩ := skipPrefix_offers_iff.mp hLS
        obtain ⟨rfl, rfl, rfl, rfl⟩ := shared_message_wait_shape hCompat hShared hPrem.1 hLR hRS
        have hOuterClock : env.clock = false := by
          cases hLL with
          | clock => simp [TypeEnvironment.tock] at hClock
          | ordinary => assumption
        have hCombine := TypeLabel.combine_silent_left interface TypeLabel.silent hPrem.2
        refine ⟨hPrem.1, hOuterClock, hCombine, rfl, ?_, ?_⟩
        · ext offer
          simp only [Finset.empty_union, hideTypeOffers, Finset.mem_filter,
            Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨⟨rfl, _⟩, hNotShared⟩
          exact hNotShared hShared
        · rw [hCombine]
          simp [TypeLabel.silent]
    | par_fuse _ _ _ _ _ _ _ _ _ _ _ _ _ hLS hRS _ hLR hPrem _ =>
        obtain ⟨_, _, _, _, rfl, _⟩ := skipPrefix_offers_iff.mp hLS
        have hShape := shared_message_wait_shape hCompat hShared hPrem.1 hLR hRS
        cases hShape.2.1
    | par_fuse_tock _ _ _ _ _ _ _ _ _ _ _ _ _ hLS hRS _ hLR hPrem _ =>
        obtain ⟨_, _, _, _, rfl, _⟩ := skipPrefix_offers_iff.mp hLS
        have hShape := shared_message_wait_shape hCompat hShared hPrem.1 hLR hRS
        cases hShape.2.1
    | left_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hSkip => cases hSkip
    | right_complete _ _ _ _ _ _ _ _ _ _ _ _ _ hSkip => cases hSkip
  · rintro ⟨hEnv, hClock, rfl, rfl, rfl, rfl⟩
    let rightCurrent : Finset BareMessage := {action} ∩ rightAlphabet.actions
    let leftEnv : TypeEnvironment := {
      immediate := env.immediate ∪ restrictTypeOffers interface rightCurrent
      future := env.future \ (env.immediate ∪ restrictTypeOffers interface rightCurrent)
      clock := false }
    let rightEnv : TypeEnvironment := {
      immediate := env.immediate
      future := (env.future ∪ restrictTypeOffers interface (typeFutureOffers left)) \ env.immediate
      clock := false }
    have hLL : LocalTypeOfferEnvironment env interface (skipPrefix left) rightEnv
        rightCurrent ∅ leftEnv := by
      apply LocalTypeOfferEnvironment.ordinary <;> simp [hClock, leftEnv, rightEnv, restrictTypeOffers]
    have hLR : LocalTypeOfferEnvironment env interface (.message rightAlphabet action.1 action.2)
        leftEnv ∅ (typeFutureOffers left) rightEnv := by
      apply LocalTypeOfferEnvironment.ordinary <;> simp [hClock, leftEnv, rightEnv, restrictTypeOffers]
    have hLeftEnv := local_wellFormed hLL hEnv hCompat hRight
      (Finset.inter_subset_right) (Finset.empty_subset _)
    have hRightCompat : PactTypeAlphabet.ParallelCompatible parent rightAlphabet left.alphabet interface :=
      ⟨hCompat.parent_hides_interface, hCompat.complementary.symm,
        hCompat.parent_eq_right, hCompat.parent_eq_left⟩
    have hRightEnv := local_wellFormed hLR hEnv hRightCompat hLeft.alphabet_wellFormed
      (Finset.empty_subset _) (typeFutureOffers_subset_alphabet left hLeft)
    have hLS := skipPrefix_offers_iff.mpr
      ⟨hLeftEnv, rfl, rfl, rfl, rfl, rfl⟩
    have hRS := TypeOffers.action_wait rightEnv rightAlphabet action.1 action.2
      ⟨hRightEnv, (show ¬ env.hasNeed action from shared_not_enabled hEnv hCompat hShared), rfl⟩
    have hRS' : TypeOffers rightEnv (.message rightAlphabet action.1 action.2)
        TypeLabel.silent (.message rightAlphabet action.1 action.2) rightCurrent ∅ := by
      by_cases hDeclared : action ∈ rightAlphabet.actions <;>
        simpa [rightCurrent, typeFutureOffers_message, hDeclared] using hRS
    have hSync : TypeLabel.Sync interface TypeLabel.silent TypeLabel.silent := by
      simp [TypeLabel.Sync, TypeLabel.silent, TypeLabel.isTock, TypeLabel.sends,
        TypeLabel.recvs, TypeLabel.messageIdsWith]
    have hHidden : hideTypeOffers interface rightCurrent = ∅ := by
      ext offer
      simp only [rightCurrent, hideTypeOffers, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨⟨rfl, _⟩, hNotShared⟩
      exact hNotShared hShared
    have hRule := TypeOffers.par env leftEnv rightEnv interface parent
      (skipPrefix left) left (.message rightAlphabet action.1 action.2)
      (.message rightAlphabet action.1 action.2) TypeLabel.silent TypeLabel.silent
      ∅ (typeFutureOffers left) rightCurrent ∅ (by simp [skipPrefix]) (by simp)
      hLS hRS' (by simp) hLL hLR ⟨hEnv, hSync⟩
    rw [TypeLabel.combine_silent_left interface TypeLabel.silent hSync] at hRule
    simpa [hHidden, TypeLabel.silent] using hRule

/-- Beside a shared prefix, delaying the left component refines delaying the whole product. -/
theorem shared_message_skip_refines_prefix
    {parent rightAlphabet : PactTypeAlphabet} {left : PactType} {interface : Interface}
    {action : BareMessage} (hLeft : left.AlphabetWellFormed) (hRight : rightAlphabet.WellFormed)
    (hCompat : PactTypeAlphabet.ParallelCompatible parent left.alphabet rightAlphabet interface)
    (hShared : action.1 ∈ interface) :
    Refines
      (.par parent (skipPrefix left) (.message rightAlphabet action.1 action.2) interface)
      (skipPrefix (.par parent left (.message rightAlphabet action.1 action.2) interface)) := by
  let original := PactType.par parent left (.message rightAlphabet action.1 action.2) interface
  let delayed := PactType.par parent (skipPrefix left) (.message rightAlphabet action.1 action.2) interface
  have hMenu : typeFutureOffers original = hideTypeOffers interface (typeFutureOffers left) := by
    dsimp [original]
    rw [typeFutureOffers_parallel, typeFutureOffers_message]
    ext offer
    by_cases hDeclared : action ∈ rightAlphabet.actions <;>
      simp only [hDeclared, if_true, if_false, hideTypeOffers, Finset.mem_filter,
        Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, or_false]
    constructor
    · rintro ⟨h | rfl, hVisible⟩
      · exact ⟨h, hVisible⟩
      · exact (hVisible hShared).elim
    · rintro ⟨h, hVisible⟩
      exact ⟨Or.inl h, hVisible⟩
  have hOffers {env : TypeEnvironment} {label : TypeLabel} {target : PactType}
      {current future : Finset BareMessage} :
      TypeOffers env delayed label target current future ↔
        TypeOffers env (skipPrefix original) label target current future := by
    rw [shared_message_skip_offers_iff hLeft hRight hCompat hShared, skipPrefix_offers_iff, hMenu]
    rfl
  refine ⟨{
    relation := fun precise abstract => precise = abstract ∨
      (precise = delayed ∧ abstract = skipPrefix original)
    initial := Or.inr ⟨rfl, rfl⟩
    skipIff := ?_
    availability := ?_
    response := ?_ }⟩
  · rintro precise abstract (rfl | ⟨rfl, rfl⟩)
    · rfl
    · simp [delayed, skipPrefix]
  · rintro precise abstract target env label offers (rfl | ⟨rfl, rfl⟩) hStep
    · exact ⟨target, hStep⟩
    · have hMatch := hOffers.mpr hStep.2
      exact ⟨target, hMatch.toTypeTransition, hMatch⟩
  · rintro precise abstract target env label offers (rfl | ⟨rfl, rfl⟩) hStep
    · exact ⟨target, hStep, Or.inl rfl⟩
    · have hMatch := hOffers.mp hStep.2
      exact ⟨target, ⟨hMatch.toTypeTransition, hMatch⟩, Or.inl rfl⟩

/-- A leading skip in one component preserves compatibility beside a shared message prefix. -/
theorem compatible_parallel_skip_shared_message
    {parent rightAlphabet : PactTypeAlphabet} {left : PactType} {interface : Interface}
    {action : BareMessage} {progress : Finset ProcId}
    (hOriginal : TypeWellFormedIn []
      (.par parent left (.message rightAlphabet action.1 action.2) interface))
    (hDelayed : TypeWellFormedIn []
      (.par parent (skipPrefix left) (.message rightAlphabet action.1 action.2) interface))
    (hShared : action.1 ∈ interface)
    (hCompatible : TypeCompatible
      (.par parent left (.message rightAlphabet action.1 action.2) interface) progress) :
    TypeCompatible
      (.par parent (skipPrefix left) (.message rightAlphabet action.1 action.2) interface) progress := by
  have hAlphabet := hOriginal.1
  simp only [PactType.AlphabetWellFormed, PactType.alphabet] at hAlphabet
  have hRefines := shared_message_skip_refines_prefix hAlphabet.2.2.1
    hAlphabet.2.2.2 hAlphabet.2.1 hShared
  exact compatibility_monotone_of_refines hDelayed (skipPrefix_wellFormed hOriginal)
    (by simp [skipPrefix, typeFairIds]) (by simp [skipPrefix, PactType.ProgressIds])
    hRefines ((compatible_skipPrefix_iff hOriginal).mpr hCompatible)

end

end Pact.WeakRefinement
