import Anvilpp.ProofHelpers.ResigningSteps
import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResidualMenus

namespace Pact.WeakRefinement

noncomputable section

open Classical

/-- A singleton exclusive offer is resolved exactly when its head is not promised. -/
theorem singleton_resolved_iff (env : TypeEnvironment) (action : BareMessage)
    (continuation : PactType) :
    TypeResolved env [(action, continuation)] ↔ typeNeed action ∉ env.future := by
  simp [TypeResolved, typeBranchNeeds, Finset.eq_empty_iff_forall_notMem]

/-- A promised singleton head is the entire waiting current offer. -/
theorem singleton_waiting_current {env : TypeEnvironment} {action : BareMessage}
    (continuation : PactType) (hPromised : typeNeed action ∈ env.future) :
    typeWaitingOffers env [(action, continuation)] = {action} := by
  have hImage : action ∈ env.future.image typeNeed :=
    Finset.mem_image.mpr ⟨typeNeed action, hPromised, by simp [typeNeed]⟩
  simp [typeWaitingOffers, typeBranchActions, hImage]

/-- Every step of a retained singleton advertises its declared head, including a default. -/
theorem optional_head_current {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {continuation target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      label target current future) :
    current = {action} ∩ alphabet.actions := by
  cases hOffers with
  | xoffer_branch _ _ _ _ selected branch hPrem =>
      obtain ⟨rfl, rfl⟩ := by simpa using hPrem.2.1
      have hDeclared := mem_actions_of_hasNeed hPrem.1 hPrem.2.2.1
      simp [hDeclared]
  | xoffer_else => simp [typeBranchActions]
  | xoffer_wait _ _ _ _ hPrem =>
      have hPromised : typeNeed action ∈ env.future := by
        simpa only [singleton_resolved_iff, not_not] using hPrem.2.1
      have hImage : action ∈ env.future.image typeNeed :=
        Finset.mem_image.mpr ⟨typeNeed action, hPromised, by simp [typeNeed]⟩
      rw [singleton_waiting_current continuation hPromised]
      simp [future_image_subset hPrem.1 hImage]

/-- All three singleton modes have the same future field. -/
theorem optional_head_future {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {continuation target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      label target current future) :
    future = typeFutureOffers
      (.xoffer alphabet (.skip alphabet) [(action, continuation)]) \ {action} := by
  cases hOffers with
  | xoffer_branch => simp [typeBranchActions]
  | xoffer_else => simp [typeBranchActions]
  | xoffer_wait _ _ _ _ hPrem =>
      have hPromised : typeNeed action ∈ env.future := by
        simpa only [singleton_resolved_iff, not_not] using hPrem.2.1
      rw [singleton_waiting_current continuation hPromised]

/-- A retained head's offer pair is independent of its environment and response mode. -/
theorem optional_head_offers_agree
    {firstEnv secondEnv : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {continuation firstTarget secondTarget : PactType}
    {firstLabel secondLabel : TypeLabel}
    {firstCurrent firstFuture secondCurrent secondFuture : Finset BareMessage}
    (hFirst : TypeOffers firstEnv
      (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      firstLabel firstTarget firstCurrent firstFuture)
    (hSecond : TypeOffers secondEnv
      (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      secondLabel secondTarget secondCurrent secondFuture) :
    firstCurrent = secondCurrent ∧ firstFuture = secondFuture :=
  ⟨(optional_head_current hFirst).trans (optional_head_current hSecond).symm,
    (optional_head_future hFirst).trans (optional_head_future hSecond).symm⟩

/-- A singleton's response fires, waits, or defaults according to its head's availability. -/
theorem optional_head_response_iff {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {continuation target : PactType} {label : TypeLabel}
    (hWF : env.WellFormed alphabet) (hClock : env.clock = false) :
    TypeTransition env (.xoffer alphabet (.skip alphabet) [(action, continuation)])
        label target ↔
      (typeNeed action ∈ env.immediate ∧
        label = TypeLabel.message action.1 action.2 ∧ target = continuation) ∨
      (typeNeed action ∈ env.future ∧ label = TypeLabel.silent ∧
        target = .xoffer alphabet (.skip alphabet) [(action, continuation)]) ∨
      (typeNeed action ∉ env.immediate ∧ typeNeed action ∉ env.future ∧
        label = TypeLabel.silent ∧ target = .skip alphabet) := by
  constructor
  · intro hStep
    cases hStep with
    | xoffer_branch _ _ _ _ selected branch hPrem =>
        obtain ⟨rfl, rfl⟩ := by simpa using hPrem.2.1
        exact Or.inl ⟨hPrem.2.2.1, rfl, rfl⟩
    | xoffer_wait _ _ _ _ hPrem =>
        refine Or.inr (Or.inl ⟨?_, rfl, rfl⟩)
        simpa only [singleton_resolved_iff, not_not] using hPrem.2.1
    | xoffer_else _ _ _ _ hPrem =>
        refine Or.inr (Or.inr ⟨?_, ?_, rfl, rfl⟩)
        · simpa [TypeNoImmediateBranch, typeBranchNeeds,
            Finset.eq_empty_iff_forall_notMem] using hPrem.2.2.1
        · exact (singleton_resolved_iff _ _ _).mp hPrem.2.2.2
  · rintro (⟨hEnabled, rfl, rfl⟩ | ⟨hPromised, rfl, rfl⟩ |
      ⟨hNotEnabled, hNotPromised, rfl, rfl⟩)
    · apply TypeTransition.xoffer_branch
      refine ⟨hWF, by simp, hEnabled, (singleton_resolved_iff _ _ _).mpr ?_⟩
      intro hPromised
      have hBoth := Finset.mem_inter.mpr ⟨hEnabled, hPromised⟩
      rw [hWF.2.1 hClock] at hBoth
      exact Finset.notMem_empty _ hBoth
    · exact TypeTransition.xoffer_wait _ _ _ _
        ⟨hWF, by simpa only [singleton_resolved_iff, not_not] using hPromised, hClock⟩
    · apply TypeTransition.xoffer_else
      refine ⟨hWF, hClock, ?_, (singleton_resolved_iff _ _ _).mpr hNotPromised⟩
      simpa [TypeNoImmediateBranch, typeBranchNeeds,
        Finset.eq_empty_iff_forall_notMem] using hNotEnabled

/-- Changing a retained singleton's non-clock mode preserves its sibling's local environment. -/
theorem optional_head_local_environment
    {outer firstEnv secondEnv localEnv : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {alphabet : PactTypeAlphabet}
    {action : BareMessage} {continuation firstTarget secondTarget : PactType}
    {firstLabel secondLabel : TypeLabel}
    {firstCurrent firstFuture secondCurrent secondFuture : Finset BareMessage}
    (hFirst : TypeOffers firstEnv
      (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      firstLabel firstTarget firstCurrent firstFuture)
    (hSecond : TypeOffers secondEnv
      (.xoffer alphabet (.skip alphabet) [(action, continuation)])
      secondLabel secondTarget secondCurrent secondFuture)
    (hFirstClock : firstEnv.clock = false) (hSecondClock : secondEnv.clock = false) :
    LocalTypeOfferEnvironment outer interface sibling firstEnv
        firstCurrent firstFuture localEnv ↔
      LocalTypeOfferEnvironment outer interface sibling secondEnv
        secondCurrent secondFuture localEnv := by
  obtain ⟨rfl, rfl⟩ := optional_head_offers_agree hFirst hSecond
  constructor
  · intro hLocal
    cases hLocal with
    | clock => simp [TypeEnvironment.tock] at hFirstClock
    | ordinary _ _ _ _ _ _ hOuter _ hLocal hImmediate hFuture =>
        exact .ordinary _ _ _ _ _ _ _ hOuter hSecondClock hLocal hImmediate hFuture
  · intro hLocal
    cases hLocal with
    | clock => simp [TypeEnvironment.tock] at hSecondClock
    | ordinary _ _ _ _ _ _ hOuter _ hLocal hImmediate hFuture =>
        exact .ordinary _ _ _ _ _ _ _ hOuter hFirstClock hLocal hImmediate hFuture

/-- Every conjunctive response advertises all declared heads. -/
theorem conjunctive_current {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    {elseType target : PactType} {branches : List (BareMessage × PactType)}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.offer alphabet elseType branches)
      label target current future) :
    current = typeBranchActions branches ∩ alphabet.actions := by
  cases hOffers <;> rfl

/-- Outside its advertised heads, a firing residual has exactly the continuation menus. -/
theorem conjunctive_firing_future (alphabet : PactTypeAlphabet)
    (selected : Finset Nat) (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) (action : BareMessage) :
    action ∈ typeFutureOffers (parallelTypeBranchesFiring alphabet selected branches) \
        (typeBranchActions branches ∩ alphabet.actions) ↔
      (∃ branch ∈ branches, action ∈ typeFutureOffers branch.2) ∧
        action ∉ typeBranchActions branches := by
  rw [Finset.mem_sdiff,
    mem_typeFutureOffers_parallelTypeBranchesFiring alphabet selected branches hAlphabet hWF]
  constructor
  · rintro ⟨⟨hDeclared, entry, hEntry, hMenu⟩, hNotHead⟩
    have hNotHead' : action ∉ typeBranchActions branches :=
      fun hHead => hNotHead (Finset.mem_inter.mpr ⟨hHead, hDeclared⟩)
    refine ⟨?_, hNotHead'⟩
    rcases hMenu with hMenu | ⟨_, rfl⟩
    · exact ⟨entry.1, List.fst_mem_of_mem_zipIdx hEntry, hMenu⟩
    · exact (hNotHead' (by
        simp only [typeBranchActions, List.mem_toFinset, List.mem_map]
        exact ⟨entry.1, List.fst_mem_of_mem_zipIdx hEntry, rfl⟩)).elim
  · rintro ⟨⟨branch, hBranch, hMenu⟩, hNotHead⟩
    have hIndexed : branch ∈ branches.zipIdx.map Prod.fst := by simpa using hBranch
    obtain ⟨entry, hEntry, hEq⟩ := List.mem_map.mp hIndexed
    refine ⟨⟨?_, entry, hEntry, Or.inl (hEq.symm ▸ hMenu)⟩, ?_⟩
    · rw [← hAlphabet branch hBranch]
      exact typeFutureOffers_subset_alphabet branch.2 (hWF branch hBranch) hMenu
    · exact fun h => hNotHead (Finset.mem_inter.mp h).1

/-- All firing subsets have the same future field after the current heads are removed. -/
theorem conjunctive_firing_futures_agree (alphabet : PactTypeAlphabet)
    (first second : Finset Nat) (branches : List (BareMessage × PactType))
    (hAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hWF : ∀ branch ∈ branches, branch.2.AlphabetWellFormed) :
    typeFutureOffers (parallelTypeBranchesFiring alphabet first branches) \
        (typeBranchActions branches ∩ alphabet.actions) =
      typeFutureOffers (parallelTypeBranchesFiring alphabet second branches) \
        (typeBranchActions branches ∩ alphabet.actions) := by
  ext action
  rw [conjunctive_firing_future alphabet first branches hAlphabet hWF,
    conjunctive_firing_future alphabet second branches hAlphabet hWF]

/-- Splitting a set of consumed heads preserves exactly their message observations. -/
theorem branch_batch_union (branches : List (BareMessage × PactType))
    (first second : Finset Nat) (observation : TypeObservation) :
    (typeBranchBatchLabel branches (first ∪ second)).contains observation ↔
      (typeBranchBatchLabel branches first).contains observation ∨
      (typeBranchBatchLabel branches second).contains observation := by
  simp only [typeBranchBatchLabel, TypeLabel.contains, List.mem_toFinset,
    List.mem_map, List.mem_filter, Finset.mem_union, decide_eq_true_eq]
  aesop

end

end Pact.WeakRefinement
