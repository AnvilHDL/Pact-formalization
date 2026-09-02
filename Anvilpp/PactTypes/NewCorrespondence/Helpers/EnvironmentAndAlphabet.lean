import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

@[simp] theorem PactTypeAlphabet.mem_localOfferSummaries_iff
    (alphabet : PactTypeAlphabet)
    (current future : Finset BareMessage) :
    TypeOfferSummary.mk current future ∈
        alphabet.localOfferSummaries ↔
      current ⊆ alphabet.actions ∧
      future ⊆ alphabet.actions := by
  classical
  simp [PactTypeAlphabet.localOfferSummaries]

/- Decorated type transitions are intentionally not target-deterministic.  For
example, an unresolved choice may silently select either branch while exposing
the same offers.  The correspondence proof therefore establishes target
relation membership with the relation clause for the source constructor. -/

/-- Proves a built relation set relates each automaton state to at most one residual. -/
lemma relationMembership_functional
    (ty : PactType) (auto : TypeAutomaton)
    {residual residual' : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty auto) residual state)
    (hRelated' : relationMembership (buildRelationSet ty auto) residual' state) :
    residual = residual' := by
  unfold relationMembership buildRelationSet at hRelated hRelated'
  exact buildRelationSetCore_functional ty hRelated hRelated'

/-- Proves a step's future offer is contained in the target menu together with its current offer. -/
theorem typeOffers_future_subset_target_union_current
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    future ⊆ typeFutureOffers target ∪ current := by
  induction hOffers using TypeOffers.rec with
  | action =>
      simp
  | action_wait =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inr hAction.1
  | choice_left =>
      simp
  | choice_right =>
      simp
  | fair_left =>
      simp
  | fair_right =>
      simp
  | cycle =>
      simp
  | cycle_wait =>
      simp
  | skip =>
      simp
  | progress =>
      simp
  | recur =>
      simp
  | seq =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | seq_tock =>
      simp
  | seq_fuse =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | seq_fuse_tock =>
      simp
  | xoffer_branch =>
      exact Finset.sdiff_subset.trans Finset.subset_union_left
  | xoffer_else =>
      simp
  | xoffer_wait =>
      exact Finset.sdiff_subset.trans Finset.subset_union_left
  | offer_some =>
      simp
  | offer_else =>
      exact Finset.sdiff_subset.trans Finset.subset_union_left
  | offer_wait =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | par outer leftEnv rightEnv interface left leftTarget right rightTarget
      leftLabel rightLabel leftCurrent leftFuture rightCurrent rightFuture
      _ _ hLeftOffers hRightOffers hNonFinal hLocal1 hLocal2 hSide hLeftIH
      hRightIH =>
      -- A clock product publishes nothing; otherwise the published menu is
      -- the target's own menu minus the current offers.
      split
      · exact Finset.empty_subset _
      · exact Finset.sdiff_subset.trans Finset.subset_union_left
  | par_fuse outer leftEnv rightEnv interface left right leftLabel rightLabel
      leftCurrent leftFuture rightCurrent rightFuture hLeftOffers hRightOffers
      hLocal1 hLocal2 hSide hNotTock hLeftIH hRightIH =>
      intro action hAction
      simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
      simp only [hideTypeOffers, Finset.mem_filter] at hAction ⊢
      obtain ⟨hAction, hInterface⟩ := hAction
      simp only [Finset.mem_union] at hAction
      rcases hAction with hLeft | hRight
      · have hLeft' := hLeftIH hLeft
        simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
          at hLeft'
        exact ⟨Finset.mem_union.mpr (Or.inl hLeft'), hInterface⟩
      · have hRight' := hRightIH hRight
        simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
          at hRight'
        exact ⟨Finset.mem_union.mpr (Or.inr hRight'), hInterface⟩
  | par_fuse_tock =>
      simp
  | left_complete outer rightEnv interface left right right' rightLabel
      rightCurrent rightFuture hLeftSkip _ hRightOffers hNotSkip _ _ hLocal
      hWF hNotTock hRightIH =>
      exact Finset.sdiff_subset.trans Finset.subset_union_left
  | left_complete_tock =>
      simp
  | right_complete outer leftEnv interface left left' right leftLabel
      leftCurrent leftFuture hRightSkip _ hLeftOffers hNotSkip _ _ hLocal
      hWF hNotTock hLeftIH =>
      exact Finset.sdiff_subset.trans Finset.subset_union_left
  | right_complete_tock =>
      simp

theorem transitionAlphabetFor_change_future_of_subset_union
     (processType : PactType)
    {env : TypeEnvironment} {label : TypeLabel}
    {current future future' : Finset BareMessage}
    (hSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        processType.transitionAlphabet)
    (hFuture' : future' ⊆ future ∪ current) :
    TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future') ∈
      processType.transitionAlphabet := by
  rw [PactType.mem_transitionAlphabet_iff] at hSymbol ⊢
  refine ⟨hSymbol.1, hSymbol.2.1, ?_⟩
  rw [PactTypeAlphabet.mem_localOfferSummaries_iff]
  rw [PactTypeAlphabet.mem_localOfferSummaries_iff] at hSymbol
  exact ⟨hSymbol.2.2.1, hFuture'.trans
    (Finset.union_subset hSymbol.2.2.2 hSymbol.2.2.1)⟩

theorem transitionAlphabetFor_of_typeOffers_target_subset
     (processType : PactType)
    {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current parentFuture childFuture : Finset BareMessage}
    (hSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current parentFuture) ∈
          processType.transitionAlphabet)
    (hOffers : TypeOffers env source label target current childFuture)
    (hTarget :
      typeFutureOffers target ⊆ parentFuture ∪ current) :
    TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk current childFuture) ∈
        processType.transitionAlphabet := by
  apply transitionAlphabetFor_change_future_of_subset_union processType
    hSymbol
  intro action hAction
  have hStepFuture :=
    typeOffers_future_subset_target_union_current hOffers hAction
  rw [Finset.mem_union] at hStepFuture ⊢
  rcases hStepFuture with hFuture | hCurrent
  · simpa [Finset.mem_union] using hTarget hFuture
  · exact Or.inr hCurrent

theorem subset_sdiff_union_self {α : Type} [DecidableEq α]
    (future current : Finset α) :
    future ⊆ (future \ current) ∪ current := by
  intro action hAction
  by_cases hCurrent : action ∈ current
  · exact Finset.mem_union.mpr (Or.inr hCurrent)
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_sdiff.mpr ⟨hAction, hCurrent⟩))

/-- Proves that the left residual's future menu is contained in the enclosing sequence menu. -/
theorem typeFutureOffers_subset_sequence_left
    (alphabet : PactTypeAlphabet) (left right : PactType) :
    typeFutureOffers left ⊆ typeFutureOffers (.seq alphabet left right) := by
  intro action hAction
  rw [typeFutureOffers_sequence]
  by_cases hComplete : left.CanCompleteBeforeTock
  · simp [hComplete, hAction]
  · simp [hComplete, hAction]

/-- Proves that a child sequence target menu is covered by the parent sequence offer envelope. -/
theorem typeFutureOffers_subset_sequence_left_sdiff_union
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (current : Finset BareMessage) :
    typeFutureOffers left ⊆
      (typeFutureOffers (.seq alphabet left right) \ current) ∪ current :=
  (typeFutureOffers_subset_sequence_left alphabet left right).trans
    (subset_sdiff_union_self (typeFutureOffers (.seq alphabet left right)) current)


end

end Pact
