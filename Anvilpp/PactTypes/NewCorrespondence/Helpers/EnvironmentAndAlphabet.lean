import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

@[simp] theorem transitionAlphabet_mk_mem_iff
    (signature : TypeAlphabet) (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) :
    TypeAutomatonSymbol.mk env label offers ∈ signature.transitionAlphabet ↔
      env ∈ signature.localEnvironments ∧
      label ∈ signature.localLabels ∧
      offers ∈ signature.localOfferSummaries := by
  classical
  simp [TypeAlphabet.transitionAlphabet]

@[simp] theorem localOfferSummaries_mk_mem_iff
    (signature : TypeAlphabet) (current future : Finset BareMessage) :
    TypeOfferSummary.mk current future ∈ signature.localOfferSummaries ↔
      current ⊆ signature.localActions ∧
      future ⊆ signature.localActions := by
  classical
  simp [TypeAlphabet.localOfferSummaries, TypeAlphabet.localOfferSets]

theorem localEnvironment_wellFormed
    (signature : TypeAlphabet) {environment : TypeEnvironment}
    (hEnvironment : environment ∈ signature.localEnvironments) :
    environment.WellFormed := by
  simp only [TypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _hImmediate, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _hClock
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      have hAvailable := hFuture hFutureMember
      simp only [Finset.mem_sdiff] at hAvailable
      exact hAvailable.2 hImmediate

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
  exact buildRelationSetCore_functional auto.signature ty hRelated hRelated'


/-- Proves a step's future offer is contained in the target menu together with its current offer. -/
theorem typeOffers_future_subset_target_union_current
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env source label target current future) :
    future ⊆ typeFutureOffers target ∪ current := by
  induction hOffers using TypeOffers.rec
    (motive_2 := fun _ _ _ _ _ _ _ => True) with
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
  | seq_fuse =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | xoffer_branch =>
      simp
  | xoffer_else =>
      simp
  | xoffer_wait =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | offer_some =>
      simp
  | offer_else =>
      simp
  | offer_wait =>
      intro action hAction
      simp at hAction ⊢
      exact Or.inl hAction.1
  | par =>
      intro action hAction
      rw [typeFutureOffers_parallel]
      simp only [Finset.mem_union]
      simp only [hideTypeOffers, Finset.mem_filter] at hAction ⊢
      obtain ⟨hAction, hInterface⟩ := hAction
      simp only [Finset.mem_union] at hAction
      rcases hAction with hLeft | hRight
      · rename_i hLeftOffers hRightOffers _ _ _ _ hLeftIH _ _ _
        have hLeft' := hLeftIH hLeft
        simp only [Finset.mem_union] at hLeft'
        rcases hLeft' with hFuture | hCurrent
        · exact Or.inl ⟨Finset.mem_union.mpr (Or.inl hFuture), hInterface⟩
        · exact Or.inr ⟨Finset.mem_union.mpr (Or.inl hCurrent), hInterface⟩
      · rename_i hLeftOffers hRightOffers _ _ _ _ _ hRightIH _ _
        have hRight' := hRightIH hRight
        simp only [Finset.mem_union] at hRight'
        rcases hRight' with hFuture | hCurrent
        · exact Or.inl ⟨Finset.mem_union.mpr (Or.inr hFuture), hInterface⟩
        · exact Or.inr ⟨Finset.mem_union.mpr (Or.inr hCurrent), hInterface⟩
  | par_fuse =>
      intro action hAction
      simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
      simp only [hideTypeOffers, Finset.mem_filter] at hAction ⊢
      obtain ⟨hAction, hInterface⟩ := hAction
      simp only [Finset.mem_union] at hAction
      rcases hAction with hLeft | hRight
      · rename_i hLeftOffers hRightOffers _ _ _ hLeftIH _ _ _
        have hLeft' := hLeftIH hLeft
        simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
          at hLeft'
        exact ⟨Finset.mem_union.mpr (Or.inl hLeft'), hInterface⟩
      · rename_i hLeftOffers hRightOffers _ _ _ _ hRightIH _ _
        have hRight' := hRightIH hRight
        simp only [typeFutureOffers, typeFutureOffersFuel, Finset.empty_union]
          at hRight'
        exact ⟨Finset.mem_union.mpr (Or.inr hRight'), hInterface⟩
  | clock =>
      trivial
  | ordinary =>
      trivial

/-- Proves that a transition-alphabet symbol carries an offer summary from the signature. -/
theorem transitionAlphabet_offerSummary_mem
    (signature : TypeAlphabet) {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    offers ∈ signature.localOfferSummaries := by
  classical
  unfold TypeAlphabet.transitionAlphabet at hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  obtain ⟨environment, _hEnvironment, hSymbol⟩ := hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  obtain ⟨label', _hLabel, hOffers⟩ := hSymbol
  rw [Finset.mem_image] at hOffers
  obtain ⟨offers', hOffers', hEq⟩ := hOffers
  cases hEq
  exact hOffers'

/-- Proves that a transition-alphabet symbol remains in the alphabet when only its offer summary is replaced by another signature offer summary. -/
theorem transitionAlphabet_change_offers
    (signature : TypeAlphabet) {env : TypeEnvironment} {label : TypeLabel}
    {offers offers' : TypeOfferSummary}
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet)
    (hOffers' : offers' ∈ signature.localOfferSummaries) :
    TypeAutomatonSymbol.mk env label offers' ∈ signature.transitionAlphabet := by
  classical
  unfold TypeAlphabet.transitionAlphabet at hSymbol ⊢
  rw [Finset.mem_biUnion] at hSymbol
  obtain ⟨environment, hEnvironment, hSymbol⟩ := hSymbol
  rw [Finset.mem_biUnion] at hSymbol
  obtain ⟨label', hLabel, hOffers⟩ := hSymbol
  rw [Finset.mem_image] at hOffers
  obtain ⟨offers0, _hOffers0, hEq⟩ := hOffers
  cases hEq
  rw [Finset.mem_biUnion]
  refine ⟨env, hEnvironment, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨label, hLabel, ?_⟩
  rw [Finset.mem_image]
  exact ⟨offers', hOffers', rfl⟩

/-- Proves that an offer summary stays supported when its future part is drawn from the old future and current parts. -/
theorem offerSummary_mem_of_future_subset_union
    (signature : TypeAlphabet) {current future future' : Finset BareMessage}
    (hOffers : TypeOfferSummary.mk current future ∈ signature.localOfferSummaries)
    (hFuture' : future' ⊆ future ∪ current) :
    TypeOfferSummary.mk current future' ∈ signature.localOfferSummaries := by
  classical
  unfold TypeAlphabet.localOfferSummaries at hOffers ⊢
  rw [Finset.mem_biUnion] at hOffers
  obtain ⟨current0, hCurrent0, hImage⟩ := hOffers
  rw [Finset.mem_image] at hImage
  obtain ⟨future0, hFuture0, hEq⟩ := hImage
  cases hEq
  rw [Finset.mem_biUnion]
  refine ⟨current, hCurrent0, ?_⟩
  rw [Finset.mem_image]
  refine ⟨future', ?_, rfl⟩
  unfold TypeAlphabet.localOfferSets at hCurrent0 hFuture0 ⊢
  rw [Finset.mem_powerset] at hCurrent0 hFuture0 ⊢
  intro action hAction
  have hUnion := hFuture' hAction
  rw [Finset.mem_union] at hUnion
  exact hUnion.elim (fun hFuture => hFuture0 hFuture)
    (fun hCurrent => hCurrent0 hCurrent)

/-- Proves transition-alphabet closure when the new future offer is drawn from the old future and current offers. -/
theorem transitionAlphabet_change_future_of_subset_union
    (signature : TypeAlphabet) {env : TypeEnvironment} {label : TypeLabel}
    {current future future' : Finset BareMessage}
    (hSymbol :
      TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future) ∈
        signature.transitionAlphabet)
    (hFuture' : future' ⊆ future ∪ current) :
    TypeAutomatonSymbol.mk env label (TypeOfferSummary.mk current future') ∈
      signature.transitionAlphabet := by
  exact transitionAlphabet_change_offers signature hSymbol
    (offerSummary_mem_of_future_subset_union signature
      (transitionAlphabet_offerSummary_mem signature hSymbol) hFuture')

/-- Proves that a child offer pair remains in the transition alphabet when its target menu is covered by the parent future and current offers. -/
theorem transitionAlphabet_of_typeOffers_target_subset
    (signature : TypeAlphabet) {env : TypeEnvironment} {source target : PactType}
    {label : TypeLabel} {current parentFuture childFuture : Finset BareMessage}
    (hSymbol :
      TypeAutomatonSymbol.mk env label
        (TypeOfferSummary.mk current parentFuture) ∈
          signature.transitionAlphabet)
    (hOffers : TypeOffers env source label target current childFuture)
    (hTarget :
      typeFutureOffers target ⊆ parentFuture ∪ current) :
    TypeAutomatonSymbol.mk env label
      (TypeOfferSummary.mk current childFuture) ∈ signature.transitionAlphabet := by
  apply transitionAlphabet_change_future_of_subset_union signature hSymbol
  intro action hAction
  have hStepFuture :=
    typeOffers_future_subset_target_union_current hOffers hAction
  rw [Finset.mem_union] at hStepFuture ⊢
  rcases hStepFuture with hFuture | hCurrent
  · simpa [Finset.mem_union] using hTarget hFuture
  · exact Or.inr hCurrent

/-- Proves that a finite set is contained in itself with a current-offer set restored after subtraction. -/
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
