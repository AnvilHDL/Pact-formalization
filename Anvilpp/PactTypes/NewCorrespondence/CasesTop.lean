import Anvilpp.PactTypes.NewCorrespondence.Simultaneous

namespace Pact

open Classical
open Pact.NewCorrespondence

noncomputable section

/-- Step correspondence for every pair in the compiler relation. -/
theorem correspondence_steps
    (processType : PactType)
    (hAdmissible : AdmissibleType processType) :
    TypeAutomatonStepCorrespondence processType := by
  -- Paper: take Γ = ∅ and obtain H-current, H-cycle, and H-menus together.
  have hWellFormed := typeWellFormedIn_nil_of_admissible hAdmissible
  obtain ⟨hCurrent, _hCycle, _hMenus⟩ :=
    correspondence_simultaneous [] processType hWellFormed
  constructor
  · intro residual residual' state env label offers hRelated hSemantic
    rcases offers with ⟨current, future⟩
    -- Paper, forward: H-current supplies the edge and its related target.
    obtain ⟨state', edgeFuture, hEdge, hTargetRelated⟩ :=
      hCurrent.1 hRelated hSemantic
    refine ⟨state', ?_, hTargetRelated⟩
    -- Paper: H-law and H-menus force the edge's future field to be `future`.
    have hFuture : edgeFuture = future := by
      by_cases hTock : label = TypeLabel.tock
      · have hSemanticFuture : future = ∅ :=
          (uniform_offer_law_clock hSemantic.2 hTock).2
        have hEdgeFuture : edgeFuture = ∅ :=
          helper_h15_edge_future_offers_agree_of_tock
            hRelated hTargetRelated hEdge hTock
        exact hEdgeFuture.trans hSemanticFuture.symm
      · have hSemanticFuture :
            future = typeFutureOffers residual' \ current :=
          hSemantic.2.future_eq_sdiff_of_label_ne_tock hTock
        have hEdgeFuture :
            edgeFuture = typeFutureOffers residual' \ current :=
          helper_h15_edge_future_offers_agree_of_not_tock
            hRelated hTargetRelated hEdge hTock
        exact hEdgeFuture.trans hSemanticFuture.symm
    simpa [hFuture] using hEdge
  · intro residual state state' env label offers hRelated hEdge
    rcases offers with ⟨current, future⟩
    -- Paper, backward: H-current reconstructs a step and a related target.
    obtain ⟨residual', semanticFuture, hSemantic, hTargetRelated⟩ :=
      hCurrent.2 hRelated hEdge
    refine ⟨residual', ?_, hTargetRelated⟩
    -- Paper: the same H-law/H-menus equation identifies the semantic future.
    have hFuture : semanticFuture = future := by
      by_cases hTock : label = TypeLabel.tock
      · have hSemanticFuture : semanticFuture = ∅ :=
          (uniform_offer_law_clock hSemantic.2 hTock).2
        have hEdgeFuture : future = ∅ :=
          helper_h15_edge_future_offers_agree_of_tock
            hRelated hTargetRelated hEdge hTock
        exact hSemanticFuture.trans hEdgeFuture.symm
      · have hSemanticFuture :
            semanticFuture = typeFutureOffers residual' \ current :=
          hSemantic.2.future_eq_sdiff_of_label_ne_tock hTock
        have hEdgeFuture :
            future = typeFutureOffers residual' \ current :=
          helper_h15_edge_future_offers_agree_of_not_tock
            hRelated hTargetRelated hEdge hTock
        exact hSemanticFuture.trans hEdgeFuture.symm
    simpa [hFuture] using hSemantic

end

end Pact
