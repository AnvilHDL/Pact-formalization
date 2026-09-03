import Anvilpp.PactTypes.Syntax.LiveEquivalenceLemmas
import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Automata.SyncEdgesDefs

/-!
The parent alphabet of a parallel node declares every non-interface action of
either child and no interface action at all.
-/

namespace Pact

namespace PactTypeAlphabet

/-- The parent alphabet of a compatible parallel node is the merge of its two
children with the interface hidden. -/
theorem parent_eq_mergeHidden
    {parent left right : PactTypeAlphabet} {interface : Interface}
    (hCompatible : ParallelCompatible parent left right interface) :
    parent = mergeHidden left right interface :=
  (PactTypeAlphabet.mergeHidden_eq_parent hCompatible).symm

/- The remaining lemmas of this file reconstructed the parent alphabet and the
completion environment from the two children.  Both are now given directly by
the parallel rules, so they have no consumer. -/

-- theorem parent_no_interface
--     {parent left right : PactTypeAlphabet} {leftType rightType : PactType}
--     {interface : Interface}
--     (hCompatible : ParallelCompatible parent left right leftType rightType
--       interface)
--     (hOwn : Disjoint (PactType.MessageActions leftType)
--       (PactType.MessageActions rightType))
--     {action : BareMessage} (hAction : action ∈ parent.actions)
--     (hInterface : action.1 ∈ interface) : False := by
--   classical
--   have hLeftUses : action ∈ PactType.MessageActions rightType := by
--     by_contra hNot
--     have : action ∈ (hideInterface left interface).actions := by
--       rw [← hCompatible.parent_left]
--       exact Finset.mem_sdiff.mpr ⟨hAction, hNot⟩
--     simp only [hideInterface, Finset.mem_filter] at this
--     exact this.2 hInterface
--   have hRightUses : action ∈ PactType.MessageActions leftType := by
--     by_contra hNot
--     have : action ∈ (hideInterface right interface).actions := by
--       rw [← hCompatible.parent_right]
--       exact Finset.mem_sdiff.mpr ⟨hAction, hNot⟩
--     simp only [hideInterface, Finset.mem_filter] at this
--     exact this.2 hInterface
--   exact (Finset.disjoint_left.mp hOwn hRightUses) hLeftUses

-- /-- Every non-interface action of the right child is declared by the parent. -/
-- theorem child_noninterface_subset_right
--     {parent left right : PactTypeAlphabet} {leftType rightType : PactType}
--     {interface : Interface}
--     (hCompatible : ParallelCompatible parent left right leftType rightType
--       interface) :
--     (hideInterface right interface).actions ⊆ parent.actions := by
--   rw [← hCompatible.parent_right]
--   exact fun _ hMem => (Finset.mem_sdiff.mp hMem).1

-- /-- The mirror for the left child. -/
-- theorem child_noninterface_subset_left
--     {parent left right : PactTypeAlphabet} {leftType rightType : PactType}
--     {interface : Interface}
--     (hCompatible : ParallelCompatible parent left right leftType rightType
--       interface) :
--     (hideInterface left interface).actions ⊆ parent.actions := by
--   rw [← hCompatible.parent_left]
--   exact fun _ hMem => (Finset.mem_sdiff.mp hMem).1

-- /-- A compatible parent alphabet *is* the merge of its children's.  Both
-- inclusions come from the two `ParallelCompatible` equations, with parallel
-- message ownership ruling out the one case where neither applies. -/
-- theorem parent_eq_mergeHidden
--     {parent left right : PactTypeAlphabet} {leftType rightType : PactType}
--     {interface : Interface}
--     (hCompatible : ParallelCompatible parent left right leftType rightType
--       interface)
--     (hOwn : Disjoint (PactType.MessageActions leftType)
--       (PactType.MessageActions rightType)) :
--     parent = mergeHidden left right interface := by
--   classical
--   have hExt : parent.actions = (mergeHidden left right interface).actions := by
--     apply Finset.ext
--     intro action
--     constructor
--     · intro hMem
--       have hNotBoth : action ∉ PactType.MessageActions rightType ∨
--           action ∉ PactType.MessageActions leftType := by
--         by_cases hRight : action ∈ PactType.MessageActions rightType
--         · exact Or.inr fun hLeft =>
--             (Finset.disjoint_left.mp hOwn hLeft) hRight
--         · exact Or.inl hRight
--       simp only [mergeHidden, Finset.mem_filter, Finset.mem_union]
--       rcases hNotBoth with hNot | hNot
--       · have : action ∈ (hideInterface left interface).actions := by
--           rw [← hCompatible.parent_left]
--           exact Finset.mem_sdiff.mpr ⟨hMem, hNot⟩
--         simp only [hideInterface, Finset.mem_filter] at this
--         exact ⟨Or.inl this.1, this.2⟩
--       · have : action ∈ (hideInterface right interface).actions := by
--           rw [← hCompatible.parent_right]
--           exact Finset.mem_sdiff.mpr ⟨hMem, hNot⟩
--         simp only [hideInterface, Finset.mem_filter] at this
--         exact ⟨Or.inr this.1, this.2⟩
--     · intro hMem
--       simp only [mergeHidden, Finset.mem_filter, Finset.mem_union] at hMem
--       rcases hMem.1 with hLeft | hRight
--       · have : action ∈ (hideInterface left interface).actions := by
--           simp only [hideInterface, Finset.mem_filter]
--           exact ⟨hLeft, hMem.2⟩
--         rw [← hCompatible.parent_left] at this
--         exact (Finset.mem_sdiff.mp this).1
--       · have : action ∈ (hideInterface right interface).actions := by
--           simp only [hideInterface, Finset.mem_filter]
--           exact ⟨hRight, hMem.2⟩
--         rw [← hCompatible.parent_right] at this
--         exact (Finset.mem_sdiff.mp this).1
--   cases parent
--   simp only [mergeHidden] at hExt ⊢
--   exact congrArg PactTypeAlphabet.mk hExt

-- end PactTypeAlphabet

-- /-- With empty sibling offers, the semantic local environment of a parallel
-- child is exactly the compiler's projection of the outer environment.  This is
-- what lets the survivor-entry families step the written child. -/
-- theorem completionLocalEnv_eq_projection
--     {outer siblingEnv localEnv : TypeEnvironment} {interface : Interface}
--     {localType : PactType} {parentAlphabet : PactTypeAlphabet}
--     (hOuter : outer.WellFormed parentAlphabet)
--     (h : LocalTypeOfferEnvironment outer interface localType siblingEnv ∅ ∅
--       localEnv) :
--     localEnv = projectAutomatonEnvironment localType.alphabet outer := by
--   classical
--   cases h with
--   | clock _ _ _ _ hClock =>
--       simp [projectAutomatonEnvironment, hClock]
--   | ordinary _ _ _ _ _ _ hOuterClock _ hLocalClock hImmediate hFuture =>
--       have hDisjoint : outer.immediate ∩ outer.future = ∅ :=
--         hOuter.2.1 hOuterClock
--       have hImm : localEnv.immediate =
--           projectTypeEnvironmentOffers localType.alphabet outer.immediate := by
--         rw [hImmediate]
--         simp [restrictTypeOffers]
--       have hFut : localEnv.future =
--           projectTypeEnvironmentOffers localType.alphabet outer.future := by
--         rw [hFuture, hImm]
--         simp only [restrictTypeOffers, Finset.filter_empty, Finset.union_empty]
--         apply Finset.sdiff_eq_self_of_disjoint
--         rw [Finset.disjoint_left]
--         intro action hFutMem hImmMem
--         simp only [projectTypeEnvironmentOffers, Finset.mem_filter]
--           at hFutMem hImmMem
--         have : action ∈ outer.immediate ∩ outer.future :=
--           Finset.mem_inter.mpr ⟨hImmMem.1, hFutMem.1⟩
--         rw [hDisjoint] at this
--         exact absurd this (Finset.notMem_empty action)
--       rw [projectAutomatonEnvironment, if_neg (by simp [hOuterClock])]
--       obtain ⟨imm, fut, clk⟩ := localEnv
--       simp only at hImm hFut hLocalClock
--       simp [hImm, hFut, hLocalClock]

-- /-- Offers projected out of a merged parent carry no interface message. -/
-- theorem mergeHidden_offers_no_interface
--     {left right : PactTypeAlphabet} {interface : Interface}
--     {offers : Finset BareMessage}
--     (hSub : offers ⊆ (PactTypeAlphabet.mergeHidden left right
--       interface).actions.image typeNeed)
--     {offer : BareMessage} (hOffer : offer ∈ offers) : offer.1 ∉ interface := by
--   classical
--   obtain ⟨action, hAction, rfl⟩ := Finset.mem_image.mp (hSub hOffer)
--   simp only [PactTypeAlphabet.mergeHidden, Finset.mem_filter] at hAction
--   exact hAction.2

-- /-- Two alphabets that agree outside an interface project a need-set the same
-- way, provided the offers themselves carry no interface message.  This is what
-- makes the two parallel children of live-equivalent nodes see the same local
-- environment: their alphabets can differ only on interface actions neither body
-- uses, and a merged parent supplies no interface need. -/
-- theorem projectTypeEnvironmentOffers_eq_of_hideInterface_eq
--     {left left' : PactTypeAlphabet} {interface : Interface}
--     {offers : Finset BareMessage}
--     (hHide : PactTypeAlphabet.hideInterface left interface =
--       PactTypeAlphabet.hideInterface left' interface)
--     (hNoInterface : ∀ offer ∈ offers, offer.1 ∉ interface) :
--     projectTypeEnvironmentOffers left offers =
--       projectTypeEnvironmentOffers left' offers := by
--   classical
--   have key : ∀ (a b : PactTypeAlphabet),
--       PactTypeAlphabet.hideInterface a interface =
--         PactTypeAlphabet.hideInterface b interface →
--       ∀ offer ∈ offers, offer ∈ a.actions.image typeNeed →
--         offer ∈ b.actions.image typeNeed := by
--     intro a b hEq offer hOffer hMem
--     obtain ⟨action, hAction, hNeed⟩ := Finset.mem_image.mp hMem
--     have hFst : action.1 = offer.1 := by rw [← hNeed]; rfl
--     have hNotIface : action.1 ∉ interface := by
--       rw [hFst]; exact hNoInterface offer hOffer
--     have : action ∈ (PactTypeAlphabet.hideInterface a interface).actions := by
--       simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
--       exact ⟨hAction, hNotIface⟩
--     rw [hEq] at this
--     simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter] at this
--     exact Finset.mem_image.mpr ⟨action, this.1, hNeed⟩
--   apply Finset.ext
--   intro offer
--   simp only [projectTypeEnvironmentOffers, Finset.mem_filter]
--   constructor
--   · rintro ⟨hOffer, hMem⟩
--     exact ⟨hOffer, key left left' hHide offer hOffer hMem⟩
--   · rintro ⟨hOffer, hMem⟩
--     exact ⟨hOffer, key left' left hHide.symm offer hOffer hMem⟩


end PactTypeAlphabet

end Pact
