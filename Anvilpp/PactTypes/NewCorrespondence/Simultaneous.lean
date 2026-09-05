import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Recursion
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.RecursionMenus
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.MarkerCorrespondence
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Sequence
import Anvilpp.PactTypes.NewCorrespondence.Simultaneous.Parallel

/-!
The retained same-cycle lemmas, parallel product menus, and the paper's
simultaneous induction for current-offer correspondence and menu agreement.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

open PendingAutomaton

/-- The done state is not a product state. -/
theorem stateProductInfo_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    stateProductInfo (.par alphabet left right interface) .final = none := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuel, stateProductInfoFuel]

set_option maxHeartbeats 1000000 in
/-- The menu at a product state is the hidden union of the component menus. -/
theorem computeFutureOf_par_pair (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (q1 q2 : TypeAutomatonState)
    (hSurvLeft : ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left)
          left).states,
        (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
        PendingAutomaton).futureReachable q1,
      computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right)
          right).states,
        (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
        PendingAutomaton).futureReachable q2,
      computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hq1 : q1 ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hq2 : q2 ∈ (compileTypeFuel (typeCompilationFuel right) right).states) :
    computeFutureOf (.par alphabet left right interface) (.pair q1 q2) =
      hideTypeOffers interface
        (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
  classical
  set N : Nat := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hN
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      N + 1 := by simp only [hN, typeCompilationFuel]; omega
  have hLeftLe : typeCompilationFuel left ≤ N := le_max_left _ _
  have hRightLe : typeCompilationFuel right ≤ N := le_max_right _ _
  have hParentClosed := compiledMenuGraphFuel_referencesClosed (N + 1)
    (.par alphabet left right interface)
    (by simp only [TypeCompilationFuelSufficient, hFuel]; exact le_rfl)
    (by simp only [PactType.OfferBranchesDisjoint]
        exact ⟨hLeftDisjoint, hRightDisjoint⟩)
  simp only [compiledMenuGraphFuel] at hParentClosed
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set parent : PendingAutomaton :=
    { states := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).edges } with hParent
  set parentMenu : FiniteMenuGraph := parent.withMenuDependencies
    (compileTypeMenuLinksFuel
      (min (N + 1) (typeCompilationFuel (.par alphabet left right interface)))
      (.par alphabet left right interface)) with hParentMenu
  -- the product term of the pair state itself is the whole right-hand side
  have hInfo : stateProductInfo (PactType.par alphabet left right interface)
      (.pair q1 q2) = some (interface, left, right, q1, q2) := by
    simp only [stateProductInfo, hFuel, stateProductInfoFuel]
  have hMenuLeft : computeFutureOfFuel N left q1 = computeFutureOf left q1 :=
    computeFutureOfFuel_eq_of_sufficient left q1 hLeftLe le_rfl
  have hMenuRight : computeFutureOfFuel N right q2 = computeFutureOf right q2 :=
    computeFutureOfFuel_eq_of_sufficient right q2 hRightLe le_rfl
  have hRhsSubset :
      hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) ⊆
        (parentMenu.futureReachable (.pair q1 q2)).biUnion fun visited =>
          parent.offersAt visited ∪
            match stateProductInfo (PactType.par alphabet left right interface)
              visited with
            | some (i, l, r, a, b) =>
                hideTypeOffers i (computeFutureOfFuel N l a ∪
                  computeFutureOfFuel N r b)
            | none => ∅ := by
    intro action hAction
    refine Finset.mem_biUnion.mpr ⟨.pair q1 q2,
      FiniteMenuGraph.mem_futureReachable_self parentMenu _, ?_⟩
    refine Finset.mem_union_right _ ?_
    rw [hInfo]
    simpa [hMenuLeft, hMenuRight] using hAction
  -- the filter by the parent alphabet is exactly the interface hiding
  have hBound : computeFutureOf left q1 ∪ computeFutureOf right q2 ⊆
      left.alphabet.actions ∪ right.alphabet.actions :=
    Finset.union_subset_union (computeFutureOf_subset_alphabet left q1)
      (computeFutureOf_subset_alphabet right q2)
  have hFilterEq :
      (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
          (fun action => action ∈
            (PactType.par alphabet left right interface).alphabet.actions) =
        hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
    have := filter_parent_actions_eq_hide hCompatible
      (computeFutureOf left q1 ∪ computeFutureOf right q2) hBound
    simpa [PactType.alphabet] using this
  apply Finset.Subset.antisymm
  · intro action hAction
    obtain ⟨hRaw, hGate⟩ := Finset.mem_filter.mp hAction
    obtain ⟨visited, hVisited, hContrib⟩ := Finset.mem_biUnion.mp hRaw
    -- every visited state contributes within the two component menus
    have hInMenus : action ∈
        computeFutureOf left q1 ∪ computeFutureOf right q2 := by
      have hParEq : compileTypeFuel (N + 1)
          (PactType.par alphabet left right interface) =
          buildParallelAutomaton alphabet left.alphabet right.alphabet interface
            (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N (left.reannotate alphabet))
            (compileTypeFuel N (right.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel right))
              (right.reannotate alphabet)) := by
        simp only [compileTypeFuel]
      have hLeftFragEq : compileTypeFuel N left =
          compileTypeFuel (typeCompilationFuel left) left :=
        compileTypeFuel_eq_of_sufficient left hLeftLe le_rfl
      have hRightFragEq : compileTypeFuel N right =
          compileTypeFuel (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient right hRightLe le_rfl
      have hReach := buildParallelAutomaton_pair_futureReachable_subset
        alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N (left.reannotate alphabet))
        (compileTypeFuel N (right.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left))
          (left.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel right))
          (right.reannotate alphabet))
        (compileTypeFuel_futureTargetsAreEdgeTargets N left)
        (compileTypeFuel_explicitOnlyAtAccepting N left)
        (compileTypeFuel_futureTargetsAreEdgeTargets N right)
        (compileTypeFuel_explicitOnlyAtAccepting N right)
        (compileTypeFuel_referencesClosed N left hLeftLe hLeftDisjoint)
        (compileTypeFuel_referencesClosed N right hRightLe hRightDisjoint)
        (compileTypeMenuLinksFuel
          (min (N + 1) (typeCompilationFuel (.par alphabet left right interface)))
          (.par alphabet left right interface))
        (compileTypeMenuLinksFuel_pair _ _)
        (compileTypeMenuLinksFuel_final _ _)
        (by rw [← hParEq]; exact hParentClosed)
        q1 q2 (by rw [hLeftFragEq]; exact hq1) (by rw [hRightFragEq]; exact hq2)
      rw [hParentMenu, hParent, hParEq] at hVisited
      have hCases := hReach hVisited
      rcases Finset.mem_insert.mp hCases with rfl | hRest
      · -- the done state offers nothing and carries no product term
        exfalso
        rw [hParent, hParEq] at hContrib
        have hShape := buildParallelAutomaton_final_edge_shape
          alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N (left.reannotate alphabet))
          (compileTypeFuel N (right.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left))
            (left.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel right))
            (right.reannotate alphabet))
        have hInfoFinal : stateProductInfo
            (PactType.par alphabet left right interface)
            TypeAutomatonState.final = none := by
          simp only [stateProductInfo, hFuel, stateProductInfoFuel]
        rw [hInfoFinal, Finset.union_empty] at hContrib
        rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hContrib
        obtain ⟨edge, hEdge, hMem⟩ := hContrib
        obtain ⟨hCurrent, hFuture⟩ := hShape edge
          (Finset.mem_filter.mp hEdge).1 (Finset.mem_filter.mp hEdge).2
        rw [hCurrent, hFuture] at hMem
        simp at hMem
      rcases Finset.mem_union.mp hRest with hPairOrRight | hLeftSurv
      · rcases Finset.mem_union.mp hPairOrRight with hPair | hRightSurv
        · -- a reachable product state: its own product term, bounded by
          -- same-cycle monotonicity in each component
          obtain ⟨pair, hPairMem, rfl⟩ := Finset.mem_image.mp hPair
          obtain ⟨hFst, hSnd⟩ := Finset.mem_product.mp hPairMem
          have hInfoPair : stateProductInfo
              (PactType.par alphabet left right interface)
              (.pair pair.1 pair.2) =
              some (interface, left, right, pair.1, pair.2) := by
            simp only [stateProductInfo, hFuel, stateProductInfoFuel]
          rw [hInfoPair] at hContrib
          rcases Finset.mem_union.mp hContrib with hOffers | hProduct
          · -- a synchronized product edge publishes only component offers
            rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hOffers
            obtain ⟨edge, hEdgeMem, hActionMem⟩ := hOffers
            have hEdge := (Finset.mem_filter.mp hEdgeMem).1
            have hSrc := (Finset.mem_filter.mp hEdgeMem).2
            rw [hParent, hParEq] at hEdge
            have hShapes := buildParallelAutomaton_outgoing_pair
              alphabet left.alphabet right.alphabet interface
              (compileTypeFuel N left) (compileTypeFuel N right)
              (compileTypeFuel N (left.reannotate alphabet))
              (compileTypeFuel N (right.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
              (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
              (computeFutureOfFuel (min N (typeCompilationFuel left))
                (left.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel right))
                (right.reannotate alphabet))
              pair.1 pair.2 edge hEdge hSrc
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            -- the gate transfers to each child by parallel compatibility
            have hGateLeft : action ∈ left.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_left hCompatible
                (by simpa [PactType.alphabet] using hGate)
            have hGateRight : action ∈ right.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_right hCompatible
                (by simpa [PactType.alphabet] using hGate)
            -- a component edge's own current sits in that component's menu
            have hLeftIn : ∀ (le : AutomatonFragmentEdge),
                le ∈ resolveAutomatonEdgesWith (compileTypeFuel N left)
                  (computeFutureOfFuel (min N (typeCompilationFuel left)) left) →
                le.source = pair.1 → le.label.semantic ≠ TypeLabel.tock →
                action ∈ le.current →
                action ∈ computeFutureOf left pair.1 := by
              intro le hle hlSrc hlTock hIn
              refine offersAt_subset_computeFutureOf left pair.1 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateLeft⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hle
              obtain ⟨orig, hOrig, rfl⟩ := hle
              simp only at hlSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hlSrc⟩, ?_⟩
              · rw [← hLeftFragEq]; exact hOrig
              · simp only at hlTock
                rw [if_neg hlTock]
                exact Finset.mem_union_left _ hIn
            have hRightIn : ∀ (re : AutomatonFragmentEdge),
                re ∈ resolveAutomatonEdgesWith (compileTypeFuel N right)
                  (computeFutureOfFuel (min N (typeCompilationFuel right))
                    right) →
                re.source = pair.2 → re.label.semantic ≠ TypeLabel.tock →
                action ∈ re.current →
                action ∈ computeFutureOf right pair.2 := by
              intro re hre hrSrc hrTock hIn
              refine offersAt_subset_computeFutureOf right pair.2 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateRight⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hre
              obtain ⟨orig, hOrig, rfl⟩ := hre
              simp only at hrSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hrSrc⟩, ?_⟩
              · rw [← hRightFragEq]; exact hOrig
              · simp only at hrTock
                rw [if_neg hrTock]
                exact Finset.mem_union_left _ hIn
            -- every product edge resolves its future by pointer, never by an
            -- explicit menu, so `offersAt` reads only its current offers
            have hFutureShape : ∀ e ∈ (compileTypeFuel (N + 1)
                (PactType.par alphabet left right interface)).edges,
                e.source = TypeAutomatonState.pair pair.1 pair.2 →
                e.label.semantic ≠ TypeLabel.tock →
                ∀ offers, e.future ≠ FutureSpec.explicit offers := by
              intro e he heSrc hTock offers hExplicit
              have hAcc := compileTypeFuel_explicitOnlyAtAccepting (N + 1)
                (PactType.par alphabet left right interface) e he hTock offers
                hExplicit
              -- the parallel fragment accepts only at the done state, whose
              -- source cannot be the product state we are visiting
              rw [hParEq] at hAcc he
              simp only [buildParallelAutomaton, finishAutomatonFragment,
                Finset.mem_singleton] at hAcc
              obtain ⟨-, hFuture⟩ := buildParallelAutomaton_final_edge_shape
                alphabet left.alphabet right.alphabet interface
                (compileTypeFuel N left) (compileTypeFuel N right)
                (compileTypeFuel N (left.reannotate alphabet))
                (compileTypeFuel N (right.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
                (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
                (computeFutureOfFuel (min N (typeCompilationFuel left))
                  (left.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel right))
                  (right.reannotate alphabet)) e he hAcc
              rw [hFuture] at hExplicit
              injection hExplicit with hOffers
              rw [heSrc] at hAcc
              simp at hAcc
            -- a contributing edge is never a clock edge
            by_cases hEdgeTock : edge.label.semantic = TypeLabel.tock
            · rw [if_pos hEdgeTock] at hActionMem; simp at hActionMem
            rw [if_neg hEdgeTock] at hActionMem
            rcases hShapes with
              ⟨le, hle, re, hre, hlSrc, hrSrc, hCur, hLbl, hSync, -⟩ |
              ⟨re, hre, hrSrc, hCur, hLbl, -⟩ | ⟨le, hle, hlSrc, hCur, hLbl, -⟩
            · -- a synchronized product edge hides a union of component offers
              obtain ⟨hlTock, hrTock⟩ := sync_components_not_tock
                left.alphabet right.alphabet interface hSync
                (by rw [← hLbl]; exact hEdgeTock)
              have hRaw : action ∈ le.current ∪ re.current := by
                rcases Finset.mem_union.mp hActionMem with hCur' | hFut
                · rw [hCur] at hCur'
                  exact (Finset.mem_filter.mp hCur').1
                · cases hFut' : edge.future with
                  | explicit offers =>
                      exact absurd hFut' (hFutureShape edge (by
                        rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                  | «at» s r => rw [hFut'] at hFut; simp at hFut
              rcases Finset.mem_union.mp hRaw with hL | hR
              · exact Finset.mem_union_left _
                  (hLeftMono (hLeftIn le hle hlSrc hlTock hL))
              · exact Finset.mem_union_right _
                  (hRightMono (hRightIn re hre hrSrc hrTock hR))
            · -- the left component completed: only right offers appear
              refine Finset.mem_union_right _ (hRightMono
                (hRightIn re hre hrSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
            · -- the right component completed: only left offers appear
              refine Finset.mem_union_left _ (hLeftMono
                (hLeftIn le hle hlSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
          · -- the product term at a reachable pair
            simp only at hProduct
            rw [computeFutureOfFuel_eq_of_sufficient left pair.1 hLeftLe le_rfl,
              computeFutureOfFuel_eq_of_sufficient right pair.2 hRightLe
                le_rfl] at hProduct
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            have hHide : hideTypeOffers interface
                (computeFutureOf left pair.1 ∪ computeFutureOf right pair.2) ⊆
                computeFutureOf left pair.1 ∪ computeFutureOf right pair.2 := by
              intro a ha
              exact (Finset.mem_filter.mp ha).1
            exact Finset.union_subset_union hLeftMono hRightMono
              (hHide hProduct)
        · -- a right survivor sub-reach: collapses to the re-signed component's
          -- menu by the survivor transport, then to the component's own
          obtain ⟨tEntry, htEntry, hInSub⟩ := Finset.mem_biUnion.mp hRightSurv
          refine Finset.mem_union_right _ ?_
          obtain ⟨htEntry, htAcc⟩ := Finset.mem_filter.mp htEntry
          have hCollapse : action ∈
              computeFutureOf (right.reannotate alphabet) tEntry := by
            rw [← computeFutureOf_par_survivorRight alphabet left right
              interface hLeftDisjoint hRightDisjoint tEntry
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).1,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                  _ q2 _ (by rw [hRightFragEq]; exact hq2)
                  (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                    hRightDisjoint s hs)) htEntry)
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).2.2,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact htAcc)]
            rw [computeFutureOf, hFuel, computeFutureOfFuel]
            refine Finset.mem_filter.mpr ⟨?_, hGate⟩
            refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
            rw [hParEq]
            exact hInSub
          have htStates : tEntry ∈
              (compileTypeFuel (typeCompilationFuel right) right).states := by
            rw [← hRightFragEq]
            exact (PendingAutomaton.futureReachable_subset_of_reference_closed
              _ q2 _ (by rw [hRightFragEq]; exact hq2)
              (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                hRightDisjoint s hs)) htEntry
          have hMono := computeFutureOf_mono_of_futureReachable right
            hRightDisjoint hq2
            (by rw [← hRightFragEq]; exact htEntry)
          exact hMono (hSurvRight tEntry (by rw [← hRightFragEq]; exact htEntry)
            hCollapse)
      · -- the mirror, for a left survivor sub-reach
        obtain ⟨sEntry, hsEntry, hInSub⟩ := Finset.mem_biUnion.mp hLeftSurv
        obtain ⟨hsEntry, hsAcc⟩ := Finset.mem_filter.mp hsEntry
        refine Finset.mem_union_left _ ?_
        have hCollapse : action ∈
            computeFutureOf (left.reannotate alphabet) sEntry := by
          rw [← computeFutureOf_par_survivorLeft alphabet left right
            interface hLeftDisjoint hRightDisjoint sEntry
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).1,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                _ q1 _ (by rw [hLeftFragEq]; exact hq1)
                (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
                  hLeftDisjoint s hs)) hsEntry)
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).2.2,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact hsAcc)]
          rw [computeFutureOf, hFuel, computeFutureOfFuel]
          refine Finset.mem_filter.mpr ⟨?_, hGate⟩
          refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
          rw [hParEq]
          exact hInSub
        have hsStates : sEntry ∈
            (compileTypeFuel (typeCompilationFuel left) left).states := by
          rw [← hLeftFragEq]
          exact (PendingAutomaton.futureReachable_subset_of_reference_closed
            _ q1 _ (by rw [hLeftFragEq]; exact hq1)
            (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
              hLeftDisjoint s hs)) hsEntry
        have hMono := computeFutureOf_mono_of_futureReachable left
          hLeftDisjoint hq1
          (by rw [← hLeftFragEq]; exact hsEntry)
        exact hMono (hSurvLeft sEntry (by rw [← hLeftFragEq]; exact hsEntry)
          hCollapse)
    rw [← hFilterEq]
    exact Finset.mem_filter.mpr ⟨hInMenus, hGate⟩
  · intro action hAction
    have hMemRaw := hRhsSubset hAction
    refine Finset.mem_filter.mpr ⟨hMemRaw, ?_⟩
    have hIn : action ∈ (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
        (fun a => a ∈ (PactType.par alphabet left right interface).alphabet.actions) := by
      rw [hFilterEq]; exact hAction
    exact (Finset.mem_filter.mp hIn).2

/-- The completed product state offers nothing: its only edges are the idle
self-loops, which carry no current offers and name no further state. -/
theorem computeFutureOf_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    computeFutureOf (.par alphabet left right interface) .final = ∅ := by
  classical
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hShape : ∀ edge ∈ (compileTypeFuel
      (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
      (PactType.par alphabet left right interface)).edges,
      edge.source = TypeAutomatonState.final →
      edge.current = ∅ ∧ edge.future = .explicit ∅ := by
    intro edge hEdge hSource
    simp only [compileTypeFuel] at hEdge
    exact buildParallelAutomaton_final_edge_shape _ _ _ _ _ _ _ _ _ _ _ _
      edge hEdge hSource
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set pending : PendingAutomaton :=
    { states := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).edges }
    with hPendingDef
  have hRefs : pending.referencedStates TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro target hTarget
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hTargetMem⟩ := hTarget
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    rw [(hShape edge hMem hSource).2] at hTargetMem
    simp at hTargetMem
  have hOffers : pending.offersAt TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro action hAction
    rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
    obtain ⟨edge, hEdge, hActionMem⟩ := hAction
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    obtain ⟨hCurrent, hFuture⟩ := hShape edge hMem hSource
    rw [hCurrent, hFuture] at hActionMem
    simp at hActionMem
  rw [FiniteMenuGraph.futureReachable_eq_singleton_of_referencedStates_eq_empty
      _ .final (by simp only [PendingAutomaton.withMenuDependencies, hRefs,
        compileTypeMenuLinksFuel_final, Finset.union_empty])]
  simp only [Finset.singleton_biUnion, hOffers,
    stateProductInfo_par_final alphabet left right interface,
    Finset.empty_union, Finset.filter_empty]

/-- H-menus at a parallel product, by the four families of related states. -/
theorem futureOffersAgree_par (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (hSurvLeft : ∀ (rho : PactType) (q1 : TypeAutomatonState),
      relationMembership (buildRelationSet left (compileType left)) rho q1 →
      ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left) left).states,
          (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
          PendingAutomaton).futureReachable q1,
        computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ (rho : PactType) (q2 : TypeAutomatonState),
      relationMembership (buildRelationSet right (compileType right)) rho q2 →
      ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right) right).states,
          (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
          PendingAutomaton).futureReachable q2,
        computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right)
    (hLeftResign : FutureOffersAgree (left.reannotate alphabet))
    (hRightResign : FutureOffersAgree (right.reannotate alphabet)) :
    FutureOffersAgree (.par alphabet left right interface) := by
  classical
  intro residual state hRelated
  rcases relationMembership_par_cases alphabet left right interface hRelated with
    ⟨q1, q2, rL, rR, hEq, hL, hR⟩ | ⟨q1, rL, hEq, hL, hNotAcc⟩ |
      ⟨q2, rR, hEq, hR, hNotAcc⟩ | hFinal
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_pair alphabet left right interface hLeftDisjoint
        hRightDisjoint hCompatible q1 q2 (hSurvLeft rL q1 hL) (hSurvRight rR q2 hR)
        (relationMembership_state_mem left _ q1 hLeftDisjoint hL)
        (relationMembership_state_mem right _ q2 hRightDisjoint hR),
      hLeft hL, hRight hR, typeFutureOffers_parallel]
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorLeft alphabet left right interface
        hLeftDisjoint hRightDisjoint q1
        (relationMembership_state_mem (left.reannotate alphabet) _ q1
          (reannotate_offerBranchesDisjoint left alphabet hLeftDisjoint) hL)
        hNotAcc]
    exact hLeftResign hL
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorRight alphabet left right interface
        hLeftDisjoint hRightDisjoint q2
        (relationMembership_state_mem (right.reannotate alphabet) _ q2
          (reannotate_offerBranchesDisjoint right alphabet hRightDisjoint) hR)
        hNotAcc]
    exact hRightResign hR
  · injection hFinal with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_final alphabet left right interface]
    simp only [typeFutureOffers, typeFutureOffersFuel]

#print axioms stateProductInfo_par_final
#print axioms buildParallelAutomaton_final_edge_shape
#print axioms computeFutureOf_par_final

/-- The paper's survivor bullet: the re-signed component's menu at a state is
bounded by the component's own.  The state is related by Lemma 4.5's
reachability clause, the re-signing transport moves that witness across, and
`<dead-declarations-inert>` equates the two menus. -/
theorem survivorMenuBound (component : PactType) (target : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (hTargetWF : target.WellFormed)
    (hNoInterface : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces component)
    (hComponent : FutureOffersAgree component)
    (hResign : FutureOffersAgree (component.reannotate target))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) residual state)
    (hActions : target.actions ⊆ residual.alphabet.actions)
    (hResidualWF : residual.AlphabetWellFormed) :
    computeFutureOf (component.reannotate target) state ⊆
      computeFutureOf component state := by
  classical
  obtain ⟨theta, hThetaRelated, hLive⟩ :=
    survivorTransport_all component bound hWF target hTargetWF hNoInterface
      residual state hRelated
  rw [hResign hThetaRelated, hComponent hRelated,
    ← PactType.liveEq_preserves_futOff hLive]
  exact typeFutureOffers_reannotate_subset residual target hResidualWF hActions

/-- In a marker-free component, the current-offer hypothesis makes every
same-cycle successor of a related state related. -/
theorem futureReachable_related_of_currentOffer
    (component : PactType) (hDisjoint : component.OfferBranchesDisjoint)
    (hNoMarker : ∀ name,
      (compileTypeFuel (typeCompilationFuel component) component).NoMarkerFor name)
    (hCurrent : CurrentOfferCorrespondence component)
    {rho : PactType} {q : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) rho q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      ∃ theta, relationMembership
        (buildRelationSet component (compileType component)) theta s := by
  classical
  let fragment := compileTypeFuel (typeCompilationFuel component) component
  let pending : PendingAutomaton := ⟨fragment.states, fragment.edges⟩
  let allowed := fragment.states.filter fun s => ∃ theta,
    relationMembership (buildRelationSet component (compileType component)) theta s
  have hStep : ∀ s ∈ allowed, pending.referencedStates s ⊆ allowed := by
    intro s hs t ht
    obtain ⟨_, theta, hTheta⟩ := Finset.mem_filter.mp hs
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at ht
    obtain ⟨edge, hEdge, hRef⟩ := ht
    obtain ⟨hEdgeMem, hSource⟩ := Finset.mem_filter.mp hEdge
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hRef
      simp at hRef
    rw [if_neg hTock] at hRef
    have hTarget : t = edge.target := by
      cases hFuture : edge.future with
      | explicit offers => rw [hFuture] at hRef; simp at hRef
      | «at» target removed =>
          rw [hFuture] at hRef
          simp only [Finset.mem_singleton] at hRef
          rw [hRef, compileTypeFuel_futureTargetsAreEdgeTargets
            (typeCompilationFuel component) component edge hEdgeMem
            target removed hFuture]
    subst t
    cases hLabel : edge.label with
    | «variable» name => exact False.elim (hNoMarker name edge hEdgeMem hLabel)
    | visible label =>
        have hPublic : (compileType component).HasEdge s edge.environment label
            ⟨edge.current, match edge.future with
              | .explicit offers => offers
              | .at target removed => computeFutureOf component target \ removed⟩
            edge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge]
          exact ⟨edge, hEdgeMem, hSource, rfl, hLabel, rfl, rfl, rfl⟩
        obtain ⟨theta', _, _, hTheta'⟩ := hCurrent.2 hTheta hPublic
        exact Finset.mem_filter.mpr
          ⟨compileTypeFuel_edgeTargetsInStates _ _ le_rfl hDisjoint edge hEdgeMem,
            theta', hTheta'⟩
  have hSeed : q ∈ allowed := Finset.mem_filter.mpr
    ⟨relationMembership_state_mem component rho q hDisjoint hRelated, rho, hRelated⟩
  intro s hs
  exact (Finset.mem_filter.mp
    (PendingAutomaton.futureReachable_subset_of_reference_closed pending q
      allowed hSeed hStep hs)).2

/-- At a related child state, narrowing to the parent alphabet cannot add
survivor offers. The current-offer hypothesis supplies the reachable witnesses;
the two menu hypotheses and survivor transport compare their menus. -/
theorem survivorMenuBound_par
    (component : PactType) (alphabet : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (hAlphabet : alphabet.WellFormed)
    (hSubset : alphabet.actions ⊆ component.alphabet.actions)
    (hTail : ∀ name, component.TailOccurrences name False)
    (hCurrent : CurrentOfferCorrespondence component)
    (hMenu : FutureOffersAgree component)
    (hResignMenu : FutureOffersAgree (component.reannotate alphabet))
    (rho : PactType) (q : TypeAutomatonState)
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) rho q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      computeFutureOf (component.reannotate alphabet) s ⊆
        computeFutureOf component s := by
  have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hWF
  obtain ⟨hA, _, _, _, _, hTR, _, _, _, _, _, _, hIS, hIAS, _⟩ := id hWF
  intro s hs
  obtain ⟨theta, hTheta⟩ := futureReachable_related_of_currentOffer component
    hDisjoint (fun name => compileTypeFuel_noMarkerFor name _ _ (hTail name))
    hCurrent hRelated s hs
  apply survivorMenuBound component alphabet bound hWF hAlphabet
    (fun action hAction => PactType.InterfaceAlphabetScoped.avoids hIAS
      action (hSubset hAction)) hMenu hResignMenu hTheta
  · rw [relationMembership_alphabet_eq_of_wellFormed component theta s hA hTheta]
    exact hSubset
  · exact relationMembership_alphabetWellFormed
      committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
      component theta s hA hIS hIAS hTR hDisjoint hTheta

/-- The parallel menu case uses only well-formedness and the lower-rank
current-offer and menu hypotheses. -/
theorem futureOffersAgree_par_of_typeWF
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    {bound : List String}
    (hWF : TypeWellFormedIn bound (.par alphabet left right interface))
    (hLeftCurrent : CurrentOfferCorrespondence left)
    (hRightCurrent : CurrentOfferCorrespondence right)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right)
    (hLeftResign : FutureOffersAgree (left.reannotate alphabet))
    (hRightResign : FutureOffersAgree (right.reannotate alphabet)) :
    FutureOffersAgree (.par alphabet left right interface) := by
  obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
  have hAlphabet : alphabet.WellFormed :=
    PactType.AlphabetWellFormed.alphabet_wellFormed hWF.1
  have hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface := by
    have h := hWF.1
    simp only [PactType.AlphabetWellFormed] at h
    exact h.2.1
  have hTail : ∀ name, left.TailOccurrences name False ∧
      right.TailOccurrences name False := by
    intro name
    simpa only [PactType.TailOccurrences] using hWF.2.2.2.1 name
  intro rho q hRelated
  exact futureOffersAgree_par alphabet left right interface
    (offerBranchesDisjoint_of_wellFormedIn hLeftWF)
    (offerBranchesDisjoint_of_wellFormedIn hRightWF) hCompatible
    (survivorMenuBound_par left alphabet bound hLeftWF hAlphabet
      (PactTypeAlphabet.parent_actions_subset_left hCompatible)
      (fun name => (hTail name).1) hLeftCurrent hLeft hLeftResign)
    (survivorMenuBound_par right alphabet bound hRightWF hAlphabet
      (PactTypeAlphabet.parent_actions_subset_right hCompatible)
      (fun name => (hTail name).2) hRightCurrent hRight hRightResign)
    hLeft hRight hLeftResign hRightResign hRelated

#print axioms futureReachable_related_of_currentOffer
#print axioms survivorMenuBound_par
#print axioms futureOffersAgree_par_of_typeWF

/-- The paper's two helpers, proved together by induction on `typeCompilationFuel`. -/
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      CurrentOfferCorrespondence processType ∧
        FutureOffersAgree processType := by
  intro bound processType
  induction hFuel : typeCompilationFuel processType
      using Nat.strong_induction_on generalizing bound processType with
  | _ n ih =>
    intro hWF
    cases processType with
    | skip alphabet =>
        exact ⟨currentOfferCorrespondence_skip alphabet,
          futureOffersAgree_skip alphabet⟩
    | var alphabet name =>
        exact ⟨currentOfferCorrespondence_var alphabet name,
          futureOffersAgree_var alphabet name⟩
    | message alphabet msg dir =>
        exact ⟨currentOfferCorrespondence_message alphabet msg dir,
          futureOffersAgree_message alphabet msg dir⟩
    | tock alphabet =>
        exact ⟨currentOfferCorrespondence_tock alphabet,
          futureOffersAgree_tock alphabet⟩
    | progress alphabet pid =>
        exact ⟨currentOfferCorrespondence_progress alphabet pid,
          futureOffersAgree_progress alphabet pid⟩
    | choice alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_choice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, ?_⟩
        · exact currentOfferCorrespondence_choice alphabet left right hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_choice alphabet left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2
    | fairChoice alphabet bid left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_fairChoice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, ?_⟩
        · exact currentOfferCorrespondence_fairChoice alphabet bid left right
            hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_fairChoice alphabet bid left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2
    | seq alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, ?_⟩
        · exact currentOfferCorrespondence_seq alphabet left right
            (fun hRel =>
              relationMembership_alphabetWellFormed
                committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
                left _ _ hLeftWF.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.1
                (offerBranchesDisjoint_of_ownership left
                  hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                hRel)
            hLeft.1 hRight.1
        · apply futureOffersAgree_seq alphabet left right
            (offerBranchesDisjoint_of_ownership left
              hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2 hRight.2 hLeft.1 hLeftWF
          intro name
          have hTail := hWF.2.2.2.1 name
          simp only [PactType.TailOccurrences] at hTail
          exact hTail.1
    | par alphabet left right interface =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeftResignFuel :
            typeCompilationFuel (left.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hLeftFuel
        have hRightResignFuel :
            typeCompilationFuel (right.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hRightFuel
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        obtain ⟨hLeftResignWF, hRightResignWF⟩ := typeWellFormedIn_survivor hWF
        have hLeftResign :=
          ih _ hLeftResignFuel bound (left.reannotate alphabet) rfl hLeftResignWF
        have hRightResign :=
          ih _ hRightResignFuel bound (right.reannotate alphabet) rfl
            hRightResignWF
        refine ⟨?_, ?_⟩
        · exact currentOfferCorrespondence_par_of_typeWF hWF hLeft.1 hRight.1
            hLeftResign.1 hRightResign.1 hLeft.2 hRight.2
        · exact futureOffersAgree_par_of_typeWF hWF hLeft.1 hRight.1
            hLeft.2 hRight.2 hLeftResign.2 hRightResign.2
    | recur alphabet name body =>
        have hBodyWF := typeWellFormedIn_recur hWF
        have hBodyFuel : typeCompilationFuel body < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBody := ih _ hBodyFuel (name :: bound) body rfl hBodyWF
        refine ⟨?_, ?_⟩
        · exact currentOfferCorrespondence_recur_of_typeWF alphabet name body
            hWF hBody.1
        · intro residual state hRelated
          have hAlphabet : body.alphabet = alphabet := by
            have h := hWF.1
            simp only [PactType.AlphabetWellFormed] at h
            exact h.2.1
          have hDisjoint := offerBranchesDisjoint_of_wellFormedIn hBodyWF
          have hTail := hBodyWF.2.2.2.1
          rcases relationMembership_recur_cases alphabet name body hRelated with
            hRoot | ⟨q, rho, hPair, hChildRelated⟩
          · cases hRoot
            -- Paper: the fresh root reads the body-entry menu.
            exact futureOffersAgree_recur_root alphabet name body hAlphabet
              hDisjoint hTail hBody.1 hBody.2
          · cases hPair
            -- Paper: installed backedges add the body menu at marker-reachable states.
            rw [computeFutureOf_recur_child_eq alphabet name body hAlphabet
              hDisjoint hTail hBody.1 hBody.2 hChildRelated]
            let replacement := PactType.recur alphabet name body
            let fuel := max (sizeOf rho + 1) (sizeOf (rho.replaceVar name replacement) + 1)
            have hRhoFuel : sizeOf rho + 1 ≤ fuel := le_max_left _ _
            have hReplacedFuel : sizeOf (rho.replaceVar name replacement) + 1 ≤ fuel :=
              le_max_right _ _
            have hRhoTail := relationMembership_tailOccurrences body rho q name True
              hBodyWF.2.2.2.2.2.1 (hTail name) hChildRelated
            have hSyntax : typeFutureOffers (rho.replaceVar name replacement) =
                typeFutureOffers rho ∪
                  if menuReachesVarFuel name replacement.CanCompleteDeclared fuel rho
                  then typeFutureOffers body else ∅ := by
              -- Paper: substitution contributes V exactly when the syntax test b_X holds.
              rw [← typeFutureOffersFuel_eq_typeFutureOffers _ fuel hReplacedFuel,
                typeFutureOffersFuel_replaceVar name replacement fuel rho hReplacedFuel,
                typeFutureOffersFuelSubst_split name _ _ fuel rho (by omega) hRhoTail,
                typeFutureOffersFuelSubst_empty name _ fuel rho (by omega) hRhoTail,
                typeFutureOffersFuel_eq_typeFutureOffers rho fuel hRhoFuel]
              rw [typeFutureOffers_recur]
            rw [hSyntax]
            have hMarker :
                (∃ reached ∈ (compiledMenuGraphFuel (typeCompilationFuel body) body).futureReachable q,
                  MarkerSource (compileTypeFuel (typeCompilationFuel body) body) name reached) ↔
                menuReachesVarFuel name replacement.CanCompleteDeclared fuel rho = true := by
              -- Paper: M_X agrees with b_X by the smaller-rank marker induction.
              rw [menuReachesVarFuel_eq_menuReachesVar name replacement.CanCompleteDeclared
                fuel rho (by omega) hRhoTail]
              exact markerReachable_iff_menuReachesVar_of_current body (name :: bound) hBodyWF
                (fun child childBound hChildLt hChildWF =>
                  (ih _ (Nat.lt_trans hChildLt hBodyFuel) childBound child rfl hChildWF).1)
                name (List.mem_cons_self) hChildRelated
            simp only [hMarker]
    | xoffer alphabet elseType branches =>
        obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBranchFuel : ∀ entry ∈ branches,
            typeCompilationFuel entry.2 < n := by
          intro entry hEntry
          rw [← hFuel]
          simp only [typeCompilationFuel]
          have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry
            hEntry
          omega
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hBranch : ∀ entry ∈ branches,
            CurrentOfferCorrespondence entry.2 ∧
              FutureOffersAgree entry.2 :=
          fun entry hEntry =>
            ih _ (hBranchFuel entry hEntry) bound entry.2 rfl
              (hBranchWF entry hEntry)
        refine ⟨?_, ?_⟩
        · refine currentOfferCorrespondence_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (fun a t hMem =>
              offerBranchesDisjoint_of_ownership t
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun a t hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem]; rfl)
            hElse.1 (fun a t hMem => (hBranch (a, t) hMem).1)
        · exact futureOffersAgree_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.xoffer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun branch hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem)
            hElse.2 (fun branch hMem => (hBranch branch hMem).2)
    | offer alphabet elseType branches =>
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hGeneratedFuel : ∀ selected,
            typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
          intro selected
          rw [← hFuel, typeCompilationFuel_parallelTypeBranchesSelecting]
          simp only [typeCompilationFuel]
          omega
        obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hSelected : ∀ selected ∈ branches,
            CurrentOfferCorrespondence
                (parallelTypeBranchesSelecting alphabet selected branches) ∧
              FutureOffersAgree
                (parallelTypeBranchesSelecting alphabet selected branches) :=
          fun selected hMem =>
            ih _ (hGeneratedFuel selected) bound _ rfl (hSelectedWF selected hMem)
        refine ⟨?_, ?_⟩
        · refine currentOfferCorrespondence_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            ?_
            (fun selected hMem =>
              offerBranchesDisjoint_of_ownership _
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun selected hMem => by
              rw [parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem]; rfl)
            hElse.1 (fun selected hMem => (hSelected selected hMem).1)
          · intro branch hMem
            have hWholeDisjoint :=
              offerBranchesDisjoint_of_ownership
                (.offer alphabet elseType branches)
                hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
                hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp only [PactType.OfferBranchesDisjoint] at hWholeDisjoint
            exact offerBranchesDisjoint_of_mem_branch hWholeDisjoint.2.2 hMem
        · refine futureOffersAgree_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.offer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun selected hMem =>
              parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem)
            ?_ hElse.2 (fun selected hMem => (hSelected selected hMem).2)
          -- The generated product's menu, from the raw branch bodies.  The gate
          -- is exactly the declaredness the syntax lemma needs.
          intro hGate selected hMem
          have h := hWF.1
          simp only [PactType.AlphabetWellFormed] at h
          exact typeFutureOffers_parallelTypeBranchesSelecting alphabet selected
            branches hGate
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).1)
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).2)


end

end Pact
