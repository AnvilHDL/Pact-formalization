import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.Parallel
import Anvilpp.PactTypes.Proofs.Correspondence.Simultaneous.CompletionFlag

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
        (compileTypeFuel_menuClosed N left hLeftLe hLeftDisjoint)
        (compileTypeFuel_menuClosed N right hRightLe hRightDisjoint)
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
        rw [hCurrent] at hMem
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
                exact hIn
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
                exact hIn
            /- Retired target-only field argument:
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
            -/
            -- a contributing edge is never a clock edge
            by_cases hEdgeTock : edge.label.semantic = TypeLabel.tock
            · rw [if_pos hEdgeTock] at hActionMem; simp at hActionMem
            rw [if_neg hEdgeTock] at hActionMem
            -- every product family publishes the hidden union of the two
            -- component currents, drawn from a `SyncEdges_I` witness
            obtain ⟨le, hle, re, hre, hlSrc, hrSrc, hCur, hLbl, hSync⟩ :
                ∃ le ∈ resolveAutomatonEdgesWith (compileTypeFuel N left)
                    (computeFutureOfFuel (min N (typeCompilationFuel left)) left),
                  ∃ re ∈ resolveAutomatonEdgesWith (compileTypeFuel N right)
                    (computeFutureOfFuel (min N (typeCompilationFuel right))
                      right),
                    le.source = pair.1 ∧ re.source = pair.2 ∧
                      edge.current =
                        hideOffers interface (le.current ∪ re.current) ∧
                      edge.label = AutomatonConstructionLabel.combine interface
                        le.label re.label ∧
                      syncAutomatonEdges left.alphabet right.alphabet interface
                        le re := by
              rcases hShapes with
                ⟨le, hle, re, hre, h1, h2, h3, h4, h5, -⟩ |
                ⟨le, hle, re, hre, h1, h2, h3, h4, h5, -⟩ |
                ⟨le, hle, re, hre, h1, h2, h3, h4, h5, -⟩ <;>
                exact ⟨le, hle, re, hre, h1, h2, h3, h4, h5⟩
            obtain ⟨hlTock, hrTock⟩ := sync_components_not_tock
              left.alphabet right.alphabet interface hSync
              (by rw [← hLbl]; exact hEdgeTock)
            have hRaw : action ∈ le.current ∪ re.current := by
              rw [hCur] at hActionMem
              exact (Finset.mem_filter.mp hActionMem).1
            rcases Finset.mem_union.mp hRaw with hL | hR
            · exact Finset.mem_union_left _
                (hLeftMono (hLeftIn le hle hlSrc hlTock hL))
            · exact Finset.mem_union_right _
                (hRightMono (hRightIn re hre hrSrc hrTock hR))
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
                exact (PendingAutomaton.futureReachable_subset_of_menu_closed
                  _ q2 _ (by rw [hRightFragEq]; exact hq2)
                  (fun s hs => compileTypeFuel_menuClosed N right hRightLe
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
            exact (PendingAutomaton.futureReachable_subset_of_menu_closed
              _ q2 _ (by rw [hRightFragEq]; exact hq2)
              (fun s hs => compileTypeFuel_menuClosed N right hRightLe
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
              exact (PendingAutomaton.futureReachable_subset_of_menu_closed
                _ q1 _ (by rw [hLeftFragEq]; exact hq1)
                (fun s hs => compileTypeFuel_menuClosed N left hLeftLe
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
          exact (PendingAutomaton.futureReachable_subset_of_menu_closed
            _ q1 _ (by rw [hLeftFragEq]; exact hq1)
            (fun s hs => compileTypeFuel_menuClosed N left hLeftLe
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

/-- The completed product state offers nothing. Its idle edges return to itself. -/
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
  have hSteps : pending.menuStep .final ⊆ {TypeAutomatonState.final} := by
    intro target hTarget
    rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hTargetMem⟩ := hTarget
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    have hEdgeTarget : edge.target = .final := by
      simp only [hPendingDef, compileTypeFuel] at hMem
      exact buildParallelAutomaton_final_edge_target _ _ _ _ _ _ _ _ _ _ _ _
        edge hMem hSource
    split_ifs at hTargetMem with hClock
    · simp at hTargetMem
    · simpa only [hEdgeTarget] using hTargetMem
  have hReach : ∀ dependencies,
      menuDependencyTargets dependencies .final = ∅ →
      (pending.withMenuDependencies dependencies).futureReachable .final =
        {TypeAutomatonState.final} := by
    intro dependencies hDependencies
    apply Finset.Subset.antisymm
    · apply FiniteMenuGraph.futureReachable_subset_of_reference_closed
        _ .final {TypeAutomatonState.final} (Finset.mem_singleton_self _)
      intro state hState
      have hStateEq := Finset.mem_singleton.mp hState
      subst state
      simpa only [PendingAutomaton.withMenuDependencies, hDependencies,
        Finset.union_empty] using hSteps
    · exact Finset.singleton_subset_iff.mpr
        (FiniteMenuGraph.mem_futureReachable_self _ _)
  have hOffers : pending.offersAt TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro action hAction
    rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
    obtain ⟨edge, hEdge, hActionMem⟩ := hAction
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    obtain ⟨hCurrent, hFuture⟩ := hShape edge hMem hSource
    rw [hCurrent] at hActionMem
    simp at hActionMem
  rw [hReach _ (compileTypeMenuLinksFuel_final _ _)]
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
  have hStep : ∀ s ∈ allowed, pending.menuStep s ⊆ allowed := by
    intro s hs t ht
    obtain ⟨_, theta, hTheta⟩ := Finset.mem_filter.mp hs
    rw [PendingAutomaton.menuStep, Finset.mem_biUnion] at ht
    obtain ⟨edge, hEdge, hRef⟩ := ht
    obtain ⟨hEdgeMem, hSource⟩ := Finset.mem_filter.mp hEdge
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hRef
      simp at hRef
    rw [if_neg hTock] at hRef
    have hTarget : t = edge.target := by
      simpa only [Finset.mem_singleton] using hRef
    subst t
    cases hLabel : edge.label with
    | «variable» name => exact False.elim (hNoMarker name edge hEdgeMem hLabel)
    | visible label =>
        have hPublic : (compileType component).HasEdge s edge.environment label
            ⟨edge.current, resolveFutureSpec (computeFutureOf component) edge.future⟩
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
    (PendingAutomaton.futureReachable_subset_of_menu_closed pending q
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


end

end Pact
