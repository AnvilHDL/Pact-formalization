import Anvilpp.PactTypes.NewCorrespondence.Helpers.RecursionFoundations

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

def binaryChoiceRelationShape
    (signature : TypeAlphabet) (whole left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (whole, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership (buildRelationSet left (compileType signature left))
        entry.1 q) ∨
    (∃ q, entry.2 = .child 1 q ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q)

/-- Proves every related pair for a type compiled through `buildChoiceAutomaton` has the binary-choice shape, given that the root's two semantic rules are each uniquely determined by their label. -/
lemma relationMembership_binaryChoice_cases
    (signature : TypeAlphabet) (whole left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (hFuelRight : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (hRootLeft : ∀ env offers target,
      DecoratedTypeTransition env whole selectionLeft offers target → target = left)
    (hRootRight : ∀ env offers target,
      DecoratedTypeTransition env whole selectionRight offers target → target = right)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership (buildRelationSet whole (compileType signature whole))
        residual state) :
    binaryChoiceRelationShape signature whole left right (residual, state) := by
  have hInit : (compileType signature whole).initial = TypeAutomatonState.root := by
    show (compileTypeFuel signature (typeCompilationFuel whole) whole).initial =
      TypeAutomatonState.root
    rw [hWhole]
    simp [buildChoiceAutomaton, finishAutomatonFragment]
  sorry
  -- refine buildRelationSet_preserves whole (compileType signature whole)
  --   (binaryChoiceRelationShape signature whole left right)
  --   (by
  --     show binaryChoiceRelationShape signature whole left right
  --       (whole, (compileType signature whole).initial)
  --     rw [hInit]; exact Or.inl rfl)
  --   (by
  --     intro entry hEntry successor hSuccessor
  --     rcases relationSuccessors_mem_cases (compileType signature whole) entry successor
  --       hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature whole
  --       (show (compileType signature whole).HasEdge edge.source edge.symbol.environment
  --         edge.symbol.label edge.symbol.offers edge.target from hEdgeMem)
  --     have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature whole
  --       edge.source edge.target edge.symbol.environment edge.symbol.label
  --       edge.symbol.offers hSymbolMem).mp hEdgeMem
  --     rw [hWhole] at hResolved
  --     obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
  --       hPTarget⟩ := hResolved
  --     rcases hEntry with hRoot | ⟨q, hStateEq, hMem⟩ | ⟨q, hStateEq, hMem⟩
  --     · -- root case: entry represents `whole` itself
  --       have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
  --         rw [hPSource, hSource, hRoot]
  --       simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
  --         Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
  --         childPendingEdges, Finset.mem_image] at hPendingMem
  --       rcases hPendingMem with (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
  --         ⟨environment, _, hEq | hEq⟩
  --       · exfalso; rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · exfalso; rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · subst hEq
  --         simp only [childState] at hPLabel hPTarget
  --         have hLabelEq : edge.symbol.label = selectionLeft := by
  --           injection hPLabel.symm
  --         have hEntry1 : entry.1 = whole := by rw [hRoot]
  --         have hResidualEq : successor.1 = left := by
  --           apply hRootLeft edge.symbol.environment edge.symbol.offers
  --           rw [← hEntry1, ← hLabelEq]; exact hStep
  --         have hTargetEq : successor.2 = .child 0
  --             (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel left)
  --           left).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial left (compileType signature left)⟩)
  --       · subst hEq
  --         simp only [childState] at hPLabel hPTarget
  --         have hLabelEq : edge.symbol.label = selectionRight := by
  --           injection hPLabel.symm
  --         have hEntry1 : entry.1 = whole := by rw [hRoot]
  --         have hResidualEq : successor.1 = right := by
  --           apply hRootRight edge.symbol.environment edge.symbol.offers
  --           rw [← hEntry1, ← hLabelEq]; exact hStep
  --         have hTargetEq : successor.2 = .child 1
  --             (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel right)
  --           right).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial right (compileType signature right)⟩)
  --     · -- left-child case: entry is already related to `q` inside `left`'s own relation
  --       have hChildSource : pendingEdge.source = .child 0 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildChoiceAutomaton_outgoing_left signature
  --           (compileTypeFuel signature (typeCompilationFuel left) left)
  --           (compileTypeFuel signature (typeCompilationFuel right) right)
  --           selectionLeft selectionRight q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature left).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature left q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_binaryChoice_left signature left right
  --                 selectionLeft selectionRight whole hWhole hFuelLeft t hStateMem]
  --       have hTargetEq : successor.2 = .child 0 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique left (compileType signature left)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inl ⟨childEdge.target, hTargetEq, hInnerMem⟩)
  --     · -- right-child case: symmetric to the left-child case
  --       have hChildSource : pendingEdge.source = .child 1 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildChoiceAutomaton_outgoing_right signature
  --           (compileTypeFuel signature (typeCompilationFuel left) left)
  --           (compileTypeFuel signature (typeCompilationFuel right) right)
  --           selectionLeft selectionRight q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature right).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature right q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r
  --                 hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_binaryChoice_right signature left right
  --                 selectionLeft selectionRight whole hWhole hFuelRight t hStateMem]
  --       have hTargetEq : successor.2 = .child 1 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique right (compileType signature right)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inr ⟨childEdge.target, hTargetEq, hInnerMem⟩))
  --   (residual, state) hRelated

/-- Proves every related choice pair has the binary-choice shape. -/
lemma relationMembership_choice_cases
    (signature : TypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.choice left right)
          (compileType signature (.choice left right)))
        residual state) :
    binaryChoiceRelationShape signature (.choice left right) left right
      (residual, state) := by
  have hFuelEq : typeCompilationFuel (.choice left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.choice left right))
        (.choice left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent := by
    rw [hFuelEq]
    show buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent =
      buildChoiceAutomaton signature (compileTypeFuel signature
        (typeCompilationFuel left) left) (compileTypeFuel signature
        (typeCompilationFuel right) right) TypeLabel.silent TypeLabel.silent
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
  have hFuelLeft :
      typeCompilationFuel left + 1 ≤ typeCompilationFuel (.choice left right) := by
    simp only [typeCompilationFuel]; omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel (.choice left right) := by
    simp only [typeCompilationFuel]; omega
  have hInit : (compileType signature (.choice left right)).initial =
      TypeAutomatonState.root := by
    show (compileTypeFuel signature (typeCompilationFuel (.choice left right))
      (.choice left right)).initial = TypeAutomatonState.root
    rw [hWhole]
    simp [buildChoiceAutomaton, finishAutomatonFragment]
  sorry
  -- refine buildRelationSet_preserves (.choice left right)
  --   (compileType signature (.choice left right))
  --   (binaryChoiceRelationShape signature (.choice left right) left right)
  --   (by
  --     show binaryChoiceRelationShape signature (.choice left right) left right
  --       (.choice left right, (compileType signature (.choice left right)).initial)
  --     rw [hInit]; exact Or.inl rfl)
  --   (by
  --     intro entry hEntry successor hSuccessor
  --     rcases relationSuccessors_mem_cases (compileType signature (.choice left right))
  --       entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
  --     have hSymbolMem := compileType_hasEdge_symbol_mem signature (.choice left right)
  --       (show (compileType signature (.choice left right)).HasEdge edge.source
  --         edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
  --         from hEdgeMem)
  --     have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
  --       (.choice left right) edge.source edge.target edge.symbol.environment
  --       edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
  --     rw [hWhole] at hResolved
  --     obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
  --       hPTarget⟩ := hResolved
  --     rcases hEntry with hRoot | ⟨q, hStateEq, hMem⟩ | ⟨q, hStateEq, hMem⟩
  --     · -- root case: entry represents `τ1 + τ2` itself, and H15 pins each
  --       -- root edge's own future offers to the child it actually selects.
  --       have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
  --         rw [hPSource, hSource, hRoot]
  --       simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
  --         Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
  --         childPendingEdges, Finset.mem_image] at hPendingMem
  --       rcases hPendingMem with (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
  --         ⟨environment, hEnvironment, hEq | hEq⟩
  --       · exfalso; rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · exfalso; rw [← hEq] at hRootSource
  --         simp [childPendingEdge, childState] at hRootSource
  --       · subst hEq
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by
  --           injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current = ∅ := hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future = typeFutureOffers left := by
  --           rw [← hPFuture, computeFutureOf_binaryChoice_left signature left right
  --             TypeLabel.silent TypeLabel.silent (.choice left right) hWhole hFuelLeft
  --             (compileTypeFuel signature (typeCompilationFuel left) left).initial
  --             (compileTypeFuel_initial_mem signature (typeCompilationFuel left) left le_rfl),
  --             Finset.sdiff_empty]
  --           show computeFutureOf signature left (compileType signature left).initial =
  --             typeFutureOffers left
  --           exact helper_h15_future_offers_agree signature
  --             (buildRelationSet_initial left (compileType signature left))
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk ∅
  --             (typeFutureOffers left) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hWF : edge.symbol.environment.WellFormed :=
  --           localEnvironment_wellFormed signature (hPEnv ▸ hEnvironment)
  --         have hEntry1 : entry.1 = .choice left right := by rw [hRoot]
  --         have hResidualEq : successor.1 = left := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             ⟨TypeTransition.choice_left edge.symbol.environment left right hWF,
  --               TypeOffers.choice_left edge.symbol.environment left right hWF⟩
  --         have hTargetEq : successor.2 = .child 0
  --             (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel left)
  --           left).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial left (compileType signature left)⟩)
  --       · subst hEq
  --         simp only [childState] at hPLabel hPCurrent hPFuture hPTarget
  --         have hLabelEq : edge.symbol.label = TypeLabel.silent := by
  --           injection hPLabel.symm
  --         have hCurrentEq : edge.symbol.offers.current = ∅ := hPCurrent.symm
  --         have hFutureEq : edge.symbol.offers.future = typeFutureOffers right := by
  --           rw [← hPFuture, computeFutureOf_binaryChoice_right signature left right
  --             TypeLabel.silent TypeLabel.silent (.choice left right) hWhole hFuelRight
  --             (compileTypeFuel signature (typeCompilationFuel right) right).initial
  --             (compileTypeFuel_initial_mem signature (typeCompilationFuel right) right le_rfl),
  --             Finset.sdiff_empty]
  --           show computeFutureOf signature right (compileType signature right).initial =
  --             typeFutureOffers right
  --           exact helper_h15_future_offers_agree signature
  --             (buildRelationSet_initial right (compileType signature right))
  --         have hOffersEq : edge.symbol.offers = TypeOfferSummary.mk ∅
  --             (typeFutureOffers right) := by
  --           rw [show edge.symbol.offers = TypeOfferSummary.mk
  --             edge.symbol.offers.current edge.symbol.offers.future from rfl,
  --             hCurrentEq, hFutureEq]
  --         have hWF : edge.symbol.environment.WellFormed :=
  --           localEnvironment_wellFormed signature (hPEnv ▸ hEnvironment)
  --         have hEntry1 : entry.1 = .choice left right := by rw [hRoot]
  --         have hResidualEq : successor.1 = right := by
  --           rw [hEntry1] at hStep
  --           rw [hLabelEq, hOffersEq] at hStep
  --           exact decoratedTypeTransition_target_unique hStep
  --             ⟨TypeTransition.choice_right edge.symbol.environment left right hWF,
  --               TypeOffers.choice_right edge.symbol.environment left right hWF⟩
  --         have hTargetEq : successor.2 = .child 1
  --             (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
  --           rw [hTarget, ← hPTarget]
  --         exact Or.inr (Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel right)
  --           right).initial, hTargetEq, hResidualEq ▸
  --             buildRelationSet_initial right (compileType signature right)⟩)
  --     · -- left-child case: entry is already related to `q` inside `left`'s own relation
  --       have hChildSource : pendingEdge.source = .child 0 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildChoiceAutomaton_outgoing_left signature
  --           (compileTypeFuel signature (typeCompilationFuel left) left)
  --           (compileTypeFuel signature (typeCompilationFuel right) right)
  --           TypeLabel.silent TypeLabel.silent q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature left).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature left q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_binaryChoice_left signature left right
  --                 TypeLabel.silent TypeLabel.silent (.choice left right) hWhole hFuelLeft
  --                 t hStateMem]
  --       have hTargetEq : successor.2 = .child 0 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique left (compileType signature left)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inl ⟨childEdge.target, hTargetEq, hInnerMem⟩)
  --     · -- right-child case: symmetric to the left-child case
  --       have hChildSource : pendingEdge.source = .child 1 q := by
  --         rw [hPSource, hSource, hStateEq]
  --       obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
  --         (buildChoiceAutomaton_outgoing_right signature
  --           (compileTypeFuel signature (typeCompilationFuel left) left)
  --           (compileTypeFuel signature (typeCompilationFuel right) right)
  --           TypeLabel.silent TypeLabel.silent q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
  --       have hInnerEdgeMem : (compileType signature right).HasEdge q
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers
  --           childEdge.target := by
  --         rw [compileType_hasEdge_iff_hasResolvedEdge signature right q childEdge.target
  --           edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
  --         refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  --         · rw [← hPEnv, hChildEdgeEq]; rfl
  --         · rw [← hPLabel, hChildEdgeEq]; rfl
  --         · rw [← hPCurrent, hChildEdgeEq]; rfl
  --         · rw [← hPFuture, hChildEdgeEq]
  --           cases hSpec : childEdge.future with
  --           | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
  --           | «at» t r =>
  --               have hStateMem := compileTypeFuel_futureTargetsInStates signature
  --                 (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r
  --                 hSpec
  --               simp only [childPendingEdge, childFutureSpec, hSpec, childState]
  --               rw [computeFutureOf_binaryChoice_right signature left right
  --                 TypeLabel.silent TypeLabel.silent (.choice left right) hWhole hFuelRight
  --                 t hStateMem]
  --       have hTargetEq : successor.2 = .child 1 childEdge.target := by
  --         rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
  --       have hInnerMem :=
  --         relationMembership_of_step_edge_unique right (compileType signature right)
  --           hMem hInnerEdgeMem hStep
  --           (fun target hTargetStep =>
  --             decoratedTypeTransition_target_unique hTargetStep hStep)
  --       exact Or.inr (Or.inr ⟨childEdge.target, hTargetEq, hInnerMem⟩))
  --   (residual, state) hRelated

/-- Proves every related fair-choice pair has the binary-choice shape. -/
lemma relationMembership_fairChoice_cases
    (signature : TypeAlphabet) (bid : BranchId) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.fairChoice bid left right)
          (compileType signature (.fairChoice bid left right)))
        residual state) :
    binaryChoiceRelationShape signature (.fairChoice bid left right) left
      right (residual, state) := by
  have hFuelEq : typeCompilationFuel (.fairChoice bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.fairChoice bid left right))
        (.fairChoice bid left right) =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    show buildChoiceAutomaton signature
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel signature
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton signature (compileTypeFuel signature
        (typeCompilationFuel left) left) (compileTypeFuel signature
        (typeCompilationFuel right) right) (TypeLabel.fair bid true)
        (TypeLabel.fair bid false)
    rw [compileTypeFuel_eq_of_sufficient signature left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient signature right (le_max_right _ _) le_rfl]
  refine relationMembership_binaryChoice_cases signature (.fairChoice bid left right)
    left right (TypeLabel.fair bid true) (TypeLabel.fair bid false) hWhole
    (by simp only [typeCompilationFuel]; omega)
    (by simp only [typeCompilationFuel]; omega)
    (by
      rintro env offers target ⟨hTrans, -⟩
      generalize hLabelEq : TypeLabel.fair bid true = actualLabel at hTrans
      cases hTrans <;> simp_all [TypeLabel.fair, Finset.ext_iff])
    (by
      rintro env offers target ⟨hTrans, -⟩
      generalize hLabelEq : TypeLabel.fair bid false = actualLabel at hTrans
      cases hTrans <;> simp_all [TypeLabel.fair, Finset.ext_iff])
    hRelated


end

end Pact
