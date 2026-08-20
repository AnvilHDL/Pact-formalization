import Anvilpp.PactSafetyHelpers
import Anvilpp.PactTypes.NewCorrespondence.CompileWFHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- States that a decorated type step's target residual is uniquely determined by its environment, source, label, and offers. -/
theorem decoratedTypeTransition_target_unique
    {env : TypeEnvironment} {source : PactType} {label : TypeLabel}
    {offers : TypeOfferSummary} {target target' : PactType}
    (hStep : DecoratedTypeTransition env source label offers target)
    (hStep' : DecoratedTypeTransition env source label offers target') :
    target = target' := by
  sorry

/-- Proves every sufficiently fuelled fragment is closed under its own future references. -/
theorem compileTypeFuel_futureTargetsInStates (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with (⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩) |
            ⟨environment, _, rfl⟩ <;> simp at hFuture
      | progress pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩ <;>
            simp at hFuture
      | tock =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_union,
            Finset.mem_image] at hEdge
          rcases hEdge with ⟨environment, _, rfl⟩ | ⟨environment, _, rfl⟩
          · split at hFuture <;> simp at hFuture
          · simp at hFuture
      | skip =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | var name =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment, Finset.mem_image]
            at hEdge
          obtain ⟨environment, _, rfl⟩ := hEdge
          simp at hFuture
      | recur name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) TypeLabel.silent
            TypeLabel.silent (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (TypeLabel.fair bid true)
            (TypeLabel.fair bid false) (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right) (ih left hLeft)
            (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par left right interface =>
          exact buildParallelAutomaton_futureTargetsInStates interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hBranches : ∀ entry ∈ branches,
              TypeCompilationFuelSufficient entry.2 fuel := by
            intro entry hEntry
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches entry hEntry
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            simp only [TypeCompilationFuelSufficient]
            omega
          have hResult := buildExclusiveOfferAutomaton_futureTargetsInStates
            signature branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
            (ih elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact ih original.2 (hBranches original hOriginal))
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [List.mem_map] at hEntry
              obtain ⟨original, hOriginal, rfl⟩ := hEntry
              exact compileTypeFuel_initial_mem signature fuel original.2
                (hBranches original hOriginal))
          simpa [compileTypeFuel] using hResult
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hSelected : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hResult :=
            buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
              signature branches (compileTypeFuel signature fuel elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches)))
              (ih elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact ih (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
              (compileTypeFuel_initial_mem signature fuel elseType hElse)
              (by
                intro entry hEntry
                simp only [List.mem_map] at hEntry
                obtain ⟨original, hOriginal, rfl⟩ := hEntry
                exact compileTypeFuel_initial_mem signature fuel
                  (parallelTypeBranchesSelecting original branches)
                  (hSelected original hOriginal))
          simpa [compileTypeFuel] using hResult

/-- Proves every sufficiently fuelled fragment's pending automaton is closed under its own future references. -/
theorem compileTypeFuel_referencesClosed (signature : TypeAlphabet)
    (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed :=
  PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

/-- States that `stateProductInfoFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem stateProductInfoFuel_eq_of_sufficient
    (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    stateProductInfoFuel leftFuel processType state =
      stateProductInfoFuel rightFuel processType state := by
  sorry

/-- States that `computeFutureOfFuel` stabilizes once its fuel is sufficient, mirroring `compileTypeFuel_eq_of_sufficient`. -/
theorem computeFutureOfFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType) (state : TypeAutomatonState)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    computeFutureOfFuel signature leftFuel processType state =
      computeFutureOfFuel signature rightFuel processType state := by
  sorry

/-- Proves a `.child 0`-tagged state's future menu, in a compiled binary choice, agrees with the left child's own. -/
theorem computeFutureOf_binaryChoice_left
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel left)
      left).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature left state := by
  sorry

/-- Proves a `.child 1`-tagged state's future menu, in a compiled binary choice, agrees with the right child's own. -/
theorem computeFutureOf_binaryChoice_right
    (signature : TypeAlphabet) (left right : PactType)
    (selectionLeft selectionRight : TypeLabel)
    (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildChoiceAutomaton signature
          (compileTypeFuel signature (typeCompilationFuel left) left)
          (compileTypeFuel signature (typeCompilationFuel right) right)
          selectionLeft selectionRight)
    (hFuel : typeCompilationFuel right + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel right)
      right).states) :
    computeFutureOf signature whole (.child 1 state) =
      computeFutureOf signature right state := by
  sorry

/-- States that substituting `μX.body` for `X` preserves and reflects a decorated step of a non-marker body residual. -/
theorem decoratedTypeTransition_replaceVar_iff
    (name : String) (body : PactType) (residual : PactType)
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    {target : PactType} :
    DecoratedTypeTransition env (residual.replaceVar name (.recur name body)) label
      offers target ↔
      ∃ residual', target = residual'.replaceVar name (.recur name body) ∧
        DecoratedTypeTransition env residual label offers residual' := by
  sorry

/-- States that a marker-labelled body edge is always sourced at a state representing the open variable it marks. -/
theorem compileTypeFuel_marker_represents_var
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {q : TypeAutomatonState} {residual : PactType}
    (hMem :
      relationMembership (buildRelationSet body (compileType signature body))
        residual q)
    {bodyEdge : PendingAutomatonEdge}
    (hBodyEdge : bodyEdge ∈
      (compileTypeFuel signature (typeCompilationFuel body) body).edges)
    (hSource : bodyEdge.source = q)
    (hMarkerLabel : bodyEdge.label = .variable name) :
    residual = .var name := by
  sorry

/-- Proves a `.child 0`-tagged state's future menu, in a compiled recursion, agrees with the body's own. -/
theorem computeFutureOf_recursion_child
    (signature : TypeAlphabet) (name : String) (body : PactType) (whole : PactType)
    (hWhole :
      compileTypeFuel signature (typeCompilationFuel whole) whole =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body))
    (hFuelBody : typeCompilationFuel body + 1 ≤ typeCompilationFuel whole)
    (state : TypeAutomatonState)
    (hState : state ∈ (compileTypeFuel signature (typeCompilationFuel body)
      body).states) :
    computeFutureOf signature whole (.child 0 state) =
      computeFutureOf signature body state := by
  sorry

/-- Defines the related-state shape for a compiled binary choice: the root represents `whole`, a tagged child state represents its own relation's residual. -/
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
  refine buildRelationSet_preserves whole (compileType signature whole)
    (binaryChoiceRelationShape signature whole left right)
    (by
      show binaryChoiceRelationShape signature whole left right
        (whole, (compileType signature whole).initial)
      rw [hInit]; exact Or.inl rfl)
    (by
      intro entry hEntry successor hSuccessor
      rcases relationSuccessors_mem_cases (compileType signature whole) entry successor
        hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature whole
        (show (compileType signature whole).HasEdge edge.source edge.symbol.environment
          edge.symbol.label edge.symbol.offers edge.target from hEdgeMem)
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature whole
        edge.source edge.target edge.symbol.environment edge.symbol.label
        edge.symbol.offers hSymbolMem).mp hEdgeMem
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      rcases hEntry with hRoot | ⟨q, hStateEq, hMem⟩ | ⟨q, hStateEq, hMem⟩
      · -- root case: entry represents `whole` itself
        have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
          rw [hPSource, hSource, hRoot]
        simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
          childPendingEdges, Finset.mem_image] at hPendingMem
        rcases hPendingMem with (⟨childEdge, _, hEq⟩ | ⟨childEdge, _, hEq⟩) |
          ⟨environment, _, hEq | hEq⟩
        · exfalso; rw [← hEq] at hRootSource
          simp [childPendingEdge, childState] at hRootSource
        · exfalso; rw [← hEq] at hRootSource
          simp [childPendingEdge, childState] at hRootSource
        · subst hEq
          simp only [childState] at hPLabel hPTarget
          have hLabelEq : edge.symbol.label = selectionLeft := by
            injection hPLabel.symm
          have hEntry1 : entry.1 = whole := by rw [hRoot]
          have hResidualEq : successor.1 = left := by
            apply hRootLeft edge.symbol.environment edge.symbol.offers
            rw [← hEntry1, ← hLabelEq]; exact hStep
          have hTargetEq : successor.2 = .child 0
              (compileTypeFuel signature (typeCompilationFuel left) left).initial := by
            rw [hTarget, ← hPTarget]
          exact Or.inr (Or.inl ⟨(compileTypeFuel signature (typeCompilationFuel left)
            left).initial, hTargetEq, hResidualEq ▸
              buildRelationSet_initial left (compileType signature left)⟩)
        · subst hEq
          simp only [childState] at hPLabel hPTarget
          have hLabelEq : edge.symbol.label = selectionRight := by
            injection hPLabel.symm
          have hEntry1 : entry.1 = whole := by rw [hRoot]
          have hResidualEq : successor.1 = right := by
            apply hRootRight edge.symbol.environment edge.symbol.offers
            rw [← hEntry1, ← hLabelEq]; exact hStep
          have hTargetEq : successor.2 = .child 1
              (compileTypeFuel signature (typeCompilationFuel right) right).initial := by
            rw [hTarget, ← hPTarget]
          exact Or.inr (Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel right)
            right).initial, hTargetEq, hResidualEq ▸
              buildRelationSet_initial right (compileType signature right)⟩)
      · -- left-child case: entry is already related to `q` inside `left`'s own relation
        have hChildSource : pendingEdge.source = .child 0 q := by
          rw [hPSource, hSource, hStateEq]
        obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_left signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
        have hInnerEdgeMem : (compileType signature left).HasEdge q
            edge.symbol.environment edge.symbol.label edge.symbol.offers
            childEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature left q childEdge.target
            edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
          refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
          · rw [← hPEnv, hChildEdgeEq]; rfl
          · rw [← hPLabel, hChildEdgeEq]; rfl
          · rw [← hPCurrent, hChildEdgeEq]; rfl
          · rw [← hPFuture, hChildEdgeEq]
            cases hSpec : childEdge.future with
            | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
            | «at» t r =>
                have hStateMem := compileTypeFuel_futureTargetsInStates signature
                  (typeCompilationFuel left) left le_rfl childEdge hChildEdgeMem t r hSpec
                simp only [childPendingEdge, childFutureSpec, hSpec, childState]
                rw [computeFutureOf_binaryChoice_left signature left right
                  selectionLeft selectionRight whole hWhole hFuelLeft t hStateMem]
        have hTargetEq : successor.2 = .child 0 childEdge.target := by
          rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
        have hInnerMem :=
          relationMembership_of_step_edge_unique left (compileType signature left)
            hMem hInnerEdgeMem hStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hStep)
        exact Or.inr (Or.inl ⟨childEdge.target, hTargetEq, hInnerMem⟩)
      · -- right-child case: symmetric to the left-child case
        have hChildSource : pendingEdge.source = .child 1 q := by
          rw [hPSource, hSource, hStateEq]
        obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
          (buildChoiceAutomaton_outgoing_right signature
            (compileTypeFuel signature (typeCompilationFuel left) left)
            (compileTypeFuel signature (typeCompilationFuel right) right)
            selectionLeft selectionRight q pendingEdge).mp ⟨hPendingMem, hChildSource⟩
        have hInnerEdgeMem : (compileType signature right).HasEdge q
            edge.symbol.environment edge.symbol.label edge.symbol.offers
            childEdge.target := by
          rw [compileType_hasEdge_iff_hasResolvedEdge signature right q childEdge.target
            edge.symbol.environment edge.symbol.label edge.symbol.offers hSymbolMem]
          refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
          · rw [← hPEnv, hChildEdgeEq]; rfl
          · rw [← hPLabel, hChildEdgeEq]; rfl
          · rw [← hPCurrent, hChildEdgeEq]; rfl
          · rw [← hPFuture, hChildEdgeEq]
            cases hSpec : childEdge.future with
            | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
            | «at» t r =>
                have hStateMem := compileTypeFuel_futureTargetsInStates signature
                  (typeCompilationFuel right) right le_rfl childEdge hChildEdgeMem t r
                  hSpec
                simp only [childPendingEdge, childFutureSpec, hSpec, childState]
                rw [computeFutureOf_binaryChoice_right signature left right
                  selectionLeft selectionRight whole hWhole hFuelRight t hStateMem]
        have hTargetEq : successor.2 = .child 1 childEdge.target := by
          rw [hTarget, ← hPTarget, hChildEdgeEq]; rfl
        have hInnerMem :=
          relationMembership_of_step_edge_unique right (compileType signature right)
            hMem hInnerEdgeMem hStep
            (fun target hTargetStep =>
              decoratedTypeTransition_target_unique hTargetStep hStep)
        exact Or.inr (Or.inr ⟨childEdge.target, hTargetEq, hInnerMem⟩))
    (residual, state) hRelated

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
  sorry

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

/-- Defines the related-state shape for a compiled sequence: a retained left state represents `ρ1 ; τ2`, a right state represents its own relation's residual. -/
def seqRelationShape
    (signature : TypeAlphabet) (left right : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 residualLeft, entry = (.seq residualLeft right, .child 0 q1) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1) ∨
    (∃ q2, entry.2 = .child 1 q2 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        entry.1 q2)

/-- Proves every related sequence pair has the sequence shape. -/
lemma relationMembership_seq_cases
    (signature : TypeAlphabet) (left right : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.seq left right)
          (compileType signature (.seq left right)))
        residual state) :
    seqRelationShape signature left right (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled parallel product: a product state represents the pointwise composition, or `skip` once both components finish. -/
def parRelationShape
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    (entry : PactType × TypeAutomatonState) : Prop :=
  (∃ q1 q2 residualLeft residualRight,
      entry = (.par residualLeft residualRight interface, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        residualLeft q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        residualRight q2) ∨
    (∃ q1 q2, entry = (.skip, .pair q1 q2) ∧
      relationMembership (buildRelationSet left (compileType signature left))
        .skip q1 ∧
      relationMembership (buildRelationSet right (compileType signature right))
        .skip q2)

/-- Proves every related parallel pair has the parallel shape. -/
lemma relationMembership_par_cases
    (signature : TypeAlphabet) (left right : PactType) (interface : Interface)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.par left right interface)
          (compileType signature (.par left right interface)))
        residual state) :
    parRelationShape signature left right interface (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled recursion: the root represents `μX.body`, a copied body state represents its residual substituted for `X`. -/
def recurRelationShape
    (signature : TypeAlphabet) (name : String) (body : PactType)
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.recur name body, TypeAutomatonState.root) ∨
    (∃ q residual,
      entry = (residual.replaceVar name (.recur name body), .child 0 q) ∧
      relationMembership (buildRelationSet body (compileType signature body))
        residual q)

/-- Proves every related recursion pair has the recursion shape. -/
lemma relationMembership_recur_cases
    (signature : TypeAlphabet) (name : String) (body : PactType)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.recur name body)
          (compileType signature (.recur name body)))
        residual state) :
    recurRelationShape signature name body (residual, state) := by
  have hFuelEq : typeCompilationFuel (.recur name body) = typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  have hWhole :
      compileTypeFuel signature (typeCompilationFuel (.recur name body))
        (.recur name body) =
        buildRecursionAutomaton signature name
          (compileTypeFuel signature (typeCompilationFuel body) body) := by
    rw [hFuelEq]
    show buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body) =
      buildRecursionAutomaton signature name
        (compileTypeFuel signature (typeCompilationFuel body) body)
    rfl
  have hInit : (compileType signature (.recur name body)).initial =
      TypeAutomatonState.root := by
    show (compileTypeFuel signature (typeCompilationFuel (.recur name body))
      (.recur name body)).initial = TypeAutomatonState.root
    rw [hWhole]
    simp [buildRecursionAutomaton, finishAutomatonFragment]
  refine buildRelationSet_preserves (.recur name body)
    (compileType signature (.recur name body))
    (recurRelationShape signature name body)
    (by
      show recurRelationShape signature name body
        (.recur name body, (compileType signature (.recur name body)).initial)
      rw [hInit]; exact Or.inl rfl)
    (by
      intro entry hEntry successor hSuccessor
      rcases relationSuccessors_mem_cases (compileType signature (.recur name body))
        entry successor hSuccessor with ⟨edge, hEdgeMem, hSource, hTarget, hStep⟩
      have hSymbolMem := compileType_hasEdge_symbol_mem signature (.recur name body)
        (show (compileType signature (.recur name body)).HasEdge edge.source
          edge.symbol.environment edge.symbol.label edge.symbol.offers edge.target
          from hEdgeMem)
      have hResolved := (compileType_hasEdge_iff_hasResolvedEdge signature
        (.recur name body) edge.source edge.target edge.symbol.environment
        edge.symbol.label edge.symbol.offers hSymbolMem).mp hEdgeMem
      rw [hWhole] at hResolved
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent, hPFuture,
        hPTarget⟩ := hResolved
      rcases hEntry with hRoot | ⟨q, bodyResidual, hEntryEq, hMem⟩
      · -- root case: entry represents `μX.body` itself
        have hRootSource : pendingEdge.source = TypeAutomatonState.root := by
          rw [hPSource, hSource, hRoot]
        simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_image] at hPendingMem
        rcases hPendingMem with ⟨environment, _, hEq⟩ | ⟨bodyEdge, _, hEq⟩
        · subst hEq
          simp only [childState] at hPTarget
          have hEntry1 : entry.1 = .recur name body := by rw [hRoot]
          rw [hEntry1] at hStep
          obtain ⟨hTrans, -⟩ := hStep
          generalize hTargetEq : successor.1 = actualTarget at hTrans
          generalize hLabelEq2 : edge.symbol.label = actualLabel at hTrans
          cases hTrans
          have hTargetEq2 : successor.2 = .child 0
              (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
            rw [hTarget, ← hPTarget]
          refine Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel body)
            body).initial, body, ?_,
            buildRelationSet_initial body (compileType signature body)⟩
          rw [← hTargetEq, ← hTargetEq2]
        · exfalso
          rw [← hEq] at hRootSource
          split at hRootSource <;> simp [childState] at hRootSource
      · -- child case: entry is already related to `q` inside `body`'s own relation
        have hEntry2 : entry.2 = .child 0 q := by rw [hEntryEq]
        have hChildSource : pendingEdge.source = .child 0 q := by
          rw [hPSource, hSource, hEntry2]
        simp only [buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
          Finset.mem_image] at hPendingMem
        rcases hPendingMem with ⟨environment, _, hEq⟩ | ⟨bodyEdge, hBodyEdgeMem, hEq⟩
        · exfalso
          rw [← hEq] at hChildSource
          simp at hChildSource
        · have hEntry1 : entry.1 = bodyResidual.replaceVar name (.recur name body) := by
            rw [hEntryEq]
          by_cases hMarker : bodyEdge.label = .variable name
          · -- marker edge: reduces to the same unfolding step as the root
            simp only [hMarker, if_true] at hEq
            subst hEq
            simp only [childState] at hPSource hPTarget
            have hSourceEq : bodyEdge.source = q := by
              simpa [childState] using hChildSource
            have hResidualEq : bodyResidual = .var name :=
              compileTypeFuel_marker_represents_var signature name body hMem
                hBodyEdgeMem hSourceEq hMarker
            rw [hEntry1, hResidualEq] at hStep
            simp only [PactType.replaceVar] at hStep
            obtain ⟨hTrans, -⟩ := hStep
            generalize hTargetEq : successor.1 = actualTarget at hTrans
            generalize hLabelEq2 : edge.symbol.label = actualLabel at hTrans
            cases hTrans
            have hTargetEq2 : successor.2 = .child 0
                (compileTypeFuel signature (typeCompilationFuel body) body).initial := by
              rw [hTarget, ← hPTarget]
            refine Or.inr ⟨(compileTypeFuel signature (typeCompilationFuel body)
              body).initial, body, ?_,
              buildRelationSet_initial body (compileType signature body)⟩
            rw [← hTargetEq, ← hTargetEq2]
          · -- copied non-marker edge: bridges to body's own relation
            simp only [hMarker, if_false] at hEq
            subst hEq
            simp only [childState] at hPSource hPTarget
            have hSourceEq : bodyEdge.source = q := by
              simpa [childState] using hChildSource
            have hInnerEdgeMem : (compileType signature body).HasEdge q
                edge.symbol.environment edge.symbol.label edge.symbol.offers
                bodyEdge.target := by
              rw [compileType_hasEdge_iff_hasResolvedEdge signature body q
                bodyEdge.target edge.symbol.environment edge.symbol.label
                edge.symbol.offers hSymbolMem]
              refine ⟨bodyEdge, hBodyEdgeMem, hSourceEq, ?_, ?_, ?_, ?_, rfl⟩
              · rw [← hPEnv]
              · rw [← hPLabel]
              · rw [← hPCurrent]
              · rw [← hPFuture]
                cases hSpec : bodyEdge.future with
                | explicit offers => simp [childFutureSpec, hSpec]
                | «at» t r =>
                    have hStateMem := compileTypeFuel_futureTargetsInStates signature
                      (typeCompilationFuel body) body le_rfl bodyEdge hBodyEdgeMem t r
                      hSpec
                    simp only [childFutureSpec, hSpec, childState]
                    rw [computeFutureOf_recursion_child signature name body
                      (.recur name body) hWhole (by omega) t hStateMem]
            rw [hEntry1] at hStep
            obtain ⟨bodyResidual', hSuccessorEq, hStep'⟩ :=
              (decoratedTypeTransition_replaceVar_iff name body bodyResidual).mp hStep
            have hTargetEq : successor.2 = .child 0 bodyEdge.target := by
              rw [hTarget, ← hPTarget]
            have hInnerMem :=
              relationMembership_of_step_edge_unique body (compileType signature body)
                hMem hInnerEdgeMem hStep'
                (fun target hTargetStep =>
                  decoratedTypeTransition_target_unique hTargetStep hStep')
            exact Or.inr ⟨bodyEdge.target, bodyResidual', by
              rw [← hSuccessorEq, ← hTargetEq], hInnerMem⟩)
    (residual, state) hRelated

/-- Defines the related-state shape for a compiled exclusive offer: the root represents the whole offer, a tagged child represents its own relation's residual, else or branch. -/
def xofferRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.xoffer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i action branchType q,
      branches[i]? = some (action, branchType) ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet branchType (compileType signature branchType))
        entry.1 q)

/-- Proves every related exclusive-offer pair has the exclusive-offer shape. -/
lemma relationMembership_xoffer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.xoffer elseType branches)
          (compileType signature (.xoffer elseType branches)))
        residual state) :
    xofferRelationShape signature elseType branches (residual, state) := by
  sorry

/-- Defines the related-state shape for a compiled conjunctive offer: the root represents the whole offer, a tagged child represents a residual of `τ0` or a generated branch commit. -/
def offerRelationShape
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.offer elseType branches, TypeAutomatonState.root) ∨
    (∃ q, entry.2 = .child 0 q ∧
      relationMembership
        (buildRelationSet elseType (compileType signature elseType))
        entry.1 q) ∨
    (∃ i selected q,
      branches[i]? = some selected ∧
      entry.2 = .child (i + 1) q ∧
      relationMembership
        (buildRelationSet (parallelTypeBranchesSelecting selected branches)
          (compileType signature
            (parallelTypeBranchesSelecting selected branches)))
        entry.1 q)

/-- Proves every related conjunctive-offer pair has the conjunctive-offer shape. -/
lemma relationMembership_offer_cases
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.offer elseType branches)
          (compileType signature (.offer elseType branches)))
        residual state) :
    offerRelationShape signature elseType branches (residual, state) := by
  sorry

/-- Defines the only related pair for a variable marker as its own seed. -/
def varRelationShape
    (name : String) (entry : PactType × TypeAutomatonState) : Prop :=
  entry = (.var name, TypeAutomatonState.root)

/-- Proves no decorated step is ever available at a variable marker. -/
lemma var_not_decoratedTypeTransition
    (name : String) {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : PactType} :
    ¬ DecoratedTypeTransition env (.var name) label offers target := by
  rintro ⟨hTrans, -⟩
  cases hTrans

/-- Proves the relation builder never grows past a variable-marker entry. -/
lemma relationSuccessors_var_eq_empty
    (signature : TypeAlphabet) (name : String)
    (entry : PactType × TypeAutomatonState) (hEntry : entry.1 = .var name) :
    relationSuccessors (compileType signature (.var name)) entry = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro pair hPair
  simp only [relationSuccessors, Finset.mem_biUnion] at hPair
  obtain ⟨edge, -, hPair⟩ := hPair
  split at hPair
  · split at hPair
    · rename_i hStep
      obtain ⟨residual', hStep'⟩ := hStep
      rw [hEntry] at hStep'
      exact var_not_decoratedTypeTransition name hStep'
    · simp at hPair
  · simp at hPair

/-- Proves every related variable-marker pair is the seed pair. -/
lemma relationMembership_var_cases
    (signature : TypeAlphabet) (name : String)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated :
      relationMembership
        (buildRelationSet (.var name) (compileType signature (.var name)))
        residual state) :
    residual = .var name ∧ state = TypeAutomatonState.root := by
  have hShape :=
    buildRelationSet_preserves (.var name) (compileType signature (.var name))
      (varRelationShape name)
      (by
        simp [varRelationShape, compileType, typeCompilationFuel,
          compileTypeFuel, finishAutomatonFragment])
      (by
        intro entry hEntry successor hSuccessor
        rw [relationSuccessors_var_eq_empty signature name entry
          (by rw [hEntry])] at hSuccessor
        exact absurd hSuccessor (by simp))
      (residual, state) hRelated
  simpa [varRelationShape, Prod.ext_iff] using hShape

end

end Pact
