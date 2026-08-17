import Anvilpp.PactTypes.Correspondence.CorrespondenceCore

/-!
# Compiler-label visibility

Closed syntax cannot leave a temporary recursion-variable marker on a semantic
compiler edge.  Parallel `.future` observations remain construction-only and
are deliberately allowed.
-/

namespace Pact

noncomputable section

private theorem allVariablesBound_branch_of_mem_visibility
    (bound : List String) : ∀ branches entry,
    PactType.AllBranchVariablesBound bound branches → entry ∈ branches →
      PactType.AllVariablesBound bound entry.2 := by
  intro branches
  induction branches with
  | nil => simp
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      intro entry hAll hEntry
      simp only [PactType.AllBranchVariablesBound] at hAll
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact hAll.1
      · exact ih entry hAll.2 hRest

private theorem allVariablesBound_parallelTypeBranches_visibility
    (bound : List String) (branches : List (BareMessage × PactType))
    (hBound : PactType.AllBranchVariablesBound bound branches) :
    PactType.AllVariablesBound bound (parallelTypeBranches branches) := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.AllVariablesBound, PactType.AllBranchVariablesBound]
            using hBound.1
      | cons next tail =>
          simp only [parallelTypeBranches, PactType.AllVariablesBound]
          constructor
          · simpa [singletonTypeXOffer, PactType.AllVariablesBound,
              PactType.AllBranchVariablesBound] using hBound.1
          · exact ih hBound.2

private theorem allVariablesBound_parallelTypeBranchesSelecting_visibility
    (bound : List String) (selected : BareMessage × PactType) :
    ∀ branches,
      PactType.AllBranchVariablesBound bound branches →
      PactType.AllVariablesBound bound
        (parallelTypeBranchesSelecting selected branches) := by
  intro branches hBound
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      cases rest with
      | nil =>
          by_cases hEq : (action, processType) = selected
          · simp [parallelTypeBranchesSelecting, hEq, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1]
      | cons next tail =>
          by_cases hEq : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.AllVariablesBound, hBound.1,
              allVariablesBound_parallelTypeBranches_visibility bound
                (next :: tail) hBound.2]
          · simp [parallelTypeBranchesSelecting, hEq, singletonTypeXOffer,
              PactType.AllVariablesBound, PactType.AllBranchVariablesBound,
              hBound.1, ih hBound.2]

/-- Any temporary variable label in a fuel-bounded compiler fragment names a
variable permitted by the surrounding syntactic binder context. -/
theorem compileTypeFuel_variable_label_mem_bound
    (signature : TypeAlphabet) : ∀ fuel processType bound,
    PactType.AllVariablesBound bound processType →
    ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
      ∀ name, edge.label = .variable name → name ∈ bound := by
  sorry -- TODO(redevelopment): proof unfolded buildParallelAutomaton's old
  -- synthetic-future-edge shape, now removed; .

/-- A fully closed compiler fragment has only visible semantic pending edges;
the remaining non-visible edges are the explicit optimistic-future
observations of synchronized products. -/
theorem compilationPendingEdgesVisible_of_allVariablesBound
    (signature : TypeAlphabet) (processType : PactType)
    (hClosed : PactType.AllVariablesBound [] processType) :
    CompilationPendingEdgesVisible signature processType := by
  intro edge hEdge hSemantic
  cases hLabel : edge.label with
  | visible label => exact ⟨label, rfl⟩
  | «variable» name =>
      have hBound := compileTypeFuel_variable_label_mem_bound signature
        (typeCompilationFuel processType) processType [] hClosed edge hEdge
          name hLabel
      simp at hBound
  | future => exact (hSemantic hLabel).elim

end

end Pact
