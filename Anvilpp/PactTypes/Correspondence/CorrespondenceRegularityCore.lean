import Anvilpp.PactTypes.Correspondence.CorrespondenceSequenceAssembly

/-!
# Regularity transport: skipping/completing, tail-occurrence, binder, variable-edge invariants
-/

namespace Pact

noncomputable section

/-- Literal termination is always a same-cycle completion.  This is a
compiler invariant, not a semantic assumption: every constructor transports
child `skipping` states into its `completing` metadata, and recursion includes
the body's completing states in the seed of its non-clock predecessor
closure. -/
private theorem compileTypeFuel_accepting_subset_completing
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
        (compileTypeFuel signature fuel processType).accepting ⊆
          (compileTypeFuel signature fuel processType).completing := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .
theorem tailBranchOccurrences_mem
    (name : String) (tail : Prop) :
    ∀ (branches : List (BareMessage × PactType))
      (entry : BareMessage × PactType),
      PactType.TailBranchOccurrences name tail branches →
      entry ∈ branches →
        PactType.TailOccurrences name tail entry.2 := by
  intro branches
  induction branches with
  | nil => intro entry _ hMem; simp at hMem
  | cons head rest ih =>
      intro entry hTail hMem
      obtain ⟨action, processType⟩ := head
      simp only [PactType.TailBranchOccurrences] at hTail
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hTail.1
      · exact ih entry hTail.2 hRest

private theorem tailOccurrences_parallelTypeBranches
    (name : String) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
        PactType.TailOccurrences name False
          (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => intro _; simp [parallelTypeBranches, PactType.TailOccurrences]
  | cons branch rest ih =>
      obtain ⟨action, processType⟩ := branch
      intro hTail
      have hFields : PactType.TailOccurrences name False processType ∧
          PactType.TailBranchOccurrences name False rest := by
        simpa only [PactType.TailBranchOccurrences] using hTail
      cases rest with
      | nil =>
          simp only [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailOccurrences, PactType.TailBranchOccurrences]
          exact ⟨trivial, hFields.1, trivial⟩
      | cons next tailBranches =>
          simp only [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailOccurrences, PactType.TailBranchOccurrences]
          exact ⟨⟨trivial, hFields.1, trivial⟩, ih hFields.2⟩

theorem tailOccurrences_parallelTypeBranchesSelecting
    (name : String) (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.TailBranchOccurrences name False branches →
        PactType.TailOccurrences name False
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _
      simp [parallelTypeBranchesSelecting, PactType.TailOccurrences]
  | cons branch rest ih =>
      obtain ⟨action, processType⟩ := branch
      intro hTail
      have hFields : PactType.TailOccurrences name False processType ∧
          PactType.TailBranchOccurrences name False rest := by
        simpa only [PactType.TailBranchOccurrences] using hTail
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · simp only [parallelTypeBranchesSelecting, if_pos hSelected,
              selectedTypeBranch, PactType.TailOccurrences]
            exact ⟨trivial, hFields.1⟩
          · simp only [parallelTypeBranchesSelecting, if_neg hSelected,
              singletonTypeXOffer, PactType.TailOccurrences,
              PactType.TailBranchOccurrences]
            exact ⟨trivial, hFields.1, trivial⟩
      | cons next tailBranches =>
          by_cases hSelected : (action, processType) = selected
          · simp only [parallelTypeBranchesSelecting, if_pos hSelected,
              selectedTypeBranch, PactType.TailOccurrences]
            exact ⟨⟨trivial, hFields.1⟩,
              tailOccurrences_parallelTypeBranches name _ hFields.2⟩
          · simp only [parallelTypeBranchesSelecting, if_neg hSelected,
              singletonTypeXOffer, PactType.TailOccurrences,
              PactType.TailBranchOccurrences]
            exact ⟨⟨trivial, hFields.1, trivial⟩, ih hFields.2⟩

private theorem tailRecursive_parallelTypeBranches :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailRecursiveBranches branches →
        PactType.TailRecursive (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.TailRecursive]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hTail
      have hFields : branchType.TailRecursive ∧
          PactType.TailRecursiveBranches rest := by
        simpa only [PactType.TailRecursiveBranches] using hTail
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailRecursive, PactType.TailRecursiveBranches] using
              hFields.1
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.TailRecursive, PactType.TailRecursiveBranches] using
              And.intro hFields.1 (ih hFields.2)

theorem tailRecursive_parallelTypeBranchesSelecting
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.TailRecursiveBranches branches →
        PactType.TailRecursive
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.TailRecursive]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hTail
      have hFields : branchType.TailRecursive ∧
          PactType.TailRecursiveBranches rest := by
        simpa only [PactType.TailRecursiveBranches] using hTail
      cases rest with
      | nil =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.TailRecursive, hFields.1]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.TailRecursive,
              PactType.TailRecursiveBranches, hFields.1]
      | cons next tail =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.TailRecursive, hFields.1,
              tailRecursive_parallelTypeBranches (next :: tail) hFields.2]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.TailRecursive,
              PactType.TailRecursiveBranches, hFields.1, ih hFields.2]

private theorem binderHygienic_parallelTypeBranches (bound : List String) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderHygienicBranches bound branches →
        PactType.BinderHygienic bound (parallelTypeBranches branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.BinderHygienic]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hHygienic
      have hFields : branchType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound rest := by
        simpa only [PactType.BinderHygienicBranches] using hHygienic
      cases rest with
      | nil =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderHygienic, PactType.BinderHygienicBranches] using
              hFields.1
      | cons next tail =>
          simpa [parallelTypeBranches, singletonTypeXOffer,
            PactType.BinderHygienic, PactType.BinderHygienicBranches] using
              And.intro hFields.1 (ih hFields.2)

theorem binderHygienic_parallelTypeBranchesSelecting
    (bound : List String) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BinderHygienicBranches bound branches →
        PactType.BinderHygienic bound
          (parallelTypeBranchesSelecting selected branches) := by
  intro branches
  induction branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.BinderHygienic]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      intro hHygienic
      have hFields : branchType.BinderHygienic bound ∧
          PactType.BinderHygienicBranches bound rest := by
        simpa only [PactType.BinderHygienicBranches] using hHygienic
      cases rest with
      | nil =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderHygienic, hFields.1]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderHygienic,
              PactType.BinderHygienicBranches, hFields.1]
      | cons next tail =>
          by_cases hSelected : (action, branchType) = selected
          · simp [parallelTypeBranchesSelecting, hSelected,
              selectedTypeBranch, PactType.BinderHygienic, hFields.1,
              binderHygienic_parallelTypeBranches bound (next :: tail)
                hFields.2]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, PactType.BinderHygienic,
              PactType.BinderHygienicBranches, hFields.1, ih hFields.2]

/- Binder-context preservation for represented residuals. -/
theorem compilationRelation_allVariablesBound
    {bound : List String} {original residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation original state residual) :
    original.AllVariablesBound bound → residual.AllVariablesBound bound := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .

theorem compilationRelation_binderFreshFor
    {forbidden : List String} {original residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation original state residual) :
    original.BinderHygienic forbidden → residual.BinderFreshFor forbidden := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .
theorem compilationRelation_tailOccurrences_false
    (name : String) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation processType state residual) :
    processType.TailOccurrences name False →
      residual.TailOccurrences name False := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .
private theorem compilationRelation_canCompleteBeforeTockSubst_eq_of_false
    (name : String) (value : Bool) {processType residual : PactType}
    {state : TypeAutomatonState}
    (hRelated : TypeCompilationRelation processType state residual)
    (hTail : processType.TailOccurrences name False) :
    PactType.canCompleteBeforeTockSubst name value residual =
      residual.CanCompleteBeforeTock :=
  PactType.canCompleteBeforeTockSubst_eq_of_tailOccurrences_false name value
    residual (compilationRelation_tailOccurrences_false name hRelated hTail)

/-- **Recursive-call sources represent bare variables.**

If a compiled fragment still carries an unresolved `.variable name` marker
edge, then — provided `name` occurs only in tail position — the source of that
edge represents exactly the residual `PactType.var name`, and the ambient tail
flag holds.

The `tail` conjunct is what makes the induction go through: a `.variable name`
marker occurring in a non-tail position (the left of a sequence, either side
of a parallel composition, or a conjunctive-offer branch) is impossible,
because there `TailOccurrences name False` holds and the conclusion `tail`
degenerates to `False`.  In the tail positions that remain (choice branches,
the right of a sequence, exclusive-offer continuations, and the body of a
non-shadowing binder) the representative residual is transported unchanged by
the corresponding `TypeCompilationRelation` constructor, so it stays
`PactType.var name`; under a non-shadowing binder `replaceVar` leaves it
alone, which is why `other ≠ name` is extracted first.

Stating the conclusion as the relation itself (rather than as uniqueness of
the represented residual) additionally supplies *existence* of a
representative, which the seed-inclusion step of
`recursionBodyCompletingClosure_subset` needs.

The induction mirrors `compileTypeFuel_futureTargetsInStates`: structural on
the compilation fuel, one case per constructor of the compiler. -/
theorem compileTypeFuel_variableEdge_source_var
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType) (tail : Prop),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences name tail processType →
      ∀ edge ∈ (compileTypeFuel signature fuel processType).edges,
        edge.label = AutomatonConstructionLabel.variable name →
          tail ∧ TypeCompilationRelation processType edge.source
            (PactType.var name) := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .
theorem compileTypeFuel_markerEdgesInert
    (signature : TypeAlphabet) (name : String) :
    ∀ (fuel : Nat) (processType : PactType) (tail : Prop),
      TypeCompilationFuelSufficient processType fuel →
      PactType.TailOccurrences name tail processType →
        MarkerEdgesInert (compileTypeFuel signature fuel processType) name := by
  sorry -- TODO(redevelopment): proof broken by upstream TypeCompilationRelation/TypeEntry split; .
