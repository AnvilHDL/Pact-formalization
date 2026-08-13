import Anvilpp.PactTypes.Correspondence.CorrespondenceOfferBranchLeaf

/-!
# offer regular leaf
-/

namespace Pact

noncomputable section

/-- Conjunctive-offer closure packages the generated branch product and its
enabled/else/wait root classifiers. -/
private theorem compilationFutureCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.offer elseType branches) := by
  have hSupportFields := hSupports
  have hGuardedFields := hGuarded
  have hTailFields := hTail
  have hLinearFields := hLinear
  have hScopedFields := hScoped
  simp only [TypeAlphabet.Supports] at hSupportFields
  simp only [PactType.ClockGuarded] at hGuardedFields
  simp only [PactType.TailRecursive] at hTailFields
  simp only [PactType.SameCycleMessageLinear] at hLinearFields
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hSelectedFuture : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationFutureCorrect signature
          (parallelTypeBranchesSelecting selected branches) := by
    intro selected index hEntry
    exact (compilationProofBundle_parallelTypeBranchesSelecting_leaf signature
      selected branches hSignature hSupportFields.2 hBranchesClosed
        hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
          hBranches).future
  exact compilationFutureCorrect_offer_of_children signature elseType branches
    hSupportFields.2 hElse.future hSelectedFuture

private theorem compilationCompletingCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationCompletingCorrect signature (.offer elseType branches) := by
  have hSupportFields := hSupports
  have hGuardedFields := hGuarded
  have hTailFields := hTail
  have hLinearFields := hLinear
  have hScopedFields := hScoped
  simp only [TypeAlphabet.Supports] at hSupportFields
  simp only [PactType.ClockGuarded] at hGuardedFields
  simp only [PactType.TailRecursive] at hTailFields
  simp only [PactType.SameCycleMessageLinear] at hLinearFields
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hSelectedCompleting : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationCompletingCorrect signature
          (parallelTypeBranchesSelecting selected branches) := by
    intro selected index hEntry
    exact (compilationProofBundle_parallelTypeBranchesSelecting_leaf signature
      selected branches hSignature hSupportFields.2 hBranchesClosed
        hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
          hBranches).completing
  exact compilationCompletingCorrect_offer signature elseType branches
    hElse.completing hSelectedCompleting

private theorem compilationFragmentStepCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hFuture : CompilationFutureCorrect signature (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.offer elseType branches) := by
  have hSupportFields := hSupports
  have hGuardedFields := hGuarded
  have hTailFields := hTail
  have hLinearFields := hLinear
  have hScopedFields := hScoped
  simp only [TypeAlphabet.Supports] at hSupportFields
  simp only [PactType.ClockGuarded] at hGuardedFields
  simp only [PactType.TailRecursive] at hTailFields
  simp only [PactType.SameCycleMessageLinear] at hLinearFields
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hSelectedScopedStep : ∀ (selected : BareMessage × PactType)
      (index : Nat), branches[index]? = some selected →
        CompilationScopedFragmentStepCorrect signature
          (parallelTypeBranchesSelecting selected branches) := by
    intro selected index hEntry
    exact (compilationProofBundle_parallelTypeBranchesSelecting_leaf signature
      selected branches hSignature hSupportFields.2 hBranchesClosed
        hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
          hBranches).scopedStep
  intro residual residual' state environment label offers hRelated hLocal
    hAvoids
  exact compilationScopedFragmentStepCorrect_offer signature elseType branches
    hSelectedScopedStep hElse.scopedStep hFuture hRelated hLocal hAvoids

/-
/-- Regression isolating the remaining conjunctive-offer execution mismatch.
The operational completion analysis of `offer tock [a ↦ tock]` is false, but
the constructor execution graph reaches the generated singleton offer, whose
`skip` else-arm marks its initial state completing. -/
theorem conjunctiveOffer_execution_completion_regression
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    let branches : List (BareMessage × PactType) := [(action, .tock)]
    let processType : PactType := .offer .tock branches
    let fragment := compileTypeFuel signature
      (typeCompilationFuel processType) processType
    let execution := sequenceExecutionAutomaton fragment
    processType.CanCompleteBeforeTock = false ∧
      ∃ completed ∈ execution.futureReachable .root,
        completed ∈ fragment.completing := by
  classical
  dsimp only
  let branches : List (BareMessage × PactType) := [(action, .tock)]
  let conjunctionType := parallelTypeBranches branches
  let fuel := max (typeCompilationFuel PactType.tock)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel PactType.tock
  let conjunction := compileTypeFuel signature fuel conjunctionType
  let fragment := buildConjunctiveOfferAutomaton signature branches
    elseFragment conjunction
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  have hElseFuel : TypeCompilationFuelSufficient PactType.tock fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hConjunctionFuel : TypeCompilationFuelSufficient conjunctionType fuel := by
    rw [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranches]
    simp [fuel, conjunctionType, branches]
  have hConjunctionStable : conjunction = compileTypeFuel signature
      (typeCompilationFuel conjunctionType) conjunctionType :=
    compileTypeFuel_eq_of_sufficient signature conjunctionType
      hConjunctionFuel (typeCompilationFuel_sufficient conjunctionType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel .tock hElseFuel
  have hConjunctionTargets : conjunction.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel conjunctionType
      hConjunctionFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel .tock hElseFuel
  have hConjunctionInitial : conjunction.initial ∈ conjunction.states :=
    compileTypeFuel_initial_mem signature fuel conjunctionType
      hConjunctionFuel
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildConjunctiveOfferAutomaton_futureTargetsInStates signature branches
      elseFragment conjunction hElseTargets hConjunctionTargets hElseInitial
        hConjunctionInitial
  have hExecutionClosed : execution.ReferencesClosed :=
    sequenceExecutionAutomaton_referencesClosed fragment hFragmentTargets
  have hRoot : (.root : TypeAutomatonState) ∈ execution.states := by
    apply Finset.mem_union_left
    simp [fragment, buildConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.offer .tock branches)) (.offer .tock branches) =
        fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    simp [fragment, elseFragment, conjunction, conjunctionType, fuel,
      typeCompilationFuel]
  have hEntries := buildConjunctiveOfferAutomaton_entries_referenced signature
    branches elseFragment conjunction (by
      intro branch hBranch
      simp only [branches, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hBranch
      rcases hBranch with ⟨rfl, rfl⟩
      exact hAvailable)
  have hPendingReference : childState 0 conjunction.initial ∈
      pending.referencedStates .root := by
    apply hEntries
    simp [conjunctiveOfferEntryStates, branches]
  have hShape := sequenceExecution_buildConjunctiveOffer_root_shape signature
    branches elseFragment conjunction
  have hReferenceEquality := sequenceExecution_root_referencedStates_eq
    fragment hShape
  have hExecutionReference : childState 0 conjunction.initial ∈
      execution.referencedStates .root := by
    rw [hReferenceEquality]
    simpa [pending, execution] using hPendingReference
  have hReachable : childState 0 conjunction.initial ∈
      execution.futureReachable .root :=
    execution.referencedStates_subset_futureReachable .root hExecutionClosed
      hRoot hExecutionReference
  have hConjunctionRelation : TypeCompilationRelation conjunctionType
      conjunction.initial conjunctionType := by
    have hCanonical := compileType_initial_relation signature conjunctionType
    simpa [conjunction, hConjunctionStable, compileType] using hCanonical
  have hConjunctionCompleting : conjunction.initial ∈
      conjunction.completing := by
    have hSkipCompleting := compilationCompletingCorrect_skip signature
    have hTockCompleting := compilationCompletingCorrect_tock signature
    have hWhole := compilationCompletingCorrect_xoffer signature .skip
      [(action, .tock)] hSkipCompleting (by
        intro selected selectedType index hEntry
        have hIndex : index = 0 := by
          simpa using (List.getElem?_eq_some_iff.mp hEntry).1
        subst index
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hEntry
        rcases hEntry with ⟨rfl, rfl⟩
        exact hTockCompleting)
    have hCanonical := (hWhole conjunction.initial conjunctionType
      hConjunctionRelation).mpr (by
        simp [conjunctionType, branches, parallelTypeBranches,
          singletonTypeXOffer, PactType.CanCompleteBeforeTock])
    simpa [conjunction, hConjunctionStable] using hCanonical
  have hParentCompleting : childState 0 conjunction.initial ∈
      fragment.completing :=
    (buildConjunctiveOffer_child0_completing_iff signature branches
      elseFragment conjunction conjunction.initial).mpr hConjunctionCompleting
  constructor
  · simp [PactType.CanCompleteBeforeTock,
      PactType.BranchCanCompleteBeforeTock]
  · rw [hParent]
    exact ⟨childState 0 conjunction.initial, hReachable, hParentCompleting⟩

/-- Consequently the strengthened execution field required by the current
hierarchy is false for this well-supported conjunctive offer. -/
theorem conjunctiveOffer_not_sequenceExecutionCorrect
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    ¬ CompilationSequenceExecutionCorrect signature
      (.offer .tock [(action, .tock)]) := by
  intro hCorrect
  have hAtRoot := hCorrect .root (.offer .tock [(action, .tock)])
    (TypeCompilationRelation.offer_source .tock [(action, .tock)])
  rcases conjunctiveOffer_execution_completion_regression signature action
      hAvailable with ⟨hCannotComplete, completed, hReachable, hCompleting⟩
  have hCanComplete := hAtRoot.2.mp
    ⟨completed, hReachable, Or.inr hCompleting⟩
  simp_all
-/

/-! ### Selected conjunctive-offer execution helpers

The following private lemmas are the `parallelTypeBranchesSelecting` analogues
of the exclusive-offer execution machinery.  The selected builder shares the
exact state/skipping/completing layout of `buildExclusiveOfferAutomaton`, so
the tagging lemmas transfer verbatim; only the root edge shapes differ. -/

/-- Every generated singleton product can finish before the next clock: each
component is either literal `skip` or a singleton `xoffer` whose synthetic
else arm is `skip`. -/
private theorem canCompleteBeforeTock_parallelTypeBranches
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranches branches).CanCompleteBeforeTock = true := by
  induction branches with
  | nil => simp [parallelTypeBranches, PactType.CanCompleteBeforeTock]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.CanCompleteBeforeTock]
      | cons next tail =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.CanCompleteBeforeTock] at ih ⊢
          exact ih

/-- Forcing the selected witness replaces exactly one synthetic else arm by a
mandatory action prefix, so the whole product completes before the next clock
precisely when that branch's continuation does. -/
private theorem canCompleteBeforeTock_parallelTypeBranchesSelecting_of_mem
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType), selected ∈ branches →
      (parallelTypeBranchesSelecting selected branches).CanCompleteBeforeTock =
        selected.2.CanCompleteBeforeTock := by
  intro branches
  induction branches with
  | nil => intro hMem; simp at hMem
  | cons branch rest ih =>
      intro hMem
      cases rest with
      | nil =>
          have hEqual : branch = selected := by
            simpa [eq_comm] using hMem
          subst branch
          simp [parallelTypeBranchesSelecting, selectedTypeBranch,
            PactType.CanCompleteBeforeTock]
      | cons next tail =>
          by_cases hSelected : branch = selected
          · subst branch
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.CanCompleteBeforeTock,
              canCompleteBeforeTock_parallelTypeBranches]
          · have hRest : selected ∈ next :: tail := by
              rcases List.mem_cons.mp hMem with hHead | hTail
              · exact absurd hHead.symm hSelected
              · exact hTail
            simp only [parallelTypeBranchesSelecting, if_neg hSelected]
            simp [PactType.CanCompleteBeforeTock, singletonTypeXOffer,
              ih hRest]

/-- Index inversion for the compiled selected-conjunction list. -/
private theorem compiledSelectedConjunction_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches))).zipIdx) :
    ∃ selected, branches[indexed.2]? = some selected ∧
      indexed.1 = (selected.1, compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)) := by
  have hFields := List.mem_zipIdx hIndexed
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hFields
  rcases hFields with ⟨hBound, hValue⟩
  have hAt :
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected
            branches)))[indexed.2]? = some indexed.1 := by
    rw [List.getElem?_eq_getElem hBound, hValue]
  rw [List.getElem?_map] at hAt
  cases hOriginal : branches[indexed.2]? with
  | none => simp [hOriginal] at hAt
  | some selected =>
      simp only [hOriginal, Option.map_some, Option.some.injEq] at hAt
      exact ⟨selected, rfl, hAt.symm⟩

private theorem sequenceExecution_buildSelectedConjunctiveOffer_root_shape
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed := by
  classical
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElse
    rcases hElse with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      exact ⟨by simp, ∅, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    exact ⟨by simp, _, rfl⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    exact ⟨by simp, ∅, rfl⟩

private theorem buildSelectedConjunctiveOffer_child0_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).skipping ↔
      state ∈ elseAutomaton.skipping := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentSkipping
    selectedConjunctions state
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childSkipping 0 elseAutomaton ↔
      state ∈ elseAutomaton.skipping := by
    simp [childSkipping, childState]
  rw [hChild]
  simp [hNotIndexed]

private theorem buildSelectedConjunctiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).completing ↔
      state ∈ elseAutomaton.completing := by
  have hNotIndexed := child_zero_not_mem_indexedFragmentCompleting
    selectedConjunctions state
  have hNotHeader : childState 0 state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union]
  have hChild : childState 0 state ∈ childCompleting 0 elseAutomaton ↔
      state ∈ elseAutomaton.completing := by
    simp [childCompleting, childState]
  rw [hChild]
  simp [hNotHeader, hNotIndexed]

private theorem buildSelectedConjunctiveOffer_root_not_skipping
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    (.root : TypeAutomatonState) ∉
      (buildSelectedConjunctiveOfferAutomaton signature branches
        elseAutomaton selectedConjunctions).skipping := by
  have hNotIndexed := root_not_mem_indexedFragmentSkipping selectedConjunctions
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, not_or]
  exact ⟨by simp [childSkipping, childState], hNotIndexed⟩

private theorem buildSelectedConjunctiveOffer_conjunction_skipping_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).skipping ↔
      state ∈ entry.2.skipping := by
  have hNotElse : childState (index + 1) state ∉
      childSkipping 0 elseAutomaton := by
    simp [childSkipping, childState]
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotElse, false_or]
  exact childState_mem_indexedFragmentSkipping_iff selectedConjunctions index
    entry hEntry state

private theorem buildSelectedConjunctiveOffer_conjunction_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).completing ↔
      state ∈ entry.2.completing := by
  have hNotHeader : childState (index + 1) state ∉
      (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
          branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
        {TypeAutomatonState.root} else
          (∅ : Finset TypeAutomatonState)) := by
    split <;> simp [childState]
  have hNotElse : childState (index + 1) state ∉
      childCompleting 0 elseAutomaton := by
    simp [childCompleting, childState]
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, hNotHeader, hNotElse, false_or]
  exact childState_mem_indexedFragmentCompleting_iff selectedConjunctions index
    entry hEntry state

/-- Hierarchy adapter for selected conjunctive-offer products.  Execution
correctness is transported through the indexed post-construction products; the
obsolete all-else counterexample no longer applies because that one outcome is
absent. -/
private theorem compilationSequenceExecutionCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationSequenceExecutionCorrect signature
      (.offer elseType branches) := by
  classical
  have hSupportFields := hSupports
  have hGuardedFields := hGuarded
  have hTailFields := hTail
  have hLinearFields := hLinear
  have hScopedFields := hScoped
  simp only [TypeAlphabet.Supports] at hSupportFields
  simp only [PactType.ClockGuarded] at hGuardedFields
  simp only [PactType.TailRecursive] at hTailFields
  simp only [PactType.SameCycleMessageLinear] at hLinearFields
  simp only [PactType.InterfaceScoped] at hScopedFields
  have hSelectedBundle : ∀ (selected : BareMessage × PactType) (index : Nat),
      branches[index]? = some selected →
        CompilationProofBundle signature
          (parallelTypeBranchesSelecting selected branches) := by
    intro selected index _
    exact compilationProofBundle_parallelTypeBranchesSelecting_leaf signature
      selected branches hSignature hSupportFields.2 hBranchesClosed
        hGuardedFields.2 hTailFields.2 hLinearFields.2 hScopedFields.2
          hBranches
  let fuel := max (typeCompilationFuel elseType)
    (conjunctiveCompilationFuel branches)
  let elseFragment := compileTypeFuel signature fuel elseType
  let selectedConjunctions := branches.map fun selected =>
    (selected.1, compileTypeFuel signature fuel
      (parallelTypeBranchesSelecting selected branches))
  let fragment := buildSelectedConjunctiveOfferAutomaton signature branches
    elseFragment selectedConjunctions
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  let execution := sequenceExecutionAutomaton fragment
  let entries := selectedConjunctiveOfferEntryStates elseFragment
    selectedConjunctions
  have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
    simp [TypeCompilationFuelSufficient, fuel]
  have hElseStable : elseFragment = compileTypeFuel signature
      (typeCompilationFuel elseType) elseType :=
    compileTypeFuel_eq_of_sufficient signature elseType hElseFuel
      (typeCompilationFuel_sufficient elseType)
  have hElseTargets : elseFragment.FutureTargetsInStates :=
    compileTypeFuel_futureTargetsInStates signature fuel elseType hElseFuel
  have hElseInitial : elseFragment.initial ∈ elseFragment.states :=
    compileTypeFuel_initial_mem signature fuel elseType hElseFuel
  have hSelectedFuel : ∀ selected : BareMessage × PactType,
      TypeCompilationFuelSufficient
        (parallelTypeBranchesSelecting selected branches) fuel := by
    intro selected
    simp only [TypeCompilationFuelSufficient,
      typeCompilationFuel_parallelTypeBranchesSelecting, fuel]
    exact le_max_right _ _
  have hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_futureTargetsInStates signature fuel _
      (hSelectedFuel selected)
  have hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, _, rfl⟩
    exact compileTypeFuel_initial_mem signature fuel _ (hSelectedFuel selected)
  have hFragmentTargets : fragment.FutureTargetsInStates :=
    buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates signature
      branches elseFragment selectedConjunctions hElseTargets
        hConjunctionTargets hElseInitial hConjunctionInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [fragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment]
  have hAvailableOriginal : ∀ branch ∈ branches,
      typeNeed branch.1 ∈ signature.localEnvironmentActions :=
    supportedBranchNeed_mem_localEnvironmentActions signature branches
      hSupportFields.2
  have hAvailable : ∀ entry ∈ selectedConjunctions,
      typeNeed entry.1 ∈ signature.localEnvironmentActions := by
    intro entry hEntry
    rcases List.mem_map.mp hEntry with ⟨selected, hSelected, rfl⟩
    exact hAvailableOriginal selected hSelected
  have hUpper : pending.referencedStates .root ⊆ insert .root entries := by
    simpa [pending, fragment, entries] using
      buildSelectedConjunctiveOfferAutomaton_root_references_upper signature
        branches elseFragment selectedConjunctions
  have hEntries : entries ⊆ pending.referencedStates .root := by
    simpa [pending, fragment, entries] using
      buildSelectedConjunctiveOfferAutomaton_entries_referenced signature
        branches elseFragment selectedConjunctions hAvailable
  have hShape : ∀ edge ∈ fragment.edges, edge.source = .root →
      edge.label ≠ .future ∧
        ∃ removed, edge.future = .at edge.target removed := by
    intro edge hEdge hSource
    exact sequenceExecution_buildSelectedConjunctiveOffer_root_shape signature
      branches elseFragment selectedConjunctions edge hEdge hSource
  have hParent : compileTypeFuel signature
      (typeCompilationFuel (.offer elseType branches))
        (.offer elseType branches) = fragment := by
    simp only [typeCompilationFuel, Nat.one_add, compileTypeFuel]
    rfl
  have hWholeFuture := compilationFutureCorrect_offer_regular_leaf signature
    elseType branches hSignature hSupports hBranchesClosed hGuarded hTail hLinear
      hScoped hElse hBranches
  have hWholeCompleting := compilationCompletingCorrect_offer_regular_leaf
    signature elseType branches hSignature hSupports hBranchesClosed hGuarded hTail
      hLinear hScoped hElse hBranches
  have hElseStates : elseFragment.states.image (childState 0) ⊆
      fragment.states := by
    intro tagged hTagged
    rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
    simp [fragment, buildSelectedConjunctiveOfferAutomaton,
      finishAutomatonFragment, childStates, childState, hState]
  have hElseOutgoing : ∀ state edge,
      edge ∈ fragment.edges ∧ edge.source = childState 0 state ↔
        ∃ childEdge ∈ elseFragment.edges,
          childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
    intro state edge
    simpa [fragment] using
      (buildSelectedConjunctiveOfferAutomaton_outgoing_else signature branches
        elseFragment selectedConjunctions state edge)
  have hElseRootRelation : TypeCompilationRelation elseType
      elseFragment.initial elseType := by
    simpa [elseFragment, hElseStable, compileType] using
      compileType_initial_relation signature elseType
  have hElseRootExecution := hElse.execution elseFragment.initial elseType
    hElseRootRelation
  have hElseRootExecution' :
      computeFuture (sequenceExecutionAutomaton elseFragment)
          elseFragment.initial = typeFutureOffers elseType ∧
        ((∃ completed ∈
              (sequenceExecutionAutomaton elseFragment).futureReachable
                elseFragment.initial,
              completed ∈ elseFragment.skipping ∨
                completed ∈ elseFragment.completing) ↔
          elseType.CanCompleteBeforeTock = true) := by
    simpa [CompilationSequenceExecutionCorrect, elseFragment, hElseStable]
      using hElseRootExecution
  have hEntryFacts : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry ∧
        ((∃ completed ∈ execution.futureReachable entry,
            completed ∈ fragment.skipping ∨
              completed ∈ fragment.completing) →
          (PactType.offer elseType branches).CanCompleteBeforeTock = true) := by
    intro entry hEntry
    simp only [entries, selectedConjunctiveOfferEntryStates, Finset.mem_union,
      Finset.mem_singleton] at hEntry
    rcases hEntry with rfl | hConjunctionEntry
    · have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
          elseFragment.initial hElseInitial
      have hParentRelation : TypeCompilationRelation
          (.offer elseType branches) (childState 0 elseFragment.initial)
            elseType := TypeCompilationRelation.offer_else elseType elseType
              branches elseFragment.initial hElseRootRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hElseRootExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment elseFragment 0 hElseOutgoing hElseStates hElseTargets
            elseFragment.initial hElseInitial
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState 0 state ∈ fragment.skipping ↔
              state ∈ elseFragment.skipping := by
          intro state
          exact buildSelectedConjunctiveOffer_child0_skipping_iff signature
            branches elseFragment selectedConjunctions state
        have hComplete : ∀ state,
            childState 0 state ∈ fragment.completing ↔
              state ∈ elseFragment.completing := by
          intro state
          exact buildSelectedConjunctiveOffer_child0_completing_iff signature
            branches elseFragment selectedConjunctions state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton elseFragment).futureReachable
              elseFragment.initial,
            childCompleted ∈ elseFragment.skipping ∨
              childCompleted ∈ elseFragment.completing :=
          (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
            hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hElseCan := hElseRootExecution'.2.mp hChildWitness
        simp [PactType.CanCompleteBeforeTock, hElseCan]
    · rw [mem_foldl_union_iff] at hConjunctionEntry
      rcases hConjunctionEntry with hEmpty | ⟨indexed, hIndexed, hEntryState⟩
      · simp at hEmpty
      simp only [Finset.mem_singleton] at hEntryState
      subst entry
      rcases compiledSelectedConjunction_zipIdx_cases signature fuel branches
          indexed (by simpa [selectedConjunctions] using hIndexed) with
        ⟨selected, hSyntaxEntry, hCompiledEntry⟩
      rcases indexed with ⟨compiledEntry, index⟩
      simp only at hCompiledEntry
      subst compiledEntry
      let selectedFragment := compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)
      have hSelectedMember : selected ∈ branches := by
        rcases List.getElem?_eq_some_iff.mp hSyntaxEntry with
          ⟨hBound, hValue⟩
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hSelectedStable : selectedFragment = compileTypeFuel signature
          (typeCompilationFuel
            (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
          (typeCompilationFuel_sufficient _)
      have hSelectedInitialState : selectedFragment.initial ∈
          selectedFragment.states :=
        compileTypeFuel_initial_mem signature fuel _ (hSelectedFuel selected)
      have hSelectedTargets : selectedFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel _
          (hSelectedFuel selected)
      have hAutomatonEntry : selectedConjunctions[index]? =
          some (selected.1, selectedFragment) := by
        simp [selectedConjunctions, selectedFragment, hSyntaxEntry]
      have hZipEntry : ((selected.1, selectedFragment), index) ∈
          selectedConjunctions.zipIdx := by
        simpa [selectedConjunctions, selectedFragment] using hIndexed
      have hSelectedStates : selectedFragment.states.image
          (childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨state, hState, rfl⟩
        have hIndexedState : childState (index + 1) state ∈
            indexedFragmentStates selectedConjunctions := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((selected.1, selectedFragment), index), hZipEntry,
            by simp [childStates, childState, hState]⟩
        simp [fragment, buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hSelectedOutgoing : ∀ state edge,
          edge ∈ fragment.edges ∧
              edge.source = childState (index + 1) state ↔
            ∃ childEdge ∈ selectedFragment.edges,
              childEdge.source = state ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro state edge
        simpa [fragment, selectedFragment] using
          (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry state edge)
      have hSelectedRelation : TypeCompilationRelation
          (parallelTypeBranchesSelecting selected branches)
            selectedFragment.initial
            (parallelTypeBranchesSelecting selected branches) := by
        simpa [selectedFragment, hSelectedStable, compileType] using
          compileType_initial_relation signature
            (parallelTypeBranchesSelecting selected branches)
      have hSelectedExecution :=
        (hSelectedBundle selected index hSyntaxEntry).execution
          selectedFragment.initial
            (parallelTypeBranchesSelecting selected branches) hSelectedRelation
      have hSelectedExecution' :
          computeFuture (sequenceExecutionAutomaton selectedFragment)
              selectedFragment.initial =
            typeFutureOffers
              (parallelTypeBranchesSelecting selected branches) ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton
                    selectedFragment).futureReachable
                      selectedFragment.initial,
                  completed ∈ selectedFragment.skipping ∨
                    completed ∈ selectedFragment.completing) ↔
              (parallelTypeBranchesSelecting selected
                branches).CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, selectedFragment,
          hSelectedStable] using hSelectedExecution
      have hExecEmbedding := sequenceExecution_taggedChild_computeFuture
        fragment selectedFragment (index + 1) hSelectedOutgoing
          hSelectedStates hSelectedTargets selectedFragment.initial
            hSelectedInitialState
      have hParentRelation : TypeCompilationRelation
          (.offer elseType branches)
            (childState (index + 1) selectedFragment.initial)
            (parallelTypeBranchesSelecting selected branches) :=
        TypeCompilationRelation.offer_branches elseType
          (parallelTypeBranchesSelecting selected branches) branches selected
            index selectedFragment.initial hSyntaxEntry hSelectedRelation
      have hPendingMenu := hWholeFuture _ _ hParentRelation
      rw [hParent] at hPendingMenu
      constructor
      · exact hExecEmbedding.trans
          (hSelectedExecution'.1.trans hPendingMenu.symm)
      · rintro ⟨completed, hReach, hCompleted⟩
        have hReachEmbedding := sequenceExecution_taggedChild_futureReachable
          fragment selectedFragment (index + 1) hSelectedOutgoing
            hSelectedStates hSelectedTargets selectedFragment.initial
              hSelectedInitialState
        rw [hReachEmbedding] at hReach
        have hSkip : ∀ state,
            childState (index + 1) state ∈ fragment.skipping ↔
              state ∈ selectedFragment.skipping := by
          intro state
          exact buildSelectedConjunctiveOffer_conjunction_skipping_iff
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry state
        have hComplete : ∀ state,
            childState (index + 1) state ∈ fragment.completing ↔
              state ∈ selectedFragment.completing := by
          intro state
          exact buildSelectedConjunctiveOffer_conjunction_completing_iff
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry state
        have hChildWitness : ∃ childCompleted ∈
            (sequenceExecutionAutomaton selectedFragment).futureReachable
              selectedFragment.initial,
            childCompleted ∈ selectedFragment.skipping ∨
              childCompleted ∈ selectedFragment.completing :=
          (taggedCompletionWitness_iff fragment selectedFragment (index + 1)
            _ hSkip hComplete).mp ⟨completed, hReach, hCompleted⟩
        have hSelectedCan := hSelectedExecution'.2.mp hChildWitness
        have hBranchCan : selected.2.CanCompleteBeforeTock = true := by
          rw [← canCompleteBeforeTock_parallelTypeBranchesSelecting_of_mem
            selected branches hSelectedMember]
          exact hSelectedCan
        have hAny : branches.any
            (fun branch => branch.2.CanCompleteBeforeTock) = true := by
          apply List.any_eq_true.mpr
          exact ⟨selected, hSelectedMember, hBranchCan⟩
        simp [PactType.CanCompleteBeforeTock,
          branchCanCompleteBeforeTock_eq_any, hAny]
  have hEntryFuture : ∀ entry ∈ entries,
      computeFuture execution entry = computeFuture pending entry := by
    intro entry hEntry
    exact (hEntryFacts entry hEntry).1
  have hRootFutureEquality : computeFuture execution .root =
      computeFuture pending .root :=
    sequenceExecution_computeFuture_root_eq fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries hEntryFuture
  have hRootReach : execution.futureReachable .root =
      {.root} ∪ entries.biUnion execution.futureReachable :=
    sequenceExecution_futureReachable_root fragment entries
      hFragmentTargets hRoot hShape hUpper hEntries
  intro state residual hRelated
  rw [hParent]
  cases hRelated with
  | offer_source =>
      constructor
      · have hPendingRoot := hWholeFuture .root
          (.offer elseType branches)
            (TypeCompilationRelation.offer_source elseType branches)
        rw [hParent] at hPendingRoot
        exact hRootFutureEquality.trans hPendingRoot
      · constructor
        · rintro ⟨completed, hReach, hCompleted⟩
          rw [hRootReach] at hReach
          simp only [Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hReach
          rcases hReach with hAtRoot | ⟨entry, hEntry, hAtEntry⟩
          · subst completed
            have hRootNotSkipping :
                (.root : TypeAutomatonState) ∉ fragment.skipping :=
              buildSelectedConjunctiveOffer_root_not_skipping signature
                branches elseFragment selectedConjunctions
            have hRootCompleting : (.root : TypeAutomatonState) ∈
                fragment.completing := hCompleted.resolve_left
              hRootNotSkipping
            exact (hWholeCompleting .root (.offer elseType branches)
              (TypeCompilationRelation.offer_source elseType branches)).mp
                (by simpa [hParent] using hRootCompleting)
          · exact (hEntryFacts entry hEntry).2
              ⟨completed, hAtEntry, hCompleted⟩
        · intro hCanComplete
          have hRootCompleting :=
            (hWholeCompleting .root (.offer elseType branches)
              (TypeCompilationRelation.offer_source elseType branches)).mpr
                hCanComplete
          refine ⟨.root, execution.mem_futureReachable_self .root, ?_⟩
          right
          simpa [hParent] using hRootCompleting
  | offer_else _ _ _ childState hChildRelated =>
      have hChildState : childState ∈ elseFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          elseType childState residual hChildRelated
        simpa [elseFragment, hElseStable] using hCanonical
      have hChildCanonical := hElse.execution childState residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton elseFragment) childState =
              typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton elseFragment).futureReachable
                    childState,
                  completed ∈ elseFragment.skipping ∨
                    completed ∈ elseFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, elseFragment,
          hElseStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            elseFragment 0 hElseOutgoing hElseStates hElseTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState 0 childState),
              completed ∈ fragment.skipping ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState 0 child ∈ fragment.skipping ↔
              child ∈ elseFragment.skipping := by
          intro child
          exact buildSelectedConjunctiveOffer_child0_skipping_iff signature
            branches elseFragment selectedConjunctions child
        have hComplete : ∀ child,
            Pact.childState 0 child ∈ fragment.completing ↔
              child ∈ elseFragment.completing := by
          intro child
          exact buildSelectedConjunctiveOffer_child0_completing_iff signature
            branches elseFragment selectedConjunctions child
        exact (taggedCompletionWitness_iff fragment elseFragment 0 _ hSkip
          hComplete).trans hChild.2
  | offer_branches _ _ _ selected index childState hSyntaxEntry
      hChildRelated =>
      let selectedFragment := compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)
      have hSelectedStable : selectedFragment = compileTypeFuel signature
          (typeCompilationFuel
            (parallelTypeBranchesSelecting selected branches))
          (parallelTypeBranchesSelecting selected branches) :=
        compileTypeFuel_eq_of_sufficient signature _ (hSelectedFuel selected)
          (typeCompilationFuel_sufficient _)
      have hAutomatonEntry : selectedConjunctions[index]? =
          some (selected.1, selectedFragment) := by
        simp [selectedConjunctions, selectedFragment, hSyntaxEntry]
      have hZipEntry : ((selected.1, selectedFragment), index) ∈
          selectedConjunctions.zipIdx := by
        rcases List.getElem?_eq_some_iff.mp hAutomatonEntry with
          ⟨hBound, hValue⟩
        have hZipBound : index < selectedConjunctions.zipIdx.length := by
          simpa using hBound
        have hMember := List.getElem_mem hZipBound
        have hAt := List.getElem_zipIdx (l := selectedConjunctions)
          (i := index) (j := 0) hZipBound
        simp only [zero_add] at hAt
        rw [hAt, hValue] at hMember
        exact hMember
      have hChildState : childState ∈ selectedFragment.states := by
        have hCanonical := compilationStateCorrect_of_compilation signature
          (parallelTypeBranchesSelecting selected branches) childState residual
            hChildRelated
        simpa [selectedFragment, hSelectedStable] using hCanonical
      have hTargets : selectedFragment.FutureTargetsInStates :=
        compileTypeFuel_futureTargetsInStates signature fuel _
          (hSelectedFuel selected)
      have hStates : selectedFragment.states.image
          (Pact.childState (index + 1)) ⊆ fragment.states := by
        intro tagged hTagged
        rcases Finset.mem_image.mp hTagged with ⟨child, hChild, rfl⟩
        have hIndexedState : Pact.childState (index + 1) child ∈
            indexedFragmentStates selectedConjunctions := by
          rw [indexedFragmentStates, mem_foldl_union_iff]
          right
          exact ⟨((selected.1, selectedFragment), index), hZipEntry,
            by simp [childStates, Pact.childState, hChild]⟩
        simp [fragment, buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, hIndexedState]
      have hOutgoing : ∀ source edge,
          edge ∈ fragment.edges ∧
              edge.source = Pact.childState (index + 1) source ↔
            ∃ childEdge ∈ selectedFragment.edges,
              childEdge.source = source ∧
                edge = childPendingEdge (index + 1) childEdge := by
        intro source edge
        simpa [fragment, selectedFragment] using
          (buildSelectedConjunctiveOfferAutomaton_outgoing_conjunction
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry source edge)
      have hChildCanonical :=
        (hSelectedBundle selected index hSyntaxEntry).execution childState
          residual hChildRelated
      have hChild :
          computeFuture (sequenceExecutionAutomaton selectedFragment)
              childState = typeFutureOffers residual ∧
            ((∃ completed ∈
                  (sequenceExecutionAutomaton
                    selectedFragment).futureReachable childState,
                  completed ∈ selectedFragment.skipping ∨
                    completed ∈ selectedFragment.completing) ↔
              residual.CanCompleteBeforeTock = true) := by
        simpa [CompilationSequenceExecutionCorrect, selectedFragment,
          hSelectedStable] using hChildCanonical
      constructor
      · exact (sequenceExecution_taggedChild_computeFuture fragment
          selectedFragment (index + 1) hOutgoing hStates hTargets childState
            hChildState).trans hChild.1
      · have hReachEquality :=
          sequenceExecution_taggedChild_futureReachable fragment
            selectedFragment (index + 1) hOutgoing hStates hTargets childState
              hChildState
        change ((∃ completed ∈
              (sequenceExecutionAutomaton fragment).futureReachable
                (Pact.childState (index + 1) childState),
              completed ∈ fragment.skipping ∨
                completed ∈ fragment.completing) ↔
            residual.CanCompleteBeforeTock = true)
        rw [hReachEquality]
        have hSkip : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.skipping ↔
              child ∈ selectedFragment.skipping := by
          intro child
          exact buildSelectedConjunctiveOffer_conjunction_skipping_iff
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry child
        have hComplete : ∀ child,
            Pact.childState (index + 1) child ∈ fragment.completing ↔
              child ∈ selectedFragment.completing := by
          intro child
          exact buildSelectedConjunctiveOffer_conjunction_completing_iff
            signature branches elseFragment selectedConjunctions index
              (selected.1, selectedFragment) hAutomatonEntry child
        exact (taggedCompletionWitness_iff fragment selectedFragment
          (index + 1) _ hSkip hComplete).trans hChild.2

theorem compilationProofBundle_offer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.offer elseType branches) := by
  have hFuture := compilationFutureCorrect_offer_regular_leaf signature
    elseType branches hSignature hSupports hBranchesClosed hGuarded hTail hLinear
      hScoped hElse hBranches
  exact
    { future := hFuture
      completing := compilationCompletingCorrect_offer_regular_leaf signature
        elseType branches hSignature hSupports hBranchesClosed hGuarded hTail hLinear
          hScoped hElse hBranches
      scopedStep := compilationFragmentStepCorrect_offer_regular_leaf
        signature elseType branches hSignature hSupports hBranchesClosed hGuarded hTail
          hLinear hScoped hFuture hElse hBranches
      execution := compilationSequenceExecutionCorrect_offer_regular_leaf
        signature elseType branches hSignature hSupports hBranchesClosed hGuarded hTail
          hLinear hScoped hElse hBranches }

end

end Pact
