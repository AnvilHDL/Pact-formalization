import Anvilpp.PactTypes.Correspondence.CorrespondenceRegularityCore

/-!
# Marker reachability (first wave) and compiledFragmentAccepting_represented
-/

namespace Pact

noncomputable section

/-! ### Marker reachability against the syntactic marker analysis

`mem_computeFuture_markerAugmented` and the installed-recursion decompositions
reduce the recursion future leaf to one Boolean side condition: whether the
compiled graph still reaches a `.variable name` marker in the same cycle.
The lemmas below compute that condition constructor by constructor and
identify it with `PactType.markerReachableSubst`. -/

/-- A name that does not occur compiles to a fragment with no marker edges at
all, so no marker is reachable from anywhere in it. -/
theorem not_markerReachable_of_tailOccurrences_false
    (signature : TypeAlphabet) (name : String) (fuel : Nat)
    (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hTail : processType.TailOccurrences name False)
    (state : TypeAutomatonState) :
    ¬ MarkerReachable (compileTypeFuel signature fuel processType) name
      state := by
  apply not_markerReachable_of_no_marker_edges
  intro edge hEdge hLabel
  exact (compileTypeFuel_variableEdge_source_var signature name fuel
    processType False hFuel hTail edge hEdge hLabel).1

/-- The immediate references of a choice root are exactly the two tagged child
entries.  Extracted from the corresponding future calculation. -/
private theorem buildChoiceAutomaton_referencedStates_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let pending : PendingAutomaton :=
      { states := fragment.states, edges := fragment.edges }
    pending.referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} := by
  classical
  let fragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  show pending.referencedStates .root =
    {.child 0 left.initial, .child 1 right.initial}
  ext state
  constructor
  · intro hState
    simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
      Finset.mem_filter] at hState
    rcases hState with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    simp only [pending, fragment, buildChoiceAutomaton,
      finishAutomatonFragment, childPendingEdges, Finset.mem_union,
      Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, _, rfl⟩
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hReference
        simp [AutomatonConstructionLabel.semantic, hSelectionLeft]
          at hReference
        simp [childState, hReference]
      · rw [hEdge] at hReference
        simp [AutomatonConstructionLabel.semantic, hSelectionRight]
          at hReference
        simp [childState, hReference]
  · intro hState
    simp only [Finset.mem_insert, Finset.mem_singleton] at hState
    rcases hState with rfl | rfl
    · let edge : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionLeft
          current := ∅
          future := .at (.child 0 left.initial) ∅
          target := .child 0 left.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [pending, fragment, buildChoiceAutomaton,
          finishAutomatonFragment, childPendingEdges, Finset.mem_union,
          Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton]
        right
        exact ⟨TypeEnvironment.tock,
          by simp [TypeAlphabet.localEnvironments], Or.inl rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, hSelectionLeft]
    · let edge : PendingAutomatonEdge :=
        { source := .root
          environment := TypeEnvironment.tock
          label := .visible selectionRight
          current := ∅
          future := .at (.child 1 right.initial) ∅
          target := .child 1 right.initial }
      simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
        Finset.mem_filter]
      refine ⟨edge, ⟨?_, rfl⟩, ?_⟩
      · simp only [pending, fragment, buildChoiceAutomaton,
          finishAutomatonFragment, childPendingEdges, Finset.mem_union,
          Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
          Finset.mem_singleton]
        right
        exact ⟨TypeEnvironment.tock,
          by simp [TypeAlphabet.localEnvironments], Or.inr rfl⟩
      · simp [edge, AutomatonConstructionLabel.semantic, hSelectionRight]

/-- A choice root carries no marker of its own; its two selection edges are
visible. -/
private theorem not_buildChoiceAutomaton_markerSource_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String) :
    ¬ MarkerSource (buildChoiceAutomaton signature left right
      selectionLeft selectionRight) name .root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
    Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hRight with ⟨childEdge, _, rfl⟩
    simp [childPendingEdge, childState] at hSource
  · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩ <;>
      (rw [hEdge] at hLabel; exact absurd hLabel (by simp))

/-- Marker reachability from a choice root is the disjunction of the two
tagged child entries. -/
theorem buildChoiceAutomaton_markerReachable_root
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (hSelectionLeft : selectionLeft ≠ TypeLabel.tock)
    (hSelectionRight : selectionRight ≠ TypeLabel.tock)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    let fragment := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    (MarkerReachable fragment name .root ↔
      (MarkerReachable fragment name (.child 0 left.initial) ∨
        MarkerReachable fragment name (.child 1 right.initial))) := by
  classical
  let fragment := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  show MarkerReachable fragment name .root ↔
    (MarkerReachable fragment name (.child 0 left.initial) ∨
      MarkerReachable fragment name (.child 1 right.initial))
  have hClosed : ({ states := fragment.states, edges := fragment.edges } :
      PendingAutomaton).ReferencesClosed := by
    apply PendingAutomaton.referencesClosed_of_futureTargetsInStates fragment
    exact buildChoiceAutomaton_futureTargetsInStates signature left right
      selectionLeft selectionRight hLeftTargets hRightTargets hLeftInitial
      hRightInitial
  have hRoot : (.root : TypeAutomatonState) ∈ fragment.states := by
    simp [fragment, buildChoiceAutomaton, finishAutomatonFragment]
  have hReferences : ({ states := fragment.states, edges := fragment.edges } :
      PendingAutomaton).referencedStates .root =
      {.child 0 left.initial, .child 1 right.initial} :=
    buildChoiceAutomaton_referencedStates_root signature left right
      selectionLeft selectionRight hSelectionLeft hSelectionRight
  rw [markerReachable_root_of_entries fragment name .root
    {.child 0 left.initial, .child 1 right.initial} hClosed hRoot
      (by rw [hReferences]; exact Finset.subset_insert _ _)
      (by rw [hReferences])]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd hMarker (not_buildChoiceAutomaton_markerSource_root
        signature left right selectionLeft selectionRight name)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hEntry
      rcases hEntry with rfl | rfl
      · exact Or.inl hInner
      · exact Or.inr hInner
  · rintro (hLeft | hRight)
    · exact Or.inr ⟨_, by simp, hLeft⟩
    · exact Or.inr ⟨_, by simp, hRight⟩

/-- Every state placed in the compiler's literal-termination set represents
`skip`.  This is the target-total half of `compileTypeFuel_accepting_iff`; it
is needed for the administrative bridge of sequence. -/
theorem compiledFragmentAccepting_represented
    (signature : TypeAlphabet) :
    ∀ (fuel : Nat) (processType : PactType),
      TypeCompilationFuelSufficient processType fuel →
      ∀ state ∈ (compileTypeFuel signature fuel processType).accepting,
        TypeCompilationRelation processType state .skip := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state hAccepting
      cases processType with
      | skip =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hAccepting
          subst state
          exact .skip
      | message msg dir =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hAccepting
          subst state
          exact .message_final msg dir
      | tock =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hAccepting
          subst state
          exact .cycle_final
      | progress pid =>
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_singleton] at hAccepting
          subst state
          exact .progress_final pid
      | var other =>
          simp [compileTypeFuel, finishAutomatonFragment] at hAccepting
      | recur binder body =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childAccepting, Finset.mem_image]
              at hAccepting
          rcases hAccepting with ⟨child, hChildAccepting, rfl⟩
          have hChild := ih body hBodyFuel child hChildAccepting
          convert TypeCompilationRelation.recur_body binder body .skip
            child hChild using 1 <;>
              simp [PactType.replaceVar, childState]
      | choice left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union, childAccepting,
            Finset.mem_image] at hAccepting
          rcases hAccepting with ⟨child, hChildAccepting, rfl⟩ |
            ⟨child, hChildAccepting, rfl⟩
          · exact TypeCompilationRelation.choice_left left right .skip child
              (ih left hLeftFuel child hChildAccepting)
          · exact TypeCompilationRelation.choice_right left right .skip child
              (ih right hRightFuel child hChildAccepting)
      | fairChoice bid left right =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union, childAccepting,
            Finset.mem_image] at hAccepting
          rcases hAccepting with ⟨child, hChildAccepting, rfl⟩ |
            ⟨child, hChildAccepting, rfl⟩
          · exact TypeCompilationRelation.fair_left bid left right .skip child
              (ih left hLeftFuel child hChildAccepting)
          · exact TypeCompilationRelation.fair_right bid left right .skip child
              (ih right hRightFuel child hChildAccepting)
      | seq left right =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childAccepting, Finset.mem_image]
              at hAccepting
          rcases hAccepting with ⟨child, hChildAccepting, rfl⟩
          exact TypeCompilationRelation.sequence_right left right .skip child
            (ih right hRightFuel child hChildAccepting)
      | par left right interface =>
          -- TODO(redevelopment): since the `parallel`/`parallel_fuse` split, a
          -- product state can be genuinely accepting (via `parallel_fuse`
          -- when both components finish); the old "no par state accepts"
          -- contradiction no longer closes this case. .
          sorry
      | xoffer elseType branches =>
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hAccepting
          rcases hAccepting with hElse | hBranch
          · simp only [childAccepting, Finset.mem_image] at hElse
            rcases hElse with ⟨child, hChildAccepting, rfl⟩
            exact TypeCompilationRelation.xoffer_else elseType .skip branches
              child (ih elseType hElseFuel child hChildAccepting)
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hBranch
            rcases hBranch with hEmpty | ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · simp only [childAccepting, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChildAccepting, rfl⟩
              have hFields := List.mem_zipIdx hIndexed
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hFields
              rcases hFields with ⟨hBound, hValue⟩
              have hAt : branchAutomata[indexed.2]? = some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              simp only [branchAutomata, List.getElem?_map] at hAt
              cases hOriginal : branches[indexed.2]? with
              | none => simp [hOriginal] at hAt
              | some branch =>
                rcases branch with ⟨action, branchType⟩
                simp only [hOriginal, Option.map_some, Option.some.injEq]
                  at hAt
                have hBranchMem : (action, branchType) ∈ branches :=
                  List.mem_of_getElem? hOriginal
                have hBranchesFuel :
                    typeBranchCompilationFuel branches ≤ fuel := by
                  simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                    at hFuel
                  omega
                have hBranchFuel :
                    TypeCompilationFuelSufficient branchType fuel :=
                  le_trans
                    (typeCompilationFuel_le_typeBranchCompilationFuel branches
                      (action, branchType) hBranchMem) hBranchesFuel
                have hFragment : indexed.1.2 =
                    compileTypeFuel signature fuel branchType := by
                  simpa using (congrArg Prod.snd hAt).symm
                rw [hFragment] at hChildAccepting
                have hChildRelated := ih branchType hBranchFuel child
                  hChildAccepting
                exact TypeCompilationRelation.xoffer_branch elseType
                  branchType .skip branches action indexed.2 child hOriginal
                    hChildRelated
      | offer elseType branches =>
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union] at hAccepting
          rcases hAccepting with hElse | hSelected
          · simp only [childAccepting, Finset.mem_image] at hElse
            rcases hElse with ⟨child, hChildAccepting, rfl⟩
            exact TypeCompilationRelation.offer_else elseType .skip branches
              child (ih elseType hElseFuel child hChildAccepting)
          · rw [indexedFragmentAccepting, mem_foldl_union_iff] at hSelected
            rcases hSelected with hEmpty | ⟨indexed, hIndexed, hChild⟩
            · simp at hEmpty
            · simp only [childAccepting, Finset.mem_image] at hChild
              rcases hChild with ⟨child, hChildAccepting, rfl⟩
              have hFields := List.mem_zipIdx hIndexed
              simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
                at hFields
              rcases hFields with ⟨hBound, hValue⟩
              have hAt : selectedConjunctions[indexed.2]? =
                  some indexed.1 := by
                rw [List.getElem?_eq_getElem hBound, ← hValue]
              simp only [selectedConjunctions, List.getElem?_map] at hAt
              cases hOriginal : branches[indexed.2]? with
              | none => simp [hOriginal] at hAt
              | some selected =>
                simp only [hOriginal, Option.map_some, Option.some.injEq]
                  at hAt
                have hChildFuel : TypeCompilationFuelSufficient
                    (parallelTypeBranchesSelecting selected branches) fuel := by
                  rw [TypeCompilationFuelSufficient,
                    typeCompilationFuel_parallelTypeBranchesSelecting]
                  simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                    at hFuel
                  omega
                have hFragment : indexed.1.2 = compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting selected branches) := by
                  simpa using (congrArg Prod.snd hAt).symm
                rw [hFragment] at hChildAccepting
                have hChildRelated := ih
                  (parallelTypeBranchesSelecting selected branches) hChildFuel
                    child hChildAccepting
                exact TypeCompilationRelation.offer_branches elseType .skip
                  branches selected indexed.2 child hOriginal hChildRelated

private theorem branchCanCompleteBeforeTockSubst_of_getElem
    (name : String) (value : Bool) :
    ∀ (branches : List (BareMessage × PactType)) (index : Nat)
      (action : BareMessage) (branchType : PactType),
      branches[index]? = some (action, branchType) →
      PactType.canCompleteBeforeTockSubst name value branchType = true →
      PactType.branchCanCompleteBeforeTockSubst name value branches = true := by
  intro branches
  induction branches with
  | nil => intro index action branchType hEntry; simp at hEntry
  | cons head rest ih =>
      intro index action branchType hEntry hComplete
      rcases head with ⟨headAction, headType⟩
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          simp [PactType.branchCanCompleteBeforeTockSubst, hComplete]
      | succ index =>
          simp only [List.getElem?_cons_succ] at hEntry
          simp [PactType.branchCanCompleteBeforeTockSubst,
            ih index action branchType hEntry hComplete]

private theorem canCompleteBeforeTockSubst_parallelTypeBranches
    (name : String) (value : Bool)
    (branches : List (BareMessage × PactType)) :
    PactType.canCompleteBeforeTockSubst name value
      (parallelTypeBranches branches) = true := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.canCompleteBeforeTockSubst]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.canCompleteBeforeTockSubst,
            PactType.branchCanCompleteBeforeTockSubst]
      | cons next tail =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.canCompleteBeforeTockSubst,
            PactType.branchCanCompleteBeforeTockSubst] at ih ⊢
          exact ih

private theorem canCompleteBeforeTockSubst_parallelTypeBranchesSelecting_of_mem
    (name : String) (value : Bool) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType), selected ∈ branches →
      PactType.canCompleteBeforeTockSubst name value
          (parallelTypeBranchesSelecting selected branches) =
        PactType.canCompleteBeforeTockSubst name value selected.2 := by
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
            PactType.canCompleteBeforeTockSubst]
      | cons next tail =>
          by_cases hSelected : branch = selected
          · subst branch
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.canCompleteBeforeTockSubst,
              canCompleteBeforeTockSubst_parallelTypeBranches]
          · have hRest : selected ∈ next :: tail := by
              rcases List.mem_cons.mp hMem with hHead | hTail
              · exact absurd hHead.symm hSelected
              · exact hTail
            simp only [parallelTypeBranchesSelecting, if_neg hSelected]
            simp [PactType.canCompleteBeforeTockSubst, singletonTypeXOffer,
              PactType.branchCanCompleteBeforeTockSubst, ih hRest]

/- Valuation forms of the three branch-completion facts above.  These are the
exact list equations needed by the binder-context predecessor induction; the
old scalar facts remain useful at its singleton wrapper. -/
theorem branchCompletionEval_of_getElem
    (valuation : String → Bool) :
    ∀ (branches : List (BareMessage × PactType)) (index : Nat)
      (action : BareMessage) (branchType : PactType),
      branches[index]? = some (action, branchType) →
      PactType.completionEval valuation branchType = true →
      PactType.branchCompletionEval valuation branches = true := by
  intro branches
  induction branches with
  | nil => intro index action branchType hEntry; simp at hEntry
  | cons head rest ih =>
      intro index action branchType hEntry hComplete
      rcases head with ⟨headAction, headType⟩
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at hEntry
          rcases hEntry with ⟨rfl, rfl⟩
          simp [PactType.branchCompletionEval, hComplete]
      | succ index =>
          simp only [List.getElem?_cons_succ] at hEntry
          simp [PactType.branchCompletionEval,
            ih index action branchType hEntry hComplete]

private theorem completionEval_parallelTypeBranches
    (valuation : String → Bool)
    (branches : List (BareMessage × PactType)) :
    PactType.completionEval valuation (parallelTypeBranches branches) = true := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, PactType.completionEval]
  | cons branch rest ih =>
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.completionEval, PactType.branchCompletionEval]
      | cons next tail =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            PactType.completionEval, PactType.branchCompletionEval] at ih ⊢
          exact ih

theorem completionEval_parallelTypeBranchesSelecting_of_mem
    (valuation : String → Bool) (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType), selected ∈ branches →
      PactType.completionEval valuation
          (parallelTypeBranchesSelecting selected branches) =
        PactType.completionEval valuation selected.2 := by
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
            PactType.completionEval]
      | cons next tail =>
          by_cases hSelected : branch = selected
          · subst branch
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              PactType.completionEval,
              completionEval_parallelTypeBranches]
          · have hRest : selected ∈ next :: tail := by
              rcases List.mem_cons.mp hMem with hHead | hTail
              · exact absurd hHead.symm hSelected
              · exact hTail
            simp only [parallelTypeBranchesSelecting, if_neg hSelected]
            simp [PactType.completionEval, singletonTypeXOffer,
              PactType.branchCompletionEval, ih hRest]

/- The syntax equation represented by a recursion header/backedge in an
ambient binder valuation.  Hygiene prevents the inserted binder from being
captured, and `completionEval_update_self` supplies the Boolean fixed point. -/
theorem completionEval_unfold_recur_of_hygienic
    (active : List String) (valuation : String → Bool)
    (binder : String) (body : PactType)
    (hSupported : ∀ name, name ∉ active → valuation name = false)
    (hFresh : body.BinderFreshFor (binder :: active)) :
    PactType.completionEval valuation
        (body.replaceVar binder (.recur binder body)) =
      PactType.completionEval valuation (.recur binder body) := by
  rw [PactType.completionEval_replaceVar_of_hygienic active valuation binder
    (.recur binder body) hSupported body hFresh]
  simpa only [PactType.completionEval] using
    PactType.completionEval_update_self valuation binder body

end

end Pact
