import Anvilpp.PactTypes.Correspondence.Core.TypeCompilationRelation

/-!
# CompilationStateCorrect and the skipping/completing state-membership classifiers
-/

namespace Pact

noncomputable section

/-- State-carrier side of the compiler relation.  Future embeddings need this
independently of the semantic equality: saturation stability is stated for a
declared child state. -/
def CompilationStateCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      state ∈ (compileTypeFuel signature
        (typeCompilationFuel processType) processType).states

private theorem childState_mem_indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) (hState : state ∈ entry.2.states) :
    childState (index + 1) state ∈ indexedFragmentStates automata := by
  classical
  rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
  have hZipBound : index < automata.zipIdx.length := by
    simpa using hBound
  have hIndexed : (entry, index) ∈ automata.zipIdx := by
    have hMember := List.getElem_mem hZipBound
    have hAt := List.getElem_zipIdx (l := automata) (i := index)
      (j := 0) hZipBound
    simp only [zero_add] at hAt
    rw [hAt, hValue] at hMember
    exact hMember
  rw [indexedFragmentStates, mem_foldl_union_iff]
  right
  refine ⟨(entry, index), hIndexed, ?_⟩
  simp [childStates, childState, hState]

/-- Every state named by `TypeCompilationRelation` belongs to the matching
sufficiently fuelled compiler fragment.  This carrier invariant is independent
of future semantics and is shared by every constructor embedding. -/
private theorem compileTypeFuel_relation_state_mem
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
          state ∈ (compileTypeFuel signature fuel processType).states := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_final msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_final =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_final pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur_source name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          simpa [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_source left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_source bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | sequence_left left right childResidual childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ childResidual
            hChildRelated
          have hTagged : childState 0 childQ ∈
              childStates 0 (compileTypeFuel signature fuel left) := by
            exact Finset.mem_image.mpr ⟨childQ, hChild, rfl⟩
          rw [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment]
          change childState 0 childQ ∈
            (childStates 0 (compileTypeFuel signature fuel left) ∪
              (compileTypeFuel signature fuel left).edges.image
                (fun edge => childState 0 edge.target)) ∪
              childStates 1 (compileTypeFuel signature fuel right)
          simp only [Finset.mem_union]
          exact Or.inl (Or.inl hTagged)
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hLeft := ih left hLeftFuel leftState leftResidual hLeftRelated
          have hRight := ih right hRightFuel rightState rightResidual
            hRightRelated
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, hLeft, hRight]
      | xoffer_source elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          have hTagged : childState 0 childQ ∈
              childStates 0 (compileTypeFuel signature fuel elseType) := by
            exact Finset.mem_image.mpr ⟨childQ, hChild, rfl⟩
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState 0 childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates
                  (branches.map fun branch =>
                    (branch.1, compileTypeFuel signature fuel branch.2))
          simp only [Finset.mem_union]
          exact Or.inl (Or.inr hTagged)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchMem : (action, branchType) ∈ branches := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hBound, hValue⟩
            have hMember := List.getElem_mem hBound
            simpa [hValue] using hMember
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel :=
            le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentStates branchAutomata
            index (action, compileTypeFuel signature fuel branchType)
            hAutomatonEntry childQ hChild
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          change childState (index + 1) childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates branchAutomata
          simp only [Finset.mem_union]
          exact Or.inr hIndexed
      | offer_source elseType branches =>
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
      | offer_branches elseType _ branches selected index childQ hEntry
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting selected branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih
            (parallelTypeBranchesSelecting selected branches) hConjunctionFuel
              childQ residual hChildRelated
          let selectedConjunctions := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting branch branches))
          have hAutomatonEntry : selectedConjunctions[index]? = some
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) := by
            simp [selectedConjunctions, hEntry]
          have hIndexed := childState_mem_indexedFragmentStates
            selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches))
              hAutomatonEntry childQ hChild
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          change childState (index + 1) childQ ∈
            ({TypeAutomatonState.root} ∪
              childStates 0 (compileTypeFuel signature fuel elseType)) ∪
                indexedFragmentStates selectedConjunctions
          simp only [Finset.mem_union]
          exact Or.inr hIndexed
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          exact Or.inl (by
            simp [childStates, childState, hChild])

theorem compilationStateCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationStateCorrect signature processType := by
  exact compileTypeFuel_relation_state_mem signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

/-- Graph future resolution agrees with syntactic same-cycle future offers at
every state/residual represented by the final pending compilation fragment. -/
def CompilationFutureCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      computeFuture pending state = typeFutureOffers residual

/-- Every visible resolved edge leaving a represented constructor state reaches
another state represented by the same compiled syntax.  Temporary variable
markers and construction-only future observations are excluded by
`HasResolvedEdge`, whose label is necessarily visible. -/
def CompilationResolvedEdgeTargetsRelated
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {source : TypeAutomatonState} {residual : PactType}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary} {target : TypeAutomatonState},
    TypeCompilationRelation processType source residual →
    fragment.HasResolvedEdge source environment label offers target →
    ∃ targetResidual,
      TypeCompilationRelation processType target targetResidual

/-- Every semantic pending compiler edge has consumed its temporary recursion
marker.  Construction-only `.future` observations are intentionally exempt;
they are used by optimistic future computation and never become type steps. -/
def CompilationPendingEdgesVisible
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ edge ∈ fragment.edges, edge.label ≠ .future →
    ∃ label, edge.label = .visible label

/-- The reusable `stepIff` property for the concrete compiler relation. -/
def CompilationStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature processType).alphabet →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        (compileType signature processType).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation processType state' residual')

/-- Replacing a variable by its recursion binder yields literal `skip` exactly
when the original residual was already literal `skip`. -/
theorem PactType.replaceVar_recur_eq_skip_iff
    (processType : PactType) (name : String) (body : PactType) :
    (processType.replaceVar name (.recur name body) = .skip) ↔
      processType = .skip := by
  cases processType <;> simp only [PactType.replaceVar] <;>
    try simp
  all_goals split <;> simp_all

theorem childState_mem_indexedFragmentSkipping_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentSkipping automata ↔
      state ∈ entry.2.skipping := by
  classical
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildSkipping, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildSkipping
  · intro hSkipping
    rcases List.getElem?_eq_some_iff.mp hEntry with
      ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childSkipping, childState, hSkipping]

theorem root_not_mem_indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentSkipping automata := by
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

theorem child_zero_not_mem_indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentSkipping automata := by
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

theorem childState_mem_indexedFragmentCompleting_iff
    (automata : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : automata[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈ indexedFragmentCompleting automata ↔
      state ∈ entry.2.completing := by
  classical
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  constructor
  · rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
    · simp at hEmpty
    simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨child, hChildCompleting, hState⟩
    have hIndex : indexed.2 = index := by
      injection hState with hTag _
      omega
    have hInner : child = state := by
      injection hState
    subst child
    have hIndexedFields := List.mem_zipIdx hIndexed
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
      at hIndexedFields
    rcases hIndexedFields with ⟨hBound, hValue⟩
    have hIndexedEntry : automata[indexed.2]? = some indexed.1 := by
      rw [List.getElem?_eq_getElem hBound, ← hValue]
    have hEntryEq : indexed.1 = entry := by
      have hOptions := congrArg (fun position => automata[position]?) hIndex
      change automata[indexed.2]? = automata[index]? at hOptions
      rw [hIndexedEntry, hEntry] at hOptions
      exact Option.some.inj hOptions
    simpa [hEntryEq] using hChildCompleting
  · intro hCompleting
    rcases List.getElem?_eq_some_iff.mp hEntry with ⟨hBound, hValue⟩
    have hZipBound : index < automata.zipIdx.length := by
      simpa using hBound
    have hIndexed : (entry, index) ∈ automata.zipIdx := by
      have hMember := List.getElem_mem hZipBound
      have hAt := List.getElem_zipIdx (l := automata) (i := index)
        (j := 0) hZipBound
      simp only [zero_add] at hAt
      rw [hAt, hValue] at hMember
      exact hMember
    right
    refine ⟨(entry, index), hIndexed, ?_⟩
    simp [childCompleting, childState, hCompleting]

theorem root_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

theorem child_zero_not_mem_indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∉ indexedFragmentCompleting automata := by
  rw [indexedFragmentCompleting, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childCompleting, Finset.mem_image] at hChild
    rcases hChild with ⟨other, hOther, hEquality⟩
    have hIndex : indexed.2 + 1 = 0 := by
      injection hEquality
    omega

/-- At every state represented by a sufficiently fuelled constructor
fragment, the compiler's syntactic `skipping` marker is exact: it holds
precisely when the represented operational residual is literal `skip`. -/
theorem compileTypeFuel_skipping_iff
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      ∀ state residual,
        TypeCompilationRelation processType state residual →
        (state ∈ (compileTypeFuel signature fuel processType).skipping ↔
          residual = .skip) := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel state residual hRelated
      cases hRelated with
      | skip =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_source msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | message_final msg dir =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_source =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | cycle_final =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_source pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | progress_final pid =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | «variable» name =>
          simp [compileTypeFuel, finishAutomatonFragment]
      | recur_source name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | recur_body name body childResidual childQ hChildRelated =>
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih body hBodyFuel childQ childResidual
            hChildRelated
          rw [PactType.replaceVar_recur_eq_skip_iff]
          simpa [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | choice_source left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | choice_left left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | choice_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | fair_source bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | fair_left bid left right _ childQ hChildRelated =>
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih left hLeftFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | fair_right bid left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | sequence_left left right childResidual childQ hChildRelated =>
          simp [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | sequence_right left right _ childQ hChildRelated =>
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih right hRightFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | parallel left right leftResidual rightResidual interface leftState
          rightState hLeftRelated hRightRelated =>
          simp [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment]
      | xoffer_source elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState,
            root_not_mem_indexedFragmentSkipping]
      | xoffer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hElseTag : childState 0 childQ ∈
                childSkipping 0 (compileTypeFuel signature fuel elseType) ↔
              childQ ∈
                (compileTypeFuel signature fuel elseType).skipping := by
            simp [childSkipping, childState]
          have hNotIndexed : childState 0 childQ ∉
              indexedFragmentSkipping
                (branches.map fun branch =>
                  (branch.1, compileTypeFuel signature fuel branch.2)) :=
            child_zero_not_mem_indexedFragmentSkipping _ childQ
          constructor
          · rintro (hElse | hIndexed)
            · exact hChild.mp (hElseTag.mp hElse)
            · exact (hNotIndexed hIndexed).elim
          · intro hSkip
            left
            exact hElseTag.mpr (hChild.mpr hSkip)
      | xoffer_branch elseType branchType _ branches action index
          childQ hEntry hChildRelated =>
          have hBranchesFuel : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hBranchFuel : TypeCompilationFuelSufficient branchType fuel := by
            rcases List.getElem?_eq_some_iff.mp hEntry with
              ⟨hIndexBound, hIndexValue⟩
            have hBranchMem : (action, branchType) ∈ branches := by
              have hMember := List.getElem_mem hIndexBound
              simpa [hIndexValue] using hMember
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranchMem)
              hBranchesFuel
          have hChild := ih branchType hBranchFuel childQ residual
            hChildRelated
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          have hAutomatonEntry : branchAutomata[index]? =
              some (action, compileTypeFuel signature fuel branchType) := by
            simp [branchAutomata, hEntry]
          have hIndexed := childState_mem_indexedFragmentSkipping_iff
            branchAutomata index
              (action, compileTypeFuel signature fuel branchType)
              hAutomatonEntry childQ
          rw [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotElse : childState (index + 1) childQ ∉
              childSkipping 0 (compileTypeFuel signature fuel elseType) := by
            simp [childSkipping, childState]
          constructor
          · rintro (hElse | hBranch)
            · exact (hNotElse hElse).elim
            · exact hChild.mp (hIndexed.mp hBranch)
          · intro hSkip
            right
            exact hIndexed.mpr (hChild.mpr hSkip)
      | offer_source elseType branches =>
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState,
            root_not_mem_indexedFragmentSkipping]
      | offer_branches elseType _ branches selected index childQ hEntry
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranchesSelecting selected branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih
            (parallelTypeBranchesSelecting selected branches) hConjunctionFuel
              childQ residual hChildRelated
          let selectedConjunctions := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting branch branches))
          have hAutomatonEntry : selectedConjunctions[index]? = some
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches)) := by
            simp [selectedConjunctions, hEntry]
          have hIndexed := childState_mem_indexedFragmentSkipping_iff
            selectedConjunctions index
              (selected.1, compileTypeFuel signature fuel
                (parallelTypeBranchesSelecting selected branches))
              hAutomatonEntry childQ
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotElse : childState (index + 1) childQ ∉
              childSkipping 0 (compileTypeFuel signature fuel elseType) := by
            simp [childSkipping, childState]
          constructor
          · rintro (hElse | hBranch)
            · exact (hNotElse hElse).elim
            · exact hChild.mp (hIndexed.mp hBranch)
          · intro hSkip
            right
            exact hIndexed.mpr (hChild.mpr hSkip)
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          rw [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment]
          simp only [Finset.mem_union]
          have hNotIndexed : childState 0 childQ ∉
              indexedFragmentSkipping
                (branches.map fun selected =>
                  (selected.1, compileTypeFuel signature fuel
                    (parallelTypeBranchesSelecting selected branches))) := by
            rw [indexedFragmentSkipping, mem_foldl_union_iff]
            rintro (hEmpty | ⟨indexed, _, hMember⟩)
            · simp at hEmpty
            · simp [childSkipping, childState] at hMember
          constructor
          · rintro (hElse | hIndexed)
            · exact hChild.mp (by simpa [childSkipping, childState] using hElse)
            · exact (hNotIndexed hIndexed).elim
          · intro hSkip
            left
            simpa [childSkipping, childState] using hChild.mpr hSkip

/-- The compiler's skipping-state marker agrees with literal `skip` at every
state represented by the compilation relation. -/
def CompilationSkippingCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  ∀ state residual,
    TypeCompilationRelation processType state residual →
      (state ∈ (compileTypeFuel signature
          (typeCompilationFuel processType) processType).skipping ↔
        residual = .skip)

theorem compilationSkippingCorrect_of_compilation
    (signature : TypeAlphabet) (processType : PactType) :
    CompilationSkippingCorrect signature processType := by
  exact compileTypeFuel_skipping_iff signature
    (typeCompilationFuel processType) processType
    (typeCompilationFuel_sufficient processType)

end

end Pact
