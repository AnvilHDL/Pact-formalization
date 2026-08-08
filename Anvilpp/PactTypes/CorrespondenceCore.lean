import Anvilpp.PactTypes.Automata

/-!
# Core and atomic type-automaton correspondence
-/

namespace Pact

noncomputable section

/-!
### Semantic residuals represented by constructor states

This relation is the invariant used by the correspondence proof.  The first
type is the fragment originally compiled; the final type is the operational
residual represented by the tagged state in the middle.
-/

inductive TypeCompilationRelation :
    PactType → TypeAutomatonState → PactType → Prop where
  | skip : TypeCompilationRelation .skip .root .skip
  | message_source (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .root (.message msg dir)
  | message_final (msg : MessageId) (dir : MessageDir) :
      TypeCompilationRelation (.message msg dir) .final .skip
  | cycle_source : TypeCompilationRelation .tock .root .tock
  | cycle_final : TypeCompilationRelation .tock .final .skip
  | progress_source (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .root (.progress pid)
  | progress_final (pid : ProcId) :
      TypeCompilationRelation (.progress pid) .final .skip
  | variable (name : String) :
      TypeCompilationRelation (.var name) .root (.var name)
  | recur_source (name : String) (body : PactType) :
      TypeCompilationRelation (.recur name body) .root (.recur name body)
  | recur_body (name : String) (body residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation body state residual →
      TypeCompilationRelation (.recur name body) (.child 0 state)
        (residual.replaceVar name (.recur name body))
  | choice_source (left right : PactType) :
      TypeCompilationRelation (.choice left right) .root (.choice left right)
  | choice_left (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.choice left right) (.child 0 state) residual
  | choice_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.choice left right) (.child 1 state) residual
  | fair_source (bid : BranchId) (left right : PactType) :
      TypeCompilationRelation (.fairChoice bid left right) .root
        (.fairChoice bid left right)
  | fair_left (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 0 state) residual
  | fair_right (bid : BranchId) (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.fairChoice bid left right) (.child 1 state) residual
  | sequence_left (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation left state residual →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq residual right)
  | sequence_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.seq left right) (.child 1 state) residual
  | parallel (left right leftResidual rightResidual : PactType)
      (interface : Interface) (leftState rightState : TypeAutomatonState) :
      TypeCompilationRelation left leftState leftResidual →
      TypeCompilationRelation right rightState rightResidual →
      TypeCompilationRelation (.par left right interface)
        (.pair leftState rightState)
        (.par leftResidual rightResidual interface)
  | xoffer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.xoffer elseType branches) .root
        (.xoffer elseType branches)
  | xoffer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.xoffer elseType branches) (.child 0 state) residual
  | xoffer_branch (elseType branchType residual : PactType)
      (branches : List (BareMessage × PactType)) (action : BareMessage)
      (index : Nat) (state : TypeAutomatonState) :
      branches[index]? = some (action, branchType) →
      TypeCompilationRelation branchType state residual →
      TypeCompilationRelation (.xoffer elseType branches)
        (.child (index + 1) state) residual
  | offer_source (elseType : PactType)
      (branches : List (BareMessage × PactType)) :
      TypeCompilationRelation (.offer elseType branches) .root
        (.offer elseType branches)
  | offer_branches (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation (parallelTypeBranches branches) state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 0 state) residual
  | offer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 1 state) residual

/-- A constructor state represents at most one semantic residual. -/
theorem TypeCompilationRelation.residual_unique
    {original left right : PactType} {state : TypeAutomatonState}
    (hLeft : TypeCompilationRelation original state left)
    (hRight : TypeCompilationRelation original state right) : left = right := by
  induction hLeft generalizing right <;> cases hRight <;>
    try simp_all
  all_goals
    first
    | solve_by_elim
    | (congr 1; solve_by_elim)
    | (constructor <;> solve_by_elim)

/-- Sufficiently fuelled compilation starts in the state representing its input. -/
theorem compileTypeFuel_initial_relation (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      TypeCompilationRelation processType
        (compileTypeFuel signature fuel processType).initial processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => exact TypeCompilationRelation.message_source msg dir
      | progress pid => exact TypeCompilationRelation.progress_source pid
      | tock => exact TypeCompilationRelation.cycle_source
      | skip => exact TypeCompilationRelation.skip
      | var name => exact TypeCompilationRelation.variable name
      | recur name body => exact TypeCompilationRelation.recur_source name body
      | choice left right => exact TypeCompilationRelation.choice_source left right
      | fairChoice bid left right =>
          exact TypeCompilationRelation.fair_source bid left right
      | seq left right =>
          apply TypeCompilationRelation.sequence_left
          apply ih left
          simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
          omega
      | par left right interface =>
          apply TypeCompilationRelation.parallel
          · apply ih left
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          · apply ih right
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
      | xoffer elseType branches =>
          exact TypeCompilationRelation.xoffer_source elseType branches
      | offer elseType branches =>
          exact TypeCompilationRelation.offer_source elseType branches

/-- The public compiler's initial state represents the original type. -/
theorem compileType_initial_relation
    (signature : TypeAlphabet) (processType : PactType) :
    TypeCompilationRelation processType
      (compileType signature processType).initial processType := by
  apply compileTypeFuel_initial_relation signature
  exact typeCompilationFuel_sufficient processType

/-- Every sufficiently fuelled fragment contains its distinguished entry state. -/
theorem compileTypeFuel_initial_mem (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
      (compileTypeFuel signature fuel processType).initial ∈
        (compileTypeFuel signature fuel processType).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => simp [compileTypeFuel, finishAutomatonFragment]
      | progress pid => simp [compileTypeFuel, finishAutomatonFragment]
      | tock => simp [compileTypeFuel, finishAutomatonFragment]
      | skip => simp [compileTypeFuel, finishAutomatonFragment]
      | var name => simp [compileTypeFuel, finishAutomatonFragment]
      | recur name body =>
          simp [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment]
      | choice left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | fairChoice bid left right =>
          simp [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment]
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hInitialOrTarget :
              (compileTypeFuel signature fuel left).initial ∈
                  (compileTypeFuel signature fuel left).states ∨
                ∃ edge ∈ (compileTypeFuel signature fuel left).edges,
                  edge.target =
                    (compileTypeFuel signature fuel left).initial :=
            Or.inl (ih left hLeft)
          simpa [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, childStates, childState] using
              hInitialOrTarget
      | par left right interface =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel ⊢
            omega
          have hLeftMem := ih left hLeft
          have hRightMem := ih right hRight
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment]
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hLeftMem, ?_⟩
          exact Finset.mem_image.mpr ⟨_, hRightMem, rfl⟩
      | xoffer elseType branches =>
          simp [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment]
      | offer elseType branches =>
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment]

/-- Every symbolic future reference produced by sufficiently fuelled
compilation points to a state declared by the same constructor fragment. -/
theorem compileTypeFuel_futureTargetsInStates
    (signature : TypeAlphabet) :
    ∀ fuel processType,
      TypeCompilationFuelSufficient processType fuel →
        (compileTypeFuel signature fuel processType).FutureTargetsInStates := by
  classical
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
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          cases hEdge with
          | inl hFirst =>
            cases hFirst with
            | inl hFiring =>
              rcases hFiring with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
            | inr hWaiting =>
              rcases hWaiting with ⟨environment, _, hEq⟩
              rw [← hEq] at hFuture
              cases hFuture
          | inr hFinal =>
            rcases hFinal with ⟨environment, _, hEq⟩
            rw [← hEq] at hFuture
            cases hFuture
      | progress pid =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with hAction | hFinal
          · rcases hAction with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
          · rcases hFinal with ⟨environment, _, hEdge⟩
            rw [← hEdge] at hFuture
            cases hFuture
      | tock =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with (⟨environment, _, hEdge⟩ |
            ⟨environment, _, hEdge⟩)
          · rw [← hEdge] at hFuture
            split at hFuture <;> cases hFuture
          · rw [← hEdge] at hFuture
            cases hFuture
      | skip =>
          intro edge hEdge target removed hFuture
          simp only [compileTypeFuel, finishAutomatonFragment,
            Finset.mem_image, Finset.mem_filter] at hEdge
          rcases hEdge with ⟨environment, _, hEdge⟩
          rw [← hEdge] at hFuture
          cases hFuture
      | var name =>
          simp [AutomatonFragment.FutureTargetsInStates, compileTypeFuel,
            finishAutomatonFragment]
      | recur name body =>
          have hBody : TypeCompilationFuelSufficient body fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildRecursionAutomaton_futureTargetsInStates signature name
            (compileTypeFuel signature fuel body) (ih body hBody)
            (compileTypeFuel_initial_mem signature fuel body hBody)
      | choice left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            TypeLabel.silent TypeLabel.silent
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | fairChoice bid left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildChoiceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel left hLeft)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | seq left right =>
          have hLeft : TypeCompilationFuelSufficient left fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hRight : TypeCompilationFuelSufficient right fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          exact buildSequenceAutomaton_futureTargetsInStates signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (ih left hLeft) (ih right hRight)
            (compileTypeFuel_initial_mem signature fuel right hRight)
      | par left right interface =>
          exact buildParallelAutomaton_futureTargetsInStates interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
      | xoffer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          apply buildExclusiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            (branches.map fun branch =>
              (branch.1, compileTypeFuel signature fuel branch.2))
          · exact ih elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply ih branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
          · exact compileTypeFuel_initial_mem signature fuel elseType hElse
          · intro entry hEntry
            simp only [List.mem_map] at hEntry
            rcases hEntry with ⟨⟨action, branchType⟩, hBranch, rfl⟩
            apply compileTypeFuel_initial_mem signature fuel branchType
            exact le_trans
              (typeCompilationFuel_le_typeBranchCompilationFuel branches
                (action, branchType) hBranch)
              hBranches
      | offer elseType branches =>
          have hElse : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hConjunction : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          exact buildConjunctiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            (compileTypeFuel signature fuel (parallelTypeBranches branches))
            (ih elseType hElse)
            (ih (parallelTypeBranches branches) hConjunction)
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (compileTypeFuel_initial_mem signature fuel
              (parallelTypeBranches branches) hConjunction)

/-- Sufficient compilation produces a pending graph closed under all
same-cycle symbolic references. -/
theorem compileTypeFuel_referencesClosed
    (signature : TypeAlphabet) (fuel : Nat) (processType : PactType)
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    ({ states := (compileTypeFuel signature fuel processType).states
       edges := (compileTypeFuel signature fuel processType).edges } :
      PendingAutomaton).ReferencesClosed := by
  exact PendingAutomaton.referencesClosed_of_futureTargetsInStates
    (compileTypeFuel signature fuel processType)
    (compileTypeFuel_futureTargetsInStates signature fuel processType hFuel)

/-- The initial state exposed by the public compiler belongs to its state set. -/
theorem compileType_initial_mem
    (signature : TypeAlphabet) (processType : PactType) :
    (compileType signature processType).initial ∈
      (compileType signature processType).states := by
  simp only [compileType, Finset.mem_union]
  left
  apply compileTypeFuel_initial_mem signature
  exact typeCompilationFuel_sufficient processType

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
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment]
      | offer_branches elseType _ branches childQ
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih (parallelTypeBranches branches) hConjunctionFuel
            childQ residual hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childStates, childState] using hChild

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

private theorem childState_mem_indexedFragmentSkipping_iff
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

private theorem root_not_mem_indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ indexedFragmentSkipping automata := by
  rw [indexedFragmentSkipping, mem_foldl_union_iff]
  rintro (hEmpty | ⟨indexed, hIndexed, hChild⟩)
  · simp at hEmpty
  · simp only [childSkipping, Finset.mem_image] at hChild
    rcases hChild with ⟨state, hState, hImpossible⟩
    cases hImpossible

private theorem child_zero_not_mem_indexedFragmentSkipping
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
          simp [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState]
      | offer_branches elseType _ branches childQ
          hChildRelated =>
          have hConjunctionFuel : TypeCompilationFuelSufficient
              (parallelTypeBranches branches) fuel := by
            rw [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranches]
            simp [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
            omega
          have hChild := ih (parallelTypeBranches branches) hConjunctionFuel
            childQ residual hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild
      | offer_else elseType _ branches childQ hChildRelated =>
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp [TypeCompilationFuelSufficient, typeCompilationFuel]
              at hFuel ⊢
            omega
          have hChild := ih elseType hElseFuel childQ residual
            hChildRelated
          simpa [compileTypeFuel, buildConjunctiveOfferAutomaton,
            finishAutomatonFragment, childSkipping, childState] using hChild

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

/-- The raw constructor-fragment form of step correspondence.  It is the
compositional interface used before the public alphabet filter is applied. -/
def CompilationFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    env ∈ signature.localEnvironments →
    (DecoratedTypeTransition env residual label offers residual' ↔
      ∃ state',
        fragment.HasResolvedEdge state env label offers state' ∧
        TypeCompilationRelation processType state' residual')

private theorem computeFuture_eq_empty_of_edges_empty
    (automaton : PendingAutomaton)
    (hEmpty : ∀ edge ∈ automaton.edges,
      edge.current = ∅ ∧ edge.future = .explicit ∅)
    (state : TypeAutomatonState) :
    computeFuture automaton state = ∅ := by
  have hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    exact ⟨∅, (hEmpty edge hEdge).2⟩
  rw [computeFuture_eq_offersAt_of_all_explicit automaton hExplicit]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  rcases hAction with ⟨edge, ⟨hEdge, _⟩, hOffer⟩
  obtain ⟨hCurrent, hFuture⟩ := hEmpty edge hEdge
  simp [hCurrent, hFuture] at hOffer

/-- Future correctness for `skip`. -/
theorem compilationFutureCorrect_skip (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .skip := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature (typeCompilationFuel .skip) .skip
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers .skip
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-- Future correctness for an atomic progress marker. -/
theorem compilationFutureCorrect_progress
    (signature : TypeAlphabet) (pid : ProcId) :
    CompilationFutureCorrect signature (.progress pid) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.progress pid)) (.progress pid)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for the clock constructor. -/
theorem compilationFutureCorrect_tock (signature : TypeAlphabet) :
    CompilationFutureCorrect signature .tock := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel .tock) .tock
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hEmpty : ∀ state, computeFuture pending state = ∅ := by
    intro state
    apply computeFuture_eq_empty_of_edges_empty pending
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hAction | hFinal
    · rcases hAction with ⟨environment, _, rfl⟩
      by_cases hClock : environment.clock = true <;>
        simp [hClock]
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨rfl, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  cases hRelated <;>
    simpa [typeFutureOffers, typeFutureOffersFuel] using hEmpty _

/-- Future correctness for an atomic message. -/
theorem compilationFutureCorrect_message
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CompilationFutureCorrect signature (.message msg dir) := by
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.message msg dir)) (.message msg dir)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  have hExplicit : ∀ edge ∈ pending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with hFiring | hWaiting | hFinal
    · rcases hFiring with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hWaiting with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
    · rcases hFinal with ⟨_, _, rfl⟩
      exact ⟨∅, rfl⟩
  intro state residual hRelated
  change computeFuture pending state = typeFutureOffers residual
  rw [computeFuture_eq_offersAt_of_all_explicit pending hExplicit]
  cases hRelated with
  | message_source =>
      ext action
      constructor
      · intro hAction
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter] at hAction
        rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
        simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hEdge
        rcases hEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hWaiting with ⟨_, _, rfl⟩
          simpa using hOffer
        · rcases hFinal with ⟨_, _, rfl⟩
          simp at hSource
      · intro hAction
        simp only [typeFutureOffers, typeFutureOffersFuel,
          Finset.mem_singleton] at hAction
        subst action
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter]
        let emptyEdge : PendingAutomatonEdge :=
          { source := .root
            environment := TypeEnvironment.empty
            label := .visible TypeLabel.silent
            current := {(msg, dir)}
            future := .explicit ∅
            target := .root }
        refine ⟨emptyEdge, ?_, ?_⟩
        · constructor
          · simp [pending, fragment, emptyEdge, typeCompilationFuel,
              compileTypeFuel, finishAutomatonFragment,
              TypeAlphabet.localEnvironments,
              TypeAlphabet.localEnvironmentActions,
              TypeEnvironment.empty, TypeEnvironment.hasNeed]
          · rfl
        · simp [emptyEdge, AutomatonConstructionLabel.semantic,
            TypeLabel.silent]
  | message_final =>
      change pending.offersAt .final = ∅
      rw [Finset.eq_empty_iff_forall_notMem]
      intro action hAction
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
      simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
        finishAutomatonFragment] at hEdge
      rcases hEdge with hFiring | hWaiting | hFinal
      · rcases hFiring with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hWaiting with ⟨_, _, rfl⟩
        simp at hSource
      · rcases hFinal with ⟨_, _, rfl⟩
        simp at hOffer

/-- Future correctness for a free-variable marker fragment. -/
theorem compilationFutureCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationFutureCorrect signature (.var name) := by
  intro state residual hRelated
  cases hRelated
  let fragment := compileTypeFuel signature
    (typeCompilationFuel (.var name)) (.var name)
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  change computeFuture pending .root = typeFutureOffers (.var name)
  rw [computeFuture_eq_offersAt_of_all_explicit pending]
  · ext action
    simp [pending, fragment, PendingAutomaton.offersAt,
      typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      typeFutureOffers, typeFutureOffersFuel]
  · intro edge hEdge
    simp [pending, fragment, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment] at hEdge
    rcases hEdge with ⟨_, _, rfl⟩
    exact ⟨∅, rfl⟩

/-! ### Parallel environment reconstruction -/

namespace TypeAlphabet

/-- Construction-local environments satisfy the same clock/disjointness
invariant as exported environments. -/
theorem localEnvironment_wellFormed {alphabet : TypeAlphabet}
    {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments) :
    environment.WellFormed := by
  simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
  · constructor
    · simp
    · intro _
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      exact (Finset.mem_sdiff.mp (hFuture hFutureMember)).2 hImmediate

/-- A construction-local clock environment is exactly the distinguished
clock environment. -/
theorem localEnvironment_eq_tock_of_clock
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hEnvironment : environment ∈ alphabet.localEnvironments)
    (hClock : environment.clock = true) :
    environment = TypeEnvironment.tock := by
  have hWellFormed := localEnvironment_wellFormed hEnvironment
  rcases hWellFormed.1 hClock with ⟨hImmediate, hFuture⟩
  cases environment
  simp_all [TypeEnvironment.tock]

/-- The future half of an exported environment cannot mention an internal
message identifier. -/
theorem environment_future_avoids_interface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments) :
    ∀ action ∈ environment.future,
      action.1 ∉ alphabet.interface := by
  simp only [environments, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    at hEnvironment
  rcases hEnvironment with rfl | ⟨immediate, _, future, hFuture, rfl⟩
  · simp [TypeEnvironment.tock]
  · intro action hAction hInterface
    have hEnvironmentAction := (Finset.mem_sdiff.mp (hFuture hAction)).1
    simp only [environmentActions, Finset.mem_image] at hEnvironmentAction
    rcases hEnvironmentAction with ⟨boundaryAction, hBoundary, hNeed⟩
    apply hAlphabet boundaryAction hBoundary
    have hMessage := congrArg Prod.fst hNeed
    simp only [typeNeed] at hMessage
    rw [hMessage]
    exact hInterface

end TypeAlphabet

private theorem hideOffers_partition (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface offers ∪ interfaceOffers interface offers = offers := by
  ext action
  simp [hideOffers, interfaceOffers]
  tauto

private theorem hideOffers_disjoint_interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) :
    Disjoint (hideOffers interface offers) (interfaceOffers interface offers) := by
  rw [Finset.disjoint_left]
  intro action hHidden hInterface
  exact (Finset.mem_filter.mp hHidden).2
    (Finset.mem_filter.mp hInterface).2

private theorem finset_eq_of_hideOffers_eq_of_interfaceOffers_eq
    (interface : Interface) {left right : Finset BareMessage}
    (hHidden : hideOffers interface left = hideOffers interface right)
    (hInterface : interfaceOffers interface left =
      interfaceOffers interface right) :
    left = right := by
  rw [← hideOffers_partition interface left,
    ← hideOffers_partition interface right, hHidden, hInterface]

private theorem hideOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left ∪ right) =
      hideOffers interface left ∪ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_union (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left ∪ right) =
      interfaceOffers interface left ∪ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem hideOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    hideOffers interface (restrictTypeOffers interface offers) = ∅ := by
  ext action
  simp [hideOffers, restrictTypeOffers]

private theorem interfaceOffers_restrictTypeOffers (interface : Interface)
    (offers : Finset BareMessage) :
    interfaceOffers interface (restrictTypeOffers interface offers) =
      restrictTypeOffers interface offers := by
  ext action
  simp [interfaceOffers, restrictTypeOffers]

private theorem hideOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    hideOffers interface (left \ right) =
      hideOffers interface left \ hideOffers interface right := by
  ext action
  simp [hideOffers]
  tauto

private theorem interfaceOffers_sdiff (interface : Interface)
    (left right : Finset BareMessage) :
    interfaceOffers interface (left \ right) =
      interfaceOffers interface left \ interfaceOffers interface right := by
  ext action
  simp [interfaceOffers]
  tauto

private theorem finset_sdiff_eq_self_of_disjoint {left right : Finset BareMessage}
    (hDisjoint : Disjoint left right) : left \ right = left := by
  ext action
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hLeft
    exact ⟨hLeft, fun hRight => Finset.disjoint_left.mp hDisjoint hLeft hRight⟩

private theorem hideOffers_eq_self_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    hideOffers interface offers = offers := by
  ext action
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hAction
    exact Finset.mem_filter.mpr ⟨hAction, hAvoids action hAction⟩

private theorem interfaceOffers_eq_empty_of_avoids
    (interface : Interface) (offers : Finset BareMessage)
    (hAvoids : ∀ action ∈ offers, action.1 ∉ interface) :
    interfaceOffers interface offers = ∅ := by
  ext action
  simp only [interfaceOffers, Finset.mem_filter]
  constructor
  · rintro ⟨hOffers, hInterface⟩
    exact (hAvoids action hOffers hInterface).elim
  · intro hEmpty
    simpa using hEmpty

/-- The exact ordinary local-environment equations reconstruct the original
outer environment after hiding the interface.  No offer-summary disjointness
is needed: the semantic future subtraction is retained verbatim. -/
private theorem combineAutomatonEnvironment_eq_of_ordinaryLocalFields
    (signature : TypeAlphabet) (interface : Interface)
    {outer leftEnvironment rightEnvironment : TypeEnvironment}
    {leftCurrent leftFuture rightCurrent rightFuture : Finset BareMessage}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hOuterClock : outer.clock = false)
    (hLeftClock : leftEnvironment.clock = false)
    (hRightClock : rightEnvironment.clock = false)
    (hLeftImmediate : leftEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightCurrent)
    (hLeftFuture : leftEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface rightFuture) \
        leftEnvironment.immediate)
    (hRightImmediate : rightEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftCurrent)
    (hRightFuture : rightEnvironment.future =
      (outer.future ∪ restrictTypeOffers interface leftFuture) \
        rightEnvironment.immediate) :
    combineAutomatonEnvironment interface leftEnvironment rightEnvironment =
      outer := by
  have hOuterWellFormed :=
    TypeAlphabet.environment_wellFormed hOuterEnvironment
  have hOuterDisjoint : Disjoint outer.future outer.immediate := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.inter_comm]
    exact hOuterWellFormed.2 hOuterClock
  have hImmediateAvoids :
      ∀ action ∈ outer.immediate, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_immediate_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hFutureAvoids :
      ∀ action ∈ outer.future, action.1 ∉ interface := by
    intro action hAction hInternal
    exact TypeAlphabet.environment_future_avoids_interface
      hAlphabet hOuterEnvironment action hAction (hInterface hInternal)
  have hHideOuterImmediate :=
    hideOffers_eq_self_of_avoids interface outer.immediate hImmediateAvoids
  have hInterfaceOuterImmediate :=
    interfaceOffers_eq_empty_of_avoids interface outer.immediate hImmediateAvoids
  have hHideOuterFuture :=
    hideOffers_eq_self_of_avoids interface outer.future hFutureAvoids
  have hHideLeftImmediate :
      hideOffers interface leftEnvironment.immediate = outer.immediate := by
    rw [hLeftImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideRightImmediate :
      hideOffers interface rightEnvironment.immediate = outer.immediate := by
    rw [hRightImmediate, hideOffers_union, hHideOuterImmediate,
      hideOffers_restrictTypeOffers, Finset.union_empty]
  have hHideLeftFuture :
      hideOffers interface leftEnvironment.future = outer.future := by
    rw [hLeftFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideLeftImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hHideRightFuture :
      hideOffers interface rightEnvironment.future = outer.future := by
    rw [hRightFuture, hideOffers_sdiff, hideOffers_union, hHideOuterFuture,
      hideOffers_restrictTypeOffers, Finset.union_empty, hHideRightImmediate]
    exact finset_sdiff_eq_self_of_disjoint hOuterDisjoint
  have hCombinedImmediate :
        hideOffers interface
            (leftEnvironment.immediate ∪ rightEnvironment.immediate) =
          outer.immediate := by
    rw [hideOffers_union, hHideLeftImmediate, hHideRightImmediate,
      Finset.union_self]
  have hCombinedFuture :
        hideOffers interface
            (leftEnvironment.future ∪ rightEnvironment.future) =
          outer.future := by
    rw [hideOffers_union, hHideLeftFuture, hHideRightFuture,
      Finset.union_self]
  cases outer with
  | mk immediate future clock =>
      cases clock
      · simp [combineAutomatonEnvironment, hLeftClock, hRightClock,
          hCombinedImmediate, hCombinedFuture]
      · simp at hOuterClock

/-- Elimination form of `LocalTypeEnvironment` exposing the exact ordinary
environment equations without losing the clock alternative. -/
private theorem LocalTypeEnvironment.clock_or_ordinary
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {interface : Interface} {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer interface siblingEnvironment sibling
      label localEnvironment) :
    (outer.clock = true ∧
        siblingEnvironment = TypeEnvironment.tock ∧
        localEnvironment = TypeEnvironment.tock) ∨
      ∃ siblingTarget current future,
        outer.clock = false ∧
        siblingEnvironment.clock = false ∧
        TypeOffers siblingEnvironment sibling label siblingTarget
          current future ∧
        localEnvironment.clock = false ∧
        localEnvironment.immediate =
          outer.immediate ∪ restrictTypeOffers interface current ∧
        localEnvironment.future =
          (outer.future ∪ restrictTypeOffers interface future) \
            localEnvironment.immediate := by
  cases hLocal with
  | clock outer interface sibling label hClock =>
      exact Or.inl ⟨hClock, rfl, rfl⟩
  | ordinary outer siblingEnvironment localEnvironment interface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      exact Or.inr ⟨siblingTarget, current, future, hOuterClock,
        hSiblingClock, hOffers, hLocalClock, hImmediate, hFuture⟩

/-- Regression: the current syntactic linearity check does not yet imply
disjoint current/future decorations.  An `offer` may expose a branch head as
current while its else continuation immediately re-offers the same message. -/
theorem sameCycleMessageLinear_offer_else_current_future_overlap :
    let action : BareMessage := ("same", .send)
    let elseType : PactType := .message action.1 action.2
    let processType : PactType := .offer elseType [(action, .skip)]
    processType.SameCycleMessageLinear ∧
      TypeOffers TypeEnvironment.empty processType TypeLabel.silent elseType
        {action} {action} ∧
      ¬ Disjoint ({action} : Finset BareMessage) {action} := by
  dsimp
  constructor
  · simp [PactType.SameCycleMessageLinear,
      PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds]
  · constructor
    · have hOffers := TypeOffers.offer_else TypeEnvironment.empty
          (.message "same" .send) [(("same", .send), .skip)] (by
            simp [TypeEnvironment.empty, TypeEnvironment.WellFormed,
              TypeNoImmediateBranch, TypeResolved, typeBranchNeeds, typeNeed])
      simpa [typeBranchActions, typeFutureOffers, typeFutureOffersFuel] using
        hOffers
    · intro hDisjoint
      have hMember : (("same", .send) : BareMessage) ∈
          ({("same", .send)} : Finset BareMessage) := by simp
      exact Finset.disjoint_left.mp hDisjoint hMember hMember

/-- Package explicitly chosen witness edges into the existential product test. -/
private theorem syncAutomatonEdges_of_witnesses
    (interface : Interface) {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hLeftWitness : leftWitness ∈ leftEdges)
    (hRightWitness : rightWitness ∈ rightEdges)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    syncAutomatonEdges interface leftEdges rightEdges left right := by
  exact ⟨leftWitness, hLeftWitness, rightWitness, hRightWitness, hSync⟩

/-- The ordinary local-environment fields, using independent witness offer
summaries, are exactly the strict witness synchronization predicate. -/
private theorem syncAutomatonEdgeWitnesses_of_ordinaryLocalFields
    (interface : Interface)
    {outer : TypeEnvironment}
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    (hOuter : combineAutomatonEnvironment interface left.environment
      right.environment = outer)
    (hLeftMatch : matchesAutomatonOfferWitness left leftWitness)
    (hRightMatch : matchesAutomatonOfferWitness right rightWitness)
    (hLeftClock : left.environment.clock = false)
    (hRightClock : right.environment.clock = false)
    (hLeftImmediate : left.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightWitness.current)
    (hLeftFuture : left.environment.future =
      (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
        left.environment.immediate)
    (hRightImmediate : right.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftWitness.current)
    (hRightFuture : right.environment.future =
      (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
        right.environment.immediate)
    (hLabelSync : TypeLabel.Sync interface left.label.semantic
      right.label.semantic) :
    syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness := by
  unfold syncAutomatonEdgeWitnesses
  simp only [hLeftClock, if_false]
  rw [hOuter]
  exact ⟨hLeftMatch, hRightMatch,
    ⟨True.intro, hRightClock, hLeftImmediate, hLeftFuture,
      hRightImmediate, hRightFuture⟩, hLabelSync⟩

/-- Realizing the offer summaries existentially stored in two semantic local
judgments as resolved witness edges yields the compiler's existential product
test.  Actual edges are used as witnesses in the clock case. -/
private theorem localTypeEnvironments_to_syncAutomatonEdges
    (signature : TypeAlphabet) (interface : Interface)
    {leftEdges rightEdges : Finset AutomatonFragmentEdge}
    {outer : TypeEnvironment} {leftEdge rightEdge : AutomatonFragmentEdge}
    {left right : PactType}
    (hAlphabet : signature.WellFormed)
    (hInterface : interface ⊆ signature.interface)
    (hOuterEnvironment : outer ∈ signature.environments)
    (hLeftEdge : leftEdge ∈ leftEdges)
    (hRightEdge : rightEdge ∈ rightEdges)
    (hLeftLocal : LocalTypeEnvironment outer interface
      rightEdge.environment right rightEdge.label.semantic
      leftEdge.environment)
    (hRightLocal : LocalTypeEnvironment outer interface
      leftEdge.environment left leftEdge.label.semantic
      rightEdge.environment)
    (hLeftRealizes :
      ∀ {target current future},
        TypeOffers leftEdge.environment left leftEdge.label.semantic target
          current future →
        ∃ witness ∈ leftEdges,
          matchesAutomatonOfferWitness leftEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hRightRealizes :
      ∀ {target current future},
        TypeOffers rightEdge.environment right rightEdge.label.semantic target
          current future →
        ∃ witness ∈ rightEdges,
          matchesAutomatonOfferWitness rightEdge witness ∧
            witness.current = current ∧ witness.future = future)
    (hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
      rightEdge.label.semantic) :
    syncAutomatonEdges interface leftEdges rightEdges leftEdge rightEdge ∧
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment = outer := by
  have hLeftCases := LocalTypeEnvironment.clock_or_ordinary hLeftLocal
  have hRightCases := LocalTypeEnvironment.clock_or_ordinary hRightLocal
  rcases hLeftCases with hClock | hOrdinary
  · rcases hClock with ⟨hOuterClock, hRightTock, hLeftTock⟩
    have hOuterLocal : outer ∈ signature.localEnvironments :=
      signature.environments_subset_localEnvironments hOuterEnvironment
    have hOuterTock := TypeAlphabet.localEnvironment_eq_tock_of_clock
      hOuterLocal hOuterClock
    have hCombined : combineAutomatonEnvironment interface
        leftEdge.environment rightEdge.environment = outer := by
      rw [hLeftTock, hRightTock, hOuterTock]
      simp [combineAutomatonEnvironment, TypeEnvironment.tock]
    constructor
    · apply syncAutomatonEdges_of_witnesses interface hLeftEdge hRightEdge
      unfold syncAutomatonEdgeWitnesses
      simp [matchesAutomatonOfferWitness, hLeftTock, hRightTock,
        hLabelSync]
      intro hFalse
      simp [TypeEnvironment.tock] at hFalse
    · exact hCombined
  · rcases hOrdinary with
      ⟨rightTarget, rightCurrent, rightFuture, hOuterClock,
        hRightClock, hRightOffers, hLeftClock, hLeftImmediate, hLeftFuture⟩
    rcases hRightCases with hClock | hOrdinary
    · rcases hClock with ⟨_, hLeftTock, hRightTock⟩
      rw [hRightTock] at hRightClock
      simp [TypeEnvironment.tock] at hRightClock
    · rcases hOrdinary with
        ⟨leftTarget, leftCurrent, leftFuture, _, hLeftClock',
          hLeftOffers, hRightClock', hRightImmediate, hRightFuture⟩
      obtain ⟨leftWitness, hLeftWitness, hLeftMatch,
          hLeftCurrent, hLeftFutureSummary⟩ := hLeftRealizes hLeftOffers
      obtain ⟨rightWitness, hRightWitness, hRightMatch,
          hRightCurrent, hRightFutureSummary⟩ := hRightRealizes hRightOffers
      rw [← hLeftCurrent] at hRightImmediate
      rw [← hLeftFutureSummary] at hRightFuture
      rw [← hRightCurrent] at hLeftImmediate
      rw [← hRightFutureSummary] at hLeftFuture
      have hCombined :=
        combineAutomatonEnvironment_eq_of_ordinaryLocalFields
          signature interface hAlphabet hInterface hOuterEnvironment
          hOuterClock hLeftClock hRightClock hLeftImmediate hLeftFuture
          hRightImmediate hRightFuture
      constructor
      · apply syncAutomatonEdges_of_witnesses interface
          hLeftWitness hRightWitness
        exact syncAutomatonEdgeWitnesses_of_ordinaryLocalFields interface
          hCombined hLeftMatch hRightMatch hLeftClock hRightClock
          hLeftImmediate hLeftFuture hRightImmediate hRightFuture hLabelSync
      · exact hCombined

/-- Strict witness synchronization reconstructs the two semantic
sibling-local environments using the witness summaries, while the actual
edges retain the product target and exposed offer summary. -/
private theorem syncAutomatonEdgeWitnesses_to_localTypeEnvironments
    (interface : Interface)
    {left right leftWitness rightWitness : AutomatonFragmentEdge}
    {leftType leftTarget rightType rightTarget : PactType}
    (hLeftOffers : TypeOffers leftWitness.environment leftType
      leftWitness.label.semantic leftTarget leftWitness.current
      leftWitness.future)
    (hRightOffers : TypeOffers rightWitness.environment rightType
      rightWitness.label.semantic rightTarget rightWitness.current
      rightWitness.future)
    (hSync : syncAutomatonEdgeWitnesses interface left right
      leftWitness rightWitness) :
    let outer := combineAutomatonEnvironment interface
      left.environment right.environment
    LocalTypeEnvironment outer interface right.environment rightType
        right.label.semantic left.environment ∧
      LocalTypeEnvironment outer interface left.environment leftType
        left.label.semantic right.environment := by
  unfold syncAutomatonEdgeWitnesses at hSync
  rcases hSync with ⟨hLeftMatch, hRightMatch, hFields, hLabelSync⟩
  rcases hLeftMatch with ⟨hLeftSource, hLeftEnvironment, hLeftLabel⟩
  rcases hRightMatch with ⟨hRightSource, hRightEnvironment, hRightLabel⟩
  rw [hLeftEnvironment, hLeftLabel] at hLeftOffers
  rw [hRightEnvironment, hRightLabel] at hRightOffers
  cases hLeftClock : left.environment.clock with
  | true =>
      simp only [hLeftClock, if_true] at hFields
      rcases hFields with ⟨hLeftTock, hRightTock⟩
      rw [hLeftTock, hRightTock]
      simp only [combineAutomatonEnvironment, TypeEnvironment.tock]
      exact ⟨LocalTypeEnvironment.clock TypeEnvironment.tock interface
          rightType right.label.semantic rfl,
        LocalTypeEnvironment.clock TypeEnvironment.tock interface
          leftType left.label.semantic rfl⟩
  | false =>
      simp only [hLeftClock, if_false] at hFields
      rcases hFields with ⟨hLeftClock', hRightClock, hLeftImmediate,
        hLeftFuture, hRightImmediate, hRightFuture⟩
      let outer := combineAutomatonEnvironment interface
        left.environment right.environment
      have hOuterClock : outer.clock = false := by
        simp [outer, combineAutomatonEnvironment, hLeftClock, hRightClock]
      change LocalTypeEnvironment outer interface right.environment rightType
          right.label.semantic left.environment ∧
        LocalTypeEnvironment outer interface left.environment leftType
          left.label.semantic right.environment
      exact ⟨
        LocalTypeEnvironment.ordinary outer right.environment left.environment
          interface rightType rightTarget right.label.semantic
          rightWitness.current rightWitness.future hOuterClock hRightClock
          hRightOffers hLeftClock hLeftImmediate hLeftFuture,
        LocalTypeEnvironment.ordinary outer left.environment right.environment
          interface leftType leftTarget left.label.semantic
          leftWitness.current leftWitness.future hOuterClock hLeftClock
          hLeftOffers hRightClock hRightImmediate hRightFuture⟩

/-- The step-for-step relation of Lemma 4.5. -/
structure TypeAutomatonCorrespondence
    (processType : PactType) (automaton : TypeAutomaton) : Type where
  relation : PactType → TypeAutomatonState → Prop
  initial : relation processType automaton.initial
  initial_mem : automaton.initial ∈ automaton.states
  stepIff :
    ∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relation residual state →
      ({ environment := env, label := label, offers := offers } :
          TypeAutomatonSymbol) ∈ automaton.alphabet →
      (DecoratedTypeTransition env residual label offers residual' ↔
        ∃ state',
          automaton.HasEdge state env label offers state' ∧
          relation residual' state')

/-- The atomic `skip` constructor already satisfies the full step correspondence. -/
theorem compileType_skip_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .skip (compileType signature .skip)) := by
  let related : PactType → TypeAutomatonState → Prop :=
    fun residual state => residual = .skip ∧ state = .root
  refine ⟨
    { relation := related
      initial := by simp [related, compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      initial_mem := by simp [compileType, typeCompilationFuel,
        compileTypeFuel, finishAutomatonFragment]
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hAlphabet
  rcases hRelated with ⟨rfl, rfl⟩
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hAlphabetParts :
        env ∈ signature.environments ∧
          label ∈ signature.labels ∧
          { current := current, future := future } ∈
            signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hAlphabet
    exact hAlphabetParts.1
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  constructor
  · rintro ⟨hTransition, hOffers⟩
    cases hTransition with
    | skip _ conditions =>
        cases hOffers with
        | skip _ _ =>
            refine ⟨.root, ?_, by simp [related]⟩
            simp only [TypeAutomaton.HasEdge]
            have hSymbol :
                { environment := env, label := TypeLabel.silent,
                  offers := { current := ∅, future := ∅ } } ∈
                    signature.transitionAlphabet := by
              simpa [compileType] using hAlphabet
            simp [compileType, typeCompilationFuel, compileTypeFuel,
              finishAutomatonFragment, resolvedAutomatonEdges]
            exact ⟨env, ⟨hLocalEnvironment, conditions.2.1,
              conditions.2.2⟩, by simp [hSymbol]⟩
  · rintro ⟨state', hEdge, hTarget⟩
    rcases hTarget with ⟨rfl, rfl⟩
    have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
    simp only [TypeAutomaton.HasEdge] at hEdge
    simp [compileType, typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, resolvedAutomatonEdges] at hEdge
    simp only [DecoratedTypeTransition]
    aesop

/-- The firing edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_action_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNeed : env.hasNeed (msg, dir))
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.message msg dir)
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      (TypeLabel.message msg dir) (TypeOfferSummary.mk {(msg, dir)} ∅)
      .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.message msg dir)
      current := {(msg, dir)}
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.message msg dir)
        current := {(msg, dir)}
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNeed]
  · simp [hSymbol]

/-- The waiting edge of an atomic message is present with its exact decoration. -/
theorem compileType_message_wait_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hNoNeed : ¬ env.hasNeed (msg, dir)) (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk {(msg, dir)} ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .root env
      TypeLabel.silent (TypeOfferSummary.mk {(msg, dir)} ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := {(msg, dir)}
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := {(msg, dir)}
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hNoNeed, hClock]
  · simp [hSymbol]

/-- The completed atomic message idles exactly like semantic `skip`. -/
theorem compileType_message_final_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.message msg dir)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.message_action_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) (TypeLabel.message msg dir)
      .skip current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.message msg dir = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.message, typeFutureOffers, typeFutureOffersFuel]

private theorem TypeOffers.message_wait_fields
    {env : TypeEnvironment} {msg : MessageId} {dir : MessageDir}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.message msg dir) TypeLabel.silent
      (.message msg dir) current future) :
    current = {(msg, dir)} ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;>
    simp_all [TypeLabel.silent, typeFutureOffers, typeFutureOffersFuel]

private theorem TypeOffers.skip_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .skip TypeLabel.silent .skip current future) :
    current = ∅ ∧ future = ∅ := by
  cases hOffers <;>
    simp_all

/-- Semantic steps of an atomic message have matching compiled edges. -/
theorem compileType_message_step_to_edge
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.message msg dir)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.message msg dir)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.message msg dir) state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | message_source =>
      cases hTransition with
      | action _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_action_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | action_wait _ _ _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.message_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.message_source msg dir⟩
          apply compileType_message_wait_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

  | message_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.message_final msg dir⟩
          apply compileType_message_final_edge signature msg dir
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_message_edge_cases
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.message msg dir)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.message msg dir ∧ current = {(msg, dir)} ∧
        future = ∅ ∧ env.hasNeed (msg, dir)) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = {(msg, dir)} ∧ future = ∅ ∧ env.clock = false ∧
        ¬ env.hasNeed (msg, dir)) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hFiring | hWaiting | hFinal
        · rcases hFiring with ⟨edgeEnv, ⟨_, hNeed⟩, rfl⟩
          simp_all
        · rcases hWaiting with ⟨edgeEnv, ⟨_, hClock, hNoNeed⟩, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic message is justified by its semantic step. -/
theorem compileType_message_edge_to_step
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.message msg dir) state residual)
    (hEdge : (compileType signature (.message msg dir)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.message msg dir) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_message_edge_cases signature msg dir hEdge
  rcases hCases with hFiring | hWaiting | hFinal
  · rcases hFiring with ⟨rfl, rfl, rfl, rfl, rfl, hNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_final =>
            refine ⟨TypeTransition.action env msg dir
              ⟨hWellFormed, hNeed⟩, ?_⟩
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action env msg dir ⟨hWellFormed, hNeed⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hNoNeed⟩
    cases hRelated with
    | message_source =>
        cases hTarget with
        | message_source =>
            refine ⟨TypeTransition.action_wait env msg dir
              ⟨hWellFormed, hNoNeed, hClock⟩, ?_⟩
            simpa [typeFutureOffers, typeFutureOffersFuel] using
              TypeOffers.action_wait env msg dir
                ⟨hWellFormed, hNoNeed, hClock⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | message_final =>
        cases hTarget with
        | message_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic message constructor satisfies the complete step correspondence. -/
theorem compileType_message_correspondence
    (signature : TypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    Nonempty (TypeAutomatonCorrespondence (.message msg dir)
      (compileType signature (.message msg dir))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.message msg dir) state residual
      initial := compileType_initial_relation signature (.message msg dir)
      initial_mem := compileType_initial_mem signature (.message msg dir)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_message_step_to_edge signature msg dir
      hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_message_edge_to_step signature msg dir
      hEnvironment hRelated hEdge hTarget

/-! ### Atomic clock correspondence -/

/-- The firing edge of an atomic clock is present with its exact decoration. -/
theorem compileType_tock_action_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = true)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.tock
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.tock
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.tock
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A non-clock environment gives an atomic clock its silent waiting edge. -/
theorem compileType_tock_wait_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .root env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .root := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .root }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .root }, ?_, by simp⟩
    simp only [typeCompilationFuel, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
    left
    refine ⟨env, hLocalEnvironment, ?_⟩
    simp [hClock]
  · simp [hSymbol]

/-- A completed atomic clock has the standard silent idle edge. -/
theorem compileType_tock_final_edge
    (signature : TypeAlphabet) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature .tock).HasEdge .final env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.tock_action_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.tock .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.tock = actualLabel at hOffers
  cases hOffers <;> simp_all

private theorem TypeOffers.tock_wait_fields
    {env : TypeEnvironment} {current future : Finset BareMessage}
    (hOffers : TypeOffers env .tock TypeLabel.silent .tock current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.silent = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic clock have matching compiled edges. -/
theorem compileType_tock_step_to_edge
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation .tock state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature .tock).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature .tock).HasEdge state env label offers state' ∧
        TypeCompilationRelation .tock state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | cycle_source =>
      cases hTransition with
      | cycle _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_action_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_action_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
      | cycle_wait _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.tock_wait_fields hOffers
          refine ⟨.root, ?_, TypeCompilationRelation.cycle_source⟩
          apply compileType_tock_wait_edge signature
          · exact hEnvironment
          · exact conditions.2
          · simpa [compileType] using hSymbol
  | cycle_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.cycle_final⟩
          apply compileType_tock_final_edge signature
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_tock_edge_cases
    (signature : TypeAlphabet)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature .tock).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧ label = TypeLabel.tock ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = true) ∨
      (source = .root ∧ target = .root ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hAction | hFinal
        · rcases hAction with ⟨edgeEnv, hLocal, rfl⟩
          by_cases hClock : edgeEnv.clock
          · left
            simp_all
          · right
            left
            simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic clock is justified by its semantic step. -/
theorem compileType_tock_edge_to_step
    (signature : TypeAlphabet)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation .tock state residual)
    (hEdge : (compileType signature .tock).HasEdge state env label offers state')
    (hTarget : TypeCompilationRelation .tock state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_tock_edge_cases signature hEdge
  rcases hCases with hAction | hWaiting | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.cycle env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle env ⟨hWellFormed, hClock⟩⟩
  · rcases hWaiting with ⟨rfl, rfl, rfl, rfl, rfl, hClock⟩
    cases hRelated with
    | cycle_source =>
        cases hTarget with
        | cycle_source =>
            exact ⟨TypeTransition.cycle_wait env ⟨hWellFormed, hClock⟩,
              TypeOffers.cycle_wait env ⟨hWellFormed, hClock⟩⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | cycle_final =>
        cases hTarget with
        | cycle_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic clock constructor satisfies the complete step correspondence. -/
theorem compileType_tock_correspondence (signature : TypeAlphabet) :
    Nonempty (TypeAutomatonCorrespondence .tock
      (compileType signature .tock)) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation .tock state residual
      initial := compileType_initial_relation signature .tock
      initial_mem := compileType_initial_mem signature .tock
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_tock_step_to_edge signature hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_tock_edge_to_step signature
      hEnvironment hRelated hEdge hTarget

/-! ### Atomic progress correspondence -/

/-- The emitting edge of an atomic progress marker is present. -/
theorem compileType_progress_action_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hSymbol : TypeAutomatonSymbol.mk env (TypeLabel.progress pid)
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .root env
      (TypeLabel.progress pid) (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .root
      environment := env
      label := .visible (TypeLabel.progress pid)
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .root
        environment := env
        label := .visible (TypeLabel.progress pid)
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment]
  · simp [hSymbol]

/-- A completed progress marker has the standard silent idle edge. -/
theorem compileType_progress_final_edge
    (signature : TypeAlphabet) (pid : ProcId) {env : TypeEnvironment}
    (hEnvironment : env ∈ signature.environments)
    (hClock : env.clock = false) (hImmediate : env.immediate = ∅)
    (hSymbol : TypeAutomatonSymbol.mk env TypeLabel.silent
      (TypeOfferSummary.mk ∅ ∅) ∈ signature.transitionAlphabet) :
    (compileType signature (.progress pid)).HasEdge .final env
      TypeLabel.silent (TypeOfferSummary.mk ∅ ∅) .final := by
  have hLocalEnvironment : env ∈ signature.localEnvironments :=
    signature.environments_subset_localEnvironments hEnvironment
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion]
  refine ⟨
    { source := .final
      environment := env
      label := .visible TypeLabel.silent
      current := ∅
      future := ∅
      target := .final }, ?_, ?_⟩
  · simp only [resolvedAutomatonEdges, Finset.mem_image]
    refine ⟨
      { source := .final
        environment := env
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }, ?_, by simp⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      hLocalEnvironment, hClock, hImmediate]
  · simp [hSymbol]

private theorem TypeOffers.progress_fields
    {env : TypeEnvironment} {pid : ProcId}
    {current future : Finset BareMessage}
    (hOffers : TypeOffers env (.progress pid) (TypeLabel.progress pid)
      .skip current future) :
    current = ∅ ∧ future = ∅ := by
  generalize hLabel : TypeLabel.progress pid = actualLabel at hOffers
  cases hOffers <;> simp_all

/-- Semantic steps of an atomic progress marker have matching compiled edges. -/
theorem compileType_progress_step_to_edge
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      (compileType signature (.progress pid)).alphabet)
    (hStep : DecoratedTypeTransition env residual label offers residual') :
    ∃ state',
      (compileType signature (.progress pid)).HasEdge state env label offers
          state' ∧
        TypeCompilationRelation (.progress pid) state' residual' := by
  rcases offers with ⟨current, future⟩
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧
          TypeOfferSummary.mk current future ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  have hTransition := hStep.1
  have hOffers := hStep.2
  cases hRelated with
  | progress_source =>
      cases hTransition with
      | progress _ _ =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.progress_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_action_edge signature pid
          · exact hEnvironment
          · simpa [compileType] using hSymbol
  | progress_final =>
      cases hTransition with
      | skip _ conditions =>
          obtain ⟨rfl, rfl⟩ := TypeOffers.skip_fields hOffers
          refine ⟨.final, ?_, TypeCompilationRelation.progress_final pid⟩
          apply compileType_progress_final_edge signature pid
          · exact hEnvironment
          · exact conditions.2.1
          · exact conditions.2.2
          · simpa [compileType] using hSymbol

private theorem compileType_progress_edge_cases
    (signature : TypeAlphabet) (pid : ProcId)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {current future : Finset BareMessage}
    (hEdge : (compileType signature (.progress pid)).HasEdge source env label
      (TypeOfferSummary.mk current future) target) :
    (source = .root ∧ target = .final ∧
        label = TypeLabel.progress pid ∧ current = ∅ ∧ future = ∅) ∨
      (source = .final ∧ target = .final ∧ label = TypeLabel.silent ∧
        current = ∅ ∧ future = ∅ ∧ env.clock = false ∧
        env.immediate = ∅) := by
  simp only [TypeAutomaton.HasEdge, compileType, Finset.mem_biUnion] at hEdge
  rcases hEdge with ⟨resolvedEdge, hResolvedEdge, hOutput⟩
  cases hLabel : resolvedEdge.label with
  | «variable» name => simp [hLabel] at hOutput
  | visible visibleLabel =>
      simp only [hLabel] at hOutput
      split at hOutput
      · simp only [Finset.mem_singleton] at hOutput
        simp only [resolvedAutomatonEdges, Finset.mem_image] at hResolvedEdge
        rcases hResolvedEdge with ⟨pendingEdge, hPendingEdge, rfl⟩
        simp [typeCompilationFuel, compileTypeFuel,
          finishAutomatonFragment] at hPendingEdge
        rcases hPendingEdge with hAction | hFinal
        · rcases hAction with ⟨edgeEnv, _, rfl⟩
          simp_all
        · rcases hFinal with ⟨edgeEnv, ⟨_, hClock, hImmediate⟩, rfl⟩
          simp_all
      · simp at hOutput

/-- Every compiled edge of an atomic progress marker has a semantic step. -/
theorem compileType_progress_edge_to_step
    (signature : TypeAlphabet) (pid : ProcId)
    {residual residual' : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hEnvironment : env ∈ signature.environments)
    (hRelated : TypeCompilationRelation (.progress pid) state residual)
    (hEdge : (compileType signature (.progress pid)).HasEdge state env label
      offers state')
    (hTarget : TypeCompilationRelation (.progress pid) state' residual') :
    DecoratedTypeTransition env residual label offers residual' := by
  have hWellFormed := TypeAlphabet.environment_wellFormed hEnvironment
  rcases offers with ⟨current, future⟩
  have hCases := compileType_progress_edge_cases signature pid hEdge
  rcases hCases with hAction | hFinal
  · rcases hAction with ⟨rfl, rfl, rfl, rfl, rfl⟩
    cases hRelated with
    | progress_source =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.progress env pid hWellFormed,
              TypeOffers.progress env pid hWellFormed⟩
  · rcases hFinal with ⟨rfl, rfl, rfl, rfl, rfl, hClock, hImmediate⟩
    cases hRelated with
    | progress_final =>
        cases hTarget with
        | progress_final =>
            exact ⟨TypeTransition.skip env
                ⟨hWellFormed, hClock, hImmediate⟩,
              TypeOffers.skip env ⟨hWellFormed, hClock, hImmediate⟩⟩

/-- The atomic progress constructor satisfies the complete correspondence. -/
theorem compileType_progress_correspondence
    (signature : TypeAlphabet) (pid : ProcId) :
    Nonempty (TypeAutomatonCorrespondence (.progress pid)
      (compileType signature (.progress pid))) := by
  refine ⟨
    { relation := fun residual state =>
        TypeCompilationRelation (.progress pid) state residual
      initial := compileType_initial_relation signature (.progress pid)
      initial_mem := compileType_initial_mem signature (.progress pid)
      stepIff := ?_ }⟩
  intro residual residual' state env label offers hRelated hSymbol
  have hEnvironment : env ∈ signature.environments := by
    have hParts : env ∈ signature.environments ∧
        label ∈ signature.labels ∧ offers ∈ signature.offerSummaries := by
      simpa [compileType, TypeAlphabet.transitionAlphabet] using hSymbol
    exact hParts.1
  constructor
  · exact compileType_progress_step_to_edge signature pid hRelated hSymbol
  · rintro ⟨state', hEdge, hTarget⟩
    exact compileType_progress_edge_to_step signature pid
      hEnvironment hRelated hEdge hTarget


end

end Pact
