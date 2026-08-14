import Anvilpp.PactTypes.Automata.CompileType

/-!
# The compiler-state/residual relation TypeCompilationRelation and its initial-state lemmas
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
  | sequence_left_entry (left right : PactType)
      (state : TypeAutomatonState) :
      -- `state` is left's own designated initial/entry position: it
      -- represents `left` itself, unstepped.  Kept by `buildSequenceAutomaton`
      -- regardless of whether `left` happens to be accepting (e.g. `.skip`).
      TypeCompilationRelation left state left →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq left right)
  | sequence_left_progressed (left right residual : PactType)
      (state : TypeAutomatonState) :
      -- Every non-accepting left state survives the redirect unconditionally.
      TypeCompilationRelation left state residual →
      residual ≠ .skip →
      TypeCompilationRelation (.seq left right) (.child 0 state)
        (.seq residual right)
  | sequence_right (left right residual : PactType)
      (state : TypeAutomatonState) :
      TypeCompilationRelation right state residual →
      TypeCompilationRelation (.seq left right) (.child 1 state) residual
  | parallel (left right leftResidual rightResidual : PactType)
      (interface : Interface) (leftState rightState : TypeAutomatonState) :
      -- Deliberately unconditional, unlike `TypeTransition.par`/`par_fuse`.
      -- This relation is a static description of what a *state* represents,
      -- not a semantic step, so it stays a plain structural recursion on
      -- `state`'s shape. When both `leftResidual`/`rightResidual` turn out to
      -- be `.skip` (exactly when both components are accepting, by
      -- `CompilationAcceptingCorrect`, proved separately by induction rather
      -- than folded into this definition), `par_fuse` supplies the one-hop
      -- `TypeTransition _ (.par .skip .skip interface) _ .skip` witness that
      -- `buildSequenceAutomaton`'s redirect needs directly from those two
      -- syntactic facts — no extra relation clause required.
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
      (selected : BareMessage × PactType) (index : Nat)
      (state : TypeAutomatonState) :
      branches[index]? = some selected →
      TypeCompilationRelation
          (parallelTypeBranchesSelecting selected branches) state residual →
      TypeCompilationRelation (.offer elseType branches)
        (.child (index + 1) state) residual
  | offer_else (elseType residual : PactType)
      (branches : List (BareMessage × PactType))
      (state : TypeAutomatonState) :
      TypeCompilationRelation elseType state residual →
      TypeCompilationRelation (.offer elseType branches) (.child 0 state) residual

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
          apply TypeCompilationRelation.sequence_left_entry
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
          simp [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
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
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          exact buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates signature
            branches (compileTypeFuel signature fuel elseType)
            selectedConjunctions (ih elseType hElse) (by
              intro entry hEntry
              simp only [selectedConjunctions, List.mem_map] at hEntry
              rcases hEntry with ⟨selected, hSelected, rfl⟩
              apply ih
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                at hFuel
              omega)
            (compileTypeFuel_initial_mem signature fuel elseType hElse)
            (by
              intro entry hEntry
              simp only [selectedConjunctions, List.mem_map] at hEntry
              rcases hEntry with ⟨selected, hSelected, rfl⟩
              apply compileTypeFuel_initial_mem
              rw [TypeCompilationFuelSufficient,
                typeCompilationFuel_parallelTypeBranchesSelecting]
              simp [TypeCompilationFuelSufficient, typeCompilationFuel]
                at hFuel
              omega)

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

end

end Pact
