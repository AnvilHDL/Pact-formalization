import Anvilpp.PactTypes.NewCorrespondence.Cases.Base
import Anvilpp.PactTypes.NewCorrespondence.Helpers.NewMainHelpers

/-!
The three helpers of Lemma 4.5 that cannot be separated: current-offer
correspondence, same-cycle completion, and the menu equation.  They are proved
by one induction on `typeCompilationFuel`, the Lean realisation of the paper's
`Rank`.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- `TypeWF_Γ(σ)`: the conjuncts of `AdmissibleType`, with closure and hygiene
taken relative to the binder context `bound` rather than the empty one, and
with the two ownership predicates that offer determinacy consumes. -/
def TypeWellFormedIn (bound : List String) (processType : PactType) : Prop :=
  processType.AlphabetWellFormed ∧
    PactType.AllVariablesBound bound processType ∧
    PactType.BinderHygienic bound processType ∧
    processType.TailClosed ∧
    PactType.ClockGuarded processType ∧
    PactType.TailRecursive processType ∧
    PactType.SameCycleMessageLinear processType ∧
    PactType.ProgressLinear processType ∧
    PactType.FairChoiceLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.ParallelProgressOwnership processType ∧
    PactType.ParallelFairChoiceOwnership processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.InterfaceAlphabetScoped processType ∧
    PactType.ConjunctiveMessageOwnership processType

/-- Progress linearity already assigns each progress identifier to a single
parallel component. -/
theorem parallelProgressOwnership_of_progressLinear :
    ∀ processType : PactType,
      PactType.ProgressLinear processType →
      PactType.ParallelProgressOwnership processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ParallelProgressOwnershipBranches branches := by
        intro branches hBranches hLinear
        induction branches with
        | nil => simp [PactType.ParallelProgressOwnershipBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.ProgressLinearBranches] at hLinear
            simp only [PactType.ParallelProgressOwnershipBranches]
            exact ⟨ih (sizeOf branchType) hType branchType rfl hLinear.1,
              hLinear.2.1, restIH hRest hLinear.2.2⟩
      intro hLinear
      cases processType with
      | skip alphabet => simp [PactType.ParallelProgressOwnership]
      | message alphabet msg dir => simp [PactType.ParallelProgressOwnership]
      | tock alphabet => simp [PactType.ParallelProgressOwnership]
      | progress alphabet pid => simp [PactType.ParallelProgressOwnership]
      | var alphabet name => simp [PactType.ParallelProgressOwnership]
      | recur alphabet name body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ih (sizeOf body) hBody body rfl hLinear
      | choice alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | fairChoice alphabet bid left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | seq alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | par alphabet left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨hLinear.2.2, ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | xoffer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩
      | offer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hLinear
          simp only [PactType.ParallelProgressOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩

/-- Fair-choice linearity already assigns each fair-choice identifier to a
single parallel component. -/
theorem parallelFairChoiceOwnership_of_fairChoiceLinear :
    ∀ processType : PactType,
      PactType.FairChoiceLinear processType →
      PactType.ParallelFairChoiceOwnership processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.ParallelFairChoiceOwnershipBranches branches := by
        intro branches hBranches hLinear
        induction branches with
        | nil => simp [PactType.ParallelFairChoiceOwnershipBranches]
        | cons head rest restIH =>
            rcases head with ⟨action, branchType⟩
            have hType : sizeOf branchType < n := by
              have hPair : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have hHead : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            have hRest : sizeOf rest < n := by
              have hTail : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by
                simp_wf; omega
              omega
            simp only [PactType.FairChoiceLinearBranches] at hLinear
            simp only [PactType.ParallelFairChoiceOwnershipBranches]
            exact ⟨ih (sizeOf branchType) hType branchType rfl hLinear.1,
              hLinear.2.1, restIH hRest hLinear.2.2⟩
      intro hLinear
      cases processType with
      | skip alphabet => simp [PactType.ParallelFairChoiceOwnership]
      | message alphabet msg dir => simp [PactType.ParallelFairChoiceOwnership]
      | tock alphabet => simp [PactType.ParallelFairChoiceOwnership]
      | progress alphabet pid => simp [PactType.ParallelFairChoiceOwnership]
      | var alphabet name => simp [PactType.ParallelFairChoiceOwnership]
      | recur alphabet name body =>
          have hBody : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ih (sizeOf body) hBody body rfl hLinear
      | choice alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | fairChoice alphabet bid left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | seq alphabet left right =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | par alphabet left right interface =>
          have hLeft : sizeOf left < n := by rw [← hSize]; simp_wf; omega
          have hRight : sizeOf right < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨hLinear.2.2, ih (sizeOf left) hLeft left rfl hLinear.1,
            ih (sizeOf right) hRight right rfl hLinear.2.1⟩
      | xoffer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩
      | offer alphabet elseType branches =>
          have hElse : sizeOf elseType < n := by rw [← hSize]; simp_wf; omega
          have hBranchSize : sizeOf branches < n := by
            rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hLinear
          simp only [PactType.ParallelFairChoiceOwnership]
          exact ⟨ih (sizeOf elseType) hElse elseType rfl hLinear.1,
            hBranches branches hBranchSize hLinear.2.1⟩

/-- An admissible type is well formed in the empty binder context. -/
theorem typeWellFormedIn_nil_of_admissible {processType : PactType}
    (hAdmissible : AdmissibleType processType) :
    TypeWellFormedIn [] processType := by
  obtain ⟨hAlphabet, hProgress, hFair, hBound, hHygienic, hClock, hTail,
    hLinear, hMsgOwn, hScoped⟩ := hAdmissible
  exact ⟨hAlphabet, hBound, hHygienic,
    PactType.tailClosed_of_allVariablesBound_nil hBound, hClock, hTail,
    hLinear, hProgress, hFair, hMsgOwn,
    parallelProgressOwnership_of_progressLinear processType hProgress,
    parallelFairChoiceOwnership_of_fairChoiceLinear processType hFair,
    hScoped⟩

/-- One public edge of `σ`'s compiled automaton, with its decoration
forgotten.  `compileType` has already deleted the private marker edges, so
this is exactly the paper's `δ_σ` viewed as a graph. -/
def AutomatonEdgeStep (processType : PactType)
    (source target : TypeAutomatonState) : Prop :=
  ∃ env label offers,
    (compileType processType).HasEdge source env label offers target

/-- The paper's side condition on a related pair: `q` is reachable from
`i_σ` in `A_σ`. -/
def AutomatonStateReachable (processType : PactType)
    (state : TypeAutomatonState) : Prop :=
  Relation.ReflTransGen (AutomatonEdgeStep processType)
    (compileType processType).initial state

/-- The entry state is reachable. -/
theorem automatonStateReachable_initial (processType : PactType) :
    AutomatonStateReachable processType (compileType processType).initial :=
  Relation.ReflTransGen.refl

/-- `AutomatonEdgeStep` forgets the decoration, so it is exactly a visible raw
edge of the constructor fragment: resolving future references rewrites no
source or target, and `compileType` deletes only the `.variable` markers. -/
theorem automatonEdgeStep_iff_fragmentEdge
    (processType : PactType) (source target : TypeAutomatonState) :
    AutomatonEdgeStep processType source target ↔
      ∃ edge ∈ (compileTypeFuel (typeCompilationFuel processType)
          processType).edges,
        edge.source = source ∧ edge.target = target ∧
          ∃ label, edge.label = AutomatonConstructionLabel.visible label := by
  constructor
  · rintro ⟨env, label, offers, hEdge⟩
    obtain ⟨edge, hMem, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge processType source target env
        label offers).mp hEdge
    exact ⟨edge, hMem, hSource, hTarget, label, hLabel⟩
  · rintro ⟨edge, hMem, hSource, hTarget, label, hLabel⟩
    refine ⟨edge.environment, label,
      { current := edge.current
        future :=
          match edge.future with
          | .explicit future => future
          | .at state removed => computeFutureOf processType state \ removed }, ?_⟩
    rw [compileType_hasEdge_iff_hasResolvedEdge]
    exact ⟨edge, hMem, hSource, rfl, hLabel, rfl, rfl, hTarget⟩

/-- Reachability descends into a child copy.  `hEnter` says that a parent edge
landing inside copy `index` either comes from that same copy and mirrors a
child edge, or lands on the child's own entry state; `hInitial` covers the
constructors whose entry state is itself inside the copy. -/
theorem automatonStateReachable_child
    {parent child : PactType} {index : Nat} {state : TypeAutomatonState}
    (hInitial : ∀ target, (compileType parent).initial = childState index target →
      target = (compileType child).initial)
    (hEnter : ∀ source target,
      AutomatonEdgeStep parent source (childState index target) →
        (∃ p, source = childState index p ∧ AutomatonEdgeStep child p target) ∨
          target = (compileType child).initial)
    (hReach : AutomatonStateReachable parent (childState index state)) :
    AutomatonStateReachable child state := by
  have hMain : ∀ reached : TypeAutomatonState,
      Relation.ReflTransGen (AutomatonEdgeStep parent)
        (compileType parent).initial reached →
      ∀ q, reached = childState index q → AutomatonStateReachable child q := by
    intro reached hPath
    induction hPath with
    | refl =>
        intro q hEq
        rw [hInitial q hEq]
        exact automatonStateReachable_initial child
    | @tail mid final _ hStep ih =>
        intro q hEq
        subst hEq
        rcases hEnter mid q hStep with ⟨p, hSource, hChildStep⟩ | hEntry
        · exact (ih p hSource).tail hChildStep
        · rw [hEntry]
          exact automatonStateReachable_initial child
  exact hMain (childState index state) hReach state rfl

/-- Current-offer correspondence: a step and an edge that carry the same
environment, label and current offer have related targets, in both directions.
The future components are left free here; they are pinned afterwards by the
uniform offer law and the menu equation. -/
def CurrentOfferCorrespondence (processType : PactType) : Prop :=
  (∀ {residual residual' : PactType} {state : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel}
      {current future : Finset BareMessage},
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual state →
      DecoratedTypeTransition env residual label
        { current := current, future := future } residual' →
      ∃ state' future',
        (compileType processType).HasEdge state env label
          { current := current, future := future' } state' ∧
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state') ∧
  (∀ {residual : PactType} {state state' : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel}
      {current future : Finset BareMessage},
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual state →
      (compileType processType).HasEdge state env label
        { current := current, future := future } state' →
      ∃ residual' future',
        DecoratedTypeTransition env residual label
          { current := current, future := future' } residual' ∧
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state')

/-- Same-cycle completion: `helper_h14_same_cycle_completion`'s conclusion. -/
def SameCycleCompletionAgrees (processType : PactType) : Prop :=
  ∀ {residual : PactType} {state : TypeAutomatonState},
    relationMembership
      (buildRelationSet processType (compileType processType))
      residual state →
    (AutomatonSameCycleReachesAccepting
        (compileTypeFuel (typeCompilationFuel processType) processType) state ↔
      TypeSameCycleCanComplete residual)

/-- Menus agree: `helper_h15_future_offers_agree`'s conclusion. -/
def FutureOffersAgree (processType : PactType) : Prop :=
  ∀ {residual : PactType} {state : TypeAutomatonState},
    relationMembership
      (buildRelationSet processType (compileType processType))
      residual state →
    computeFutureOf processType state = typeFutureOffers residual

/-! ### Base-fragment menus missing from `CompileWFHelpers` -/

/-- A two-state fragment whose only references stay inside `{a, b}` and which
offers nothing at either state has an empty menu at `a`. -/
private lemma computeFutureOfFuel_eq_empty_of_pair
    {fuel : Nat} {processType : PactType} {a b : TypeAutomatonState}
    (hFragment : PendingAutomaton)
    (hFragmentDef : hFragment =
      { states := (compileTypeFuel (fuel + 1) processType).states,
        edges := (compileTypeFuel (fuel + 1) processType).edges })
    (hClosed : ∀ state ∈ ({a, b} : Finset TypeAutomatonState),
      hFragment.referencedStates state ⊆ {a, b})
    (hOffersA : hFragment.offersAt a = ∅)
    (hOffersB : hFragment.offersAt b = ∅)
    (hProductA : stateProductInfo processType a = none)
    (hProductB : stateProductInfo processType b = none) :
    computeFutureOfFuel (fuel + 1) processType a = ∅ := by
  classical
  have hReach : hFragment.futureReachable a ⊆ ({a, b} : Finset TypeAutomatonState) :=
    hFragment.futureReachable_subset_of_reference_closed a {a, b}
      (by simp) hClosed
  simp only [computeFutureOfFuel]
  rw [← hFragmentDef]
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro action hAction
  rw [Finset.mem_filter] at hAction
  obtain ⟨hAction, -⟩ := hAction
  rw [Finset.mem_biUnion] at hAction
  obtain ⟨visited, hVisited, hMember⟩ := hAction
  have hVisitedCases := hReach hVisited
  simp only [Finset.mem_insert, Finset.mem_singleton] at hVisitedCases
  rcases hVisitedCases with rfl | rfl
  · rw [hOffersA, hProductA] at hMember; simp at hMember
  · rw [hOffersB, hProductB] at hMember; simp at hMember

/-- A progress fragment publishes no message action: its firing edge and its
final idle loop both carry an empty current offer. -/
lemma computeFutureOf_progress_root
    {alphabet : PactTypeAlphabet} (pid : ProcId) :
    computeFutureOf (.progress alphabet pid) .root = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.progress alphabet pid))
    (.progress alphabet pid) .root = ∅
  simp only [typeCompilationFuel]
  refine computeFutureOfFuel_eq_empty_of_pair
    (a := TypeAutomatonState.root) (b := TypeAutomatonState.final)
    { states := (compileTypeFuel 1 (.progress alphabet pid)).states,
      edges := (compileTypeFuel 1 (.progress alphabet pid)).edges }
    rfl ?_ ?_ ?_ ?_ ?_
  · intro state _ reference hReference
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hReference⟩ := hReference
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩ <;>
      · rw [← hEq] at hReference
        simp only [AutomatonConstructionLabel.semantic, TypeLabel.progress,
          TypeLabel.silent, TypeLabel.tock] at hReference
        simp_all
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hAction⟩ := hAction
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩ <;>
      · rw [← hEq] at hAction
        simp [AutomatonConstructionLabel.semantic, TypeLabel.progress,
          TypeLabel.silent, TypeLabel.tock] at hAction
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hAction⟩ := hAction
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩ <;>
      · rw [← hEq] at hAction
        simp [AutomatonConstructionLabel.semantic, TypeLabel.progress,
          TypeLabel.silent, TypeLabel.tock] at hAction
  · simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  · simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]

/-- A variable fragment publishes no message action: its only edge is the
private marker, which carries an empty current offer and points at an inert
private state. -/
lemma computeFutureOf_var_root
    {alphabet : PactTypeAlphabet} (name : String) :
    computeFutureOf (.var alphabet name) .root = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.var alphabet name))
    (.var alphabet name) .root = ∅
  simp only [typeCompilationFuel]
  refine computeFutureOfFuel_eq_empty_of_pair
    (a := TypeAutomatonState.root) (b := TypeAutomatonState.final)
    { states := (compileTypeFuel 1 (.var alphabet name)).states,
      edges := (compileTypeFuel 1 (.var alphabet name)).edges }
    rfl ?_ ?_ ?_ ?_ ?_
  · intro state _ reference hReference
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hReference⟩ := hReference
    obtain ⟨_, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hReference
    simp only [AutomatonConstructionLabel.semantic, TypeLabel.silent,
      TypeLabel.tock] at hReference
    simp_all
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hAction⟩ := hAction
    obtain ⟨_, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hAction
    simp [AutomatonConstructionLabel.semantic, TypeLabel.silent,
      TypeLabel.tock] at hAction
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
    obtain ⟨_, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hSource
    simp at hSource
  · simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  · simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]

/-- When the action a message fragment carries is not declared by its own
alphabet, the compiler's gate removes both root families, so the root menu is
empty — matching the semantic gate. -/
lemma computeFutureOf_message_root_of_not_declared
    {alphabet : PactTypeAlphabet} (msg : MessageId) (dir : MessageDir)
    (hDeclared : (msg, dir) ∉ alphabet.actions) :
    computeFutureOf (.message alphabet msg dir) .root = ∅ := by
  classical
  show computeFutureOfFuel
    (typeCompilationFuel (.message alphabet msg dir))
    (.message alphabet msg dir) .root = ∅
  simp only [typeCompilationFuel, computeFutureOfFuel]
  have hReferences :
      ({ states := (compileTypeFuel 1 (.message alphabet msg dir)).states,
          edges := (compileTypeFuel 1 (.message alphabet msg dir)).edges } :
        PendingAutomaton).referencedStates .root ⊆
        {TypeAutomatonState.root} := by
    simp only [PendingAutomaton.referencedStates, compileTypeFuel,
      finishAutomatonFragment]
    intro reference hReference
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_union,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hReference⟩ := hReference
    rcases hEdgeMem with (⟨_, ⟨-, -, hAction⟩, hEq⟩ | ⟨_, ⟨-, -, -, hAction⟩, hEq⟩) |
      ⟨_, -, hEq⟩
    · exact absurd hAction hDeclared
    · exact absurd hAction hDeclared
    · rw [← hEq] at hSource; simp at hSource
  rw [futureReachable_eq_singleton_of_referencedStates_subset_self _ _
    hReferences, Finset.singleton_biUnion]
  have hNoProduct :
      stateProductInfo (.message alphabet msg dir)
        TypeAutomatonState.root = none := by
    simp [stateProductInfo, stateProductInfoFuel, typeCompilationFuel]
  rw [hNoProduct]
  simp only [Finset.union_empty]
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro action hAction
  rw [Finset.mem_filter] at hAction
  obtain ⟨hAction, -⟩ := hAction
  simp only [PendingAutomaton.offersAt, compileTypeFuel,
    finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_union, Finset.mem_image] at hAction
  obtain ⟨edge, ⟨hEdgeMem, hSource⟩, hAction⟩ := hAction
  rcases hEdgeMem with (⟨_, ⟨-, -, hDecl⟩, hEq⟩ | ⟨_, ⟨-, -, -, hDecl⟩, hEq⟩) |
    ⟨_, -, hEq⟩
  · exact absurd hDecl hDeclared
  · exact absurd hDecl hDeclared
  · rw [← hEq] at hSource; simp at hSource

/-! ### Menus agree at the base fragments -/

lemma futureOffersAgree_skip (alphabet : PactTypeAlphabet) :
    FutureOffersAgree (.skip alphabet) := by
  intro residual state hRelated
  obtain ⟨hResidual, hState⟩ := relationMembership_skip_cases alphabet hRelated
  subst hResidual; subst hState
  rw [computeFutureOf_skip_root]
  simp [typeFutureOffers, typeFutureOffersFuel]

lemma futureOffersAgree_var (alphabet : PactTypeAlphabet) (name : String) :
    FutureOffersAgree (.var alphabet name) := by
  intro residual state hRelated
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  obtain ⟨hResidual, hState⟩ := hRelated
  subst hResidual; subst hState
  rw [computeFutureOf_var_root]
  simp [typeFutureOffers, typeFutureOffersFuel]

lemma futureOffersAgree_tock (alphabet : PactTypeAlphabet) :
    FutureOffersAgree (.tock alphabet) := by
  intro residual state hRelated
  rcases relationMembership_tock_cases alphabet hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · rw [computeFutureOf_tock_root]
    simp [typeFutureOffers, typeFutureOffersFuel]
  · rw [computeFutureOf_tock_final]
    simp [typeFutureOffers, typeFutureOffersFuel]

lemma futureOffersAgree_progress (alphabet : PactTypeAlphabet) (pid : ProcId) :
    FutureOffersAgree (.progress alphabet pid) := by
  intro residual state hRelated
  rcases relationMembership_progress_cases alphabet pid hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · rw [computeFutureOf_progress_root]
    simp [typeFutureOffers, typeFutureOffersFuel]
  · rw [computeFutureOf_progress_final]
    simp [typeFutureOffers, typeFutureOffersFuel]

lemma futureOffersAgree_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    FutureOffersAgree (.message alphabet msg dir) := by
  intro residual state hRelated
  rcases relationMembership_message_cases alphabet msg dir hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · by_cases hDeclared : (msg, dir) ∈ alphabet.actions
    · rw [computeFutureOf_message_root msg dir hDeclared]
      simp [typeFutureOffers, typeFutureOffersFuel, hDeclared]
    · rw [computeFutureOf_message_root_of_not_declared msg dir hDeclared]
      simp [typeFutureOffers, typeFutureOffersFuel, hDeclared]
  · rw [computeFutureOf_message_final msg dir]
    simp [typeFutureOffers, typeFutureOffersFuel]

/-- Every branch continuation of an offer inherits `TypeWF_Γ`.  One list
induction discharges all thirteen conjuncts at once. -/
private lemma branchesWellFormedIn_of_conjuncts {bound : List String}
    (branches : List (BareMessage × PactType))
    (hA : ∀ entry ∈ branches, PactType.AlphabetWellFormed entry.2)
    (hB : PactType.AllBranchVariablesBound bound branches)
    (hH : PactType.BinderHygienicBranches bound branches)
    (hTC : ∀ other : String, PactType.TailBranchOccurrences other True branches)
    (hCG : PactType.ClockGuardedBranches branches)
    (hTR : PactType.TailRecursiveBranches branches)
    (hSC : PactType.SameCycleMessageLinearBranches branches)
    (hPL : PactType.ProgressLinearBranches branches)
    (hFL : PactType.FairChoiceLinearBranches branches)
    (hMO : ∀ entry ∈ branches, PactType.ParallelMessageOwnership entry.2)
    (hPO : PactType.ParallelProgressOwnershipBranches branches)
    (hFO : PactType.ParallelFairChoiceOwnershipBranches branches)
    (hIS : PactType.InterfaceScopedBranches branches)
    (hIAS : PactType.InterfaceAlphabetScopedBranches branches)
    (hCMO : ∀ entry ∈ branches, PactType.ConjunctiveMessageOwnership entry.2) :
    ∀ entry ∈ branches, TypeWellFormedIn bound entry.2 := by
  induction branches with
  | nil => intro entry hEntry; cases hEntry
  | cons head rest ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.AllBranchVariablesBound] at hB
      simp only [PactType.BinderHygienicBranches] at hH
      simp only [PactType.ClockGuardedBranches] at hCG
      simp only [PactType.TailRecursiveBranches] at hTR
      simp only [PactType.SameCycleMessageLinearBranches] at hSC
      simp only [PactType.ProgressLinearBranches] at hPL
      simp only [PactType.FairChoiceLinearBranches] at hFL
      simp only [PactType.ParallelProgressOwnershipBranches] at hPO
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFO
      simp only [PactType.InterfaceScopedBranches] at hIS
      simp only [PactType.InterfaceAlphabetScopedBranches] at hIAS
      have hTCsplit : ∀ other : String,
          PactType.TailOccurrences other True branchType ∧
            PactType.TailBranchOccurrences other True rest := by
        intro other
        simpa only [PactType.TailBranchOccurrences] using hTC other
      intro entry hEntry
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · exact ⟨hA _ (by simp), hB.1, hH.1,
          fun other => (hTCsplit other).1, hCG.1, hTR.1, hSC.1, hPL.1, hFL.1,
          hMO _ (by simp), hPO.1, hFO.1, hIS.1, hIAS.1, hCMO _ (by simp)⟩
      · exact ih (fun e hE => hA e (by simp [hE])) hB.2 hH.2
          (fun other => (hTCsplit other).2) hCG.2 hTR.2 hSC.2.2 hPL.2.2 hFL.2.2
          (fun e hE => hMO e (by simp [hE])) hPO.2.2 hFO.2.2 hIS.2 hIAS.2
          (fun e hE => hCMO e (by simp [hE])) entry hRest

lemma typeWellFormedIn_xoffer {bound : List String}
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : TypeWellFormedIn bound (.xoffer alphabet elseType branches)) :
    TypeWellFormedIn bound elseType ∧
      ∀ entry ∈ branches, TypeWellFormedIn bound entry.2 := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hTCsplit : ∀ other : String,
      PactType.TailOccurrences other True elseType ∧
        PactType.TailBranchOccurrences other True branches := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hBranchAlphabet : ∀ entry ∈ branches,
      PactType.AlphabetWellFormed entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.BranchesAlphabetWellFormed alphabet list →
        ∀ entry ∈ list, PactType.AlphabetWellFormed entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.BranchesAlphabetWellFormed] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.2.1
          · exact ihList hList.2.2 entry hTail
    exact hAux branches hA.2.2.2
  have hBranchOwnership : ∀ entry ∈ branches,
      PactType.ParallelMessageOwnership entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ParallelMessageOwnershipBodies list →
        ∀ entry ∈ list, PactType.ParallelMessageOwnership entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.ParallelMessageOwnershipBodies] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 entry hTail
    exact hAux branches hMO.2
  have hBranchConjunctive : ∀ entry ∈ branches,
      PactType.ConjunctiveMessageOwnership entry.2 := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ConjunctiveMessageOwnershipBodies list →
        ∀ entry ∈ list, PactType.ConjunctiveMessageOwnership entry.2 := by
      intro list
      induction list with
      | nil => intro _ entry hEntry; cases hEntry
      | cons head tail ihList =>
          rcases head with ⟨headAction, headType⟩
          intro hList entry hEntry
          simp only [PactType.ConjunctiveMessageOwnershipBodies] at hList
          simp only [List.mem_cons] at hEntry
          rcases hEntry with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 entry hTail
    exact hAux branches hCMO.2
  exact ⟨⟨hA.2.2.1, hB.1, hH.1, fun other => (hTCsplit other).1, hCG.1, hTR.1,
      hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1, hCMO.1⟩,
    branchesWellFormedIn_of_conjuncts branches hBranchAlphabet hB.2 hH.2
      (fun other => (hTCsplit other).2) hCG.2 hTR.2 hSC.2.1 hPL.2.1 hFL.2.1
      hBranchOwnership hPO.2 hFO.2 hIS.2 hIAS.2.2 hBranchConjunctive⟩

/-! ### Same-cycle completion at the base fragments

These five are `helper_h14_same_cycle_completion`'s own base cases, restated
as standalone lemmas so that the simultaneous induction can use them without
re-entering that theorem's `sizeOf` induction. -/

lemma sameCycleCompletionAgrees_skip (alphabet : PactTypeAlphabet) :
    SameCycleCompletionAgrees (.skip alphabet) := by
  intro residual state hRelated
  obtain ⟨hResidual, hState⟩ := relationMembership_skip_cases alphabet hRelated
  subst hResidual; subst hState
  constructor
  · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
  · intro _
    refine ⟨TypeAutomatonState.root, Relation.ReflTransGen.refl, ?_⟩
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]

lemma sameCycleCompletionAgrees_var (alphabet : PactTypeAlphabet)
    (name : String) :
    SameCycleCompletionAgrees (.var alphabet name) := by
  intro residual state hRelated
  unfold relationMembership buildRelationSet buildRelationSetCore at hRelated
  simp only [typeCompilationFuel, buildRelationSetCoreFuel,
    Finset.mem_singleton, Prod.mk.injEq] at hRelated
  obtain ⟨hResidual, hState⟩ := hRelated
  subst hResidual; subst hState
  constructor
  · rintro ⟨finalState, -, hFinal⟩
    exfalso
    simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
      at hFinal
  · rintro ⟨_, hReaches⟩
    exfalso
    exact absurd (Relation.ReflTransGen.cases_head hReaches) (by
      rintro (h | ⟨c, ⟨env, label, hTrans, -⟩, -⟩)
      · exact nomatch h
      · cases hTrans)

lemma sameCycleCompletionAgrees_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    SameCycleCompletionAgrees (.message alphabet msg dir) := by
  intro residual state hRelated
  set env : TypeEnvironment :=
    { immediate := {(msg, dir.invert)}, future := ∅, clock := false } with hEnvDef
  have hHasNeed : env.hasNeed (msg, dir) := by
    simp [TypeEnvironment.hasNeed, hEnvDef]
  have hRootStepDeclared : ∀ {target : TypeAutomatonState},
      AutomatonNonClockStep (compileTypeFuel
        (typeCompilationFuel (.message alphabet msg dir))
        (.message alphabet msg dir)) TypeAutomatonState.root target →
      (msg, dir) ∈ alphabet.actions := by
    intro target hStep
    obtain ⟨edge, hEdge, hSource, -, -⟩ := hStep
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with (⟨environment, ⟨-, -, hAction⟩, hEq⟩ |
        ⟨environment, ⟨-, -, -, hAction⟩, hEq⟩) | ⟨environment, -, hEq⟩
    · exact hAction
    · exact hAction
    · rw [← hEq] at hSource
      simp at hSource
  rcases relationMembership_message_cases alphabet msg dir hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · constructor
    · rintro ⟨finalState, hReach, hFinal⟩
      rcases Relation.ReflTransGen.cases_head hReach with rfl | ⟨mid, hStep, -⟩
      · exact absurd hFinal (by
          simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment])
      have hAction : (msg, dir) ∈ alphabet.actions := hRootStepDeclared hStep
      have hWF : env.WellFormed alphabet := by
        refine ⟨by simp [hEnvDef], by simp [hEnvDef], ?_, by simp [hEnvDef]⟩
        simpa [hEnvDef, typeNeed] using
          Finset.mem_image_of_mem typeNeed hAction
      exact ⟨alphabet, Relation.ReflTransGen.single ⟨env, _,
        TypeTransition.action env alphabet msg dir ⟨hWF, hHasNeed⟩ hAction,
        by simp [TypeLabel.isTock, TypeLabel.message]⟩⟩
    · rintro ⟨targetAlphabet, hReaches⟩
      have hDeclared : (msg, dir) ∈ alphabet.actions := by
        rcases Relation.ReflTransGen.cases_head hReaches with h |
          ⟨mid, ⟨env', label, hTrans, -⟩, -⟩
        · exact nomatch h
        · cases hTrans with
          | action _ _ _ _ _ hAction => exact hAction
          | action_wait _ _ _ _ _ hAction => exact hAction
      have hEnvMem := firing_environment_mem_localEnvironmentsFor
        alphabet msg dir hDeclared
      rw [← hEnvDef] at hEnvMem
      set edge : PendingAutomatonEdge :=
        { source := TypeAutomatonState.root, environment := env,
          label := AutomatonConstructionLabel.visible (TypeLabel.message msg dir),
          current := {(msg, dir)}, future := FutureSpec.at TypeAutomatonState.final ∅,
          target := TypeAutomatonState.final } with hEdgeDef
      have hEdgeMem : edge ∈
          (compileTypeFuel (typeCompilationFuel (.message alphabet msg dir))
            (.message alphabet msg dir)).edges := by
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        exact Or.inl (Or.inl ⟨env, ⟨hEnvMem, hHasNeed, hDeclared⟩, hEdgeDef.symm⟩)
      refine ⟨TypeAutomatonState.final,
        Relation.ReflTransGen.single ⟨edge, hEdgeMem, rfl, rfl, ?_⟩, ?_⟩
      · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
          TypeLabel.message]
      · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  · constructor
    · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
    · intro _
      refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
      simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]

lemma sameCycleCompletionAgrees_tock (alphabet : PactTypeAlphabet) :
    SameCycleCompletionAgrees (.tock alphabet) := by
  intro residual state hRelated
  rcases relationMembership_tock_cases alphabet hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · have hTockStays : ∀ ρ', TypeSameCycleReaches (.tock alphabet) ρ' →
        ρ' = .tock alphabet := by
      intro ρ' hPath
      induction hPath with
      | refl => rfl
      | tail _ hbc ih =>
          rw [ih] at hbc
          obtain ⟨env, label, hTrans, hNotTock⟩ := hbc
          cases hTrans with
          | cycle env hCond => exact absurd (by simp [TypeLabel.isTock]) hNotTock
          | cycle_wait env hCond => rfl
    have hAutoStays : ∀ q, Relation.ReflTransGen
        (AutomatonNonClockStep
          (compileTypeFuel (typeCompilationFuel (.tock alphabet))
            (.tock alphabet)))
        TypeAutomatonState.root q → q = TypeAutomatonState.root := by
      intro q hR
      induction hR with
      | refl => rfl
      | tail _ hbc ih =>
          rw [ih] at hbc
          obtain ⟨edge, hMem, hSource, hTarget, hNotTock⟩ := hbc
          simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
            Finset.mem_union, Finset.mem_image] at hMem
          rcases hMem with ⟨env, -, hEq⟩ | ⟨env, -, hEq⟩
          · rw [← hEq] at hSource hTarget hNotTock
            split at hSource <;> split at hTarget <;> split at hNotTock <;>
              simp_all [AutomatonConstructionLabel.semantic, TypeLabel.isTock]
          · rw [← hEq] at hSource
            simp at hSource
    constructor
    · rintro ⟨finalState, hReach, hFinal⟩
      rw [hAutoStays finalState hReach] at hFinal
      simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment] at hFinal
    · rintro ⟨targetAlphabet, hReaches⟩
      exact absurd (hTockStays (.skip targetAlphabet) hReaches) (by simp)
  · constructor
    · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
    · intro _
      refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
      simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]

lemma sameCycleCompletionAgrees_progress (alphabet : PactTypeAlphabet)
    (pid : ProcId) :
    SameCycleCompletionAgrees (.progress alphabet pid) := by
  intro residual state hRelated
  rcases relationMembership_progress_cases alphabet pid hRelated with
    ⟨hResidual, hState⟩ | ⟨hResidual, hState⟩ <;> subst hResidual <;> subst hState
  · constructor
    · intro _
      have hEnv : TypeEnvironment.empty.WellFormed alphabet := by
        simp [TypeEnvironment.WellFormed, TypeEnvironment.empty]
      exact ⟨alphabet, Relation.ReflTransGen.single ⟨TypeEnvironment.empty, _,
        TypeTransition.progress TypeEnvironment.empty alphabet pid hEnv rfl,
        by simp [TypeLabel.isTock, TypeLabel.progress]⟩⟩
    · intro _
      have hEmptyLocal : TypeEnvironment.empty ∈
          alphabet.localEnvironments := by
        simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
        exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
      set edge : PendingAutomatonEdge :=
        { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
          label := AutomatonConstructionLabel.visible (TypeLabel.progress pid),
          current := ∅, future := FutureSpec.at TypeAutomatonState.final ∅,
          target := TypeAutomatonState.final } with hEdgeDef
      have hEdgeMem : edge ∈
          (compileTypeFuel (typeCompilationFuel (.progress alphabet pid))
            (.progress alphabet pid)).edges := by
        simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image, Finset.mem_filter]
        exact Or.inl ⟨TypeEnvironment.empty, ⟨hEmptyLocal, rfl⟩, hEdgeDef.symm⟩
      refine ⟨TypeAutomatonState.final,
        Relation.ReflTransGen.single ⟨edge, hEdgeMem, rfl, rfl, ?_⟩, ?_⟩
      · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
          TypeLabel.progress]
      · simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]
  · constructor
    · intro _; exact ⟨alphabet, Relation.ReflTransGen.refl⟩
    · intro _
      refine ⟨TypeAutomatonState.final, Relation.ReflTransGen.refl, ?_⟩
      simp [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment]

/-! ### Recovering the transition-alphabet guard where it is needed

The paper's `<current-offer-correspondence>` carries no alphabet guard, so
`CurrentOfferCorrespondence` does not either.  `StepIffStatement` does, so the
base cases — which are proved in that form — need the guard supplied rather
than assumed.  It is available: a semantic step's environment is well formed
over the type's own alphabet, and well-formedness is exactly membership in
`localEnvironments`. -/

theorem PactTypeAlphabet.mem_localEnvironments_of_wellFormed
    {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) :
    env ∈ alphabet.localEnvironments := by
  classical
  obtain ⟨hClock, hNonClock, hImmediate, hFuture⟩ := hWF
  simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image]
  cases hEnvClock : env.clock with
  | true =>
      obtain ⟨hI, hF⟩ := hClock hEnvClock
      refine Or.inl ?_
      rcases env with ⟨immediate, future, clock⟩
      simp only at hI hF hEnvClock
      simp [TypeEnvironment.tock, hI, hF, hEnvClock]
  | false =>
      refine Or.inr ⟨env.immediate, hImmediate, env.future, ?_, ?_⟩
      · intro action hAction
        refine Finset.mem_sdiff.mpr ⟨hFuture hAction, ?_⟩
        intro hImm
        have hDisjoint := hNonClock hEnvClock
        have : action ∈ env.immediate ∩ env.future :=
          Finset.mem_inter.mpr ⟨hImm, hAction⟩
        rw [hDisjoint] at this
        exact absurd this (by simp)
      · rcases env with ⟨immediate, future, clock⟩
        simp only at hEnvClock
        simp [hEnvClock]

private lemma mem_transitionAlphabet_of
    {processType : PactType} {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hEnv : env ∈ processType.alphabet.localEnvironments)
    (_hLabel : label ∈ processType.labels)
    (hOffers : offers ∈ processType.alphabet.localOfferSummaries) :
    SymbolGuard processType env offers :=
  ⟨hEnv, hOffers⟩

private lemma mem_localOfferSummaries_of_subset
    {alphabet : PactTypeAlphabet} {current future : Finset BareMessage}
    (hCurrent : current ⊆ alphabet.actions) (hFuture : future ⊆ alphabet.actions) :
    ({ current := current, future := future } : TypeOfferSummary) ∈
      alphabet.localOfferSummaries := by
  classical
  simp only [PactTypeAlphabet.localOfferSummaries, Finset.mem_biUnion,
    Finset.mem_powerset, Finset.mem_image]
  exact ⟨current, hCurrent, future, hFuture, rfl⟩

private lemma silent_mem_labels (processType : PactType) :
    TypeLabel.silent ∈ processType.labels := by
  classical
  simp only [PactType.labels, TypeLabel.silent, Finset.mem_union,
    Finset.mem_image, Finset.mem_powerset]
  exact Or.inl ⟨∅, Finset.empty_subset _, rfl⟩

private lemma tock_mem_labels (processType : PactType) :
    TypeLabel.tock ∈ processType.labels := by
  simp [PactType.labels]

private lemma message_mem_labels {processType : PactType}
    {msg : MessageId} {dir : MessageDir}
    (hDeclared : (msg, dir) ∈ processType.alphabet.actions) :
    TypeLabel.message msg dir ∈ processType.labels := by
  classical
  simp only [PactType.labels, TypeLabel.message, Finset.mem_union,
    Finset.mem_image, Finset.mem_powerset]
  refine Or.inl ⟨{TypeObservation.message msg dir}, ?_, rfl⟩
  intro observation hObservation
  simp only [Finset.mem_singleton] at hObservation
  subst hObservation
  simp only [PactType.observations, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inl (Or.inl ⟨(msg, dir),
    Finset.mem_union_left _ hDeclared, rfl⟩))

private lemma progress_mem_labels {processType : PactType} {pid : ProcId}
    (hDeclared : pid ∈ PactType.ProgressIds processType) :
    TypeLabel.progress pid ∈ processType.labels := by
  classical
  simp only [PactType.labels, TypeLabel.progress, Finset.mem_union,
    Finset.mem_image, Finset.mem_powerset]
  refine Or.inl ⟨{TypeObservation.progress pid}, ?_, rfl⟩
  intro observation hObservation
  simp only [Finset.mem_singleton] at hObservation
  subst hObservation
  simp only [PactType.observations, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨pid, hDeclared, rfl⟩)

/-- Every compiled edge of a base fragment draws its environment from the
fragment's own local environments: each edge family is an image of a filtered
`localEnvironments`. -/
private lemma compileType_base_edge_env_mem
    {processType : PactType} {source target : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hFamilies : ∀ edge ∈ (compileTypeFuel (typeCompilationFuel processType)
        processType).edges, edge.environment ∈ processType.alphabet.localEnvironments)
    (hEdge : (compileType processType).HasEdge source env label offers target) :
    env ∈ processType.alphabet.localEnvironments := by
  classical
  obtain ⟨edge, hPending, hSource, hEnv, hLabel, hCurrent, hFuture, hTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge processType source target env label
      offers).mp hEdge
  rw [← hEnv]
  exact hFamilies edge hPending

private lemma skip_edge_families (alphabet : PactTypeAlphabet) :
    ∀ edge ∈ (compileTypeFuel (typeCompilationFuel (.skip alphabet))
      (.skip alphabet)).edges,
      edge.environment ∈ (PactType.skip alphabet).alphabet.localEnvironments := by
  intro edge hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image, Finset.mem_filter] at hEdge
  obtain ⟨environment, ⟨hLocal, -⟩, hEq⟩ := hEdge
  rw [← hEq]; exact hLocal

private lemma message_edge_families (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    ∀ edge ∈ (compileTypeFuel (typeCompilationFuel (.message alphabet msg dir))
      (.message alphabet msg dir)).edges,
      edge.environment ∈
        (PactType.message alphabet msg dir).alphabet.localEnvironments := by
  intro edge hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (⟨environment, ⟨hLocal, -⟩, hEq⟩ |
      ⟨environment, ⟨hLocal, -⟩, hEq⟩) | ⟨environment, ⟨hLocal, -⟩, hEq⟩ <;>
    · rw [← hEq]; exact hLocal

private lemma tock_edge_families (alphabet : PactTypeAlphabet) :
    ∀ edge ∈ (compileTypeFuel (typeCompilationFuel (.tock alphabet))
      (.tock alphabet)).edges,
      edge.environment ∈ (PactType.tock alphabet).alphabet.localEnvironments := by
  intro edge hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨environment, hLocal, hEq⟩ | ⟨environment, ⟨hLocal, -⟩, hEq⟩
  · rw [← hEq]; split <;> exact hLocal
  · rw [← hEq]; exact hLocal

private lemma progress_edge_families (alphabet : PactTypeAlphabet)
    (pid : ProcId) :
    ∀ edge ∈ (compileTypeFuel (typeCompilationFuel (.progress alphabet pid))
      (.progress alphabet pid)).edges,
      edge.environment ∈
        (PactType.progress alphabet pid).alphabet.localEnvironments := by
  intro edge hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨environment, ⟨hLocal, -⟩, hEq⟩ |
      ⟨environment, ⟨hLocal, -⟩, hEq⟩ <;>
    · rw [← hEq]; exact hLocal

private lemma compileType_message_root_edge_declared
    {alphabet : PactTypeAlphabet} (msg : MessageId) (dir : MessageDir)
    {target : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary}
    (hEdge : (compileType (.message alphabet msg dir)).HasEdge
      TypeAutomatonState.root env label offers target) :
    (msg, dir) ∈ alphabet.actions := by
  classical
  obtain ⟨edge, hPending, hSource, -, -, -, -, -⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.message alphabet msg dir)
      TypeAutomatonState.root target env label offers).mp hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hPending
  rcases hPending with (⟨environment, ⟨-, -, hA⟩, hEq⟩ |
      ⟨environment, ⟨-, -, -, hA⟩, hEq⟩) | ⟨environment, -, hEq⟩
  · exact hA
  · exact hA
  · rw [← hEq] at hSource; simp at hSource

/-- The shape of the guard obligation the base cases must discharge: the
symbol carried by an actual step, or by an actual edge, lies in the fixed
transition alphabet.  This is recoverable exactly because every base rule and
every base edge family carries its own declaration gate. -/
def BaseGuard (processType : PactType) : Prop :=
  ∀ {residual : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership
      (buildRelationSet processType (compileType processType)) residual state →
    ((∃ target, DecoratedTypeTransition env residual label offers target) ∨
      (∃ state', (compileType processType).HasEdge state env label offers
        state')) →
    SymbolGuard processType env offers

private lemma skip_guard (alphabet : PactTypeAlphabet) :
    BaseGuard (.skip alphabet) := by
  intro residual state env label offers hRelated hCase
  rcases offers with ⟨current, future⟩
  obtain ⟨hR, hS⟩ := relationMembership_skip_cases alphabet hRelated
  subst hR; subst hS
  rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
  · cases hOffers with
    | skip _ _ cond =>
        refine mem_transitionAlphabet_of
          (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
          (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) ?_)
        simp [typeFutureOffers, typeFutureOffersFuel]
  · obtain ⟨-, -, hLabel, hCurrent, hFuture, -⟩ :=
      compileType_skip_edge_cases hEdge
    subst hLabel; subst hCurrent; subst hFuture
    exact mem_transitionAlphabet_of
      (compileType_base_edge_env_mem (skip_edge_families alphabet) hEdge)
      (silent_mem_labels _)
      (mem_localOfferSummaries_of_subset (by simp) (by simp))

private lemma message_guard (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    BaseGuard (.message alphabet msg dir) := by
  intro residual state env label offers hRelated hCase
  rcases offers with ⟨current, future⟩
  rcases relationMembership_message_cases alphabet msg dir hRelated with
    ⟨hR, hS⟩ | ⟨hR, hS⟩ <;> subst hR <;> subst hS
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | action _ _ _ _ cond hA =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (message_mem_labels hA)
            (mem_localOfferSummaries_of_subset ?_ ?_)
          · intro x hx
            simp at hx
            subst hx; exact hA
          · simp [typeFutureOffers, typeFutureOffersFuel]
      | action_wait _ _ _ _ cond hA =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset ?_ ?_)
          · intro x hx
            simp at hx
            subst hx; exact hA
          · have hFut : typeFutureOffers (PactType.message alphabet msg dir) ⊆
                alphabet.actions := by
              rw [show typeFutureOffers (PactType.message alphabet msg dir)
                    = ({(msg, dir)} : Finset BareMessage) from by
                simp [typeFutureOffers, typeFutureOffersFuel, hA]]
              intro y hy
              simp at hy
              subst hy
              exact hA
            exact Finset.Subset.trans Finset.sdiff_subset hFut
    · have hEnvMem := compileType_base_edge_env_mem
        (message_edge_families alphabet msg dir) hEdge
      have hDeclared : (msg, dir) ∈ alphabet.actions :=
        compileType_message_root_edge_declared msg dir hEdge
      have hCurrentSub : ({(msg, dir)} : Finset BareMessage) ⊆ alphabet.actions := by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx; exact hDeclared
      rcases compileType_message_edge_cases msg dir hEdge with
        ⟨-, -, hLabel, hCurrent, hFuture, -⟩ |
        ⟨-, -, hLabel, hCurrent, hFuture, -, -⟩ |
        ⟨hSource, -, -, -, -, -⟩
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (message_mem_labels hDeclared)
          (mem_localOfferSummaries_of_subset hCurrentSub (by simp))
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset hCurrentSub (by simp))
      · simp at hSource
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | skip _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset (by simp) ?_)
          simp [typeFutureOffers, typeFutureOffersFuel]
    · have hEnvMem := compileType_base_edge_env_mem
        (message_edge_families alphabet msg dir) hEdge
      rcases compileType_message_edge_cases msg dir hEdge with
        ⟨hSource, -⟩ | ⟨hSource, -⟩ | ⟨-, -, hLabel, hCurrent, hFuture, -⟩
      · simp at hSource
      · simp at hSource
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) (by simp))

private lemma tock_guard (alphabet : PactTypeAlphabet) :
    BaseGuard (.tock alphabet) := by
  intro residual state env label offers hRelated hCase
  rcases offers with ⟨current, future⟩
  rcases relationMembership_tock_cases alphabet hRelated with
    ⟨hR, hS⟩ | ⟨hR, hS⟩ <;> subst hR <;> subst hS
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | cycle _ _ cond =>
          exact mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (tock_mem_labels _)
            (mem_localOfferSummaries_of_subset (by simp) (by simp))
      | cycle_wait _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset (by simp) ?_)
          simp [typeFutureOffers, typeFutureOffersFuel]
    · have hEnvMem := compileType_base_edge_env_mem
        (tock_edge_families alphabet) hEdge
      rcases compileType_tock_edge_cases hEdge with
        ⟨-, -, hLabel, hCurrent, hFuture, -⟩ |
        ⟨-, -, hLabel, hCurrent, hFuture, -⟩ | ⟨hSource, -⟩
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (tock_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) (by simp))
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) (by simp))
      · simp at hSource
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | skip _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset (by simp) ?_)
          simp [typeFutureOffers, typeFutureOffersFuel]
    · have hEnvMem := compileType_base_edge_env_mem
        (tock_edge_families alphabet) hEdge
      rcases compileType_tock_edge_cases hEdge with
        ⟨hSource, -⟩ | ⟨hSource, -⟩ | ⟨-, -, hLabel, hCurrent, hFuture, -⟩
      · simp at hSource
      · simp at hSource
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) (by simp))

private lemma progress_guard (alphabet : PactTypeAlphabet) (pid : ProcId) :
    BaseGuard (.progress alphabet pid) := by
  intro residual state env label offers hRelated hCase
  rcases offers with ⟨current, future⟩
  rcases relationMembership_progress_cases alphabet pid hRelated with
    ⟨hR, hS⟩ | ⟨hR, hS⟩ <;> subst hR <;> subst hS
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | progress _ _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (progress_mem_labels (pid := pid) (by simp [PactType.ProgressIds]))
            (mem_localOfferSummaries_of_subset (by simp) ?_)
          simp [typeFutureOffers, typeFutureOffersFuel]
    · have hEnvMem := compileType_base_edge_env_mem
        (progress_edge_families alphabet pid) hEdge
      rcases compileType_progress_edge_cases pid hEdge with
        ⟨-, -, hLabel, hCurrent, hFuture, -⟩ | ⟨hSource, -⟩
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem
          (progress_mem_labels (pid := pid) (by simp [PactType.ProgressIds]))
          (mem_localOfferSummaries_of_subset (by simp) (by simp))
      · simp at hSource
  · rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
    · cases hOffers with
      | skip _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset (by simp) ?_)
          simp [typeFutureOffers, typeFutureOffersFuel]
    · have hEnvMem := compileType_base_edge_env_mem
        (progress_edge_families alphabet pid) hEdge
      rcases compileType_progress_edge_cases pid hEdge with
        ⟨hSource, -⟩ | ⟨-, -, hLabel, hCurrent, hFuture, -⟩
      · simp at hSource
      · subst hLabel; subst hCurrent; subst hFuture
        exact mem_transitionAlphabet_of hEnvMem (silent_mem_labels _)
          (mem_localOfferSummaries_of_subset (by simp) (by simp))

private lemma var_guard (alphabet : PactTypeAlphabet) (name : String) :
    BaseGuard (.var alphabet name) := by
  intro residual state env label offers hRelated hCase
  obtain ⟨hR, hS⟩ := relationMembership_var_cases alphabet name hRelated
  subst hR; subst hS
  rcases hCase with ⟨target, hTrans, hOffers⟩ | ⟨state', hEdge⟩
  · exact absurd hTrans (by rintro h; cases h)
  · exfalso
    rw [compileType_hasEdge_iff_hasResolvedEdge (.var alphabet name)
      TypeAutomatonState.root state' env label offers] at hEdge
    obtain ⟨edge, hPending, -, -, hLabel, -, -, -⟩ := hEdge
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image] at hPending
    obtain ⟨environment, -, rfl⟩ := hPending
    simp at hLabel


/-! ### Current-offer correspondence at the base fragments -/

/-- The full step correspondence is stronger than its current-offer half, once
every edge target is known to be related to some residual. -/
theorem currentOfferCorrespondence_of_stepIff {processType : PactType}
    (hStep : StepIffStatement processType)
    (hGuard : BaseGuard processType)
    (hTargets : ∀ {residual : PactType} {state state' : TypeAutomatonState}
      {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
      relationMembership
        (buildRelationSet processType (compileType processType)) residual state →
      (compileType processType).HasEdge state env label offers state' →
      ∃ residual',
        relationMembership
          (buildRelationSet processType (compileType processType))
          residual' state') :
    CurrentOfferCorrespondence processType := by
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    have hSymbol := hGuard hRelated (Or.inl ⟨residual', hTransition⟩)
    obtain ⟨state', hEdge, hRelated'⟩ := (hStep hRelated hSymbol).mp hTransition
    exact ⟨state', future, hEdge, hRelated'⟩
  · intro residual state state' env label current future hRelated hEdge
    have hSymbol := hGuard hRelated (Or.inr ⟨state', hEdge⟩)
    obtain ⟨residual', hRelated'⟩ := hTargets hRelated hEdge
    exact ⟨residual', future,
      (hStep hRelated hSymbol).mpr ⟨state', hEdge, hRelated'⟩, hRelated'⟩

lemma currentOfferCorrespondence_skip (alphabet : PactTypeAlphabet) :
    CurrentOfferCorrespondence (.skip alphabet) := by
  refine currentOfferCorrespondence_of_stepIff
    (fun hRelated hSymbol => correspondence_skip_stepIff alphabet hRelated hSymbol)
    (skip_guard alphabet) ?_
  intro residual state state' env label offers hRelated hEdge
  rcases offers with ⟨current, future⟩
  obtain ⟨-, hTarget, -, -, -, -⟩ := compileType_skip_edge_cases hEdge
  subst hTarget
  exact ⟨.skip alphabet, by
    simp [relationMembership, buildRelationSet, buildRelationSetCore,
      typeCompilationFuel, buildRelationSetCoreFuel]⟩

lemma currentOfferCorrespondence_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    CurrentOfferCorrespondence (.message alphabet msg dir) := by
  refine currentOfferCorrespondence_of_stepIff
    (fun hRelated hSymbol =>
      correspondence_message_stepIff alphabet msg dir hRelated hSymbol)
    (message_guard alphabet msg dir) ?_
  intro residual state state' env label offers hRelated hEdge
  rcases offers with ⟨current, future⟩
  rcases compileType_message_edge_cases msg dir hEdge with
    ⟨-, hTarget, -⟩ | ⟨-, hTarget, -⟩ | ⟨-, hTarget, -⟩ <;> subst hTarget
  · exact ⟨.skip alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩
  · exact ⟨.message alphabet msg dir, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩
  · exact ⟨.skip alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩

lemma currentOfferCorrespondence_tock (alphabet : PactTypeAlphabet) :
    CurrentOfferCorrespondence (.tock alphabet) := by
  refine currentOfferCorrespondence_of_stepIff
    (fun hRelated hSymbol => correspondence_tock_stepIff alphabet hRelated hSymbol)
    (tock_guard alphabet) ?_
  intro residual state state' env label offers hRelated hEdge
  rcases offers with ⟨current, future⟩
  rcases compileType_tock_edge_cases hEdge with
    ⟨-, hTarget, -⟩ | ⟨-, hTarget, -⟩ | ⟨-, hTarget, -⟩ <;> subst hTarget
  · exact ⟨.skip alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩
  · exact ⟨.tock alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩
  · exact ⟨.skip alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩

lemma currentOfferCorrespondence_progress (alphabet : PactTypeAlphabet)
    (pid : ProcId) :
    CurrentOfferCorrespondence (.progress alphabet pid) := by
  refine currentOfferCorrespondence_of_stepIff
    (fun hRelated hSymbol =>
      correspondence_progress_stepIff alphabet pid hRelated hSymbol)
    (progress_guard alphabet pid) ?_
  intro residual state state' env label offers hRelated hEdge
  rcases offers with ⟨current, future⟩
  rcases compileType_progress_edge_cases pid hEdge with
    ⟨-, hTarget, -⟩ | ⟨-, hTarget, -⟩ <;> subst hTarget <;>
    exact ⟨.skip alphabet, by
      simp [relationMembership, buildRelationSet, buildRelationSetCore,
        typeCompilationFuel, buildRelationSetCoreFuel]⟩

lemma currentOfferCorrespondence_var (alphabet : PactTypeAlphabet)
    (name : String) :
    CurrentOfferCorrespondence (.var alphabet name) := by
  refine currentOfferCorrespondence_of_stepIff
    (correspondence_var_stepIff alphabet name) (var_guard alphabet name) ?_
  intro residual state state' env label offers hRelated hEdge
  exfalso
  rw [compileType_hasEdge_iff_hasResolvedEdge (.var alphabet name)
    state state' env label offers] at hEdge
  obtain ⟨edge, hPending, -, -, hLabel, -, -, -⟩ := hEdge
  simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
    Finset.mem_image] at hPending
  obtain ⟨environment, -, rfl⟩ := hPending
  simp at hLabel

/-! ### `TypeWF_Γ` descends to every written child -/

lemma typeWellFormedIn_choice {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : TypeWellFormedIn bound (.choice alphabet left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other True left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other => (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed,
      hCG.1, hTR.1, hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1,
      hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_fairChoice {bound : List String}
    {alphabet : PactTypeAlphabet} {bid : BranchId} {left right : PactType}
    (h : TypeWellFormedIn bound (.fairChoice alphabet bid left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other True left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other => (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed,
      hCG.1, hTR.1, hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1,
      hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_seq {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    (h : TypeWellFormedIn bound (.seq alphabet left right)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other False left ∧
        PactType.TailOccurrences other True right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim left (hSplit other).1
  have hRightClosed : right.TailClosed := fun other => (hSplit other).2
  exact ⟨⟨hA.2.2.2.1, hB.1, hH.1, hLeftClosed, hCG.1, hTR.1, hSC.1, hPL.1,
      hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2.2, hB.2, hH.2, hRightClosed,
      hCG.2, hTR.2, hSC.2.1, hPL.2.1, hFL.2.1, hMO.2, hPO.2, hFO.2, hIS.2,
      hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_par {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType} {interface : Interface}
    (h : TypeWellFormedIn bound (.par alphabet left right interface)) :
    TypeWellFormedIn bound left ∧ TypeWellFormedIn bound right := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hSplit : ∀ other : String,
      PactType.TailOccurrences other False left ∧
        PactType.TailOccurrences other False right := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hLeftClosed : left.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim left (hSplit other).1
  have hRightClosed : right.TailClosed := fun other =>
    PactType.tailOccurrences_mono other False.elim right (hSplit other).2
  exact ⟨⟨hA.2.2.1, hB.1, hH.1, hLeftClosed, hCG.1, hTR.1, hSC.1, hPL.1, hFL.1,
      hMO.2.1, hPO.2.1, hFO.2.1, hIS.2.1, hIAS.2.1, hCMO.1⟩,
    ⟨hA.2.2.2, hB.2, hH.2, hRightClosed, hCG.2, hTR.2, hSC.2, hPL.2.1, hFL.2.1,
      hMO.2.2, hPO.2.2, hFO.2.2, hIS.2.2, hIAS.2.2, hCMO.2⟩⟩

lemma typeWellFormedIn_recur {bound : List String}
    {alphabet : PactTypeAlphabet} {name : String} {body : PactType}
    (h : TypeWellFormedIn bound (.recur alphabet name body)) :
    TypeWellFormedIn (name :: bound) body := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hBodyClosed : body.TailClosed := by
    intro other
    by_cases hName : name = other
    · subst hName; exact hTR.1
    · have hOther := hTC other
      simpa only [PactType.TailOccurrences, if_neg hName] using hOther
  exact ⟨hA.2.2, hB, hH.2, hBodyClosed, hCG.2, hTR.2, hSC.1, hPL, hFL, hMO,
    hPO, hFO, hIS, hIAS.2, hCMO⟩

/-! ### Re-signing preserves the structural well-formedness conjuncts

`reannotate` rewrites alphabet annotations and leaves every constructor, every
binder name and every declared identifier in place, so each conjunct of
`TypeWF_Γ` that is not itself about alphabets transfers. -/

theorem PactType.reannotate_allVariablesBound (bound : List String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.AllVariablesBound bound processType →
        PactType.AllVariablesBound bound (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
          PactType.AllBranchVariablesBound bound
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.AllBranchVariablesBound]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                branchAlphabet hHold.1,
              restIH hRestSize hHold.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.AllBranchVariablesBound bound branches →
          PactType.AllBranchVariablesBound bound
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.AllBranchVariablesBound]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.AllBranchVariablesBound] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.AllBranchVariablesBound]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl _
                hHold.1,
              restIH _ hRestSize hHold.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.AllVariablesBound]
      | progress a p => simp [PactType.reannotate, PactType.AllVariablesBound]
      | tock a => simp [PactType.reannotate, PactType.AllVariablesBound]
      | skip a => simp [PactType.reannotate, PactType.AllVariablesBound]
      | var a name =>
          simpa [PactType.reannotate, PactType.AllVariablesBound] using hHolds
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ih (sizeOf body) hB (name :: bound) body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf l) hL bound l rfl _ hHolds.1,
            ih (sizeOf r) hR bound r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.AllVariablesBound] at hHolds
          simp only [PactType.reannotate, PactType.AllVariablesBound]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2⟩

theorem PactType.reannotate_binderHygienic (bound : List String) :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.BinderHygienic bound processType →
        PactType.BinderHygienic bound (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType bound with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BinderHygienicBranches bound branches →
          PactType.BinderHygienicBranches bound
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BinderHygienicBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderHygienicBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BinderHygienicBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl
                branchAlphabet hHold.1,
              restIH hRestSize hHold.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BinderHygienicBranches bound branches →
          PactType.BinderHygienicBranches bound
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BinderHygienicBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.BinderHygienicBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BinderHygienicBranches]
            exact ⟨ih (sizeOf branchType) hBranchSize bound branchType rfl _
                hHold.1,
              restIH _ hRestSize hHold.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.BinderHygienic]
      | progress a p => simp [PactType.reannotate, PactType.BinderHygienic]
      | tock a => simp [PactType.reannotate, PactType.BinderHygienic]
      | skip a => simp [PactType.reannotate, PactType.BinderHygienic]
      | var a name => simp [PactType.reannotate, PactType.BinderHygienic]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨hHolds.1,
            ih (sizeOf body) hB (name :: bound) body rfl alphabet hHolds.2⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl alphabet hHolds.1,
            ih (sizeOf r) hR bound r rfl alphabet hHolds.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf l) hL bound l rfl _ hHolds.1,
            ih (sizeOf r) hR bound r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.BinderHygienic] at hHolds
          simp only [PactType.reannotate, PactType.BinderHygienic]
          exact ⟨ih (sizeOf e) hE bound e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2⟩

theorem reannotateBranches_progressIds (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchProgressIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchProgressIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.reannotateBranches, PactType.BranchProgressIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateBranches, PactType.BranchProgressIds,
        (PactType.reannotate_ownership_data alphabet branchType).2.2.1, ih]

theorem reannotateOfferBranches_progressIds (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      PactType.BranchProgressIds
          (PactType.reannotateOfferBranches alphabet seen branches) =
        PactType.BranchProgressIds branches := by
  intro branches
  induction branches with
  | nil => intro seen; simp [PactType.reannotateOfferBranches_nil,
      PactType.BranchProgressIds]
  | cons branch rest ih =>
      intro seen
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateOfferBranches_cons, PactType.BranchProgressIds,
        (PactType.reannotate_ownership_data _ branchType).2.2.1, ih]

theorem reannotateBranches_fairChoiceIds (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchFairChoiceIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchFairChoiceIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.reannotateBranches, PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateBranches, PactType.BranchFairChoiceIds,
        (PactType.reannotate_ownership_data alphabet branchType).2.2.2.1, ih]

theorem reannotateOfferBranches_fairChoiceIds (alphabet : PactTypeAlphabet) :
    ∀ (branches : List (BareMessage × PactType)) (seen : Finset BareMessage),
      PactType.BranchFairChoiceIds
          (PactType.reannotateOfferBranches alphabet seen branches) =
        PactType.BranchFairChoiceIds branches := by
  intro branches
  induction branches with
  | nil => intro seen; simp [PactType.reannotateOfferBranches_nil,
      PactType.BranchFairChoiceIds]
  | cons branch rest ih =>
      intro seen
      rcases branch with ⟨action, branchType⟩
      simp [PactType.reannotateOfferBranches_cons, PactType.BranchFairChoiceIds,
        (PactType.reannotate_ownership_data _ branchType).2.2.2.1, ih]

theorem PactType.reannotate_progressIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.ProgressIds (processType.reannotate alphabet) =
      PactType.ProgressIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.1

theorem PactType.reannotate_fairChoiceIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.FairChoiceIds (processType.reannotate alphabet) =
      PactType.FairChoiceIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.2.2.1

theorem PactType.reannotate_progressLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.ProgressLinear processType →
        PactType.ProgressLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ProgressLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches, PactType.ProgressLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.ProgressLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches, PactType.ProgressLinearBranches,
              PactType.reannotate_progressIds, reannotateBranches_progressIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.ProgressLinearBranches branches →
          PactType.ProgressLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil, PactType.ProgressLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.ProgressLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons, PactType.ProgressLinearBranches,
              PactType.reannotate_progressIds, reannotateOfferBranches_progressIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.ProgressLinear]
      | progress a p => simp [PactType.reannotate, PactType.ProgressLinear]
      | tock a => simp [PactType.reannotate, PactType.ProgressLinear]
      | skip a => simp [PactType.reannotate, PactType.ProgressLinear]
      | var a name => simp [PactType.reannotate, PactType.ProgressLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear]
          exact ih (sizeOf body) hB body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds, reannotateBranches_progressIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1,
            hHolds.2.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.ProgressLinear] at hHolds
          simp only [PactType.reannotate, PactType.ProgressLinear, PactType.reannotate_progressIds, reannotateOfferBranches_progressIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1,
            hHolds.2.2⟩

theorem PactType.reannotate_fairChoiceLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.FairChoiceLinear processType →
        PactType.FairChoiceLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.FairChoiceLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches, PactType.FairChoiceLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.FairChoiceLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches, PactType.FairChoiceLinearBranches,
              PactType.reannotate_fairChoiceIds, reannotateBranches_fairChoiceIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.FairChoiceLinearBranches branches →
          PactType.FairChoiceLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil, PactType.FairChoiceLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.FairChoiceLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons, PactType.FairChoiceLinearBranches,
              PactType.reannotate_fairChoiceIds, reannotateOfferBranches_fairChoiceIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | progress a p => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | tock a => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | skip a => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | var a name => simp [PactType.reannotate, PactType.FairChoiceLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear]
          exact ih (sizeOf body) hB body rfl alphabet hHolds
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2.1,
            hHolds.2.2.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2.1, hHolds.2.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds, reannotateBranches_fairChoiceIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1,
            hHolds.2.2⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.FairChoiceLinear] at hHolds
          simp only [PactType.reannotate, PactType.FairChoiceLinear, PactType.reannotate_fairChoiceIds, reannotateOfferBranches_fairChoiceIds]
          exact ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1,
            hHolds.2.2⟩

/-! ### The generated conjunctive child inherits `TypeWF_Γ`

The paper's `<compiler-call-decrease>`, "Generated conjunctive children"
clause.  Eight of the thirteen conjuncts are bundled here and proved by one
induction over the branch list; `AlphabetWellFormed`, `ClockGuarded`,
`TailRecursive` and `TailClosed` come from existing results. -/

/-- The eight `TypeWF_Γ` conjuncts that the branch product must carry and that
are neither about alphabets nor already available for it. -/
def GeneratedChildConjuncts (bound : List String) (processType : PactType) :
    Prop :=
  PactType.AllVariablesBound bound processType ∧
    PactType.BinderHygienic bound processType ∧
    PactType.InterfaceScoped processType ∧
    PactType.ProgressLinear processType ∧
    PactType.FairChoiceLinear processType ∧
    PactType.ParallelMessageOwnership processType ∧
    PactType.ParallelProgressOwnership processType ∧
    PactType.ParallelFairChoiceOwnership processType

theorem generatedChildConjuncts_reannotate {bound : List String}
    {processType : PactType} (alphabet : PactTypeAlphabet)
    (h : GeneratedChildConjuncts bound processType) :
    GeneratedChildConjuncts bound (processType.reannotate alphabet) := by
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ := h
  exact ⟨PactType.reannotate_allVariablesBound bound processType alphabet hB,
    PactType.reannotate_binderHygienic bound processType alphabet hH,
    PactType.reannotate_interfaceScoped processType alphabet hS,
    PactType.reannotate_progressLinear processType alphabet hP,
    PactType.reannotate_fairChoiceLinear processType alphabet hF,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.1.mpr hM,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.1.mpr hPo,
    (PactType.reannotate_ownership_data alphabet processType).2.2.2.2.2.2.mpr hFo⟩

theorem singletonTypeXOfferAt_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (h : GeneratedChildConjuncts bound branch.2) :
    GeneratedChildConjuncts bound (singletonTypeXOfferAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ :=
    generatedChildConjuncts_reannotate (bound := bound) alphabet h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [singletonTypeXOfferAt, PactType.AllVariablesBound,
      PactType.AllBranchVariablesBound, PactType.BinderHygienic,
      PactType.BinderHygienicBranches, PactType.InterfaceScoped,
      PactType.InterfaceScopedBranches, PactType.ProgressLinear,
      PactType.ProgressLinearBranches, PactType.FairChoiceLinear,
      PactType.FairChoiceLinearBranches, PactType.ParallelMessageOwnership,
      PactType.ParallelMessageOwnershipBodies,
      PactType.ParallelProgressOwnership,
      PactType.ParallelProgressOwnershipBranches,
      PactType.ParallelFairChoiceOwnership,
      PactType.ParallelFairChoiceOwnershipBranches,
      PactType.ProgressIds, PactType.BranchProgressIds,
      PactType.FairChoiceIds, PactType.BranchFairChoiceIds]
  · exact ⟨trivial, hB, trivial⟩
  · exact ⟨trivial, hH, trivial⟩
  · exact ⟨trivial, hS, trivial⟩
  · exact ⟨trivial, ⟨hP, by simp, trivial⟩, by simp⟩
  · exact ⟨trivial, ⟨hF, by simp, trivial⟩, by simp⟩
  · exact ⟨trivial, hM, trivial⟩
  · exact ⟨trivial, hPo, by simp, trivial⟩
  · exact ⟨trivial, hFo, by simp, trivial⟩

theorem selectedTypeBranchAt_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (h : GeneratedChildConjuncts bound branch.2) :
    GeneratedChildConjuncts bound (selectedTypeBranchAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  obtain ⟨hB, hH, hS, hP, hF, hM, hPo, hFo⟩ :=
    generatedChildConjuncts_reannotate (bound := bound) alphabet h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [selectedTypeBranchAt, PactType.AllVariablesBound,
      PactType.BinderHygienic, PactType.InterfaceScoped,
      PactType.ProgressLinear, PactType.FairChoiceLinear,
      PactType.ParallelMessageOwnership, PactType.ParallelProgressOwnership,
      PactType.ParallelFairChoiceOwnership,
      PactType.ProgressIds, PactType.FairChoiceIds]
  · exact ⟨trivial, hB⟩
  · exact ⟨trivial, hH⟩
  · exact ⟨trivial, hS⟩
  · exact ⟨trivial, hP, by simp⟩
  · exact ⟨trivial, hF, by simp⟩
  · exact ⟨trivial, hM⟩
  · exact ⟨trivial, hPo⟩
  · exact ⟨trivial, hFo⟩

theorem PactType.reannotate_messageIds (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.MessageIds (processType.reannotate alphabet) =
      PactType.MessageIds processType :=
  (PactType.reannotate_ownership_data alphabet processType).1

theorem PactType.reannotate_messageActions (alphabet : PactTypeAlphabet)
    (processType : PactType) :
    PactType.MessageActions (processType.reannotate alphabet) =
      PactType.MessageActions processType :=
  (PactType.reannotate_ownership_data alphabet processType).2.1

/-- Re-signing leaves the message identifiers of every branch in place. -/
theorem PactType.reannotateBranches_branchMessageIds
    (alphabet : PactTypeAlphabet) :
    ∀ branches : List (BareMessage × PactType),
      PactType.BranchMessageIds
          (PactType.reannotateBranches alphabet branches) =
        PactType.BranchMessageIds branches := by
  intro branches
  induction branches with
  | nil => simp [PactType.BranchMessageIds]
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      rw [PactType.reannotateBranches_cons]
      simp only [PactType.BranchMessageIds, ih,
        PactType.reannotate_messageIds]

/-- Conjunctive ownership speaks only about message identifiers, so re-signing
transports it in both directions. -/
theorem PactType.reannotate_conjunctiveMessageOwnership :
    ∀ (processType : PactType) (target : PactTypeAlphabet),
      (PactType.ConjunctiveMessageOwnership (processType.reannotate target) ↔
        PactType.ConjunctiveMessageOwnership processType) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBodies : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ target : PactTypeAlphabet,
          (PactType.ConjunctiveMessageOwnershipBodies
              (PactType.reannotateBranches target branches) ↔
            PactType.ConjunctiveMessageOwnershipBodies branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _
            rw [PactType.reannotateBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            rw [PactType.reannotateBranches_cons]
            simp only [PactType.ConjunctiveMessageOwnershipBodies]
            exact and_congr (ih (sizeOf body) hBodySize body rfl target)
              (restIH hTailSize target)
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n → ∀ (target : PactTypeAlphabet)
            (seen : Finset BareMessage),
          (PactType.ConjunctiveMessageOwnershipBranches
              (PactType.reannotateOfferBranches target seen branches) ↔
            PactType.ConjunctiveMessageOwnershipBranches branches) := by
        intro branches
        induction branches with
        | nil =>
            intro _ _ _
            rw [PactType.reannotateOfferBranches_nil]
        | cons head tail restIH =>
            intro hSizeCons target seen
            rcases head with ⟨action, body⟩
            have hBodySize : sizeOf body < n := by
              have hPair : sizeOf body < sizeOf (action, body) := by
                simp_wf; omega
              have hHead : sizeOf (action, body) <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailSize : sizeOf tail < n := by
              have hRest : sizeOf tail <
                  sizeOf ((action, body) :: tail) := by simp_wf; omega
              omega
            have hTailIds : PactType.BranchMessageIds
                (PactType.reannotateOfferBranches target seen tail) =
                  PactType.BranchMessageIds tail := by
              have hShape : ∀ list : List (BareMessage × PactType),
                  PactType.reannotateOfferBranches target seen list =
                    PactType.reannotateBranches target list := by
                intro list
                induction list with
                | nil =>
                    rw [PactType.reannotateOfferBranches_nil,
                      PactType.reannotateBranches_nil]
                | cons entry rest shapeIH =>
                    rcases entry with ⟨entryAction, entryBody⟩
                    rw [PactType.reannotateOfferBranches_cons,
                      PactType.reannotateBranches_cons, shapeIH]
              rw [hShape tail,
                PactType.reannotateBranches_branchMessageIds]
            rw [PactType.reannotateOfferBranches_cons]
            simp only [PactType.ConjunctiveMessageOwnershipBranches,
              PactType.reannotate_messageIds, hTailIds]
            exact and_congr (ih (sizeOf body) hBodySize body rfl target)
              (and_congr Iff.rfl (restIH hTailSize target seen))
      intro target
      subst hSize
      cases processType with
      | message _ _ _ | progress _ _ | tock _ | skip _ | var _ _ =>
          simp [PactType.reannotate, PactType.ConjunctiveMessageOwnership]
      | recur alphabet name body =>
          have hBodySize : sizeOf body < sizeOf
              (PactType.recur alphabet name body) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact ih (sizeOf body) hBodySize body rfl target
      | choice alphabet left right =>
          have hL : sizeOf left < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.choice alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | seq alphabet left right =>
          have hL : sizeOf left < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.seq alphabet left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | fairChoice alphabet bid left right =>
          have hL : sizeOf left < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.fairChoice alphabet bid left right) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf left) hL left rfl target)
            (ih (sizeOf right) hR right rfl target)
      | par alphabet left right interface =>
          have hL : sizeOf left < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          have hR : sizeOf right < sizeOf
              (PactType.par alphabet left right interface) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr
            (ih (sizeOf left) hL left rfl
              (target.projectParallel left.alphabet interface))
            (ih (sizeOf right) hR right rfl
              (target.projectParallel right.alphabet interface))
      | xoffer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.xoffer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf elseType) hE elseType rfl target)
            (hBodies branches hB target)
      | offer alphabet elseType branches =>
          have hE : sizeOf elseType < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          have hB : sizeOf branches < sizeOf
              (PactType.offer alphabet elseType branches) := by simp_wf; omega
          simp only [PactType.reannotate,
            PactType.ConjunctiveMessageOwnership]
          exact and_congr (ih (sizeOf elseType) hE elseType rfl target)
            (hBranches branches hB target ∅)

theorem singletonTypeXOfferAt_ids (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    PactType.MessageIds (singletonTypeXOfferAt alphabet branch) =
        {branch.1.1} ∪ PactType.MessageIds branch.2 ∧
      PactType.MessageActions (singletonTypeXOfferAt alphabet branch) =
        {branch.1} ∪ PactType.MessageActions branch.2 ∧
      PactType.ProgressIds (singletonTypeXOfferAt alphabet branch) =
        PactType.ProgressIds branch.2 ∧
      PactType.FairChoiceIds (singletonTypeXOfferAt alphabet branch) =
        PactType.FairChoiceIds branch.2 := by
  rcases branch with ⟨action, body⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [singletonTypeXOfferAt, PactType.MessageIds, PactType.BranchMessageIds,
      PactType.MessageActions, PactType.BranchMessageActions,
      PactType.ProgressIds, PactType.BranchProgressIds,
      PactType.FairChoiceIds, PactType.BranchFairChoiceIds,
      PactType.reannotate_messageIds, PactType.reannotate_messageActions,
      PactType.reannotate_progressIds, PactType.reannotate_fairChoiceIds]

theorem selectedTypeBranchAt_ids (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    PactType.MessageIds (selectedTypeBranchAt alphabet branch) =
        {branch.1.1} ∪ PactType.MessageIds branch.2 ∧
      PactType.MessageActions (selectedTypeBranchAt alphabet branch) =
        {branch.1} ∪ PactType.MessageActions branch.2 ∧
      PactType.ProgressIds (selectedTypeBranchAt alphabet branch) =
        PactType.ProgressIds branch.2 ∧
      PactType.FairChoiceIds (selectedTypeBranchAt alphabet branch) =
        PactType.FairChoiceIds branch.2 := by
  rcases branch with ⟨action, body⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [selectedTypeBranchAt, PactType.MessageIds, PactType.MessageActions,
      PactType.ProgressIds, PactType.FairChoiceIds,
      PactType.reannotate_messageIds, PactType.reannotate_messageActions,
      PactType.reannotate_progressIds, PactType.reannotate_fairChoiceIds]

theorem parallelTypeBranchesWithin_conjuncts {bound : List String} :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ b ∈ branches, GeneratedChildConjuncts bound b.2) →
      PactType.ProgressLinearBranches branches →
      PactType.FairChoiceLinearBranches branches →
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        GeneratedChildConjuncts bound
          (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ alphabet
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesWithin, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          exact singletonTypeXOfferAt_conjuncts alphabet (action, body)
            (hBranch (action, body) (by simp))
      | cons next tail =>
          simp only [PactType.ProgressLinearBranches] at hProg
          simp only [PactType.FairChoiceLinearBranches] at hFair
          simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
          simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
          simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
          have hHead := singletonTypeXOfferAt_conjuncts alphabet
            (action, body) (hBranch (action, body) (by simp))
          have hRestConj := ih (fun b hb => hBranch b (by simp [hb]))
            hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
            alphabet
          obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
          obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
          obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
            singletonTypeXOfferAt_ids alphabet (action, body)
          have hIdsR := parallelTypeBranchesWithin_messageIds
            alphabet (next :: tail)
          have hActsR := parallelTypeBranchesWithin_messageActions
            alphabet (next :: tail)
          have hProgR := parallelTypeBranchesWithin_progressIds
            alphabet (next :: tail)
          have hFairR := parallelTypeBranchesWithin_fairChoiceIds
            alphabet (next :: tail)
          simp only [parallelTypeBranchesWithin]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
              PactType.InterfaceScoped, PactType.ProgressLinear,
              PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
              PactType.ParallelProgressOwnership,
              PactType.ParallelFairChoiceOwnership]
          · exact ⟨hHB, hRB⟩
          · exact ⟨hHH, hRH⟩
          · exact ⟨by simp, hHS, hRS⟩
          · refine ⟨hHP, hRP, ?_⟩
            rw [hProgL, hProgR]; exact hProg.2.1
          · refine ⟨hHF, hRF, ?_⟩
            rw [hFairL, hFairR]; exact hFair.2.1
          · refine ⟨?_, hHM, hRM⟩
            rw [hIdsL, hIdsR]
            intro x hx
            exact absurd (Finset.mem_inter.mp hx).2
              (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
          · refine ⟨?_, hHPo, hRPo⟩
            rw [hProgL, hProgR]; exact hProgOwn.2.1
          · refine ⟨?_, hHFo, hRFo⟩
            rw [hFairL, hFairR]; exact hFairOwn.2.1

theorem parallelTypeBranchesSelectingWithin_conjuncts {bound : List String}
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      (∀ b ∈ branches, GeneratedChildConjuncts bound b.2) →
      PactType.ProgressLinearBranches branches →
      PactType.FairChoiceLinearBranches branches →
      PactType.ParallelMessageOwnershipBranches branches →
      PactType.ParallelProgressOwnershipBranches branches →
      PactType.ParallelFairChoiceOwnershipBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        GeneratedChildConjuncts bound
          (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ _ _ _ _ _ alphabet
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelectingWithin, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet
      have hHeadConj := hBranch (action, body) (by simp)
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            exact selectedTypeBranchAt_conjuncts alphabet (action, body) hHeadConj
          · rw [if_neg hSel]
            exact singletonTypeXOfferAt_conjuncts alphabet (action, body) hHeadConj
      | cons next tail =>
          simp only [PactType.ProgressLinearBranches] at hProg
          simp only [PactType.FairChoiceLinearBranches] at hFair
          simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
          simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
          simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            have hHead := selectedTypeBranchAt_conjuncts alphabet
              (action, body) hHeadConj
            have hRestConj := parallelTypeBranchesWithin_conjuncts (next :: tail)
              (fun b hb => hBranch b (by simp [hb]))
              hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
              alphabet
            obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
            obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
            obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
              selectedTypeBranchAt_ids alphabet (action, body)
            have hIdsRe := parallelTypeBranchesWithin_messageIds
              alphabet (next :: tail)
            have hActsRe := parallelTypeBranchesWithin_messageActions
              alphabet (next :: tail)
            have hProgRe := parallelTypeBranchesWithin_progressIds
              alphabet (next :: tail)
            have hFairRe := parallelTypeBranchesWithin_fairChoiceIds
              alphabet (next :: tail)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
                PactType.InterfaceScoped, PactType.ProgressLinear,
                PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
                PactType.ParallelProgressOwnership,
                PactType.ParallelFairChoiceOwnership]
            · exact ⟨hHB, hRB⟩
            · exact ⟨hHH, hRH⟩
            · exact ⟨by simp, hHS, hRS⟩
            · refine ⟨hHP, hRP, ?_⟩
              rw [hProgL, hProgRe]; exact hProg.2.1
            · refine ⟨hHF, hRF, ?_⟩
              rw [hFairL, hFairRe]; exact hFair.2.1
            · refine ⟨?_, hHM, hRM⟩
              rw [hIdsL, hIdsRe]
              intro x hx
              exact absurd (Finset.mem_inter.mp hx).2
                (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
            · refine ⟨?_, hHPo, hRPo⟩
              rw [hProgL, hProgRe]; exact hProgOwn.2.1
            · refine ⟨?_, hHFo, hRFo⟩
              rw [hFairL, hFairRe]; exact hFairOwn.2.1
          · rw [if_neg hSel]
            have hHead := singletonTypeXOfferAt_conjuncts alphabet
              (action, body) hHeadConj
            have hRestConj := ih (fun b hb => hBranch b (by simp [hb]))
              hProg.2.2 hFair.2.2 hMsgOwn.2.2.2 hProgOwn.2.2 hFairOwn.2.2
              alphabet
            obtain ⟨hHB, hHH, hHS, hHP, hHF, hHM, hHPo, hHFo⟩ := hHead
            obtain ⟨hRB, hRH, hRS, hRP, hRF, hRM, hRPo, hRFo⟩ := hRestConj
            obtain ⟨hIdsL, hActsL, hProgL, hFairL⟩ :=
              singletonTypeXOfferAt_ids alphabet (action, body)
            obtain ⟨hIdsRe, hActsRe, hProgRe, hFairRe⟩ :=
              parallelTypeBranchesSelectingWithin_ownershipData
                alphabet selected
                (next :: tail)
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp only [PactType.AllVariablesBound, PactType.BinderHygienic,
                PactType.InterfaceScoped, PactType.ProgressLinear,
                PactType.FairChoiceLinear, PactType.ParallelMessageOwnership,
                PactType.ParallelProgressOwnership,
                PactType.ParallelFairChoiceOwnership]
            · exact ⟨hHB, hRB⟩
            · exact ⟨hHH, hRH⟩
            · exact ⟨by simp, hHS, hRS⟩
            · refine ⟨hHP, hRP, ?_⟩
              rw [hProgL, hProgRe]; exact hProg.2.1
            · refine ⟨hHF, hRF, ?_⟩
              rw [hFairL, hFairRe]; exact hFair.2.1
            · refine ⟨?_, hHM, hRM⟩
              rw [hIdsL, hIdsRe]
              intro x hx
              exact absurd (Finset.mem_inter.mp hx).2
                (Finset.disjoint_left.mp hMsgOwn.2.1 (Finset.mem_inter.mp hx).1)
            · refine ⟨?_, hHPo, hRPo⟩
              rw [hProgL, hProgRe]; exact hProgOwn.2.1
            · refine ⟨?_, hHFo, hRFo⟩
              rw [hFairL, hFairRe]; exact hFairOwn.2.1


/-- The generated conjunctive child carries the eight `TypeWF_Γ` conjuncts that
are neither alphabet-shaped nor already available for it. -/
theorem parallelTypeBranchesSelecting_conjuncts {bound : List String}
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hBranch : ∀ b ∈ branches, GeneratedChildConjuncts bound b.2)
    (hProg : PactType.ProgressLinearBranches branches)
    (hFair : PactType.FairChoiceLinearBranches branches)
    (hMsgOwn : PactType.ParallelMessageOwnershipBranches branches)
    (hProgOwn : PactType.ParallelProgressOwnershipBranches branches)
    (hFairOwn : PactType.ParallelFairChoiceOwnershipBranches branches) :
    GeneratedChildConjuncts bound
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelecting, PactType.AllVariablesBound,
          PactType.BinderHygienic, PactType.InterfaceScoped,
          PactType.ProgressLinear, PactType.FairChoiceLinear,
          PactType.ParallelMessageOwnership,
          PactType.ParallelProgressOwnership,
          PactType.ParallelFairChoiceOwnership]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_conjuncts selected
        (branch :: rest) hBranch hProg hFair hMsgOwn hProgOwn hFairOwn alphabet

theorem PactType.reannotate_canCompleteBeforeTock :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.CanCompleteBeforeTock (processType.reannotate alphabet) =
        PactType.CanCompleteBeforeTock processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchCanCompleteBeforeTock
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BranchCanCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchCanCompleteBeforeTock
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchCanCompleteBeforeTock branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchCanCompleteBeforeTock]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BranchCanCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.CanCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.CanCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

theorem PactType.reannotate_prefixMessageIds :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.PrefixMessageIds (processType.reannotate alphabet) =
        PactType.PrefixMessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchPrefixMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchPrefixMessageIds branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchPrefixMessageIds]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BranchPrefixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchPrefixMessageIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchPrefixMessageIds branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchPrefixMessageIds]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BranchPrefixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.PrefixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

theorem PactType.reannotate_suffixMessageIds :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.SuffixMessageIds (processType.reannotate alphabet) =
        PactType.SuffixMessageIds processType := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.BranchSuffixMessageIds
              (PactType.reannotateBranches branchAlphabet branches) =
            PactType.BranchSuffixMessageIds branches := by
        intro branches branchAlphabet hBranchesSize
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.BranchSuffixMessageIds]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.BranchSuffixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl branchAlphabet,
              restIH hRestSize]
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.BranchSuffixMessageIds
              (PactType.reannotateOfferBranches branchAlphabet seen branches) =
            PactType.BranchSuffixMessageIds branches := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.BranchSuffixMessageIds]
        | cons branch rest restIH =>
            intro seen hBranchesSize
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.BranchSuffixMessageIds, PactType.reannotate_canCompleteBeforeTock,
              ih (sizeOf branchType) hBranchSize branchType rfl _,
              restIH _ hRestSize]
      cases processType with
      | message a m d => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | progress a p => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | tock a => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | skip a => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | var a name => simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf body) hB body rfl alphabet]
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl alphabet, ih (sizeOf r) hR r rfl alphabet]
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf l) hL l rfl _, ih (sizeOf r) hR r rfl _]
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hBranches bs alphabet hBs]
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp [PactType.reannotate, PactType.SuffixMessageIds,
            PactType.reannotate_canCompleteBeforeTock,
            PactType.reannotate_canCompleteBeforeTock,
            ih (sizeOf e) hE e rfl alphabet, hOfferBranches bs alphabet ∅ hBs]

/-! ### Same-cycle identifier sets of the generated branch product

`PrefixMessageIds` and `SuffixMessageIds` of the product are exactly the branch
list's own, and the product can always complete before a clock (every factor
carries a `skip` else-arm).  These are stated separately because
`<future-offers-agree>`'s `.offer` case unfolds the same sets. -/

theorem parallelTypeBranchesWithin_cycleData :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      PactType.CanCompleteBeforeTock
          (parallelTypeBranchesWithin alphabet branches) = true ∧
        PactType.PrefixMessageIds
            (parallelTypeBranchesWithin alphabet branches) =
          PactType.BranchPrefixMessageIds branches ∧
        PactType.SuffixMessageIds
            (parallelTypeBranchesWithin alphabet branches) =
          PactType.BranchSuffixMessageIds branches := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesWithin, PactType.CanCompleteBeforeTock,
          PactType.PrefixMessageIds, PactType.SuffixMessageIds,
          PactType.BranchPrefixMessageIds, PactType.BranchSuffixMessageIds]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet
      cases rest with
      | nil =>
          refine ⟨?_, ?_, ?_⟩ <;>
            simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
              PactType.CanCompleteBeforeTock,
              PactType.BranchCanCompleteBeforeTock,
              PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
              PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
              PactType.reannotate_canCompleteBeforeTock,
              PactType.reannotate_prefixMessageIds,
              PactType.reannotate_suffixMessageIds]
      | cons next tail =>
          obtain ⟨hC, hP, hS⟩ :=
            ih alphabet
          refine ⟨?_, ?_, ?_⟩ <;>
            simp [parallelTypeBranchesWithin, singletonTypeXOfferAt,
              PactType.CanCompleteBeforeTock,
              PactType.BranchCanCompleteBeforeTock,
              PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
              PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
              PactType.reannotate_canCompleteBeforeTock,
              PactType.reannotate_prefixMessageIds,
              PactType.reannotate_suffixMessageIds, hC, hP, hS,
              Finset.union_assoc]

theorem parallelTypeBranchesSelectingWithin_cycleData
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)) (alphabet : PactTypeAlphabet),
      PactType.PrefixMessageIds
            (parallelTypeBranchesSelectingWithin alphabet selected branches) =
          PactType.BranchPrefixMessageIds branches ∧
        PactType.SuffixMessageIds
            (parallelTypeBranchesSelectingWithin alphabet selected branches) =
          PactType.BranchSuffixMessageIds branches := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet
      refine ⟨?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelectingWithin, PactType.PrefixMessageIds,
          PactType.SuffixMessageIds, PactType.BranchPrefixMessageIds,
          PactType.BranchSuffixMessageIds]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet
      cases rest with
      | nil =>
          by_cases hSel : (action, body) = selected
          · subst hSel
            refine ⟨?_, ?_⟩ <;>
              simp [parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
                PactType.CanCompleteBeforeTock,
                PactType.BranchCanCompleteBeforeTock,
                PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
                PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
                PactType.reannotate_canCompleteBeforeTock,
                PactType.reannotate_prefixMessageIds,
                PactType.reannotate_suffixMessageIds]
          · refine ⟨?_, ?_⟩ <;>
              simp [parallelTypeBranchesSelectingWithin, if_neg hSel,
                singletonTypeXOfferAt,
                PactType.CanCompleteBeforeTock,
                PactType.BranchCanCompleteBeforeTock,
                PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
                PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
                PactType.reannotate_canCompleteBeforeTock,
                PactType.reannotate_prefixMessageIds,
                PactType.reannotate_suffixMessageIds]
      | cons next tail =>
          obtain ⟨hPw, hSw⟩ :=
            (parallelTypeBranchesWithin_cycleData (next :: tail) alphabet).2
          obtain ⟨hPs, hSs⟩ :=
            ih alphabet
          by_cases hSel : (action, body) = selected
          · subst hSel
            refine ⟨?_, ?_⟩ <;>
              simp [parallelTypeBranchesSelectingWithin, selectedTypeBranchAt,
                PactType.CanCompleteBeforeTock,
                PactType.BranchCanCompleteBeforeTock,
                PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
                PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
                PactType.reannotate_canCompleteBeforeTock,
                PactType.reannotate_prefixMessageIds,
                PactType.reannotate_suffixMessageIds,
                hPw, hSw, Finset.union_assoc]
          · refine ⟨?_, ?_⟩ <;>
              simp [parallelTypeBranchesSelectingWithin, if_neg hSel,
                singletonTypeXOfferAt,
                PactType.CanCompleteBeforeTock,
                PactType.BranchCanCompleteBeforeTock,
                PactType.PrefixMessageIds, PactType.BranchPrefixMessageIds,
                PactType.SuffixMessageIds, PactType.BranchSuffixMessageIds,
                PactType.reannotate_canCompleteBeforeTock,
                PactType.reannotate_prefixMessageIds,
                PactType.reannotate_suffixMessageIds,
                hPs, hSs, Finset.union_assoc]

theorem PactType.reannotate_sameCycleMessageLinear :
    ∀ (processType : PactType) (alphabet : PactTypeAlphabet),
      PactType.SameCycleMessageLinear processType →
        PactType.SameCycleMessageLinear (processType.reannotate alphabet) := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      intro alphabet hHolds
      have hBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet),
          sizeOf branches < n →
          PactType.SameCycleMessageLinearBranches branches →
          PactType.SameCycleMessageLinearBranches
            (PactType.reannotateBranches branchAlphabet branches) := by
        intro branches branchAlphabet hBranchesSize hHold
        induction branches with
        | nil => simp [PactType.reannotateBranches,
            PactType.SameCycleMessageLinearBranches]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.SameCycleMessageLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateBranches,
              PactType.SameCycleMessageLinearBranches,
              PactType.reannotate_prefixMessageIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl
                branchAlphabet hHold.1, hHold.2.1, restIH hRestSize hHold.2.2⟩
      have hOfferBranches : ∀ (branches : List (BareMessage × PactType))
          (branchAlphabet : PactTypeAlphabet) (seen : Finset BareMessage),
          sizeOf branches < n →
          PactType.SameCycleMessageLinearBranches branches →
          PactType.SameCycleMessageLinearBranches
            (PactType.reannotateOfferBranches branchAlphabet seen branches) := by
        intro branches branchAlphabet
        induction branches with
        | nil =>
            intro seen _ _
            simp [PactType.reannotateOfferBranches_nil,
              PactType.SameCycleMessageLinearBranches]
        | cons branch rest restIH =>
            intro seen hBranchesSize hHold
            rcases branch with ⟨action, branchType⟩
            simp only [PactType.SameCycleMessageLinearBranches] at hHold
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            simp only [PactType.reannotateOfferBranches_cons,
              PactType.SameCycleMessageLinearBranches,
              PactType.reannotate_prefixMessageIds]
            exact ⟨ih (sizeOf branchType) hBranchSize branchType rfl _ hHold.1,
              hHold.2.1, restIH _ hRestSize hHold.2.2⟩
      cases processType with
      | message a m d => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | progress a p => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | tock a => simp [PactType.reannotate, PactType.SameCycleMessageLinear]
      | skip a => simp [PactType.reannotate, PactType.SameCycleMessageLinear]
      | var a name => simp [PactType.reannotate,
          PactType.SameCycleMessageLinear]
      | recur a name body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds,
            PactType.reannotate_suffixMessageIds]
          exact ⟨ih (sizeOf body) hB body rfl alphabet hHolds.1, hHolds.2⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds,
            PactType.reannotate_suffixMessageIds]
          exact ⟨ih (sizeOf l) hL l rfl alphabet hHolds.1,
            ih (sizeOf r) hR r rfl alphabet hHolds.2.1, hHolds.2.2⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear]
          exact ⟨ih (sizeOf l) hL l rfl _ hHolds.1,
            ih (sizeOf r) hR r rfl _ hHolds.2⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds]
          refine ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hBranches bs alphabet hBs hHolds.2.1, ?_⟩
          intro branch hBranchMem
          obtain ⟨source, hSource, hEq⟩ :=
            reannotateBranches_mem hBranchMem
          rw [hEq]
          exact hHolds.2.2 source hSource
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          simp only [PactType.SameCycleMessageLinear] at hHolds
          simp only [PactType.reannotate, PactType.SameCycleMessageLinear,
            PactType.reannotate_prefixMessageIds]
          refine ⟨ih (sizeOf e) hE e rfl alphabet hHolds.1,
            hOfferBranches bs alphabet ∅ hBs hHolds.2.1, ?_⟩
          intro branch hBranchMem
          obtain ⟨source, hSource, branchAlphabet, hEq⟩ :=
            reannotateOfferBranches_mem alphabet bs ∅ branch
              hBranchMem
          rw [hEq]
          exact hHolds.2.2 source hSource

/-- A surviving parallel component, re-signed by the node's own alphabet, is
well formed in the same binder context.  The node alphabet declares none of the
interfaces inside either component, which is what makes the re-signing
alphabet-correct. -/
lemma typeWellFormedIn_survivor {bound : List String}
    {alphabet : PactTypeAlphabet} {left right : PactType}
    {interface : Interface}
    (h : TypeWellFormedIn bound (.par alphabet left right interface)) :
    TypeWellFormedIn bound (left.reannotate alphabet) ∧
      TypeWellFormedIn bound (right.reannotate alphabet) := by
  obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par h
  obtain ⟨hA, -, -, -, -, -, -, -, -, -, -, -, -, hIAS, -⟩ := h
  have hAlphaWF : alphabet.WellFormed := by
    simp only [PactType.AlphabetWellFormed] at hA
    exact hA.1
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  have hAvoid : ∀ (child : PactType),
      PactType.ParallelInterfaces child ⊆
        interface ∪ PactType.ParallelInterfaces left ∪
          PactType.ParallelInterfaces right →
      ∀ action ∈ alphabet.actions,
        action.1 ∉ PactType.ParallelInterfaces child := by
    intro child hSub action hAction hIn
    exact Finset.disjoint_left.mp hIAS.1
      (Finset.mem_image.mpr ⟨action, hAction, rfl⟩) (hSub hIn)
  have hLeftAvoid := hAvoid left
    (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
  have hRightAvoid := hAvoid right Finset.subset_union_right
  refine ⟨?_, ?_⟩
  · obtain ⟨gA, gB, gH, gTC, gCG, gTR, gSC, gPL, gFL, gMO, gPO, gFO, gIS,
      gIAS⟩ := hLeftWF
    have hOwn := PactType.reannotate_ownership_data alphabet left
    exact ⟨PactType.reannotate_alphabetWellFormed_avoiding left alphabet gA
        hAlphaWF gIS hLeftAvoid,
      PactType.reannotate_allVariablesBound bound left alphabet gB,
      PactType.reannotate_binderHygienic bound left alphabet gH,
      fun other => PactType.reannotate_tailOccurrences other left alphabet True
        (gTC other),
      PactType.reannotate_clockGuarded left alphabet gCG,
      PactType.reannotate_tailRecursive left alphabet gTR,
      PactType.reannotate_sameCycleMessageLinear left alphabet gSC,
      PactType.reannotate_progressLinear left alphabet gPL,
      PactType.reannotate_fairChoiceLinear left alphabet gFL,
      hOwn.2.2.2.2.1.mpr gMO, hOwn.2.2.2.2.2.1.mpr gPO,
      hOwn.2.2.2.2.2.2.mpr gFO,
      PactType.reannotate_interfaceScoped left alphabet gIS,
      PactType.reannotate_interfaceAlphabetScoped left alphabet gIAS.1
        hLeftAvoid,
      (PactType.reannotate_conjunctiveMessageOwnership left alphabet).mpr
        gIAS.2⟩
  · obtain ⟨gA, gB, gH, gTC, gCG, gTR, gSC, gPL, gFL, gMO, gPO, gFO, gIS,
      gIAS⟩ := hRightWF
    have hOwn := PactType.reannotate_ownership_data alphabet right
    exact ⟨PactType.reannotate_alphabetWellFormed_avoiding right alphabet gA
        hAlphaWF gIS hRightAvoid,
      PactType.reannotate_allVariablesBound bound right alphabet gB,
      PactType.reannotate_binderHygienic bound right alphabet gH,
      fun other => PactType.reannotate_tailOccurrences other right alphabet True
        (gTC other),
      PactType.reannotate_clockGuarded right alphabet gCG,
      PactType.reannotate_tailRecursive right alphabet gTR,
      PactType.reannotate_sameCycleMessageLinear right alphabet gSC,
      PactType.reannotate_progressLinear right alphabet gPL,
      PactType.reannotate_fairChoiceLinear right alphabet gFL,
      hOwn.2.2.2.2.1.mpr gMO, hOwn.2.2.2.2.2.1.mpr gPO,
      hOwn.2.2.2.2.2.2.mpr gFO,
      PactType.reannotate_interfaceScoped right alphabet gIS,
      PactType.reannotate_interfaceAlphabetScoped right alphabet gIAS.1
        hRightAvoid,
      (PactType.reannotate_conjunctiveMessageOwnership right alphabet).mpr
        gIAS.2⟩

theorem singletonTypeXOfferAt_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hLinear : PactType.SameCycleMessageLinear branch.2)
    (hHead : branch.1.1 ∉ PactType.PrefixMessageIds branch.2) :
    PactType.SameCycleMessageLinear (singletonTypeXOfferAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [singletonTypeXOfferAt, PactType.SameCycleMessageLinear,
    PactType.SameCycleMessageLinearBranches, PactType.PrefixMessageIds,
    PactType.reannotate_prefixMessageIds]
  refine ⟨trivial, ⟨PactType.reannotate_sameCycleMessageLinear body alphabet
    hLinear, hHead, trivial⟩, ?_⟩
  intro branch hBranchMem
  simp

theorem selectedTypeBranchAt_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (branch : BareMessage × PactType)
    (hLinear : PactType.SameCycleMessageLinear branch.2)
    (hHead : branch.1.1 ∉ PactType.PrefixMessageIds branch.2) :
    PactType.SameCycleMessageLinear (selectedTypeBranchAt alphabet branch) := by
  rcases branch with ⟨action, body⟩
  simp only [selectedTypeBranchAt, PactType.SameCycleMessageLinear,
    PactType.SuffixMessageIds, PactType.reannotate_prefixMessageIds]
  refine ⟨trivial, PactType.reannotate_sameCycleMessageLinear body alphabet
    hLinear, ?_⟩
  simpa [Finset.disjoint_left] using hHead

theorem parallelTypeBranchesWithin_sameCycleMessageLinear :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.SameCycleMessageLinearBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        PactType.SameCycleMessageLinear
          (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ alphabet
      simp [parallelTypeBranchesWithin, PactType.SameCycleMessageLinear]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hLinear alphabet
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin]
          exact singletonTypeXOfferAt_sameCycleMessageLinear alphabet
            (action, body) hLinear.1 hLinear.2.1
      | cons next tail =>
          simp only [parallelTypeBranchesWithin,
            PactType.SameCycleMessageLinear]
          exact ⟨singletonTypeXOfferAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1,
            ih hLinear.2.2 alphabet⟩

theorem parallelTypeBranchesSelectingWithin_sameCycleMessageLinear
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType)),
      PactType.SameCycleMessageLinearBranches branches →
      ∀ alphabet : PactTypeAlphabet,
        PactType.SameCycleMessageLinear
          (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro _ alphabet
      simp [parallelTypeBranchesSelectingWithin,
        PactType.SameCycleMessageLinear]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro hLinear alphabet
      simp only [PactType.SameCycleMessageLinearBranches] at hLinear
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            exact selectedTypeBranchAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1
          · rw [if_neg hSel]
            exact singletonTypeXOfferAt_sameCycleMessageLinear alphabet
              (action, body) hLinear.1 hLinear.2.1
      | cons next tail =>
          simp only [parallelTypeBranchesSelectingWithin]
          by_cases hSel : (action, body) = selected
          · rw [if_pos hSel]
            simp only [PactType.SameCycleMessageLinear]
            exact ⟨selectedTypeBranchAt_sameCycleMessageLinear alphabet
                (action, body) hLinear.1 hLinear.2.1,
              parallelTypeBranchesWithin_sameCycleMessageLinear (next :: tail)
                hLinear.2.2 alphabet⟩
          · rw [if_neg hSel]
            simp only [PactType.SameCycleMessageLinear]
            exact ⟨singletonTypeXOfferAt_sameCycleMessageLinear alphabet
                (action, body) hLinear.1 hLinear.2.1,
              ih hLinear.2.2 alphabet⟩

theorem parallelTypeBranchesSelecting_sameCycleMessageLinear
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hLinear : PactType.SameCycleMessageLinearBranches branches) :
    PactType.SameCycleMessageLinear
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting,
      PactType.SameCycleMessageLinear]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_sameCycleMessageLinear selected
        (branch :: rest) hLinear alphabet

/-! ### `TypeWF_Γ` for an offer's default and generated children -/

private lemma tailBranchOccurrences_of_mem {name : String}
    {branches : List (BareMessage × PactType)}
    (h : PactType.TailBranchOccurrences name False branches) :
    ∀ branch ∈ branches, branch.2.TailOccurrences name False := by
  induction branches with
  | nil => intro branch hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.TailBranchOccurrences] at h
      intro branch hMem
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact h.1
      · exact ih h.2 branch hTail

private lemma branchesGeneratedChildConjuncts {bound : List String}
    (branches : List (BareMessage × PactType))
    (hBound : PactType.AllBranchVariablesBound bound branches)
    (hHyg : PactType.BinderHygienicBranches bound branches)
    (hScope : PactType.InterfaceScopedBranches branches)
    (hProg : PactType.ProgressLinearBranches branches)
    (hFair : PactType.FairChoiceLinearBranches branches)
    (hMsgOwn : PactType.ParallelMessageOwnershipBranches branches)
    (hProgOwn : PactType.ParallelProgressOwnershipBranches branches)
    (hFairOwn : PactType.ParallelFairChoiceOwnershipBranches branches) :
    ∀ b ∈ branches, GeneratedChildConjuncts bound b.2 := by
  induction branches with
  | nil => intro b hMem; cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, body⟩
      simp only [PactType.AllBranchVariablesBound] at hBound
      simp only [PactType.BinderHygienicBranches] at hHyg
      simp only [PactType.InterfaceScopedBranches] at hScope
      simp only [PactType.ProgressLinearBranches] at hProg
      simp only [PactType.FairChoiceLinearBranches] at hFair
      simp only [PactType.ParallelMessageOwnershipBranches] at hMsgOwn
      simp only [PactType.ParallelProgressOwnershipBranches] at hProgOwn
      simp only [PactType.ParallelFairChoiceOwnershipBranches] at hFairOwn
      intro b hMem
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact ⟨hBound.1, hHyg.1, hScope.1, hProg.1, hFair.1, hMsgOwn.1,
          hProgOwn.1, hFairOwn.1⟩
      · exact ih hBound.2 hHyg.2 hScope.2 hProg.2.2 hFair.2.2 hMsgOwn.2.2.2
          hProgOwn.2.2 hFairOwn.2.2 b hTail

/-- The branch product synchronises on nothing, so its parallel nodes ask
exactly for the branch separation a conjunctive offer already has. -/
theorem parallelTypeBranchesWithin_conjunctiveMessageOwnership :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ConjunctiveMessageOwnership
        (parallelTypeBranchesWithin alphabet branches) := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet _
      simp [parallelTypeBranchesWithin, PactType.ConjunctiveMessageOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet hConj
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      have hBody : PactType.ConjunctiveMessageOwnership
          (body.reannotate alphabet) :=
        (PactType.reannotate_conjunctiveMessageOwnership body alphabet).mpr
          hConj.1
      cases rest with
      | nil =>
          simp only [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ConjunctiveMessageOwnership,
            PactType.ConjunctiveMessageOwnershipBodies]
          exact ⟨trivial, hBody, trivial⟩
      | cons next tail =>
          simp only [parallelTypeBranchesWithin, singletonTypeXOfferAt,
            PactType.ConjunctiveMessageOwnership,
            PactType.ConjunctiveMessageOwnershipBodies]
          exact ⟨⟨trivial, hBody, trivial⟩, ih alphabet hConj.2.2⟩

/-- The committed product: the selected branch becomes a sequence, the rest
stay singleton offers, and the parallel nodes again synchronise on nothing. -/
theorem parallelTypeBranchesSelectingWithin_conjunctiveMessageOwnership
    (selected : BareMessage × PactType) :
    ∀ (branches : List (BareMessage × PactType))
      (alphabet : PactTypeAlphabet),
      PactType.ConjunctiveMessageOwnershipBranches branches →
      PactType.ConjunctiveMessageOwnership
        (parallelTypeBranchesSelectingWithin alphabet selected branches) := by
  intro branches
  induction branches with
  | nil =>
      intro alphabet _
      simp [parallelTypeBranchesSelectingWithin,
        PactType.ConjunctiveMessageOwnership]
  | cons head rest ih =>
      rcases head with ⟨action, body⟩
      intro alphabet hConj
      simp only [PactType.ConjunctiveMessageOwnershipBranches] at hConj
      have hBody : PactType.ConjunctiveMessageOwnership
          (body.reannotate alphabet) :=
        (PactType.reannotate_conjunctiveMessageOwnership body alphabet).mpr
          hConj.1
      cases rest with
      | nil =>
          by_cases hSel : (action, body) = selected
          · rw [parallelTypeBranchesSelectingWithin, if_pos hSel]
            simp only [selectedTypeBranchAt,
              PactType.ConjunctiveMessageOwnership]
            exact ⟨trivial, hBody⟩
          · rw [parallelTypeBranchesSelectingWithin, if_neg hSel]
            simp only [singletonTypeXOfferAt,
              PactType.ConjunctiveMessageOwnership,
              PactType.ConjunctiveMessageOwnershipBodies]
            exact ⟨trivial, hBody, trivial⟩
      | cons next tail =>
          by_cases hSel : (action, body) = selected
          · rw [parallelTypeBranchesSelectingWithin, if_pos hSel]
            simp only [selectedTypeBranchAt,
              PactType.ConjunctiveMessageOwnership]
            · exact ⟨⟨trivial, hBody⟩,
                parallelTypeBranchesWithin_conjunctiveMessageOwnership
                  (next :: tail) alphabet hConj.2.2⟩
            · exact List.cons_ne_nil _ _
          · rw [parallelTypeBranchesSelectingWithin, if_neg hSel]
            simp only [singletonTypeXOfferAt,
              PactType.ConjunctiveMessageOwnership,
              PactType.ConjunctiveMessageOwnershipBodies]
            · exact ⟨⟨trivial, hBody, trivial⟩, ih alphabet hConj.2.2⟩
            · exact List.cons_ne_nil _ _

/-- The committed offer inherits conjunctive ownership from the offer. -/
theorem parallelTypeBranchesSelecting_conjunctiveMessageOwnership
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType))
    (hConj : PactType.ConjunctiveMessageOwnershipBranches branches) :
    PactType.ConjunctiveMessageOwnership
      (parallelTypeBranchesSelecting alphabet selected branches) := by
  cases branches with
  | nil =>
      simp [parallelTypeBranchesSelecting,
        PactType.ConjunctiveMessageOwnership]
  | cons head tail =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_conjunctiveMessageOwnership
        selected (head :: tail) alphabet hConj

/-- The paper's `<compiler-call-decrease>` at a conjunctive offer: the default
continuation and every generated child are well formed in the same context. -/
theorem typeWellFormedIn_offer {bound : List String}
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    (h : TypeWellFormedIn bound (.offer alphabet elseType branches)) :
    TypeWellFormedIn bound elseType ∧
      ∀ selected ∈ branches,
        TypeWellFormedIn bound
          (parallelTypeBranchesSelecting alphabet selected branches) := by
  obtain ⟨hA, hB, hH, hTC, hCG, hTR, hSC, hPL, hFL, hMO, hPO, hFO, hIS, hIAS,
    hCMO⟩ := h
  have hAoffer := hA
  have hISoffer := hIS
  have hIASoffer := hIAS
  simp only [PactType.AlphabetWellFormed] at hA
  simp only [PactType.AllVariablesBound] at hB
  simp only [PactType.BinderHygienic] at hH
  simp only [PactType.ClockGuarded] at hCG
  simp only [PactType.TailRecursive] at hTR
  simp only [PactType.SameCycleMessageLinear] at hSC
  simp only [PactType.ProgressLinear] at hPL
  simp only [PactType.FairChoiceLinear] at hFL
  simp only [PactType.ParallelMessageOwnership] at hMO
  simp only [PactType.ParallelProgressOwnership] at hPO
  simp only [PactType.ParallelFairChoiceOwnership] at hFO
  simp only [PactType.InterfaceScoped] at hIS
  simp only [PactType.InterfaceAlphabetScoped] at hIAS
  simp only [PactType.ConjunctiveMessageOwnership] at hCMO
  have hBundle := PactType.parallelMessageOwnershipBranches_of_conjuncts
    branches hMO.2 hCMO.2
  have hTCsplit : ∀ other : String,
      PactType.TailOccurrences other True elseType ∧
        PactType.TailBranchOccurrences other False branches := by
    intro other
    simpa only [PactType.TailOccurrences] using hTC other
  have hPairwise : List.Pairwise BranchDeclarationsDisjoint branches :=
    branchDeclarationsDisjoint_pairwise branches hBundle hPO.2 hFO.2
  have hConj := branchesGeneratedChildConjuncts (bound := bound) branches
    hB.2 hH.2 hIS.2 hPL.2.1 hFL.2.1 hBundle hPO.2 hFO.2
  refine ⟨⟨hA.2.2.1, hB.1, hH.1, fun other => (hTCsplit other).1, hCG.1, hTR.1,
      hSC.1, hPL.1, hFL.1, hMO.1, hPO.1, hFO.1, hIS.1, hIAS.2.1,
      hCMO.1⟩, ?_⟩
  intro selected hSelected
  obtain ⟨gB, gH, gS, gP, gF, gM, gPo, gFo⟩ :=
    parallelTypeBranchesSelecting_conjuncts (bound := bound) alphabet selected
      branches hConj hPL.2.1 hFL.2.1 hBundle hPO.2 hFO.2
  have hBranchTailRec : ∀ branch ∈ branches, branch.2.TailRecursive := by
    intro branch hMem
    exact tailRecursive_of_mem_branches hTR.2 hMem
  have hBranchClock : ∀ branch ∈ branches, branch.2.ClockGuarded := by
    have hAux : ∀ list : List (BareMessage × PactType),
        PactType.ClockGuardedBranches list →
        ∀ branch ∈ list, branch.2.ClockGuarded := by
      intro list
      induction list with
      | nil => intro _ branch hMem; cases hMem
      | cons hd tl ihList =>
          rcases hd with ⟨a, t⟩
          intro hList branch hMem
          simp only [PactType.ClockGuardedBranches] at hList
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hTail
          · exact hList.1
          · exact ihList hList.2 branch hTail
    exact hAux branches hCG.2
  have hBranchLinear : PactType.SameCycleMessageLinearBranches branches :=
    hSC.2.1
  exact ⟨committedOffer_alphabetWellFormed alphabet elseType branches selected
      hAoffer hISoffer hIASoffer hSelected,
    gB, gH,
    fun other => parallelTypeBranchesSelecting_tailOccurrences other alphabet
      selected branches True
      (tailBranchOccurrences_of_mem (hTCsplit other).2)
      (tailBranchOccurrences_of_mem (hTCsplit other).2 selected hSelected),
    parallelTypeBranchesSelecting_clockGuarded alphabet selected branches
      hBranchClock (hBranchClock selected hSelected),
    parallelTypeBranchesSelecting_tailRecursive alphabet selected branches
      hBranchTailRec (hBranchTailRec selected hSelected),
    parallelTypeBranchesSelecting_sameCycleMessageLinear alphabet selected
      branches hBranchLinear,
    gP, gF, gM, gPo, gFo, gS,
    parallelTypeBranchesSelecting_interfaceAlphabetScoped alphabet selected
      branches hIAS.2.2
      (fun action hAction hIn =>
        Finset.disjoint_left.mp hIAS.1
          (Finset.mem_image.mpr ⟨action, hAction, rfl⟩)
          (Finset.mem_union_right _ hIn)),
    parallelTypeBranchesSelecting_conjunctiveMessageOwnership alphabet selected
      branches hCMO.2⟩

/-! ### Residual ownership transport (hop 1 of the guard transport)

`ObservationOwnedBy` is defined purely over `MessageActions`, `ProgressIds`
and `FairChoiceIds`, so an observation owned by a residual is owned by the
source once those three sets transport.  The three behave alike, so they are
bundled into one induction. -/

private lemma union_subset_union_union {α : Type} [DecidableEq α]
    {XL XR A B R : Finset α} (hL : XL ⊆ A ∪ R) (hR : XR ⊆ B ∪ R) :
    XL ∪ XR ⊆ (A ∪ B) ∪ R := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp (hL h) with h2 | h2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h2)
    · exact Finset.mem_union_right _ h2
  · rcases Finset.mem_union.mp (hR h) with h2 | h2
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h2)
    · exact Finset.mem_union_right _ h2

theorem branch_subset_parallelBranchInterfaces
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    PactType.ParallelInterfaces branch.2 ⊆
      PactType.ParallelBranchInterfaces branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.ParallelBranchInterfaces]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq; exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

theorem parallelTypeBranchesSelecting_parallelInterfaces
    (alphabet : PactTypeAlphabet) (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.ParallelInterfaces
        (parallelTypeBranchesSelecting alphabet selected branches) =
      PactType.ParallelBranchInterfaces branches := by
  cases branches with
  | nil => simp [parallelTypeBranchesSelecting, PactType.ParallelInterfaces,
      PactType.ParallelBranchInterfaces]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_parallelInterfaces selected
        (branch :: rest) alphabet

theorem replaceVar_ownership_subset (name : String) (replacement : PactType) :
    ∀ processType : PactType,
      PactType.MessageActions (processType.replaceVar name replacement) ⊆
          PactType.MessageActions processType ∪
            PactType.MessageActions replacement ∧
        PactType.ProgressIds (processType.replaceVar name replacement) ⊆
          PactType.ProgressIds processType ∪ PactType.ProgressIds replacement ∧
        PactType.FairChoiceIds (processType.replaceVar name replacement) ⊆
          PactType.FairChoiceIds processType ∪
            PactType.FairChoiceIds replacement ∧
        PactType.MessageIds (processType.replaceVar name replacement) ⊆
          PactType.MessageIds processType ∪ PactType.MessageIds replacement ∧
        PactType.ParallelInterfaces (processType.replaceVar name replacement) ⊆
          PactType.ParallelInterfaces processType ∪
            PactType.ParallelInterfaces replacement := by
  intro processType
  induction hSize : sizeOf processType using Nat.strong_induction_on
      generalizing processType with
  | _ n ih =>
      have hBranches : ∀ branches : List (BareMessage × PactType),
          sizeOf branches < n →
          PactType.BranchMessageActions
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchMessageActions branches ∪
              PactType.MessageActions replacement ∧
          PactType.BranchProgressIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchProgressIds branches ∪
              PactType.ProgressIds replacement ∧
          PactType.BranchFairChoiceIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchFairChoiceIds branches ∪
              PactType.FairChoiceIds replacement ∧
          PactType.BranchMessageIds
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.BranchMessageIds branches ∪
              PactType.MessageIds replacement ∧
          PactType.ParallelBranchInterfaces
              (PactType.replaceBranches branches name replacement) ⊆
            PactType.ParallelBranchInterfaces branches ∪
              PactType.ParallelInterfaces replacement := by
        intro branches hBranchesSize
        induction branches with
        | nil =>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceBranches, PactType.BranchMessageActions,
                PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
                PactType.BranchMessageIds, PactType.ParallelBranchInterfaces]
        | cons branch rest restIH =>
            rcases branch with ⟨action, branchType⟩
            have hBranchSize : sizeOf branchType < n := by
              have h1 : sizeOf branchType < sizeOf (action, branchType) := by
                simp_wf; omega
              have h2 : sizeOf (action, branchType) <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            have hRestSize : sizeOf rest < n := by
              have h3 : sizeOf rest <
                  sizeOf ((action, branchType) :: rest) := by simp_wf; omega
              omega
            obtain ⟨hM, hP, hF, hI, hPI⟩ :=
              ih (sizeOf branchType) hBranchSize branchType rfl
            obtain ⟨rM, rP, rF, rI, rPI⟩ := restIH hRestSize
            simp only [PactType.replaceBranches, PactType.BranchMessageActions,
              PactType.BranchProgressIds, PactType.BranchFairChoiceIds,
              PactType.BranchMessageIds, PactType.ParallelBranchInterfaces]
            refine ⟨union_subset_union_union ?_ rM,
              union_subset_union_union hP rP,
              union_subset_union_union hF rF,
              union_subset_union_union ?_ rI,
              union_subset_union_union hPI rPI⟩
            · exact union_subset_union_union Finset.subset_union_left hM
            · exact union_subset_union_union Finset.subset_union_left hI
      cases processType with
      | message a m d =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | progress a p =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | tock a =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | skip a =>
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [PactType.replaceVar, PactType.MessageActions,
              PactType.ProgressIds, PactType.FairChoiceIds,
              PactType.MessageIds, PactType.ParallelInterfaces]
      | var a other =>
          by_cases hEq : name = other <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceVar, hEq, PactType.MessageActions,
                PactType.ProgressIds, PactType.FairChoiceIds,
                PactType.MessageIds, PactType.ParallelInterfaces]
      | recur a other body =>
          have hB : sizeOf body < n := by rw [← hSize]; simp_wf; omega
          by_cases hEq : name = other
          · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.replaceVar, hEq, PactType.MessageActions,
                PactType.ProgressIds, PactType.FairChoiceIds,
                PactType.MessageIds, PactType.ParallelInterfaces]
          · obtain ⟨hM, hP, hF, hI, hPI⟩ := ih (sizeOf body) hB body rfl
            simp only [PactType.replaceVar, if_neg hEq,
              PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨hM, hP, hF, hI, hPI⟩
      | choice a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | fairChoice a bid l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union
              (union_subset_union_union Finset.subset_union_left lF) rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | seq a l r =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union lPI rPI⟩
      | par a l r i =>
          have hL : sizeOf l < n := by rw [← hSize]; simp_wf; omega
          have hR : sizeOf r < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨lM, lP, lF, lI, lPI⟩ := ih (sizeOf l) hL l rfl
          obtain ⟨rM, rP, rF, rI, rPI⟩ := ih (sizeOf r) hR r rfl
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union lM rM,
            union_subset_union_union lP rP,
            union_subset_union_union lF rF,
            union_subset_union_union lI rI,
            union_subset_union_union
              (union_subset_union_union Finset.subset_union_left lPI) rPI⟩
      | xoffer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨eM, eP, eF, eI, ePI⟩ := ih (sizeOf e) hE e rfl
          obtain ⟨bM, bP, bF, bI, bPI⟩ := hBranches bs hBs
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union eM bM,
            union_subset_union_union eP bP,
            union_subset_union_union eF bF,
            union_subset_union_union eI bI,
            union_subset_union_union ePI bPI⟩
      | offer a e bs =>
          have hE : sizeOf e < n := by rw [← hSize]; simp_wf; omega
          have hBs : sizeOf bs < n := by rw [← hSize]; simp_wf; omega
          obtain ⟨eM, eP, eF, eI, ePI⟩ := ih (sizeOf e) hE e rfl
          obtain ⟨bM, bP, bF, bI, bPI⟩ := hBranches bs hBs
          simp only [PactType.replaceVar, PactType.MessageActions,
            PactType.ProgressIds, PactType.FairChoiceIds,
            PactType.MessageIds, PactType.ParallelInterfaces]
          exact ⟨union_subset_union_union eM bM,
            union_subset_union_union eP bP,
            union_subset_union_union eF bF,
            union_subset_union_union eI bI,
            union_subset_union_union ePI bPI⟩

/-- Top-level form of the generated child's identifier computation. -/
theorem parallelTypeBranchesSelecting_ownership (alphabet : PactTypeAlphabet)
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.MessageIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchMessageIds branches ∧
      PactType.MessageActions
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchMessageActions branches ∧
      PactType.ProgressIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchProgressIds branches ∧
      PactType.FairChoiceIds
        (parallelTypeBranchesSelecting alphabet selected branches) =
        PactType.BranchFairChoiceIds branches := by
  cases branches with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [parallelTypeBranchesSelecting, PactType.MessageActions,
          PactType.ProgressIds, PactType.FairChoiceIds, PactType.MessageIds,
          PactType.BranchMessageActions, PactType.BranchProgressIds,
          PactType.BranchFairChoiceIds, PactType.BranchMessageIds]
  | cons branch rest =>
      simp only [parallelTypeBranchesSelecting]
      exact parallelTypeBranchesSelectingWithin_ownershipData alphabet selected
        (branch :: rest)

/-- Hop 1 of the guard transport: a residual's declared identifiers are among
its source's.  The five sets `LabelOwned` reads are bundled into one induction,
since they behave alike at every clause. -/
theorem relationMembership_ownership_subset :
    ∀ (source residual : PactType) (state : TypeAutomatonState),
      relationMembership (buildRelationSet source (compileType source))
        residual state →
      PactType.MessageActions residual ⊆ PactType.MessageActions source ∧
        PactType.ProgressIds residual ⊆ PactType.ProgressIds source ∧
        PactType.FairChoiceIds residual ⊆ PactType.FairChoiceIds source ∧
        PactType.MessageIds residual ⊆ PactType.MessageIds source ∧
        PactType.ParallelInterfaces residual ⊆
          PactType.ParallelInterfaces source := by
  intro source
  induction hFuel : typeCompilationFuel source using Nat.strong_induction_on
      generalizing source with
  | _ n ih =>
      intro residual state hRelated
      cases source with
      | skip a =>
          obtain ⟨hR, -⟩ := relationMembership_skip_cases a hRelated
          subst hR
          exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
            Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
      | var a name =>
          obtain ⟨hR, -⟩ := relationMembership_var_cases a name hRelated
          subst hR
          exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
            Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
      | message a m d =>
          rcases relationMembership_message_cases a m d hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | tock a =>
          rcases relationMembership_tock_cases a hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | progress a p =>
          rcases relationMembership_progress_cases a p hRelated with
            ⟨hR, -⟩ | ⟨hR, -⟩ <;> subst hR <;>
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | choice a l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_choice_cases a l r hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨q, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | fairChoice a bid l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_fairChoice_cases a bid l r hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨q, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans (Finset.subset_union_right.trans Finset.subset_union_left),
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | seq a l r =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_seq_cases a l r hRelated with
            ⟨q1, ρ, hEntry, hChild, -⟩ | ⟨q2, -, hChild⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hL l rfl ρ q1 hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨Finset.union_subset_union m (Finset.Subset.refl _),
              Finset.union_subset_union p (Finset.Subset.refl _),
              Finset.union_subset_union f (Finset.Subset.refl _),
              Finset.union_subset_union mi (Finset.Subset.refl _),
              Finset.union_subset_union pi (Finset.Subset.refl _)⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hR r rfl residual q2 hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
      | recur a name body =>
          have hB : typeCompilationFuel body < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_recur_cases a name body hRelated with
            hRoot | ⟨q, ρ, hEntry, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hB body rfl ρ q hChild
            obtain ⟨sm, sp, sf, smi, spi⟩ :=
              replaceVar_ownership_subset name (.recur a name body) ρ
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces] at m p f mi pi ⊢
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · intro x hx
              rcases Finset.mem_union.mp (sm hx) with h | h
              · exact m h
              · simpa [PactType.MessageActions] using h
            · intro x hx
              rcases Finset.mem_union.mp (sp hx) with h | h
              · exact p h
              · simpa [PactType.ProgressIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (sf hx) with h | h
              · exact f h
              · simpa [PactType.FairChoiceIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (smi hx) with h | h
              · exact mi h
              · simpa [PactType.MessageIds] using h
            · intro x hx
              rcases Finset.mem_union.mp (spi hx) with h | h
              · exact pi h
              · simpa [PactType.ParallelInterfaces] using h
      | par a l r i =>
          have hL : typeCompilationFuel l < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hR : typeCompilationFuel r < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          have hLre : typeCompilationFuel (l.reannotate a) < n := by
            rw [typeCompilationFuel_reannotate]; exact hL
          have hRre : typeCompilationFuel (r.reannotate a) < n := by
            rw [typeCompilationFuel_reannotate]; exact hR
          rcases relationMembership_par_cases a l r i hRelated with
            ⟨q1, q2, ρl, ρr, hEntry, hLeft, hRight⟩ |
            ⟨q1, ρl, hEntry, hLeft, -⟩ | ⟨q2, ρr, hEntry, hRight, -⟩ | hFinal
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨lm, lp, lf, lmi, lpi⟩ := ih _ hL l rfl ρl q1 hLeft
            obtain ⟨rm, rp, rf, rmi, rpi⟩ := ih _ hR r rfl ρr q2 hRight
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨Finset.union_subset (lm.trans Finset.subset_union_left)
                (rm.trans Finset.subset_union_right),
              Finset.union_subset (lp.trans Finset.subset_union_left)
                (rp.trans Finset.subset_union_right),
              Finset.union_subset (lf.trans Finset.subset_union_left)
                (rf.trans Finset.subset_union_right),
              Finset.union_subset (lmi.trans Finset.subset_union_left)
                (rmi.trans Finset.subset_union_right),
              Finset.union_subset_union
                (Finset.union_subset_union (Finset.Subset.refl _) lpi) rpi⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hLre (l.reannotate a) rfl _ q1 hLeft
            rw [PactType.reannotate_messageActions] at m
            rw [PactType.reannotate_progressIds] at p
            rw [PactType.reannotate_fairChoiceIds] at f
            rw [PactType.reannotate_messageIds] at mi
            rw [PactType.reannotate_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans (Finset.subset_union_right.trans
                Finset.subset_union_left)⟩
          · injection hEntry with hRes hStateEq
            subst hRes
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hRre (r.reannotate a) rfl _ q2 hRight
            rw [PactType.reannotate_messageActions] at m
            rw [PactType.reannotate_progressIds] at p
            rw [PactType.reannotate_fairChoiceIds] at f
            rw [PactType.reannotate_messageIds] at mi
            rw [PactType.reannotate_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩
          · injection hFinal with hRes hStateEq
            subst hRes
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [PactType.MessageActions, PactType.ProgressIds,
                PactType.FairChoiceIds, PactType.MessageIds,
                PactType.ParallelInterfaces]
      | xoffer a e bs =>
          have hE : typeCompilationFuel e < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_xoffer_cases a e bs hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨idx, action, branchType, q, hGet, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hE e rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · have hMem : (action, branchType) ∈ bs := List.mem_of_getElem? hGet
            have hBF : typeCompilationFuel branchType < n := by
              rw [← hFuel]
              simp only [typeCompilationFuel]
              have hLe : typeCompilationFuel branchType ≤
                  typeBranchCompilationFuel bs :=
                typeCompilationFuel_le_typeBranchCompilationFuel bs
                  (action, branchType) hMem
              have hMax : typeBranchCompilationFuel bs ≤
                  max (typeCompilationFuel e) (typeBranchCompilationFuel bs) :=
                le_max_right _ _
              omega
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hBF branchType rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            refine ⟨(m.trans ?_).trans Finset.subset_union_right,
              (p.trans ?_).trans Finset.subset_union_right,
              (f.trans ?_).trans Finset.subset_union_right,
              (mi.trans ?_).trans Finset.subset_union_right,
              (pi.trans ?_).trans Finset.subset_union_right⟩
            · exact Finset.subset_union_right.trans
                (branch_subset_branchMessageActions hMem)
            · exact branch_subset_branchProgressIds hMem
            · exact branch_subset_branchFairChoiceIds hMem
            · exact Finset.subset_union_right.trans
                (branch_subset_branchMessageIds hMem)
            · exact branch_subset_parallelBranchInterfaces hMem
      | offer a e bs =>
          have hE : typeCompilationFuel e < n := by
            rw [← hFuel]; simp only [typeCompilationFuel]; omega
          rcases relationMembership_offer_cases a e bs hRelated with
            hRoot | ⟨q, -, hChild⟩ | ⟨idx, selected, q, hGet, -, hChild⟩
          · injection hRoot with hRes hStateEq
            subst hRes
            exact ⟨Finset.Subset.refl _, Finset.Subset.refl _,
              Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _⟩
          · obtain ⟨m, p, f, mi, pi⟩ := ih _ hE e rfl residual q hChild
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_left,
              p.trans Finset.subset_union_left,
              f.trans Finset.subset_union_left,
              mi.trans Finset.subset_union_left,
              pi.trans Finset.subset_union_left⟩
          · have hGF : typeCompilationFuel
                (parallelTypeBranchesSelecting a selected bs) < n := by
              rw [← hFuel, typeCompilationFuel_parallelTypeBranchesSelecting]
              simp only [typeCompilationFuel]; omega
            obtain ⟨m, p, f, mi, pi⟩ := ih _ hGF
              (parallelTypeBranchesSelecting a selected bs) rfl residual q hChild
            obtain ⟨gI, gm, gp, gf⟩ :=
              parallelTypeBranchesSelecting_ownership a selected bs
            rw [gm] at m; rw [gp] at p; rw [gf] at f; rw [gI] at mi
            rw [parallelTypeBranchesSelecting_parallelInterfaces] at pi
            simp only [PactType.MessageActions, PactType.ProgressIds,
              PactType.FairChoiceIds, PactType.MessageIds,
              PactType.ParallelInterfaces]
            exact ⟨m.trans Finset.subset_union_right,
              p.trans Finset.subset_union_right,
              f.trans Finset.subset_union_right,
              mi.trans Finset.subset_union_right,
              pi.trans Finset.subset_union_right⟩

/-- Hop 1, in the form the guard transport uses it: an observation owned by a
residual is owned by its source. -/
theorem relationMembership_observationOwnedBy
    {source residual : PactType} {state : TypeAutomatonState}
    {observation : TypeObservation}
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state)
    (hOwned : ObservationOwnedBy residual observation) :
    ObservationOwnedBy source observation := by
  obtain ⟨hM, hP, hF, hMI, hPI⟩ :=
    relationMembership_ownership_subset source residual state hRelated
  cases observation with
  | message msg dir => exact hM hOwned
  | resolved msg => exact ⟨hM hOwned.1, hM hOwned.2⟩
  | progress pid => exact hP hOwned
  | fair bid tag => exact hF hOwned

/-- Hop 1 at the level of labels: a label supported by a residual is supported
by its source.  Combined with `offers_label_supported` this takes a decorated
step of a residual to support at the enclosing child type. -/
theorem relationMembership_labelSupportedBy
    {source residual : PactType} {state : TypeAutomatonState}
    {label : TypeLabel}
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state)
    (hSupported : LabelSupportedBy residual label) :
    LabelSupportedBy source label := by
  cases label with
  | tock => trivial
  | actions observations =>
      intro observation hMem
      exact relationMembership_observationOwnedBy hRelated
        (hSupported observation hMem)

/-- Hop 1 at the level of `LabelOwned`, which is the predicate the guard
transport actually wants: unlike `LabelSupportedBy` it records that a
`resolved` observation comes from an interface, so the `resolved` case needs no
separate argument. -/
theorem relationMembership_labelOwned
    {source residual : PactType} {state : TypeAutomatonState}
    {label : TypeLabel}
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state)
    (hOwned : residual.LabelOwned label) :
    source.LabelOwned label := by
  obtain ⟨hM, hP, hF, hMI, hPI⟩ :=
    relationMembership_ownership_subset source residual state hRelated
  obtain ⟨hMsg, hProg, hFair, hRes⟩ := hOwned
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro msg dir hContains
    exact ⟨hM (hMsg msg dir hContains).1, hMI (hMsg msg dir hContains).2⟩
  · intro pid hContains
    exact hP (hProg pid hContains)
  · intro bid taken hContains
    exact hF (hFair bid taken hContains)
  · intro msg hContains
    exact ⟨hPI (hRes msg hContains).1, hMI (hRes msg hContains).2⟩

/-- The guard transport in the form the step component uses: a decorated step of
a residual has its label owned by the enclosing source type.  Label ownership is
taken from the offers half of `DecoratedTypeTransition`, where it is proved. -/
theorem relationMembership_decoratedTransition_labelOwned
    {source residual target : PactType} {state : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary}
    (hRelated : relationMembership (buildRelationSet source (compileType source))
      residual state)
    (hStep : DecoratedTypeTransition env residual label offers target) :
    source.LabelOwned label :=
  relationMembership_labelOwned hRelated (TypeOffers.labelOwned hStep.2)

/-! ### Reachability transport into a child copy -/

private theorem automatonStateReachable_binaryChoice_child0
    {whole left right : PactType} {alphabet : PactTypeAlphabet}
    {selL selR : TypeLabel}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildChoiceAutomaton alphabet
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right) selL selR)
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 0 q)) :
    AutomatonStateReachable left q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildChoiceAutomaton, finishAutomatonFragment,
        childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
      Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with (⟨childEdge, hChild, hEq⟩ | ⟨childEdge, hChild, hEq⟩) |
      ⟨env, -, hSel | hSel⟩
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq,
        true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq]
        at hTarget
      exact absurd hTarget.1 (by decide)
    · subst hSel
      simp only [childState, TypeAutomatonState.child.injEq, true_and] at hTarget
      exact Or.inr hTarget.symm
    · subst hSel
      simp only [childState, TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by decide)

private theorem automatonStateReachable_binaryChoice_child1
    {whole left right : PactType} {alphabet : PactTypeAlphabet}
    {selL selR : TypeLabel}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildChoiceAutomaton alphabet
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right) selL selR)
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 1 q)) :
    AutomatonStateReachable right q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildChoiceAutomaton, finishAutomatonFragment,
        childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildChoiceAutomaton, finishAutomatonFragment, childPendingEdges,
      Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with (⟨childEdge, hChild, hEq⟩ | ⟨childEdge, hChild, hEq⟩) |
      ⟨env, -, hSel | hSel⟩
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq]
        at hTarget
      exact absurd hTarget.1 (by decide)
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq,
        true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · subst hSel
      simp only [childState, TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by decide)
    · subst hSel
      simp only [childState, TypeAutomatonState.child.injEq, true_and] at hTarget
      exact Or.inr hTarget.symm

private theorem automatonStateReachable_sequence_child0
    {whole left right : PactType}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildSequenceAutomaton
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right))
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 0 q)) :
    AutomatonStateReachable left q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    have : (compileType whole).initial =
        childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial := by
      simp [compileType, hWhole, buildSequenceAutomaton, finishAutomatonFragment]
    rw [this] at hEq
    simp only [childState, TypeAutomatonState.child.injEq, true_and] at hEq
    exact hEq.symm
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
      childPendingEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      at hMem
    rcases hMem with (⟨childEdge, ⟨hChild, -⟩, hEq⟩ | ⟨childEdge, hChild, hEq⟩) |
      ⟨childEdge, ⟨hChild, -⟩, hEq⟩
    · subst hEq
      simp only [sequenceKeptLeftEdge, childState,
        TypeAutomatonState.child.injEq, true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq]
        at hTarget
      exact absurd hTarget.1 (by decide)
    · subst hEq
      simp only [sequenceRedirectEdge, childState,
        TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by decide)

private theorem automatonStateReachable_sequence_child1
    {whole left right : PactType}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildSequenceAutomaton
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right))
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 1 q)) :
    AutomatonStateReachable right q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    have hInit : (compileType whole).initial =
        childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial := by
      simp [compileType, hWhole, buildSequenceAutomaton, finishAutomatonFragment]
    rw [hInit] at hEq
    simp only [childState, TypeAutomatonState.child.injEq] at hEq
    exact absurd hEq.1 (by decide)
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
      childPendingEdges, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      at hMem
    rcases hMem with (⟨childEdge, ⟨hChild, -⟩, hEq⟩ | ⟨childEdge, hChild, hEq⟩) |
      ⟨childEdge, ⟨hChild, -⟩, hEq⟩
    · subst hEq
      simp only [sequenceKeptLeftEdge, childState,
        TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by decide)
    · subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq,
        true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · subst hEq
      simp only [sequenceRedirectEdge, childState,
        TypeAutomatonState.child.injEq, true_and] at hTarget
      exact Or.inr hTarget.symm

private theorem automatonStateReachable_exclusiveOffer_child0
    {whole elseType : PactType} {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)))
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 0 q)) :
    AutomatonStateReachable elseType q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hMem
    rcases hMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, hChild, hEq⟩ := hElse
      subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq,
        true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        obtain ⟨childEdge, -, hEq⟩ := hChild
        subst hEq
        simp only [childPendingEdge, childState,
          TypeAutomatonState.child.injEq] at hTarget
        exact absurd hTarget.1 (by omega)
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        obtain ⟨env, -, hEq⟩ := hRoot
        subst hEq
        simp only [childState, TypeAutomatonState.child.injEq] at hTarget
        exact absurd hTarget.1 (by omega)
    · obtain ⟨env, -, hEq⟩ := hWait
      subst hEq
      simp only [childState] at hTarget
      exact absurd hTarget (by simp)
    · obtain ⟨env, -, hEq⟩ := hResolved
      subst hEq
      simp only [childState, TypeAutomatonState.child.injEq, true_and] at hTarget
      exact Or.inr hTarget.symm

private theorem automatonStateReachable_exclusiveOffer_branch
    {whole elseType : PactType} {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)))
    {index : Nat} {action : BareMessage} {branchType : PactType}
    (hGet : branches[index]? = some (action, branchType))
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState (index + 1) q)) :
    AutomatonStateReachable branchType q := by
  have hMapGet : (branches.map fun branch =>
      (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2))[index]? =
      some (action, compileTypeFuel (typeCompilationFuel branchType) branchType) := by
    rw [List.getElem?_map, hGet]; rfl
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildExclusiveOfferAutomaton,
        finishAutomatonFragment, childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hMem
    rcases hMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, -, hEq⟩ := hElse
      subst hEq
      simp only [childPendingEdge, childState,
        TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by omega)
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        obtain ⟨childEdge, hChildMem, hEq⟩ := hChild
        subst hEq
        simp only [childPendingEdge, childState,
          TypeAutomatonState.child.injEq] at hSource hTarget hLabel
        have hIndexEq : indexed.2 = index := by omega
        have hEntry := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [hIndexEq, hMapGet] at hEntry
        have hAuto : indexed.1.2 =
            compileTypeFuel (typeCompilationFuel branchType) branchType := by
          rw [Option.some.injEq] at hEntry
          rw [← hEntry]
        rw [hAuto] at hChildMem
        refine Or.inl ⟨childEdge.source, ?_, ?_⟩
        · rw [← hSource, hIndexEq]; rfl
        · rw [automatonEdgeStep_iff_fragmentEdge]
          exact ⟨childEdge, hChildMem, rfl, hTarget.2, label, hLabel⟩
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        obtain ⟨env, -, hEq⟩ := hRoot
        subst hEq
        simp only [childState, TypeAutomatonState.child.injEq] at hTarget
        have hIndexEq : indexed.2 = index := by omega
        have hEntry := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [hIndexEq, hMapGet] at hEntry
        have hAuto : indexed.1.2 =
            compileTypeFuel (typeCompilationFuel branchType) branchType := by
          rw [Option.some.injEq] at hEntry
          rw [← hEntry]
        rw [← hTarget.2, hAuto]
        exact Or.inr rfl
    · obtain ⟨env, -, hEq⟩ := hWait
      subst hEq
      simp only [childState] at hTarget
      exact absurd hTarget (by simp)
    · obtain ⟨env, -, hEq⟩ := hResolved
      subst hEq
      simp only [childState, TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by omega)

private theorem automatonStateReachable_conjunctiveOffer_child0
    {whole elseType : PactType} {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildSelectedConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun selected =>
          (selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches))))
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState 0 q)) :
    AutomatonStateReachable elseType q := by
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hMem
    rcases hMem with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · obtain ⟨childEdge, hChild, hEq⟩ := hElse
      subst hEq
      simp only [childPendingEdge, childState, TypeAutomatonState.child.injEq,
        true_and] at hSource hTarget hLabel
      refine Or.inl ⟨childEdge.source, hSource.symm ▸ rfl, ?_⟩
      rw [automatonEdgeStep_iff_fragmentEdge]
      exact ⟨childEdge, hChild, rfl, hTarget, label, hLabel⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        obtain ⟨childEdge, -, hEq⟩ := hChild
        subst hEq
        simp only [childPendingEdge, childState,
          TypeAutomatonState.child.injEq] at hTarget
        exact absurd hTarget.1 (by omega)
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        obtain ⟨env, -, hEq⟩ := hRoot
        subst hEq
        simp only [childState, TypeAutomatonState.child.injEq] at hTarget
        exact absurd hTarget.1 (by omega)
    · obtain ⟨env, -, hEq⟩ := hWait
      subst hEq
      simp only [childState] at hTarget
      exact absurd hTarget (by simp)
    · obtain ⟨env, -, hEq⟩ := hResolved
      subst hEq
      simp only [childState, TypeAutomatonState.child.injEq, true_and] at hTarget
      exact Or.inr hTarget.symm

private theorem automatonStateReachable_conjunctiveOffer_branch
    {whole elseType : PactType} {alphabet : PactTypeAlphabet}
    {branches : List (BareMessage × PactType)}
    (hWhole : compileTypeFuel (typeCompilationFuel whole) whole =
      buildSelectedConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun selected =>
          (selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches))))
    {index : Nat} {selected : BareMessage × PactType}
    (hGet : branches[index]? = some selected)
    {q : TypeAutomatonState}
    (hReach : AutomatonStateReachable whole (childState (index + 1) q)) :
    AutomatonStateReachable
      (parallelTypeBranchesSelecting alphabet selected branches) q := by
  have hMapGet : (branches.map fun sel =>
      (sel.1,
        compileTypeFuel
          (typeCompilationFuel (parallelTypeBranchesSelecting alphabet sel branches))
          (parallelTypeBranchesSelecting alphabet sel branches)))[index]? =
      some (selected.1,
        compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches)) := by
    rw [List.getElem?_map, hGet]; rfl
  refine automatonStateReachable_child ?_ ?_ hReach
  · intro target hEq
    exact absurd hEq (by
      simp [compileType, hWhole, buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, childState])
  · intro source target hStep
    rw [automatonEdgeStep_iff_fragmentEdge, hWhole] at hStep
    obtain ⟨edge, hMem, hSource, hTarget, label, hLabel⟩ := hStep
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hMem
    rcases hMem with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · obtain ⟨childEdge, -, hEq⟩ := hElse
      subst hEq
      simp only [childPendingEdge, childState,
        TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by omega)
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        obtain ⟨childEdge, hChildMem, hEq⟩ := hChild
        subst hEq
        simp only [childPendingEdge, childState,
          TypeAutomatonState.child.injEq] at hSource hTarget hLabel
        have hIndexEq : indexed.2 = index := by omega
        have hEntry := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [hIndexEq, hMapGet] at hEntry
        have hAuto : indexed.1.2 =
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches) := by
          rw [Option.some.injEq] at hEntry
          rw [← hEntry]
        rw [hAuto] at hChildMem
        refine Or.inl ⟨childEdge.source, ?_, ?_⟩
        · rw [← hSource, hIndexEq]; rfl
        · rw [automatonEdgeStep_iff_fragmentEdge]
          exact ⟨childEdge, hChildMem, rfl, hTarget.2, label, hLabel⟩
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, hIndexedMem, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        obtain ⟨env, -, hEq⟩ := hRoot
        subst hEq
        simp only [childState, TypeAutomatonState.child.injEq] at hTarget
        have hIndexEq : indexed.2 = index := by omega
        have hEntry := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [hIndexEq, hMapGet] at hEntry
        have hAuto : indexed.1.2 =
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches) := by
          rw [Option.some.injEq] at hEntry
          rw [← hEntry]
        rw [← hTarget.2, hAuto]
        exact Or.inr rfl
    · obtain ⟨env, -, hEq⟩ := hWait
      subst hEq
      simp only [childState] at hTarget
      exact absurd hTarget (by simp)
    · obtain ⟨env, -, hEq⟩ := hResolved
      subst hEq
      simp only [childState, TypeAutomatonState.child.injEq] at hTarget
      exact absurd hTarget.1 (by omega)

/-! ### The menu equation at a binary-choice root -/

/-- Compiling a binary choice at its own budget builds the choice automaton
over the two children compiled at theirs. -/
theorem compileTypeFuel_choice_eq (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    compileTypeFuel (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) =
      buildChoiceAutomaton alphabet
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right)
        TypeLabel.silent TypeLabel.silent := by
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  rw [compileTypeFuel_eq_of_sufficient left (Nat.le_max_left _ _)
      (Nat.le_refl _),
    compileTypeFuel_eq_of_sufficient right (Nat.le_max_right _ _)
      (Nat.le_refl _)]

/-- A reachable state is a state of the compiled fragment. -/
theorem automatonStateReachable_mem_states (processType : PactType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    {state : TypeAutomatonState}
    (hReach : AutomatonStateReachable processType state) :
    state ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).states := by
  induction hReach with
  | refl =>
      exact compileTypeFuel_initial_mem (typeCompilationFuel processType)
        processType (Nat.le_refl _)
  | tail _ hStep ih =>
      obtain ⟨edge, hEdge, -, hTarget, -⟩ :=
        (automatonEdgeStep_iff_fragmentEdge processType _ _).mp hStep
      rw [← hTarget]
      exact compileTypeFuel_edgeTargetsInStates (typeCompilationFuel processType)
        processType (Nat.le_refl _) hDisjoint edge hEdge

/-- Every state named by the compiler relation belongs to the compiled
fragment's carrier. -/
theorem relationMembership_state_mem
    (processType residual : PactType) (state : TypeAutomatonState)
    (hRelated : relationMembership
      (buildRelationSet processType (compileType processType)) residual state) :
    state ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).states := by
  sorry

/-- The compiled menu is bounded by the type's own alphabet.  With the gate on
`computeFutureOfFuel` this is the paper's typing `X : Q_τ → 2^(Ω(τ))` directly,
rather than an induction over the saturation. -/
theorem computeFutureOf_subset_alphabet (processType : PactType)
    (state : TypeAutomatonState) :
    computeFutureOf processType state ⊆ processType.alphabet.actions := by
  classical
  unfold computeFutureOf
  obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel processType = k + 1 :=
    ⟨typeCompilationFuel processType - 1, by
      have := typeCompilationFuel_positive processType
      omega⟩
  rw [hk, computeFutureOfFuel]
  intro action hAction
  exact (Finset.mem_filter.mp hAction).2

/-- Every offer a builder publishes at an edge is declared by the type's own
alphabet.  The `.explicit` clause is cheap: every explicit future a builder
emits is `∅`, except on `.variable` edges, which `compileType` drops. -/
def EdgeOffersLocal (processType : PactType) : Prop :=
  ∀ edge ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).edges,
    edge.current ⊆ processType.alphabet.actions ∧
      ∀ offers, edge.future = .explicit offers →
        offers ⊆ processType.alphabet.actions

/-- Every environment on a compiled fragment's edges comes from the type's own
alphabet.  This is the edge half of the composite `BaseGuard`; the builders all
filter their own environments out of `localEnvironments` and copy their
children's edges unchanged, so it descends structurally. -/
def EdgeEnvironmentsLocal (processType : PactType) : Prop :=
  ∀ edge ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).edges,
    edge.environment ∈ processType.alphabet.localEnvironments

/-- The sum builder keeps edge environments local for any pair of selection
labels; `.choice` and `.fairChoice` differ only in those labels. -/
private lemma sumBuilder_edge_families (alphabet : PactTypeAlphabet)
    (left right : PactType) (selLeft selRight : TypeLabel)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeEnvironmentsLocal left)
    (hRight : EdgeEnvironmentsLocal right)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildChoiceAutomaton alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      selLeft selRight).edges) :
    edge.environment ∈ alphabet.localEnvironments := by
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (hChild | hChild) | hSelect
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    have := hLeft childEdge hChildMem
    rw [hLeftAlphabet] at this
    simpa [childPendingEdge] using this
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    have := hRight childEdge hChildMem
    rw [hRightAlphabet] at this
    simpa [childPendingEdge] using this
  · simp only [Finset.mem_biUnion, Finset.mem_filter] at hSelect
    obtain ⟨environment, ⟨hLocal, -⟩, hMem⟩ := hSelect
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | rfl <;> exact hLocal

/-- Saturation only ever unions `offersAt` over the states it collects, so a
bound on every state's own published offers bounds the whole menu.  This is the
Lean counterpart of the paper's typing `X : Q_τ → 2^(Ω(τ))`. -/
private lemma offersAt_subset_of_edgeOffers {processType : PactType}
    (hOffers : EdgeOffersLocal processType) (state : TypeAutomatonState) :
    PendingAutomaton.offersAt
        { states := (compileTypeFuel (typeCompilationFuel processType)
            processType).states,
          edges := (compileTypeFuel (typeCompilationFuel processType)
            processType).edges } state ⊆ processType.alphabet.actions := by
  classical
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter] at hAction
  obtain ⟨edge, ⟨hEdgeMem, -⟩, hIn⟩ := hAction
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · rw [if_pos hTock] at hIn
    exact absurd hIn (Finset.notMem_empty _)
  · rw [if_neg hTock] at hIn
    rcases Finset.mem_union.mp hIn with hCurrent | hFuture
    · exact (hOffers edge hEdgeMem).1 hCurrent
    · cases hSpec : edge.future with
      | explicit offers =>
          rw [hSpec] at hFuture
          simp only at hFuture
          exact (hOffers edge hEdgeMem).2 offers hSpec hFuture
      | «at» t r =>
          rw [hSpec] at hFuture
          simp only at hFuture
          exact absurd hFuture (Finset.notMem_empty _)

/-- The sum builder keeps published offers local for any selection labels. -/
private lemma sumBuilder_edge_offers (alphabet : PactTypeAlphabet)
    (left right : PactType) (selLeft selRight : TypeLabel)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeOffersLocal left) (hRight : EdgeOffersLocal right)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildChoiceAutomaton alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      selLeft selRight).edges) :
    edge.current ⊆ alphabet.actions ∧
      ∀ offers, edge.future = .explicit offers → offers ⊆ alphabet.actions := by
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (hChild | hChild) | hSelect
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    obtain ⟨hCur, hFut⟩ := hLeft childEdge hChildMem
    rw [hLeftAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    obtain ⟨hCur, hFut⟩ := hRight childEdge hChildMem
    rw [hRightAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · simp only [Finset.mem_biUnion, Finset.mem_filter] at hSelect
    obtain ⟨environment, -, hMem⟩ := hSelect
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | rfl <;> exact ⟨by simp, by intro _ h; simp at h⟩

/-- The fuel-parametrized form of both locality predicates.  The `.par` builder
compiles re-stamped children at the same fuel, and `reannotate` preserves size,
so only an induction on fuel reaches them. -/
def EdgeLocalAt (fuel : Nat) (processType : PactType) : Prop :=
  ∀ edge ∈ (compileTypeFuel fuel processType).edges,
    edge.environment ∈ processType.alphabet.localEnvironments ∧
      edge.current ⊆ processType.alphabet.actions ∧
      ∀ offers, edge.future = .explicit offers →
        offers ⊆ processType.alphabet.actions

/-- At a sufficient budget the fuel-parametrized form is the pair of predicates
the guard consumes. -/
theorem edgeLocal_of_edgeLocalAt {processType : PactType} {fuel : Nat}
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hLocal : EdgeLocalAt fuel processType) :
    EdgeEnvironmentsLocal processType ∧ EdgeOffersLocal processType := by
  have hEq : compileTypeFuel (typeCompilationFuel processType) processType =
      compileTypeFuel fuel processType :=
    compileTypeFuel_eq_of_sufficient processType (le_refl _) hFuel
  refine ⟨fun edge hEdge => ?_, fun edge hEdge => ?_⟩ <;> rw [hEq] at hEdge
  · exact (hLocal edge hEdge).1
  · exact (hLocal edge hEdge).2

/-- The converse bridge: a locality proof at the type's own budget transports to
any sufficient budget. -/
theorem edgeLocalAt_of_edgeLocal {processType : PactType} {fuel : Nat}
    (hFuel : TypeCompilationFuelSufficient processType fuel)
    (hLocal : EdgeEnvironmentsLocal processType ∧ EdgeOffersLocal processType) :
    EdgeLocalAt fuel processType := by
  have hEq : compileTypeFuel (typeCompilationFuel processType) processType =
      compileTypeFuel fuel processType :=
    compileTypeFuel_eq_of_sufficient processType (le_refl _) hFuel
  intro edge hEdge
  rw [← hEq] at hEdge
  exact ⟨hLocal.1 edge hEdge, hLocal.2 edge hEdge⟩

/-- Edge locality at the leaves.  Every builder draws its environments from
`localEnvironments` and its currents from `∅` or a gated singleton. -/
private lemma edgeLocal_skip (alphabet : PactTypeAlphabet) :
    EdgeEnvironmentsLocal (.skip alphabet) ∧ EdgeOffersLocal (.skip alphabet) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image, Finset.mem_filter] at hEdge <;>
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hEdge
  · exact hLocal
  · exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_var (alphabet : PactTypeAlphabet) (name : String) :
    EdgeEnvironmentsLocal (.var alphabet name) ∧
      EdgeOffersLocal (.var alphabet name) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image, Finset.mem_filter] at hEdge <;>
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hEdge
  · exact hLocal
  · exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    EdgeEnvironmentsLocal (.message alphabet msg dir) ∧
      EdgeOffersLocal (.message alphabet msg dir) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge <;>
    rcases hEdge with (⟨environment, ⟨hLocal, hCond⟩, rfl⟩ |
      ⟨environment, ⟨hLocal, hCond⟩, rfl⟩) | ⟨environment, ⟨hLocal, -⟩, rfl⟩
  · exact hLocal
  · exact hLocal
  · exact hLocal
  · exact ⟨by simpa using hCond.2, by intro _ h; simp at h⟩
  · exact ⟨by simpa using hCond.2.2, by intro _ h; simp at h⟩
  · exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_tock (alphabet : PactTypeAlphabet) :
    EdgeEnvironmentsLocal (.tock alphabet) ∧ EdgeOffersLocal (.tock alphabet) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge <;>
    rcases hEdge with ⟨environment, hLocal, rfl⟩ | ⟨environment, ⟨hLocal, -⟩, rfl⟩
  · split <;> exact hLocal
  · exact hLocal
  · split <;>
      exact ⟨by simp, by
        intro _ h
        simp only [] at h
        cases h
        first
          | (simp; done)
          | done⟩
  · exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_progress (alphabet : PactTypeAlphabet)
    (pid : ProcId) :
    EdgeEnvironmentsLocal (.progress alphabet pid) ∧
      EdgeOffersLocal (.progress alphabet pid) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge <;>
    rcases hEdge with ⟨environment, ⟨hLocal, -⟩, rfl⟩ | ⟨environment, ⟨hLocal, -⟩, rfl⟩
  · exact hLocal
  · exact hLocal
  · exact ⟨by simp, by intro _ h; simp at h⟩
  · exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeEnvironmentsLocal left ∧ EdgeOffersLocal left)
    (hRight : EdgeEnvironmentsLocal right ∧ EdgeOffersLocal right) :
    EdgeEnvironmentsLocal (.choice alphabet left right) ∧
      EdgeOffersLocal (.choice alphabet left right) := by
  refine ⟨fun edge hEdge => ?_, fun edge hEdge => ?_⟩ <;>
    rw [compileTypeFuel_choice_eq alphabet left right] at hEdge
  · exact sumBuilder_edge_families alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.1 hRight.1 edge hEdge
  · exact sumBuilder_edge_offers alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.2 hRight.2 edge hEdge

/-- Compiling a sequence at its own budget builds the sequence automaton over
the two children compiled at theirs. -/
theorem compileTypeFuel_seq_eq (alphabet : PactTypeAlphabet)
    (left right : PactType) :
    compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) =
      buildSequenceAutomaton
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right) := by
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  rw [compileTypeFuel_eq_of_sufficient left (Nat.le_max_left _ _)
      (Nat.le_refl _),
    compileTypeFuel_eq_of_sufficient right (Nat.le_max_right _ _)
      (Nat.le_refl _)]

private lemma edgeLocal_seq (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeEnvironmentsLocal left ∧ EdgeOffersLocal left)
    (hRight : EdgeEnvironmentsLocal right ∧ EdgeOffersLocal right) :
    EdgeEnvironmentsLocal (.seq alphabet left right) ∧
      EdgeOffersLocal (.seq alphabet left right) := by
  classical
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_seq_eq alphabet left right] at hEdge <;>
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      sequenceLeftEdges, sequenceRightEdges, sequenceRedirectEdges,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hEdge <;>
    rcases hEdge with (⟨childEdge, ⟨hChildMem, -⟩, rfl⟩ |
      ⟨childEdge, hChildMem, rfl⟩) | ⟨childEdge, ⟨hChildMem, -⟩, rfl⟩
  · have := hLeft.1 childEdge hChildMem
    rw [hLeftAlphabet] at this
    simpa [sequenceKeptLeftEdge] using this
  · have := hRight.1 childEdge hChildMem
    rw [hRightAlphabet] at this
    simpa [childPendingEdge] using this
  · have := hLeft.1 childEdge hChildMem
    rw [hLeftAlphabet] at this
    simpa [sequenceRedirectEdge] using this
  · obtain ⟨hCur, -⟩ := hLeft.2 childEdge hChildMem
    rw [hLeftAlphabet] at hCur
    refine ⟨by simpa [sequenceKeptLeftEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [sequenceKeptLeftEdge, sequenceRedirectFutureSpec] at hOffers
    split at hOffers
    · cases hOffers; simp
    · exact absurd hOffers (by simp)
  · obtain ⟨hCur, hFut⟩ := hRight.2 childEdge hChildMem
    rw [hRightAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · obtain ⟨hCur, -⟩ := hLeft.2 childEdge hChildMem
    rw [hLeftAlphabet] at hCur
    refine ⟨by simpa [sequenceRedirectEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [sequenceRedirectEdge, sequenceRedirectFutureSpec] at hOffers
    split at hOffers
    · cases hOffers; simp
    · exact absurd hOffers (by simp)

/-- Compiling a recursion at its own budget builds the recursion automaton over
the body compiled at its own. -/
theorem compileTypeFuel_recur_eq (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType) :
    compileTypeFuel (typeCompilationFuel (.recur alphabet name body))
        (.recur alphabet name body) =
      buildRecursionAutomaton alphabet name
        (compileTypeFuel (typeCompilationFuel body) body) := by
  have hFuelEq : typeCompilationFuel (.recur alphabet name body) =
      typeCompilationFuel body + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]

private lemma edgeLocal_recur (alphabet : PactTypeAlphabet)
    (name : String) (body : PactType)
    (hBodyAlphabet : body.alphabet = alphabet)
    (hBody : EdgeEnvironmentsLocal body ∧ EdgeOffersLocal body) :
    EdgeEnvironmentsLocal (.recur alphabet name body) ∧
      EdgeOffersLocal (.recur alphabet name body) := by
  classical
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_recur_eq alphabet name body] at hEdge <;>
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge <;>
    rcases hEdge with ⟨environment, ⟨hLocal, -⟩, rfl⟩ |
      ⟨childEdge, hChildMem, rfl⟩
  · exact hLocal
  · have := hBody.1 childEdge hChildMem
    rw [hBodyAlphabet] at this
    split <;> exact this
  · exact ⟨by simp, by intro _ h; simp at h⟩
  · obtain ⟨hCur, hFut⟩ := hBody.2 childEdge hChildMem
    rw [hBodyAlphabet] at hCur hFut
    split
    · exact ⟨by simp, by intro _ h; simp at h⟩
    · refine ⟨hCur, ?_⟩
      intro offers hOffers
      simp only [childFutureSpec] at hOffers
      cases hSpec : childEdge.future with
      | explicit childOffers =>
          rw [hSpec] at hOffers
          simp only [FutureSpec.explicit.injEq] at hOffers
          subst hOffers
          exact hFut childOffers hSpec
      | «at» t r => rw [hSpec] at hOffers; simp at hOffers

/-- Hiding annihilates an interface-restricted contribution: `restrictTypeOffers`
keeps exactly the ids `hideOffers` drops. -/
theorem hideOffers_union_restrictTypeOffers (interface : Interface)
    (offers extra : Finset BareMessage) :
    hideOffers interface (offers ∪ restrictTypeOffers interface extra) =
      hideOffers interface offers := by
  classical
  ext action
  simp only [hideOffers, restrictTypeOffers, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hMem | hRestricted, hNotInterface⟩
    · exact ⟨hMem, hNotInterface⟩
    · exact absurd hRestricted.2 hNotInterface
  · rintro ⟨hMem, hNotInterface⟩
    exact ⟨Or.inl hMem, hNotInterface⟩

/-- A hidden child need is a parent need.  `typeNeed` preserves the message id
and both hiding operators filter on that id, so hiding commutes with
`image typeNeed`. -/
theorem hideOffers_subset_localEnvironmentActions (interface : Interface)
    {child parent : PactTypeAlphabet}
    (hHide : PactTypeAlphabet.hideInterface child interface = parent)
    {offers : Finset BareMessage}
    (hOffers : offers ⊆ child.localEnvironmentActions) :
    hideOffers interface offers ⊆ parent.localEnvironmentActions := by
  classical
  intro action hAction
  simp only [hideOffers, Finset.mem_filter] at hAction
  obtain ⟨hMem, hNotInterface⟩ := hAction
  have hChild := hOffers hMem
  simp only [PactTypeAlphabet.localEnvironmentActions, Finset.mem_image] at hChild
  obtain ⟨base, hBase, rfl⟩ := hChild
  simp only [PactTypeAlphabet.localEnvironmentActions, Finset.mem_image]
  refine ⟨base, ?_, rfl⟩
  rw [← hHide]
  simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
  exact ⟨hBase, by simpa [typeNeed] using hNotInterface⟩

/-- The combined environment of two ordinary component edges is the shared outer
environment with the interface hidden.  Both components carry that outer
environment plus interface traffic only, and hiding annihilates the traffic. -/
theorem combineAutomatonEnvironment_ordinary_eq
    {interface : Interface} {outer : TypeEnvironment}
    {leftEdge rightEdge : AutomatonFragmentEdge}
    (hLeftNonClock : leftEdge.environment.clock = false)
    (hRightNonClock : rightEdge.environment.clock = false)
    (hLeftImm : leftEdge.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightEdge.current)
    (hRightImm : rightEdge.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftEdge.current) :
    (combineAutomatonEnvironment interface leftEdge.environment
      rightEdge.environment).immediate = hideOffers interface outer.immediate := by
  classical
  rw [combineAutomatonEnvironment, hLeftNonClock, hRightNonClock]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [hLeftImm, hRightImm]
  ext action
  simp only [hideOffers, restrictTypeOffers, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨(hOuter | hRestricted) | (hOuter | hRestricted), hNotInterface⟩
    · exact ⟨hOuter, hNotInterface⟩
    · exact absurd hRestricted.2 hNotInterface
    · exact ⟨hOuter, hNotInterface⟩
    · exact absurd hRestricted.2 hNotInterface
  · rintro ⟨hOuter, hNotInterface⟩
    exact ⟨Or.inl (Or.inl hOuter), hNotInterface⟩

/-- The future half of the same collapse.  Each component's future is the shared
outer future plus interface traffic, minus that component's own immediate set;
hiding removes the traffic and the collapse of the immediate sets makes the two
subtractions agree. -/
theorem combineAutomatonEnvironment_ordinary_future_eq
    {interface : Interface} {outer : TypeEnvironment}
    {leftEdge rightEdge : AutomatonFragmentEdge}
    (hLeftNonClock : leftEdge.environment.clock = false)
    (hRightNonClock : rightEdge.environment.clock = false)
    (hLeftImm : leftEdge.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface rightEdge.current)
    (hRightImm : rightEdge.environment.immediate =
      outer.immediate ∪ restrictTypeOffers interface leftEdge.current)
    (hLeftFut : leftEdge.environment.future =
      (outer.future ∪ restrictTypeOffers interface rightEdge.future) \
        leftEdge.environment.immediate)
    (hRightFut : rightEdge.environment.future =
      (outer.future ∪ restrictTypeOffers interface leftEdge.future) \
        rightEdge.environment.immediate) :
    (combineAutomatonEnvironment interface leftEdge.environment
      rightEdge.environment).future =
      hideOffers interface outer.future \ hideOffers interface outer.immediate := by
  classical
  rw [combineAutomatonEnvironment, hLeftNonClock, hRightNonClock]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [hLeftFut, hRightFut, hLeftImm, hRightImm]
  ext action
  simp only [hideOffers, restrictTypeOffers, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_union, not_or, not_and]
  constructor
  · rintro ⟨(⟨hFut, hNotOuterImm, -⟩ | ⟨hFut, hNotOuterImm, -⟩), hNotInterface⟩ <;>
      rcases hFut with hOuter | hRestricted
    · exact ⟨⟨hOuter, hNotInterface⟩, fun h => absurd hNotOuterImm (by simp [h])⟩
    · exact absurd hRestricted.2 hNotInterface
    · exact ⟨⟨hOuter, hNotInterface⟩, fun h => absurd hNotOuterImm (by simp [h])⟩
    · exact absurd hRestricted.2 hNotInterface
  · rintro ⟨⟨hOuter, hNotInterface⟩, hNotImm⟩
    refine ⟨Or.inl ⟨Or.inl hOuter, ?_, fun _ => hNotInterface⟩, hNotInterface⟩
    exact fun hImm => hNotImm hImm hNotInterface

/-- An environment drawn from a child's `localEnvironments` has both offer
fields inside that child's `localEnvironmentActions`. -/
theorem mem_localEnvironments_fields {environment : TypeEnvironment}
    {alphabet : PactTypeAlphabet}
    (hMem : environment ∈ alphabet.localEnvironments) :
    environment.immediate ⊆ alphabet.localEnvironmentActions ∧
      environment.future ⊆ alphabet.localEnvironmentActions := by
  classical
  simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
    Finset.mem_image] at hMem
  rcases hMem with rfl | ⟨immediate, hImmediate, future, hFuture, hEq⟩
  · exact ⟨by simp [TypeEnvironment.tock], by simp [TypeEnvironment.tock]⟩
  · rw [← hEq]
    exact ⟨hImmediate, hFuture.trans Finset.sdiff_subset⟩

/-- The environment a synchronized product edge publishes is local to the
parent.  On the clock branch it is `tock`; otherwise both collapse equations
apply and the outer environment's own locality transports through
`parent_eq_left`. -/
theorem combineAutomatonEnvironment_mem_localEnvironments
    {parent left right : PactTypeAlphabet} {interface : Interface}
    {outer : TypeEnvironment}
    (hHide : PactTypeAlphabet.hideInterface left interface = parent)
    {leftEdge rightEdge : AutomatonFragmentEdge}
    (hLeftLocal : AutomatonLocalEnvironment outer interface left rightEdge
      leftEdge)
    (hRightLocal : AutomatonLocalEnvironment outer interface right leftEdge
      rightEdge)
    (hOuterImm : outer.immediate ⊆ left.localEnvironmentActions)
    (hOuterFut : outer.future ⊆ left.localEnvironmentActions) :
    combineAutomatonEnvironment interface leftEdge.environment
      rightEdge.environment ∈ parent.localEnvironments := by
  classical
  cases hLeftLocal with
  | clock _ _ hLeftTock =>
      cases hRightLocal with
      | clock _ _ hRightTock =>
          rw [combineAutomatonEnvironment, hLeftTock, hRightTock]
          simp [PactTypeAlphabet.localEnvironments, TypeEnvironment.tock]
      | ordinary hOuterNonClock _ _ _ _ => simp_all
  | ordinary hOuterNonClock hRightNonClock hLeftNonClock hLeftImm hLeftFut =>
      cases hRightLocal with
      | clock hOuterClock _ _ =>
          rw [hOuterClock] at hOuterNonClock; simp at hOuterNonClock
      | ordinary _ _ _ hRightImm hRightFut =>
          have hImmEq := combineAutomatonEnvironment_ordinary_eq hLeftNonClock
            hRightNonClock hLeftImm hRightImm
          have hFutEq := combineAutomatonEnvironment_ordinary_future_eq
            hLeftNonClock hRightNonClock hLeftImm hRightImm hLeftFut hRightFut
          have hClockEq : (combineAutomatonEnvironment interface
              leftEdge.environment rightEdge.environment).clock = false := by
            rw [combineAutomatonEnvironment, hLeftNonClock, hRightNonClock]
            simp
          simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
            Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
            Finset.mem_image]
          refine Or.inr ⟨hideOffers interface outer.immediate,
            hideOffers_subset_localEnvironmentActions interface hHide hOuterImm,
            hideOffers interface outer.future \
              hideOffers interface outer.immediate, ?_, ?_⟩
          · rw [Finset.subset_sdiff]
            exact ⟨(Finset.sdiff_subset).trans
              (hideOffers_subset_localEnvironmentActions interface hHide hOuterFut),
              Finset.sdiff_disjoint⟩
          · rw [← hFutEq, ← hImmEq, ← hClockEq]

/-- Edge locality across the parallel product.  The raw synchronized family
publishes a combined environment, handled by
`combineAutomatonEnvironment_mem_localEnvironments`; the two completion families
draw their environments straight from the parent; the four survivor and done
families copy a re-stamped child edge, whose alphabet is already the parent's. -/
private lemma buildParallelAutomaton_edge_families
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hHide : PactTypeAlphabet.hideInterface leftAlphabet interface =
      parentAlphabet)
    (hLeftEnv : ∀ edge ∈ left.edges,
      edge.environment ∈ leftAlphabet.localEnvironments)
    (hRightEnv : ∀ edge ∈ right.edges,
      edge.environment ∈ rightAlphabet.localEnvironments)
    (hRestampedLeftEnv : ∀ edge ∈ restampedLeft.edges,
      edge.environment ∈ parentAlphabet.localEnvironments)
    (hRestampedRightEnv : ∀ edge ∈ restampedRight.edges,
      edge.environment ∈ parentAlphabet.localEnvironments)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges) :
    edge.environment ∈ parentAlphabet.localEnvironments := by
  classical
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · -- synchronized: the combined environment collapses to the outer one
    simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨hRightMem, hSync, -⟩, rfl⟩ := hRaw
    obtain ⟨hLeftLocal, hRightLocal, -⟩ := hSync
    -- The outer environment sits inside the left component's own environment,
    -- which the left fragment already draws from its alphabet.
    have hLeftEnvMem : leftEdge.environment ∈ leftAlphabet.localEnvironments := by
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftMem
      obtain ⟨pending, hPending, rfl⟩ := hLeftMem
      exact hLeftEnv pending hPending
    obtain ⟨hLeftImmField, hLeftFutField⟩ :=
      mem_localEnvironments_fields hLeftEnvMem
    refine combineAutomatonEnvironment_mem_localEnvironments hHide
      hLeftLocal hRightLocal ?_ ?_
    · cases hLeftLocal with
      | clock _ hRightTock hLeftTock =>
          rw [combineAutomatonEnvironment, hLeftTock, hRightTock]
          simp [TypeEnvironment.tock]
      | ordinary _ _ _ hLeftImm _ =>
          intro action hAction
          exact hLeftImmField (by rw [hLeftImm]; exact Finset.mem_union_left _ hAction)
    · cases hLeftLocal with
      | clock _ hRightTock hLeftTock =>
          rw [combineAutomatonEnvironment, hLeftTock, hRightTock]
          simp [TypeEnvironment.tock]
      | ordinary _ _ _ hLeftImm hLeftFut =>
          -- `hLeftFut` subtracts the left immediate set, so a member of the
          -- outer future that survives is already outside it.
          intro action hAction
          by_cases hImm : action ∈ leftEdge.environment.immediate
          · rw [hLeftImm] at hImm
            rcases Finset.mem_union.mp hImm with hOuterImm | hRestricted
            · exact hLeftImmField (by rw [hLeftImm]; exact Finset.mem_union_left _ hOuterImm)
            · exact hLeftImmField (by rw [hLeftImm]; exact Finset.mem_union_right _ hRestricted)
          · refine hLeftFutField ?_
            rw [hLeftFut]
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hAction, hImm⟩
  · -- left complete: the environment is drawn from the parent by the filter
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hLeftComplete
    obtain ⟨-, -, -, -, environment, ⟨hLocal, -⟩, rfl⟩ := hLeftComplete
    exact hLocal
  · -- right complete: the mirror
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hRightComplete
    obtain ⟨-, -, -, -, environment, ⟨hLocal, -⟩, rfl⟩ := hRightComplete
    exact hLocal
  · -- left-complete survivor: copies a re-stamped right edge
    simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftSurvivor
    exact hRestampedRightEnv pending hPending
  · -- right-complete survivor: copies a re-stamped left edge
    simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightSurvivor
    exact hRestampedLeftEnv pending hPending
  · -- left-complete done: same re-stamped right edge, target `.final`
    simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftDone
    exact hRestampedRightEnv pending hPending
  · -- right-complete done: the mirror
    simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightDone
    exact hRestampedLeftEnv pending hPending
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hDone
    exact hLocal

/-- A hidden union of two child currents is declared by the parent.  Both
`hideInterface` equations feed the same filter, so each side lands in the
parent's own actions. -/
theorem hideOffers_union_subset_actions {parent left right : PactTypeAlphabet}
    {interface : Interface}
    (hLeftHide : PactTypeAlphabet.hideInterface left interface = parent)
    (hRightHide : PactTypeAlphabet.hideInterface right interface = parent)
    {leftOffers rightOffers : Finset BareMessage}
    (hLeftOffers : leftOffers ⊆ left.actions)
    (hRightOffers : rightOffers ⊆ right.actions) :
    hideOffers interface (leftOffers ∪ rightOffers) ⊆ parent.actions := by
  classical
  intro action hAction
  simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hAction
  obtain ⟨hMem, hNotInterface⟩ := hAction
  rcases hMem with hLeft | hRight
  · rw [← hLeftHide]
    simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
    exact ⟨hLeftOffers hLeft, hNotInterface⟩
  · rw [← hRightHide]
    simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
    exact ⟨hRightOffers hRight, hNotInterface⟩

/-- Offers that meet no interface id are already the hidden ones, so a child
current the product copies unchanged is declared by the parent. -/
theorem offers_subset_hidden_of_restrict_empty {parent child : PactTypeAlphabet}
    {interface : Interface}
    (hHide : PactTypeAlphabet.hideInterface child interface = parent)
    {offers : Finset BareMessage} (hOffers : offers ⊆ child.actions)
    (hRestrict : restrictTypeOffers interface offers = ∅) :
    offers ⊆ parent.actions := by
  classical
  intro action hAction
  rw [← hHide]
  simp only [PactTypeAlphabet.hideInterface, Finset.mem_filter]
  refine ⟨hOffers hAction, ?_⟩
  intro hInterface
  have : action ∈ restrictTypeOffers interface offers := by
    simp only [restrictTypeOffers, Finset.mem_filter]
    exact ⟨hAction, hInterface⟩
  rw [hRestrict] at this
  exact absurd this (Finset.notMem_empty _)

/-- The offer half of parallel edge locality.  The raw family hides the union of
the two component currents; the completion and survivor families copy a child's
current unchanged.  Every family's future field is `.explicit` only at `∅`, by
`parallelFutureSpec`. -/
private lemma buildParallelAutomaton_edge_offers
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hLeftHide : PactTypeAlphabet.hideInterface leftAlphabet interface =
      parentAlphabet)
    (hRightHide : PactTypeAlphabet.hideInterface rightAlphabet interface =
      parentAlphabet)
    (hLeftCurrent : ∀ edge ∈ left.edges, edge.current ⊆ leftAlphabet.actions)
    (hRightCurrent : ∀ edge ∈ right.edges, edge.current ⊆ rightAlphabet.actions)
    (hRestampedLeftCurrent : ∀ edge ∈ restampedLeft.edges,
      edge.current ⊆ parentAlphabet.actions)
    (hRestampedRightCurrent : ∀ edge ∈ restampedRight.edges,
      edge.current ⊆ parentAlphabet.actions)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges) :
    edge.current ⊆ parentAlphabet.actions ∧
      ∀ offers, edge.future = .explicit offers →
        offers ⊆ parentAlphabet.actions := by
  classical
  have hSpec : ∀ (label : AutomatonConstructionLabel) (target : TypeAutomatonState)
      (removed : Finset BareMessage) (offers : Finset BareMessage),
      parallelFutureSpec label target removed = .explicit offers →
      offers ⊆ parentAlphabet.actions := by
    intro label target removed offers hEq
    simp only [parallelFutureSpec] at hEq
    split at hEq
    · cases hEq; simp
    · exact absurd hEq (by simp)
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image, resolveAutomatonEdgesWith] at hRaw
    obtain ⟨leftEdge, ⟨leftPending, hLeftPending, rfl⟩, rightEdge,
      ⟨⟨rightPending, hRightPending, rfl⟩, -⟩, rfl⟩ := hRaw
    exact ⟨hideOffers_union_subset_actions hLeftHide hRightHide
      (hLeftCurrent leftPending hLeftPending)
      (hRightCurrent rightPending hRightPending), hSpec _ _ _⟩
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftComplete
    obtain ⟨-, -, resolved, ⟨⟨pending, hPending, rfl⟩, -, -, hRestrict, -⟩,
      environment, -, rfl⟩ := hLeftComplete
    exact ⟨offers_subset_hidden_of_restrict_empty hRightHide
      (hRightCurrent pending hPending) hRestrict, hSpec _ _ _⟩
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightComplete
    obtain ⟨-, -, resolved, ⟨⟨pending, hPending, rfl⟩, -, -, hRestrict, -⟩,
      environment, -, rfl⟩ := hRightComplete
    exact ⟨offers_subset_hidden_of_restrict_empty hLeftHide
      (hLeftCurrent pending hPending) hRestrict, hSpec _ _ _⟩
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftSurvivor
    exact ⟨hRestampedRightCurrent pending hPending, hSpec _ _ _⟩
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightSurvivor
    exact ⟨hRestampedLeftCurrent pending hPending, hSpec _ _ _⟩
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftDone
    exact ⟨hRestampedRightCurrent pending hPending, hSpec _ _ _⟩
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightDone
    exact ⟨hRestampedLeftCurrent pending hPending, hSpec _ _ _⟩
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    exact ⟨by simp, by intro _ h; simp only [] at h; cases h; simp⟩

/-- Compiling a conjunctive offer at its own budget builds the selected
conjunctive automaton over the else arm and every selected product, each
compiled at its own budget. -/
theorem compileTypeFuel_offer_eq (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    compileTypeFuel (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
      buildSelectedConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun selected =>
          (selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches))) := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  congr 1
  · exact compileTypeFuel_eq_of_sufficient elseType (Nat.le_max_left _ _)
      (Nat.le_refl _)
  · refine List.map_congr_left ?_
    intro selected hSelected
    have hFuel : typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) ≤
        max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches) := by
      rw [typeCompilationFuel_parallelTypeBranchesSelecting]
      omega
    rw [compileTypeFuel_eq_of_sufficient _ hFuel (Nat.le_refl _)]

/-- The guard at a composite constructor.  Both halves are
constructor-independent.  A semantic step is offered only to an environment
well formed for its own source, and both its offer components are declared by
that source.  A compiled edge carries an environment the builder drew from the
node's `localEnvironments`, a current offer the builder drew from its actions,
and a future the alphabet gate on `computeFutureOf` bounds directly. -/
theorem baseGuard_of_families {processType : PactType}
    (hWF : processType.AlphabetWellFormed)
    (hScoped : processType.InterfaceScoped)
    (hAlphaScoped : processType.InterfaceAlphabetScoped)
    (hTailRec : processType.TailRecursive)
    (hTailClosed : processType.TailClosed)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (hFamilies : EdgeEnvironmentsLocal processType)
    (hOffers : EdgeOffersLocal processType) :
    BaseGuard processType := by
  intro residual state env label offers hRelated hCase
  rcases offers with ⟨current, future⟩
  rcases hCase with ⟨target, hTrans, hOffersStep⟩ | ⟨state', hEdge⟩
  · have hResWF : residual.AlphabetWellFormed :=
      relationMembership_alphabetWellFormed
        committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
        processType residual state hWF hScoped hAlphaScoped hTailRec
        hDisjoint hRelated
    have hResAlpha : residual.alphabet = processType.alphabet :=
      relationMembership_alphabet_eq processType residual state
        (PactType.alphabetCoherent_of_wellFormed processType hWF) hRelated
    have hEnvWF : env.WellFormed residual.alphabet :=
      PactType.typeOffers_env_wellFormed hOffersStep hResWF
    rw [hResAlpha] at hEnvWF
    refine ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hEnvWF, ?_⟩
    refine mem_localOfferSummaries_of_subset ?_ ?_
    · have := typeOffers_current_subset_alphabet hResWF hOffersStep
      rw [hResAlpha] at this
      exact this
    · have hTargetAlpha : target.alphabet = residual.alphabet :=
        TypeOffers.preserves_alphabet hResWF hOffersStep
      have hTargetWF : target.AlphabetWellFormed :=
        DecoratedTypeTransition.preserves_alphabetWellFormed hResWF
          (relationMembership_tailRecursive processType residual state hTailRec
            hTailClosed hRelated).1
          (relationMembership_offerBranchesDisjoint processType residual state
            hTailRec hDisjoint hRelated) ⟨hTrans, hOffersStep⟩
      have := typeOffers_future_subset_fixedAlphabet hResWF hTargetAlpha
        hTargetWF hOffersStep
      rw [hResAlpha] at this
      exact this
  · obtain ⟨edge, hPending, -, hEnv, -, hCurrent, hFutureEq, -⟩ :=
      (compileType_hasEdge_iff_hasResolvedEdge processType state state' env
        label ⟨current, future⟩).mp hEdge
    refine ⟨by rw [← hEnv]; exact hFamilies edge hPending, ?_⟩
    refine mem_localOfferSummaries_of_subset ?_ ?_
    · have hC := (hOffers edge hPending).1
      simpa [hCurrent] using hC
    · -- The gate bounds whatever the edge's future resolves to.
      rw [show future = _ from hFutureEq.symm]
      cases hSpec : edge.future with
      | explicit offersExplicit =>
          simpa [hSpec] using (hOffers edge hPending).2 offersExplicit hSpec
      | «at» t r =>
          simp only
          exact fun action hAction =>
            computeFutureOf_subset_alphabet processType t
              (Finset.mem_sdiff.mp hAction).1

/-- A copied left-child edge of a binary choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem choice_child0_edge_restrict (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.choice alphabet left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.choice alphabet left right)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType left).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_choice_child_left alphabet left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_left alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      TypeLabel.silent TypeLabel.silent q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge left q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_left alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem]

/-- The forward direction of `choice_child0_edge_restrict`: a left-child edge
lifts to the copied edge of the binary choice. -/
theorem choice_child0_edge_lift (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.choice alphabet left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType left).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.choice alphabet left right)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_choice_child_left alphabet left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_left alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- The forward direction of `choice_child1_edge_restrict`: a left-child edge
lifts to the copied edge of the binary choice. -/
theorem choice_child1_edge_lift (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.choice alphabet left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType right).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.choice alphabet left right)).HasEdge
      (.child 1 q) env label ⟨current, future⟩ (.child 1 q') := by
  classical
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_choice_child_right alphabet left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
    (.child 1 q) (.child 1 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 1 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inr ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_right alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- A copied right-child edge of a binary choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem choice_child1_edge_restrict (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.choice alphabet left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.choice alphabet left right)).HasEdge
      (.child 1 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 1 q' ∧
      (compileType right).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel (.choice alphabet left right) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.choice alphabet left right) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_choice_child_right alphabet left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
      (.child 1 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_right alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      TypeLabel.silent TypeLabel.silent q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge right q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_right alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem]

/-- Every edge of a compiled type lands on a state that still represents some
residual.  This is the third premise of the current-offer assembly. -/
def TargetsRelated (processType : PactType) : Prop :=
  ∀ {residual : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership
      (buildRelationSet processType (compileType processType)) residual state →
    (compileType processType).HasEdge state env label offers state' →
    ∃ residual',
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual' state'

/-- Every edge lands on a state that still represents some residual.  A public
edge always resolves a `.visible` pending edge, so the variable-marker escape of
the relation's closure lemma cannot occur. -/
theorem targetsRelated (processType : PactType) : TargetsRelated processType := by
  classical
  intro residual state state' env label offers _ hEdge
  obtain ⟨pendingEdge, hPendingMem, -, -, hPLabel, -, -, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge processType state state' env label
      offers).mp hEdge
  rcases buildRelationSetCoreFuel_edge_target_mem
    (typeCompilationFuel processType) processType le_rfl pendingEdge hPendingMem with
    ⟨residual', hMem⟩ | ⟨name, hName⟩
  · exact ⟨residual', by rw [← hPTarget]; exact hMem⟩
  · rw [hPLabel] at hName; cases hName

/-- The uniform offer law makes a step's future field a function of its target
and current offer, so two decorated steps agreeing on those agree outright. -/
theorem decoratedTypeTransition_future_eq
    {env : TypeEnvironment} {source target : PactType} {label : TypeLabel}
    {current futureA futureB : Finset BareMessage}
    (hA : DecoratedTypeTransition env source label
      (TypeOfferSummary.mk current futureA) target)
    (hB : DecoratedTypeTransition env source label
      (TypeOfferSummary.mk current futureB) target) :
    futureA = futureB := by
  by_cases hTock : label = TypeLabel.tock
  · subst hTock
    have hFA := (uniform_offer_law_clock hA.2 rfl).2
    have hFB := (uniform_offer_law_clock hB.2 rfl).2
    simp only at hFA hFB
    rw [hFA, hFB]
  · have hFA := hA.2.future_eq_sdiff_of_label_ne_tock hTock
    have hFB := hB.2.future_eq_sdiff_of_label_ne_tock hTock
    simp only at hFA hFB
    rw [hFA, hFB]

/-- Current-offer correspondence at a binary choice.  Following the paper: the
root's guards, labels, current offers and targets are identical in the semantic
rule and the selection edge family, and copied states use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hWF : (PactType.choice alphabet left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.choice alphabet left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.choice alphabet left right).alphabet)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence (.choice alphabet left right) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: invert the choice rule and take its own selection edge.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_choice_eq alphabet left right
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | choice_left cEnv cAlpha cLeft cRight hChoiceEnv =>
          refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel left)
            left).initial, computeFutureOf (.choice alphabet left right)
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial), ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.choice alphabet left right) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial) ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inl rfl⟩
            · simp [childState]
          · exact relationMembership_choice_left alphabet left right left
              (buildRelationSet_initial left (compileType left))
      | choice_right cEnv cAlpha cLeft cRight hChoiceEnv =>
          refine ⟨.child 1 (compileTypeFuel (typeCompilationFuel right)
            right).initial, computeFutureOf (.choice alphabet left right)
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial), ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.choice alphabet left right) TypeAutomatonState.root
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial) ∅,
                target := childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inr rfl⟩
            · simp [childState]
          · exact relationMembership_choice_right alphabet left right right
              (buildRelationSet_initial right (compileType right))
    · -- Copied left state: the lower-rank hypothesis, lifted.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hLeft.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        choice_child0_edge_lift alphabet left right hLeftDisjoint hLeftAlphabet
          hChildEdge,
        relationMembership_choice_left alphabet left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      exact ⟨.child 1 q', future',
        choice_child1_edge_lift alphabet left right hRightDisjoint hRightAlphabet
          hChildEdge,
        relationMembership_choice_right alphabet left right residual' hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_choice_cases alphabet left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: the only root edges are the two selection edges.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_choice_eq alphabet left right
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge (.choice alphabet left right)
          TypeAutomatonState.root state' env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      obtain ⟨environment, hEnvFilter, hEq | hEq⟩ :=
        (buildChoiceAutomaton_outgoing_root alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          TypeLabel.silent TypeLabel.silent pendingEdge).mp
          ⟨hPendingMem, hPSource⟩ <;>
        rw [Finset.mem_filter] at hEnvFilter <;>
        subst hEq <;>
        simp only [childState] at hPEnv hPLabel hPCurrent hPTarget
      · have hLabelEq : label = TypeLabel.silent := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨left, typeFutureOffers left, ?_, ?_⟩
        · exact ⟨TypeTransition.choice_left _ alphabet left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.choice_left _ alphabet left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_choice_left alphabet left right left
            (buildRelationSet_initial left (compileType left))
      · have hLabelEq : label = TypeLabel.silent := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨right, typeFutureOffers right, ?_, ?_⟩
        · exact ⟨TypeTransition.choice_right _ alphabet left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.choice_right _ alphabet left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_choice_right alphabet left right right
            (buildRelationSet_initial right (compileType right))
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        choice_child0_edge_restrict alphabet left right hLeftDisjoint
          hLeftAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hLeft.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_choice_left alphabet left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        choice_child1_edge_restrict alphabet left right hRightDisjoint
          hRightAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hRight.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_choice_right alphabet left right residual' hChildTarget⟩

/-- Current-offer correspondence at a sequence.  Following the paper: apply the
lower-rank hypothesis to the left step, let completion decide whether its target
is retained or redirected to the right entry, and copy right states unchanged. -/
theorem currentOfferCorrespondence_seq (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeftResidualWF : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet left (compileType left))
        residual state → residual.AlphabetWellFormed)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence (.seq alphabet left right) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_seq_cases alphabet left right hRelated with
      ⟨q, leftResidual, hEntry, hChildRelated, -⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Left phase: the residual is `leftResidual; right`.
      rw [Prod.ext_iff] at hEntry
      obtain ⟨hResEq, hStateEq⟩ := hEntry
      simp only at hResEq hStateEq
      subst hResEq; subst hStateEq
      rcases decoratedTypeTransition_seq_cases hTransition with
        ⟨leftTarget, childFuture, hTargetEq, hNonFinal, hChildStep, hNotTock,
          hFutureEq⟩ |
        ⟨leftTarget, childCurrent, childFuture, hTargetEq, hNonFinal, hTock,
          hChildStep, hFutureEq⟩ |
        ⟨tSkip, oSkip, childFuture, hTargetEq, hChildTrans, hChildOffers,
          hNotTock, hFutureEq⟩ |
        ⟨tSkip, oSkip, childCurrent, childFuture, hTargetEq, hTock,
          hChildTrans, hChildOffers, hFutureEq⟩
      · -- Retained: apply the lower-rank hypothesis to the left step.
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated hChildStep
        subst hTargetEq
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_step alphabet left right hRelated
            hChildRelated hChildTarget hNonFinal
            hChildStep hNotTock hChildEdge
        exact ⟨.child 0 q', _, hParentEdge, hParentTarget⟩
      · -- Retained under a clock: a clock step offers nothing now.
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated hChildStep
        subst hTargetEq; subst hTock
        have hCurrentEmpty : current = ∅ := by
          simpa using
            TypeOffers.current_eq_empty_of_label_tock hTransition.2 rfl
        subst hCurrentEmpty
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_step_tock alphabet left right hRelated
            hChildRelated hChildTarget hNonFinal hChildStep hChildEdge
        exact ⟨.child 0 q', _, hParentEdge, hParentTarget⟩
      · -- Redirected: the left operand completes, so the edge enters the right
        -- entry.
        -- Both judgments preserve the alphabet, so the two skip annotations
        -- the inversion produced are the same one.
        have hResWF := hLeftResidualWF hChildRelated
        have hSkipEq : oSkip = tSkip := by
          have hT := TypeTransition.preserves_alphabet hResWF hChildTrans
          have hO := TypeOffers.preserves_alphabet hResWF hChildOffers
          exact hO.trans hT.symm
        rw [hSkipEq] at hChildOffers
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated ⟨hChildTrans, hChildOffers⟩
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_fuse alphabet tSkip left right
            hRightDisjoint hRightAlphabet hRelated hChildRelated hChildTarget
            ⟨hChildTrans, hChildOffers⟩ hNotTock hChildEdge
        exact ⟨_, _, hParentEdge, hTargetEq ▸ hParentTarget⟩
      · -- Redirected under a clock: the parent offers nothing now either.
        subst hTock
        have hCurrentEmpty : current = ∅ := by
          simpa using
            TypeOffers.current_eq_empty_of_label_tock hTransition.2 rfl
        have hChildCurrentEmpty : childCurrent = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildOffers rfl
        subst hCurrentEmpty; subst hChildCurrentEmpty
        have hResWF := hLeftResidualWF hChildRelated
        have hSkipEq : oSkip = tSkip := by
          have hT := TypeTransition.preserves_alphabet hResWF hChildTrans
          have hO := TypeOffers.preserves_alphabet hResWF hChildOffers
          exact hO.trans hT.symm
        rw [hSkipEq] at hChildOffers
        obtain ⟨q', childFuture', hChildEdge, hChildTarget⟩ :=
          hLeft.1 hChildRelated ⟨hChildTrans, hChildOffers⟩
        obtain ⟨hParentEdge, hParentTarget⟩ :=
          compileType_seq_lift_left_fuse_tock alphabet tSkip left right
            hRelated hChildRelated hChildTarget
            ⟨hChildTrans, hChildOffers⟩ hChildEdge
        subst hTargetEq
        exact ⟨_, _, hParentEdge, hParentTarget⟩
    · -- Right phase: copied unchanged.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      -- The right component copies its edges unchanged.
      obtain ⟨state', hParentEdge, hParentTarget⟩ :=
        compileType_seq_lift_right_step alphabet left right hRightDisjoint
          hRightAlphabet hRelated hChildRelated hChildTarget
          (offers := TypeOfferSummary.mk current future')
          (rightTarget := residual') hChildEdge
      exact ⟨state', future', hParentEdge, hParentTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    -- The same case split, read off the edge instead of the step.
    obtain ⟨residual', hTargetRelated⟩ := targetsRelated _ hRelated hEdge
    cases compileType_seq_edge_cases alphabet left right hRightDisjoint
        hRightAlphabet hRelated hEdge hTargetRelated with
    | leftStep leftResidual leftTarget q q' childFuture hRes hRes' hState
        hState' hNonFinal hLeftRelated hLeftTargetRelated hChildEdge hNotTock
        hFuture =>
        subst hRes; subst hRes'; subst hState; subst hState'; subst hFuture
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        -- `final-states-completion`: the edge's target is not accepting, so the
        -- residual it represents is not `skip`.
        have hNotAccepting : q' ∉ (compileType left).accepting := by
          intro hAccept
          obtain ⟨skipAlpha, hSkip⟩ :=
            (final_states_completion left hLeftTargetRelated).mp hAccept
          exact hNonFinal (by rw [hSkip]; rfl)
        have hNonFinal'' : leftTarget'' ≠ .skip leftTarget''.alphabet := by
          intro hSkip
          exact hNotAccepting
            ((final_states_completion left hChildTarget'').mpr
              ⟨leftTarget''.alphabet, hSkip⟩)
        exact ⟨_, _,
          ⟨TypeTransition.seq env alphabet leftResidual leftTarget'' right label
              hChildStep.1 hNonFinal'',
            TypeOffers.seq env alphabet leftResidual leftTarget'' right label
              current childFuture'' hChildStep.2 hNonFinal'' hNotTock⟩,
          relationMembership_seq_left alphabet left right leftTarget''
            hChildTarget'' hNotAccepting⟩
    | leftStepTock leftResidual leftTarget q q' childFuture hRes hRes' hState
        hState' hNonFinal hLeftRelated hLeftTargetRelated hChildEdge hTock
        hFuture =>
        subst hRes; subst hRes'; subst hState; subst hState'; subst hFuture
        subst hTock
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        have hNotAccepting : q' ∉ (compileType left).accepting := by
          intro hAccept
          obtain ⟨skipAlpha, hSkip⟩ :=
            (final_states_completion left hLeftTargetRelated).mp hAccept
          exact hNonFinal (by rw [hSkip]; rfl)
        have hNonFinal'' : leftTarget'' ≠ .skip leftTarget''.alphabet := by
          intro hSkip
          exact hNotAccepting
            ((final_states_completion left hChildTarget'').mpr
              ⟨leftTarget''.alphabet, hSkip⟩)
        have hCurrentEmpty : current = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildStep.2 rfl
        exact ⟨_, _,
          ⟨TypeTransition.seq env alphabet leftResidual leftTarget'' right
              TypeLabel.tock hChildStep.1 hNonFinal'',
            hCurrentEmpty ▸ TypeOffers.seq_tock env alphabet leftResidual
              leftTarget'' right current childFuture'' hChildStep.2
              hNonFinal''⟩,
          relationMembership_seq_left alphabet left right leftTarget''
            hChildTarget'' hNotAccepting⟩
    | leftFuse leftResidual skipAlphabet q q' childFuture hRes hRes' hState
        hLeftRelated hLeftTargetRelated hChildEdge hNotTock hFuture =>
        subst hRes; subst hState; subst hFuture
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        -- The edge's target is accepting, so its residual completes the left
        -- operand and the step fuses into the right entry.
        have hAccept : q' ∈ (compileType left).accepting :=
          (final_states_completion left hLeftTargetRelated).mpr
            ⟨skipAlphabet, rfl⟩
        obtain ⟨skipAlpha'', hSkip''⟩ :=
          (final_states_completion left hChildTarget'').mp hAccept
        subst hSkip''
        exact ⟨_, _,
          ⟨TypeTransition.seq_fuse env alphabet skipAlpha'' leftResidual right
              label hChildStep.1,
            TypeOffers.seq_fuse env alphabet skipAlpha'' leftResidual right
              label current childFuture'' hChildStep.2 hNotTock⟩,
          hRes' ▸ hTargetRelated⟩
    | leftFuseTock leftResidual skipAlphabet q q' childFuture hRes hRes' hState
        hLeftRelated hLeftTargetRelated hChildEdge hTock hFuture =>
        subst hRes; subst hState; subst hFuture; subst hTock
        obtain ⟨leftTarget'', childFuture'', hChildStep, hChildTarget''⟩ :=
          hLeft.2 hLeftRelated hChildEdge
        have hAccept : q' ∈ (compileType left).accepting :=
          (final_states_completion left hLeftTargetRelated).mpr
            ⟨skipAlphabet, rfl⟩
        obtain ⟨skipAlpha'', hSkip''⟩ :=
          (final_states_completion left hChildTarget'').mp hAccept
        subst hSkip''
        have hCurrentEmpty : current = ∅ :=
          TypeOffers.current_eq_empty_of_label_tock hChildStep.2 rfl
        exact ⟨_, _,
          ⟨TypeTransition.seq_fuse env alphabet skipAlpha'' leftResidual right
              TypeLabel.tock hChildStep.1,
            hCurrentEmpty ▸ TypeOffers.seq_fuse_tock env alphabet skipAlpha''
              leftResidual right current childFuture'' hChildStep.2⟩,
          hRes' ▸ hTargetRelated⟩
    | rightStep q q' hState hState' hRightRelated hRightTargetRelated
        hChildEdge =>
        subst hState; subst hState'
        obtain ⟨residual'', future'', hChildStep, hChildTarget''⟩ :=
          hRight.2 hRightRelated hChildEdge
        exact ⟨residual'', future'', hChildStep,
          relationMembership_seq_right alphabet left right residual''
            hChildTarget''⟩

/-- Menus agree at a binary choice: the root reaches exactly its two copied
child entries, and their menus agree by the child hypotheses. -/
theorem futureOffersAgree_choice (alphabet : PactTypeAlphabet)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right) :
    FutureOffersAgree (.choice alphabet left right) := by
  classical
  set whole : PactType := .choice alphabet left right with hWholeDef
  have hWhole := compileTypeFuel_choice_eq alphabet left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hProductLeft : ∀ visited,
      stateProductInfo whole (.child 0 visited) = stateProductInfo left visited :=
    stateProductInfo_choice_child_left alphabet left right
  have hProductRight : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_choice_child_right alphabet left right
  -- A copied child state has its child's own menu.
  have hTransportLeft : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left)
      left).states, computeFutureOf whole (.child 0 q) = computeFutureOf left q :=
    fun q hq => computeFutureOf_binaryChoice_left alphabet left right
      TypeLabel.silent TypeLabel.silent whole hWhole hFuelLeft hLeftDisjoint
      (by rw [hLeftAlphabet, hWholeDef]; rfl) hProductLeft q hq
  have hTransportRight : ∀ q ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states,
      computeFutureOf whole (.child 1 q) = computeFutureOf right q :=
    fun q hq => computeFutureOf_binaryChoice_right alphabet left right
      TypeLabel.silent TypeLabel.silent whole hWhole hFuelRight hRightDisjoint
      (by rw [hRightAlphabet, hWholeDef]; rfl) hProductRight q hq
  intro residual state hRelated
  rcases relationMembership_choice_cases alphabet left right hRelated with
    hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
  · -- Root: split the menu across the two selection edges.
    injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    have hWholeDisjoint : whole.OfferBranchesDisjoint := by
      simp only [hWholeDef, PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩
    have hEnv : ∃ environment ∈ alphabet.localEnvironments,
        environment.clock = false :=
      ⟨TypeEnvironment.empty, empty_mem_localEnvironments alphabet, rfl⟩
    have hOffers :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).offersAt
          TypeAutomatonState.root = ∅ := by
      rw [hWhole]
      exact buildChoiceAutomaton_offersAt_root alphabet _ _ _ _
    have hRefs :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).referencedStates
          TypeAutomatonState.root =
        {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
          childState 1
            (compileTypeFuel (typeCompilationFuel right) right).initial} := by
      rw [hWhole]
      exact buildChoiceAutomaton_referencedStates_root alphabet _ _ _ _
        (by simp [TypeLabel.silent]) (by simp [TypeLabel.silent]) hEnv
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
        childState 1
          (compileTypeFuel (typeCompilationFuel right) right).initial}
      _ rfl
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildChoiceAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hRefs]
        simp [Finset.insert_subset_iff])
      (by rw [hRefs])
      (by
        simp only [hWholeDef]
        exact stateProductInfo_choice_root alphabet left right)
      (by
        intro action hIn
        rw [hOffers] at hIn
        exact absurd hIn (Finset.notMem_empty _))
    rw [hDecomp, hOffers, Finset.empty_union, Finset.biUnion_insert,
      Finset.singleton_biUnion]
    simp only [childState]
    have hLeftMenu : computeFutureOf left
        (compileTypeFuel (typeCompilationFuel left) left).initial =
          typeFutureOffers left :=
      hLeft (buildRelationSet_initial left _ rfl)
    have hRightMenu : computeFutureOf right
        (compileTypeFuel (typeCompilationFuel right) right).initial =
          typeFutureOffers right :=
      hRight (buildRelationSet_initial right _ rfl)
    rw [hTransportLeft _ (compileTypeFuel_initial_mem _ left (Nat.le_refl _)),
      hTransportRight _ (compileTypeFuel_initial_mem _ right (Nat.le_refl _)),
      hLeftMenu, hRightMenu]
    exact (typeFutureOffers_choice alphabet left right).symm
  · subst hState
    rw [hTransportLeft q (relationMembership_state_mem left _ q hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q (relationMembership_state_mem right _ q hChild)]
    exact hRight hChild

/-- Compiling a fair choice at its own budget builds the same sum automaton,
with observable selection labels. -/
theorem compileTypeFuel_fairChoice_eq (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType) :
    compileTypeFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
      buildChoiceAutomaton alphabet
        (compileTypeFuel (typeCompilationFuel left) left)
        (compileTypeFuel (typeCompilationFuel right) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  rw [compileTypeFuel_eq_of_sufficient left (Nat.le_max_left _ _)
      (Nat.le_refl _),
    compileTypeFuel_eq_of_sufficient right (Nat.le_max_right _ _)
      (Nat.le_refl _)]

private lemma edgeLocal_fairChoice (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : EdgeEnvironmentsLocal left ∧ EdgeOffersLocal left)
    (hRight : EdgeEnvironmentsLocal right ∧ EdgeOffersLocal right) :
    EdgeEnvironmentsLocal (.fairChoice alphabet bid left right) ∧
      EdgeOffersLocal (.fairChoice alphabet bid left right) := by
  refine ⟨fun edge hEdge => ?_, fun edge hEdge => ?_⟩ <;>
    rw [compileTypeFuel_fairChoice_eq alphabet bid left right] at hEdge
  · exact sumBuilder_edge_families alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.1 hRight.1 edge hEdge
  · exact sumBuilder_edge_offers alphabet left right _ _ hLeftAlphabet
      hRightAlphabet hLeft.2 hRight.2 edge hEdge

/-- A copied left-child edge of a fair choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem fairChoice_child0_edge_restrict (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType left).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_left alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge left q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_left alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          ((.fairChoice alphabet bid left right)) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem]

/-- The forward direction of `fairChoice_child0_edge_restrict`: a left-child edge
lifts to the copied edge of the fair choice. -/
theorem fairChoice_child0_edge_lift (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType left).HasEdge q env label ⟨current, future⟩ q') :
    (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 0 visited) =
        stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge left q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_left alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          ((.fairChoice alphabet bid left right)) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- The forward direction of `fairChoice_child1_edge_restrict`: a left-child edge
lifts to the copied edge of the fair choice. -/
theorem fairChoice_child1_edge_lift (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType right).HasEdge q env label ⟨current, future⟩ q') :
    (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 1 q) env label ⟨current, future⟩ (.child 1 q') := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge right q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
    (.child 1 q) (.child 1 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 1 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildChoiceAutomaton, finishAutomatonFragment, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton, childPendingEdges, Finset.mem_image]
    exact Or.inl (Or.inr ⟨childEdge, hChildEdgeMem, rfl⟩)
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_right alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          ((.fairChoice alphabet bid left right)) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- A copied right-child edge of a fair choice restricts to an edge of the
child.  This is the inversion the step correspondence performs inline; naming it
lets target relatedness reuse it. -/
theorem fairChoice_child1_edge_restrict (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType ((.fairChoice alphabet bid left right))).HasEdge
      (.child 1 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 1 q' ∧
      (compileType right).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelRight : typeCompilationFuel right + 1 ≤
      typeCompilationFuel ((.fairChoice alphabet bid left right)) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo ((.fairChoice alphabet bid left right)) (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
      (.child 1 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  obtain ⟨childEdge, hChildEdgeMem, hChildEdgeSource, hChildEdgeEq⟩ :=
    (buildChoiceAutomaton_outgoing_right alphabet
      (compileTypeFuel (typeCompilationFuel left) left)
      (compileTypeFuel (typeCompilationFuel right) right)
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) q pendingEdge).mp
      ⟨hPendingMem, hPSource⟩
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEdgeEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge right q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildEdgeSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEdgeEq]; rfl
  · rw [← hPLabel, hChildEdgeEq]; rfl
  · rw [← hPCurrent, hChildEdgeEq]; rfl
  · rw [← hPFuture, hChildEdgeEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_binaryChoice_right alphabet left right
          (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          ((.fairChoice alphabet bid left right)) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem]

/-- Current-offer correspondence at a fair choice.  Following the paper: the
root's guards, labels, current offers and targets are identical in the semantic
rule and the selection edge family, and copied states use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_fairChoice (alphabet : PactTypeAlphabet) (bid : BranchId)
    (left right : PactType)
    (hWF : (PactType.fairChoice alphabet bid left right).AlphabetWellFormed)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hRightAlphabet : right.alphabet = (PactType.fairChoice alphabet bid left right).alphabet)
    (hLeft : CurrentOfferCorrespondence left)
    (hRight : CurrentOfferCorrespondence right) :
    CurrentOfferCorrespondence ((.fairChoice alphabet bid left right)) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: invert the choice rule and take its own selection edge.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | fair_left cEnv cAlpha cBid cLeft cRight hChoiceEnv =>
          refine ⟨.child 0 (compileTypeFuel (typeCompilationFuel left)
            left).initial, computeFutureOf ((.fairChoice alphabet bid left right))
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial), ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              ((.fairChoice alphabet bid left right)) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel left)
                left).initial) env (TypeLabel.fair bid true) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible (TypeLabel.fair bid true),
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial) ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel left) left).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inl rfl⟩
            · simp [childState]
          · exact relationMembership_fairChoice_left alphabet bid left right left
              (buildRelationSet_initial left (compileType left))
      | fair_right cEnv cAlpha cBid cLeft cRight hChoiceEnv =>
          refine ⟨.child 1 (compileTypeFuel (typeCompilationFuel right)
            right).initial, computeFutureOf ((.fairChoice alphabet bid left right))
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial), ?_, ?_⟩
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              ((.fairChoice alphabet bid left right)) TypeAutomatonState.root
              (.child 1 (compileTypeFuel (typeCompilationFuel right)
                right).initial) env (TypeLabel.fair bid false) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible (TypeLabel.fair bid false),
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial) ∅,
                target := childState 1 (compileTypeFuel
                  (typeCompilationFuel right) right).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildChoiceAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
                Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr ⟨env, ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed
                hChoiceEnv.1, hChoiceEnv.2⟩, Or.inr rfl⟩
            · simp [childState]
          · exact relationMembership_fairChoice_right alphabet bid left right right
              (buildRelationSet_initial right (compileType right))
    · -- Copied left state: the lower-rank hypothesis, lifted.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hLeft.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        fairChoice_child0_edge_lift alphabet bid left right hLeftDisjoint hLeftAlphabet
          hChildEdge,
        relationMembership_fairChoice_left alphabet bid left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hRight.1 hChildRelated hTransition
      exact ⟨.child 1 q', future',
        fairChoice_child1_edge_lift alphabet bid left right hRightDisjoint hRightAlphabet
          hChildEdge,
        relationMembership_fairChoice_right alphabet bid left right residual' hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
      hRoot | ⟨q, hStateEq, hChildRelated⟩ | ⟨q, hStateEq, hChildRelated⟩
    · -- Root: the only root edges are the two selection edges.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, rfl⟩ := hRoot
      subst hResEq
      have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge ((.fairChoice alphabet bid left right))
          TypeAutomatonState.root state' env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      obtain ⟨environment, hEnvFilter, hEq | hEq⟩ :=
        (buildChoiceAutomaton_outgoing_root alphabet
          (compileTypeFuel (typeCompilationFuel left) left)
          (compileTypeFuel (typeCompilationFuel right) right)
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) pendingEdge).mp
          ⟨hPendingMem, hPSource⟩ <;>
        rw [Finset.mem_filter] at hEnvFilter <;>
        subst hEq <;>
        simp only [childState] at hPEnv hPLabel hPCurrent hPTarget
      · have hLabelEq : label = TypeLabel.fair bid true := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨left, typeFutureOffers left, ?_, ?_⟩
        · exact ⟨TypeTransition.fair_left _ alphabet bid left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.fair_left _ alphabet bid left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_fairChoice_left alphabet bid left right left
            (buildRelationSet_initial left (compileType left))
      · have hLabelEq : label = TypeLabel.fair bid false := by
          have := hPLabel; simp at this; exact this.symm
        have hCurrentEq : current = ∅ := hPCurrent.symm
        have hEnvMem : environment ∈ alphabet.localEnvironments := hEnvFilter.1
        have hEnvClock : environment.clock = false := by
          simpa using hEnvFilter.2
        subst hLabelEq hCurrentEq
        have hEnvEq : environment = env := hPEnv
        subst hEnvEq
        refine ⟨right, typeFutureOffers right, ?_, ?_⟩
        · exact ⟨TypeTransition.fair_right _ alphabet bid left right
              (PactTypeAlphabet.environment_wellFormed hEnvMem) hEnvClock,
            TypeOffers.fair_right _ alphabet bid left right
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hEnvClock⟩⟩
        · rw [← hPTarget]
          exact relationMembership_fairChoice_right alphabet bid left right right
            (buildRelationSet_initial right (compileType right))
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        fairChoice_child0_edge_restrict alphabet bid left right hLeftDisjoint
          hLeftAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hLeft.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_fairChoice_left alphabet bid left right residual' hChildTarget⟩
    · subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        fairChoice_child1_edge_restrict alphabet bid left right hRightDisjoint
          hRightAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hRight.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_fairChoice_right alphabet bid left right residual' hChildTarget⟩

/-- Menus agree at a fair choice.  The construction is the same sum as an
ordinary choice, with observable selection labels. -/
theorem futureOffersAgree_fairChoice (alphabet : PactTypeAlphabet)
    (bid : BranchId) (left right : PactType)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hLeftAlphabet : left.alphabet = alphabet)
    (hRightAlphabet : right.alphabet = alphabet)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right) :
    FutureOffersAgree (.fairChoice alphabet bid left right) := by
  classical
  set whole : PactType := .fairChoice alphabet bid left right with hWholeDef
  have hWhole := compileTypeFuel_fairChoice_eq alphabet bid left right
  have hFuelLeft : typeCompilationFuel left + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hFuelRight :
      typeCompilationFuel right + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hProductLeft : ∀ visited,
      stateProductInfo whole (.child 0 visited) = stateProductInfo left visited :=
    stateProductInfo_fairChoice_child_left alphabet bid left right
  have hProductRight : ∀ visited,
      stateProductInfo whole (.child 1 visited) =
        stateProductInfo right visited :=
    stateProductInfo_fairChoice_child_right alphabet bid left right
  -- A copied child state has its child's own menu.
  have hTransportLeft : ∀ q ∈ (compileTypeFuel (typeCompilationFuel left)
      left).states, computeFutureOf whole (.child 0 q) = computeFutureOf left q :=
    fun q hq => computeFutureOf_binaryChoice_left alphabet left right
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) whole hWhole hFuelLeft hLeftDisjoint
      (by rw [hLeftAlphabet, hWholeDef]; rfl) hProductLeft q hq
  have hTransportRight : ∀ q ∈ (compileTypeFuel (typeCompilationFuel right)
      right).states,
      computeFutureOf whole (.child 1 q) = computeFutureOf right q :=
    fun q hq => computeFutureOf_binaryChoice_right alphabet left right
      (TypeLabel.fair bid true) (TypeLabel.fair bid false) whole hWhole hFuelRight hRightDisjoint
      (by rw [hRightAlphabet, hWholeDef]; rfl) hProductRight q hq
  intro residual state hRelated
  rcases relationMembership_fairChoice_cases alphabet bid left right hRelated with
    hRoot | ⟨q, hState, hChild⟩ | ⟨q, hState, hChild⟩
  · -- Root: split the menu across the two selection edges.
    injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    have hWholeDisjoint : whole.OfferBranchesDisjoint := by
      simp only [hWholeDef, PactType.OfferBranchesDisjoint]
      exact ⟨hLeftDisjoint, hRightDisjoint⟩
    have hEnv : ∃ environment ∈ alphabet.localEnvironments,
        environment.clock = false :=
      ⟨TypeEnvironment.empty, empty_mem_localEnvironments alphabet, rfl⟩
    have hOffers :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).offersAt
          TypeAutomatonState.root = ∅ := by
      rw [hWhole]
      exact buildChoiceAutomaton_offersAt_root alphabet _ _ _ _
    have hRefs :
        ({ states := (compileTypeFuel (typeCompilationFuel whole) whole).states
           edges := (compileTypeFuel (typeCompilationFuel whole)
             whole).edges } : PendingAutomaton).referencedStates
          TypeAutomatonState.root =
        {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
          childState 1
            (compileTypeFuel (typeCompilationFuel right) right).initial} := by
      rw [hWhole]
      exact buildChoiceAutomaton_referencedStates_root alphabet _ _ _ _
        (by simp [TypeLabel.fair]) (by simp [TypeLabel.fair]) hEnv
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      {childState 0 (compileTypeFuel (typeCompilationFuel left) left).initial,
        childState 1
          (compileTypeFuel (typeCompilationFuel right) right).initial}
      _ rfl
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildChoiceAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hRefs]
        simp [Finset.insert_subset_iff])
      (by rw [hRefs])
      (by
        simp only [hWholeDef]
        exact stateProductInfo_fairChoice_root alphabet bid left right)
      (by
        intro action hIn
        rw [hOffers] at hIn
        exact absurd hIn (Finset.notMem_empty _))
    rw [hDecomp, hOffers, Finset.empty_union, Finset.biUnion_insert,
      Finset.singleton_biUnion]
    simp only [childState]
    have hLeftMenu : computeFutureOf left
        (compileTypeFuel (typeCompilationFuel left) left).initial =
          typeFutureOffers left :=
      hLeft (buildRelationSet_initial left _ rfl)
    have hRightMenu : computeFutureOf right
        (compileTypeFuel (typeCompilationFuel right) right).initial =
          typeFutureOffers right :=
      hRight (buildRelationSet_initial right _ rfl)
    rw [hTransportLeft _ (compileTypeFuel_initial_mem _ left (Nat.le_refl _)),
      hTransportRight _ (compileTypeFuel_initial_mem _ right (Nat.le_refl _)),
      hLeftMenu, hRightMenu]
    exact (typeFutureOffers_fairChoice alphabet bid left right).symm
  · subst hState
    rw [hTransportLeft q (relationMembership_state_mem left _ q hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q (relationMembership_state_mem right _ q hChild)]
    exact hRight hChild

/-- Compiling an exclusive offer at its own budget builds the offer automaton
over the default and branch fragments compiled at theirs. -/
theorem compileTypeFuel_xoffer_eq (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    compileTypeFuel (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) =
      buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)) := by
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]
  congr 1
  · exact compileTypeFuel_eq_of_sufficient elseType (Nat.le_max_left _ _)
      (Nat.le_refl _)
  · refine List.map_congr_left ?_
    intro branch hBranch
    have hFuel : typeCompilationFuel branch.2 ≤
        max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches) := by
      have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
        branch hBranch
      omega
    rw [compileTypeFuel_eq_of_sufficient branch.2 hFuel (Nat.le_refl _)]

/-- Environments and offers stay local across the indexed branch copies. -/
private lemma indexedFragment_edgeLocal
    (alphabet : PactTypeAlphabet)
    (automata : List (BareMessage × AutomatonFragment))
    (hFamilies : ∀ entry ∈ automata, ∀ edge ∈ entry.2.edges,
      edge.environment ∈ alphabet.localEnvironments)
    (hOffers : ∀ entry ∈ automata, ∀ edge ∈ entry.2.edges,
      edge.current ⊆ alphabet.actions ∧
        ∀ offers, edge.future = .explicit offers → offers ⊆ alphabet.actions) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.environment ∈ alphabet.localEnvironments ∧
        edge.current ⊆ alphabet.actions ∧
        ∀ offers, edge.future = .explicit offers →
          offers ⊆ alphabet.actions := by
  classical
  intro edge hEdge
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    simp only [childPendingEdges, Finset.mem_image] at hChildEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChildEdge
    obtain ⟨hCur, hFut⟩ := hOffers indexed.1 hEntry childEdge hChildMem
    refine ⟨hFamilies indexed.1 hEntry childEdge hChildMem, hCur, ?_⟩
    intro offers hSpecEq
    simp only [childPendingEdge, childFutureSpec] at hSpecEq
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hSpecEq
        simp only [FutureSpec.explicit.injEq] at hSpecEq
        subst hSpecEq
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hSpecEq; simp at hSpecEq

private lemma edgeLocal_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hBranchAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hElse : EdgeEnvironmentsLocal elseType ∧ EdgeOffersLocal elseType)
    (hBranch : ∀ branch ∈ branches,
      EdgeEnvironmentsLocal branch.2 ∧ EdgeOffersLocal branch.2) :
    EdgeEnvironmentsLocal (.xoffer alphabet elseType branches) ∧
      EdgeOffersLocal (.xoffer alphabet elseType branches) := by
  classical
  have hIndexedFamilies : ∀ entry ∈ (branches.map fun branch =>
      (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)),
      ∀ edge ∈ entry.2.edges,
        edge.environment ∈ alphabet.localEnvironments := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨branch, hBranchMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hBranch branch hBranchMem).1 edge hEdgeMem
    rwa [hBranchAlphabet branch hBranchMem] at this
  have hIndexedOffers : ∀ entry ∈ (branches.map fun branch =>
      (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)),
      ∀ edge ∈ entry.2.edges,
        edge.current ⊆ alphabet.actions ∧
          ∀ offers, edge.future = .explicit offers →
            offers ⊆ alphabet.actions := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨branch, hBranchMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hBranch branch hBranchMem).2 edge hEdgeMem
    rwa [hBranchAlphabet branch hBranchMem] at this
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_xoffer_eq alphabet elseType branches] at hEdge <;>
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge <;>
    rcases hEdge with ((((hElseEdge | hIndexed) | hBranchEdge) | hWait) |
      hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    have := hElse.1 childEdge hChildMem
    rw [hElseAlphabet] at this
    simpa [childPendingEdge] using this
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).1
  · rw [mem_foldl_union_iff] at hBranchEdge
    rcases hBranchEdge with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hNewEdge
      exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hWait
    exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hResolved
    exact hLocal
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    obtain ⟨hCur, hFut⟩ := hElse.2 childEdge hChildMem
    rw [hElseAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).2
  · rw [mem_foldl_union_iff] at hBranchEdge
    rcases hBranchEdge with hEmpty | ⟨indexed, hIndexedMem, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨-, -, -, hGate⟩, rfl⟩ := hNewEdge
      have hEntry : indexed.1 ∈ (branches.map fun branch =>
          (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)) := by
        have hMapped : indexed.1 ∈ (branches.map fun branch =>
            (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
              branch.2)).zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexedMem
        simpa using hMapped
      obtain ⟨branch, hBranchMem, hEq⟩ := List.mem_map.mp hEntry
      refine ⟨?_, by intro _ h; simp at h⟩
      have hActionEq : indexed.1.1 = branch.1 := by rw [← hEq]
      simp only [Finset.singleton_subset_iff, hActionEq]
      exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨-, -, -, hGate⟩, rfl⟩ := hWait
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    have hIn : action ∈ typeBranchActions branches :=
      (Finset.mem_inter.mp hAction).2
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
    obtain ⟨branch, hBranchMem, rfl⟩ := hIn
    exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, -, rfl⟩ := hResolved
    exact ⟨by simp, by intro _ h; simp at h⟩

private lemma edgeLocal_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hSelectedAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        alphabet)
    (hElse : EdgeEnvironmentsLocal elseType ∧ EdgeOffersLocal elseType)
    (hSelected : ∀ selected ∈ branches,
      EdgeEnvironmentsLocal (parallelTypeBranchesSelecting alphabet selected
          branches) ∧
        EdgeOffersLocal (parallelTypeBranchesSelecting alphabet selected
          branches)) :
    EdgeEnvironmentsLocal (.offer alphabet elseType branches) ∧
      EdgeOffersLocal (.offer alphabet elseType branches) := by
  classical
  have hIndexedFamilies : ∀ entry ∈ (branches.map fun selected =>
      (selected.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches))),
      ∀ edge ∈ entry.2.edges,
        edge.environment ∈ alphabet.localEnvironments := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨selected, hSelectedMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hSelected selected hSelectedMem).1 edge hEdgeMem
    rwa [hSelectedAlphabet selected hSelectedMem] at this
  have hIndexedOffers : ∀ entry ∈ (branches.map fun selected =>
      (selected.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches))),
      ∀ edge ∈ entry.2.edges,
        edge.current ⊆ alphabet.actions ∧
          ∀ offers, edge.future = .explicit offers →
            offers ⊆ alphabet.actions := by
    intro entry hEntry edge hEdgeMem
    obtain ⟨selected, hSelectedMem, rfl⟩ := List.mem_map.mp hEntry
    have := (hSelected selected hSelectedMem).2 edge hEdgeMem
    rwa [hSelectedAlphabet selected hSelectedMem] at this
  constructor <;> intro edge hEdge <;>
    rw [compileTypeFuel_offer_eq alphabet elseType branches] at hEdge <;>
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge <;>
    rcases hEdge with ((((hElseEdge | hIndexed) | hEnabled) | hWait) | hResolved)
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    have := hElse.1 childEdge hChildMem
    rw [hElseAlphabet] at this
    simpa [childPendingEdge] using this
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).1
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hNewEdge
      exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hWait
    exact hLocal
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hResolved
    exact hLocal
  · simp only [childPendingEdges, Finset.mem_image] at hElseEdge
    obtain ⟨childEdge, hChildMem, rfl⟩ := hElseEdge
    obtain ⟨hCur, hFut⟩ := hElse.2 childEdge hChildMem
    rw [hElseAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    intro offers hOffers
    simp only [childPendingEdge, childFutureSpec] at hOffers
    cases hSpec : childEdge.future with
    | explicit childOffers =>
        rw [hSpec] at hOffers
        simp only [FutureSpec.explicit.injEq] at hOffers
        subst hOffers
        exact hFut childOffers hSpec
    | «at» t r => rw [hSpec] at hOffers; simp at hOffers
  · exact (indexedFragment_edgeLocal alphabet _ hIndexedFamilies
      hIndexedOffers edge hIndexed).2
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, -, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, -, rfl⟩ := hNewEdge
      exact ⟨by simp, by intro _ h; simp at h⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨-, -, -, -, hGate⟩, rfl⟩ := hWait
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
    obtain ⟨branch, hBranchMem, rfl⟩ := hAction
    exact hGate branch hBranchMem
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨-, -, -, -, hGate⟩, rfl⟩ := hResolved
    refine ⟨?_, by intro _ h; simp at h⟩
    intro action hAction
    simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
    obtain ⟨branch, hBranchMem, rfl⟩ := hAction
    exact hGate branch hBranchMem

/-- Alphabet well-formedness descends to each branch body. -/
theorem branchAlphabetWellFormed_of_mem :
    ∀ {alphabet : PactTypeAlphabet} {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.BranchesAlphabetWellFormed alphabet branches →
      branch ∈ branches → branch.2.AlphabetWellFormed
  | _, (_, _) :: rest, branch, hWF, hMem => by
      rw [PactType.BranchesAlphabetWellFormed] at hWF
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hWF.2.1
      · exact branchAlphabetWellFormed_of_mem hWF.2.2 hRest
  | _, [], _, _, hMem => by simp at hMem
  termination_by _ branches => sizeOf branches

/-- Interface scoping descends to each branch body. -/
theorem interfaceScopedBranches_mem :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.InterfaceScopedBranches branches → branch ∈ branches →
      branch.2.InterfaceScoped
  | (_, _) :: rest, branch, hScoped, hMem => by
      rw [PactType.InterfaceScopedBranches] at hScoped
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hScoped.1
      · exact interfaceScopedBranches_mem hScoped.2 hRest
  | [], _, _, hMem => by simp at hMem
  termination_by branches => sizeOf branches

/-- Interface-alphabet scoping descends to each branch body. -/
theorem interfaceAlphabetScopedBranches_mem :
    ∀ {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.InterfaceAlphabetScopedBranches branches → branch ∈ branches →
      branch.2.InterfaceAlphabetScoped
  | (_, _) :: rest, branch, hScoped, hMem => by
      rw [PactType.InterfaceAlphabetScopedBranches] at hScoped
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact hScoped.1
      · exact interfaceAlphabetScopedBranches_mem hScoped.2 hRest
  | [], _, _, hMem => by simp at hMem
  termination_by branches => sizeOf branches

/-- Edge locality holds at every constructor.  Each builder draws environments
from the node's own `localEnvironments` and its currents from `∅`, a gated
singleton, or a gated branch-action set, and copies child edges unchanged. -/
theorem edgeLocalAt_holds :
    ∀ fuel processType, TypeCompilationFuelSufficient processType fuel →
      processType.AlphabetWellFormed →
      processType.InterfaceScoped →
      processType.InterfaceAlphabetScoped →
      EdgeLocalAt fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel _ _ _
      exact (Nat.not_lt_zero _
        (TypeCompilationFuelSufficient.positive hFuel)).elim
  | succ fuel ih =>
      intro processType hFuel hWF hScoped hAlphaScoped
      cases processType with
      | skip alphabet =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_skip alphabet)
      | var alphabet name =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_var alphabet name)
      | message alphabet msg dir =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_message alphabet msg dir)
      | tock alphabet =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_tock alphabet)
      | progress alphabet pid =>
          exact edgeLocalAt_of_edgeLocal hFuel (edgeLocal_progress alphabet pid)
      | choice alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_choice alphabet left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | fairChoice alphabet bid left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_fairChoice alphabet bid left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | seq alphabet left right =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_seq alphabet left right hWF.2.1 hWF.2.2.1 ?_ ?_)
          · exact edgeLocal_of_edgeLocalAt hLeftFuel
              (ih left hLeftFuel hWF.2.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · exact edgeLocal_of_edgeLocalAt hRightFuel
              (ih right hRightFuel hWF.2.2.2.2 hScoped.2 hAlphaScoped.2.2)
      | recur alphabet name body =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hBodyFuel : TypeCompilationFuelSufficient body fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_recur alphabet name body hWF.2.1 ?_)
          exact edgeLocal_of_edgeLocalAt hBodyFuel
            (ih body hBodyFuel hWF.2.2 hScoped hAlphaScoped.2)
      | xoffer alphabet elseType branches =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hBranchFuel : ∀ branch ∈ branches,
              TypeCompilationFuelSufficient branch.2 fuel := by
            intro branch hBranch
            have hBound := typeCompilationFuel_le_typeBranchCompilationFuel
              branches branch hBranch
            simp only [TypeCompilationFuelSufficient]; omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_xoffer alphabet elseType branches hWF.2.1 ?_ ?_ ?_)
          · intro branch hBranch
            exact PactType.branch_alphabet_eq_of_mem hWF.2.2.2 hBranch
          · exact edgeLocal_of_edgeLocalAt hElseFuel
              (ih elseType hElseFuel hWF.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · intro branch hBranch
            exact edgeLocal_of_edgeLocalAt (hBranchFuel branch hBranch)
              (ih branch.2 (hBranchFuel branch hBranch)
                (branchAlphabetWellFormed_of_mem hWF.2.2.2 hBranch)
                (interfaceScopedBranches_mem hScoped.2 hBranch)
                (interfaceAlphabetScopedBranches_mem hAlphaScoped.2.2 hBranch))
      | offer alphabet elseType branches =>
          have hWFOffer := hWF
          have hScopedOffer := hScoped
          have hAlphaScopedOffer := hAlphaScoped
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hElseFuel : TypeCompilationFuelSufficient elseType fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hSelectedFuel : ∀ selected ∈ branches,
              TypeCompilationFuelSufficient
                (parallelTypeBranchesSelecting alphabet selected branches) fuel := by
            intro selected hSelected
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_parallelTypeBranchesSelecting]
            omega
          refine edgeLocalAt_of_edgeLocal (by
            simp only [TypeCompilationFuelSufficient, typeCompilationFuel]; omega)
            (edgeLocal_offer alphabet elseType branches hWF.2.1 ?_ ?_ ?_)
          · intro selected hSelected
            exact parallelTypeBranchesSelecting_alphabet_eq_of_mem hSelected
          · exact edgeLocal_of_edgeLocalAt hElseFuel
              (ih elseType hElseFuel hWF.2.2.1 hScoped.1 hAlphaScoped.2.1)
          · intro selected hSelected
            exact edgeLocal_of_edgeLocalAt (hSelectedFuel selected hSelected)
              (ih _ (hSelectedFuel selected hSelected)
                (committedOfferAlphabetWellFormed_holds alphabet elseType branches
                  selected hWFOffer hScopedOffer hAlphaScopedOffer hSelected)
                (committedOfferScoping_holds alphabet elseType branches selected
                  hScopedOffer hAlphaScopedOffer hSelected).1
                (committedOfferScoping_holds alphabet elseType branches selected
                  hScopedOffer hAlphaScopedOffer hSelected).2)
      | par alphabet left right interface =>
          simp only [PactType.AlphabetWellFormed] at hWF
          simp only [PactType.InterfaceScoped] at hScoped
          simp only [PactType.InterfaceAlphabetScoped] at hAlphaScoped
          simp only [TypeCompilationFuelSufficient, typeCompilationFuel] at hFuel
          have hLeftFuel : TypeCompilationFuelSufficient left fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          have hRightFuel : TypeCompilationFuelSufficient right fuel := by
            simp only [TypeCompilationFuelSufficient]; omega
          -- The re-stamped children avoid the parent's own interfaces, so the
          -- three regularity predicates transport across `reannotate`.
          have hAvoidLeft : ∀ action ∈ alphabet.actions,
              action.1 ∉ PactType.ParallelInterfaces left := by
            intro action hAction hInterface
            refine absurd hAlphaScoped.1 (Finset.not_disjoint_iff.mpr
              ⟨action.1, Finset.mem_image.mpr ⟨action, hAction, rfl⟩, ?_⟩)
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hInterface)
          have hAvoidRight : ∀ action ∈ alphabet.actions,
              action.1 ∉ PactType.ParallelInterfaces right := by
            intro action hAction hInterface
            refine absurd hAlphaScoped.1 (Finset.not_disjoint_iff.mpr
              ⟨action.1, Finset.mem_image.mpr ⟨action, hAction, rfl⟩, ?_⟩)
            exact Finset.mem_union_right _ hInterface
          have hLeftRestampFuel : TypeCompilationFuelSufficient
              (left.reannotate alphabet) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_reannotate]
            exact hLeftFuel
          have hRightRestampFuel : TypeCompilationFuelSufficient
              (right.reannotate alphabet) fuel := by
            simp only [TypeCompilationFuelSufficient,
              typeCompilationFuel_reannotate]
            exact hRightFuel
          have hLeftLocal := ih left hLeftFuel hWF.2.2.1 hScoped.2.1
            hAlphaScoped.2.1
          have hRightLocal := ih right hRightFuel hWF.2.2.2 hScoped.2.2
            hAlphaScoped.2.2
          have hLeftRestamp := ih (left.reannotate alphabet) hLeftRestampFuel
            (PactType.reannotate_alphabetWellFormed_avoiding left alphabet
              hWF.2.2.1 hWF.1 hScoped.2.1 hAvoidLeft)
            (PactType.reannotate_interfaceScoped left alphabet hScoped.2.1)
            (PactType.reannotate_interfaceAlphabetScoped left alphabet
              hAlphaScoped.2.1 hAvoidLeft)
          have hRightRestamp := ih (right.reannotate alphabet) hRightRestampFuel
            (PactType.reannotate_alphabetWellFormed_avoiding right alphabet
              hWF.2.2.2 hWF.1 hScoped.2.2 hAvoidRight)
            (PactType.reannotate_interfaceScoped right alphabet hScoped.2.2)
            (PactType.reannotate_interfaceAlphabetScoped right alphabet
              hAlphaScoped.2.2 hAvoidRight)
          intro edge hEdge
          rw [compileTypeFuel] at hEdge
          refine ⟨?_, ?_⟩
          · exact buildParallelAutomaton_edge_families alphabet left.alphabet
              right.alphabet interface _ _ _ _ _ _ _ _
              hWF.2.1.parent_eq_left
              (fun e he => (hLeftLocal e he).1) (fun e he => (hRightLocal e he).1)
              (fun e he => by
                have := (hLeftRestamp e he).1
                rwa [PactType.reannotate_alphabet] at this)
              (fun e he => by
                have := (hRightRestamp e he).1
                rwa [PactType.reannotate_alphabet] at this)
              edge hEdge
          · exact buildParallelAutomaton_edge_offers alphabet left.alphabet
              right.alphabet interface _ _ _ _ _ _ _ _
              hWF.2.1.parent_eq_left hWF.2.1.parent_eq_right
              (fun e he => (hLeftLocal e he).2.1)
              (fun e he => (hRightLocal e he).2.1)
              (fun e he => by
                have := (hLeftRestamp e he).2.1
                rwa [PactType.reannotate_alphabet] at this)
              (fun e he => by
                have := (hRightRestamp e he).2.1
                rwa [PactType.reannotate_alphabet] at this)
              edge hEdge

/-- A copied default-arm edge of an exclusive offer restricts to an edge of
the default arm. -/
theorem xoffer_else_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType elseType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_xoffer_child_else alphabet elseType branches
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel elseType) elseType).edges,
      pendingEdge = childPendingEdge 0 childEdge := by
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, hMem, hEq⟩ := hElse
      exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge elseType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_else elseType branches
          (.xoffer alphabet elseType branches) hWhole hFuelElse hElseDisjoint
          hElseAlphabet hProductInfo t hStateMem]

/-- A default-arm edge lifts to the copied edge of an exclusive offer. -/
theorem xoffer_else_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType elseType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_xoffer_child_else alphabet elseType branches
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge elseType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_else elseType branches
          (.xoffer alphabet elseType branches) hWhole hFuelElse hElseDisjoint
          hElseAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

theorem xoffer_branch_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hGet : branches[i]? = some (action, branchType))
    (hBranchDisjoint : branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : branchType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child (i + 1) q' ∧
      (compileType branchType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelBranch : typeCompilationFuel branchType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    have hBound := typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) (List.mem_of_getElem? hGet)
    simp only [typeCompilationFuel] at *
    omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child (i + 1) visited) =
        stateProductInfo branchType visited :=
    stateProductInfo_xoffer_child_branch alphabet elseType branches i action branchType hGet
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
      (.child (i + 1) q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel branchType) branchType).edges,
      pendingEdge = childPendingEdge (i + 1) childEdge := by
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElse
      rw [← hEq] at hPSource
      simp [childPendingEdge, childState] at hPSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, hMem, hEq⟩ := hIn
        -- The tag pins the index, and the index pins the branch automaton.
        have hIdx : indexed.2 = i := by
          rw [← hEq] at hPSource
          have h := hPSource
          simp only [childPendingEdge, childState,
            TypeAutomatonState.child.injEq] at h
          omega
        subst hIdx
        have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [List.getElem?_map, hGet] at hMapGet
        have hFragEq : indexed.1.2 =
            compileTypeFuel (typeCompilationFuel branchType) branchType := by
          simpa using (congrArg (fun o => (Option.map Prod.snd o)) hMapGet).symm
        rw [hFragEq] at hMem
        exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge branchType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel branchType) branchType le_rfl hBranchDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_branch elseType branches
          (.xoffer alphabet elseType branches) hWhole i action branchType hGet
          hFuelBranch hBranchDisjoint hBranchAlphabet hProductInfo t hStateMem]

/-- A branch-body edge lifts to the copied edge of an exclusive offer. -/
theorem xoffer_branch_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (action : BareMessage) (branchType : PactType)
    (hGet : branches[i]? = some (action, branchType))
    (hBranchDisjoint : branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : branchType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType branchType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.xoffer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ (.child (i + 1) q') := by
  classical
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hFuelBranch : typeCompilationFuel branchType + 1 ≤
      typeCompilationFuel (.xoffer alphabet elseType branches) := by
    have hBound := typeCompilationFuel_le_typeBranchCompilationFuel branches
      (action, branchType) (List.mem_of_getElem? hGet)
    simp only [typeCompilationFuel] at *
    omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.xoffer alphabet elseType branches) (.child (i + 1) visited) =
        stateProductInfo branchType visited :=
    stateProductInfo_xoffer_child_branch alphabet elseType branches i action branchType hGet
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge branchType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.xoffer alphabet elseType branches)
    (.child (i + 1) q) (.child (i + 1) q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hMapGet : (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel branch.2) branch.2))[i]? =
        some (action, compileTypeFuel (typeCompilationFuel branchType)
          branchType) := by
      simpa using congrArg (Option.map fun b => ((b.1 : BareMessage),
        compileTypeFuel (typeCompilationFuel b.2) b.2)) hGet
    exact ((buildExclusiveOfferAutomaton_outgoing_branch alphabet branches
      (compileTypeFuel (typeCompilationFuel elseType) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel branch.2) branch.2)) i action
      (compileTypeFuel (typeCompilationFuel branchType) branchType) hMapGet q
      (childPendingEdge (i + 1) childEdge)).mpr
      ⟨childEdge, hChildEdgeMem, hCSource, rfl⟩).1
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel branchType) branchType le_rfl hBranchDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_exclusiveOffer_branch elseType branches
          (.xoffer alphabet elseType branches) hWhole i action branchType hGet
          hFuelBranch hBranchDisjoint hBranchAlphabet hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- Current-offer correspondence at an exclusive offer.  Following the paper:
the root's guards, labels, current offers and targets are identical in the
semantic rule and the edge family, and the copied default and branch entries use
the lower-rank hypothesis. -/
theorem currentOfferCorrespondence_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.xoffer alphabet elseType branches).alphabet)
    (hBranchDisjoint : ∀ action branchType, (action, branchType) ∈ branches →
      branchType.OfferBranchesDisjoint)
    (hBranchAlphabet : ∀ action branchType, (action, branchType) ∈ branches →
      branchType.alphabet = (PactType.xoffer alphabet elseType branches).alphabet)
    (hElse : CurrentOfferCorrespondence elseType)
    (hBranches : ∀ action branchType, (action, branchType) ∈ branches →
      CurrentOfferCorrespondence branchType) :
    CurrentOfferCorrespondence (.xoffer alphabet elseType branches) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_xoffer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, action, branchType, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: each offer rule names its own root edge family.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | xoffer_branch cEnv cAlpha cElse cBranches cAction residual' hCond hGate =>
          obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hCond.2.1
          refine Exists.intro
            (.child (index + 1) (compileTypeFuel
              (typeCompilationFuel residual') residual').initial)
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                (.child (index + 1) (compileTypeFuel
                  (typeCompilationFuel residual') residual').initial) \
                {cAction}) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              (.child (index + 1) (compileTypeFuel
                (typeCompilationFuel residual') residual').initial) env
              (TypeLabel.message cAction.1 cAction.2) _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible
                  (TypeLabel.message cAction.1 cAction.2),
                current := {cAction},
                future := FutureSpec.at (childState (index + 1)
                  (compileTypeFuel (typeCompilationFuel residual') residual').initial)
                  {cAction},
                target := childState (index + 1) (compileTypeFuel
                  (typeCompilationFuel residual') residual').initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
                Finset.mem_union]
              refine Or.inl (Or.inl (Or.inr ?_))
              rw [mem_foldl_union_iff]
              refine Or.inr ⟨(⟨cAction, compileTypeFuel
                (typeCompilationFuel residual') residual'⟩, index), ?_, ?_⟩
              · exact List.mk_mem_zipIdx_iff_getElem?.mpr
                  ((branches_map_getElem?_eq_some_iff branches index cAction
                    (compileTypeFuel (typeCompilationFuel residual') residual')).mpr
                    ⟨residual', hBranchGet, rfl⟩)
              · simp only [Finset.mem_image, Finset.mem_filter]
                exact ⟨env,
                  ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                    hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_xoffer_branch alphabet elseType branches
              hBranchGet
              (buildRelationSet_initial residual' (compileType residual'))
      | xoffer_else cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro
            (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
              elseType).initial)
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                  elseType).initial)) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                elseType).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial) ∅,
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
                Finset.mem_union, Finset.mem_image, Finset.mem_filter]
              exact Or.inr ⟨env,
                ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                  hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_xoffer_else alphabet elseType branches
              (buildRelationSet_initial elseType (compileType elseType))
      | xoffer_wait cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro TypeAutomatonState.root
            (Exists.intro
              (computeFutureOf (.xoffer alphabet elseType branches)
                TypeAutomatonState.root \
                  typeWaitingOffers env branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.xoffer alphabet elseType branches) TypeAutomatonState.root
              TypeAutomatonState.root env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeWaitingOffers env branches,
                future := FutureSpec.at TypeAutomatonState.root
                  (typeWaitingOffers env branches),
                target := TypeAutomatonState.root }
              ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
              Finset.mem_union, Finset.mem_image, Finset.mem_filter]
            refine Or.inl (Or.inr ⟨env, ⟨
              PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
              hCond.2.2, ?_, hGate⟩, ?_⟩)
            · exact hCond.2.1
            · simp [typeWaitingOffers, typeBranchActions]
          · exact relationMembership_xoffer_root alphabet elseType branches
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hElse.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        xoffer_else_edge_lift alphabet elseType branches hElseDisjoint
          hElseAlphabet hChildEdge,
        relationMembership_xoffer_else alphabet elseType branches hChildTarget⟩
    · -- Copied branch entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        (hBranches action branchType
          (List.mem_of_getElem? hGet)).1 hChildRelated hTransition
      exact ⟨.child (i + 1) q', future',
        xoffer_branch_edge_lift alphabet elseType branches i action branchType
          hGet (hBranchDisjoint action branchType (List.mem_of_getElem? hGet))
          (hBranchAlphabet action branchType (List.mem_of_getElem? hGet))
          hChildEdge,
        relationMembership_xoffer_branch alphabet elseType branches
          hGet hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_xoffer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, action, branchType, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: the three root families are exactly the three offer rules.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge
          (.xoffer alphabet elseType branches) TypeAutomatonState.root state'
          env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
      rcases hPendingMem with ((((hElseCopy | hIndexed) | hBranch) | hWait)
        | hResolved)
      · exfalso
        obtain ⟨childEdge, -, hEq⟩ := hElseCopy
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [childPendingEdges, Finset.mem_image] at hIn
          obtain ⟨childEdge, -, hEq⟩ := hIn
          rw [← hEq] at hPSource
          simp [childPendingEdge, childState] at hPSource
      · -- Fire family: one root edge per enabled branch.
        rw [mem_foldl_union_iff] at hBranch
        rcases hBranch with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [Finset.mem_image, ] at hIn
          obtain ⟨environment, hFilter, hEq⟩ := hIn
          rw [Finset.mem_filter] at hFilter
          obtain ⟨hEnvMem, hEnabled, hResolvedNeeds, hGate⟩ := hFilter
          -- Recover the branch this index names.
          have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
          rw [List.getElem?_map] at hMapGet
          obtain ⟨entry, hEntryGet, hEntryEq⟩ :=
            Option.map_eq_some_iff.mp hMapGet
          rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
          simp only at hPEnv hPLabel hPCurrent hPTarget
          subst hPEnv
          have hActionEq : indexed.1.1 = entry.1 := by rw [← hEntryEq]
          have hLabelEq : label =
              TypeLabel.message indexed.1.1.1 indexed.1.1.2 := by
            have h := hPLabel; simp at h; exact h.symm
          subst hLabelEq
          have hCurrentEq : current = {indexed.1.1} := hPCurrent.symm
          subst hCurrentEq
          refine ⟨entry.2, typeFutureOffers entry.2 \ {entry.1}, ?_, ?_⟩
          · rw [hActionEq]
            exact ⟨TypeTransition.xoffer_branch environment alphabet elseType
                branches entry.1 entry.2
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hActionEq ▸ hEnabled,
                  hResolvedNeeds⟩ hGate,
              TypeOffers.xoffer_branch environment alphabet elseType branches
                entry.1 entry.2
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hActionEq ▸ hEnabled,
                  hResolvedNeeds⟩ hGate⟩
          · rw [← hPTarget]
            have hFragEq : indexed.1.2 =
                compileTypeFuel (typeCompilationFuel entry.2) entry.2 := by
              rw [← hEntryEq]
            rw [hFragEq]
            exact relationMembership_xoffer_branch alphabet elseType branches
              hEntryGet
              (buildRelationSet_initial entry.2 (compileType entry.2))
      · -- Wait family: the root's silent self-loop.
        obtain ⟨environment, hFilter, hEq⟩ := hWait
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hUnresolved, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        refine ⟨.xoffer alphabet elseType branches,
          typeFutureOffers (.xoffer alphabet elseType branches) \
            typeWaitingOffers environment branches, ?_, ?_⟩
        · have hCurrentEq : current = typeWaitingOffers environment branches :=
            hPCurrent.symm
          subst hCurrentEq
          exact ⟨TypeTransition.xoffer_wait environment alphabet elseType
              branches ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                hUnresolved, hClock⟩ hGate,
            TypeOffers.xoffer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hUnresolved,
                hClock⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_xoffer_root alphabet elseType branches
      · -- Default family: the root's silent edge into the copied else entry.
        obtain ⟨environment, hFilter, hEq⟩ := hResolved
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = ∅ := hPCurrent.symm
        subst hCurrentEq
        refine ⟨elseType, typeFutureOffers elseType, ?_, ?_⟩
        · exact ⟨TypeTransition.xoffer_else environment alphabet elseType
              branches ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate,
            TypeOffers.xoffer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_xoffer_else alphabet elseType branches
            (buildRelationSet_initial elseType (compileType elseType))
    · -- Copied default entry: restrict, apply the child, and lift back.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        xoffer_else_edge_restrict alphabet elseType branches hElseDisjoint
          hElseAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hElse.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_xoffer_else alphabet elseType branches hChildTarget⟩
    · -- Copied branch entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        xoffer_branch_edge_restrict alphabet elseType branches i action
          branchType hGet
          (hBranchDisjoint action branchType (List.mem_of_getElem? hGet))
          (hBranchAlphabet action branchType (List.mem_of_getElem? hGet))
          hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        (hBranches action branchType
          (List.mem_of_getElem? hGet)).2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_xoffer_branch alphabet elseType branches hGet
          hChildTarget⟩

/-- A default tag on a conjunctive offer peels to the default arm. -/
theorem stateProductInfo_offer_child_else (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (q : TypeAutomatonState) :
    stateProductInfo (.offer alphabet elseType branches) (.child 0 q) =
      stateProductInfo elseType q := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel]
  exact stateProductInfoFuel_eq_of_sufficient elseType q
    (Nat.le_max_left _ _) (Nat.le_refl _)

/-- So does a selected-conjunction tag. -/
theorem stateProductInfo_offer_child_branch (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hBranch : branches[i]? = some selected)
    (q : TypeAutomatonState) :
    stateProductInfo (.offer alphabet elseType branches) (.child (i + 1) q) =
      stateProductInfo
        (parallelTypeBranchesSelecting alphabet selected branches) q := by
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hFuel : typeCompilationFuel
      (parallelTypeBranchesSelecting alphabet selected branches) ≤
      max (typeCompilationFuel elseType)
        (conjunctiveCompilationFuel branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact Nat.le_max_right _ _
  simp only [stateProductInfo, hFuelEq, stateProductInfoFuel, hBranch]
  exact stateProductInfoFuel_eq_of_sufficient _ q hFuel (Nat.le_refl _)

/-- A copied default-arm edge of a conjunctive offer restricts to an edge of
the default arm. -/
theorem offer_else_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.offer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child 0 q' ∧
      (compileType elseType).HasEdge q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_offer_child_else alphabet elseType branches
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
      (.child 0 q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Invert directly: only the copied default family is sourced at `child 0`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel (typeCompilationFuel elseType) elseType).edges,
      pendingEdge = childPendingEdge 0 childEdge := by
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · obtain ⟨childEdge, hMem, hEq⟩ := hElse
      exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge elseType q childEdge.target env
    label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches
          (.offer alphabet elseType branches) hWhole hElseAlphabet hFuelElse
          hElseDisjoint hProductInfo t hStateMem]

/-- A default-arm edge lifts to the copied edge of a conjunctive offer. -/
theorem offer_else_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge : (compileType elseType).HasEdge q env label ⟨current, future⟩ q') :
    (compileType (.offer alphabet elseType branches)).HasEdge
      (.child 0 q) env label ⟨current, future⟩ (.child 0 q') := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelElse : typeCompilationFuel elseType + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches) (.child 0 visited) =
        stateProductInfo elseType visited :=
    stateProductInfo_offer_child_else alphabet elseType branches
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge elseType q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
    (.child 0 q) (.child 0 q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge 0 childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdgeMem, rfl⟩)))
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel elseType) elseType le_rfl hElseDisjoint childEdge
          hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches
          (.offer alphabet elseType branches) hWhole hElseAlphabet hFuelElse
          hElseDisjoint hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- A copied selected-conjunction edge of a conjunctive offer restricts to an
edge of that generated product. -/
theorem offer_selected_edge_restrict (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hGet : branches[i]? = some selected)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint :
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet :
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    {q : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage} {state' : TypeAutomatonState}
    (hEdge : (compileType (.offer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ state') :
    ∃ q', state' = .child (i + 1) q' ∧
      (compileType (parallelTypeBranchesSelecting alphabet selected branches)).HasEdge
        q env label ⟨current, future⟩ q' := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelSel :
      typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches)
          (.child (i + 1) visited) =
        stateProductInfo
          (parallelTypeBranchesSelecting alphabet selected branches) visited :=
    stateProductInfo_offer_child_branch alphabet elseType branches i selected
      hGet
  obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
    hPFuture, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
      (.child (i + 1) q) state' env label ⟨current, future⟩).mp hEdge
  rw [hWhole] at hPendingMem
  -- Only the copied selected-conjunction family is sourced at `child (i+1)`.
  obtain ⟨childEdge, hChildEdgeMem, hChildEq⟩ : ∃ childEdge ∈
      (compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)).edges,
      pendingEdge = childPendingEdge (i + 1) childEdge := by
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
    rcases hPendingMem with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElse
      rw [← hEq] at hPSource
      simp [childPendingEdge, childState] at hPSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn
        obtain ⟨childEdge, hMem, hEq⟩ := hIn
        have hIdx : indexed.2 = i := by
          have h := hPSource
          rw [← hEq] at h
          simp only [childPendingEdge, childState,
            TypeAutomatonState.child.injEq] at h
          omega
        subst hIdx
        have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        rw [List.getElem?_map, hGet] at hMapGet
        have hFragEq : indexed.1.2 =
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches) := by
          simpa using (congrArg (fun o => (Option.map Prod.snd o)) hMapGet).symm
        rw [hFragEq] at hMem
        exact ⟨childEdge, hMem, hEq.symm⟩
    · exfalso
      rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn
        obtain ⟨environment, -, hEq⟩ := hIn
        rw [← hEq] at hPSource
        simp [childState] at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hPSource
      simp at hPSource
    · exfalso
      obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hPSource
      simp at hPSource
  have hChildSource : childEdge.source = q := by
    rw [hChildEq] at hPSource
    simpa [childPendingEdge, childState] using hPSource
  refine ⟨childEdge.target, by rw [← hPTarget, hChildEq]; rfl, ?_⟩
  rw [compileType_hasEdge_iff_hasResolvedEdge
    (parallelTypeBranchesSelecting alphabet selected branches) q
    childEdge.target env label ⟨current, future⟩]
  refine ⟨childEdge, hChildEdgeMem, hChildSource, ?_, ?_, ?_, ?_, rfl⟩
  · rw [← hPEnv, hChildEq]; rfl
  · rw [← hPLabel, hChildEq]; rfl
  · rw [← hPCurrent, hChildEq]; rfl
  · rw [← hPFuture, hChildEq]
    cases hSpec : childEdge.future with
    | explicit offers => simp [childPendingEdge, childFutureSpec, hSpec]
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) le_rfl
          hSelDisjoint childEdge hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches
          (.offer alphabet elseType branches) hWhole i selected hGet hFuelSel
          hSelAlphabet hDisjoint hProductInfo t hStateMem]

/-- A selected-conjunction edge lifts to the copied edge of a conjunctive
offer. -/
theorem offer_selected_edge_lift (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (i : Nat) (selected : BareMessage × PactType)
    (hGet : branches[i]? = some selected)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint :
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet :
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    {q q' : TypeAutomatonState} {env : TypeEnvironment} {label : TypeLabel}
    {current future : Finset BareMessage}
    (hEdge :
      (compileType (parallelTypeBranchesSelecting alphabet selected branches)).HasEdge
        q env label ⟨current, future⟩ q') :
    (compileType (.offer alphabet elseType branches)).HasEdge
      (.child (i + 1) q) env label ⟨current, future⟩ (.child (i + 1) q') := by
  classical
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hFuelSel :
      typeCompilationFuel
        (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
      typeCompilationFuel (.offer alphabet elseType branches) := by
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [typeCompilationFuel]; omega
  have hProductInfo : ∀ visited,
      stateProductInfo (.offer alphabet elseType branches)
          (.child (i + 1) visited) =
        stateProductInfo
          (parallelTypeBranchesSelecting alphabet selected branches) visited :=
    stateProductInfo_offer_child_branch alphabet elseType branches i selected
      hGet
  obtain ⟨childEdge, hChildEdgeMem, hCSource, hCEnv, hCLabel, hCCurrent,
    hCFuture, hCTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge
      (parallelTypeBranchesSelecting alphabet selected branches) q q' env label
      ⟨current, future⟩).mp hEdge
  rw [compileType_hasEdge_iff_hasResolvedEdge (.offer alphabet elseType branches)
    (.child (i + 1) q) (.child (i + 1) q') env label ⟨current, future⟩, hWhole]
  refine ⟨childPendingEdge (i + 1) childEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hMapGet : (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches)))[i]? =
        some (selected.1, compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches)) := by
      rw [List.getElem?_map, hGet]; rfl
    exact ((buildSelectedConjunctiveOfferAutomaton_outgoing_branch alphabet
      branches (compileTypeFuel (typeCompilationFuel elseType) elseType)
      (branches.map fun branch => (branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches))) i selected.1
      (compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)) hMapGet q
      (childPendingEdge (i + 1) childEdge)).mpr
      ⟨childEdge, hChildEdgeMem, hCSource, rfl⟩).1
  · simp [childPendingEdge, childState, hCSource]
  · simp [childPendingEdge, hCEnv]
  · simp [childPendingEdge, hCLabel]
  · simp [childPendingEdge, hCCurrent]
  · cases hSpec : childEdge.future with
    | explicit offers => simpa [childPendingEdge, childFutureSpec, hSpec] using hCFuture
    | «at» t r =>
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) le_rfl
          hSelDisjoint childEdge hChildEdgeMem t r hSpec
        simp only [childPendingEdge, childFutureSpec, hSpec, childState]
        rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches
          (.offer alphabet elseType branches) hWhole i selected hGet hFuelSel
          hSelAlphabet hDisjoint hProductInfo t hStateMem]
        simpa [childFutureSpec, hSpec] using hCFuture
  · simp [childPendingEdge, childState, hCTarget]

/-- Current-offer correspondence at a conjunctive offer.  The construction has
the same form as the exclusive offer, except that the `i`-th child is the
compiled residual obtained by selecting branch `i`; the root's three rules name
the builder's three root families, and the copied entries use the lower-rank
hypothesis. -/
theorem currentOfferCorrespondence_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hElseDisjoint : elseType.OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet =
      (PactType.offer alphabet elseType branches).alphabet)
    (hDisjoint : ∀ branch ∈ branches, branch.2.OfferBranchesDisjoint)
    (hSelDisjoint : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).OfferBranchesDisjoint)
    (hSelAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        (PactType.offer alphabet elseType branches).alphabet)
    (hElse : CurrentOfferCorrespondence elseType)
    (hSelected : ∀ selected ∈ branches,
      CurrentOfferCorrespondence
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    CurrentOfferCorrespondence (.offer alphabet elseType branches) := by
  classical
  constructor
  · intro residual residual' state env label current future hRelated hTransition
    rcases relationMembership_offer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, selected, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: each offer rule names its own root edge family.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
      obtain ⟨-, hOffers⟩ := hTransition
      cases hOffers with
      | offer_some cEnv cAlpha cElse cBranches cEnabled hCond hGate =>
          obtain ⟨index, hBranchGet⟩ := List.mem_iff_getElem?.mp hCond.2.1
          refine Exists.intro
            (.child (index + 1) (compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet cEnabled branches))
              (parallelTypeBranchesSelecting alphabet cEnabled
                branches)).initial)
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                (.child (index + 1) (compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet cEnabled branches))
                  (parallelTypeBranchesSelecting alphabet cEnabled
                    branches)).initial)) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              (.child (index + 1) (compileTypeFuel
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet cEnabled branches))
                (parallelTypeBranchesSelecting alphabet cEnabled
                  branches)).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := (∅ : Finset BareMessage),
                future := FutureSpec.at (childState (index + 1)
                  (compileTypeFuel
                    (typeCompilationFuel
                      (parallelTypeBranchesSelecting alphabet cEnabled branches))
                    (parallelTypeBranchesSelecting alphabet cEnabled
                      branches)).initial) ∅,
                target := childState (index + 1) (compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet cEnabled branches))
                  (parallelTypeBranchesSelecting alphabet cEnabled
                    branches)).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildSelectedConjunctiveOfferAutomaton,
                finishAutomatonFragment, Finset.mem_union]
              refine Or.inl (Or.inl (Or.inr ?_))
              rw [mem_foldl_union_iff]
              refine Or.inr ⟨(⟨cEnabled.1, compileTypeFuel
                (typeCompilationFuel
                  (parallelTypeBranchesSelecting alphabet cEnabled branches))
                (parallelTypeBranchesSelecting alphabet cEnabled branches)⟩,
                index), ?_, ?_⟩
              · refine List.mk_mem_zipIdx_iff_getElem?.mpr ?_
                rw [List.getElem?_map, hBranchGet]; rfl
              · simp only [Finset.mem_image, Finset.mem_filter]
                exact ⟨env,
                  ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                    hCond.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_offer_selected alphabet elseType branches
              hBranchGet
              (buildRelationSet_initial _ (compileType _))
      | offer_else cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro
            (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
              elseType).initial)
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                  elseType).initial) \ typeBranchActions branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              (.child 0 (compileTypeFuel (typeCompilationFuel elseType)
                elseType).initial) env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeBranchActions branches,
                future := FutureSpec.at (childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial)
                  (typeBranchActions branches),
                target := childState 0 (compileTypeFuel
                  (typeCompilationFuel elseType) elseType).initial }
              ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
            · simp only [buildSelectedConjunctiveOfferAutomaton,
                finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
                Finset.mem_filter]
              exact Or.inr ⟨env,
                ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                  hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩
            · simp [childState]
          · exact relationMembership_offer_else alphabet elseType branches
              (buildRelationSet_initial elseType (compileType elseType))
      | offer_wait cEnv cAlpha cElse cBranches hCond hGate =>
          refine Exists.intro TypeAutomatonState.root
            (Exists.intro
              (computeFutureOf (.offer alphabet elseType branches)
                TypeAutomatonState.root \ typeBranchActions branches) ⟨?_, ?_⟩)
          · rw [compileType_hasEdge_iff_hasResolvedEdge
              (.offer alphabet elseType branches) TypeAutomatonState.root
              TypeAutomatonState.root env TypeLabel.silent _, hWhole]
            refine Exists.intro
              { source := TypeAutomatonState.root, environment := env,
                label := AutomatonConstructionLabel.visible TypeLabel.silent,
                current := typeBranchActions branches,
                future := FutureSpec.at TypeAutomatonState.root
                  (typeBranchActions branches),
                target := TypeAutomatonState.root }
              ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
            simp only [buildSelectedConjunctiveOfferAutomaton,
              finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
              Finset.mem_filter]
            exact Or.inl (Or.inr ⟨env,
              ⟨PactTypeAlphabet.mem_localEnvironments_of_wellFormed hCond.1,
                hCond.2.1, hCond.2.2.1, hCond.2.2.2, hGate⟩, rfl⟩)
          · exact relationMembership_offer_root alphabet elseType branches
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        hElse.1 hChildRelated hTransition
      exact ⟨.child 0 q', future',
        offer_else_edge_lift alphabet elseType branches hElseDisjoint
          hElseAlphabet hChildEdge,
        relationMembership_offer_else alphabet elseType branches hChildTarget⟩
    · -- Copied selected-conjunction entry.
      subst hStateEq
      obtain ⟨q', future', hChildEdge, hChildTarget⟩ :=
        (hSelected selected (List.mem_of_getElem? hGet)).1 hChildRelated
          hTransition
      exact ⟨.child (i + 1) q', future',
        offer_selected_edge_lift alphabet elseType branches i selected hGet
          hDisjoint (hSelDisjoint selected (List.mem_of_getElem? hGet))
          (hSelAlphabet selected (List.mem_of_getElem? hGet)) hChildEdge,
        relationMembership_offer_selected alphabet elseType branches hGet
          hChildTarget⟩
  · intro residual state state' env label current future hRelated hEdge
    rcases relationMembership_offer_cases alphabet elseType branches hRelated
      with hRoot | ⟨q, hStateEq, hChildRelated⟩ |
        ⟨i, selected, q, hGet, hStateEq, hChildRelated⟩
    · -- Root: the three root families are exactly the three offer rules.
      rw [Prod.ext_iff] at hRoot
      obtain ⟨hResEq, hStateEq'⟩ := hRoot
      simp only at hResEq hStateEq'
      subst hResEq; subst hStateEq'
      have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
      obtain ⟨pendingEdge, hPendingMem, hPSource, hPEnv, hPLabel, hPCurrent,
        hPFuture, hPTarget⟩ :=
        (compileType_hasEdge_iff_hasResolvedEdge
          (.offer alphabet elseType branches) TypeAutomatonState.root state'
          env label ⟨current, future⟩).mp hEdge
      rw [hWhole] at hPendingMem
      simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image] at hPendingMem
      rcases hPendingMem with ((((hElseCopy | hIndexed) | hEnabled) | hWait)
        | hResolved)
      · exfalso
        obtain ⟨childEdge, -, hEq⟩ := hElseCopy
        rw [← hEq] at hPSource
        simp [childPendingEdge, childState] at hPSource
      · exfalso
        rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
        rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [childPendingEdges, Finset.mem_image] at hIn
          obtain ⟨childEdge, -, hEq⟩ := hIn
          rw [← hEq] at hPSource
          simp [childPendingEdge, childState] at hPSource
      · -- Enabled family: one root edge per enabled branch.
        rw [mem_foldl_union_iff] at hEnabled
        rcases hEnabled with hEmpty | ⟨indexed, hIndexedMem, hIn⟩
        · exact absurd hEmpty (Finset.notMem_empty _)
        · rw [Finset.mem_image] at hIn
          obtain ⟨environment, hFilter, hEq⟩ := hIn
          rw [Finset.mem_filter] at hFilter
          obtain ⟨hEnvMem, hEnabledNeed, hGate⟩ := hFilter
          have hMapGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
          rw [List.getElem?_map] at hMapGet
          obtain ⟨entry, hEntryGet, hEntryEq⟩ :=
            Option.map_eq_some_iff.mp hMapGet
          rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
          simp only at hPEnv hPLabel hPCurrent hPTarget
          subst hPEnv
          have hActionEq : indexed.1.1 = entry.1 := by rw [← hEntryEq]
          have hEnabledEntry : TypeBranchEnabled environment entry := by
            simp only [TypeBranchEnabled]
            rw [← hActionEq]
            exact hEnabledNeed
          have hLabelEq : label = TypeLabel.silent := by
            have h := hPLabel; simp at h; exact h.symm
          subst hLabelEq
          have hCurrentEq : current = ∅ := hPCurrent.symm
          subst hCurrentEq
          refine ⟨parallelTypeBranchesSelecting alphabet entry branches,
            typeFutureOffers
              (parallelTypeBranchesSelecting alphabet entry branches), ?_, ?_⟩
          · exact ⟨TypeTransition.offer_some environment alphabet elseType
                branches entry
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hEnabledEntry⟩
                hGate,
              TypeOffers.offer_some environment alphabet elseType branches entry
                ⟨PactTypeAlphabet.environment_wellFormed hEnvMem,
                  List.mem_of_getElem? hEntryGet, hEnabledEntry⟩
                hGate⟩
          · rw [← hPTarget]
            have hFragEq : indexed.1.2 =
                compileTypeFuel
                  (typeCompilationFuel
                    (parallelTypeBranchesSelecting alphabet entry branches))
                  (parallelTypeBranchesSelecting alphabet entry branches) := by
              rw [← hEntryEq]
            rw [hFragEq]
            exact relationMembership_offer_selected alphabet elseType branches
              hEntryGet (buildRelationSet_initial _ (compileType _))
      · -- Wait family: the root's silent self-loop.
        obtain ⟨environment, hFilter, hEq⟩ := hWait
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hUnresolved, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        subst hCurrentEq
        refine ⟨.offer alphabet elseType branches,
          typeFutureOffers (.offer alphabet elseType branches) \
            typeBranchActions branches, ?_, ?_⟩
        · exact ⟨TypeTransition.offer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hUnresolved⟩ hGate,
            TypeOffers.offer_wait environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hUnresolved⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_offer_root alphabet elseType branches
      · -- Default family: the root's silent edge into the copied else entry.
        obtain ⟨environment, hFilter, hEq⟩ := hResolved
        rw [Finset.mem_filter] at hFilter
        obtain ⟨hEnvMem, hClock, hNoImmediate, hResolvedNeeds, hGate⟩ := hFilter
        rw [← hEq] at hPEnv hPLabel hPCurrent hPTarget
        simp only at hPEnv hPLabel hPCurrent hPTarget
        subst hPEnv
        have hLabelEq : label = TypeLabel.silent := by
          have h := hPLabel; simp at h; exact h.symm
        subst hLabelEq
        have hCurrentEq : current = typeBranchActions branches := hPCurrent.symm
        subst hCurrentEq
        refine ⟨elseType,
          typeFutureOffers elseType \ typeBranchActions branches, ?_, ?_⟩
        · exact ⟨TypeTransition.offer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate,
            TypeOffers.offer_else environment alphabet elseType branches
              ⟨PactTypeAlphabet.environment_wellFormed hEnvMem, hClock,
                hNoImmediate, hResolvedNeeds⟩ hGate⟩
        · rw [← hPTarget]
          exact relationMembership_offer_else alphabet elseType branches
            (buildRelationSet_initial elseType (compileType elseType))
    · -- Copied default entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        offer_else_edge_restrict alphabet elseType branches hElseDisjoint
          hElseAlphabet hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        hElse.2 hChildRelated hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_offer_else alphabet elseType branches hChildTarget⟩
    · -- Copied selected-conjunction entry.
      subst hStateEq
      obtain ⟨q', hTargetEq, hChildEdge⟩ :=
        offer_selected_edge_restrict alphabet elseType branches i selected hGet
          hDisjoint (hSelDisjoint selected (List.mem_of_getElem? hGet))
          (hSelAlphabet selected (List.mem_of_getElem? hGet)) hEdge
      obtain ⟨residual', future', hChildStep, hChildTarget⟩ :=
        (hSelected selected (List.mem_of_getElem? hGet)).2 hChildRelated
          hChildEdge
      subst hTargetEq
      exact ⟨residual', future', hChildStep,
        relationMembership_offer_selected alphabet elseType branches hGet
          hChildTarget⟩

/-- Menus agree at an exclusive offer.  The root exposes the branch heads on its
own edges and reaches exactly the default and branch entries. -/
theorem futureOffersAgree_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions)
    (hWholeDisjoint :
      (PactType.xoffer alphabet elseType branches).OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hBranchAlphabet : ∀ branch ∈ branches, branch.2.alphabet = alphabet)
    (hElse : FutureOffersAgree elseType)
    (hBranches : ∀ branch ∈ branches, FutureOffersAgree branch.2) :
    FutureOffersAgree (.xoffer alphabet elseType branches) := by
  classical
  set whole : PactType := .xoffer alphabet elseType branches with hWholeDef
  have hWhole := compileTypeFuel_xoffer_eq alphabet elseType branches
  have hDisjointParts :
      elseType.OfferBranchesDisjoint ∧
        PactType.OfferBranchesDisjointBranches branches := by
    simpa only [hWholeDef, PactType.OfferBranchesDisjoint] using hWholeDisjoint
  have hElseDisjoint : elseType.OfferBranchesDisjoint := hDisjointParts.1
  have hBranchDisjoint : ∀ branch ∈ branches,
      branch.2.OfferBranchesDisjoint := by
    intro branch hBranch
    exact offerBranchesDisjoint_of_mem hDisjointParts.2 hBranch
  have hElseFuel :
      typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hBranchFuel : ∀ branch ∈ branches,
      typeCompilationFuel branch.2 + 1 ≤ typeCompilationFuel whole := by
    intro branch hBranch
    have hLe := typeCompilationFuel_le_typeBranchCompilationFuel branches
      branch hBranch
    simp only [hWholeDef, typeCompilationFuel]
    omega
  intro residual state hRelated
  rcases relationMembership_xoffer_cases alphabet elseType branches
      hRelated with hRoot | ⟨q, hState, hChild⟩ |
      ⟨i, action, branchType, q, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    set branchAutomata :=
      branches.map fun branch =>
        (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2)
      with hBranchAutomata
    set elseFragment :=
      compileTypeFuel (typeCompilationFuel elseType) elseType with hElseFragment
    set pending : PendingAutomaton :=
      { states := (compileTypeFuel (typeCompilationFuel whole) whole).states
        edges := (compileTypeFuel (typeCompilationFuel whole) whole).edges }
      with hPending
    have hHeads : branchAutomata.map Prod.fst = branches.map Prod.fst := by
      rw [hBranchAutomata, List.map_map]
      rfl
    have hOffers : pending.offersAt TypeAutomatonState.root =
        typeBranchActions branches := by
      rw [hPending, hWhole]
      exact buildExclusiveOfferAutomaton_offersAt_root alphabet branches
        elseFragment branchAutomata hHeads hGuard
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      (exclusiveOfferEntries elseFragment branchAutomata) pending hPending
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        rw [hPending]
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hPending, hWhole]
        exact buildExclusiveOfferAutomaton_referencedStates_root_subset
          alphabet branches elseFragment branchAutomata)
      (by
        rw [hPending, hWhole]
        exact buildExclusiveOfferAutomaton_entries_subset_referencedStates_root
          alphabet branches elseFragment branchAutomata hHeads hGuard)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_xoffer_root alphabet elseType branches)
      (by
        intro action hIn
        rw [hOffers] at hIn
        simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
        obtain ⟨branch, hMem, rfl⟩ := hIn
        simpa [hWholeDef, PactType.alphabet] using hGuard branch hMem)
    rw [hDecomp, hOffers, hWholeDef,
      typeFutureOffers_xoffer alphabet elseType branches hGuard]
    -- the default entry carries the default's menu
    have hElseMenu : computeFutureOf whole
        (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
      rw [childState, computeFutureOf_exclusiveOffer_else elseType branches
        whole hWhole hElseFuel hElseDisjoint
        (by rw [hElseAlphabet, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_else alphabet elseType branches)
        elseFragment.initial
        (compileTypeFuel_initial_mem _ elseType (Nat.le_refl _))]
      exact hElse (buildRelationSet_initial elseType _ rfl)
    -- and each branch entry its branch's
    have hBranchMenu : ∀ indexed ∈ branchAutomata.zipIdx,
        ∃ branch ∈ branches,
          computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
            typeFutureOffers branch.2 := by
      intro indexed hIndexed
      have hGetAuto : branchAutomata[indexed.2]? = some indexed.1 := by
        rw [← List.mk_mem_zipIdx_iff_getElem?]
        simpa using hIndexed
      rw [hBranchAutomata, List.getElem?_map, Option.map_eq_some_iff]
        at hGetAuto
      obtain ⟨branch, hGetBranch, hEq⟩ := hGetAuto
      have hMem : branch ∈ branches := List.mem_of_getElem? hGetBranch
      refine ⟨branch, hMem, ?_⟩
      have hShape : indexed.1.2 =
          compileTypeFuel (typeCompilationFuel branch.2) branch.2 := by
        rw [← hEq]
      rw [hShape, childState, computeFutureOf_exclusiveOffer_branch elseType
        branches whole hWhole indexed.2 branch.1 branch.2 hGetBranch
        (hBranchFuel branch hMem) (hBranchDisjoint branch hMem)
        (by rw [hBranchAlphabet branch hMem, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_branch alphabet elseType branches
          indexed.2 branch.1 branch.2 hGetBranch) _
        (compileTypeFuel_initial_mem _ branch.2 (Nat.le_refl _))]
      exact hBranches branch hMem (buildRelationSet_initial branch.2 _ rfl)
    have hBranchMenu' : ∀ branch ∈ branches,
        ∃ indexed ∈ branchAutomata.zipIdx,
          computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
            typeFutureOffers branch.2 := by
      intro branch hMem
      obtain ⟨index, hGetBranch⟩ := List.getElem?_of_mem hMem
      have hGetAuto : branchAutomata[index]? =
          some (branch.1, compileTypeFuel (typeCompilationFuel branch.2)
            branch.2) := by
        rw [hBranchAutomata, List.getElem?_map, hGetBranch]
        rfl
      refine ⟨((branch.1, compileTypeFuel (typeCompilationFuel branch.2)
        branch.2), index), List.mk_mem_zipIdx_iff_getElem?.mpr hGetAuto, ?_⟩
      rw [childState, computeFutureOf_exclusiveOffer_branch elseType branches
        whole hWhole index branch.1 branch.2 hGetBranch
        (hBranchFuel branch hMem) (hBranchDisjoint branch hMem)
        (by rw [hBranchAlphabet branch hMem, hWholeDef]; rfl)
        (stateProductInfo_xoffer_child_branch alphabet elseType branches index
          branch.1 branch.2 hGetBranch) _
        (compileTypeFuel_initial_mem _ branch.2 (Nat.le_refl _))]
      exact hBranches branch hMem (buildRelationSet_initial branch.2 _ rfl)
    ext offer
    rw [mem_foldl_offer_menu, Finset.mem_union, Finset.mem_biUnion,
      typeBranchActions, List.mem_toFinset, List.mem_map]
    simp only [exclusiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro (⟨branch, hMem, rfl⟩ | ⟨entry, hEntry, hIn⟩)
      · exact Or.inr ⟨branch, hMem, Or.inl rfl⟩
      · rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · rw [hElseMenu] at hIn
          exact Or.inl hIn
        · obtain ⟨branch, hMem, hMenu⟩ := hBranchMenu indexed hIndexed
          rw [hMenu] at hIn
          exact Or.inr ⟨branch, hMem, Or.inr hIn⟩
    · rintro (hElseIn | ⟨branch, hMem, rfl | hMenuIn⟩)
      · exact Or.inr ⟨childState 0 elseFragment.initial, Or.inl rfl,
          by rw [hElseMenu]; exact hElseIn⟩
      · exact Or.inl ⟨branch, hMem, rfl⟩
      · obtain ⟨indexed, hIndexed, hMenu⟩ := hBranchMenu' branch hMem
        exact Or.inr ⟨childState (indexed.2 + 1) indexed.1.2.initial,
          Or.inr ⟨indexed, hIndexed, rfl⟩, by rw [hMenu]; exact hMenuIn⟩
  · subst hState
    rw [computeFutureOf_exclusiveOffer_else elseType branches whole hWhole
      hElseFuel hElseDisjoint (by rw [hElseAlphabet, hWholeDef]; rfl)
      (stateProductInfo_xoffer_child_else alphabet elseType branches) q
      (relationMembership_state_mem elseType _ q hChild)]
    exact hElse hChild
  · subst hState
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
    have hDisjoint : branchType.OfferBranchesDisjoint :=
      hBranchDisjoint (action, branchType) hMem
    rw [computeFutureOf_exclusiveOffer_branch elseType branches whole hWhole
      i action branchType hGet (hBranchFuel (action, branchType) hMem)
      hDisjoint (by rw [hBranchAlphabet (action, branchType) hMem, hWholeDef]; rfl)
      (stateProductInfo_xoffer_child_branch alphabet elseType branches i action
        branchType hGet) q
      (relationMembership_state_mem branchType _ q hChild)]
    exact hBranches (action, branchType) hMem hChild

/-! ### Conjunctive-offer automaton helpers

The conjunctive builder has the same five-family edge set and the same
accepting set as the exclusive one, so these mirror the
`buildExclusiveOfferAutomaton` family clause for clause.  The committing
family differs only in its decoration: it is silent with an empty current
offer, and its guard drops the future-resolution condition. -/

/-- A conjunctive offer's tagged-else outgoing edges are exactly the else
fragment's own edges, tagged. -/
theorem conjunctiveOffer_outgoing_else
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildSelectedConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions).edges ∧
      edge.source = childState 0 state) ↔
      ∃ childEdge ∈ elseAutomaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, hChildEdge, hEdgeEq⟩
      have hChildSource := hSource
      rw [← hEdgeEq] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdgeEq.symm⟩
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, _hIndexed, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, _hChildEdge, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childState] at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)))
    · simp [childPendingEdge, childState, hChildSource]

/-- A conjunctive offer's tagged-branch outgoing edges are exactly that
generated child's own edges, tagged. -/
theorem conjunctiveOffer_outgoing_branch
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    (edge ∈ (buildSelectedConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions).edges ∧
      edge.source = childState (i + 1) state) ↔
      ∃ childEdge ∈ automaton.edges,
        childEdge.source = state ∧ edge = childPendingEdge (i + 1) childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, _hChildEdge, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, hChildEdge, hEdgeEq⟩
        have hChildSource := hSource
        rw [← hEdgeEq] at hChildSource
        simp [childPendingEdge, childState] at hChildSource
        rcases hChildSource with ⟨hIndexEq, hSourceEq⟩
        have hIndexedGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem
        have hEntryEq : indexed.1 = (action, automaton) := by
          have hGet : selectedConjunctions[i]? = some indexed.1 := by
            simpa [hIndexEq] using hIndexedGet
          rw [hBranch] at hGet
          exact (Option.some.inj hGet).symm
        have hAutomatonEq : indexed.1.2 = automaton := congrArg Prod.snd hEntryEq
        have hEdgeEq' : edge = childPendingEdge (i + 1) childEdge := by
          simpa [hIndexEq] using hEdgeEq.symm
        exact ⟨childEdge, by simpa [hAutomatonEq] using hChildEdge,
          hSourceEq, hEdgeEq'⟩
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, _hIndexed, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, _hEnvironment, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childState] at hSource
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, _hEnvironment, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childState] at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image]
      refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
      rw [indexedFragmentEdges, mem_foldl_union_iff]
      exact Or.inr ⟨((action, automaton), i),
        List.mk_mem_zipIdx_iff_getElem?.mpr hBranch,
        Finset.mem_image.mpr ⟨childEdge, hChildEdge, rfl⟩⟩
    · simp [childPendingEdge, childState, hChildSource]

/-- Tagged-else acceptance in a conjunctive offer is the else fragment's own. -/
theorem buildSelectedConjunctiveOfferAutomaton_child0_accepting_iff
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (q : TypeAutomatonState) :
    childState 0 q ∈ (buildSelectedConjunctiveOfferAutomaton alphabet branches
        elseAutomaton selectedConjunctions).accepting ↔
      q ∈ elseAutomaton.accepting := by
  classical
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  constructor
  · rintro (⟨q', hq', hEq⟩ | ⟨indexed, -, q', -, hEq⟩)
    · injection hEq with _ hEq'; exact hEq' ▸ hq'
    · exact nomatch hEq
  · intro hq; exact Or.inl ⟨q, hq, rfl⟩

/-- Tagged-branch acceptance in a conjunctive offer is that generated child's
own. -/
theorem buildSelectedConjunctiveOfferAutomaton_branch_accepting_iff
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (q : TypeAutomatonState) :
    childState (i + 1) q ∈ (buildSelectedConjunctiveOfferAutomaton alphabet
        branches elseAutomaton selectedConjunctions).accepting ↔
      q ∈ automaton.accepting := by
  classical
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  constructor
  · rintro (⟨q', hq', hEq⟩ | ⟨indexed, hIndexed, q', hq', hEq⟩)
    · exact nomatch hEq
    · injection hEq with hIdx hQ
      have hIdxEq : indexed.2 = i := by omega
      have hGet := List.mk_mem_zipIdx_iff_getElem?.mp hIndexed
      rw [hIdxEq, hBranch] at hGet
      have hEntry : indexed.1 = (action, automaton) := (Option.some.inj hGet).symm
      rw [hEntry] at hq'
      exact hQ ▸ hq'
  · intro hq
    exact Or.inr ⟨((action, automaton), i),
      List.mk_mem_zipIdx_iff_getElem?.mpr hBranch, q, hq, rfl⟩

/-- The conjunctive offer's fresh root is never accepting. -/
theorem buildSelectedConjunctiveOfferAutomaton_root_not_accepting
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    TypeAutomatonState.root ∉ (buildSelectedConjunctiveOfferAutomaton alphabet
      branches elseAutomaton selectedConjunctions).accepting := by
  classical
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union, childAccepting, Finset.mem_image, childState,
    indexedFragmentAccepting, mem_foldl_union_iff, Finset.notMem_empty, false_or]
  rintro (⟨q, -, hEq⟩ | ⟨indexed, -, q, -, hEq⟩) <;> exact nomatch hEq

/-- The conjunctive offer's root waits at itself, enters the default, or
commits to one generated child. -/
theorem automatonNonClockStep_root_conjunctiveOffer
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    {target : TypeAutomatonState}
    (hStep : AutomatonNonClockStep (buildSelectedConjunctiveOfferAutomaton
      alphabet branches elseAutomaton selectedConjunctions)
      TypeAutomatonState.root target) :
    target = TypeAutomatonState.root ∨
    target = childState 0 elseAutomaton.initial ∨
    ∃ i action automaton, selectedConjunctions[i]? = some (action, automaton) ∧
      target = childState (i + 1) automaton.initial := by
  classical
  obtain ⟨edge, hEdge, hSource, hTarget, -⟩ := hStep
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
  · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
    rw [← hEdgeEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
    · simp at hEmpty
    · simp only [childPendingEdges, Finset.mem_image] at hChild
      rcases hChild with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, hIndexedMem, hRoot⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
      rcases hRoot with ⟨environment, -, hEdgeEq⟩
      refine Or.inr (Or.inr ⟨indexed.2, indexed.1.1, indexed.1.2,
        List.mk_mem_zipIdx_iff_getElem?.mp hIndexedMem, ?_⟩)
      rw [← hTarget, ← hEdgeEq]
  · simp only [Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, -, hEdgeEq⟩
    exact Or.inl (by rw [← hTarget, ← hEdgeEq])
  · simp only [Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, -, hEdgeEq⟩
    exact Or.inr (Or.inl (by rw [← hTarget, ← hEdgeEq]))

/-- The empty environment always realizes the conjunctive offer's else edge. -/
theorem automatonNonClockStep_root_conjunctiveOffer_else
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hEnvMem : TypeEnvironment.empty ∈ alphabet.localEnvironments)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    AutomatonNonClockStep (buildSelectedConjunctiveOfferAutomaton alphabet
        branches elseAutomaton selectedConjunctions) TypeAutomatonState.root
      (childState 0 elseAutomaton.initial) := by
  classical
  set edge : PendingAutomatonEdge :=
    { source := TypeAutomatonState.root, environment := TypeEnvironment.empty,
      label := .visible TypeLabel.silent,
      current := typeBranchActions branches,
      future := FutureSpec.at (childState 0 elseAutomaton.initial)
        (typeBranchActions branches),
      target := childState 0 elseAutomaton.initial } with hEdgeDef
  refine ⟨edge, ?_, rfl, rfl, ?_⟩
  · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    exact Or.inr ⟨TypeEnvironment.empty,
      ⟨hEnvMem, rfl, by simp [TypeEnvironment.empty],
        by simp [TypeEnvironment.empty], hBranchActions⟩, hEdgeDef.symm⟩
  · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
      TypeLabel.silent]

/-- The environment needing exactly `action` realizes that generated child's
commit edge. -/
theorem automatonNonClockStep_root_conjunctiveOffer_branch
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (i : Nat) (action : BareMessage) (automaton : AutomatonFragment)
    (hBranch : selectedConjunctions[i]? = some (action, automaton))
    (hEnvMem : ({ immediate := {typeNeed action}, future := ∅, clock := false } :
      TypeEnvironment) ∈ alphabet.localEnvironments)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    AutomatonNonClockStep (buildSelectedConjunctiveOfferAutomaton alphabet
        branches elseAutomaton selectedConjunctions) TypeAutomatonState.root
      (childState (i + 1) automaton.initial) := by
  classical
  set env : TypeEnvironment :=
    { immediate := {typeNeed action}, future := ∅, clock := false } with hEnvDef
  set edge : PendingAutomatonEdge :=
    { source := TypeAutomatonState.root, environment := env,
      label := .visible TypeLabel.silent,
      current := ∅,
      future := FutureSpec.at (childState (i + 1) automaton.initial) ∅,
      target := childState (i + 1) automaton.initial } with hEdgeDef
  refine ⟨edge, ?_, rfl, rfl, ?_⟩
  · simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union]
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [mem_foldl_union_iff]
    refine Or.inr ⟨((action, automaton), i),
      List.mk_mem_zipIdx_iff_getElem?.mpr hBranch, ?_⟩
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨env, ⟨hEnvMem, by simp [hEnvDef], hBranchActions⟩, hEdgeDef.symm⟩
  · simp [hEdgeDef, AutomatonConstructionLabel.semantic, TypeLabel.isTock,
      TypeLabel.silent]

/-- Root reachability for a conjunctive offer: the wait edges self-loop, the
root is never accepting, and every escape lands at the default entry or a
generated child's entry — each realized by a witness environment. -/
theorem automatonSameCycleReachesAccepting_root_conjunctiveOffer
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hEnvMem : TypeEnvironment.empty ∈ alphabet.localEnvironments)
    (hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions)
    (hFiringEnv : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      selectedConjunctions[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } :
        TypeEnvironment) ∈ alphabet.localEnvironments) :
    AutomatonSameCycleReachesAccepting (buildSelectedConjunctiveOfferAutomaton
        alphabet branches elseAutomaton selectedConjunctions)
        TypeAutomatonState.root ↔
      AutomatonSameCycleReachesAccepting (buildSelectedConjunctiveOfferAutomaton
        alphabet branches elseAutomaton selectedConjunctions)
        (childState 0 elseAutomaton.initial) ∨
      ∃ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
        selectedConjunctions[i]? = some (action, automaton) ∧
        AutomatonSameCycleReachesAccepting (buildSelectedConjunctiveOfferAutomaton
          alphabet branches elseAutomaton selectedConjunctions)
          (childState (i + 1) automaton.initial) := by
  classical
  set offer := buildSelectedConjunctiveOfferAutomaton alphabet branches
    elseAutomaton selectedConjunctions with hOfferDef
  constructor
  · rintro ⟨finalState, hReach, hFinal⟩
    have hAux : ∀ reached,
        Relation.ReflTransGen (AutomatonNonClockStep offer)
          TypeAutomatonState.root reached →
        reached = TypeAutomatonState.root ∨
        Relation.ReflTransGen (AutomatonNonClockStep offer)
          (childState 0 elseAutomaton.initial) reached ∨
        ∃ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
          selectedConjunctions[i]? = some (action, automaton) ∧
          Relation.ReflTransGen (AutomatonNonClockStep offer)
            (childState (i + 1) automaton.initial) reached := by
      intro reached hR
      induction hR with
      | refl => exact Or.inl rfl
      | tail _ hStep ih =>
          rcases ih with hRoot | hElse | ⟨i, action, automaton, hGet, hPath⟩
          · rw [hRoot] at hStep
            rcases automatonNonClockStep_root_conjunctiveOffer alphabet branches
                elseAutomaton selectedConjunctions hStep with
              h | h | ⟨i, action, automaton, hGet, h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl (by rw [h]))
            · exact Or.inr (Or.inr ⟨i, action, automaton, hGet, by rw [h]⟩)
          · exact Or.inr (Or.inl (hElse.tail hStep))
          · exact Or.inr (Or.inr ⟨i, action, automaton, hGet, hPath.tail hStep⟩)
    rcases hAux finalState hReach with hRoot | hElse | ⟨i, action, automaton, hGet, hPath⟩
    · exfalso
      rw [hRoot] at hFinal
      exact absurd hFinal (buildSelectedConjunctiveOfferAutomaton_root_not_accepting
        alphabet branches elseAutomaton selectedConjunctions)
    · exact Or.inl ⟨finalState, hElse, hFinal⟩
    · exact Or.inr ⟨i, action, automaton, hGet, finalState, hPath, hFinal⟩
  · rintro (⟨finalState, hReach, hFinal⟩ |
      ⟨i, action, automaton, hGet, finalState, hReach, hFinal⟩)
    · exact ⟨finalState, Relation.ReflTransGen.head
        (automatonNonClockStep_root_conjunctiveOffer_else alphabet branches
          elseAutomaton selectedConjunctions hEnvMem hBranchActions) hReach, hFinal⟩
    · exact ⟨finalState, Relation.ReflTransGen.head
        (automatonNonClockStep_root_conjunctiveOffer_branch alphabet branches
          elseAutomaton selectedConjunctions i action automaton hGet
          (hFiringEnv i action automaton hGet) hBranchActions) hReach, hFinal⟩

/-! ### Same-cycle completion at the compound fragments

`helper_h14_same_cycle_completion`'s proved constructor cases, restated with
the children's completion statements as hypotheses so that the simultaneous
induction supplies them. -/

lemma sameCycleCompletionAgrees_choice
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.choice alphabet left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.choice alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.choice alphabet left right))
        (.choice alphabet left right) =
        buildChoiceAutomaton alphabet leftAuto rightAuto
          TypeLabel.silent TypeLabel.silent := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildChoiceAutomaton alphabet
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        TypeLabel.silent TypeLabel.silent =
      buildChoiceAutomaton alphabet leftAuto rightAuto
        TypeLabel.silent TypeLabel.silent
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  rw [hWhole]
  have hEmptyLocal :
      TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hShape := helper_h12_binaryChoice_shape (.choice alphabet left right) left right
    rfl hFuelEq hRelated
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      TypeLabel.silent TypeLabel.silent)
    leftAuto 0
    (automatonNonClockStep_binaryChoice_child0 alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
    (buildChoiceAutomaton_child0_accepting_iff alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      TypeLabel.silent TypeLabel.silent)
    rightAuto 1
    (automatonNonClockStep_binaryChoice_child1 alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
    (buildChoiceAutomaton_child1_accepting_iff alphabet leftAuto
      rightAuto
      TypeLabel.silent TypeLabel.silent)
  rcases hShape with ⟨hResidualEq, hStateEq⟩ |
    ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    rw [typeSameCycleCanComplete_choice_iff,
      automatonSameCycleReachesAccepting_root_binaryChoice alphabet
        leftAuto rightAuto _ _
        hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.silent])
        (by simp [TypeLabel.isTock, TypeLabel.silent])]
    have hIHLeft := hLeftComplete
      (buildRelationSet_initial left (compileType left))
    have hIHRight := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHLeft hIHRight
    rw [← hLeftAutoDef] at hIHLeft
    rw [← hRightAutoDef] at hIHRight
    rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
  · subst hStateEq
    exact (hTag0 q).trans (hLeftComplete hLeftRelated)
  · subst hStateEq
    exact (hTag1 q).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_fairChoice
    (alphabet : PactTypeAlphabet) (bid : BranchId) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.fairChoice alphabet bid left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.fairChoice alphabet bid left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.fairChoice alphabet bid left right))
        (.fairChoice alphabet bid left right) =
        buildChoiceAutomaton alphabet leftAuto rightAuto
          (TypeLabel.fair bid true) (TypeLabel.fair bid false) := by
    rw [hFuelEq]
    rw [compileTypeFuel.eq_def]
    show buildChoiceAutomaton alphabet
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
      buildChoiceAutomaton alphabet leftAuto rightAuto
        (TypeLabel.fair bid true) (TypeLabel.fair bid false)
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  rw [hWhole]
  have hEmptyLocal :
      TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hShape := helper_h12_binaryChoice_shape (.fairChoice alphabet bid left right)
    left right rfl hFuelEq hRelated
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    leftAuto 0
    (automatonNonClockStep_binaryChoice_child0 alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    (buildChoiceAutomaton_child0_accepting_iff alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildChoiceAutomaton alphabet leftAuto rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    rightAuto 1
    (automatonNonClockStep_binaryChoice_child1 alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
    (buildChoiceAutomaton_child1_accepting_iff alphabet leftAuto
      rightAuto
      (TypeLabel.fair bid true) (TypeLabel.fair bid false))
  rcases hShape with ⟨hResidualEq, hStateEq⟩ |
    ⟨q, hStateEq, hLeftRelated⟩ | ⟨q, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    rw [typeSameCycleCanComplete_fairChoice_iff,
      automatonSameCycleReachesAccepting_root_binaryChoice alphabet
        leftAuto rightAuto _ _
        hEmptyLocal (by simp [TypeLabel.isTock, TypeLabel.fair])
        (by simp [TypeLabel.isTock, TypeLabel.fair])]
    have hIHLeft := hLeftComplete
      (buildRelationSet_initial left (compileType left))
    have hIHRight := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHLeft hIHRight
    rw [← hLeftAutoDef] at hIHLeft
    rw [← hRightAutoDef] at hIHRight
    rw [hTag0 leftAuto.initial, hTag1 rightAuto.initial, hIHLeft, hIHRight]
  · subst hStateEq
    exact (hTag0 q).trans (hLeftComplete hLeftRelated)
  · subst hStateEq
    exact (hTag1 q).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_seq
    (alphabet : PactTypeAlphabet) (left right : PactType)
    (hLeftComplete : SameCycleCompletionAgrees left)
    (hRightComplete : SameCycleCompletionAgrees right) :
    SameCycleCompletionAgrees (.seq alphabet left right) := by
  intro residual state hRelated
  have hFuelEq : typeCompilationFuel (.seq alphabet left right) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  set leftAuto := compileTypeFuel (typeCompilationFuel left) left
    with hLeftAutoDef
  set rightAuto := compileTypeFuel (typeCompilationFuel right) right
    with hRightAutoDef
  have hWhole :
      compileTypeFuel (typeCompilationFuel (.seq alphabet left right))
        (.seq alphabet left right) =
        buildSequenceAutomaton leftAuto rightAuto := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildSequenceAutomaton
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel (max (typeCompilationFuel left) (typeCompilationFuel right)) right) =
      buildSequenceAutomaton leftAuto rightAuto
    rw [hLeftAutoDef, hRightAutoDef,
      compileTypeFuel_eq_of_sufficient left (le_max_left _ _) le_rfl,
      compileTypeFuel_eq_of_sufficient right (le_max_right _ _) le_rfl]
  have hTag1 := automatonSameCycleReachesAccepting_of_child_tag
    (buildSequenceAutomaton leftAuto rightAuto) rightAuto 1
    (automatonNonClockStep_sequence_child1 leftAuto rightAuto)
    (buildSequenceAutomaton_child1_accepting_iff leftAuto rightAuto)
  rw [hWhole]
  rcases helper_h12_seq_shape alphabet left right hRelated with
    ⟨ρ, q1, hResidualEq, hStateEq, hLeftRelated, hSurvives⟩ |
    ⟨q2, hStateEq, hRightRelated⟩
  · subst hResidualEq; subst hStateEq
    have hIHLeft := hLeftComplete hLeftRelated
    have hIHRightInit := hRightComplete
      (buildRelationSet_initial right (compileType right))
    simp only [compileType] at hIHRightInit
    rw [← hRightAutoDef] at hIHRightInit
    rw [typeSameCycleCanComplete_seq_iff]
    constructor
    · rintro ⟨finalState, hReach, hFinal⟩
      rcases automatonSameCycleReaches_sequence_child0_cases
          leftAuto rightAuto q1 finalState hReach with
        ⟨q', hEq, -⟩ | ⟨q', hLeftReach, hAccepting, hRest⟩
      · exfalso
        rw [hEq] at hFinal
        simp [buildSequenceAutomaton, finishAutomatonFragment,
          childAccepting, childState] at hFinal
      · exact ⟨hIHLeft.mp ⟨q', hLeftReach, hAccepting⟩,
          hIHRightInit.mp
            ((hTag1 rightAuto.initial).mp ⟨finalState, hRest, hFinal⟩)⟩
    · rintro ⟨hLeftDone, hRightDone⟩
      obtain ⟨q', hLeftReach, hAccepting⟩ := hIHLeft.mpr hLeftDone
      obtain ⟨q2', hRightReach, hRightFinal⟩ :=
        (hTag1 rightAuto.initial).mpr (hIHRightInit.mpr hRightDone)
      refine ⟨q2', Relation.ReflTransGen.trans ?_ hRightReach, hRightFinal⟩
      have hNotDeleted : q1 ∉ sequenceDeleted leftAuto := by
        simp only [sequenceDeleted, Finset.mem_sdiff, Finset.mem_singleton,
          not_and, not_not]
        intro hAcceptingQ1
        rcases hSurvives with hNot | hInit
        · exact absurd hAcceptingQ1
            (by simpa only [compileType, ← hLeftAutoDef] using hNot)
        · simpa only [compileType, ← hLeftAutoDef] using hInit
      rcases automatonSameCycleReaches_sequence_lift_left_of_not_deleted
          leftAuto rightAuto q1 q' hLeftReach hAccepting hNotDeleted with
        hPath | hEq
      · exact hPath
      · -- `q1` already accepts, so it is `left`'s entry and its own idle
        -- step redirects into the right entry.
        subst hEq
        have hEntry : q1 = leftAuto.initial := by
          rcases hSurvives with hNot | hInit
          · exact absurd hAccepting (by
              simpa only [compileType, ← hLeftAutoDef] using hNot)
          · simpa only [compileType, ← hLeftAutoDef] using hInit
        rw [hEntry] at hAccepting ⊢
        obtain ⟨target, hStep, hTargetAccepting⟩ :=
          compileTypeFuel_nonClockStep_of_initial_accepting
            (typeCompilationFuel left) left hAccepting
        refine Relation.ReflTransGen.single ?_
        refine (automatonNonClockStep_sequence_child0 leftAuto
          rightAuto leftAuto.initial _).mpr ⟨target, hStep, ?_⟩
        rw [sequenceRedirect, if_pos hTargetAccepting]
  · subst hStateEq
    exact (hTag1 q2).trans (hRightComplete hRightRelated)

lemma sameCycleCompletionAgrees_xoffer
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseComplete : SameCycleCompletionAgrees elseType)
    (hBranchComplete : ∀ entry ∈ branches, SameCycleCompletionAgrees entry.2) :
    SameCycleCompletionAgrees (.xoffer alphabet elseType branches) := by
  intro residual state hRelated
  have hEmptyLocal : TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hFuelEq : typeCompilationFuel (.xoffer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  set elseAuto := compileTypeFuel (typeCompilationFuel elseType) elseType
    with hElseAutoDef
  set branchAutos := branches.map (fun branch =>
    (branch.1, compileTypeFuel (typeCompilationFuel branch.2) branch.2))
    with hBranchAutosDef
  have hWhole :
      compileTypeFuel
        (typeCompilationFuel (.xoffer alphabet elseType branches))
        (.xoffer alphabet elseType branches) =
        buildExclusiveOfferAutomaton alphabet branches elseAuto branchAutos := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildExclusiveOfferAutomaton alphabet branches
        (compileTypeFuel (max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches)) elseType)
        (branches.map fun branch => (branch.1, compileTypeFuel (max (typeCompilationFuel elseType) (typeBranchCompilationFuel branches)) branch.2)) = _
    rw [hElseAutoDef, hBranchAutosDef,
      compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl]
    congr 1
    apply List.map_congr_left
    intro branch hBranch
    congr 1
    exact compileTypeFuel_eq_of_sufficient branch.2
      (le_trans (typeCompilationFuel_le_typeBranchCompilationFuel branches branch hBranch)
        (le_max_right _ _)) le_rfl
  have hMapGet : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) →
      ∃ branchType, branches[i]? = some (action, branchType) ∧
        automaton = compileTypeFuel (typeCompilationFuel branchType) branchType := by
    intro i action automaton hGet
    rw [hBranchAutosDef, List.getElem?_map] at hGet
    cases hb : branches[i]? with
    | none => rw [hb] at hGet; exact absurd hGet (by simp)
    | some b =>
        rw [hb] at hGet
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hGet
        exact ⟨b.2, by rw [← hGet.1], hGet.2.symm⟩
  have hMapGetRev : ∀ (i : Nat) (branch : BareMessage × PactType),
      branches[i]? = some branch →
      branchAutos[i]? = some (branch.1,
        compileTypeFuel (typeCompilationFuel branch.2) branch.2) := by
    intro i branch hGet
    rw [hBranchAutosDef, List.getElem?_map, hGet]
    rfl
  have hFiringEnv : (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) →
      ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } : TypeEnvironment)
        ∈ alphabet.localEnvironments := by
    intro hBranchActions i action automaton hGet
    obtain ⟨branchType, hBranchGet, -⟩ := hMapGet i action automaton hGet
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
    have hAction : action ∈ alphabet.actions := hBranchActions _ hMem
    simpa [typeNeed] using
      firing_environment_mem_localEnvironmentsFor alphabet action.1 action.2
        (by simpa using hAction)
  rw [hWhole]
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildExclusiveOfferAutomaton alphabet branches elseAuto branchAutos)
    elseAuto 0
    (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ 0
      (exclusiveOffer_outgoing_else alphabet branches elseAuto branchAutos)
      q target)
    (buildExclusiveOfferAutomaton_child0_accepting_iff alphabet branches
      elseAuto branchAutos)
  have hTagBranch : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      branchAutos[i]? = some (action, automaton) → ∀ q,
      (AutomatonSameCycleReachesAccepting (buildExclusiveOfferAutomaton alphabet
        branches elseAuto branchAutos) (childState (i + 1) q) ↔
        AutomatonSameCycleReachesAccepting automaton q) := by
    intro i action automaton hGet
    exact automatonSameCycleReachesAccepting_of_child_tag _ automaton (i + 1)
      (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ (i + 1)
        (exclusiveOffer_outgoing_branch alphabet branches elseAuto branchAutos
          i action automaton hGet) q target)
      (buildExclusiveOfferAutomaton_branch_accepting_iff alphabet branches
        elseAuto branchAutos i action automaton hGet)
  -- Every root edge family the offer builder emits is gated on the
  -- branch heads being declared, so one root step witnesses the gate.
  have hRootStepActions : ∀ {target : TypeAutomatonState},
      AutomatonNonClockStep (buildExclusiveOfferAutomaton alphabet
        branches elseAuto branchAutos) TypeAutomatonState.root target →
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions := by
    intro target hStep
    obtain ⟨edge, hEdge, hSource, -, -⟩ := hStep
    simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, -, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hBranch
      rcases hBranch with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, ⟨-, -, -, hActions⟩, -⟩
        exact hActions
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, ⟨-, -, -, hActions⟩, -⟩
      exact hActions
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
  rcases helper_h12_xoffer_shape alphabet elseType branches hRelated with
    ⟨hResidualEq, hStateEq⟩ | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, action, branchType, q, hGet, hStateEq, hBranchRelated⟩
  · subst hResidualEq; subst hStateEq
    by_cases hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    · rw [typeSameCycleCanComplete_xoffer_iff alphabet elseType branches hBranchActions,
        automatonSameCycleReachesAccepting_root_exclusiveOffer alphabet branches
          elseAuto branchAutos hEmptyLocal hBranchActions
          (hFiringEnv hBranchActions)]
      have hIHElse := hElseComplete
        (buildRelationSet_initial elseType (compileType elseType))
      simp only [compileType] at hIHElse
      rw [← hElseAutoDef] at hIHElse
      rw [hTag0 elseAuto.initial, hIHElse]
      constructor
      · rintro (hElse | ⟨i, action, automaton, hGet, hReach⟩)
        · exact Or.inl hElse
        · obtain ⟨branchType, hBranchGet, hAutoEq⟩ := hMapGet i action automaton hGet
          have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hBranchGet
          subst hAutoEq
          refine Or.inr ⟨(action, branchType), hMem, ?_⟩
          have hIHBranch := hBranchComplete _ hMem
            (buildRelationSet_initial branchType (compileType branchType))
          simp only [compileType] at hIHBranch
          exact hIHBranch.mp ((hTagBranch i action _ hGet _).mp hReach)
      · rintro (hElse | ⟨entry, hMem, hEntry⟩)
        · exact Or.inl hElse
        · obtain ⟨i, hBranchGet⟩ := List.mem_iff_getElem?.mp hMem
          refine Or.inr ⟨i, entry.1,
            compileTypeFuel (typeCompilationFuel entry.2) entry.2,
            hMapGetRev i entry hBranchGet, ?_⟩
          have hIHBranch := hBranchComplete _ hMem
            (buildRelationSet_initial entry.2 (compileType entry.2))
          simp only [compileType] at hIHBranch
          exact (hTagBranch i entry.1 _ (hMapGetRev i entry hBranchGet) _).mpr
            (hIHBranch.mpr hEntry)
    -- Undeclared branch head: the builders emit no root edge and the
    -- `xoffer_*` rules do not fire, so both sides are unreachable.
    · constructor
      · rintro ⟨finalState, hReach, hFinal⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReach with rfl | ⟨mid, hStep, -⟩
        · exact buildExclusiveOfferAutomaton_root_not_accepting alphabet
            branches elseAuto branchAutos hFinal
        · exact hBranchActions (hRootStepActions hStep)
      · rintro ⟨targetAlphabet, hReaches⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReaches with h |
          ⟨mid, ⟨env, label, hTrans, -⟩, -⟩
        · exact nomatch h
        · refine hBranchActions ?_
          cases hTrans with
          | xoffer_branch _ _ _ _ _ _ _ hActions => exact hActions
          | xoffer_else _ _ _ _ _ hActions => exact hActions
          | xoffer_wait _ _ _ _ _ hActions => exact hActions
  · subst hStateEq
    exact (hTag0 q).trans (hElseComplete hElseRelated)
  · subst hStateEq
    have hMem : (action, branchType) ∈ branches := List.mem_of_getElem? hGet
    exact ((hTagBranch i action _
      (hMapGetRev i (action, branchType) hGet) q).trans
      (hBranchComplete _ hMem hBranchRelated))

lemma sameCycleCompletionAgrees_offer
    (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hElseComplete : SameCycleCompletionAgrees elseType)
    (hSelectedComplete : ∀ selected ∈ branches,
      SameCycleCompletionAgrees
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    SameCycleCompletionAgrees (.offer alphabet elseType branches) := by
  intro residual state hRelated
  have hEmptyLocal : TypeEnvironment.empty ∈ alphabet.localEnvironments := by
    simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
    exact Or.inr ⟨∅, Finset.empty_subset _, ∅, Finset.empty_subset _, rfl⟩
  have hFuelEq : typeCompilationFuel (.offer alphabet elseType branches) =
      max (typeCompilationFuel elseType) (conjunctiveCompilationFuel branches) + 1 := by
    simp only [typeCompilationFuel]; omega
  set elseAuto := compileTypeFuel (typeCompilationFuel elseType) elseType
    with hElseAutoDef
  set conjAutos := branches.map (fun selected =>
    (selected.1,
      compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches))
        (parallelTypeBranchesSelecting alphabet selected branches)))
    with hConjAutosDef
  have hWhole :
      compileTypeFuel
        (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
        buildSelectedConjunctiveOfferAutomaton alphabet branches elseAuto
          conjAutos := by
    rw [hFuelEq, compileTypeFuel.eq_def]
    show buildSelectedConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches)) elseType)
        (branches.map fun selected => (selected.1,
          compileTypeFuel (max (typeCompilationFuel elseType)
            (conjunctiveCompilationFuel branches))
            (parallelTypeBranchesSelecting alphabet selected branches))) = _
    rw [hElseAutoDef, hConjAutosDef,
      compileTypeFuel_eq_of_sufficient elseType (le_max_left _ _) le_rfl]
    congr 1
    apply List.map_congr_left
    intro selected hSelectedMem
    congr 1
    refine compileTypeFuel_eq_of_sufficient
      (parallelTypeBranchesSelecting alphabet selected branches) ?_ le_rfl
    show typeCompilationFuel
      (parallelTypeBranchesSelecting alphabet selected branches) ≤ _
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    exact le_max_right _ _
  have hMapGet : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) →
      ∃ selected, branches[i]? = some selected ∧ selected.1 = action ∧
        automaton = compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches) := by
    intro i action automaton hGet
    rw [hConjAutosDef, List.getElem?_map] at hGet
    cases hb : branches[i]? with
    | none => rw [hb] at hGet; exact absurd hGet (by simp)
    | some b =>
        rw [hb] at hGet
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hGet
        exact ⟨b, rfl, hGet.1, hGet.2.symm⟩
  have hMapGetRev : ∀ (i : Nat) (selected : BareMessage × PactType),
      branches[i]? = some selected →
      conjAutos[i]? = some (selected.1,
        compileTypeFuel
          (typeCompilationFuel
            (parallelTypeBranchesSelecting alphabet selected branches))
          (parallelTypeBranchesSelecting alphabet selected branches)) := by
    intro i selected hGet
    rw [hConjAutosDef, List.getElem?_map, hGet]
    rfl
  have hFiringEnv : (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) →
      ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) →
      ({ immediate := {typeNeed action}, future := ∅, clock := false } : TypeEnvironment)
        ∈ alphabet.localEnvironments := by
    intro hBranchActions i action automaton hGet
    obtain ⟨selected, hSelGet, hActionEq, -⟩ := hMapGet i action automaton hGet
    have hMem : selected ∈ branches := List.mem_of_getElem? hSelGet
    have hAction : action ∈ alphabet.actions := hActionEq ▸ hBranchActions _ hMem
    simpa [typeNeed] using
      firing_environment_mem_localEnvironmentsFor alphabet action.1 action.2
        (by simpa using hAction)
  rw [hWhole]
  have hTag0 := automatonSameCycleReachesAccepting_of_child_tag
    (buildSelectedConjunctiveOfferAutomaton alphabet branches elseAuto conjAutos)
    elseAuto 0
    (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ 0
      (conjunctiveOffer_outgoing_else alphabet branches elseAuto conjAutos)
      q target)
    (buildSelectedConjunctiveOfferAutomaton_child0_accepting_iff alphabet branches
      elseAuto conjAutos)
  have hTagBranch : ∀ (i : Nat) (action : BareMessage) (automaton : AutomatonFragment),
      conjAutos[i]? = some (action, automaton) → ∀ q,
      (AutomatonSameCycleReachesAccepting (buildSelectedConjunctiveOfferAutomaton
        alphabet branches elseAuto conjAutos) (childState (i + 1) q) ↔
        AutomatonSameCycleReachesAccepting automaton q) := by
    intro i action automaton hGet
    exact automatonSameCycleReachesAccepting_of_child_tag _ automaton (i + 1)
      (fun q target => automatonNonClockStep_of_outgoing_childPendingEdge _ _ (i + 1)
        (conjunctiveOffer_outgoing_branch alphabet branches elseAuto conjAutos
          i action automaton hGet) q target)
      (buildSelectedConjunctiveOfferAutomaton_branch_accepting_iff alphabet branches
        elseAuto conjAutos i action automaton hGet)
  -- Every root edge family the conjunctive builder emits is gated on the branch
  -- heads being declared, so one root step witnesses the gate.
  have hRootStepActions : ∀ {target : TypeAutomatonState},
      AutomatonNonClockStep (buildSelectedConjunctiveOfferAutomaton alphabet
        branches elseAuto conjAutos) TypeAutomatonState.root target →
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions := by
    intro target hStep
    obtain ⟨edge, hEdge, hSource, -, -⟩ := hStep
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
    rcases hEdge with ((((hElse | hIndexed) | hEnabled) | hWait) | hResolved)
    · rcases hElse with ⟨childEdge, -, hEdgeEq⟩
      rw [← hEdgeEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hChild⟩
      · simp at hEmpty
      · simp only [childPendingEdges, Finset.mem_image] at hChild
        rcases hChild with ⟨childEdge, -, hEdgeEq⟩
        rw [← hEdgeEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, -, hRoot⟩
      · simp at hEmpty
      · simp only [Finset.mem_image, Finset.mem_filter] at hRoot
        rcases hRoot with ⟨environment, ⟨-, -, hActions⟩, -⟩
        exact hActions
    · simp only [Finset.mem_filter] at hWait
      rcases hWait with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
    · simp only [Finset.mem_filter] at hResolved
      rcases hResolved with ⟨environment, ⟨-, -, -, -, hActions⟩, -⟩
      exact hActions
  rcases relationMembership_offer_cases alphabet elseType branches hRelated with
    hRoot | ⟨q, hStateEq, hElseRelated⟩ |
    ⟨i, selected, q, hGet, hStateEq, hSelectedRelated⟩
  · injection hRoot with hResidualEq hStateEq
    subst hResidualEq; subst hStateEq
    by_cases hBranchActions : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    · rw [typeSameCycleCanComplete_offer_iff alphabet elseType branches hBranchActions,
        automatonSameCycleReachesAccepting_root_conjunctiveOffer alphabet branches
          elseAuto conjAutos hEmptyLocal hBranchActions
          (hFiringEnv hBranchActions)]
      have hIHElse := hElseComplete
        (buildRelationSet_initial elseType (compileType elseType))
      simp only [compileType] at hIHElse
      rw [← hElseAutoDef] at hIHElse
      rw [hTag0 elseAuto.initial, hIHElse]
      constructor
      · rintro (hElse | ⟨i, action, automaton, hGet, hReach⟩)
        · exact Or.inl hElse
        · obtain ⟨selected, hSelGet, -, hAutoEq⟩ := hMapGet i action automaton hGet
          have hMem : selected ∈ branches := List.mem_of_getElem? hSelGet
          subst hAutoEq
          refine Or.inr ⟨selected, hMem, ?_⟩
          have hIHSel := hSelectedComplete selected hMem
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting alphabet selected branches)
              (compileType
                (parallelTypeBranchesSelecting alphabet selected branches)))
          simp only [compileType] at hIHSel
          exact hIHSel.mp ((hTagBranch i action _ hGet _).mp hReach)
      · rintro (hElse | ⟨selected, hMem, hEntry⟩)
        · exact Or.inl hElse
        · obtain ⟨i, hSelGet⟩ := List.mem_iff_getElem?.mp hMem
          refine Or.inr ⟨i, selected.1,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches))
              (parallelTypeBranchesSelecting alphabet selected branches),
            hMapGetRev i selected hSelGet, ?_⟩
          have hIHSel := hSelectedComplete selected hMem
            (buildRelationSet_initial
              (parallelTypeBranchesSelecting alphabet selected branches)
              (compileType
                (parallelTypeBranchesSelecting alphabet selected branches)))
          simp only [compileType] at hIHSel
          exact (hTagBranch i selected.1 _ (hMapGetRev i selected hSelGet) _).mpr
            (hIHSel.mpr hEntry)
    -- Undeclared branch head: the builders emit no root edge and the `offer_*`
    -- rules do not fire, so both sides are unreachable.
    · constructor
      · rintro ⟨finalState, hReach, hFinal⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReach with rfl | ⟨mid, hStep, -⟩
        · exact buildSelectedConjunctiveOfferAutomaton_root_not_accepting alphabet
            branches elseAuto conjAutos hFinal
        · exact hBranchActions (hRootStepActions hStep)
      · rintro ⟨targetAlphabet, hReaches⟩
        exfalso
        rcases Relation.ReflTransGen.cases_head hReaches with h |
          ⟨mid, ⟨env, label, hTrans, -⟩, -⟩
        · exact nomatch h
        · refine hBranchActions ?_
          cases hTrans with
          | offer_some _ _ _ _ _ _ hActions => exact hActions
          | offer_else _ _ _ _ _ hActions => exact hActions
          | offer_wait _ _ _ _ _ hActions => exact hActions
  · subst hStateEq
    exact (hTag0 q).trans (hElseComplete hElseRelated)
  · subst hStateEq
    have hMem : selected ∈ branches := List.mem_of_getElem? hGet
    exact ((hTagBranch i selected.1 _ (hMapGetRev i selected hGet) q).trans
      (hSelectedComplete selected hMem hSelectedRelated))

/-- The three helpers, proved together by induction on `typeCompilationFuel`. -/
theorem correspondence_simultaneous :
    ∀ (bound : List String) (processType : PactType),
      TypeWellFormedIn bound processType →
      CurrentOfferCorrespondence processType ∧
        SameCycleCompletionAgrees processType ∧
        FutureOffersAgree processType := by
  intro bound processType
  induction hFuel : typeCompilationFuel processType
      using Nat.strong_induction_on generalizing bound processType with
  | _ n ih =>
    intro hWF
    cases processType with
    | skip alphabet =>
        exact ⟨currentOfferCorrespondence_skip alphabet,
          sameCycleCompletionAgrees_skip alphabet,
          futureOffersAgree_skip alphabet⟩
    | var alphabet name =>
        exact ⟨currentOfferCorrespondence_var alphabet name,
          sameCycleCompletionAgrees_var alphabet name,
          futureOffersAgree_var alphabet name⟩
    | message alphabet msg dir =>
        exact ⟨currentOfferCorrespondence_message alphabet msg dir,
          sameCycleCompletionAgrees_message alphabet msg dir,
          futureOffersAgree_message alphabet msg dir⟩
    | tock alphabet =>
        exact ⟨currentOfferCorrespondence_tock alphabet,
          sameCycleCompletionAgrees_tock alphabet,
          futureOffersAgree_tock alphabet⟩
    | progress alphabet pid =>
        exact ⟨currentOfferCorrespondence_progress alphabet pid,
          sameCycleCompletionAgrees_progress alphabet pid,
          futureOffersAgree_progress alphabet pid⟩
    | choice alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_choice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_choice alphabet left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_choice alphabet left right hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_choice alphabet left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2.2 hRight.2.2
    | fairChoice alphabet bid left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_fairChoice hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_fairChoice alphabet bid left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_fairChoice alphabet bid left right
            hWF.1
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.2.1]; rfl)
            hLeft.1 hRight.1
        · exact futureOffersAgree_fairChoice alphabet bid left right
            (offerBranchesDisjoint_of_ownership left hLeftWF.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            hLeft.2.2 hRight.2.2
    | seq alphabet left right =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_seq hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, sameCycleCompletionAgrees_seq alphabet left right hLeft.2.1 hRight.2.1, ?_⟩
        · exact currentOfferCorrespondence_seq alphabet left right
            (offerBranchesDisjoint_of_ownership right
              hRightWF.2.2.2.2.2.2.2.2.2.1 hRightWF.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.1
              hRightWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.2.1)
            (fun hRel =>
              relationMembership_alphabetWellFormed
                committedOfferAlphabetWellFormed_holds committedOfferScoping_holds
                left _ _ hLeftWF.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.1
                hLeftWF.2.2.2.2.2.1
                (offerBranchesDisjoint_of_ownership left
                  hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
                  hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
                hRel)
            hLeft.1 hRight.1
        · sorry -- menu equation, `.seq`
    | par alphabet left right interface =>
        obtain ⟨hLeftWF, hRightWF⟩ := typeWellFormedIn_par hWF
        have hLeftFuel : typeCompilationFuel left < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hRightFuel : typeCompilationFuel right < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hLeftResignFuel :
            typeCompilationFuel (left.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hLeftFuel
        have hRightResignFuel :
            typeCompilationFuel (right.reannotate alphabet) < n := by
          rw [typeCompilationFuel_reannotate]; exact hRightFuel
        have hLeft := ih _ hLeftFuel bound left rfl hLeftWF
        have hRight := ih _ hRightFuel bound right rfl hRightWF
        refine ⟨?_, ?_, ?_⟩
        · sorry -- current-offer correspondence, `.par`
        · sorry -- same-cycle completion, `.par`
        · sorry -- menu equation, `.par`
    | recur alphabet name body =>
        have hBodyWF := typeWellFormedIn_recur hWF
        have hBodyFuel : typeCompilationFuel body < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBody := ih _ hBodyFuel (name :: bound) body rfl hBodyWF
        refine ⟨?_, ?_, ?_⟩
        · sorry -- current-offer correspondence, `.recur`
        · sorry -- same-cycle completion, `.recur`
        · sorry -- menu equation, `.recur`
    | xoffer alphabet elseType branches =>
        obtain ⟨hElseWF, hBranchWF⟩ := typeWellFormedIn_xoffer hWF
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hBranchFuel : ∀ entry ∈ branches,
            typeCompilationFuel entry.2 < n := by
          intro entry hEntry
          rw [← hFuel]
          simp only [typeCompilationFuel]
          have := typeCompilationFuel_le_typeBranchCompilationFuel branches entry
            hEntry
          omega
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hBranch : ∀ entry ∈ branches,
            CurrentOfferCorrespondence entry.2 ∧
              SameCycleCompletionAgrees entry.2 ∧ FutureOffersAgree entry.2 :=
          fun entry hEntry =>
            ih _ (hBranchFuel entry hEntry) bound entry.2 rfl
              (hBranchWF entry hEntry)
        refine ⟨?_, sameCycleCompletionAgrees_xoffer alphabet elseType branches
            hElse.2.1 (fun entry hEntry => (hBranch entry hEntry).2.1), ?_⟩
        · refine currentOfferCorrespondence_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            (fun a t hMem =>
              offerBranchesDisjoint_of_ownership t
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hBranchWF (a, t) hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun a t hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem]; rfl)
            hElse.1 (fun a t hMem => (hBranch (a, t) hMem).1)
        · sorry -- menu equation, `.xoffer`
    | offer alphabet elseType branches =>
        have hElseFuel : typeCompilationFuel elseType < n := by
          rw [← hFuel]; simp only [typeCompilationFuel]; omega
        have hGeneratedFuel : ∀ selected,
            typeCompilationFuel
                (parallelTypeBranchesSelecting alphabet selected branches) < n := by
          intro selected
          rw [← hFuel, typeCompilationFuel_parallelTypeBranchesSelecting]
          simp only [typeCompilationFuel]
          omega
        obtain ⟨hElseWF, hSelectedWF⟩ := typeWellFormedIn_offer hWF
        have hElse := ih _ hElseFuel bound elseType rfl hElseWF
        have hSelected : ∀ selected ∈ branches,
            CurrentOfferCorrespondence
                (parallelTypeBranchesSelecting alphabet selected branches) ∧
              SameCycleCompletionAgrees
                (parallelTypeBranchesSelecting alphabet selected branches) ∧
              FutureOffersAgree
                (parallelTypeBranchesSelecting alphabet selected branches) :=
          fun selected hMem =>
            ih _ (hGeneratedFuel selected) bound _ rfl (hSelectedWF selected hMem)
        refine ⟨?_, sameCycleCompletionAgrees_offer alphabet elseType branches
            hElse.2.1
            (fun selected hMem => (hSelected selected hMem).2.1), ?_⟩
        · refine currentOfferCorrespondence_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership elseType
              hElseWF.2.2.2.2.2.2.2.2.2.1 hElseWF.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.1
              hElseWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              rw [h.2.1]; rfl)
            ?_
            (fun selected hMem =>
              offerBranchesDisjoint_of_ownership _
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.1
                (hSelectedWF selected hMem).2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (fun selected hMem => by
              rw [parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem]; rfl)
            hElse.1 (fun selected hMem => (hSelected selected hMem).1)
          · intro branch hMem
            have hWholeDisjoint :=
              offerBranchesDisjoint_of_ownership
                (.offer alphabet elseType branches)
                hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
                hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2
            simp only [PactType.OfferBranchesDisjoint] at hWholeDisjoint
            exact offerBranchesDisjoint_of_mem_branch hWholeDisjoint.2.2 hMem
        · sorry -- menu equation, `.offer`

end

end Pact
