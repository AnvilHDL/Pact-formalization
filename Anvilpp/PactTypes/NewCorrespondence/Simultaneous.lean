import Anvilpp.PactTypes.NewCorrespondence.Cases.Base
import Anvilpp.PactTypes.NewCorrespondence.Helpers.NewMainHelpers
import Anvilpp.PactTypes.NewCorrespondence.Helpers.OwnershipTransport
import Anvilpp.PactTypes.NewCorrespondence.Helpers.TypeWellFormedIn
import Anvilpp.PactTypes.NewCorrespondence.Helpers.SurvivorTransport

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


/-- Every state the relation names is carried by the compiled fragment.  Each
clause of the relation tags a child state exactly as the matching constructor
tags its child carrier. -/
theorem buildRelationSetCoreFuel_state_mem :
    ∀ (fuel : Nat) (processType : PactType),
      processType.OfferBranchesDisjoint →
      ∀ (residual : PactType) (state : TypeAutomatonState),
        (residual, state) ∈ buildRelationSetCoreFuel fuel processType →
        state ∈ (compileTypeFuel fuel processType).states := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hDisjoint residual state hMem
      simp only [buildRelationSetCoreFuel, Finset.mem_singleton] at hMem
      injection hMem with hResidual hState
      subst hState
      simp [compileTypeFuel]
  | succ fuel ih =>
      intro processType hDisjoint residual state hMem
      cases processType with
      | skip alphabet =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton] at hMem
          injection hMem with hResidual hState
          subst hState
          simp [compileTypeFuel, finishAutomatonFragment]
      | message alphabet msg dir =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton] at hMem
          rcases hMem with h | h
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
      | tock alphabet =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton] at hMem
          rcases hMem with h | h
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
      | progress alphabet pid =>
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_singleton] at hMem
          rcases hMem with h | h
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
          · injection h with hResidual hState
            subst hState
            simp [compileTypeFuel, finishAutomatonFragment]
      | var alphabet name =>
          simp only [buildRelationSetCoreFuel, Finset.mem_singleton] at hMem
          injection hMem with hResidual hState
          subst hState
          simp [compileTypeFuel, finishAutomatonFragment]
      | choice alphabet left right =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image] at hMem
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hRoot | hLeft | hRight
          · injection hRoot with hResidual hState
            subst hState
            exact Or.inl (Or.inl (Finset.mem_singleton_self _))
          · obtain ⟨entry, hEntry, hEq⟩ := hLeft
            injection hEq with hResidual hState
            subst hState
            exact Or.inl (Or.inr (Finset.mem_image_of_mem _
              (ih left hDisjoint.1 entry.1 entry.2 hEntry)))
          · obtain ⟨entry, hEntry, hEq⟩ := hRight
            injection hEq with hResidual hState
            subst hState
            exact Or.inr (Finset.mem_image_of_mem _
              (ih right hDisjoint.2 entry.1 entry.2 hEntry))
      | fairChoice alphabet bid left right =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image] at hMem
          simp only [compileTypeFuel, buildChoiceAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hRoot | hLeft | hRight
          · injection hRoot with hResidual hState
            subst hState
            exact Or.inl (Or.inl (Finset.mem_singleton_self _))
          · obtain ⟨entry, hEntry, hEq⟩ := hLeft
            injection hEq with hResidual hState
            subst hState
            exact Or.inl (Or.inr (Finset.mem_image_of_mem _
              (ih left hDisjoint.1 entry.1 entry.2 hEntry)))
          · obtain ⟨entry, hEntry, hEq⟩ := hRight
            injection hEq with hResidual hState
            subst hState
            exact Or.inr (Finset.mem_image_of_mem _
              (ih right hDisjoint.2 entry.1 entry.2 hEntry))
      | seq alphabet left right =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_union,
            Finset.mem_image, Finset.mem_filter] at hMem
          simp only [compileTypeFuel, buildSequenceAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hLeft | hRight
          · obtain ⟨entry, ⟨hEntry, hNotDeleted⟩, hEq⟩ := hLeft
            injection hEq with hResidual hState
            subst hState
            exact Or.inl (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr
              ⟨ih left hDisjoint.1 entry.1 entry.2 hEntry, hNotDeleted⟩))
          · obtain ⟨entry, hEntry, hEq⟩ := hRight
            injection hEq with hResidual hState
            subst hState
            exact Or.inr (Finset.mem_image_of_mem _
              (ih right hDisjoint.2 entry.1 entry.2 hEntry))
      | par alphabet left right interface =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hMem
          simp only [compileTypeFuel, buildParallelAutomaton,
            finishAutomatonFragment, Finset.mem_insert, Finset.mem_union]
          have hLeftShape := CompiledShape.compileTypeFuel_shapeEq_reannotate fuel left
            hDisjoint.1 alphabet
          have hRightShape := CompiledShape.compileTypeFuel_shapeEq_reannotate fuel right
            hDisjoint.2 alphabet
          rcases hMem with hFinal | (hPair | hSurvivorLeft) | hSurvivorRight
          · injection hFinal with hResidual hState
            subst hState
            exact Or.inl rfl
          · obtain ⟨entry, hEntry, hEq⟩ := hPair
            obtain ⟨hLeftMem, hRightMem⟩ := Finset.mem_product.mp hEntry
            injection hEq with hResidual hState
            subst hState
            refine Or.inr (Or.inl (Or.inl (Finset.mem_biUnion.mpr
              ⟨entry.1.2, ih left hDisjoint.1 entry.1.1 entry.1.2 hLeftMem,
                Finset.mem_image_of_mem _
                  (ih right hDisjoint.2 entry.2.1 entry.2.2 hRightMem)⟩)))
          · obtain ⟨entry, ⟨hEntry, hNotAcc⟩, hEq⟩ := hSurvivorLeft
            injection hEq with hResidual hState
            subst hState
            refine Or.inr (Or.inl (Or.inr (Finset.mem_image_of_mem _ ?_)))
            rw [← hLeftShape.1]
            exact ih (left.reannotate alphabet)
              (reannotate_offerBranchesDisjoint _ _ hDisjoint.1)
              entry.1 entry.2 hEntry
          · obtain ⟨entry, ⟨hEntry, hNotAcc⟩, hEq⟩ := hSurvivorRight
            injection hEq with hResidual hState
            subst hState
            refine Or.inr (Or.inr (Finset.mem_image_of_mem _ ?_))
            rw [← hRightShape.1]
            exact ih (right.reannotate alphabet)
              (reannotate_offerBranchesDisjoint _ _ hDisjoint.2)
              entry.1 entry.2 hEntry
      | recur alphabet name body =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_image] at hMem
          simp only [compileTypeFuel, buildRecursionAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hRoot | hBody
          · injection hRoot with hResidual hState
            subst hState
            exact Or.inl (Finset.mem_singleton_self _)
          · obtain ⟨entry, hEntry, hEq⟩ := hBody
            injection hEq with hResidual hState
            subst hState
            exact Or.inr (Finset.mem_image_of_mem _
              (ih body hDisjoint entry.1 entry.2 hEntry))
      | xoffer alphabet elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image] at hMem
          simp only [compileTypeFuel, buildExclusiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hRoot | hElse | hIndexed
          · injection hRoot with hResidual hState
            subst hState
            exact Or.inl (Or.inl (Finset.mem_singleton_self _))
          · obtain ⟨entry, hEntry, hEq⟩ := hElse
            injection hEq with hResidual hState
            subst hState
            exact Or.inl (Or.inr (Finset.mem_image_of_mem _
              (ih elseType hDisjoint.1 entry.1 entry.2 hEntry)))
          · rw [mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hInner⟩
            · simp at hEmpty
            · simp only [Finset.mem_image] at hInner
              obtain ⟨entry, hEntry, hEq⟩ := hInner
              injection hEq with hResidual hState
              subst hState
              have hBranchMem : indexed.1 ∈ branches := by
                have hMapped : indexed.1 ∈ branches.zipIdx.map Prod.fst :=
                  List.mem_map_of_mem (f := Prod.fst) hIndexedMem
                simpa using hMapped
              refine Or.inr ?_
              rw [indexedFragmentStates, mem_foldl_union_iff]
              refine Or.inr ⟨((indexed.1.1, compileTypeFuel fuel indexed.1.2),
                indexed.2), ?_, ?_⟩
              · rw [List.zipIdx_map]
                exact List.mem_map_of_mem hIndexedMem
              · exact Finset.mem_image_of_mem _
                  (ih indexed.1.2
                    (offerBranchesDisjoint_of_mem_branch hDisjoint.2 hBranchMem)
                    entry.1 entry.2 hEntry)
      | offer alphabet elseType branches =>
          simp only [PactType.OfferBranchesDisjoint] at hDisjoint
          simp only [buildRelationSetCoreFuel, Finset.mem_insert,
            Finset.mem_union, Finset.mem_image] at hMem
          simp only [compileTypeFuel, buildSelectedConjunctiveOfferAutomaton,
            finishAutomatonFragment, Finset.mem_union]
          rcases hMem with hRoot | hElse | hIndexed
          · injection hRoot with hResidual hState
            subst hState
            exact Or.inl (Or.inl (Finset.mem_singleton_self _))
          · obtain ⟨entry, hEntry, hEq⟩ := hElse
            injection hEq with hResidual hState
            subst hState
            exact Or.inl (Or.inr (Finset.mem_image_of_mem _
              (ih elseType hDisjoint.1 entry.1 entry.2 hEntry)))
          · rw [mem_foldl_union_iff] at hIndexed
            rcases hIndexed with hEmpty | ⟨indexed, hIndexedMem, hInner⟩
            · simp at hEmpty
            · simp only [Finset.mem_image] at hInner
              obtain ⟨entry, hEntry, hEq⟩ := hInner
              injection hEq with hResidual hState
              subst hState
              refine Or.inr ?_
              rw [indexedFragmentStates, mem_foldl_union_iff]
              refine Or.inr ⟨((indexed.1.1, compileTypeFuel fuel
                (parallelTypeBranchesSelecting alphabet indexed.1 branches)),
                indexed.2), ?_, ?_⟩
              · rw [List.zipIdx_map]
                exact List.mem_map_of_mem hIndexedMem
              · refine Finset.mem_image_of_mem _
                  (ih (parallelTypeBranchesSelecting alphabet indexed.1 branches)
                    ?_ entry.1 entry.2 hEntry)
                exact parallelTypeBranchesSelecting_offerBranchesDisjoint
                  indexed.1 branches (fun branch hBranch =>
                    offerBranchesDisjoint_of_mem_branch hDisjoint.2.2 hBranch)

/-- Every state named by the compiler relation belongs to the compiled
fragment's carrier. -/
theorem relationMembership_state_mem
    (processType residual : PactType) (state : TypeAutomatonState)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (hRelated : relationMembership
      (buildRelationSet processType (compileType processType)) residual state) :
    state ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).states :=
  buildRelationSetCoreFuel_state_mem (typeCompilationFuel processType)
    processType hDisjoint residual state hRelated

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
  ∀ {bound : List String}, TypeWellFormedIn bound processType →
  (∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target)) →
  ∀ {residual : PactType} {state state' : TypeAutomatonState}
    {env : TypeEnvironment} {label : TypeLabel} {offers : TypeOfferSummary},
    relationMembership
      (buildRelationSet processType (compileType processType)) residual state →
    (compileType processType).HasEdge state env label offers state' →
    ∃ residual',
      relationMembership
        (buildRelationSet processType (compileType processType))
        residual' state'

/-- Relation-level re-signing transport at arbitrary fuel: a state related under
a type is related under its re-stamping.  **Open.**  Discharge via
`survivorTransport_all` after threading `TypeWellFormedIn` through
`buildRelationSetCoreFuel_edge_target_mem`'s induction, the way
`OfferBranchesDisjoint` already is; the fuel there is always sufficient, so
`buildRelationSetCoreFuel_eq_of_sufficient` normalises it to
`typeCompilationFuel`. -/
theorem resignTransport_relationMembership :
    ∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target) := by
  sorry

/-- The survivor menu bound over a same-cycle reach, at the shape the parallel
menu clause consumes.  **Open** only in its two side conditions: closedness of
the component (`futureReachable_related` needs `AllVariablesBound []`, but
`bound` grows at every `.recur`, so this wants the disjunctive *related-or-inert*
form, with the inert half from `AutomatonFragment.MarkerOffersInert`), and
`alphabet.actions` avoiding `ParallelInterfaces component` (expected from
`InterfaceAlphabetScoped`).  Everything else is
`survivorMenuBound_reach`. -/
theorem survivorMenuBound_par
    (component : PactType) (alphabet : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (q : TypeAutomatonState) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      computeFutureOf (component.reannotate alphabet) s ⊆
        computeFutureOf component s := by
  sorry

/-- Every edge lands on a state that still represents some residual.  A public
edge always resolves a `.visible` pending edge, so the variable-marker escape of
the relation's closure lemma cannot occur. -/
theorem targetsRelated (processType : PactType) : TargetsRelated processType := by
  classical
  intro bound hWF hResign residual state state' env label offers _ hEdge
  obtain ⟨pendingEdge, hPendingMem, -, -, hPLabel, -, -, hPTarget⟩ :=
    (compileType_hasEdge_iff_hasResolvedEdge processType state state' env label
      offers).mp hEdge
  have hDisjoint : processType.OfferBranchesDisjoint :=
    offerBranchesDisjoint_of_ownership processType hWF.2.2.2.2.2.2.2.2.2.1
      hWF.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.1
      hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases buildRelationSetCoreFuel_edge_target_mem
    hResign
    (fun component target fuel hDisjointComponent =>
      (CompiledShape.compileTypeFuel_shapeEq_reannotate fuel component
        hDisjointComponent target).2.2)
    reannotate_offerBranchesDisjoint
    (fun _ selected branches hBranches =>
      parallelTypeBranchesSelecting_offerBranchesDisjoint selected branches
        (branchesDisjoint_mem hBranches))
    (typeCompilationFuel processType) processType le_rfl hDisjoint pendingEdge
    hPendingMem with
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
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    {seqBound : List String}
    (hSeqWF : TypeWellFormedIn seqBound (.seq alphabet left right))
    (hResign : ∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target))
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
    obtain ⟨residual', hTargetRelated⟩ :=
      targetsRelated _ hSeqWF hResign hRelated hEdge
    cases compileType_seq_edge_cases alphabet left right hLeftDisjoint hResign
        hRightDisjoint
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
    rw [hTransportLeft q
      (relationMembership_state_mem left _ q hLeftDisjoint hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q
      (relationMembership_state_mem right _ q hRightDisjoint hChild)]
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
    rw [hTransportLeft q
      (relationMembership_state_mem left _ q hLeftDisjoint hChild)]
    exact hLeft hChild
  · subst hState
    rw [hTransportRight q
      (relationMembership_state_mem right _ q hRightDisjoint hChild)]
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

/-- Each branch of a conjunctive offer carries the node alphabet and is itself
alphabet-well-formed. -/
theorem offerBranchesWellFormed_of_mem :
    ∀ {alphabet : PactTypeAlphabet} {seen : Finset BareMessage}
      {branches : List (BareMessage × PactType)}
      {branch : BareMessage × PactType},
      PactType.OfferBranchesWellFormed alphabet seen branches →
      branch ∈ branches →
      branch.2.alphabet = alphabet ∧ branch.2.AlphabetWellFormed
  | _, _, (_, _) :: rest, branch, hWF, hMem => by
      rw [PactType.OfferBranchesWellFormed] at hWF
      rcases List.mem_cons.mp hMem with rfl | hRest
      · exact ⟨hWF.1, hWF.2.1⟩
      · exact offerBranchesWellFormed_of_mem hWF.2.2 hRest
  | _, _, [], _, _, hMem => by simp at hMem
  termination_by _ _ branches => sizeOf branches

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

/-- A conjunctive-offer root carries no product information. -/
theorem stateProductInfo_offer_root (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    stateProductInfo (.offer alphabet elseType branches)
        TypeAutomatonState.root = none := by
  obtain ⟨k, hk⟩ : ∃ k,
      typeCompilationFuel (.offer alphabet elseType branches) = k + 1 :=
    ⟨typeCompilationFuel (.offer alphabet elseType branches) - 1, by
      have := typeCompilationFuel_positive (.offer alphabet elseType branches)
      omega⟩
  simp only [stateProductInfo, hk, stateProductInfoFuel]

/-- A conjunctive-offer root offers exactly the branch head actions.  Unlike the
exclusive root, its enabling edges publish nothing (their current offer is `∅`);
the branch actions come from the wait and default families, whose filters the
empty environment always satisfies. -/
theorem buildSelectedConjunctiveOfferAutomaton_offersAt_root
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    ({ states := (buildSelectedConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).states
       edges := (buildSelectedConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).edges } : PendingAutomaton).offersAt
        TypeAutomatonState.root =
      typeBranchActions branches := by
  classical
  apply Finset.Subset.antisymm
  · -- Every root edge publishes either `∅` or exactly the branch actions.
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hAction
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hEdge
    rcases hEdge with ((((hElseCopy | hIndexed) | hEnabled) | hWait) | hResolved)
    · exfalso
      obtain ⟨childEdge, -, hEq⟩ := hElseCopy
      rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
    · exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
      rcases hIndexed with hEmpty | ⟨indexed, -, hIn'⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hIn'
        obtain ⟨childEdge, -, hEq⟩ := hIn'
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · -- An enabling edge publishes nothing.
      exfalso
      rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, -, hIn'⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hIn'
        obtain ⟨environment, -, hEq⟩ := hIn'
        rw [← hEq] at hIn
        simp at hIn
    · obtain ⟨environment, -, hEq⟩ := hWait
      rw [← hEq] at hIn
      simpa using hIn
    · obtain ⟨environment, -, hEq⟩ := hResolved
      rw [← hEq] at hIn
      simpa using hIn
  · -- The empty environment satisfies the default family's filter, and that
    -- edge publishes exactly the branch actions.
    intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter]
    refine Exists.intro
      { source := TypeAutomatonState.root,
        environment := TypeEnvironment.empty,
        label := AutomatonConstructionLabel.visible TypeLabel.silent,
        current := typeBranchActions branches,
        future := FutureSpec.at (childState 0 elseAutomaton.initial)
          (typeBranchActions branches),
        target := childState 0 elseAutomaton.initial }
      ⟨⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter]
      refine Or.inr ⟨TypeEnvironment.empty,
        ⟨empty_mem_localEnvironments alphabet, rfl, ?_, ?_, hGuard⟩, rfl⟩
      · simp [TypeEnvironment.empty]
      · simp [TypeEnvironment.empty]
    · simpa using hAction

/-- Menus agree at an exclusive offer.  The root exposes the branch heads on its
own edges and reaches exactly the default and branch entries. -/
theorem futureOffersAgree_xoffer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
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
    -- Both menus are gated on the same declaredness condition: if it fails,
    -- `typeFutureOffers` is empty by its own gate and the root has no outgoing
    -- edges, since all three root families carry the gate too.
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    case neg =>
      -- The semantic menu is `∅` by its own gate, and the compiled menu is
      -- bounded by the type's alphabet, which the undeclared heads escape.
      have hSemantic : typeFutureOffers whole = ∅ := by
        rw [hWholeDef]
        simp only [typeFutureOffers, typeFutureOffersFuel, if_neg hGuard]
      rw [hSemantic]
      -- Every root family carries the gate, so the root has no outgoing edge;
      -- its same-cycle reach is itself and it publishes nothing.
      have hNoRootEdge : ∀ edge ∈ (compileTypeFuel (typeCompilationFuel whole)
          whole).edges, edge.source ≠ TypeAutomatonState.root := by
        intro edge hEdge hSource
        rw [hWhole] at hEdge
        simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
          childPendingEdges, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter] at hEdge
        rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
        · obtain ⟨childEdge, -, hEq⟩ := hElse
          rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [childPendingEdges, Finset.mem_image] at hIn
            obtain ⟨childEdge, -, hEq⟩ := hIn
            rw [← hEq] at hSource
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hBranch
          rcases hBranch with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [Finset.mem_image] at hIn
            obtain ⟨environment, hEnv, -⟩ := hIn
            rw [Finset.mem_filter] at hEnv
            exact hGuard hEnv.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hWait
          exact hGuard hEnv.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hResolved
          exact hGuard hEnv.2.2.2.2
      -- With no root-sourced edge the root references nothing, so its
      -- same-cycle reach is itself and it publishes no offer.
      have hRefs : pending.referencedStates TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.referencedStates]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hOffersEmpty : pending.offersAt TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.offersAt]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hReach : pending.futureReachable TypeAutomatonState.root =
          {TypeAutomatonState.root} := by
        simp only [PendingAutomaton.futureReachable]
        generalize pending.states.card = k
        induction k with
        | zero => rfl
        | succ k ihk =>
            rw [PendingAutomaton.futureReachableAux]
            have hStep : PendingAutomaton.futureStep pending
                {TypeAutomatonState.root} = {TypeAutomatonState.root} := by
              simp only [PendingAutomaton.futureStep]
              rw [show ({TypeAutomatonState.root} : Finset TypeAutomatonState).biUnion
                  pending.referencedStates = ∅ by
                rw [Finset.singleton_biUnion]; exact hRefs]
              simp
            rw [hStep]
            exact ihk
      -- The menu unfolds to a union over `{root}` of `offersAt root`, which is
      -- empty, plus the product term, which is `none` at an offer root.
      obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel whole = k + 1 :=
        ⟨typeCompilationFuel whole - 1, by
          have := typeCompilationFuel_positive whole; omega⟩
      show computeFutureOf whole TypeAutomatonState.root = ∅
      unfold computeFutureOf
      rw [hk, computeFutureOfFuel]
      simp only [← hk, ← hPending]
      rw [hReach]
      simp only [Finset.singleton_biUnion, hOffersEmpty]
      rw [show stateProductInfo whole TypeAutomatonState.root = none by
        simp only [hWholeDef]
        exact stateProductInfo_xoffer_root alphabet elseType branches]
      simp
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
      (relationMembership_state_mem elseType _ q hElseDisjoint hChild)]
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
      (relationMembership_state_mem branchType _ q hDisjoint hChild)]
    exact hBranches (action, branchType) hMem hChild

/-- Menus agree at a conjunctive offer.  The root exposes the branch heads on
its own edges and reaches exactly the default entry and the entries of the
generated selected products. -/
theorem futureOffersAgree_offer (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType))
    (hWholeDisjoint :
      (PactType.offer alphabet elseType branches).OfferBranchesDisjoint)
    (hElseAlphabet : elseType.alphabet = alphabet)
    (hSelAlphabet : ∀ selected ∈ branches,
      (parallelTypeBranchesSelecting alphabet selected branches).alphabet =
        alphabet)
    -- Needed only once the branch heads are declared; both menus are empty
    -- otherwise, by their shared gate.
    (hSelMenu : (∀ b ∈ branches, b.1 ∈ alphabet.actions) →
      ∀ selected ∈ branches,
      typeFutureOffers
          (parallelTypeBranchesSelecting alphabet selected branches) =
        branches.foldl (fun offers branch =>
          offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅)
    (hElse : FutureOffersAgree elseType)
    (hSelected : ∀ selected ∈ branches,
      FutureOffersAgree
        (parallelTypeBranchesSelecting alphabet selected branches)) :
    FutureOffersAgree (.offer alphabet elseType branches) := by
  classical
  set whole : PactType := .offer alphabet elseType branches with hWholeDef
  have hWhole := compileTypeFuel_offer_eq alphabet elseType branches
  have hDisjointParts :
      elseType.OfferBranchesDisjoint ∧
        PactType.OfferBranchesDisjointBranches branches := by
    have hParts := hWholeDisjoint
    simp only [hWholeDef, PactType.OfferBranchesDisjoint] at hParts
    exact ⟨hParts.1, hParts.2.2⟩
  have hElseDisjoint : elseType.OfferBranchesDisjoint := hDisjointParts.1
  have hBranchDisjoint : ∀ branch ∈ branches,
      branch.2.OfferBranchesDisjoint := by
    intro branch hBranch
    exact offerBranchesDisjoint_of_mem_branch hDisjointParts.2 hBranch
  have hElseFuel :
      typeCompilationFuel elseType + 1 ≤ typeCompilationFuel whole := by
    simp only [hWholeDef, typeCompilationFuel]
    omega
  have hSelFuel : ∀ selected ∈ branches,
      typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet selected branches) + 1 ≤
        typeCompilationFuel whole := by
    intro selected _
    rw [typeCompilationFuel_parallelTypeBranchesSelecting]
    simp only [hWholeDef, typeCompilationFuel]
    omega
  intro residual state hRelated
  rcases relationMembership_offer_cases alphabet elseType branches
      hRelated with hRoot | ⟨q, hState, hChild⟩ |
      ⟨i, selected, q, hGet, hState, hChild⟩
  · injection hRoot with hResidual hStateEq
    subst hResidual
    subst hStateEq
    set selectedAutomata :=
      branches.map fun selected =>
        (selected.1,
          compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet selected branches))
            (parallelTypeBranchesSelecting alphabet selected branches))
      with hSelectedAutomata
    set elseFragment :=
      compileTypeFuel (typeCompilationFuel elseType) elseType with hElseFragment
    set pending : PendingAutomaton :=
      { states := (compileTypeFuel (typeCompilationFuel whole) whole).states
        edges := (compileTypeFuel (typeCompilationFuel whole) whole).edges }
      with hPending
    have hHeads : selectedAutomata.map Prod.fst = branches.map Prod.fst := by
      rw [hSelectedAutomata, List.map_map]
      rfl
    -- Both menus are gated on the same declaredness condition: if it fails,
    -- `typeFutureOffers` is empty by its own gate and the root has no outgoing
    -- edges, since all three root families carry the gate too.
    by_cases hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    case neg =>
      -- The semantic menu is `∅` by its own gate, and the compiled root has no
      -- outgoing edge at all.
      have hSemantic : typeFutureOffers whole = ∅ := by
        rw [hWholeDef]
        simp only [typeFutureOffers, typeFutureOffersFuel, if_neg hGuard]
      rw [hSemantic]
      -- Every root family carries the gate, so the root has no outgoing edge;
      -- its same-cycle reach is itself and it publishes nothing.
      have hNoRootEdge : ∀ edge ∈ (compileTypeFuel (typeCompilationFuel whole)
          whole).edges, edge.source ≠ TypeAutomatonState.root := by
        intro edge hEdge hSource
        rw [hWhole] at hEdge
        simp only [buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment, childPendingEdges, Finset.mem_union,
          Finset.mem_image, Finset.mem_filter] at hEdge
        rcases hEdge with
          ((((hElseCopy | hIndexed) | hEnabled) | hWait) | hResolved)
        · obtain ⟨childEdge, -, hEq⟩ := hElseCopy
          rw [← hEq] at hSource; simp [childPendingEdge, childState] at hSource
        · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
          rcases hIndexed with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [childPendingEdges, Finset.mem_image] at hIn
            obtain ⟨childEdge, -, hEq⟩ := hIn
            rw [← hEq] at hSource
            simp [childPendingEdge, childState] at hSource
        · rw [mem_foldl_union_iff] at hEnabled
          rcases hEnabled with hEmpty | ⟨indexed, -, hIn⟩
          · exact absurd hEmpty (Finset.notMem_empty _)
          · rw [Finset.mem_image] at hIn
            obtain ⟨environment, hEnv, -⟩ := hIn
            rw [Finset.mem_filter] at hEnv
            exact hGuard hEnv.2.2
        · obtain ⟨environment, hEnv, -⟩ := hWait
          exact hGuard hEnv.2.2.2.2
        · obtain ⟨environment, hEnv, -⟩ := hResolved
          exact hGuard hEnv.2.2.2.2
      -- With no root-sourced edge the root references nothing, so its
      -- same-cycle reach is itself and it publishes no offer.
      have hRefs : pending.referencedStates TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.referencedStates]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hOffersEmpty : pending.offersAt TypeAutomatonState.root = ∅ := by
        rw [hPending]
        simp only [PendingAutomaton.offersAt]
        rw [Finset.filter_eq_empty_iff.mpr (fun edge hEdge => hNoRootEdge edge
          hEdge)]
        simp
      have hReach : pending.futureReachable TypeAutomatonState.root =
          {TypeAutomatonState.root} := by
        simp only [PendingAutomaton.futureReachable]
        generalize pending.states.card = k
        induction k with
        | zero => rfl
        | succ k ihk =>
            rw [PendingAutomaton.futureReachableAux]
            have hStep : PendingAutomaton.futureStep pending
                {TypeAutomatonState.root} = {TypeAutomatonState.root} := by
              simp only [PendingAutomaton.futureStep]
              rw [show ({TypeAutomatonState.root} : Finset TypeAutomatonState).biUnion
                  pending.referencedStates = ∅ by
                rw [Finset.singleton_biUnion]; exact hRefs]
              simp
            rw [hStep]
            exact ihk
      -- The menu unfolds to a union over `{root}` of `offersAt root`, which is
      -- empty, plus the product term, which is `none` at an offer root.
      obtain ⟨k, hk⟩ : ∃ k, typeCompilationFuel whole = k + 1 :=
        ⟨typeCompilationFuel whole - 1, by
          have := typeCompilationFuel_positive whole; omega⟩
      show computeFutureOf whole TypeAutomatonState.root = ∅
      unfold computeFutureOf
      rw [hk, computeFutureOfFuel]
      simp only [← hk, ← hPending]
      rw [hReach]
      simp only [Finset.singleton_biUnion, hOffersEmpty]
      rw [show stateProductInfo whole TypeAutomatonState.root = none by
        simp only [hWholeDef]
        exact stateProductInfo_offer_root alphabet elseType branches]
      simp
    have hOffers : pending.offersAt TypeAutomatonState.root =
        typeBranchActions branches := by
      rw [hPending, hWhole]
      exact buildSelectedConjunctiveOfferAutomaton_offersAt_root alphabet
        branches elseFragment selectedAutomata hGuard
    have hDecomp := computeFutureOf_root_decomposition whole
      TypeAutomatonState.root
      (conjunctiveOfferEntries elseFragment selectedAutomata) pending hPending
      (referencesClosed_compileTypeFuel whole (typeCompilationFuel whole)
        (Nat.le_refl _) hWholeDisjoint)
      (by
        rw [hPending]
        show TypeAutomatonState.root ∈
          (compileTypeFuel (typeCompilationFuel whole) whole).states
        rw [hWhole]
        simp only [buildSelectedConjunctiveOfferAutomaton,
          finishAutomatonFragment]
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
      (by
        rw [hPending, hWhole]
        exact buildSelectedConjunctiveOfferAutomaton_referencedStates_root_subset
          alphabet branches elseFragment selectedAutomata)
      (by
        rw [hPending, hWhole]
        exact
          buildSelectedConjunctiveOfferAutomaton_entries_subset_referencedStates_root
            alphabet branches elseFragment selectedAutomata hHeads hGuard)
      (by
        simp only [hWholeDef]
        exact stateProductInfo_offer_root alphabet elseType branches)
      (by
        intro action hIn
        rw [hOffers] at hIn
        simp only [typeBranchActions, List.mem_toFinset, List.mem_map] at hIn
        obtain ⟨branch, hMem, rfl⟩ := hIn
        simpa [hWholeDef, PactType.alphabet] using hGuard branch hMem)
    rw [hDecomp, hOffers, hWholeDef,
      typeFutureOffers_offer alphabet elseType branches hGuard]
    -- the default entry carries the default's menu
    have hElseMenu : computeFutureOf whole
        (childState 0 elseFragment.initial) = typeFutureOffers elseType := by
      rw [childState, computeFutureOf_selectedConjunctiveOffer_else elseType
        branches whole hWhole (by rw [hElseAlphabet, hWholeDef]; rfl)
        hElseFuel hElseDisjoint
        (stateProductInfo_offer_child_else alphabet elseType branches)
        elseFragment.initial
        (compileTypeFuel_initial_mem _ elseType (Nat.le_refl _))]
      exact hElse (buildRelationSet_initial elseType _ rfl)
    -- and each selected-product entry the branch fold's menu
    have hBranchMenu : ∀ indexed ∈ selectedAutomata.zipIdx,
        computeFutureOf whole
            (childState (indexed.2 + 1) indexed.1.2.initial) =
          branches.foldl (fun offers branch =>
            offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
      intro indexed hIndexed
      have hGetAuto : selectedAutomata[indexed.2]? = some indexed.1 := by
        rw [← List.mk_mem_zipIdx_iff_getElem?]
        simpa using hIndexed
      rw [hSelectedAutomata, List.getElem?_map, Option.map_eq_some_iff]
        at hGetAuto
      obtain ⟨branch, hGetBranch, hEq⟩ := hGetAuto
      have hMem : branch ∈ branches := List.mem_of_getElem? hGetBranch
      have hShape : indexed.1.2 =
          compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet branch branches))
            (parallelTypeBranchesSelecting alphabet branch branches) := by
        rw [← hEq]
      rw [hShape, childState, computeFutureOf_selectedConjunctiveOffer_branch
        elseType branches whole hWhole indexed.2 branch hGetBranch
        (hSelFuel branch hMem)
        (by rw [hSelAlphabet branch hMem, hWholeDef]; rfl) hBranchDisjoint
        (stateProductInfo_offer_child_branch alphabet elseType branches
          indexed.2 branch hGetBranch) _
        (compileTypeFuel_initial_mem _ _ (Nat.le_refl _))]
      rw [← hSelMenu hGuard branch hMem]
      exact hSelected branch hMem (buildRelationSet_initial _ _ rfl)
    have hBranchMenu' : ∀ branch ∈ branches,
        ∃ indexed ∈ selectedAutomata.zipIdx,
          computeFutureOf whole
              (childState (indexed.2 + 1) indexed.1.2.initial) =
            branches.foldl (fun offers branch =>
              offers ∪ {branch.1} ∪ typeFutureOffers branch.2) ∅ := by
      intro branch hMem
      obtain ⟨index, hGetBranch⟩ := List.getElem?_of_mem hMem
      have hGetAuto : selectedAutomata[index]? =
          some (branch.1, compileTypeFuel
            (typeCompilationFuel
              (parallelTypeBranchesSelecting alphabet branch branches))
            (parallelTypeBranchesSelecting alphabet branch branches)) := by
        rw [hSelectedAutomata, List.getElem?_map, hGetBranch]
        rfl
      refine ⟨((branch.1, compileTypeFuel
        (typeCompilationFuel
          (parallelTypeBranchesSelecting alphabet branch branches))
        (parallelTypeBranchesSelecting alphabet branch branches)), index),
        List.mk_mem_zipIdx_iff_getElem?.mpr hGetAuto, ?_⟩
      rw [childState, computeFutureOf_selectedConjunctiveOffer_branch elseType
        branches whole hWhole index branch hGetBranch (hSelFuel branch hMem)
        (by rw [hSelAlphabet branch hMem, hWholeDef]; rfl) hBranchDisjoint
        (stateProductInfo_offer_child_branch alphabet elseType branches index
          branch hGetBranch) _
        (compileTypeFuel_initial_mem _ _ (Nat.le_refl _))]
      rw [← hSelMenu hGuard branch hMem]
      exact hSelected branch hMem (buildRelationSet_initial _ _ rfl)
    ext offer
    rw [mem_foldl_offer_menu, Finset.mem_union, Finset.mem_biUnion,
      typeBranchActions, List.mem_toFinset, List.mem_map]
    simp only [conjunctiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro (⟨branch, hMem, rfl⟩ | ⟨entry, hEntry, hIn⟩)
      · exact Or.inr ⟨branch, hMem, Or.inl rfl⟩
      · rcases hEntry with rfl | ⟨indexed, hIndexed, rfl⟩
        · rw [hElseMenu] at hIn
          exact Or.inl hIn
        · rw [hBranchMenu indexed hIndexed, mem_foldl_offer_menu] at hIn
          simp only [Finset.notMem_empty, false_or] at hIn
          exact Or.inr hIn
    · rintro (hElseIn | ⟨branch, hMem, rfl | hMenuIn⟩)
      · exact Or.inr ⟨childState 0 elseFragment.initial, Or.inl rfl,
          by rw [hElseMenu]; exact hElseIn⟩
      · exact Or.inl ⟨branch, hMem, rfl⟩
      · obtain ⟨indexed, hIndexed, hMenu⟩ := hBranchMenu' branch hMem
        refine Or.inr ⟨childState (indexed.2 + 1) indexed.1.2.initial,
          Or.inr ⟨indexed, hIndexed, rfl⟩, ?_⟩
        rw [hMenu, mem_foldl_offer_menu]
        exact Or.inr ⟨branch, hMem, Or.inr hMenuIn⟩
  · subst hState
    rw [computeFutureOf_selectedConjunctiveOffer_else elseType branches whole
      hWhole (by rw [hElseAlphabet, hWholeDef]; rfl) hElseFuel hElseDisjoint
      (stateProductInfo_offer_child_else alphabet elseType branches) q
      (relationMembership_state_mem elseType _ q hElseDisjoint hChild)]
    exact hElse hChild
  · subst hState
    have hMem : selected ∈ branches := List.mem_of_getElem? hGet
    rw [computeFutureOf_selectedConjunctiveOffer_branch elseType branches whole
      hWhole i selected hGet (hSelFuel selected hMem)
      (by rw [hSelAlphabet selected hMem, hWholeDef]; rfl) hBranchDisjoint
      (stateProductInfo_offer_child_branch alphabet elseType branches i
        selected hGet) q
      (relationMembership_state_mem _ _ q
        (parallelTypeBranchesSelecting_offerBranchesDisjoint selected branches
          hBranchDisjoint) hChild)]
    exact hSelected selected hMem hChild

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


open PendingAutomaton

/-- A product state carries its own product term: the compiler reads the
interface and both component states straight off the state. -/
theorem stateProductInfo_par_pair (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (q1 q2 : TypeAutomatonState) :
    stateProductInfo (.par alphabet left right interface) (.pair q1 q2) =
      some (interface, left, right, q1, q2) := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuel, stateProductInfoFuel]

/-- The done state is not a product state. -/
theorem stateProductInfo_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    stateProductInfo (.par alphabet left right interface) .final = none := by
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  simp only [stateProductInfo, hFuel, stateProductInfoFuel]

set_option maxHeartbeats 1000000 in
/-- The menu at a product state is the hidden union of the component menus. -/
theorem computeFutureOf_par_pair (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (q1 q2 : TypeAutomatonState)
    (hSurvLeft : ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left)
          left).states,
        (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
        PendingAutomaton).futureReachable q1,
      computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right)
          right).states,
        (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
        PendingAutomaton).futureReachable q2,
      computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hq1 : q1 ∈ (compileTypeFuel (typeCompilationFuel left) left).states)
    (hq2 : q2 ∈ (compileTypeFuel (typeCompilationFuel right) right).states) :
    computeFutureOf (.par alphabet left right interface) (.pair q1 q2) =
      hideTypeOffers interface
        (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
  classical
  set N : Nat := max (typeCompilationFuel left) (typeCompilationFuel right)
    with hN
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      N + 1 := by simp only [hN, typeCompilationFuel]; omega
  have hLeftLe : typeCompilationFuel left ≤ N := le_max_left _ _
  have hRightLe : typeCompilationFuel right ≤ N := le_max_right _ _
  have hParentClosed := compileTypeFuel_referencesClosed (N + 1)
    (.par alphabet left right interface)
    (by simp only [TypeCompilationFuelSufficient, hFuel]; exact le_rfl)
    (by simp only [PactType.OfferBranchesDisjoint]
        exact ⟨hLeftDisjoint, hRightDisjoint⟩)
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set parent : PendingAutomaton :=
    { states := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel (N + 1)
        (PactType.par alphabet left right interface)).edges } with hParent
  -- the product term of the pair state itself is the whole right-hand side
  have hInfo : stateProductInfo (PactType.par alphabet left right interface)
      (.pair q1 q2) = some (interface, left, right, q1, q2) := by
    simp only [stateProductInfo, hFuel, stateProductInfoFuel]
  have hMenuLeft : computeFutureOfFuel N left q1 = computeFutureOf left q1 :=
    computeFutureOfFuel_eq_of_sufficient left q1 hLeftLe le_rfl
  have hMenuRight : computeFutureOfFuel N right q2 = computeFutureOf right q2 :=
    computeFutureOfFuel_eq_of_sufficient right q2 hRightLe le_rfl
  have hRhsSubset :
      hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) ⊆
        (parent.futureReachable (.pair q1 q2)).biUnion fun visited =>
          parent.offersAt visited ∪
            match stateProductInfo (PactType.par alphabet left right interface)
              visited with
            | some (i, l, r, a, b) =>
                hideTypeOffers i (computeFutureOfFuel N l a ∪
                  computeFutureOfFuel N r b)
            | none => ∅ := by
    intro action hAction
    refine Finset.mem_biUnion.mpr ⟨.pair q1 q2,
      PendingAutomaton.mem_futureReachable_self parent _, ?_⟩
    refine Finset.mem_union_right _ ?_
    rw [hInfo]
    simpa [hMenuLeft, hMenuRight] using hAction
  -- the filter by the parent alphabet is exactly the interface hiding
  have hBound : computeFutureOf left q1 ∪ computeFutureOf right q2 ⊆
      left.alphabet.actions ∪ right.alphabet.actions :=
    Finset.union_subset_union (computeFutureOf_subset_alphabet left q1)
      (computeFutureOf_subset_alphabet right q2)
  have hFilterEq :
      (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
          (fun action => action ∈
            (PactType.par alphabet left right interface).alphabet.actions) =
        hideTypeOffers interface
          (computeFutureOf left q1 ∪ computeFutureOf right q2) := by
    have := filter_parent_actions_eq_hide hCompatible
      (computeFutureOf left q1 ∪ computeFutureOf right q2) hBound
    simpa [PactType.alphabet] using this
  apply Finset.Subset.antisymm
  · intro action hAction
    obtain ⟨hRaw, hGate⟩ := Finset.mem_filter.mp hAction
    obtain ⟨visited, hVisited, hContrib⟩ := Finset.mem_biUnion.mp hRaw
    -- every visited state contributes within the two component menus
    have hInMenus : action ∈
        computeFutureOf left q1 ∪ computeFutureOf right q2 := by
      have hParEq : compileTypeFuel (N + 1)
          (PactType.par alphabet left right interface) =
          buildParallelAutomaton alphabet left.alphabet right.alphabet interface
            (compileTypeFuel N left) (compileTypeFuel N right)
            (compileTypeFuel N (left.reannotate alphabet))
            (compileTypeFuel N (right.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
            (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
            (computeFutureOfFuel (min N (typeCompilationFuel left))
              (left.reannotate alphabet))
            (computeFutureOfFuel (min N (typeCompilationFuel right))
              (right.reannotate alphabet)) := by
        simp only [compileTypeFuel]
      have hLeftFragEq : compileTypeFuel N left =
          compileTypeFuel (typeCompilationFuel left) left :=
        compileTypeFuel_eq_of_sufficient left hLeftLe le_rfl
      have hRightFragEq : compileTypeFuel N right =
          compileTypeFuel (typeCompilationFuel right) right :=
        compileTypeFuel_eq_of_sufficient right hRightLe le_rfl
      have hReach := buildParallelAutomaton_pair_futureReachable_subset
        alphabet left.alphabet right.alphabet interface
        (compileTypeFuel N left) (compileTypeFuel N right)
        (compileTypeFuel N (left.reannotate alphabet))
        (compileTypeFuel N (right.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
        (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
        (computeFutureOfFuel (min N (typeCompilationFuel left))
          (left.reannotate alphabet))
        (computeFutureOfFuel (min N (typeCompilationFuel right))
          (right.reannotate alphabet))
        (compileTypeFuel_futureTargetsAreEdgeTargets N left)
        (compileTypeFuel_explicitOnlyAtAccepting N left)
        (compileTypeFuel_futureTargetsAreEdgeTargets N right)
        (compileTypeFuel_explicitOnlyAtAccepting N right)
        (compileTypeFuel_referencesClosed N left hLeftLe hLeftDisjoint)
        (compileTypeFuel_referencesClosed N right hRightLe hRightDisjoint)
        (by rw [← hParEq]; exact hParentClosed)
        q1 q2 (by rw [hLeftFragEq]; exact hq1) (by rw [hRightFragEq]; exact hq2)
      rw [hParent, hParEq] at hVisited
      have hCases := hReach hVisited
      rcases Finset.mem_insert.mp hCases with rfl | hRest
      · -- the done state offers nothing and carries no product term
        exfalso
        rw [hParent, hParEq] at hContrib
        have hShape := buildParallelAutomaton_final_edge_shape
          alphabet left.alphabet right.alphabet interface
          (compileTypeFuel N left) (compileTypeFuel N right)
          (compileTypeFuel N (left.reannotate alphabet))
          (compileTypeFuel N (right.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
          (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
          (computeFutureOfFuel (min N (typeCompilationFuel left))
            (left.reannotate alphabet))
          (computeFutureOfFuel (min N (typeCompilationFuel right))
            (right.reannotate alphabet))
        have hInfoFinal : stateProductInfo
            (PactType.par alphabet left right interface)
            TypeAutomatonState.final = none := by
          simp only [stateProductInfo, hFuel, stateProductInfoFuel]
        rw [hInfoFinal, Finset.union_empty] at hContrib
        rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hContrib
        obtain ⟨edge, hEdge, hMem⟩ := hContrib
        obtain ⟨hCurrent, hFuture⟩ := hShape edge
          (Finset.mem_filter.mp hEdge).1 (Finset.mem_filter.mp hEdge).2
        rw [hCurrent, hFuture] at hMem
        simp at hMem
      rcases Finset.mem_union.mp hRest with hPairOrRight | hLeftSurv
      · rcases Finset.mem_union.mp hPairOrRight with hPair | hRightSurv
        · -- a reachable product state: its own product term, bounded by
          -- same-cycle monotonicity in each component
          obtain ⟨pair, hPairMem, rfl⟩ := Finset.mem_image.mp hPair
          obtain ⟨hFst, hSnd⟩ := Finset.mem_product.mp hPairMem
          have hInfoPair : stateProductInfo
              (PactType.par alphabet left right interface)
              (.pair pair.1 pair.2) =
              some (interface, left, right, pair.1, pair.2) := by
            simp only [stateProductInfo, hFuel, stateProductInfoFuel]
          rw [hInfoPair] at hContrib
          rcases Finset.mem_union.mp hContrib with hOffers | hProduct
          · -- a synchronized product edge publishes only component offers
            rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hOffers
            obtain ⟨edge, hEdgeMem, hActionMem⟩ := hOffers
            have hEdge := (Finset.mem_filter.mp hEdgeMem).1
            have hSrc := (Finset.mem_filter.mp hEdgeMem).2
            rw [hParent, hParEq] at hEdge
            have hShapes := buildParallelAutomaton_outgoing_pair
              alphabet left.alphabet right.alphabet interface
              (compileTypeFuel N left) (compileTypeFuel N right)
              (compileTypeFuel N (left.reannotate alphabet))
              (compileTypeFuel N (right.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
              (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
              (computeFutureOfFuel (min N (typeCompilationFuel left))
                (left.reannotate alphabet))
              (computeFutureOfFuel (min N (typeCompilationFuel right))
                (right.reannotate alphabet))
              pair.1 pair.2 edge hEdge hSrc
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            -- the gate transfers to each child by parallel compatibility
            have hGateLeft : action ∈ left.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_left hCompatible
                (by simpa [PactType.alphabet] using hGate)
            have hGateRight : action ∈ right.alphabet.actions :=
              PactTypeAlphabet.parent_actions_subset_right hCompatible
                (by simpa [PactType.alphabet] using hGate)
            -- a component edge's own current sits in that component's menu
            have hLeftIn : ∀ (le : AutomatonFragmentEdge),
                le ∈ resolveAutomatonEdgesWith (compileTypeFuel N left)
                  (computeFutureOfFuel (min N (typeCompilationFuel left)) left) →
                le.source = pair.1 → le.label.semantic ≠ TypeLabel.tock →
                action ∈ le.current →
                action ∈ computeFutureOf left pair.1 := by
              intro le hle hlSrc hlTock hIn
              refine offersAt_subset_computeFutureOf left pair.1 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateLeft⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hle
              obtain ⟨orig, hOrig, rfl⟩ := hle
              simp only at hlSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hlSrc⟩, ?_⟩
              · rw [← hLeftFragEq]; exact hOrig
              · simp only at hlTock
                rw [if_neg hlTock]
                exact Finset.mem_union_left _ hIn
            have hRightIn : ∀ (re : AutomatonFragmentEdge),
                re ∈ resolveAutomatonEdgesWith (compileTypeFuel N right)
                  (computeFutureOfFuel (min N (typeCompilationFuel right))
                    right) →
                re.source = pair.2 → re.label.semantic ≠ TypeLabel.tock →
                action ∈ re.current →
                action ∈ computeFutureOf right pair.2 := by
              intro re hre hrSrc hrTock hIn
              refine offersAt_subset_computeFutureOf right pair.2 ?_
              refine Finset.mem_filter.mpr ⟨?_, hGateRight⟩
              simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hre
              obtain ⟨orig, hOrig, rfl⟩ := hre
              simp only at hrSrc hIn
              rw [PendingAutomaton.offersAt, Finset.mem_biUnion]
              refine ⟨orig, Finset.mem_filter.mpr ⟨?_, hrSrc⟩, ?_⟩
              · rw [← hRightFragEq]; exact hOrig
              · simp only at hrTock
                rw [if_neg hrTock]
                exact Finset.mem_union_left _ hIn
            -- every product edge resolves its future by pointer, never by an
            -- explicit menu, so `offersAt` reads only its current offers
            have hFutureShape : ∀ e ∈ (compileTypeFuel (N + 1)
                (PactType.par alphabet left right interface)).edges,
                e.source = TypeAutomatonState.pair pair.1 pair.2 →
                e.label.semantic ≠ TypeLabel.tock →
                ∀ offers, e.future ≠ FutureSpec.explicit offers := by
              intro e he heSrc hTock offers hExplicit
              have hAcc := compileTypeFuel_explicitOnlyAtAccepting (N + 1)
                (PactType.par alphabet left right interface) e he hTock offers
                hExplicit
              -- the parallel fragment accepts only at the done state, whose
              -- source cannot be the product state we are visiting
              rw [hParEq] at hAcc he
              simp only [buildParallelAutomaton, finishAutomatonFragment,
                Finset.mem_singleton] at hAcc
              obtain ⟨-, hFuture⟩ := buildParallelAutomaton_final_edge_shape
                alphabet left.alphabet right.alphabet interface
                (compileTypeFuel N left) (compileTypeFuel N right)
                (compileTypeFuel N (left.reannotate alphabet))
                (compileTypeFuel N (right.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel left)) left)
                (computeFutureOfFuel (min N (typeCompilationFuel right)) right)
                (computeFutureOfFuel (min N (typeCompilationFuel left))
                  (left.reannotate alphabet))
                (computeFutureOfFuel (min N (typeCompilationFuel right))
                  (right.reannotate alphabet)) e he hAcc
              rw [hFuture] at hExplicit
              injection hExplicit with hOffers
              rw [heSrc] at hAcc
              simp at hAcc
            -- a contributing edge is never a clock edge
            by_cases hEdgeTock : edge.label.semantic = TypeLabel.tock
            · rw [if_pos hEdgeTock] at hActionMem; simp at hActionMem
            rw [if_neg hEdgeTock] at hActionMem
            rcases hShapes with
              ⟨le, hle, re, hre, hlSrc, hrSrc, hCur, hLbl, hSync, -⟩ |
              ⟨re, hre, hrSrc, hCur, hLbl, -⟩ | ⟨le, hle, hlSrc, hCur, hLbl, -⟩
            · -- a synchronized product edge hides a union of component offers
              obtain ⟨hlTock, hrTock⟩ := sync_components_not_tock
                left.alphabet right.alphabet interface hSync
                (by rw [← hLbl]; exact hEdgeTock)
              have hRaw : action ∈ le.current ∪ re.current := by
                rcases Finset.mem_union.mp hActionMem with hCur' | hFut
                · rw [hCur] at hCur'
                  exact (Finset.mem_filter.mp hCur').1
                · cases hFut' : edge.future with
                  | explicit offers =>
                      exact absurd hFut' (hFutureShape edge (by
                        rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                  | «at» s r => rw [hFut'] at hFut; simp at hFut
              rcases Finset.mem_union.mp hRaw with hL | hR
              · exact Finset.mem_union_left _
                  (hLeftMono (hLeftIn le hle hlSrc hlTock hL))
              · exact Finset.mem_union_right _
                  (hRightMono (hRightIn re hre hrSrc hrTock hR))
            · -- the left component completed: only right offers appear
              refine Finset.mem_union_right _ (hRightMono
                (hRightIn re hre hrSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
            · -- the right component completed: only left offers appear
              refine Finset.mem_union_left _ (hLeftMono
                (hLeftIn le hle hlSrc (by rw [← hLbl]; exact hEdgeTock) ?_))
              rcases Finset.mem_union.mp hActionMem with hCur' | hFut
              · rw [hCur] at hCur'; exact hCur'
              · cases hFut' : edge.future with
                | explicit offers =>
                    exact absurd hFut' (hFutureShape edge (by
                      rw [hParEq]; exact hEdge) hSrc hEdgeTock offers)
                | «at» s r => rw [hFut'] at hFut; simp at hFut
          · -- the product term at a reachable pair
            simp only at hProduct
            rw [computeFutureOfFuel_eq_of_sufficient left pair.1 hLeftLe le_rfl,
              computeFutureOfFuel_eq_of_sufficient right pair.2 hRightLe
                le_rfl] at hProduct
            have hLeftMono := computeFutureOf_mono_of_futureReachable left
              hLeftDisjoint hq1
              (by rw [← hLeftFragEq]; exact hFst)
            have hRightMono := computeFutureOf_mono_of_futureReachable right
              hRightDisjoint hq2
              (by rw [← hRightFragEq]; exact hSnd)
            have hHide : hideTypeOffers interface
                (computeFutureOf left pair.1 ∪ computeFutureOf right pair.2) ⊆
                computeFutureOf left pair.1 ∪ computeFutureOf right pair.2 := by
              intro a ha
              exact (Finset.mem_filter.mp ha).1
            exact Finset.union_subset_union hLeftMono hRightMono
              (hHide hProduct)
        · -- a right survivor sub-reach: collapses to the re-signed component's
          -- menu by the survivor transport, then to the component's own
          obtain ⟨tEntry, htEntry, hInSub⟩ := Finset.mem_biUnion.mp hRightSurv
          refine Finset.mem_union_right _ ?_
          obtain ⟨htEntry, htAcc⟩ := Finset.mem_filter.mp htEntry
          have hCollapse : action ∈
              computeFutureOf (right.reannotate alphabet) tEntry := by
            rw [← computeFutureOf_par_survivorRight alphabet left right
              interface hLeftDisjoint hRightDisjoint tEntry
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).1,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                  _ q2 _ (by rw [hRightFragEq]; exact hq2)
                  (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                    hRightDisjoint s hs)) htEntry)
              (by
                rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                  (typeCompilationFuel (right.reannotate alphabet)) right
                  hRightDisjoint alphabet).2.2,
                  typeCompilationFuel_reannotate, ← hRightFragEq]
                exact htAcc)]
            rw [computeFutureOf, hFuel, computeFutureOfFuel]
            refine Finset.mem_filter.mpr ⟨?_, hGate⟩
            refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
            rw [hParEq]
            exact hInSub
          have htStates : tEntry ∈
              (compileTypeFuel (typeCompilationFuel right) right).states := by
            rw [← hRightFragEq]
            exact (PendingAutomaton.futureReachable_subset_of_reference_closed
              _ q2 _ (by rw [hRightFragEq]; exact hq2)
              (fun s hs => compileTypeFuel_referencesClosed N right hRightLe
                hRightDisjoint s hs)) htEntry
          have hMono := computeFutureOf_mono_of_futureReachable right
            hRightDisjoint hq2
            (by rw [← hRightFragEq]; exact htEntry)
          exact hMono (hSurvRight tEntry (by rw [← hRightFragEq]; exact htEntry)
            hCollapse)
      · -- the mirror, for a left survivor sub-reach
        obtain ⟨sEntry, hsEntry, hInSub⟩ := Finset.mem_biUnion.mp hLeftSurv
        obtain ⟨hsEntry, hsAcc⟩ := Finset.mem_filter.mp hsEntry
        refine Finset.mem_union_left _ ?_
        have hCollapse : action ∈
            computeFutureOf (left.reannotate alphabet) sEntry := by
          rw [← computeFutureOf_par_survivorLeft alphabet left right
            interface hLeftDisjoint hRightDisjoint sEntry
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).1,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact (PendingAutomaton.futureReachable_subset_of_reference_closed
                _ q1 _ (by rw [hLeftFragEq]; exact hq1)
                (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
                  hLeftDisjoint s hs)) hsEntry)
            (by
              rw [(CompiledShape.compileTypeFuel_shapeEq_reannotate
                (typeCompilationFuel (left.reannotate alphabet)) left
                hLeftDisjoint alphabet).2.2,
                typeCompilationFuel_reannotate, ← hLeftFragEq]
              exact hsAcc)]
          rw [computeFutureOf, hFuel, computeFutureOfFuel]
          refine Finset.mem_filter.mpr ⟨?_, hGate⟩
          refine Finset.mem_biUnion.mpr ⟨visited, ?_, hContrib⟩
          rw [hParEq]
          exact hInSub
        have hsStates : sEntry ∈
            (compileTypeFuel (typeCompilationFuel left) left).states := by
          rw [← hLeftFragEq]
          exact (PendingAutomaton.futureReachable_subset_of_reference_closed
            _ q1 _ (by rw [hLeftFragEq]; exact hq1)
            (fun s hs => compileTypeFuel_referencesClosed N left hLeftLe
              hLeftDisjoint s hs)) hsEntry
        have hMono := computeFutureOf_mono_of_futureReachable left
          hLeftDisjoint hq1
          (by rw [← hLeftFragEq]; exact hsEntry)
        exact hMono (hSurvLeft sEntry (by rw [← hLeftFragEq]; exact hsEntry)
          hCollapse)
    rw [← hFilterEq]
    exact Finset.mem_filter.mpr ⟨hInMenus, hGate⟩
  · intro action hAction
    have hMemRaw := hRhsSubset hAction
    refine Finset.mem_filter.mpr ⟨hMemRaw, ?_⟩
    have hIn : action ∈ (computeFutureOf left q1 ∪ computeFutureOf right q2).filter
        (fun a => a ∈ (PactType.par alphabet left right interface).alphabet.actions) := by
      rw [hFilterEq]; exact hAction
    exact (Finset.mem_filter.mp hIn).2

/-- The compiled parallel product, unfolded at its own fuel. -/
theorem compileTypeFuel_par_eq (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    compileTypeFuel (typeCompilationFuel (.par alphabet left right interface))
        (.par alphabet left right interface) =
      buildParallelAutomaton alphabet left.alphabet right.alphabet interface
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) left)
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right)) right)
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right))
          (left.reannotate alphabet))
        (compileTypeFuel
          (max (typeCompilationFuel left) (typeCompilationFuel right))
          (right.reannotate alphabet))
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel left)) left)
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel right)) right)
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel left)) (left.reannotate alphabet))
        (computeFutureOfFuel
          (min (max (typeCompilationFuel left) (typeCompilationFuel right))
            (typeCompilationFuel right)) (right.reannotate alphabet)) := by
  have hFuelEq : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  rw [hFuelEq]
  simp only [compileTypeFuel]

/-- The completed product state offers nothing: its only edges are the idle
self-loops, which carry no current offers and name no further state. -/
theorem computeFutureOf_par_final (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface) :
    computeFutureOf (.par alphabet left right interface) .final = ∅ := by
  classical
  have hFuel : typeCompilationFuel (.par alphabet left right interface) =
      max (typeCompilationFuel left) (typeCompilationFuel right) + 1 := by
    simp only [typeCompilationFuel]; omega
  have hShape : ∀ edge ∈ (compileTypeFuel
      (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
      (PactType.par alphabet left right interface)).edges,
      edge.source = TypeAutomatonState.final →
      edge.current = ∅ ∧ edge.future = .explicit ∅ := by
    intro edge hEdge hSource
    simp only [compileTypeFuel] at hEdge
    exact buildParallelAutomaton_final_edge_shape _ _ _ _ _ _ _ _ _ _ _ _
      edge hEdge hSource
  rw [computeFutureOf, hFuel, computeFutureOfFuel]
  set pending : PendingAutomaton :=
    { states := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).states
      edges := (compileTypeFuel
        (max (typeCompilationFuel left) (typeCompilationFuel right) + 1)
        (PactType.par alphabet left right interface)).edges }
    with hPendingDef
  have hRefs : pending.referencedStates TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro target hTarget
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at hTarget
    obtain ⟨edge, hEdge, hTargetMem⟩ := hTarget
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    rw [(hShape edge hMem hSource).2] at hTargetMem
    simp at hTargetMem
  have hOffers : pending.offersAt TypeAutomatonState.final = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro action hAction
    rw [PendingAutomaton.offersAt, Finset.mem_biUnion] at hAction
    obtain ⟨edge, hEdge, hActionMem⟩ := hAction
    have hMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    obtain ⟨hCurrent, hFuture⟩ := hShape edge hMem hSource
    rw [hCurrent, hFuture] at hActionMem
    simp at hActionMem
  rw [PendingAutomaton.futureReachable_eq_singleton_of_referencedStates_eq_empty
      pending TypeAutomatonState.final hRefs]
  simp only [Finset.singleton_biUnion, hOffers,
    stateProductInfo_par_final alphabet left right interface,
    Finset.empty_union, Finset.filter_empty]

/-- H-menus at a parallel product, by the four families of related states. -/
theorem futureOffersAgree_par (alphabet : PactTypeAlphabet)
    (left right : PactType) (interface : Interface)
    (hLeftDisjoint : left.OfferBranchesDisjoint)
    (hRightDisjoint : right.OfferBranchesDisjoint)
    (hCompatible : PactTypeAlphabet.ParallelCompatible alphabet left.alphabet
      right.alphabet interface)
    (hSurvLeft : ∀ q1 : TypeAutomatonState,
      ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel left) left).states,
          (compileTypeFuel (typeCompilationFuel left) left).edges⟩ :
          PendingAutomaton).futureReachable q1,
        computeFutureOf (left.reannotate alphabet) s ⊆ computeFutureOf left s)
    (hSurvRight : ∀ q2 : TypeAutomatonState,
      ∀ t ∈ (⟨(compileTypeFuel (typeCompilationFuel right) right).states,
          (compileTypeFuel (typeCompilationFuel right) right).edges⟩ :
          PendingAutomaton).futureReachable q2,
        computeFutureOf (right.reannotate alphabet) t ⊆ computeFutureOf right t)
    (hLeft : FutureOffersAgree left) (hRight : FutureOffersAgree right)
    (hLeftResign : FutureOffersAgree (left.reannotate alphabet))
    (hRightResign : FutureOffersAgree (right.reannotate alphabet)) :
    FutureOffersAgree (.par alphabet left right interface) := by
  classical
  intro residual state hRelated
  rcases relationMembership_par_cases alphabet left right interface hRelated with
    ⟨q1, q2, rL, rR, hEq, hL, hR⟩ | ⟨q1, rL, hEq, hL, hNotAcc⟩ |
      ⟨q2, rR, hEq, hR, hNotAcc⟩ | hFinal
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_pair alphabet left right interface hLeftDisjoint
        hRightDisjoint hCompatible q1 q2 (hSurvLeft q1) (hSurvRight q2)
        (relationMembership_state_mem left _ q1 hLeftDisjoint hL)
        (relationMembership_state_mem right _ q2 hRightDisjoint hR),
      hLeft hL, hRight hR, typeFutureOffers_parallel]
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorLeft alphabet left right interface
        hLeftDisjoint hRightDisjoint q1
        (relationMembership_state_mem (left.reannotate alphabet) _ q1
          (reannotate_offerBranchesDisjoint left alphabet hLeftDisjoint) hL)
        hNotAcc]
    exact hLeftResign hL
  · injection hEq with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_survivorRight alphabet left right interface
        hLeftDisjoint hRightDisjoint q2
        (relationMembership_state_mem (right.reannotate alphabet) _ q2
          (reannotate_offerBranchesDisjoint right alphabet hRightDisjoint) hR)
        hNotAcc]
    exact hRightResign hR
  · injection hFinal with hResidual hState
    subst hResidual
    subst hState
    rw [computeFutureOf_par_final alphabet left right interface]
    simp only [typeFutureOffers, typeFutureOffersFuel]

#print axioms stateProductInfo_par_pair
#print axioms stateProductInfo_par_final
#print axioms compileTypeFuel_par_eq
#print axioms buildParallelAutomaton_final_edge_shape
#print axioms computeFutureOf_par_final

/-- The paper's survivor bullet: the re-signed component's menu at a state is
bounded by the component's own.  The state is related by Lemma 4.5's
reachability clause, the re-signing transport moves that witness across, and
`<dead-declarations-inert>` equates the two menus. -/
theorem survivorMenuBound (component : PactType) (target : PactTypeAlphabet)
    (bound : List String) (hWF : TypeWellFormedIn bound component)
    (hTargetWF : target.WellFormed)
    (hNoInterface : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces component)
    (hComponent : FutureOffersAgree component)
    (hResign : FutureOffersAgree (component.reannotate target))
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet component (compileType component)) residual state)
    (hActions : target.actions ⊆ residual.alphabet.actions)
    (hResidualWF : residual.AlphabetWellFormed) :
    computeFutureOf (component.reannotate target) state ⊆
      computeFutureOf component state := by
  classical
  obtain ⟨theta, hThetaRelated, hLive⟩ :=
    survivorTransport_all component bound hWF target hTargetWF hNoInterface
      residual state hRelated
  rw [hResign hThetaRelated, hComponent hRelated,
    ← PactType.liveEq_preserves_futOff hLive]
  exact typeFutureOffers_reannotate_subset residual target hResidualWF hActions

/-- Lemma 4.5's reachability clause, in the same-cycle form the menus need: from
a related state, every state reachable before the next clock is related.  The
marker escape of the closure lemma cannot fire, because a closed type compiles
without marker edges. -/
theorem futureReachable_related
    (processType : PactType)
    (hClosed : PactType.AllVariablesBound [] processType)
    (hDisjoint : processType.OfferBranchesDisjoint)
    (hResign : ∀ (component : PactType) (target : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel component →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (component.reannotate target))
    (hAccepting : ∀ (component : PactType) (target : PactTypeAlphabet)
      (fuel : Nat), component.OfferBranchesDisjoint →
      (compileTypeFuel fuel (component.reannotate target)).accepting =
        (compileTypeFuel fuel component).accepting)
    (hResignDisjoint : ∀ (component : PactType) (target : PactTypeAlphabet),
      component.OfferBranchesDisjoint →
      (component.reannotate target).OfferBranchesDisjoint)
    (hSelectingDisjoint : ∀ (alphabet : PactTypeAlphabet)
      (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      PactType.OfferBranchesDisjointBranches branches →
      (parallelTypeBranchesSelecting alphabet selected
        branches).OfferBranchesDisjoint)
    {residual : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership
      (buildRelationSet processType (compileType processType)) residual state) :
    ∀ p ∈ (⟨(compileTypeFuel (typeCompilationFuel processType)
          processType).states,
        (compileTypeFuel (typeCompilationFuel processType)
          processType).edges⟩ : PendingAutomaton).futureReachable state,
      ∃ rho, relationMembership
        (buildRelationSet processType (compileType processType)) rho p := by
  classical
  set frag := compileTypeFuel (typeCompilationFuel processType) processType
    with hFrag
  set pending : PendingAutomaton := ⟨frag.states, frag.edges⟩ with hPending
  -- the related states form a reference-closed set
  set allowed : Finset TypeAutomatonState :=
    frag.states.filter (fun p => ∃ rho, relationMembership
      (buildRelationSet processType (compileType processType)) rho p)
    with hAllowed
  have hStep : ∀ s ∈ allowed, pending.referencedStates s ⊆ allowed := by
    intro s hs t ht
    obtain ⟨hsStates, rho, hRho⟩ := Finset.mem_filter.mp hs
    rw [PendingAutomaton.referencedStates, Finset.mem_biUnion] at ht
    obtain ⟨edge, hEdge, hMem⟩ := ht
    have hEdgeMem := (Finset.mem_filter.mp hEdge).1
    have hSource := (Finset.mem_filter.mp hEdge).2
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hMem; simp at hMem
    rw [if_neg hTock] at hMem
    have hTargetEq : t = edge.target := by
      cases hFut : edge.future with
      | explicit offers => rw [hFut] at hMem; simp at hMem
      | «at» s' r =>
          rw [hFut] at hMem
          simp only [Finset.mem_singleton] at hMem
          rw [hMem, compileTypeFuel_futureTargetsAreEdgeTargets
            (typeCompilationFuel processType) processType edge hEdgeMem s' r
            hFut]
    subst hTargetEq
    rcases buildRelationSetCoreFuel_edge_target_mem hResign hAccepting
        hResignDisjoint hSelectingDisjoint (typeCompilationFuel processType)
        processType le_rfl hDisjoint edge hEdgeMem with
      ⟨rho', hRho'⟩ | ⟨markerName, hMarker⟩
    · refine Finset.mem_filter.mpr ⟨?_, rho', hRho'⟩
      exact compileTypeFuel_edgeTargetsInStates _ _ le_rfl hDisjoint edge
        hEdgeMem
    · exact absurd hMarker (compileTypeFuel_noMarker_of_closed _ processType
        hClosed markerName edge hEdgeMem)
  intro p hp
  have hSeed : state ∈ allowed :=
    Finset.mem_filter.mpr
      ⟨relationMembership_state_mem processType residual state hDisjoint
        hRelated, residual, hRelated⟩
  exact (Finset.mem_filter.mp
    (PendingAutomaton.futureReachable_subset_of_reference_closed pending state
      allowed hSeed hStep hp)).2

/-- The survivor bound over a whole same-cycle reach: Lemma 4.5's reachability
clause makes every reachable state related, and the survivor bullet then bounds
its re-signed menu. -/
theorem survivorMenuBound_reach (component : PactType)
    (target : PactTypeAlphabet) (bound : List String)
    (hWF : TypeWellFormedIn bound component)
    (hClosed : PactType.AllVariablesBound [] component)
    (hDisjoint : component.OfferBranchesDisjoint)
    (hResign : ∀ (c : PactType) (a : PactTypeAlphabet)
      (residual : PactType) (state : TypeAutomatonState) (fuel : Nat),
      (residual, state) ∈ buildRelationSetCoreFuel fuel c →
      ∃ theta, (theta, state) ∈
        buildRelationSetCoreFuel fuel (c.reannotate a))
    (hAccepting : ∀ (c : PactType) (a : PactTypeAlphabet) (fuel : Nat),
      c.OfferBranchesDisjoint →
      (compileTypeFuel fuel (c.reannotate a)).accepting =
        (compileTypeFuel fuel c).accepting)
    (hResignDisjoint : ∀ (c : PactType) (a : PactTypeAlphabet),
      c.OfferBranchesDisjoint → (c.reannotate a).OfferBranchesDisjoint)
    (hSelectingDisjoint : ∀ (a : PactTypeAlphabet)
      (selected : BareMessage × PactType)
      (branches : List (BareMessage × PactType)),
      PactType.OfferBranchesDisjointBranches branches →
      (parallelTypeBranchesSelecting a selected branches).OfferBranchesDisjoint)
    (hTargetWF : target.WellFormed)
    (hNoInterface : ∀ action ∈ target.actions,
      action.1 ∉ PactType.ParallelInterfaces component)
    (hComponent : FutureOffersAgree component)
    (hResignAgree : FutureOffersAgree (component.reannotate target))
    (hResidualWF : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet component (compileType component))
        residual state → residual.AlphabetWellFormed)
    (hResidualActions : ∀ {residual : PactType} {state : TypeAutomatonState},
      relationMembership (buildRelationSet component (compileType component))
        residual state → target.actions ⊆ residual.alphabet.actions)
    {seed : PactType} {q : TypeAutomatonState}
    (hSeed : relationMembership
      (buildRelationSet component (compileType component)) seed q) :
    ∀ s ∈ (⟨(compileTypeFuel (typeCompilationFuel component) component).states,
        (compileTypeFuel (typeCompilationFuel component) component).edges⟩ :
        PendingAutomaton).futureReachable q,
      computeFutureOf (component.reannotate target) s ⊆
        computeFutureOf component s := by
  intro s hs
  obtain ⟨rho, hRho⟩ := futureReachable_related component hClosed hDisjoint
    hResign hAccepting hResignDisjoint hSelectingDisjoint hSeed s hs
  exact survivorMenuBound component target bound hWF hTargetWF hNoInterface
    hComponent hResignAgree hRho (hResidualActions hRho) (hResidualWF hRho)

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
            (offerBranchesDisjoint_of_ownership left
              hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.1
              hLeftWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            hWF resignTransport_relationMembership
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
        obtain ⟨hLeftResignWF, hRightResignWF⟩ := typeWellFormedIn_survivor hWF
        have hLeftResign :=
          ih _ hLeftResignFuel bound (left.reannotate alphabet) rfl hLeftResignWF
        have hRightResign :=
          ih _ hRightResignFuel bound (right.reannotate alphabet) rfl
            hRightResignWF
        refine ⟨?_, ?_, ?_⟩
        · sorry -- current-offer correspondence, `.par`
        · sorry -- same-cycle completion, `.par`
        · exact futureOffersAgree_par alphabet left right interface
            (offerBranchesDisjoint_of_ownership left
              hLeftWF.2.2.2.2.2.2.2.2.2.1 hLeftWF.2.2.2.2.2.2.2.2.2.2.1
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
            (fun q => survivorMenuBound_par left alphabet bound hLeftWF q)
            (fun q => survivorMenuBound_par right alphabet bound hRightWF q)
            hLeft.2.2 hRight.2.2 hLeftResign.2.2 hRightResign.2.2
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
        · exact futureOffersAgree_xoffer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.xoffer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun branch hMem => by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact PactType.branch_alphabet_eq_of_mem h.2.2.2 hMem)
            hElse.2.2 (fun branch hMem => (hBranch branch hMem).2.2)
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
        · refine futureOffersAgree_offer alphabet elseType branches
            (offerBranchesDisjoint_of_ownership
              (.offer alphabet elseType branches)
              hWF.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.1
              hWF.2.2.2.2.2.2.2.2.2.2.2.1 hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (by
              have h := hWF.1
              simp only [PactType.AlphabetWellFormed] at h
              exact h.2.1)
            (fun selected hMem =>
              parallelTypeBranchesSelecting_alphabet_eq_of_mem hMem)
            ?_ hElse.2.2 (fun selected hMem => (hSelected selected hMem).2.2)
          -- The generated product's menu, from the raw branch bodies.  The gate
          -- is exactly the declaredness the syntax lemma needs.
          intro hGate selected hMem
          have h := hWF.1
          simp only [PactType.AlphabetWellFormed] at h
          exact typeFutureOffers_parallelTypeBranchesSelecting alphabet selected
            branches hGate
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).1)
            (fun b hb => (offerBranchesWellFormed_of_mem h.2.2.2 hb).2)

end


end Pact
