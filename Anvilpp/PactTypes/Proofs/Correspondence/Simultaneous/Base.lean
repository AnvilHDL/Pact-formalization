import Anvilpp.PactTypes.Proofs.Automata.MenuDependenciesLemmas
import Anvilpp.PactTypes.Proofs.Correspondence.Cases.Base
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.NewMainHelpers
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.OwnershipTransport
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.TypeWellFormedIn
import Anvilpp.PactTypes.Proofs.Correspondence.Helpers.SurvivorTransport

/-!
The three correspondence predicates, the base fragments, the compiled-guard
and edge-locality machinery, reachability transport into child copies, and the
relation's carrier and target lemmas.
-/

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

/-- Current-offer correspondence: a step and an edge that carry the same
environment, label and current offer have related targets, in both directions.
This is the current-and-target stage. Full offer correspondence is established
constructor by constructor after the same-rank menu equation. -/
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
      hFragment.menuStep state ⊆ {a, b})
    (hOffersA : hFragment.offersAt a = ∅)
    (hOffersB : hFragment.offersAt b = ∅)
    (hProductA : stateProductInfo processType a = none)
    (hProductB : stateProductInfo processType b = none)
    (hNoLinks : compileTypeMenuLinksFuel
      (min (fuel + 1) (typeCompilationFuel processType)) processType = ∅ := by
      simp [typeCompilationFuel, compileTypeMenuLinksFuel]) :
    computeFutureOfFuel (fuel + 1) processType a = ∅ := by
  classical
  have hReach : hFragment.futureReachable a ⊆ ({a, b} : Finset TypeAutomatonState) :=
    hFragment.futureReachable_subset_of_menu_closed a {a, b}
      (by simp) hClosed
  simp only [computeFutureOfFuel, hNoLinks, PendingAutomaton.withMenuDependencies_empty]
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
    simp only [PendingAutomaton.menuStep, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hReference⟩ := hReference
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩ <;>
      · rw [← hEq] at hReference
        simp only [AutomatonConstructionLabel.semantic, TypeLabel.progress,
          TypeLabel.silent] at hReference
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
          TypeLabel.silent] at hAction
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_union, Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hAction⟩ := hAction
    rcases hEdgeMem with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩ <;>
      · rw [← hEq] at hAction
        simp [AutomatonConstructionLabel.semantic, TypeLabel.progress,
          TypeLabel.silent] at hAction
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
    simp only [PendingAutomaton.menuStep, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hReference
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hReference⟩ := hReference
    obtain ⟨_, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hReference
    simp only [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hReference
    simp_all
  · refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro action hAction
    simp only [PendingAutomaton.offersAt, compileTypeFuel,
      finishAutomatonFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hAction
    obtain ⟨edge, ⟨hEdgeMem, -⟩, hAction⟩ := hAction
    obtain ⟨_, _, hEq⟩ := hEdgeMem
    rw [← hEq] at hAction
    simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hAction
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

/-- An undeclared atomic head has an empty projected menu, although it may wait. -/
lemma computeFutureOf_message_root_of_not_declared
    {alphabet : PactTypeAlphabet} (msg : MessageId) (dir : MessageDir)
    (hDeclared : (msg, dir) ∉ alphabet.actions) :
    computeFutureOf (.message alphabet msg dir) .root = ∅ := by
  simp [computeFutureOf_message_root_projected, hDeclared]

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

private lemma action_declared_of_hasNeed {alphabet : PactTypeAlphabet}
    {env : TypeEnvironment} (msg : MessageId) (dir : MessageDir)
    (hEnv : env.WellFormed alphabet) (hNeed : env.hasNeed (msg, dir)) :
    (msg, dir) ∈ alphabet.actions := by
  obtain ⟨⟨m, d⟩, hMem, hEq⟩ := Finset.mem_image.mp (hEnv.2.2.1 hNeed)
  cases d <;> cases dir <;> simp_all [typeNeed, MessageDir.invert]

/-- Admissible environments and projected offer fields put every base step
and edge inside the fixed transition alphabet. -/
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
        simp
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
      | action _ _ _ _ cond =>
          have hA := action_declared_of_hasNeed msg dir cond.1 cond.2
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (message_mem_labels hA)
            (mem_localOfferSummaries_of_subset ?_ ?_)
          · exact Finset.inter_subset_right
          · simp
      | action_wait _ _ _ _ cond =>
          refine mem_transitionAlphabet_of
            (PactTypeAlphabet.mem_localEnvironments_of_wellFormed cond.1)
            (silent_mem_labels _)
            (mem_localOfferSummaries_of_subset ?_ ?_)
          · exact Finset.inter_subset_right
          · have hFut : typeFutureOffers (PactType.message alphabet msg dir) ⊆
                alphabet.actions := by
              by_cases hA : (msg, dir) ∈ alphabet.actions <;>
                simp [typeFutureOffers, typeFutureOffersFuel, hA]
            exact Finset.Subset.trans Finset.sdiff_subset hFut
    · have hEnvMem := compileType_base_edge_env_mem
        (message_edge_families alphabet msg dir) hEdge
      have hCurrentSub : ({(msg, dir)} ∩ alphabet.actions : Finset BareMessage) ⊆
          alphabet.actions := Finset.inter_subset_right
      rcases compileType_message_edge_cases msg dir hEdge with
        ⟨-, -, hLabel, hCurrent, hFuture, hNeed⟩ |
        ⟨-, -, hLabel, hCurrent, hFuture, -, -⟩ |
        ⟨hSource, -, -, -, -, -⟩
      · subst hLabel; subst hCurrent; subst hFuture
        have hDeclared := action_declared_of_hasNeed msg dir
          (PactTypeAlphabet.environment_wellFormed hEnvMem) hNeed
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
          simp
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
          simp
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
          simp
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
          simp
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
          simp
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

/-- Forgetting the future equality gives the current-and-target stage. -/
theorem TypeAutomatonStepCorrespondence.toCurrent {ty : PactType}
    (h : TypeAutomatonStepCorrespondence ty) : CurrentOfferCorrespondence ty := by
  constructor
  · intro rho rho' q env label current future hRelated hStep
    obtain ⟨q', hEdge, hTarget⟩ := h.1 hRelated hStep
    exact ⟨q', future, hEdge, hTarget⟩
  · intro rho q q' env label current future hRelated hEdge
    obtain ⟨rho', hStep, hTarget⟩ := h.2 hRelated hEdge
    exact ⟨rho', future, hStep, hTarget⟩

/-- The fixed-target lemma and target coverage give both full-pair simulations. -/
theorem offerCorrespondence_of_stepIff {processType : PactType}
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
    TypeAutomatonStepCorrespondence processType := by
  constructor
  · intro residual residual' state env label offers hRelated hTransition
    have hSymbol := hGuard hRelated (Or.inl ⟨residual', hTransition⟩)
    obtain ⟨state', hEdge, hRelated'⟩ := (hStep hRelated hSymbol).mp hTransition
    exact ⟨state', hEdge, hRelated'⟩
  · intro residual state state' env label offers hRelated hEdge
    have hSymbol := hGuard hRelated (Or.inr ⟨state', hEdge⟩)
    obtain ⟨residual', hRelated'⟩ := hTargets hRelated hEdge
    exact ⟨residual',
      (hStep hRelated hSymbol).mpr ⟨state', hEdge, hRelated'⟩, hRelated'⟩

lemma offerCorrespondence_skip (alphabet : PactTypeAlphabet) :
    TypeAutomatonStepCorrespondence (.skip alphabet) := by
  refine offerCorrespondence_of_stepIff
    (fun hRelated hSymbol => correspondence_skip_stepIff alphabet hRelated hSymbol)
    (skip_guard alphabet) ?_
  intro residual state state' env label offers hRelated hEdge
  rcases offers with ⟨current, future⟩
  obtain ⟨-, hTarget, -, -, -, -⟩ := compileType_skip_edge_cases hEdge
  subst hTarget
  exact ⟨.skip alphabet, by
    simp [relationMembership, buildRelationSet, buildRelationSetCore,
      typeCompilationFuel, buildRelationSetCoreFuel]⟩

lemma offerCorrespondence_message (alphabet : PactTypeAlphabet)
    (msg : MessageId) (dir : MessageDir) :
    TypeAutomatonStepCorrespondence (.message alphabet msg dir) := by
  refine offerCorrespondence_of_stepIff
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

lemma offerCorrespondence_tock (alphabet : PactTypeAlphabet) :
    TypeAutomatonStepCorrespondence (.tock alphabet) := by
  refine offerCorrespondence_of_stepIff
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

lemma offerCorrespondence_progress (alphabet : PactTypeAlphabet)
    (pid : ProcId) :
    TypeAutomatonStepCorrespondence (.progress alphabet pid) := by
  refine offerCorrespondence_of_stepIff
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

lemma offerCorrespondence_var (alphabet : PactTypeAlphabet)
    (name : String) :
    TypeAutomatonStepCorrespondence (.var alphabet name) := by
  refine offerCorrespondence_of_stepIff
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

lemma currentOfferCorrespondence_skip (alphabet : PactTypeAlphabet) :
    CurrentOfferCorrespondence (.skip alphabet) :=
  (offerCorrespondence_skip alphabet).toCurrent

lemma currentOfferCorrespondence_message (alphabet : PactTypeAlphabet) (msg : MessageId) (dir : MessageDir) :
    CurrentOfferCorrespondence (.message alphabet msg dir) :=
  (offerCorrespondence_message alphabet msg dir).toCurrent

lemma currentOfferCorrespondence_tock (alphabet : PactTypeAlphabet) :
    CurrentOfferCorrespondence (.tock alphabet) :=
  (offerCorrespondence_tock alphabet).toCurrent

lemma currentOfferCorrespondence_progress (alphabet : PactTypeAlphabet) (pid : ProcId) :
    CurrentOfferCorrespondence (.progress alphabet pid) :=
  (offerCorrespondence_progress alphabet pid).toCurrent

lemma currentOfferCorrespondence_var (alphabet : PactTypeAlphabet) (name : String) :
    CurrentOfferCorrespondence (.var alphabet name) :=
  (offerCorrespondence_var alphabet name).toCurrent

/-! ### `TypeWF_Γ` descends to every written child -/


/-! ### Reachability transport into a child copy -/

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
          simp only [compileTypeFuel, buildAtomicConjunctiveOfferAutomaton,
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
              refine Or.inr ⟨((indexed.1, compileTypeFuel fuel
                (parallelTypeBranchesFiring alphabet indexed.1 branches)),
                indexed.2), ?_, ?_⟩
              · rw [List.zipIdx_map]
                exact List.mem_map_of_mem hIndexedMem
              · refine Finset.mem_image_of_mem _
                  (ih (parallelTypeBranchesFiring alphabet indexed.1 branches)
                    ?_ entry.1 entry.2 hEntry)
                exact parallelTypeBranchesFiring_offerBranchesDisjoint
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

theorem computeFutureOfFuel_subset_alphabet (fuel : Nat) (processType : PactType)
    (state : TypeAutomatonState) :
    computeFutureOfFuel fuel processType state ⊆ processType.alphabet.actions := by
  cases fuel with
  | zero => simp [computeFutureOfFuel]
  | succ fuel =>
      rw [computeFutureOfFuel]
      intro action hAction
      exact (Finset.mem_filter.mp hAction).2

/-- The stored part of a future field stays within the declared alphabet. -/
def FutureSpec.AlphabetLocal (actions : Finset BareMessage) : FutureSpec → Prop
  | .explicit offers => offers ⊆ actions
  | .at _ _ => True
  | .atUnion offers _ _ => offers ⊆ actions

theorem FutureSpec.AlphabetLocal.resolve {actions : Finset BareMessage}
    {spec : FutureSpec} (hLocal : spec.AlphabetLocal actions)
    (futureAt : TypeAutomatonState → Finset BareMessage)
    (hMenus : ∀ state, futureAt state ⊆ actions) :
    resolveFutureSpec futureAt spec ⊆ actions := by
  cases spec with
  | explicit offers => exact hLocal
  | «at» state removed => exact Finset.Subset.trans Finset.sdiff_subset (hMenus state)
  | atUnion offers state removed =>
      exact Finset.Subset.trans Finset.sdiff_subset
        (Finset.union_subset hLocal (hMenus state))

theorem childFutureSpec_alphabetLocal (index : Nat) (spec : FutureSpec)
    (actions : Finset BareMessage) :
    (childFutureSpec index spec).AlphabetLocal actions ↔ spec.AlphabetLocal actions := by
  cases spec <;> rfl

/-- A child copy changes state references, not the resolved offer set. -/
theorem resolve_childFutureSpec (index : Nat) (spec : FutureSpec)
    (parent child : TypeAutomatonState → Finset BareMessage)
    (hMenus : ∀ state, spec.referenced = some state →
      parent (childState index state) = child state) :
    resolveFutureSpec parent (childFutureSpec index spec) =
      resolveFutureSpec child spec := by
  cases spec with
  | explicit offers => rfl
  | «at» state removed | atUnion offers state removed =>
      simp only [childFutureSpec, resolveFutureSpec, hMenus state rfl]

/-- Current offers and stored future contributions are declared by the type. -/
def EdgeOffersLocal (processType : PactType) : Prop :=
  ∀ edge ∈ (compileTypeFuel (typeCompilationFuel processType)
      processType).edges,
    edge.current ⊆ processType.alphabet.actions ∧
      edge.future.AlphabetLocal processType.alphabet.actions

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
lemma sumBuilder_edge_families (alphabet : PactTypeAlphabet)
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

/-- The sum builder keeps published offers local for any selection labels. -/
lemma sumBuilder_edge_offers (alphabet : PactTypeAlphabet)
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
      edge.future.AlphabetLocal alphabet.actions := by
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (hChild | hChild) | hSelect
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    obtain ⟨hCur, hFut⟩ := hLeft childEdge hChildMem
    rw [hLeftAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    exact (childFutureSpec_alphabetLocal _ _ _).mpr hFut
  · simp only [childPendingEdges, Finset.mem_image] at hChild
    obtain ⟨childEdge, hChildMem, rfl⟩ := hChild
    obtain ⟨hCur, hFut⟩ := hRight childEdge hChildMem
    rw [hRightAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    exact (childFutureSpec_alphabetLocal _ _ _).mpr hFut
  · simp only [Finset.mem_biUnion, Finset.mem_filter] at hSelect
    obtain ⟨environment, -, hMem⟩ := hSelect
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | rfl <;> exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

/-- The fuel-parametrized form of both locality predicates.  The `.par` builder
compiles re-stamped children at the same fuel, and `reannotate` preserves size,
so only an induction on fuel reaches them. -/
def EdgeLocalAt (fuel : Nat) (processType : PactType) : Prop :=
  ∀ edge ∈ (compileTypeFuel fuel processType).edges,
    edge.environment ∈ processType.alphabet.localEnvironments ∧
      edge.current ⊆ processType.alphabet.actions ∧
      edge.future.AlphabetLocal processType.alphabet.actions

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
lemma edgeLocal_skip (alphabet : PactTypeAlphabet) :
    EdgeEnvironmentsLocal (.skip alphabet) ∧ EdgeOffersLocal (.skip alphabet) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image, Finset.mem_filter] at hEdge <;>
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hEdge
  · exact hLocal
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

lemma edgeLocal_var (alphabet : PactTypeAlphabet) (name : String) :
    EdgeEnvironmentsLocal (.var alphabet name) ∧
      EdgeOffersLocal (.var alphabet name) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_image, Finset.mem_filter] at hEdge <;>
    obtain ⟨environment, ⟨hLocal, -⟩, rfl⟩ := hEdge
  · exact hLocal
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

lemma edgeLocal_message (alphabet : PactTypeAlphabet)
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
  · exact ⟨Finset.inter_subset_right, by simp [FutureSpec.AlphabetLocal]⟩
  · exact ⟨Finset.inter_subset_right, by simp [FutureSpec.AlphabetLocal]⟩
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

lemma edgeLocal_tock (alphabet : PactTypeAlphabet) :
    EdgeEnvironmentsLocal (.tock alphabet) ∧ EdgeOffersLocal (.tock alphabet) := by
  classical
  constructor <;> intro edge hEdge <;>
    simp only [typeCompilationFuel, compileTypeFuel, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge <;>
    rcases hEdge with ⟨environment, hLocal, rfl⟩ | ⟨environment, ⟨hLocal, -⟩, rfl⟩
  · split <;> exact hLocal
  · exact hLocal
  · split <;>
      exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

lemma edgeLocal_progress (alphabet : PactTypeAlphabet)
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
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

lemma edgeLocal_choice (alphabet : PactTypeAlphabet)
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
        (compileTypeFuel (typeCompilationFuel right) right)
        (computeFutureOfFuel (typeCompilationFuel left) left)
        (fun state => decide (∃ entry ∈ buildRelationSetCoreFuel
            (typeCompilationFuel left) left,
          entry.2 = state ∧
            typeCanCompleteThisCycleFuel (sizeOf entry.1 + 1) entry.1 = true)) :=
  compileTypeFuel_sequence_eq_build alphabet left right

lemma edgeLocal_seq (alphabet : PactTypeAlphabet)
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
  · obtain ⟨hCur, hFut⟩ := hLeft.2 childEdge hChildMem
    have hResolved := hFut.resolve (computeFutureOf left)
      (computeFutureOf_subset_alphabet left)
    rw [hLeftAlphabet] at hCur hResolved
    refine ⟨by simpa [sequenceKeptLeftEdge] using hCur, ?_⟩
    simp only [sequenceKeptLeftEdge, sequenceLeftFutureSpec]
    split_ifs
    · exact Finset.empty_subset _
    · exact hResolved
    · exact Finset.Subset.trans Finset.sdiff_subset hResolved
  · obtain ⟨hCur, hFut⟩ := hRight.2 childEdge hChildMem
    rw [hRightAlphabet] at hCur hFut
    refine ⟨by simpa [childPendingEdge] using hCur, ?_⟩
    exact (childFutureSpec_alphabetLocal _ _ _).mpr hFut
  · obtain ⟨hCur, hFut⟩ := hLeft.2 childEdge hChildMem
    have hResolved := hFut.resolve (computeFutureOf left)
      (computeFutureOf_subset_alphabet left)
    rw [hLeftAlphabet] at hCur hResolved
    refine ⟨by simpa [sequenceRedirectEdge] using hCur, ?_⟩
    simp only [sequenceRedirectEdge, sequenceLeftFutureSpec]
    split_ifs
    · exact Finset.empty_subset _
    · exact hResolved
    · exact Finset.Subset.trans Finset.sdiff_subset hResolved

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

lemma edgeLocal_recur (alphabet : PactTypeAlphabet)
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
  · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩
  · obtain ⟨hCur, hFut⟩ := hBody.2 childEdge hChildMem
    rw [hBodyAlphabet] at hCur hFut
    split
    · exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩
    · refine ⟨hCur, ?_⟩
      exact (childFutureSpec_alphabetLocal _ _ _).mpr hFut

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

/-- Edge locality across the parallel product.  The raw family and the two
survivor-entry families publish a combined environment, handled by
`combineAutomatonEnvironment_mem_localEnvironments`; the four survivor and done
families copy a re-stamped child edge, whose alphabet is already the parent's. -/
lemma buildParallelAutomaton_edge_families
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hHide : PactTypeAlphabet.hideInterface leftAlphabet interface =
      parentAlphabet)
    (hLeftEnv : ∀ edge ∈ left.edges,
      edge.environment ∈ leftAlphabet.localEnvironments)
    (_hRightEnv : ∀ edge ∈ right.edges,
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
  -- The three synchronized families publish the same combined environment, so
  -- the argument for it is shared.
  have combined : ∀ leftEdge rightEdge : AutomatonFragmentEdge,
      leftEdge ∈ resolveAutomatonEdgesWith left leftFuture →
      syncAutomatonEdges leftAlphabet rightAlphabet interface leftEdge rightEdge →
      combineAutomatonEnvironment interface leftEdge.environment
        rightEdge.environment ∈ parentAlphabet.localEnvironments := by
    intro leftEdge rightEdge hLeftMem hSync
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
  rcases hEdge with
    ((((((hRaw | hLeftComplete) | hRightComplete) | hLeftSurvivor) |
      hRightSurvivor) | hLeftDone) | hRightDone) | hDone
  · -- synchronized: the combined environment collapses to the outer one
    simp only [parallelRawTransitionEdges, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_image] at hRaw
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨-, hSync, -⟩, rfl⟩ := hRaw
    exact combined leftEdge rightEdge hLeftMem hSync
  · -- left complete: the survivor entry publishes the same combined environment
    simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hLeftComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨-, hSync, -⟩, rfl⟩ := hLeftComplete
    exact combined leftEdge rightEdge hLeftMem hSync
  · -- right complete: the mirror
    simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image] at hRightComplete
    obtain ⟨leftEdge, hLeftMem, rightEdge, ⟨-, hSync, -⟩, rfl⟩ := hRightComplete
    exact combined leftEdge rightEdge hLeftMem hSync
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

/-- The offer half of parallel edge locality.  The three synchronized families
hide the component offer pairs. Survivor families retain the resolved child
pair; the done family contributes nothing. -/
lemma buildParallelAutomaton_edge_offers
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
    (hLeftResolved : ∀ edge ∈ left.edges,
      resolveFutureSpec leftFuture edge.future ⊆ leftAlphabet.actions)
    (hRightResolved : ∀ edge ∈ right.edges,
      resolveFutureSpec rightFuture edge.future ⊆ rightAlphabet.actions)
    (hRestampedLeftResolved : ∀ edge ∈ restampedLeft.edges,
      resolveFutureSpec restampedLeftFuture edge.future ⊆ parentAlphabet.actions)
    (hRestampedRightResolved : ∀ edge ∈ restampedRight.edges,
      resolveFutureSpec restampedRightFuture edge.future ⊆ parentAlphabet.actions)
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildParallelAutomaton parentAlphabet leftAlphabet
      rightAlphabet interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture restampedRightFuture).edges) :
    edge.current ⊆ parentAlphabet.actions ∧
      edge.future.AlphabetLocal parentAlphabet.actions := by
  classical
  have hSpec : ∀ (label : AutomatonConstructionLabel) (offers : Finset BareMessage),
      offers ⊆ parentAlphabet.actions →
      (parallelFutureSpec label offers).AlphabetLocal parentAlphabet.actions := by
    intro label offers hOffers
    unfold parallelFutureSpec
    split_ifs
    · exact Finset.empty_subset _
    · exact hOffers
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
      (hRightCurrent rightPending hRightPending), hSpec _ _
        (hideOffers_union_subset_actions hLeftHide hRightHide
          (hLeftResolved leftPending hLeftPending)
          (hRightResolved rightPending hRightPending))⟩
  · simp only [parallelLeftCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftComplete
    obtain ⟨leftEdge, ⟨leftPending, hLeftPending, rfl⟩, rightEdge,
      ⟨⟨rightPending, hRightPending, rfl⟩, -⟩, rfl⟩ := hLeftComplete
    exact ⟨hideOffers_union_subset_actions hLeftHide hRightHide
      (hLeftCurrent leftPending hLeftPending)
      (hRightCurrent rightPending hRightPending), hSpec _ _
        (hideOffers_union_subset_actions hLeftHide hRightHide
          (hLeftResolved leftPending hLeftPending)
          (hRightResolved rightPending hRightPending))⟩
  · simp only [parallelRightCompleteEdges, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightComplete
    obtain ⟨leftEdge, ⟨leftPending, hLeftPending, rfl⟩, rightEdge,
      ⟨⟨rightPending, hRightPending, rfl⟩, -⟩, rfl⟩ := hRightComplete
    exact ⟨hideOffers_union_subset_actions hLeftHide hRightHide
      (hLeftCurrent leftPending hLeftPending)
      (hRightCurrent rightPending hRightPending), hSpec _ _
        (hideOffers_union_subset_actions hLeftHide hRightHide
          (hLeftResolved leftPending hLeftPending)
          (hRightResolved rightPending hRightPending))⟩
  · simp only [parallelLeftCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftSurvivor
    exact ⟨hRestampedRightCurrent pending hPending,
      hSpec _ _ (hRestampedRightResolved pending hPending)⟩
  · simp only [parallelRightCompleteSurvivorEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightSurvivor
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightSurvivor
    exact ⟨hRestampedLeftCurrent pending hPending,
      hSpec _ _ (hRestampedLeftResolved pending hPending)⟩
  · simp only [parallelLeftCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hLeftDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hLeftDone
    exact ⟨hRestampedRightCurrent pending hPending,
      hSpec _ _ (hRestampedRightResolved pending hPending)⟩
  · simp only [parallelRightCompleteDoneEdges, Finset.mem_filter,
      Finset.mem_image, resolveAutomatonEdgesWith] at hRightDone
    obtain ⟨resolved, ⟨⟨pending, hPending, rfl⟩, -⟩, rfl⟩ := hRightDone
    exact ⟨hRestampedLeftCurrent pending hPending,
      hSpec _ _ (hRestampedLeftResolved pending hPending)⟩
  · simp only [parallelDoneEdges, Finset.mem_image, Finset.mem_filter] at hDone
    obtain ⟨environment, -, rfl⟩ := hDone
    exact ⟨by simp, by simp [FutureSpec.AlphabetLocal]⟩

/-- Compiling a conjunctive offer at its own budget builds the selected
conjunctive automaton over the else arm and every selected product, each
compiled at its own budget. -/
theorem compileTypeFuel_offer_eq (alphabet : PactTypeAlphabet)
    (elseType : PactType) (branches : List (BareMessage × PactType)) :
    compileTypeFuel (typeCompilationFuel (.offer alphabet elseType branches))
        (.offer alphabet elseType branches) =
      buildAtomicConjunctiveOfferAutomaton alphabet branches
        (compileTypeFuel (typeCompilationFuel elseType) elseType)
        ((conjunctiveSelections branches.length).toList.map fun selected =>
          (selected,
            compileTypeFuel
              (typeCompilationFuel
                (parallelTypeBranchesFiring alphabet selected branches))
              (parallelTypeBranchesFiring alphabet selected branches))) := by
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
        (parallelTypeBranchesFiring alphabet selected branches) ≤
        max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches) := by
      exact (typeCompilationFuel_parallelTypeBranchesFiring alphabet selected branches).trans
        (Nat.le_max_right _ _)
    rw [compileTypeFuel_eq_of_sufficient _ hFuel (Nat.le_refl _)]

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
    have hResolve := resolve_childFutureSpec 0 childEdge.future
      (computeFutureOf (.choice alphabet left right)) (computeFutureOf left) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_left alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem)
    exact hResolve.symm

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
  · have hResolve := resolve_childFutureSpec 0 childEdge.future
      (computeFutureOf (.choice alphabet left right)) (computeFutureOf left) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel left) left le_rfl hLeftDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_left alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelLeft hLeftDisjoint
          hLeftAlphabet hProductInfo t hStateMem)
    exact hResolve.trans hCFuture
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
  · have hResolve := resolve_childFutureSpec 1 childEdge.future
      (computeFutureOf (.choice alphabet left right)) (computeFutureOf right) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_right alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem)
    exact hResolve.trans hCFuture
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
    have hResolve := resolve_childFutureSpec 1 childEdge.future
      (computeFutureOf (.choice alphabet left right)) (computeFutureOf right) (by
        intro t hRef
        have hStateMem := compileTypeFuel_futureTargetsInStates
          (typeCompilationFuel right) right le_rfl hRightDisjoint childEdge
          hChildEdgeMem t hRef
        exact computeFutureOf_binaryChoice_right alphabet left right
          TypeLabel.silent TypeLabel.silent
          (.choice alphabet left right) hWhole hFuelRight hRightDisjoint
          hRightAlphabet hProductInfo t hStateMem)
    exact hResolve.symm

end

end Pact
