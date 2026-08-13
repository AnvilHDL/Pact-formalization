import Anvilpp.PactTypes.Correspondence.Core.AtomicCompletingFuture

/-!
# TypeEnvironment.AvoidsInterface, CompilationScopedFragmentStepCorrect, and local-environment well-formedness
-/

namespace Pact

noncomputable section

/-! ### Parallel environment reconstruction -/

namespace TypeEnvironment

/-- An environment does not mention messages hidden by a parallel interface. -/
def AvoidsInterface (environment : TypeEnvironment)
    (interface : Interface) : Prop :=
  (∀ action ∈ environment.immediate, action.1 ∉ interface) ∧
    ∀ action ∈ environment.future, action.1 ∉ interface

theorem AvoidsInterface.mono
    {environment : TypeEnvironment} {larger smaller : Interface}
    (hAvoids : environment.AvoidsInterface larger)
    (hSubset : smaller ⊆ larger) :
    environment.AvoidsInterface smaller := by
  exact ⟨fun action hAction hSmaller =>
      hAvoids.1 action hAction (hSubset hSmaller),
    fun action hAction hSmaller =>
      hAvoids.2 action hAction (hSubset hSmaller)⟩

theorem tock_avoidsInterface (interface : Interface) :
    TypeEnvironment.tock.AvoidsInterface interface := by
  simp [AvoidsInterface, TypeEnvironment.tock]

end TypeEnvironment

/-- Passing through a sibling-local environment may add only actions from the
parent interface, so avoidance of a disjoint descendant interface is
preserved. -/
theorem LocalTypeEnvironment.avoidsInterface_of_disjoint
    {outer siblingEnvironment localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {sibling : PactType} {label : TypeLabel}
    (hLocal : LocalTypeEnvironment outer parentInterface siblingEnvironment
      sibling label localEnvironment)
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface) :
    localEnvironment.AvoidsInterface childInterface := by
  cases hLocal with
  | clock outer parentInterface sibling label hClock =>
      exact TypeEnvironment.tock_avoidsInterface childInterface
  | ordinary outer siblingEnvironment localEnvironment parentInterface sibling
      siblingTarget label current future hOuterClock hSiblingClock hOffers
      hLocalClock hImmediate hFuture =>
      constructor
      · intro action hAction hChild
        rw [hImmediate] at hAction
        rcases Finset.mem_union.mp hAction with hOuter | hParent
        · exact hOuterAvoids.1 action hOuter hChild
        · exact Finset.disjoint_left.mp hDisjoint
            (Finset.mem_filter.mp hParent).2 hChild
      · intro action hAction hChild
        rw [hFuture] at hAction
        rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hAction).1 with
          hOuter | hParent
        · exact hOuterAvoids.2 action hOuter hChild
        · exact Finset.disjoint_left.mp hDisjoint
            (Finset.mem_filter.mp hParent).2 hChild

theorem TypeEnvironment.avoidsInterface_of_ordinary_fields
    {outer localEnvironment : TypeEnvironment}
    {parentInterface childInterface : Interface}
    {current future : Finset BareMessage}
    (hOuterAvoids : outer.AvoidsInterface childInterface)
    (hDisjoint : Disjoint parentInterface childInterface)
    (hImmediate : localEnvironment.immediate =
      outer.immediate ∪ restrictTypeOffers parentInterface current)
    (hFuture : localEnvironment.future =
      (outer.future ∪ restrictTypeOffers parentInterface future) \
        localEnvironment.immediate) :
    localEnvironment.AvoidsInterface childInterface := by
  constructor
  · intro action hAction hChild
    rw [hImmediate] at hAction
    rcases Finset.mem_union.mp hAction with hOuter | hParent
    · exact hOuterAvoids.1 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild
  · intro action hAction hChild
    rw [hFuture] at hAction
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hAction).1 with
      hOuter | hParent
    · exact hOuterAvoids.2 action hOuter hChild
    · exact Finset.disjoint_left.mp hDisjoint
        (Finset.mem_filter.mp hParent).2 hChild

/-- Induction-facing raw correspondence.  Enclosing synchronized products may
supply local environments, provided those environments avoid every parallel
interface nested below the syntax node. -/
def CompilationScopedFragmentStepCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual residual' : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {offers : TypeOfferSummary},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    (DecoratedTypeTransition environment residual label offers residual' ↔
      ∃ target,
        fragment.HasResolvedEdge state environment label offers target ∧
        TypeCompilationRelation processType target residual')

/-- A free-variable marker has neither a semantic transition nor a resolved
edge: `TypeTransition` has no `.var` case, and every compiled `.var` edge is
labelled `.variable name`, never `.visible _`. -/
theorem compilationScopedFragmentStepCorrect_var
    (signature : TypeAlphabet) (name : String) :
    CompilationScopedFragmentStepCorrect signature (.var name) := by
  intro residual residual' state environment label offers hRelated hLocal
    hAvoids
  cases hRelated
  constructor
  · intro hStep
    cases hStep.1
  · rintro ⟨target, hEdge, _⟩
    exfalso
    simp only [AutomatonFragment.HasResolvedEdge, typeCompilationFuel,
      compileTypeFuel, finishAutomatonFragment, Finset.mem_image] at hEdge
    obtain ⟨edge, ⟨environment', _, rfl⟩, _, _, hLabel, _⟩ := hEdge
    simp at hLabel

/-- A synchronization witness selected independently of the product's actual
child target is represented by a semantic offer derivation at the same related
source. -/
def CompilationScopedResolvedOfferWitnessCorrect
    (signature : TypeAlphabet) (processType : PactType) : Prop :=
  let fragment := compileTypeFuel signature
    (typeCompilationFuel processType) processType
  ∀ {residual : PactType} {state : TypeAutomatonState}
    {environment : TypeEnvironment} {label : TypeLabel}
    {actualOffers : TypeOfferSummary} {actualTarget : TypeAutomatonState},
    TypeCompilationRelation processType state residual →
    environment ∈ signature.localEnvironments →
    environment.AvoidsInterface processType.ParallelInterfaces →
    fragment.HasResolvedEdge state environment label actualOffers
      actualTarget →
    ∀ witness ∈ resolvedAutomatonEdges fragment,
      witness.label ≠ .future →
      witness.source = state →
      witness.environment = environment →
      witness.label.semantic = label →
      ∃ target,
        TypeOffers environment residual label target witness.current
          witness.future

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

/-- Every exported environment avoids a declared sub-interface. -/
theorem environment_avoids_subinterface
    {alphabet : TypeAlphabet} {environment : TypeEnvironment}
    {interface : Interface}
    (hAlphabet : alphabet.WellFormed)
    (hEnvironment : environment ∈ alphabet.environments)
    (hInterface : interface ⊆ alphabet.interface) :
    environment.AvoidsInterface interface := by
  constructor
  · intro action hAction hInternal
    exact environment_immediate_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)
  · intro action hAction hInternal
    exact environment_future_avoids_interface hAlphabet hEnvironment
      action hAction (hInterface hInternal)

end TypeAlphabet

end

end Pact
