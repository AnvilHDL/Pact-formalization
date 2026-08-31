import Anvilpp.PactTypes.Syntax.PactTypeRegularity
import Anvilpp.PactTypes.Syntax.TypeTransitionSystem

/-!
# The type automaton alphabet and its transition-symbol encoding
-/

namespace Pact

noncomputable section

/-! ## Constructor-based finite automata -/

namespace PactTypeAlphabet

  /-- Environment polarities complementary to the actions a type declares. -/
  def localEnvironmentActions (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    alphabet.actions.image typeNeed

  /-- Well-formed environments over the actions a type declares. -/
  def localEnvironments (alphabet : PactTypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.localEnvironmentActions.powerset.biUnion fun immediate =>
        (alphabet.localEnvironmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  /-- Offer summaries over the actions a type declares. -/
  def localOfferSummaries (alphabet : PactTypeAlphabet) : Finset TypeOfferSummary :=
    alphabet.actions.powerset.biUnion fun current =>
      alphabet.actions.powerset.image fun future =>
        { current := current, future := future }

  /-- `TypeEnvironment.tock` is the only clocked environment over one type's
  alphabet: every other member is built with `clock := false`. -/
  theorem eq_tock_of_mem_localEnvironments_of_clock
      {alphabet : PactTypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment = TypeEnvironment.tock := by
    simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with hTock | ⟨immediate, _, future, _, rfl⟩
    · exact hTock
    · exact absurd hClock (by simp)

  /-- A clocked environment over one type's alphabet offers nothing immediately. -/
  theorem immediate_eq_empty_of_mem_localEnvironments_of_clock
      {alphabet : PactTypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment.immediate = ∅ := by
    rw [eq_tock_of_mem_localEnvironments_of_clock hEnvironment hClock]
    rfl

  /-- Environments over one type's alphabet are well formed. -/
  theorem environment_wellFormed {alphabet : PactTypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments) :
      environment.WellFormed alphabet := by
    simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with rfl | ⟨immediate, hImmediateSub, future, hFuture, rfl⟩
    · simp [TypeEnvironment.WellFormed, TypeEnvironment.tock]
    · refine ⟨by simp, ?_, hImmediateSub, hFuture.trans Finset.sdiff_subset⟩
      intro _
      change immediate ∩ future = ∅
      rw [← Finset.disjoint_iff_inter_eq_empty]
      apply Finset.disjoint_left.mpr
      intro action hImmediate hFutureMember
      have hAvailable := hFuture hFutureMember
      simp only [Finset.mem_sdiff] at hAvailable
      exact hAvailable.2 hImmediate

end PactTypeAlphabet

namespace PactType

  /-- Both polarities of every message a type synchronizes on. -/
  def interfaceActions (processType : PactType) : Finset BareMessage :=
    (PactType.ParallelInterfaces processType).biUnion fun msg =>
      {(msg, .send), (msg, .recv)}

  /-- Actions a type may name in a label: the ones it declares, plus the
  interface actions an enclosing parallel node has yet to hide. -/
  def localActionsWithInterface (processType : PactType) : Finset BareMessage :=
    processType.alphabet.actions ∪ processType.interfaceActions

  /-- Observations a type may emit, all read off its own syntax. -/
  def observations (processType : PactType) : Finset TypeObservation :=
    processType.localActionsWithInterface.image
        (fun action => TypeObservation.message action.1 action.2) ∪
      (PactType.ParallelInterfaces processType).image TypeObservation.resolved ∪
      (PactType.ProgressIds processType).image TypeObservation.progress ∪
      (PactType.FairChoiceIds processType).biUnion (fun bid =>
        {TypeObservation.fair bid false, TypeObservation.fair bid true})

  /-- `Lab_τ = 2^(Label(τ)) ∪ {#}`; the empty subset is epsilon. -/
  def labels (processType : PactType) : Finset TypeLabel :=
    processType.observations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

end PactType

/-- One letter of the decorated transition alphabet `Σ_τ`. -/
structure TypeAutomatonSymbol : Type where
  environment : TypeEnvironment
  label : TypeLabel
  offers : TypeOfferSummary
  deriving DecidableEq

/-- `Σ_τ`, read entirely off the type: environments and offers from the actions
it declares, labels from those actions together with the interfaces it resolves
and the identifiers its syntax mentions. -/
def PactType.transitionAlphabet (processType : PactType) :
    Finset TypeAutomatonSymbol :=
  processType.alphabet.localEnvironments.biUnion fun environment =>
    processType.labels.biUnion fun label =>
      processType.alphabet.localOfferSummaries.image fun offers =>
        { environment := environment, label := label, offers := offers }

@[simp] theorem PactType.mem_transitionAlphabet_iff
    (processType : PactType) (environment : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary) :
    TypeAutomatonSymbol.mk environment label offers ∈
        processType.transitionAlphabet ↔
      environment ∈ processType.alphabet.localEnvironments ∧
      label ∈ processType.labels ∧
      offers ∈ processType.alphabet.localOfferSummaries := by
  classical
  simp [PactType.transitionAlphabet]

end

end Pact
