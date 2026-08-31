import Anvilpp.PactTypes.Syntax.TypeTransitionSystem

/-!
# The type automaton alphabet and its transition-symbol encoding
-/

namespace Pact

noncomputable section

/-! ## Constructor-based finite automata -/

/--
The observation pool one type automaton is compiled against.  It holds only
what is fixed once at the start of compilation and never changes: the
interfaces that may be resolved, and the progress and fair-choice identifiers
that may be observed.  Every action-indexed set is read off the type's own
alphabet instead.
-/
structure TypeAlphabet : Type where
  interface : Interface
  progress : Finset ProcId
  fair : Finset BranchId
  deriving DecidableEq

namespace TypeAlphabet

  /-- Both polarities of every fixed internal/interface message. -/
  def interfaceActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.interface.biUnion fun msg => {(msg, .send), (msg, .recv)}

  /-- Exactly the actions one fixed type alphabet declares.  The signature is
  carried only so the `For` family reads uniformly; it never narrows the set,
  because a type owns every action it declares. -/
  def localActionsFor (_signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    alphabet.actions

  /-- Environment actions visible to a type with fixed alphabet `alphabet`. -/
  def localEnvironmentActionsFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    (signature.localActionsFor alphabet).image typeNeed

  /-- Well-formed environments over one type's fixed action alphabet. -/
  def localEnvironmentsFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      (signature.localEnvironmentActionsFor alphabet).powerset.biUnion
        fun immediate =>
          (signature.localEnvironmentActionsFor alphabet \ immediate).powerset.image
            fun future =>
              { immediate := immediate, future := future, clock := false }

  /-- Offer summaries over one type's fixed action alphabet. -/
  def localOfferSummariesFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset TypeOfferSummary :=
    (signature.localActionsFor alphabet).powerset.biUnion fun current =>
      (signature.localActionsFor alphabet).powerset.image fun future =>
        { current := current, future := future }

  /-- Actions a type may still name in a label: the ones it declares, plus the
  interface actions an enclosing parallel node has yet to hide. -/
  def localActionsWithInterfaceFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    signature.localActionsFor alphabet ∪ signature.interfaceActions

  /-- Observations a type may emit: the actions it may name, plus the resolved
  observations and identifiers the pool fixes. -/
  def localObservationsFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset TypeObservation :=
    (signature.localActionsWithInterfaceFor alphabet).image
        (fun action => TypeObservation.message action.1 action.2) ∪
      signature.interface.image TypeObservation.resolved ∪
      signature.progress.image TypeObservation.progress ∪
      signature.fair.biUnion (fun bid =>
        {TypeObservation.fair bid false, TypeObservation.fair bid true})

  /-- `Lab_τ = 2^(Label(τ)) ∪ {#}`; the empty subset is epsilon. -/
  def localLabelsFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset TypeLabel :=
    (signature.localObservationsFor alphabet).powerset.image TypeLabel.actions ∪
      {TypeLabel.tock}

  /-- `TypeEnvironment.tock` is the only clocked environment over one type's
  alphabet: every other member is built with `clock := false`. -/
  theorem eq_tock_of_mem_localEnvironmentsFor_of_clock
      {signature : TypeAlphabet} {alphabet : PactTypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ signature.localEnvironmentsFor alphabet)
      (hClock : environment.clock = true) :
      environment = TypeEnvironment.tock := by
    simp only [localEnvironmentsFor, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with hTock | ⟨immediate, _, future, _, rfl⟩
    · exact hTock
    · exact absurd hClock (by simp)

  /-- A clocked environment over one type's alphabet offers nothing immediately. -/
  theorem immediate_eq_empty_of_mem_localEnvironmentsFor_of_clock
      {signature : TypeAlphabet} {alphabet : PactTypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ signature.localEnvironmentsFor alphabet)
      (hClock : environment.clock = true) :
      environment.immediate = ∅ := by
    rw [eq_tock_of_mem_localEnvironmentsFor_of_clock hEnvironment hClock]
    rfl

  /-- Environments over one type's alphabet are well formed. -/
  theorem environmentFor_wellFormed {signature : TypeAlphabet}
      {alphabet : PactTypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ signature.localEnvironmentsFor alphabet) :
      environment.WellFormed alphabet := by
    simp only [localEnvironmentsFor, Finset.mem_union, Finset.mem_singleton,
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

end TypeAlphabet

/-- The observation pool a type is compiled against, read off the type itself:
the interfaces it synchronizes on, and the progress and fair-choice identifiers
its syntax mentions. -/
def PactType.observationPool (processType : PactType) : TypeAlphabet :=
  { interface := PactType.ParallelInterfaces processType
    progress := PactType.ProgressIds processType
    fair := PactType.FairChoiceIds processType }

/-- One letter of the decorated transition alphabet `Σ_τ`. -/
structure TypeAutomatonSymbol : Type where
  environment : TypeEnvironment
  label : TypeLabel
  offers : TypeOfferSummary
  deriving DecidableEq

/-- The public transition alphabet of one fixed type alphabet.  Every component
is read off this type: its environments and offers from the actions it owns, and
its labels from those same actions together with the resolved observations and
identifiers the pool fixes once at the start of compilation. -/
def TypeAlphabet.transitionAlphabetFor
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) :
    Finset TypeAutomatonSymbol :=
  (signature.localEnvironmentsFor alphabet).biUnion fun environment =>
    (signature.localLabelsFor alphabet).biUnion fun label =>
      (signature.localOfferSummariesFor alphabet).image fun offers =>
        { environment := environment, label := label, offers := offers }

end

end Pact
