import Anvilpp.PactTypes.Syntax.TypeTransitionSystem

/-!
# The type automaton alphabet and its transition-symbol encoding
-/

namespace Pact

noncomputable section

/-! ## Constructor-based finite automata -/

/--
The fixed finite alphabet for one type automaton.
-/
structure TypeAlphabet : Type extends MessageAlphabet where
  progress : Finset ProcId
  fair : Finset BranchId
  deriving DecidableEq

namespace TypeAlphabet

  /-- Boundary actions cannot use an internal message identifier (Section 2.1). -/
  def WellFormed (alphabet : TypeAlphabet) : Prop :=
    ∀ action ∈ alphabet.boundary, action.1 ∉ alphabet.interface

  /-- Both polarities of every fixed internal/interface message. -/
  def interfaceActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.interface.biUnion fun msg => {(msg, .send), (msg, .recv)}

  /-- Actions visible to a constructor while it is compiled as a subautomaton. -/
  def localActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.boundary ∪ alphabet.interfaceActions

  /-- Environment polarities complementary to the type's boundary actions. -/
  def environmentActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.boundary.image typeNeed

  def localEnvironmentActions (alphabet : TypeAlphabet) : Finset BareMessage :=
    alphabet.localActions.image typeNeed

  theorem environmentActions_subset_localEnvironmentActions
      (alphabet : TypeAlphabet) :
      alphabet.environmentActions ⊆ alphabet.localEnvironmentActions := by
    apply Finset.image_mono
    exact Finset.subset_union_left

  /-- The finite set `E_τ` of well-formed erased boundary environments. -/
  def environments (alphabet : TypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.environmentActions.powerset.biUnion fun immediate =>
        (alphabet.environmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  theorem environment_immediate_avoids_interface
      {alphabet : TypeAlphabet} {environment : TypeEnvironment}
      (hAlphabet : alphabet.WellFormed)
      (hEnvironment : environment ∈ alphabet.environments) :
      ∀ action ∈ environment.immediate,
        action.1 ∉ alphabet.interface := by
    simp only [environments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with rfl | ⟨immediate, hImmediate, future, _, rfl⟩
    · simp [TypeEnvironment.tock]
    · intro action hAction hInterface
      have hEnvironmentAction := hImmediate hAction
      simp only [environmentActions, Finset.mem_image] at hEnvironmentAction
      rcases hEnvironmentAction with ⟨boundaryAction, hBoundary, hNeed⟩
      apply hAlphabet boundaryAction hBoundary
      have hMessage := congrArg Prod.fst hNeed
      simp only [typeNeed] at hMessage
      rw [hMessage]
      exact hInterface

  /-- Environments used internally before a parallel constructor hides `I`. -/
  def localEnvironments (alphabet : TypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.localEnvironmentActions.powerset.biUnion fun immediate =>
        (alphabet.localEnvironmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  /-- `TypeEnvironment.tock` is the only clocked local environment: every
  other member is built with `clock := false`. -/
  theorem eq_tock_of_mem_localEnvironments_of_clock {alphabet : TypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment = TypeEnvironment.tock := by
    simp only [localEnvironments, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hEnvironment
    rcases hEnvironment with hTock | ⟨immediate, _, future, _, rfl⟩
    · exact hTock
    · exact absurd hClock (by simp)

  /-- A clocked local environment offers nothing immediately. -/
  theorem immediate_eq_empty_of_mem_localEnvironments_of_clock
      {alphabet : TypeAlphabet} {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.localEnvironments)
      (hClock : environment.clock = true) :
      environment.immediate = ∅ := by
    rw [eq_tock_of_mem_localEnvironments_of_clock hEnvironment hClock]
    rfl

  theorem environments_subset_localEnvironments (alphabet : TypeAlphabet) :
      alphabet.environments ⊆ alphabet.localEnvironments := by
    intro environment hEnvironment
    simp only [environments, localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image] at hEnvironment ⊢
    rcases hEnvironment with hTock | ⟨immediate, hImmediate, future,
      hFuture, rfl⟩
    · exact Or.inl hTock
    · right
      refine ⟨immediate, ?_, future, ?_, rfl⟩
      · exact hImmediate.trans
          (environmentActions_subset_localEnvironmentActions alphabet)
      · intro action hAction
        have hInEnvironment := hFuture hAction
        simp only [Finset.mem_sdiff] at hInEnvironment ⊢
        exact ⟨(environmentActions_subset_localEnvironmentActions alphabet)
          hInEnvironment.1, hInEnvironment.2⟩

  theorem environment_wellFormed {alphabet : TypeAlphabet}
      {environment : TypeEnvironment}
      (hEnvironment : environment ∈ alphabet.environments) :
      environment.WellFormed := by
    simp only [environments, Finset.mem_union, Finset.mem_singleton,
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
        have hAvailable := hFuture hFutureMember
        simp only [Finset.mem_sdiff] at hAvailable
        exact hAvailable.2 hImmediate

  /-- The fixed observations from which non-clock labels are formed. -/
  def observations (alphabet : TypeAlphabet) : Finset TypeObservation :=
    alphabet.boundary.image (fun action =>
      TypeObservation.message action.1 action.2) ∪
    alphabet.interface.image TypeObservation.resolved ∪
    alphabet.progress.image TypeObservation.progress ∪
    alphabet.fair.biUnion (fun bid =>
      {TypeObservation.fair bid false, TypeObservation.fair bid true})

  def localObservations (alphabet : TypeAlphabet) : Finset TypeObservation :=
    alphabet.localActions.image (fun action =>
      TypeObservation.message action.1 action.2) ∪
    alphabet.interface.image TypeObservation.resolved ∪
    alphabet.progress.image TypeObservation.progress ∪
    alphabet.fair.biUnion (fun bid =>
      {TypeObservation.fair bid false, TypeObservation.fair bid true})

  /-- `Lab_τ = 2^(Label(τ)) ∪ {#}`; the empty subset is epsilon. -/
  def labels (alphabet : TypeAlphabet) : Finset TypeLabel :=
    alphabet.observations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

  def localLabels (alphabet : TypeAlphabet) : Finset TypeLabel :=
    alphabet.localObservations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

  /-- `Offer_τ`: offers exposed outside this type are boundary actions. -/
  def offerSets (alphabet : TypeAlphabet) : Finset (Finset BareMessage) :=
    alphabet.boundary.powerset

  def localOfferSets (alphabet : TypeAlphabet) : Finset (Finset BareMessage) :=
    alphabet.localActions.powerset

  def offerSummaries (alphabet : TypeAlphabet) : Finset TypeOfferSummary :=
    alphabet.offerSets.biUnion fun current =>
      alphabet.offerSets.image fun future =>
        { current := current, future := future }

  /-- Offer summaries available while compiling a constructor or one of its
  children.  Interface actions are local actions until the enclosing parallel
  constructor hides them. -/
  def localOfferSummaries (alphabet : TypeAlphabet) : Finset TypeOfferSummary :=
    alphabet.localOfferSets.biUnion fun current =>
      alphabet.localOfferSets.image fun future =>
        { current := current, future := future }

  /-- Actions from the surrounding signature that belong to one fixed type
  alphabet.  The intersection keeps malformed annotations from enlarging the
  signature; admissible types make it redundant for every action they use. -/
  def localActionsFor (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    signature.localActions ∩ alphabet.actions

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

  theorem localActionsFor_subset_localActions (signature : TypeAlphabet)
      (alphabet : PactTypeAlphabet) :
      signature.localActionsFor alphabet ⊆ signature.localActions := by
    intro action hAction
    exact (Finset.mem_inter.mp hAction).1

  theorem localEnvironmentActionsFor_subset_localEnvironmentActions
      (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) :
      signature.localEnvironmentActionsFor alphabet ⊆
        signature.localEnvironmentActions := by
    apply Finset.image_mono
    exact localActionsFor_subset_localActions signature alphabet

  theorem localEnvironmentsFor_subset_localEnvironments
      (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) :
      signature.localEnvironmentsFor alphabet ⊆
        signature.localEnvironments := by
    intro environment hEnvironment
    simp only [localEnvironmentsFor, localEnvironments, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
      Finset.mem_image] at hEnvironment ⊢
    rcases hEnvironment with hTock | ⟨immediate, hImmediate, future,
      hFuture, rfl⟩
    · exact Or.inl hTock
    · right
      refine ⟨immediate, hImmediate.trans
        (localEnvironmentActionsFor_subset_localEnvironmentActions
          signature alphabet), future, ?_, rfl⟩
      intro action hAction
      have hMember := hFuture hAction
      simp only [Finset.mem_sdiff] at hMember ⊢
      exact ⟨
        localEnvironmentActionsFor_subset_localEnvironmentActions
          signature alphabet hMember.1,
        hMember.2⟩

  theorem localOfferSummariesFor_subset_localOfferSummaries
      (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) :
      signature.localOfferSummariesFor alphabet ⊆
        signature.localOfferSummaries := by
    intro offers hOffers
    simp only [localOfferSummariesFor, localOfferSummaries, localOfferSets,
      Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
      at hOffers ⊢
    rcases hOffers with ⟨current, hCurrent, future, hFuture, rfl⟩
    exact ⟨current,
      hCurrent.trans (localActionsFor_subset_localActions signature alphabet),
      future,
      hFuture.trans (localActionsFor_subset_localActions signature alphabet),
      rfl⟩

  /-
  Validate a type against a previously chosen alphabet.  This checks use of
  the signature; it does not synthesize or enlarge the signature from syntax.
  -/
  mutual
    /-- Check that a type uses only declarations from its fixed alphabet. -/
    def Supports (alphabet : TypeAlphabet) : PactType → Prop
      | .message _ msg dir =>
          (msg, dir) ∈ alphabet.boundary ∨ msg ∈ alphabet.interface
      | .progress _ pid => pid ∈ alphabet.progress
      | .tock _ | .skip _ | .var _ _ => True
      | .choice _ left right | .seq _ left right =>
          alphabet.Supports left ∧ alphabet.Supports right
      | .fairChoice _ bid left right =>
          bid ∈ alphabet.fair ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .par _ left right interface =>
          interface ⊆ alphabet.interface ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .recur _ _ body => alphabet.Supports body
      | .xoffer _ elseType branches | .offer _ elseType branches =>
          alphabet.Supports elseType ∧ alphabet.SupportsBranches branches
    termination_by processType => sizeOf processType

    def SupportsBranches (alphabet : TypeAlphabet) :
        List (BareMessage × PactType) → Prop
      | [] => True
      | (action, processType) :: rest =>
          (action ∈ alphabet.boundary ∨ action.1 ∈ alphabet.interface) ∧
            alphabet.Supports processType ∧ alphabet.SupportsBranches rest
    termination_by branches => sizeOf branches
    decreasing_by
      all_goals
        simp_wf
        omega
  end

end TypeAlphabet

/-- One letter of the decorated transition alphabet `Σ_τ`. -/
structure TypeAutomatonSymbol : Type where
  environment : TypeEnvironment
  label : TypeLabel
  offers : TypeOfferSummary
  deriving DecidableEq

def TypeAlphabet.transitionAlphabet
    (alphabet : TypeAlphabet) : Finset TypeAutomatonSymbol :=
  alphabet.localEnvironments.biUnion fun environment =>
    alphabet.localLabels.biUnion fun label =>
      alphabet.localOfferSummaries.image fun offers =>
        { environment := environment, label := label, offers := offers }

/-- The public transition alphabet of one fixed type alphabet.  Labels remain
drawn from the surrounding signature because a parallel node may emit a
resolved observation for an interface hidden from its boundary action set.
Environments and offers are restricted to the actions owned by this type. -/
def TypeAlphabet.transitionAlphabetFor
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet) :
    Finset TypeAutomatonSymbol :=
  (signature.localEnvironmentsFor alphabet).biUnion fun environment =>
    signature.localLabels.biUnion fun label =>
      (signature.localOfferSummariesFor alphabet).image fun offers =>
        { environment := environment, label := label, offers := offers }

end

end Pact
