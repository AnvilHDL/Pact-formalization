import Anvilpp.PactTypes.Syntax

/-!
# Constructor-based Pact type automata
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

  /-
  Validate a type against a previously chosen alphabet.  This checks use of
  the signature; it does not synthesize or enlarge the signature from syntax.
  -/
  mutual
    /-- Check that a type uses only declarations from its fixed alphabet. -/
    def Supports (alphabet : TypeAlphabet) : PactType → Prop
      | .message msg dir =>
          (msg, dir) ∈ alphabet.boundary ∨ msg ∈ alphabet.interface
      | .progress pid => pid ∈ alphabet.progress
      | .tock | .skip | .var _ => True
      | .choice left right | .seq left right =>
          alphabet.Supports left ∧ alphabet.Supports right
      | .fairChoice bid left right =>
          bid ∈ alphabet.fair ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .par left right interface =>
          interface ⊆ alphabet.interface ∧
            alphabet.Supports left ∧ alphabet.Supports right
      | .recur _ body => alphabet.Supports body
      | .xoffer elseType branches | .offer elseType branches =>
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
  alphabet.environments.biUnion fun environment =>
    alphabet.labels.biUnion fun label =>
      alphabet.offerSummaries.image fun offers =>
        { environment := environment, label := label, offers := offers }

/-! ### Construction representation -/

/--
Tagged States

* `root` and `final` are the two distinguished states used by atomic types.
* `child i q` injects state `q` into child automaton `i` of a sum/sequence.
* `pair q₁ q₂` is a state of a synchronized parallel product.
-/
inductive TypeAutomatonState : Type where
  /-- Fresh entry state introduced by a constructor. -/
  | root
  /-- Completed state used by atomic constructors. -/
  | final
  /-- State `state` embedded into child automaton `index`. -/
  | child : Nat → TypeAutomatonState → TypeAutomatonState
  /-- Product state containing one state from each parallel component. -/
  | pair : TypeAutomatonState → TypeAutomatonState → TypeAutomatonState
  deriving DecidableEq

/--
Visible labels become part of the final automaton. Variable labels are
temporary back-edge markers consumed when compiling the matching binder.
Future-observation labels are internal edges used only by `computeFuture`;
they retain optimistic component offers without becoming semantic steps.
-/
inductive AutomatonConstructionLabel : Type where
  | visible : TypeLabel → AutomatonConstructionLabel
  | variable : String → AutomatonConstructionLabel
  | future : AutomatonConstructionLabel
  deriving DecidableEq

/--
How to fill an edge's future-offer field.

* `explicit offers` copies a future set already computed by a child.
* `at state removed` computes `OF(state) \ removed` after the parent graph is
  complete. This is what prevents a constructor from inspecting a partial
  automaton during recursive construction.
-/
inductive FutureSpec : Type where
  | explicit : Finset BareMessage → FutureSpec
  | at : TypeAutomatonState → Finset BareMessage → FutureSpec
  deriving DecidableEq

/-- An edge whose future-offer field has not necessarily been resolved yet. -/
structure PendingAutomatonEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : FutureSpec
  target : TypeAutomatonState
  deriving DecidableEq

/--
A constructor fragment whose future references remain symbolic.

Keeping `FutureSpec.at` references unresolved is essential for recursion:
an enclosing binder can add a back-edge, changing the future offers reachable
from a child state.  Resolution therefore happens only when an operation
actually needs decorated edges, and once more for the final automaton.
-/
structure AutomatonFragment : Type where
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  /-- States whose represented semantic residual is literally `skip`. -/
  skipping : Finset TypeAutomatonState
  /-- States whose represented residual may optimistically finish before the
  next clock.  Unlike `skipping`, this is analysis metadata rather than a
  source of semantic administrative transitions. -/
  completing : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

/-- Every symbolic future reference in a fragment points to a declared state. -/
def AutomatonFragment.FutureTargetsInStates
    (fragment : AutomatonFragment) : Prop :=
  ∀ edge ∈ fragment.edges, ∀ target removed,
    edge.future = .at target removed → target ∈ fragment.states

/-- A constructor edge after its future-offer field has been computed. -/
structure AutomatonFragmentEdge : Type where
  source : TypeAutomatonState
  environment : TypeEnvironment
  label : AutomatonConstructionLabel
  current : Finset BareMessage
  future : Finset BareMessage
  target : TypeAutomatonState
  deriving DecidableEq

/-- Complete state/edge graph used while resolving pending future fields. -/
structure PendingAutomaton : Type where
  states : Finset TypeAutomatonState
  edges : Finset PendingAutomatonEdge

namespace AutomatonConstructionLabel

  /-- Treat a temporary recursion edge as silent for local synchronization. -/
  def semantic : AutomatonConstructionLabel → TypeLabel
    | .visible label => label
    | .variable _ => TypeLabel.silent
    | .future => TypeLabel.silent

  /-- Combine product labels while preserving an unresolved recursion marker. -/
  def combine (interface : Interface)
      (left right : AutomatonConstructionLabel) : AutomatonConstructionLabel :=
    match left, right with
    | .future, _ => .future
    | _, .future => .future
    | .variable name, _ => .variable name
    | _, .variable name => .variable name
    | .visible leftLabel, .visible rightLabel =>
        .visible (TypeLabel.combine interface leftLabel rightLabel)

  /-- A synchronized non-clock product edge cannot hide a clock edge in
  either component. -/
  theorem component_nonclock_of_sync
      (interface : Interface) (left right : AutomatonConstructionLabel)
      (hSync : TypeLabel.Sync interface left.semantic right.semantic)
      (hCombined : (combine interface left right).semantic ≠ TypeLabel.tock) :
      left.semantic ≠ TypeLabel.tock ∧ right.semantic ≠ TypeLabel.tock := by
    have hClockIff : left.semantic = TypeLabel.tock ↔
        right.semantic = TypeLabel.tock := by
      have hIsTock := hSync.2.2
      cases hLeft : left.semantic <;> cases hRight : right.semantic <;>
        simp [TypeLabel.isTock, hLeft, hRight] at hIsTock ⊢
    constructor
    · intro hLeft
      have hRight := hClockIff.mp hLeft
      cases left with
      | visible leftLabel =>
          simp only [semantic] at hLeft
          subst leftLabel
          cases right with
          | visible rightLabel =>
              simp only [semantic] at hRight
              subst rightLabel
              exact hCombined rfl
          | «variable» name => simp [semantic, TypeLabel.silent] at hRight
          | future => simp [semantic, TypeLabel.silent] at hRight
      | «variable» name => simp [semantic, TypeLabel.silent] at hLeft
      | future => simp [semantic, TypeLabel.silent] at hLeft
    · intro hRight
      have hLeft := hClockIff.mpr hRight
      cases left with
      | visible leftLabel =>
          simp only [semantic] at hLeft
          subst leftLabel
          cases right with
          | visible rightLabel =>
              simp only [semantic] at hRight
              subst rightLabel
              exact hCombined rfl
          | «variable» name => simp [semantic, TypeLabel.silent] at hRight
          | future => simp [semantic, TypeLabel.silent] at hRight
      | «variable» name => simp [semantic, TypeLabel.silent] at hLeft
      | future => simp [semantic, TypeLabel.silent] at hLeft

end AutomatonConstructionLabel

/-! ### Future-offer computation -/

namespace PendingAutomaton

  /-- States whose offers are referenced by outgoing edges from `state`. -/
  def referencedStates (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      -- A clock transition ends the current cycle.  Its decorated `future`
      -- field describes the offers after taking that transition, but those
      -- offers must not be used while computing the menu still reachable
      -- from `state` in the current cycle.
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        match edge.future with
        | .explicit _ => ∅
        | .at target _ => {target}

  /-- Offers already visible directly on outgoing edges from `state`. -/
  def offersAt (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset BareMessage :=
    (automaton.edges.filter fun edge => edge.source = state).biUnion fun edge =>
      if edge.label.semantic = TypeLabel.tock then ∅
      else
        edge.current ∪
          match edge.future with
          | .explicit offers => offers
          | .at _ _ => ∅

  private def futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
    reached ∪ reached.biUnion automaton.referencedStates

  private def futureReachableAux (automaton : PendingAutomaton) :
      Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
    | 0, reached => reached
    | fuel + 1, reached =>
        futureReachableAux automaton fuel (futureStep automaton reached)

  /-- Every symbolic reference in the graph points to a declared state. -/
  def ReferencesClosed (automaton : PendingAutomaton) : Prop :=
    ∀ state ∈ automaton.states,
      automaton.referencedStates state ⊆ automaton.states

  theorem referencesClosed_of_futureTargetsInStates
      (fragment : AutomatonFragment)
      (hTargets : fragment.FutureTargetsInStates) :
      ({ states := fragment.states, edges := fragment.edges } :
        PendingAutomaton).ReferencesClosed := by
    intro state _ target hTarget
    simp only [referencedStates, Finset.mem_biUnion, Finset.mem_filter]
      at hTarget
    rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
    by_cases hClock : edge.label.semantic = TypeLabel.tock
    · simp [hClock] at hFuture
    · simp only [hClock, if_false] at hFuture
      cases hSpec : edge.future with
      | explicit offers => simp [hSpec] at hFuture
      | «at» referenced removed =>
          simp only [hSpec, Finset.mem_singleton] at hFuture
          subst target
          exact hTargets edge hEdge referenced removed hSpec

  private theorem subset_futureStep (automaton : PendingAutomaton)
      (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureStep reached := by
    exact Finset.subset_union_left

  private theorem futureStep_subset_states
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hReached : reached ⊆ automaton.states) :
      automaton.futureStep reached ⊆ automaton.states := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState
    rcases hState with hState | ⟨source, hSource, hReference⟩
    · exact hReached hState
    · exact hClosed source (hReached hSource) hReference

  private theorem futureReachableAux_fixed_of_futureStep_eq
      (automaton : PendingAutomaton) (reached : Finset TypeAutomatonState)
      (hFixed : automaton.futureStep reached = reached) :
      ∀ fuel, futureReachableAux automaton fuel reached = reached := by
    intro fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
        simp only [futureReachableAux, hFixed]
        exact ih

  private theorem futureStep_futureReachableAux
      (automaton : PendingAutomaton) : ∀ fuel reached,
      automaton.futureStep (futureReachableAux automaton fuel reached) =
        futureReachableAux automaton fuel (automaton.futureStep reached) := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        exact ih (automaton.futureStep reached)

  private theorem futureReachableAux_succ
      (automaton : PendingAutomaton) (fuel : Nat)
      (reached : Finset TypeAutomatonState) :
      futureReachableAux automaton (fuel + 1) reached =
        automaton.futureStep (futureReachableAux automaton fuel reached) := by
    simp only [futureReachableAux]
    exact (futureStep_futureReachableAux automaton fuel reached).symm

  /-- If `k` is at least the number of states still missing from `reached`,
  `k` saturation rounds reach a fixed point. -/
  private theorem futureReachableAux_fixed_after_missing
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed) :
      ∀ k reached,
        reached ⊆ automaton.states →
        automaton.states.card ≤ reached.card + k →
        automaton.futureStep (futureReachableAux automaton k reached) =
          futureReachableAux automaton k reached := by
    intro k
    induction k with
    | zero =>
        intro reached hReached hCard
        have hEqual : reached = automaton.states := by
          exact Finset.eq_of_subset_of_card_le hReached (by simpa using hCard)
        rw [hEqual]
        apply Finset.Subset.antisymm
        · exact futureStep_subset_states automaton automaton.states hClosed
            (fun _ h => h)
        · exact subset_futureStep automaton automaton.states
    | succ k ih =>
        intro reached hReached hCard
        let next := automaton.futureStep reached
        have hNextSubset : next ⊆ automaton.states :=
          futureStep_subset_states automaton reached hClosed hReached
        by_cases hFixed : next = reached
        · have hStepFixed : automaton.futureStep reached = reached := by
            simpa [next] using hFixed
          have hAux : futureReachableAux automaton (k + 1) reached = reached := by
            simp only [futureReachableAux]
            rw [hStepFixed]
            exact futureReachableAux_fixed_of_futureStep_eq
              automaton reached hStepFixed k
          rw [hAux]
          exact hStepFixed
        · have hStrict : reached.card < next.card := by
            apply Finset.card_lt_card
            exact Finset.ssubset_iff_subset_ne.mpr
              ⟨subset_futureStep automaton reached, Ne.symm hFixed⟩
          have hNextCard : automaton.states.card ≤ next.card + k := by
            omega
          simpa only [futureReachableAux, next] using
            ih next hNextSubset hNextCard

  /-- Saturation is stable after `|states|` rounds; running any additional
  number of rounds does not change the reached set. -/
  theorem futureReachableAux_add_card_stable
      (automaton : PendingAutomaton) (hClosed : automaton.ReferencesClosed)
      (reached : Finset TypeAutomatonState)
      (hReached : reached ⊆ automaton.states) (extra : Nat) :
      futureReachableAux automaton (automaton.states.card + extra) reached =
        futureReachableAux automaton automaton.states.card reached := by
    have hFixed : automaton.futureStep
          (futureReachableAux automaton automaton.states.card reached) =
        futureReachableAux automaton automaton.states.card reached := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · exact hReached
      · omega
    induction extra with
    | zero => simp
    | succ extra ih =>
        rw [Nat.add_succ,
          futureReachableAux_succ automaton (automaton.states.card + extra),
          ih, hFixed]

  /-- Pointwise preservation of references lifts to every finite saturation
  depth.  This is the graph-theoretic core used by constructor state tags. -/
  theorem futureReachableAux_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        parent.referencedStates (embed state) =
          (child.referencedStates state).image embed) :
      ∀ fuel reached,
        parent.futureReachableAux fuel (reached.image embed) =
          (child.futureReachableAux fuel reached).image embed := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [futureReachableAux]
        have hStep : parent.futureStep (reached.image embed) =
            (child.futureStep reached).image embed := by
          apply Finset.Subset.antisymm
          · intro target hTarget
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hTarget
            rcases hTarget with hDirect | ⟨source, hSource, hTarget⟩
            · rcases Finset.mem_image.mp hDirect with ⟨state, hState, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨state, Finset.mem_union_left _ hState, rfl⟩
            · rcases Finset.mem_image.mp hSource with ⟨state, hState, rfl⟩
              rw [hReferences] at hTarget
              rcases Finset.mem_image.mp hTarget with
                ⟨referenced, hReferenced, rfl⟩
              apply Finset.mem_image.mpr
              exact ⟨referenced, Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨state, hState, hReferenced⟩), rfl⟩
          · intro target hTarget
            rcases Finset.mem_image.mp hTarget with ⟨state, hState, rfl⟩
            simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
              at hState ⊢
            rcases hState with hDirect | ⟨source, hSource, hReferenced⟩
            · exact Or.inl (Finset.mem_image.mpr ⟨state, hDirect, rfl⟩)
            · right
              refine ⟨embed source,
                Finset.mem_image.mpr ⟨source, hSource, rfl⟩, ?_⟩
              rw [hReferences]
              exact Finset.mem_image.mpr ⟨state, hReferenced, rfl⟩
        rw [hStep]
        exact ih (child.futureStep reached)

  /-- Offers unioned over an embedded reached set are preserved whenever
  `offersAt` is preserved pointwise by the embedding. -/
  theorem biUnion_offersAt_image_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hOffers : ∀ state,
        parent.offersAt (embed state) = child.offersAt state)
      (reached : Finset TypeAutomatonState) :
      (reached.image embed).biUnion parent.offersAt =
        reached.biUnion child.offersAt := by
    ext action
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨state, hState, rfl⟩, hAction⟩
      rw [hOffers] at hAction
      exact ⟨state, hState, hAction⟩
    · rintro ⟨state, hState, hAction⟩
      refine ⟨embed state, ⟨state, hState, rfl⟩, ?_⟩
      rw [hOffers]
      exact hAction

  /-- Saturate references for at most `|Q|` rounds. -/
  def futureReachable (automaton : PendingAutomaton)
      (state : TypeAutomatonState) : Finset TypeAutomatonState :=
    futureReachableAux automaton automaton.states.card {state}

  /-- An exact reference-preserving state embedding preserves the saturated
  same-cycle reachable set.  A larger parent carrier only adds redundant
  saturation rounds. -/
  theorem futureReachable_eq_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        parent.referencedStates (embed state) =
          (child.referencedStates state).image embed)
      (hClosed : child.ReferencesClosed)
      (state : TypeAutomatonState) (hState : state ∈ child.states)
      (hCard : child.states.card ≤ parent.states.card) :
      parent.futureReachable (embed state) =
        (child.futureReachable state).image embed := by
    obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hCard
    unfold futureReachable
    rw [show ({embed state} : Finset TypeAutomatonState) =
        ({state} : Finset TypeAutomatonState).image embed by simp]
    rw [futureReachableAux_image_of_embedding child parent embed hReferences]
    rw [hExtra,
      child.futureReachableAux_add_card_stable hClosed {state} (by
        simpa using hState) extra]

  /-- Two closed pending graphs with the same edge set have the same
  same-cycle reachability from any state carried by both graphs.  Their state
  carriers may differ because constructor views retain different bookkeeping
  states; only the finite saturation bound changes, and closure makes those
  extra rounds redundant. -/
  theorem futureReachable_eq_of_same_edges
      (first second : PendingAutomaton)
      (hEdges : first.edges = second.edges)
      (hFirstClosed : first.ReferencesClosed)
      (hSecondClosed : second.ReferencesClosed)
      (state : TypeAutomatonState)
      (hFirstState : state ∈ first.states)
      (hSecondState : state ∈ second.states) :
      first.futureReachable state = second.futureReachable state := by
    let shared : PendingAutomaton :=
      { states := first.states ∪ second.states, edges := first.edges }
    have hFirstCard : first.states.card ≤ shared.states.card :=
      Finset.card_le_card Finset.subset_union_left
    have hSecondCard : second.states.card ≤ shared.states.card :=
      Finset.card_le_card Finset.subset_union_right
    have hFirst := futureReachable_eq_of_embedding first shared id
      (fun current => by
        change first.referencedStates current =
          (first.referencedStates current).image id
        ext target
        simp) hFirstClosed state hFirstState hFirstCard
    have hSecondReferences : ∀ current,
        shared.referencedStates (id current) =
          (second.referencedStates current).image id := by
      intro current
      unfold referencedStates
      rw [hEdges]
      ext target
      simp
    have hSecond := futureReachable_eq_of_embedding second shared id
      hSecondReferences hSecondClosed state hSecondState hSecondCard
    have hFirst' : shared.futureReachable state =
        first.futureReachable state := by simpa using hFirst
    have hSecond' : shared.futureReachable state =
        second.futureReachable state := by simpa using hSecond
    exact hFirst'.symm.trans hSecond'

  /-- If a state has no same-cycle future references, saturation cannot leave
  that state. -/
  theorem futureReachable_eq_singleton_of_referencedStates_eq_empty
      (automaton : PendingAutomaton) (state : TypeAutomatonState)
      (hReferences : automaton.referencedStates state = ∅) :
      automaton.futureReachable state = {state} := by
    unfold futureReachable
    have hAux : ∀ fuel,
        futureReachableAux automaton fuel {state} = {state} := by
      intro fuel
      induction fuel with
      | zero => rfl
      | succ fuel ih =>
          change futureReachableAux automaton fuel
            (({state} : Finset TypeAutomatonState) ∪
              ({state} : Finset TypeAutomatonState).biUnion
                automaton.referencedStates) = {state}
          simp [hReferences, ih]
    exact hAux automaton.states.card

  private theorem futureStep_mono (automaton : PendingAutomaton)
      {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureStep smaller ⊆ automaton.futureStep larger := by
    intro state hState
    simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hState ⊢
    rcases hState with hDirect | ⟨source, hSource, hReference⟩
    · exact Or.inl (hSubset hDirect)
    · exact Or.inr ⟨source, hSubset hSource, hReference⟩

  private theorem futureReachableAux_mono (automaton : PendingAutomaton)
      (fuel : Nat) {smaller larger : Finset TypeAutomatonState}
      (hSubset : smaller ⊆ larger) :
      automaton.futureReachableAux fuel smaller ⊆
        automaton.futureReachableAux fuel larger := by
    induction fuel generalizing smaller larger with
    | zero => exact hSubset
    | succ fuel ih =>
        exact ih (futureStep_mono automaton hSubset)

  private theorem subset_futureReachableAux (automaton : PendingAutomaton)
      (fuel : Nat) (reached : Finset TypeAutomatonState) :
      reached ⊆ automaton.futureReachableAux fuel reached := by
    induction fuel generalizing reached with
    | zero => exact fun _ h => h
    | succ fuel ih =>
        exact (subset_futureStep automaton reached).trans
          (ih (automaton.futureStep reached))

  /-- Saturated same-cycle reachability unfolds by one symbolic-reference
  step.  This is the finite-graph fixed-point equation behind constructor
  roots: a state reaches itself and everything reachable from each of its
  immediate same-cycle references. -/
  theorem futureReachable_unfold (automaton : PendingAutomaton)
      (state : TypeAutomatonState) (hClosed : automaton.ReferencesClosed)
      (hState : state ∈ automaton.states) :
      automaton.futureReachable state =
        {state} ∪ (automaton.referencedStates state).biUnion
          automaton.futureReachable := by
    let closure := automaton.futureReachable state
    let unfolded := ({state} : Finset TypeAutomatonState) ∪
      (automaton.referencedStates state).biUnion automaton.futureReachable
    have hClosureFixed : automaton.futureStep closure = closure := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [closure, futureReachable] using hState
      · omega
    have hStateClosure : state ∈ closure := by
      apply subset_futureReachableAux automaton automaton.states.card {state}
      simp [closure, futureReachable]
    have hReferenceClosure : ∀ reference,
        reference ∈ automaton.referencedStates state →
          automaton.futureReachable reference ⊆ closure := by
      intro reference hReference target hTarget
      have hReferenceState : reference ∈ automaton.states :=
        hClosed state hState hReference
      have hReferenceInClosure : reference ∈ closure := by
        rw [← hClosureFixed]
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨state, hStateClosure, hReference⟩)
      have hSingletonSubset : ({reference} : Finset TypeAutomatonState) ⊆
          closure := by
        simpa using hReferenceInClosure
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hSingletonSubset
      have hClosureStable : automaton.futureReachableAux
          automaton.states.card closure = closure := by
        exact futureReachableAux_fixed_of_futureStep_eq automaton closure
          hClosureFixed automaton.states.card
      rw [hClosureStable] at hMonotone
      exact hMonotone hTarget
    have hUnfoldedSubset : unfolded ⊆ closure := by
      intro target hTarget
      simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion] at hTarget
      rcases hTarget with rfl | ⟨reference, hReference, hReachable⟩
      · exact hStateClosure
      · exact hReferenceClosure reference hReference hReachable
    have hUnfoldedFixed : automaton.futureStep unfolded = unfolded := by
      apply Finset.Subset.antisymm
      · intro target hTarget
        simp only [futureStep, Finset.mem_union, Finset.mem_biUnion] at hTarget
        rcases hTarget with hDirect | ⟨source, hSource, hReference⟩
        · exact hDirect
        · simp only [unfolded, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion] at hSource ⊢
          rcases hSource with rfl | ⟨first, hFirst, hSourceReachable⟩
          · exact Or.inr ⟨target, hReference,
              subset_futureReachableAux automaton automaton.states.card
                {target} (by simpa)⟩
          · have hFirstState : first ∈ automaton.states :=
              hClosed state hState hFirst
            have hFirstFixed : automaton.futureStep
                (automaton.futureReachable first) =
                automaton.futureReachable first := by
              apply futureReachableAux_fixed_after_missing automaton hClosed
              · simpa [futureReachable] using hFirstState
              · omega
            have hTargetReachable : target ∈
                automaton.futureReachable first := by
              rw [← hFirstFixed]
              exact Finset.mem_union_right _
                (Finset.mem_biUnion.mpr
                  ⟨source, hSourceReachable, hReference⟩)
            exact Or.inr ⟨first, hFirst, hTargetReachable⟩
      · exact subset_futureStep automaton unfolded
    apply Finset.Subset.antisymm
    · have hStart : ({state} : Finset TypeAutomatonState) ⊆ unfolded := by
        exact Finset.subset_union_left
      have hMonotone := futureReachableAux_mono automaton
        automaton.states.card hStart
      have hUnfoldedStable : automaton.futureReachableAux
          automaton.states.card unfolded = unfolded :=
        futureReachableAux_fixed_of_futureStep_eq automaton unfolded
          hUnfoldedFixed automaton.states.card
      simpa [closure, futureReachable, hUnfoldedStable] using hMonotone
    · exact hUnfoldedSubset

  /-- If an embedding preserves every child reference as a parent reference,
  every state reachable in the child maps to a state reachable in the parent.
  This one-sided form permits the parent to add references, as sequence does
  when it installs continuation bridges. -/
  theorem futureReachable_image_subset_of_embedding
      (child parent : PendingAutomaton)
      (embed : TypeAutomatonState → TypeAutomatonState)
      (hReferences : ∀ state,
        (child.referencedStates state).image embed ⊆
          parent.referencedStates (embed state))
      (hParentClosed : parent.ReferencesClosed)
      (state : TypeAutomatonState) (hParentState : embed state ∈ parent.states) :
      (child.futureReachable state).image embed ⊆
        parent.futureReachable (embed state) := by
    let parentReach := parent.futureReachable (embed state)
    have hParentFixed : parent.futureStep parentReach = parentReach := by
      apply futureReachableAux_fixed_after_missing parent hParentClosed
      · simpa [parentReach, futureReachable] using hParentState
      · omega
    have hLiftAux : ∀ fuel reached,
        reached.image embed ⊆ parentReach →
          (child.futureReachableAux fuel reached).image embed ⊆
            parentReach := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih (child.futureStep reached)
          intro target hTarget
          rcases Finset.mem_image.mp hTarget with
            ⟨childTarget, hChildTarget, rfl⟩
          simp only [futureStep, Finset.mem_union, Finset.mem_biUnion]
            at hChildTarget
          rcases hChildTarget with hDirect |
              ⟨childSource, hSource, hReference⟩
          · exact hReached (Finset.mem_image.mpr
              ⟨childTarget, hDirect, rfl⟩)
          · have hMappedSource : embed childSource ∈ parentReach :=
              hReached (Finset.mem_image.mpr
                ⟨childSource, hSource, rfl⟩)
            have hMappedReference : embed childTarget ∈
                parent.referencedStates (embed childSource) :=
              hReferences childSource
                (Finset.mem_image.mpr ⟨childTarget, hReference, rfl⟩)
            rw [← hParentFixed]
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨embed childSource, hMappedSource, hMappedReference⟩)
    unfold futureReachable
    apply hLiftAux child.states.card {state}
    intro target hTarget
    rcases Finset.mem_image.mp hTarget with ⟨source, hSource, rfl⟩
    simp only [Finset.mem_singleton] at hSource
    subst source
    exact subset_futureReachableAux parent parent.states.card {embed state}
      (by simp)

  /-- The starting state is always contained in its finite reference closure. -/
  theorem mem_futureReachable_self (automaton : PendingAutomaton)
      (state : TypeAutomatonState) :
      state ∈ automaton.futureReachable state := by
    apply subset_futureReachableAux automaton automaton.states.card {state}
    simp [futureReachable]

  /-- Every immediate same-cycle reference is contained in the finite
  reference closure of its source. -/
  theorem referencedStates_subset_futureReachable
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states) :
      automaton.referencedStates source ⊆
        automaton.futureReachable source := by
    rw [automaton.futureReachable_unfold source hClosed hSource]
    intro target hTarget
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨target, hTarget, automaton.mem_futureReachable_self target⟩)

  /-- Reference closure is transitive: the closure of any already reached
  state is contained in the original closure. -/
  theorem futureReachable_subset_of_mem
      (automaton : PendingAutomaton) {source target : TypeAutomatonState}
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states)
      (hTarget : target ∈ automaton.futureReachable source) :
      automaton.futureReachable target ⊆
        automaton.futureReachable source := by
    let closure := automaton.futureReachable source
    have hClosureFixed : automaton.futureStep closure = closure := by
      apply futureReachableAux_fixed_after_missing automaton hClosed
      · simpa [closure, futureReachable] using hSource
      · omega
    have hSingletonSubset : ({target} : Finset TypeAutomatonState) ⊆
        closure := by
      simpa [closure] using hTarget
    have hMonotone := futureReachableAux_mono automaton
      automaton.states.card hSingletonSubset
    have hClosureStable : automaton.futureReachableAux
        automaton.states.card closure = closure :=
      futureReachableAux_fixed_of_futureStep_eq automaton closure
        hClosureFixed automaton.states.card
    change automaton.futureReachableAux automaton.states.card {target} ⊆
      closure
    rw [← hClosureStable]
    exact hMonotone

  /-- A finite reference closure is contained in any set which contains its
  source and is closed under immediate references. -/
  theorem futureReachable_subset_of_reference_closed
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (allowed : Finset TypeAutomatonState)
      (hSource : source ∈ allowed)
      (hAllowed : ∀ state ∈ allowed,
        automaton.referencedStates state ⊆ allowed) :
      automaton.futureReachable source ⊆ allowed := by
    unfold futureReachable
    have hAux : ∀ fuel reached, reached ⊆ allowed →
        automaton.futureReachableAux fuel reached ⊆ allowed := by
      intro fuel
      induction fuel with
      | zero =>
          intro reached hReached
          exact hReached
      | succ fuel ih =>
          intro reached hReached
          apply ih
          intro state hState
          simp only [futureStep, Finset.mem_union,
            Finset.mem_biUnion] at hState
          rcases hState with hState | ⟨parent, hParent, hReference⟩
          · exact hReached hState
          · exact hAllowed parent (hReached hParent) hReference
    apply hAux
    simpa using hSource

  /-- A root whose immediate references are exactly a set of child entries,
  possibly together with a self-reference, reaches precisely itself and the
  complete closures of those child entries.  This packages the harmless
  self-loop pattern used by the offer constructors. -/
  theorem futureReachable_eq_self_union_biUnion
      (automaton : PendingAutomaton) (source : TypeAutomatonState)
      (entries : Finset TypeAutomatonState)
      (hClosed : automaton.ReferencesClosed)
      (hSource : source ∈ automaton.states)
      (hReferencesUpper : automaton.referencedStates source ⊆
        insert source entries)
      (hEntries : entries ⊆ automaton.referencedStates source) :
      automaton.futureReachable source =
        {source} ∪ entries.biUnion automaton.futureReachable := by
    apply Finset.Subset.antisymm
    · apply automaton.futureReachable_subset_of_reference_closed source
        ({source} ∪ entries.biUnion automaton.futureReachable)
      · simp
      · intro state hState reference hReference
        simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.mem_biUnion] at hState ⊢
        rcases hState with rfl | ⟨entry, hEntry, hReachable⟩
        · have hClassified := hReferencesUpper hReference
          simp only [Finset.mem_insert] at hClassified
          rcases hClassified with rfl | hEntry
          · exact Or.inl rfl
          · exact Or.inr ⟨reference, hEntry,
              automaton.mem_futureReachable_self reference⟩
        · have hEntryState : entry ∈ automaton.states :=
            hClosed source hSource (hEntries hEntry)
          have hReferenceReachable : reference ∈
              automaton.futureReachable entry := by
            have hStateInStates : state ∈ automaton.states :=
              (automaton.futureReachable_subset_of_reference_closed
                entry automaton.states hEntryState
                  (fun current hCurrent => hClosed current hCurrent))
                hReachable
            have hReferenceAtState :=
              automaton.referencedStates_subset_futureReachable state
                hClosed hStateInStates
            have hStateClosure := automaton.futureReachable_subset_of_mem
              hClosed hEntryState hReachable
            exact hStateClosure (hReferenceAtState hReference)
          exact Or.inr ⟨entry, hEntry, hReferenceReachable⟩
    · intro state hState
      simp only [Finset.mem_union, Finset.mem_singleton,
        Finset.mem_biUnion] at hState
      rcases hState with rfl | ⟨entry, hEntry, hReachable⟩
      · exact automaton.mem_futureReachable_self _
      · have hEntryReachable :=
          automaton.referencedStates_subset_futureReachable source hClosed
            hSource (hEntries hEntry)
        exact (automaton.futureReachable_subset_of_mem hClosed hSource
          hEntryReachable) hReachable

end PendingAutomaton

/--
Compute `OF(q)` on a complete pending automaton.

Starting at `q`, follow every `FutureSpec.at` reference and union the current
and explicit future offers encountered. At most `|Q|` rounds are needed because
revisiting a finite state cannot expose a new state.
-/
def computeFuture (automaton : PendingAutomaton)
    (state : TypeAutomatonState) : Finset BareMessage :=
  (automaton.futureReachable state).biUnion automaton.offersAt

/-- Once a state is in the same-cycle reference closure, everything reachable
from it is already included in the source's future menu. -/
theorem computeFuture_subset_of_mem_futureReachable
    (automaton : PendingAutomaton) {source target : TypeAutomatonState}
    (hClosed : automaton.ReferencesClosed)
    (hSource : source ∈ automaton.states)
    (hTarget : target ∈ automaton.futureReachable source) :
    computeFuture automaton target ⊆ computeFuture automaton source := by
  intro action hAction
  simp only [computeFuture, Finset.mem_biUnion] at hAction ⊢
  rcases hAction with ⟨reached, hReached, hOffer⟩
  exact ⟨reached,
    automaton.futureReachable_subset_of_mem hClosed hSource hTarget hReached,
    hOffer⟩

/-- If following a symbolic reference can only decrease the directly visible
offer menu, then the finite reference closure adds no offers.  This is the
generic fixed-point principle used by the execution view of a parallel
product. -/
theorem computeFuture_eq_offersAt_of_references_monotone
    (automaton : PendingAutomaton) (source : TypeAutomatonState)
    (hClosed : automaton.ReferencesClosed)
    (hSource : source ∈ automaton.states)
    (hMonotone : ∀ state ∈ automaton.states,
      ∀ target ∈ automaton.referencedStates state,
        automaton.offersAt target ⊆ automaton.offersAt state) :
    computeFuture automaton source = automaton.offersAt source := by
  classical
  let allowed := automaton.states.filter fun state =>
    automaton.offersAt state ⊆ automaton.offersAt source
  have hSourceAllowed : source ∈ allowed := by
    simp [allowed, hSource]
  have hAllowedClosed : ∀ state ∈ allowed,
      automaton.referencedStates state ⊆ allowed := by
    intro state hState target hTarget
    have hFields := Finset.mem_filter.mp hState
    have hTargetState := hClosed state hFields.1 hTarget
    apply Finset.mem_filter.mpr
    exact ⟨hTargetState, (hMonotone state hFields.1 target hTarget).trans
      hFields.2⟩
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [computeFuture, Finset.mem_biUnion] at hAction
    rcases hAction with ⟨state, hReachable, hOffer⟩
    have hReachableAllowed :=
      automaton.futureReachable_subset_of_reference_closed source allowed
        hSourceAllowed hAllowedClosed hReachable
    exact (Finset.mem_filter.mp hReachableAllowed).2 hOffer
  · intro action hAction
    simp only [computeFuture, Finset.mem_biUnion]
    exact ⟨source, automaton.mem_futureReachable_self source, hAction⟩

/-- Predicate-scoped variant of reference monotonicity.  It is useful when a
constructor carrier contains bookkeeping states which are deliberately not
semantic residuals: only the closure starting from a represented state must
remain represented and menu-decreasing. -/
theorem computeFuture_eq_offersAt_of_references_monotone_on
    (automaton : PendingAutomaton) (source : TypeAutomatonState)
    (represented : TypeAutomatonState → Prop)
    (hClosed : automaton.ReferencesClosed)
    (hSourceState : source ∈ automaton.states)
    (hSource : represented source)
    (hStep : ∀ state ∈ automaton.states, represented state →
      ∀ target ∈ automaton.referencedStates state,
        represented target ∧
          automaton.offersAt target ⊆ automaton.offersAt state) :
    computeFuture automaton source = automaton.offersAt source := by
  classical
  let allowed := automaton.states.filter fun state =>
    represented state ∧
      automaton.offersAt state ⊆ automaton.offersAt source
  have hSourceAllowed : source ∈ allowed := by
    simp [allowed, hSourceState, hSource]
  have hAllowedClosed : ∀ state ∈ allowed,
      automaton.referencedStates state ⊆ allowed := by
    intro state hState target hTarget
    have hFields := Finset.mem_filter.mp hState
    have hTargetState := hClosed state hFields.1 hTarget
    have hNext := hStep state hFields.1 hFields.2.1 target hTarget
    apply Finset.mem_filter.mpr
    exact ⟨hTargetState, hNext.1, hNext.2.trans hFields.2.2⟩
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [computeFuture, Finset.mem_biUnion] at hAction
    rcases hAction with ⟨state, hReachable, hOffer⟩
    have hReachableAllowed :=
      automaton.futureReachable_subset_of_reference_closed source allowed
        hSourceAllowed hAllowedClosed hReachable
    exact (Finset.mem_filter.mp hReachableAllowed).2.2 hOffer
  · intro action hAction
    simp only [computeFuture, Finset.mem_biUnion]
    exact ⟨source, automaton.mem_futureReachable_self source, hAction⟩

/-- `computeFuture` at a constructor root with only child-entry references
and an optional self-reference is the root's direct menu union the complete
menu of every child entry. -/
theorem computeFuture_eq_offersAt_union_biUnion
    (automaton : PendingAutomaton) (source : TypeAutomatonState)
    (entries : Finset TypeAutomatonState)
    (hClosed : automaton.ReferencesClosed)
    (hSource : source ∈ automaton.states)
    (hReferencesUpper : automaton.referencedStates source ⊆
      insert source entries)
    (hEntries : entries ⊆ automaton.referencedStates source) :
    computeFuture automaton source =
      automaton.offersAt source ∪ entries.biUnion (computeFuture automaton) := by
  rw [computeFuture,
    automaton.futureReachable_eq_self_union_biUnion source entries hClosed
      hSource hReferencesUpper hEntries]
  ext action
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨state, hState, hAction⟩
    rcases hState with rfl | ⟨entry, hEntry, hReachable⟩
    · exact Or.inl hAction
    · apply Or.inr
      refine ⟨entry, hEntry, ?_⟩
      change action ∈
        (automaton.futureReachable entry).biUnion automaton.offersAt
      exact Finset.mem_biUnion.mpr ⟨state, hReachable, hAction⟩
  · rintro (hAction | ⟨entry, hEntry, hFuture⟩)
    · exact ⟨source, Or.inl rfl, hAction⟩
    · change action ∈
          (automaton.futureReachable entry).biUnion automaton.offersAt
        at hFuture
      rcases Finset.mem_biUnion.mp hFuture with
        ⟨state, hReachable, hAction⟩
      exact ⟨state, Or.inr ⟨entry, hEntry, hReachable⟩, hAction⟩

/-- `computeFuture` is the least closed future menu: collect the offers stored
at the current state, then union the complete menus of every immediate
same-cycle symbolic reference. -/
theorem computeFuture_unfold
    (automaton : PendingAutomaton) (state : TypeAutomatonState)
    (hClosed : automaton.ReferencesClosed)
    (hState : state ∈ automaton.states) :
    computeFuture automaton state =
      automaton.offersAt state ∪
        (automaton.referencedStates state).biUnion
          (computeFuture automaton) := by
  rw [computeFuture, automaton.futureReachable_unfold state hClosed hState]
  ext action
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨reached, hReached, hOffer⟩
    rcases hReached with rfl | ⟨reference, hReference, hReachable⟩
    · exact Or.inl hOffer
    · apply Or.inr
      refine ⟨reference, hReference, ?_⟩
      change action ∈
        (automaton.futureReachable reference).biUnion automaton.offersAt
      exact Finset.mem_biUnion.mpr ⟨reached, hReachable, hOffer⟩
  · rintro (hOffer | ⟨reference, hReference, hFuture⟩)
    · exact ⟨state, Or.inl rfl, hOffer⟩
    · change action ∈
          (automaton.futureReachable reference).biUnion automaton.offersAt
        at hFuture
      rcases Finset.mem_biUnion.mp hFuture with
        ⟨reached, hReachable, hOffer⟩
      exact ⟨reached, Or.inr ⟨reference, hReference, hReachable⟩, hOffer⟩

/-- A constructor embedding preserves `computeFuture` once it preserves the
local reference and offer observations.  A larger parent state set merely
runs extra saturation rounds, which are harmless by finite stabilization. -/
theorem computeFuture_eq_of_embedding
    (child parent : PendingAutomaton)
    (embed : TypeAutomatonState → TypeAutomatonState)
    (hReferences : ∀ state,
      parent.referencedStates (embed state) =
        (child.referencedStates state).image embed)
    (hOffers : ∀ state,
      parent.offersAt (embed state) = child.offersAt state)
    (hClosed : child.ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ child.states)
    (hCard : child.states.card ≤ parent.states.card) :
    computeFuture parent (embed state) = computeFuture child state := by
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hCard
  unfold computeFuture PendingAutomaton.futureReachable
  rw [show ({embed state} : Finset TypeAutomatonState) =
      ({state} : Finset TypeAutomatonState).image embed by simp]
  rw [PendingAutomaton.futureReachableAux_image_of_embedding
    child parent embed hReferences]
  rw [hExtra,
    child.futureReachableAux_add_card_stable hClosed {state} (by
      simpa using hState) extra]
  exact PendingAutomaton.biUnion_offersAt_image_of_embedding
    child parent embed hOffers _

/-- `computeFuture` is independent of bookkeeping-only differences in the
state carrier once both pending graphs are closed and have the same edges. -/
theorem computeFuture_eq_of_same_edges
    (first second : PendingAutomaton)
    (hEdges : first.edges = second.edges)
    (hFirstClosed : first.ReferencesClosed)
    (hSecondClosed : second.ReferencesClosed)
    (state : TypeAutomatonState)
    (hFirstState : state ∈ first.states)
    (hSecondState : state ∈ second.states) :
    computeFuture first state = computeFuture second state := by
  let shared : PendingAutomaton :=
    { states := first.states ∪ second.states, edges := first.edges }
  have hFirstCard : first.states.card ≤ shared.states.card :=
    Finset.card_le_card Finset.subset_union_left
  have hSecondCard : second.states.card ≤ shared.states.card :=
    Finset.card_le_card Finset.subset_union_right
  have hFirst := computeFuture_eq_of_embedding first shared id
    (fun current => by
      change first.referencedStates current =
        (first.referencedStates current).image id
      ext target
      simp)
    (fun current => by
      change first.offersAt current = first.offersAt current
      rfl)
      hFirstClosed state hFirstState hFirstCard
  have hSecondReferences : ∀ current,
      shared.referencedStates (id current) =
        (second.referencedStates current).image id := by
    intro current
    unfold PendingAutomaton.referencedStates
    rw [hEdges]
    ext target
    simp
  have hSecondOffers : ∀ current,
      shared.offersAt (id current) = second.offersAt current := by
    intro current
    unfold PendingAutomaton.offersAt
    rw [hEdges]
    rfl
  have hSecond := computeFuture_eq_of_embedding second shared id
    hSecondReferences hSecondOffers hSecondClosed state hSecondState hSecondCard
  have hFirst' : computeFuture shared state = computeFuture first state := by
    simpa using hFirst
  have hSecond' : computeFuture shared state = computeFuture second state := by
    simpa using hSecond
  exact hFirst'.symm.trans hSecond'

/-- With no outgoing same-cycle reference, future resolution is exactly the
offers stored directly at the state. -/
theorem computeFuture_eq_offersAt_of_referencedStates_eq_empty
    (automaton : PendingAutomaton) (state : TypeAutomatonState)
    (hReferences : automaton.referencedStates state = ∅) :
    computeFuture automaton state = automaton.offersAt state := by
  rw [computeFuture,
    automaton.futureReachable_eq_singleton_of_referencedStates_eq_empty
      state hReferences]
  simp

/-- A graph containing only explicit future fields has no symbolic future
references.  Parallel products have this form after their child decorations
have been resolved. -/
theorem PendingAutomaton.referencedStates_eq_empty_of_all_explicit
    (automaton : PendingAutomaton)
    (hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers)
    (state : TypeAutomatonState) :
    automaton.referencedStates state = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _⟩, hFuture⟩
  obtain ⟨offers, hOffers⟩ := hExplicit edge hEdge
  simp [hOffers] at hFuture

/-- Consequently, resolution on an all-explicit graph only unions the offers
stored directly on outgoing edges. -/
theorem computeFuture_eq_offersAt_of_all_explicit
    (automaton : PendingAutomaton)
    (hExplicit : ∀ edge ∈ automaton.edges,
      ∃ offers, edge.future = .explicit offers)
    (state : TypeAutomatonState) :
    computeFuture automaton state = automaton.offersAt state := by
  apply computeFuture_eq_offersAt_of_referencedStates_eq_empty
  exact automaton.referencedStates_eq_empty_of_all_explicit hExplicit state

/-! ### Marker-augmented future resolution

A `.variable name` marker edge produced by the compiler carries no offers of
its own (`current = ∅`, `future = .explicit ∅`), so it contributes nothing to
`computeFuture` until an enclosing recursion binder installs its backedge.
`markerAugmentedPending` activates every such marker with a fixed menu.

The point of the construction is that markers stay `.explicit`, so the
*reference* structure — and therefore same-cycle reachability — is completely
unchanged; only `offersAt` grows, and only at marker sources.  Consequently the
recursion future leaf can reuse the ordinary `CompilationFutureCorrect`
invariant plus a reachability side condition, instead of redeveloping the
entire future correspondence inside the installed recursion graph. -/
def markerAugmentedPending (fragment : AutomatonFragment) (name : String)
    (menu : Finset BareMessage) : PendingAutomaton :=
  { states := fragment.states
    edges := fragment.edges.image fun edge =>
      if edge.label = AutomatonConstructionLabel.variable name then
        { edge with future := .explicit menu }
      else edge }

/-- A state is a marker source when it has an outgoing `.variable name` edge. -/
def MarkerSource (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = state ∧ edge.label = AutomatonConstructionLabel.variable name

/-- The shape every compiled `.variable` marker edge has: no offers at all. -/
def MarkerEdgesInert (fragment : AutomatonFragment) (name : String) : Prop :=
  ∀ edge ∈ fragment.edges,
    edge.label = AutomatonConstructionLabel.variable name →
      edge.current = ∅ ∧ edge.future = FutureSpec.explicit ∅

/-- Activating markers does not change the same-cycle reference structure. -/
theorem markerAugmentedPending_referencedStates
    (fragment : AutomatonFragment) (name : String) (menu : Finset BareMessage)
    (hMarkers : MarkerEdgesInert fragment name)
    (state : TypeAutomatonState) :
    (markerAugmentedPending fragment name menu).referencedStates state =
      (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).referencedStates
        state := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, markerAugmentedPending,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨⟨original, hOriginal, rfl⟩, hSource⟩, hTarget⟩
    by_cases hMarker :
        original.label = AutomatonConstructionLabel.variable name
    · exfalso
      simp only [hMarker, if_pos rfl] at hSource hTarget
      simp at hTarget
    · simp only [if_neg hMarker] at hSource hTarget
      exact ⟨original, ⟨hOriginal, hSource⟩, hTarget⟩
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    by_cases hMarker : edge.label = AutomatonConstructionLabel.variable name
    · exfalso
      rw [(hMarkers edge hEdge hMarker).2] at hTarget
      simp at hTarget
    · exact ⟨edge, ⟨⟨edge, hEdge, by simp [hMarker]⟩, by simp [hMarker, hSource]⟩,
        by simp [hMarker, hTarget]⟩

/-- Consequently the saturated same-cycle reachable set is unchanged. -/
theorem markerAugmentedPending_futureReachable
    (fragment : AutomatonFragment) (name : String) (menu : Finset BareMessage)
    (hMarkers : MarkerEdgesInert fragment name)
    (hClosed : (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ fragment.states) :
    (markerAugmentedPending fragment name menu).futureReachable state =
      (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).futureReachable
        state := by
  classical
  have hAugClosed :
      (markerAugmentedPending fragment name menu).ReferencesClosed := by
    intro current hCurrent target hTarget
    rw [markerAugmentedPending_referencedStates fragment name menu hMarkers]
      at hTarget
    exact hClosed current hCurrent hTarget
  have hResult := PendingAutomaton.futureReachable_eq_of_embedding
    (markerAugmentedPending fragment name menu)
    (⟨fragment.states, fragment.edges⟩ : PendingAutomaton) id
    (fun current => by
      rw [markerAugmentedPending_referencedStates fragment name menu hMarkers]
      simp)
    hAugClosed state hState (by simp [markerAugmentedPending])
  simpa using hResult.symm

/-- Exact decomposition of a marker-augmented future menu: the ordinary menu,
plus the activation menu exactly when some reachable state is a marker
source. -/
theorem mem_computeFuture_markerAugmented
    (fragment : AutomatonFragment) (name : String) (menu : Finset BareMessage)
    (hMarkers : MarkerEdgesInert fragment name)
    (hClosed : (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ fragment.states)
    (action : BareMessage) :
    action ∈ computeFuture (markerAugmentedPending fragment name menu) state ↔
      action ∈ computeFuture
          (⟨fragment.states, fragment.edges⟩ : PendingAutomaton) state ∨
        (action ∈ menu ∧
          ∃ reached ∈ (⟨fragment.states, fragment.edges⟩ : PendingAutomaton).futureReachable
                state,
            MarkerSource fragment name reached) := by
  classical
  simp only [computeFuture, Finset.mem_biUnion,
    markerAugmentedPending_futureReachable fragment name menu hMarkers hClosed
      state hState]
  constructor
  · rintro ⟨reached, hReached, hOffer⟩
    simp only [PendingAutomaton.offersAt, markerAugmentedPending,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hOffer
    rcases hOffer with ⟨edge, ⟨⟨original, hOriginal, rfl⟩, hSource⟩, hAction⟩
    by_cases hMarker :
        original.label = AutomatonConstructionLabel.variable name
    · right
      simp only [hMarker, if_pos rfl] at hSource hAction
      have hFields := hMarkers original hOriginal hMarker
      simp only [hFields.1, Finset.empty_union] at hAction
      have hNotTock : ¬ (AutomatonConstructionLabel.variable name).semantic =
          TypeLabel.tock := by
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      rw [if_neg (by simpa [hMarker] using hNotTock)] at hAction
      exact ⟨by simpa using hAction,
        reached, hReached, ⟨original, hOriginal, hSource, hMarker⟩⟩
    · left
      simp only [if_neg hMarker] at hSource hAction
      exact ⟨reached, hReached, by
        simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
          Finset.mem_filter]
        exact ⟨original, ⟨hOriginal, hSource⟩, hAction⟩⟩
  · rintro (⟨reached, hReached, hOffer⟩ | ⟨hMenu, reached, hReached,
      ⟨edge, hEdge, hSource, hLabel⟩⟩)
    · refine ⟨reached, hReached, ?_⟩
      simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
        Finset.mem_filter] at hOffer
      rcases hOffer with ⟨original, ⟨hOriginal, hOriginalSource⟩, hAction⟩
      by_cases hMarker :
          original.label = AutomatonConstructionLabel.variable name
      · exfalso
        have hFields := hMarkers original hOriginal hMarker
        rw [hFields.1, hFields.2] at hAction
        simp at hAction
      · simp only [PendingAutomaton.offersAt, markerAugmentedPending,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
        exact ⟨original, ⟨⟨original, hOriginal, by simp [hMarker]⟩,
          by simp [hMarker, hOriginalSource]⟩, by simp [hMarker, hAction]⟩
    · refine ⟨reached, hReached, ?_⟩
      simp only [PendingAutomaton.offersAt, markerAugmentedPending,
        Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      refine ⟨{ edge with future := .explicit menu },
        ⟨⟨edge, hEdge, by simp [hLabel]⟩, by simp [hSource]⟩, ?_⟩
      have hFields := hMarkers edge hEdge hLabel
      have hNotTock : ¬ edge.label.semantic = TypeLabel.tock := by
        simp [hLabel, AutomatonConstructionLabel.semantic, TypeLabel.silent]
      simp only [if_neg hNotTock, hFields.1, Finset.empty_union]
      simpa using hMenu

/-! ### Same-cycle marker reachability

`mem_computeFuture_markerAugmented` reduces an activated marker menu to one
Boolean side condition: whether any same-cycle reachable state still carries an
outgoing `.variable name` edge.  The predicate is named here, together with the
transport lemmas used to compute it constructor by constructor. -/

/-- Some state reachable in the same cycle still calls the enclosing binder. -/
def MarkerReachable (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) : Prop :=
  ∃ reached ∈ (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).futureReachable state,
    MarkerSource fragment name reached

/-- A fragment with no marker edges at all reaches no marker. -/
theorem not_markerReachable_of_no_marker_edges
    (fragment : AutomatonFragment) (name : String)
    (hNone : ∀ edge ∈ fragment.edges,
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (state : TypeAutomatonState) :
    ¬ MarkerReachable fragment name state := by
  rintro ⟨reached, _, edge, hEdge, _, hLabel⟩
  exact hNone edge hEdge hLabel

/-- Marker reachability transports along an exact reference-preserving state
embedding whose image reflects marker sources. -/
theorem markerReachable_of_embedding
    (child parent : AutomatonFragment) (name : String)
    (embed : TypeAutomatonState → TypeAutomatonState)
    (hReferences : ∀ state,
      (⟨parent.states, parent.edges⟩ : PendingAutomaton).referencedStates
          (embed state) =
        ((⟨child.states, child.edges⟩ :
          PendingAutomaton).referencedStates state).image embed)
    (hClosed : (⟨child.states, child.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hCard : child.states.card ≤ parent.states.card)
    (hMarker : ∀ state ∈ child.states,
      (MarkerSource parent name (embed state) ↔ MarkerSource child name state))
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    MarkerReachable parent name (embed state) ↔
      MarkerReachable child name state := by
  classical
  have hReach := PendingAutomaton.futureReachable_eq_of_embedding
    (⟨child.states, child.edges⟩ : PendingAutomaton)
    (⟨parent.states, parent.edges⟩ : PendingAutomaton) embed hReferences
      hClosed state hState hCard
  have hInside : (⟨child.states, child.edges⟩ :
      PendingAutomaton).futureReachable state ⊆ child.states := by
    apply PendingAutomaton.futureReachable_subset_of_reference_closed
    · exact hState
    · intro current hCurrent
      exact hClosed current hCurrent
  constructor
  · rintro ⟨reached, hReached, hSource⟩
    rw [hReach] at hReached
    rcases Finset.mem_image.mp hReached with ⟨original, hOriginal, rfl⟩
    exact ⟨original, hOriginal,
      (hMarker original (hInside hOriginal)).mp hSource⟩
  · rintro ⟨reached, hReached, hSource⟩
    refine ⟨embed reached, ?_, (hMarker reached (hInside hReached)).mpr hSource⟩
    rw [hReach]
    exact Finset.mem_image.mpr ⟨reached, hReached, rfl⟩

/-- Marker reachability out of a constructor root whose immediate references
are exactly a finite set of child entries (possibly with a harmless
self-reference). -/
theorem markerReachable_root_of_entries
    (fragment : AutomatonFragment) (name : String)
    (source : TypeAutomatonState) (entries : Finset TypeAutomatonState)
    (hClosed : (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).ReferencesClosed)
    (hSource : source ∈ fragment.states)
    (hReferencesUpper : (⟨fragment.states, fragment.edges⟩ :
        PendingAutomaton).referencedStates source ⊆ insert source entries)
    (hEntries : entries ⊆ (⟨fragment.states, fragment.edges⟩ :
      PendingAutomaton).referencedStates source) :
    MarkerReachable fragment name source ↔
      (MarkerSource fragment name source ∨
        ∃ entry ∈ entries, MarkerReachable fragment name entry) := by
  classical
  have hReach := PendingAutomaton.futureReachable_eq_self_union_biUnion
    (⟨fragment.states, fragment.edges⟩ : PendingAutomaton) source entries
      hClosed hSource hReferencesUpper hEntries
  constructor
  · rintro ⟨reached, hReached, hMarker⟩
    rw [hReach] at hReached
    simp only [Finset.mem_union, Finset.mem_singleton,
      Finset.mem_biUnion] at hReached
    rcases hReached with rfl | ⟨entry, hEntry, hInner⟩
    · exact Or.inl hMarker
    · exact Or.inr ⟨entry, hEntry, ⟨reached, hInner, hMarker⟩⟩
  · rintro (hMarker | ⟨entry, hEntry, reached, hReached, hMarker⟩)
    · exact ⟨source, PendingAutomaton.mem_futureReachable_self _ _, hMarker⟩
    · refine ⟨reached, ?_, hMarker⟩
      rw [hReach]
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨entry, hEntry, hReached⟩)

/-- Regression for the clock boundary in future resolution.  Although the
edge out of `root` is decorated with the offers available at `final`, those
offers belong to the next cycle and are therefore not reachable from `root`
for the purpose of `OF(root)`.  This is the graph shape produced by the left
side of `tock ; a!`. -/
theorem computeFuture_stops_at_clock_regression :
    let action : BareMessage := ("a", .send)
    let clockEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .tock
        label := .visible .tock
        current := ∅
        future := .at .final ∅
        target := .final }
    let messageEdge : PendingAutomatonEdge :=
      { source := .final
        environment := .empty
        label := .visible .silent
        current := {action}
        future := .explicit ∅
        target := .final }
    let graph : PendingAutomaton :=
      { states := {.root, .final}, edges := {clockEdge, messageEdge} }
    computeFuture graph .root = ∅ := by
  native_decide

/-- A recursion marker has no future menu until its binder installs the
back-edge.  Resolving a child fragment before that installation therefore
loses information: this is the small graph phenomenon that constructor
combinators (notably parallel product) must preserve symbolically. -/
theorem computeFuture_changes_when_recursion_backedge_is_installed :
    let action : BareMessage := ("a", .send)
    let variableEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .empty
        label := .variable "x"
        current := ∅
        future := .explicit ∅
        target := .final }
    let backEdge : PendingAutomatonEdge :=
      { source := .root
        environment := .empty
        label := .visible .silent
        current := ∅
        future := .at .final ∅
        target := .final }
    let messageEdge : PendingAutomatonEdge :=
      { source := .final
        environment := .empty
        label := .visible .silent
        current := {action}
        future := .explicit ∅
        target := .final }
    let openGraph : PendingAutomaton :=
      { states := {.root, .final}, edges := {variableEdge, messageEdge} }
    let closedGraph : PendingAutomaton :=
      { states := {.root, .final}, edges := {backEdge, messageEdge} }
    computeFuture openGraph .root = ∅ ∧
      computeFuture closedGraph .root = {action} := by
  native_decide

/-- Package a constructor graph without resolving its future references. -/
def finishAutomatonFragment
    (states : Finset TypeAutomatonState) (initial : TypeAutomatonState)
    (accepting skipping completing : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) : AutomatonFragment :=
  { states := states
    initial := initial
    accepting := accepting
    skipping := skipping
    completing := completing
    edges := edges }

/-- Resolve future fields against all states and edges currently in a fragment. -/
def resolvedAutomatonEdges
    (automaton : AutomatonFragment) : Finset AutomatonFragmentEdge :=
  let pending : PendingAutomaton :=
    { states := automaton.states, edges := automaton.edges }
  automaton.edges.image fun edge =>
      let resolvedFuture :=
        match edge.future with
        | .explicit offers => offers
        | .at state removed => computeFuture pending state \ removed
      { source := edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := resolvedFuture
        target := edge.target }

/-- The current and resolved future fields of a non-clock edge are already
contained in the same-cycle menu at its source.  Removing offers from an
`at` decoration can only make the resolved edge smaller than the graph
fixed point. -/
theorem resolvedAutomatonEdge_offers_subset_computeFuture
    (fragment : AutomatonFragment) (edge : AutomatonFragmentEdge)
    (hEdge : edge ∈ resolvedAutomatonEdges fragment)
    (hClosed : ({ states := fragment.states, edges := fragment.edges } :
      PendingAutomaton).ReferencesClosed)
    (hSource : edge.source ∈ fragment.states)
    (hNonClock : edge.label.semantic ≠ TypeLabel.tock) :
    edge.current ∪ edge.future ⊆
      computeFuture { states := fragment.states, edges := fragment.edges }
        edge.source := by
  classical
  let pending : PendingAutomaton :=
    { states := fragment.states, edges := fragment.edges }
  rw [computeFuture_unfold pending edge.source hClosed hSource]
  simp only [resolvedAutomatonEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨raw, hRaw, rfl⟩
  intro action hAction
  simp only [Finset.mem_union, Finset.mem_biUnion]
  cases hSpec : raw.future with
  | explicit future =>
      simp only [hSpec] at hAction hNonClock ⊢
      left
      simp only [pending, PendingAutomaton.offersAt,
        Finset.mem_biUnion, Finset.mem_filter]
      refine ⟨raw, ⟨hRaw, rfl⟩, ?_⟩
      simpa [hSpec, hNonClock] using hAction
  | «at» target removed =>
      simp only [hSpec] at hAction hNonClock ⊢
      rcases Finset.mem_union.mp hAction with hCurrent | hFuture
      · left
        simp only [pending, PendingAutomaton.offersAt,
          Finset.mem_biUnion, Finset.mem_filter]
        refine ⟨raw, ⟨hRaw, rfl⟩, ?_⟩
        simp [hSpec, hNonClock, hCurrent]
      · right
        refine ⟨target, ?_, ?_⟩
        · simp only [pending, PendingAutomaton.referencedStates,
            Finset.mem_biUnion, Finset.mem_filter]
          refine ⟨raw, ⟨hRaw, rfl⟩, ?_⟩
          simp [hSpec, hNonClock]
        · exact (Finset.mem_sdiff.mp hFuture).1

def childState (index : Nat) (state : TypeAutomatonState) :
    TypeAutomatonState := .child index state

def childStates (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.states.image (childState index)

private def childAccepting (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.accepting.image (childState index)

def childSkipping (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.skipping.image (childState index)

def childCompleting (index : Nat) (automaton : AutomatonFragment) :
    Finset TypeAutomatonState :=
  automaton.completing.image (childState index)

def childFutureSpec (index : Nat) : FutureSpec → FutureSpec
  | .explicit offers => .explicit offers
  | .at state removed => .at (childState index state) removed

def childPendingEdge (index : Nat)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState index edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := childFutureSpec index edge.future
    target := childState index edge.target }

def childPendingEdges (index : Nat) (automaton : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  automaton.edges.image (childPendingEdge index)

/-- Whenever a constructor's outgoing edges at a tagged child state are exactly
the tagged images of the child's own outgoing edges, marker sources agree.
Tagging preserves an edge's label, so no marker is created or destroyed. -/
theorem markerSource_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat) (name : String)
    (state : TypeAutomatonState)
    (hOutgoing : ∀ edge : PendingAutomatonEdge,
      (edge ∈ parent.edges ∧ edge.source = childState index state) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧ edge = childPendingEdge index childEdge) :
    MarkerSource parent name (childState index state) ↔
      MarkerSource child name state := by
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ :=
      (hOutgoing edge).mp ⟨hEdge, hSource⟩
    exact ⟨childEdge, hChildEdge, hChildSource,
      by simpa [childPendingEdge] using hLabel⟩
  · rintro ⟨childEdge, hChildEdge, hChildSource, hLabel⟩
    obtain ⟨hEdge, hSource⟩ :=
      (hOutgoing (childPendingEdge index childEdge)).mpr
        ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    exact ⟨childPendingEdge index childEdge, hEdge, hSource,
      by simpa [childPendingEdge] using hLabel⟩

/-- Same-cycle references at a tagged child state are the tagged images of the
child's own references, whenever the constructor's outgoing edges there are
exactly the tagged child edges.  `childPendingEdge` preserves the label — hence
the clock test — and retags only `.at` references. -/
theorem referencedStates_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat)
    (state : TypeAutomatonState)
    (hOutgoing : ∀ edge : PendingAutomatonEdge,
      (edge ∈ parent.edges ∧ edge.source = childState index state) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = state ∧ edge = childPendingEdge index childEdge) :
    (⟨parent.states, parent.edges⟩ : PendingAutomaton).referencedStates
        (childState index state) =
      ((⟨child.states, child.edges⟩ : PendingAutomaton).referencedStates
        state).image (childState index) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    obtain ⟨childEdge, hChildEdge, hChildSource, rfl⟩ :=
      (hOutgoing edge).mp ⟨hEdge, hSource⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos (by simpa [childPendingEdge] using hTock)] at hTarget
      simp at hTarget
    · rw [if_neg (by simpa [childPendingEdge] using hTock)] at hTarget
      cases hSpec : childEdge.future with
      | explicit offers =>
          rw [show (childPendingEdge index childEdge).future = .explicit offers
            by simp [childPendingEdge, hSpec, childFutureSpec]] at hTarget
          simp at hTarget
      | «at» inner removed =>
          rw [show (childPendingEdge index childEdge).future =
            .at (childState index inner) removed by
              simp [childPendingEdge, hSpec, childFutureSpec]] at hTarget
          rw [Finset.mem_singleton] at hTarget
          subst hTarget
          exact ⟨inner, ⟨childEdge, ⟨hChildEdge, hChildSource⟩, by
            simp [if_neg hTock, hSpec]⟩, rfl⟩
  · rintro ⟨inner, ⟨childEdge, ⟨hChildEdge, hChildSource⟩, hInner⟩, rfl⟩
    by_cases hTock : childEdge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hInner
      simp at hInner
    · rw [if_neg hTock] at hInner
      cases hSpec : childEdge.future with
      | explicit offers =>
          rw [hSpec] at hInner
          simp at hInner
      | «at» dest removed =>
          rw [hSpec, Finset.mem_singleton] at hInner
          obtain ⟨hEdge, hSource⟩ :=
            (hOutgoing (childPendingEdge index childEdge)).mpr
              ⟨childEdge, hChildEdge, hChildSource, rfl⟩
          refine ⟨childPendingEdge index childEdge, ⟨hEdge, hSource⟩, ?_⟩
          rw [if_neg (by simpa [childPendingEdge] using hTock),
            show (childPendingEdge index childEdge).future =
              .at (childState index dest) removed by
                simp [childPendingEdge, hSpec, childFutureSpec]]
          simp [hInner]

/-- Marker reachability transports into a tagged child whose outgoing edges are
exactly the tagged child edges.  This packages the two facts above and is the
uniform tool for choice, sequence-right, and both offer constructors. -/
theorem markerReachable_of_outgoing_childPendingEdge
    (parent child : AutomatonFragment) (index : Nat) (name : String)
    (hOutgoing : ∀ (q : TypeAutomatonState) (edge : PendingAutomatonEdge),
      (edge ∈ parent.edges ∧ edge.source = childState index q) ↔
        ∃ childEdge ∈ child.edges,
          childEdge.source = q ∧ edge = childPendingEdge index childEdge)
    (hClosed : (⟨child.states, child.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hCard : child.states.card ≤ parent.states.card)
    (state : TypeAutomatonState) (hState : state ∈ child.states) :
    MarkerReachable parent name (childState index state) ↔
      MarkerReachable child name state :=
  markerReachable_of_embedding child parent name (childState index)
    (fun current => referencedStates_of_outgoing_childPendingEdge parent child
      index current (hOutgoing current))
    hClosed hCard
    (fun current _ => markerSource_of_outgoing_childPendingEdge parent child
      index name current (hOutgoing current))
    state hState

/-! ### Interface operations for parallel products -/

/-- Remove offers whose message identifier belongs to the internal interface. -/
def hideOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∉ interface

/-- Keep only offers whose message identifier belongs to the interface. -/
def interfaceOffers (interface : Interface)
    (offers : Finset BareMessage) : Finset BareMessage :=
  offers.filter fun offer => offer.1 ∈ interface

/-- Hide the interface from the union of two component environments. -/
def combineAutomatonEnvironment (interface : Interface)
    (left right : TypeEnvironment) : TypeEnvironment :=
  if left.clock && right.clock then TypeEnvironment.tock
  else
    { immediate := hideOffers interface (left.immediate ∪ right.immediate)
      future := hideOffers interface (left.future ∪ right.future)
      clock := false }

/-- A local-environment witness may choose a different target and offer
summary from the actual component transition, but it must start at the same
residual under the same environment and semantic label. -/
def matchesAutomatonOfferWitness
    (actual witness : AutomatonFragmentEdge) : Prop :=
  witness.source = actual.source ∧
    witness.environment = actual.environment ∧
    witness.label.semantic = actual.label.semantic

/-- Exact automaton counterpart of the two `LocalTypeEnvironment` premises.

The actual edges determine the product target and its exposed current/future
summary.  The two witness edges justify the sibling-local environments; this
mirrors the semantic rule's existential sibling target and offer summary.
Using the equations verbatim is important because the future equation removes
the local immediate set and therefore does not require current/future
disjointness. -/
def syncAutomatonEdgeWitnesses (interface : Interface)
    (left right leftWitness rightWitness : AutomatonFragmentEdge) : Prop :=
  let outer := combineAutomatonEnvironment interface
    left.environment right.environment
  matchesAutomatonOfferWitness left leftWitness ∧
    matchesAutomatonOfferWitness right rightWitness ∧
    (if left.environment.clock then
      left.environment = TypeEnvironment.tock ∧
        right.environment = TypeEnvironment.tock
    else
      left.environment.clock = false ∧
        right.environment.clock = false ∧
        left.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface rightWitness.current ∧
        left.environment.future =
          (outer.future ∪ restrictTypeOffers interface rightWitness.future) \
            left.environment.immediate ∧
        right.environment.immediate =
          outer.immediate ∪ restrictTypeOffers interface leftWitness.current ∧
        right.environment.future =
          (outer.future ∪ restrictTypeOffers interface leftWitness.future) \
            right.environment.immediate) ∧
    TypeLabel.Sync interface left.label.semantic right.label.semantic

/-- Component edges synchronize when suitable local-environment offer
witnesses occur in their respective resolved edge relations. -/
def syncAutomatonEdges (interface : Interface)
    (leftEdges rightEdges : Finset AutomatonFragmentEdge)
    (left right : AutomatonFragmentEdge) : Prop :=
  ∃ leftWitness ∈ leftEdges, ∃ rightWitness ∈ rightEdges,
    syncAutomatonEdgeWitnesses interface left right leftWitness rightWitness

/-- Regression: interface synchronization alone cannot pair edges that see
different boundary environments. -/
theorem syncAutomatonEdges_rejects_boundary_environment_mismatch :
    let action : BareMessage := ("b", .send)
    let left : AutomatonFragmentEdge :=
      { source := .root
        environment :=
          { immediate := {typeNeed action}, future := ∅, clock := false }
        label := .visible (TypeLabel.message action.1 action.2)
        current := {action}
        future := ∅
        target := .final }
    let right : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := ∅
        future := ∅
        target := .root }
    ¬ syncAutomatonEdges ∅ {left} {right} left right := by
  classical
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, typeNeed]

/-- Regression for the existential local-environment reading: the actual left
edge may select the `a` branch while a distinct silent edge from the same
source/environment witnesses the `b` offer used to construct the right local
environment. -/
theorem syncAutomatonEdges_accepts_independent_offer_witness :
    let aSend : BareMessage := ("a", .send)
    let aRecv : BareMessage := ("a", .recv)
    let bSend : BareMessage := ("b", .send)
    let interface : Interface := {"a"}
    let leftEnvironment : TypeEnvironment :=
      { immediate := {aRecv}, future := ∅, clock := false }
    let leftActual : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {aSend}
        target := .child 0 .root }
    let leftWitness : AutomatonFragmentEdge :=
      { source := .root
        environment := leftEnvironment
        label := .visible TypeLabel.silent
        current := ∅
        future := {bSend}
        target := .child 1 .root }
    let rightActual : AutomatonFragmentEdge :=
      { source := .root
        environment := TypeEnvironment.empty
        label := .visible TypeLabel.silent
        current := {aRecv}
        future := ∅
        target := .root }
    syncAutomatonEdges interface {leftActual, leftWitness} {rightActual}
      leftActual rightActual := by
  simp [syncAutomatonEdges, syncAutomatonEdgeWitnesses,
    matchesAutomatonOfferWitness, combineAutomatonEnvironment, hideOffers,
    restrictTypeOffers, TypeEnvironment.empty, TypeLabel.Sync,
    TypeLabel.silent, AutomatonConstructionLabel.semantic, TypeLabel.sends,
    TypeLabel.recvs, TypeLabel.messageIdsWith]
  native_decide

/-! ### Reusable constructor combinators -/

/-- One step of backward closure for completion: add every state with a
non-clock outgoing edge into an already-completing state.  Message, progress,
and administrative edges may all occur before the next clock, so completion
at their target transports backward to their source. -/
private def completingBackStep (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
  reached ∪
    (body.edges.filter fun edge =>
      edge.label.semantic ≠ TypeLabel.tock ∧ edge.target ∈ reached).image
      fun edge => edge.source

private def completingBackClosureAux (body : AutomatonFragment) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      completingBackClosureAux body fuel (completingBackStep body reached)

/-- Saturate backward closure for `|E|` rounds.  Every state a round can add
is the source of some edge, so after `body.edges.card` rounds no new source
remains available and the operator has reached its fixed point.  Using the
edge count rather than the state count makes saturation provable with no
well-formedness side condition on the fragment. -/
def completingBackClosure (body : AutomatonFragment)
    (seed : Finset TypeAutomatonState) : Finset TypeAutomatonState :=
  completingBackClosureAux body body.edges.card seed

/-! #### Hypothesis-free saturation

`completingBackStep` is extensive and monotone, and everything it can add
lies in `body.edges.image (·.source)`.  A strictly growing chain inside that
finite set therefore stabilizes within `body.edges.card` rounds. -/

private theorem completingBackStep_subset (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) :
    reached ⊆ completingBackStep body reached :=
  Finset.subset_union_left

private theorem completingBackStep_mono (body : AutomatonFragment)
    {left right : Finset TypeAutomatonState} (hSubset : left ⊆ right) :
    completingBackStep body left ⊆ completingBackStep body right := by
  classical
  intro state hState
  simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hState ⊢
  rcases hState with hState | ⟨edge, ⟨hEdge, hLabel, hTarget⟩, hSource⟩
  · exact Or.inl (hSubset hState)
  · exact Or.inr ⟨edge, ⟨hEdge, hLabel, hSubset hTarget⟩, hSource⟩

/-- Anything a round adds is the source of an edge of `body`. -/
private theorem completingBackStep_subset_union_sources
    (body : AutomatonFragment) (reached : Finset TypeAutomatonState) :
    completingBackStep body reached ⊆
      reached ∪ body.edges.image (fun edge => edge.source) := by
  classical
  intro state hState
  simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hState ⊢
  rcases hState with hState | ⟨edge, ⟨hEdge, _, _⟩, hSource⟩
  · exact Or.inl hState
  · exact Or.inr ⟨edge, hEdge, hSource⟩

/-- The recursion unrolls on the left; this is the matching right-hand step. -/
private theorem completingBackClosureAux_succ_right
    (body : AutomatonFragment) :
    ∀ fuel reached,
      completingBackClosureAux body (fuel + 1) reached =
        completingBackStep body
          (completingBackClosureAux body fuel reached) := by
  intro fuel
  induction fuel with
  | zero => intro reached; rfl
  | succ fuel ih =>
      intro reached
      show completingBackClosureAux body (fuel + 1)
          (completingBackStep body reached) = _
      rw [ih (completingBackStep body reached)]
      rfl

private theorem subset_completingBackClosureAux (body : AutomatonFragment) :
    ∀ fuel reached, reached ⊆ completingBackClosureAux body fuel reached := by
  intro fuel
  induction fuel with
  | zero => intro reached; exact Finset.Subset.refl _
  | succ fuel ih =>
      intro reached
      exact (completingBackStep_subset body reached).trans
        (ih (completingBackStep body reached))

/-- Once a round changes nothing, no later round changes anything either. -/
private theorem completingBackClosureAux_stable
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    ∀ extra fuel,
      completingBackStep body (completingBackClosureAux body fuel seed) =
          completingBackClosureAux body fuel seed →
        completingBackClosureAux body (fuel + extra) seed =
          completingBackClosureAux body fuel seed := by
  intro extra
  induction extra with
  | zero => intro fuel _; rfl
  | succ extra ih =>
      intro fuel hStable
      have hPrevious : completingBackClosureAux body (fuel + extra) seed =
          completingBackClosureAux body fuel seed := ih fuel hStable
      show completingBackClosureAux body (fuel + extra + 1) seed = _
      rw [completingBackClosureAux_succ_right, hPrevious, hStable]

/-- Either the chain has already stabilized, or it has consumed at least
`fuel` distinct edge sources. -/
private theorem completingBackClosureAux_stable_or_card
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    ∀ fuel,
      completingBackStep body (completingBackClosureAux body fuel seed) =
          completingBackClosureAux body fuel seed ∨
        fuel ≤ ((completingBackClosureAux body fuel seed) ∩
          body.edges.image (fun edge => edge.source)).card := by
  classical
  intro fuel
  induction fuel with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ fuel ih =>
      by_cases hStable :
          completingBackStep body
              (completingBackClosureAux body (fuel + 1) seed) =
            completingBackClosureAux body (fuel + 1) seed
      · exact Or.inl hStable
      · refine Or.inr ?_
        have hStep : completingBackClosureAux body (fuel + 1) seed =
            completingBackStep body
              (completingBackClosureAux body fuel seed) :=
          completingBackClosureAux_succ_right body fuel seed
        have hPreviousNotStable :
            completingBackStep body
                (completingBackClosureAux body fuel seed) ≠
              completingBackClosureAux body fuel seed := by
          intro hEq
          apply hStable
          rw [hStep, hEq, hEq]
        have hCard : fuel ≤ ((completingBackClosureAux body fuel seed) ∩
            body.edges.image (fun edge => edge.source)).card := by
          rcases ih with hEq | hCard
          · exact absurd hEq hPreviousNotStable
          · exact hCard
        have hGrow : (completingBackClosureAux body fuel seed) ∩
              body.edges.image (fun edge => edge.source) ⊂
            (completingBackClosureAux body (fuel + 1) seed) ∩
              body.edges.image (fun edge => edge.source) := by
          constructor
          · intro state hState
            simp only [Finset.mem_inter] at hState ⊢
            exact ⟨(hStep ▸ completingBackStep_subset body _) hState.1,
              hState.2⟩
          · intro hSubset
            apply hPreviousNotStable
            apply Finset.Subset.antisymm _ (completingBackStep_subset body _)
            intro state hState
            rcases Finset.mem_union.mp
              (completingBackStep_subset_union_sources body
                (completingBackClosureAux body fuel seed) hState) with
              hOld | hSource
            · exact hOld
            · have hInter : state ∈
                  (completingBackClosureAux body (fuel + 1) seed) ∩
                    body.edges.image (fun edge => edge.source) :=
                Finset.mem_inter.mpr ⟨hStep ▸ hState, hSource⟩
              exact (Finset.mem_inter.mp (hSubset hInter)).1
        have := Finset.card_lt_card hGrow
        omega

/-- The saturated closure really is a fixed point of one more round. -/
private theorem completingBackClosure_fixed (body : AutomatonFragment)
    (seed : Finset TypeAutomatonState) :
    completingBackStep body (completingBackClosure body seed) =
      completingBackClosure body seed := by
  classical
  set sources := body.edges.image (fun edge => edge.source) with hSources
  have hSourcesCard : sources.card ≤ body.edges.card :=
    Finset.card_image_le
  have hAtSources :
      completingBackStep body
          (completingBackClosureAux body sources.card seed) =
        completingBackClosureAux body sources.card seed := by
    rcases completingBackClosureAux_stable_or_card body seed sources.card with
      hStable | hCard
    · exact hStable
    · have hFull : (completingBackClosureAux body sources.card seed) ∩
          sources = sources := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
        exact hCard
      have hContained : sources ⊆
          completingBackClosureAux body sources.card seed := by
        intro state hState
        have := hFull ▸ hState
        exact (Finset.mem_inter.mp this).1
      apply Finset.Subset.antisymm _ (completingBackStep_subset body _)
      intro state hState
      rcases Finset.mem_union.mp
        (completingBackStep_subset_union_sources body _ hState) with
        hOld | hSource
      · exact hOld
      · exact hContained hSource
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hSourcesCard
  unfold completingBackClosure
  rw [hExtra, completingBackClosureAux_stable body seed extra sources.card
    hAtSources, hAtSources]

/-! ### Backward-closure characterization

`completingBackClosure` is definitionally a forward `futureReachable`
saturation on the *reversed* non-clock graph: reverse every edge other than a
`tock` edge of `body`, encoding its (reversed) target as a `FutureSpec.at`
reference, and reuse the whole `PendingAutomaton.futureReachable` proof library
instead of redeveloping the fixed-point argument. -/

/-- One non-clock edge of `body`, reversed and repackaged as a `FutureSpec.at`
reference from its target back to its source. -/
private def nonClockBackEdge
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := edge.target
    environment := TypeEnvironment.empty
    label := .visible TypeLabel.silent
    current := ∅
    future := .at edge.source ∅
    target := edge.target }

private def nonClockBackEdges (body : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (body.edges.filter fun edge => edge.label.semantic != TypeLabel.tock).image
    nonClockBackEdge

/-- The pending automaton whose forward same-cycle reference closure from a
state computes exactly the states that reach it backward through non-clock
edges of `body`. -/
private def nonClockBackPending (body : AutomatonFragment) : PendingAutomaton :=
  { states := body.states, edges := nonClockBackEdges body }

private theorem nonClockBackPending_referencedStates
    (body : AutomatonFragment) (state : TypeAutomatonState) :
    (nonClockBackPending body).referencedStates state =
      (body.edges.filter fun edge =>
        edge.label.semantic ≠ TypeLabel.tock ∧ edge.target = state).image
        fun edge => edge.source := by
  classical
  ext source
  constructor
  · intro hMember
    simp only [PendingAutomaton.referencedStates, nonClockBackPending,
      Finset.mem_biUnion, Finset.mem_filter] at hMember
    obtain ⟨backEdge, ⟨hBackEdge, hSource⟩, hReference⟩ := hMember
    simp only [nonClockBackEdges, Finset.mem_image, Finset.mem_filter,
      bne_iff_ne] at hBackEdge
    obtain ⟨edge, ⟨hEdge, hLabel⟩, hBackEdgeEq⟩ := hBackEdge
    have hSourceEq : edge.target = state := by
      rw [← hBackEdgeEq] at hSource
      simpa [nonClockBackEdge] using hSource
    have hReferenceEq : source = edge.source := by
      rw [← hBackEdgeEq] at hReference
      simpa [nonClockBackEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent] using hReference
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨edge, ⟨hEdge, hLabel, hSourceEq⟩, hReferenceEq.symm⟩
  · intro hMember
    simp only [Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨edge, ⟨hEdge, hLabel, hTarget⟩, hSourceEq⟩ := hMember
    have hFilterMem : edge ∈ body.edges.filter fun edge =>
        edge.label.semantic != TypeLabel.tock := by
      simp [hEdge, hLabel]
    simp only [PendingAutomaton.referencedStates, nonClockBackPending,
      Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨nonClockBackEdge edge, ⟨?_, ?_⟩, ?_⟩
    · simp only [nonClockBackEdges, Finset.mem_image]
      exact ⟨edge, hFilterMem, rfl⟩
    · simp [nonClockBackEdge, hTarget]
    · simp [nonClockBackEdge, AutomatonConstructionLabel.semantic,
        TypeLabel.silent, hSourceEq]

private theorem completingBackStep_eq_futureStep (body : AutomatonFragment)
    (reached : Finset TypeAutomatonState) :
    completingBackStep body reached =
      (nonClockBackPending body).futureStep reached := by
  classical
  simp only [completingBackStep, PendingAutomaton.futureStep]
  congr 1
  ext source
  simp only [Finset.mem_biUnion, nonClockBackPending_referencedStates,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨edge, ⟨hEdge, hLabel, hTargetReached⟩, rfl⟩
    exact ⟨edge.target, hTargetReached, edge, ⟨hEdge, hLabel, rfl⟩, rfl⟩
  · rintro ⟨target, hTargetReached, edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
    exact ⟨edge, ⟨hEdge, hLabel, hTarget ▸ hTargetReached⟩, rfl⟩

private theorem completingBackClosureAux_eq_futureReachableAux
    (body : AutomatonFragment) :
    ∀ fuel reached,
      completingBackClosureAux body fuel reached =
        (nonClockBackPending body).futureReachableAux fuel reached := by
  intro fuel
  induction fuel with
  | zero => intro reached; rfl
  | succ fuel ih =>
      intro reached
      simp only [completingBackClosureAux, PendingAutomaton.futureReachableAux]
      rw [completingBackStep_eq_futureStep]
      exact ih _

/-- `completingBackClosure` is exactly forward `futureReachable` saturation on
the reversed silent-edge graph, started from `seed` instead of a singleton.
This transports the entire proved `futureReachable` fixed-point theory
(closure, monotonicity, unfolding) to backward completion closure. -/
private theorem completingBackClosure_eq_futureReachableAux
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    completingBackClosure body seed =
      (nonClockBackPending body).futureReachableAux body.edges.card seed := by
  simp only [completingBackClosure]
  exact completingBackClosureAux_eq_futureReachableAux body body.edges.card
    seed

/-- Two saturated iterates from the same seed agree: whichever stabilizes
first is propagated to the other by `completingBackClosureAux_stable`. -/
private theorem completingBackClosureAux_eq_of_fixed
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState)
    {left right : Nat}
    (hLeft : completingBackStep body (completingBackClosureAux body left seed) =
      completingBackClosureAux body left seed)
    (hRight : completingBackStep body
        (completingBackClosureAux body right seed) =
      completingBackClosureAux body right seed) :
    completingBackClosureAux body left seed =
      completingBackClosureAux body right seed := by
  rcases Nat.le_total left right with hLe | hLe
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    exact (completingBackClosureAux_stable body seed extra left hLeft).symm
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
    exact completingBackClosureAux_stable body seed extra right hRight

/-- The reversed non-clock graph is reference-closed whenever `body`'s
states already contain every edge endpoint (ordinary edge endpoints, not
symbolic future references, so no `FutureTargetsInStates` premise is needed
here). -/
private theorem nonClockBackPending_referencesClosed
    (body : AutomatonFragment)
    (hSources : ∀ edge ∈ body.edges, edge.source ∈ body.states) :
    (nonClockBackPending body).ReferencesClosed := by
  intro state _ target hTarget
  rw [nonClockBackPending_referencedStates] at hTarget
  simp only [Finset.mem_image, Finset.mem_filter] at hTarget
  rcases hTarget with ⟨edge, ⟨hEdge, _, _⟩, rfl⟩
  simpa [nonClockBackPending] using hSources edge hEdge

/-- Backward completion closure unfolds by one symbolic non-clock predecessor
step: a state is in the closure of `seed` exactly when it already belongs to
`seed`, or it has an outgoing silent edge into a state whose own backward
closure already contains `seed`-reachable material.  In practice this is used
through the two directional corollaries below. -/
theorem completingBackClosure_superset_seed
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    seed ⊆ completingBackClosure body seed :=
  subset_completingBackClosureAux body body.edges.card seed

/-- If `source` has a non-clock edge into some state already in the closure of
`seed`, then `source` itself is in the closure of `seed`.  This is the
predecessor-step direction used to place the recursion root/backedge sources
into the closure.  It needs no well-formedness side condition: the closure is
a fixed point of `completingBackStep` by `completingBackClosure_fixed`. -/
theorem completingBackClosure_mem_of_nonClockEdge
    (body : AutomatonFragment) (seed : Finset TypeAutomatonState)
    (edge : PendingAutomatonEdge) (hEdge : edge ∈ body.edges)
    (hLabel : edge.label.semantic ≠ TypeLabel.tock)
    (hTarget : edge.target ∈ completingBackClosure body seed) :
    edge.source ∈ completingBackClosure body seed := by
  classical
  have hStepMem : edge.source ∈
      completingBackStep body (completingBackClosure body seed) := by
    simp only [completingBackStep, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter]
    exact Or.inr ⟨edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
  rwa [completingBackClosure_fixed body seed] at hStepMem

/-- Backward completion closure is contained in any predecessor-closed set
containing `seed`: if a set contains `seed` and is closed under taking
non-clock
predecessors, the whole closure lands inside it.  This is the direction used
to bound the closure from above by a syntactic completion characterization. -/
theorem completingBackClosure_subset_of_predecessor_closed
    (body : AutomatonFragment) (seed allowed : Finset TypeAutomatonState)
    (hSeed : seed ⊆ allowed)
    (hAllowed : ∀ edge ∈ body.edges,
      edge.label.semantic ≠ TypeLabel.tock → edge.target ∈ allowed →
        edge.source ∈ allowed) :
    completingBackClosure body seed ⊆ allowed := by
  rw [completingBackClosure_eq_futureReachableAux]
  have hAux : ∀ fuel reached, reached ⊆ allowed →
      (nonClockBackPending body).futureReachableAux fuel reached ⊆ allowed := by
    intro fuel
    induction fuel with
    | zero => intro reached hReached; exact hReached
    | succ fuel ih =>
        intro reached hReached
        simp only [PendingAutomaton.futureReachableAux]
        apply ih
        intro state hState
        simp only [PendingAutomaton.futureStep, Finset.mem_union,
          Finset.mem_biUnion] at hState
        rcases hState with hState | ⟨source, hSource, hReference⟩
        · exact hReached hState
        · rw [nonClockBackPending_referencedStates] at hReference
          simp only [Finset.mem_image, Finset.mem_filter] at hReference
          rcases hReference with ⟨edge, ⟨hEdge, hLabel, hTarget⟩, rfl⟩
          apply hAllowed edge hEdge hLabel
          rw [hTarget]
          exact hReached hSource
  exact hAux body.edges.card seed hSeed

/-- Backward completion closure is monotone in the seed. -/
theorem completingBackClosure_mono
    (body : AutomatonFragment)
    {seed1 seed2 : Finset TypeAutomatonState} (hSubset : seed1 ⊆ seed2) :
    completingBackClosure body seed1 ⊆ completingBackClosure body seed2 := by
  apply completingBackClosure_subset_of_predecessor_closed
  · exact hSubset.trans (completingBackClosure_superset_seed body seed2)
  · intro edge hEdge hLabel hTarget
    exact completingBackClosure_mem_of_nonClockEdge body seed2
      edge hEdge hLabel hTarget

/-- Inserting a state with no incoming non-clock edges into the seed only adds
that state itself to the closure: it can never unlock a new predecessor,
since no edge targets it. -/
private theorem completingBackClosure_union_isolated_target
    (body : AutomatonFragment) (isolated : TypeAutomatonState)
    (seed : Finset TypeAutomatonState)
    (hNoIncoming : ∀ edge ∈ body.edges, edge.target ≠ isolated) :
    completingBackClosure body ({isolated} ∪ seed) =
      {isolated} ∪ completingBackClosure body seed := by
  apply Finset.Subset.antisymm
  · apply completingBackClosure_subset_of_predecessor_closed
    · exact Finset.union_subset_union (Finset.Subset.refl _)
        (completingBackClosure_superset_seed body seed)
    · intro edge hEdge hLabel hTarget
      simp only [Finset.mem_union, Finset.mem_singleton] at hTarget ⊢
      rcases hTarget with hTarget | hTarget
      · exact absurd hTarget (hNoIncoming edge hEdge)
      · exact Or.inr (completingBackClosure_mem_of_nonClockEdge body seed
          edge hEdge hLabel hTarget)
  · apply Finset.union_subset
    · exact (Finset.subset_union_left).trans
        (completingBackClosure_superset_seed body ({isolated} ∪ seed))
    · exact completingBackClosure_mono body Finset.subset_union_right

/-- A carrier whose states and edges are `body`'s own states/edges, each
tagged by `childState index`, but whose completing/skipping/accepting/initial
bookkeeping is irrelevant to backward closure and is therefore left blank.
This is definitionally the state/edge shape shared by `buildRecursionAutomaton`'s
`taggedCarrier` (at `index = 0`) and by any other constructor that lifts a
child fragment's edges with `childPendingEdge`. -/
def taggedFragment (index : Nat) (body : AutomatonFragment) :
    AutomatonFragment :=
  { states := childStates index body
    initial := childState index body.initial
    accepting := ∅
    skipping := ∅
    completing := ∅
    edges := body.edges.image fun edge =>
      { source := childState index edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := edge.future
        target := childState index edge.target } }

/-- The reversed non-clock predecessor function commutes exactly with
`childState index`-tagging: predecessors of a tagged state in the tagged
carrier are exactly the tagged predecessors of the untagged state in `body`.
-/
private theorem nonClockBackPending_taggedFragment_referencedStates
    (index : Nat) (body : AutomatonFragment) (state : TypeAutomatonState) :
    (nonClockBackPending (taggedFragment index body)).referencedStates
        (childState index state) =
      ((nonClockBackPending body).referencedStates state).image
        (childState index) := by
  classical
  rw [nonClockBackPending_referencedStates,
    nonClockBackPending_referencedStates]
  ext source
  constructor
  · intro hMember
    simp only [taggedFragment, Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨edge, ⟨⟨original, hOriginal, hEdgeEq⟩, hLabel, hTarget⟩, hSourceEq⟩ :=
      hMember
    subst hEdgeEq
    simp only at hLabel hTarget
    have hTargetEq : original.target = state := by injection hTarget
    simp only [Finset.mem_image, Finset.mem_filter]
    exact ⟨original.source, ⟨original, ⟨hOriginal, hLabel, hTargetEq⟩, rfl⟩,
      hSourceEq⟩
  · intro hMember
    simp only [Finset.mem_image, Finset.mem_filter] at hMember
    obtain ⟨candidate, ⟨original, ⟨hOriginal, hLabel, hTarget⟩, hSourceEq⟩, hEq⟩ :=
      hMember
    simp only [taggedFragment, Finset.mem_image, Finset.mem_filter]
    refine ⟨_, ⟨⟨original, hOriginal, rfl⟩, ?_, ?_⟩, ?_⟩
    · simpa using hLabel
    · simp [childState, hTarget]
    · simp only [childState, hSourceEq]; exact hEq

/-- Backward completion closure commutes with `childState`-tagging: computing
the closure in the tagged carrier and reading off tagged states is the same
as computing the closure directly in `body` and tagging the result.  This is
the single reusable embedding underlying every constructor's use of backward
completion closure over a tagged child. -/
theorem completingBackClosure_taggedFragment_image
    (index : Nat) (body : AutomatonFragment) (seed : Finset TypeAutomatonState) :
    completingBackClosure (taggedFragment index body) (seed.image (childState index)) =
      (completingBackClosure body seed).image (childState index) := by
  classical
  rw [completingBackClosure_eq_futureReachableAux,
    completingBackClosure_eq_futureReachableAux]
  have hEdgesCard : (taggedFragment index body).edges.card = body.edges.card := by
    simp only [taggedFragment]
    apply Finset.card_image_of_injective
    intro a b hEq
    simp only [PendingAutomatonEdge.mk.injEq, childState,
      TypeAutomatonState.child.injEq] at hEq
    cases a
    cases b
    simp_all
  rw [hEdgesCard]
  exact PendingAutomaton.futureReachableAux_image_of_embedding
    (nonClockBackPending body)
      (nonClockBackPending (taggedFragment index body))
    (childState index)
    (fun state =>
      nonClockBackPending_taggedFragment_referencedStates index body state)
    body.edges.card seed

/-- `completingBackStep`, hence the whole closure, depends only on the
`(source, label, target)` projection of each edge.  Two fragments whose edges
agree on that projection (in particular differing only in unused `future`
bookkeeping) and whose declared state sets both bound the true edge/seed
footprint compute the same backward completion closure regardless of their
raw `states.card` fuel bound.  This lets `buildRecursionAutomaton`'s literal
`taggedCarrier` be identified with the canonical `taggedFragment` used by the
embedding lemma above. -/
private theorem completingBackClosure_eq_of_edges_agree
    (first second : AutomatonFragment)
    (hAgree : ∀ source label target,
        (∃ edge ∈ first.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target) ↔
        (∃ edge ∈ second.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target))
    (seed : Finset TypeAutomatonState) :
    completingBackClosure first seed = completingBackClosure second seed := by
  classical
  have hStep : ∀ reached, completingBackStep first reached =
      completingBackStep second reached := by
    intro reached
    simp only [completingBackStep]
    congr 1
    ext source
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨edge, ⟨hEdge, hLabel, hReached⟩, rfl⟩
      obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
        (hAgree edge.source edge.label edge.target).mp ⟨edge, hEdge, rfl, rfl, rfl⟩
      exact ⟨edge', ⟨hEdge', hLabelEq ▸ hLabel, hTargetEq ▸ hReached⟩, hSourceEq⟩
    · rintro ⟨edge, ⟨hEdge, hLabel, hReached⟩, rfl⟩
      obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
        (hAgree edge.source edge.label edge.target).mpr ⟨edge, hEdge, rfl, rfl, rfl⟩
      exact ⟨edge', ⟨hEdge', hLabelEq ▸ hLabel, hTargetEq ▸ hReached⟩, hSourceEq⟩
  have hAux : ∀ fuel reached, completingBackClosureAux first fuel reached =
      completingBackClosureAux second fuel reached := by
    intro fuel
    induction fuel with
    | zero => intro reached; rfl
    | succ fuel ih =>
        intro reached
        simp only [completingBackClosureAux, hStep]
        exact ih _
  -- Both fragments saturate; transport `second`'s fixed point along the
  -- shared step function, then match the two saturated iterates.
  have hFirstFixed : completingBackStep first
      (completingBackClosureAux first first.edges.card seed) =
      completingBackClosureAux first first.edges.card seed :=
    completingBackClosure_fixed first seed
  have hSecondFixed : completingBackStep first
      (completingBackClosureAux first second.edges.card seed) =
      completingBackClosureAux first second.edges.card seed := by
    rw [hAux second.edges.card seed, hStep]
    exact completingBackClosure_fixed second seed
  calc completingBackClosure first seed
      = completingBackClosureAux first second.edges.card seed :=
        completingBackClosureAux_eq_of_fixed first seed hFirstFixed hSecondFixed
    _ = completingBackClosureAux second second.edges.card seed :=
        hAux second.edges.card seed
    _ = completingBackClosure second seed := rfl

/-- Backward completion closure is monotone under edge-set growth: enlarging
the carrier's edges (any edge realized in `first`, as a `(source, label,
target)` triple, also realized in `second`) can only enlarge the closure.
Unlike `completingBackClosure_eq_of_edges_agree` this is one-directional and
needs no card/fuel matching argument at all -- it is a direct
predecessor-closure argument: `completingBackClosure second seed` is itself
predecessor-closed under `second`'s (hence, via `hSubset`, under `first`'s)
edges and contains `seed`, so it already bounds `first`'s closure from above. -/
theorem completingBackClosure_mono_edges
    (first second : AutomatonFragment)
    (hSubset : ∀ source label target,
        (∃ edge ∈ first.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target) →
        (∃ edge ∈ second.edges,
          edge.source = source ∧ edge.label = label ∧ edge.target = target))
    (seed : Finset TypeAutomatonState) :
    completingBackClosure first seed ⊆ completingBackClosure second seed := by
  apply completingBackClosure_subset_of_predecessor_closed
  · exact completingBackClosure_superset_seed second seed
  · intro edge hEdge hLabel hTarget
    obtain ⟨edge', hEdge', hSourceEq, hLabelEq, hTargetEq⟩ :=
      hSubset edge.source edge.label edge.target ⟨edge, hEdge, rfl, rfl, rfl⟩
    have hLabel' : edge'.label.semantic ≠ TypeLabel.tock := by
      rw [hLabelEq]; exact hLabel
    have hTarget' : edge'.target ∈ completingBackClosure second seed := by
      rw [hTargetEq]; exact hTarget
    have hResult := completingBackClosure_mem_of_nonClockEdge second seed edge'
      hEdge' hLabel' hTarget'
    rwa [hSourceEq] at hResult

/--
Build a recursion binder with an explicit silent header step.

The fresh root represents the binder itself. Matching variable edges inside
the tagged body are replaced by silent back-edges to the body entry, which is
the graph representation of substituting the binder at those occurrences.
-/
def buildRecursionAutomaton (signature : TypeAlphabet) (name : String)
    (body : AutomatonFragment) : AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 body
  let accepting := childAccepting 0 body
  let skipping := childSkipping 0 body
  let recursiveCallSources :=
    (body.edges.filter fun edge => edge.label = .variable name).image
      fun edge => childState 0 edge.source
  let seedCompleting :=
    (if body.initial ∈ body.completing then
      {TypeAutomatonState.root} ∪ recursiveCallSources
    else ∅) ∪
      childCompleting 0 body
  -- Close backward through every non-clock edge of the tagged carrier, so
  -- completion installed at a recursive-call source propagates across
  -- messages, progress actions, and administrative steps—exactly the paths
  -- that may finish before the next `tock`. `root` has no incoming tagged
  -- edges, so it never gains extra predecessors from this closure.
  let taggedBodyEdges : Finset PendingAutomatonEdge :=
    body.edges.image fun edge =>
      { source := childState 0 edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := edge.future
        target := childState 0 edge.target }
  let taggedCarrier : AutomatonFragment :=
    { states := states
      initial := TypeAutomatonState.root
      accepting := accepting
      skipping := skipping
      completing := ∅
      edges := taggedBodyEdges }
  let completing := completingBackClosure taggedCarrier seedCompleting
  let headerEdges : Finset PendingAutomatonEdge :=
    signature.localEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
  let bodyEdges : Finset PendingAutomatonEdge := body.edges.image fun edge =>
    if edge.label = .variable name then
      { source := childState 0 edge.source
        environment := edge.environment
        label := AutomatonConstructionLabel.visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 body.initial) ∅
        target := childState 0 body.initial }
    else
      { source := childState 0 edge.source
        environment := edge.environment
        label := edge.label
        current := edge.current
        future := childFutureSpec 0 edge.future
        target := childState 0 edge.target }
  finishAutomatonFragment states .root accepting skipping completing
    (headerEdges ∪ bodyEdges)

/-- Installing backedges does not change the offers directly visible at a
tagged body state.  A matching marker contributes nothing before installation
(it is inert) and nothing after installation either, because the backedge it
becomes carries empty `current` and a symbolic `.at` future; every other body
edge keeps its `current`, and `childFutureSpec` preserves `.explicit`
payloads while sending `.at` to `.at`.  Header edges leave from `.root`, which
is never a tagged state. -/
theorem buildRecursionAutomaton_offersAt_child
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name) (q : TypeAutomatonState) :
    (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).offersAt (childState 0 q) =
      (⟨body.states, body.edges⟩ : PendingAutomaton).offersAt q := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter,
    buildRecursionAutomaton, finishAutomatonFragment, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    rcases hEdge with ⟨environment, _, rfl⟩ | ⟨original, hOriginal, rfl⟩
    · exact absurd hSource (by simp [childState])
    · by_cases hMarker :
          original.label = AutomatonConstructionLabel.variable name
      · exfalso
        rw [if_pos hMarker] at hAction
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hAction
      · rw [if_neg hMarker] at hSource hAction
        refine ⟨original, ⟨hOriginal, ?_⟩, ?_⟩
        · simpa [childState] using hSource
        · cases hSpec : original.future with
          | explicit offers => simpa [hSpec, childFutureSpec] using hAction
          | «at» target removed =>
              simpa [hSpec, childFutureSpec] using hAction
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hAction⟩
    by_cases hMarker : edge.label = AutomatonConstructionLabel.variable name
    · exfalso
      have hFields := hMarkers edge hEdge hMarker
      rw [hFields.1, hFields.2] at hAction
      simp at hAction
    · refine ⟨_, ⟨Or.inr ⟨edge, hEdge, rfl⟩, ?_⟩, ?_⟩
      · rw [if_neg hMarker]
        simp [childState, hSource]
      · rw [if_neg hMarker]
        cases hSpec : edge.future with
        | explicit offers => simpa [hSpec, childFutureSpec] using hAction
        | «at» target removed =>
            simpa [hSpec, childFutureSpec] using hAction

/-- Installing backedges changes the same-cycle reference structure at a
tagged body state in exactly one way: a marker source additionally references
the tagged body entry.  Every other reference is the tagged image of a body
reference.  This is the precise sense in which the installed graph is the
body's own graph plus the recursive back-reference. -/
theorem mem_buildRecursionAutomaton_referencedStates_child
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name) (q target : TypeAutomatonState) :
    target ∈ (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).referencedStates (childState 0 q) ↔
      (∃ inner ∈ (⟨body.states, body.edges⟩ :
          PendingAutomaton).referencedStates q,
        target = childState 0 inner) ∨
        (MarkerSource body name q ∧ target = childState 0 body.initial) := by
  classical
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    rcases hEdge with ⟨environment, _, rfl⟩ | ⟨original, hOriginal, rfl⟩
    · exact absurd hSource (by simp [childState])
    · by_cases hMarker :
          original.label = AutomatonConstructionLabel.variable name
      · right
        rw [if_pos hMarker] at hSource hTarget
        refine ⟨⟨original, hOriginal, ?_, hMarker⟩, ?_⟩
        · simpa [childState] using hSource
        · simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
            using hTarget
      · left
        rw [if_neg hMarker] at hSource hTarget
        have hSourceEq : original.source = q := by
          simpa [childState] using hSource
        by_cases hTock : original.label.semantic = TypeLabel.tock
        · exfalso
          simp only [hTock, if_pos rfl] at hTarget
          simp at hTarget
        · cases hSpec : original.future with
          | explicit offers =>
              exfalso
              simp only [hSpec, childFutureSpec, if_neg hTock] at hTarget
              simp at hTarget
          | «at» inner removed =>
              simp only [hSpec, childFutureSpec, if_neg hTock] at hTarget
              refine ⟨inner, ⟨original, ⟨hOriginal, hSourceEq⟩, ?_⟩, ?_⟩
              · simp [hSpec, if_neg hTock]
              · simpa using hTarget
  · rintro (⟨inner, ⟨original, ⟨hOriginal, hSourceEq⟩, hInner⟩, rfl⟩ |
      ⟨⟨original, hOriginal, hSourceEq, hMarker⟩, rfl⟩)
    · have hMarker : original.label ≠ AutomatonConstructionLabel.variable name := by
        intro hEq
        have hFields := hMarkers original hOriginal hEq
        rw [hFields.2] at hInner
        by_cases hTock : original.label.semantic = TypeLabel.tock
        · simp [hTock] at hInner
        · simp [if_neg hTock] at hInner
      by_cases hTock : original.label.semantic = TypeLabel.tock
      · exfalso; simp [hTock] at hInner
      · cases hSpec : original.future with
        | explicit offers =>
            exfalso
            simp only [hSpec, if_neg hTock] at hInner
            simp at hInner
        | «at» innerTarget removed =>
            simp only [hSpec, if_neg hTock] at hInner
            refine ⟨_, ⟨Or.inr ⟨original, hOriginal, rfl⟩, ?_⟩, ?_⟩
            · rw [if_neg hMarker]
              simp [childState, hSourceEq]
            · rw [if_neg hMarker]
              simp only [hSpec, childFutureSpec, if_neg hTock]
              exact Finset.mem_singleton.mpr
                (congrArg (childState 0) (by simpa using hInner))
    · refine ⟨_, ⟨Or.inr ⟨original, hOriginal, rfl⟩, ?_⟩, ?_⟩
      · rw [if_pos hMarker]
        simp [childState, hSourceEq]
      · rw [if_pos hMarker]
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]

/-- Tagged body reachability is always available in the installed graph:
whatever the body reaches from `state`, its tagged copy is reached from the
tagged `state`.  No marker hypothesis is needed, because installing backedges
only ever *adds* references. -/
theorem futureReachable_buildRecursionAutomaton_child_superset
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ body.states) :
    ((⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state).image (childState 0) ⊆
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).futureReachable (childState 0 state) := by
  classical
  set child : PendingAutomaton := ⟨body.states, body.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildRecursionAutomaton signature name body).states,
      (buildRecursionAutomaton signature name body).edges⟩ with hParent
  have hReachSubset : child.futureReachable state ⊆ body.states :=
    child.futureReachable_subset_of_reference_closed state body.states hState
      (fun current hCurrent => hBodyClosed current hCurrent)
  have hStepClosed : ∀ q ∈ child.futureReachable state,
      child.referencedStates q ⊆ child.futureReachable state := by
    intro q hq
    have hqStates : q ∈ child.states := hReachSubset hq
    exact (child.referencedStates_subset_futureReachable q hBodyClosed
      hqStates).trans
      (child.futureReachable_subset_of_mem hBodyClosed hState hq)
  have hTaggedState : childState 0 state ∈ parent.states := by
    simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, hState]
  intro tagged hTagged
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hTagged
  have hAllowed : child.futureReachable state ⊆
      (child.futureReachable state).filter
        fun candidate => childState 0 candidate ∈
          parent.futureReachable (childState 0 state) := by
    apply child.futureReachable_subset_of_reference_closed
    · exact Finset.mem_filter.mpr ⟨child.mem_futureReachable_self _,
        parent.mem_futureReachable_self _⟩
    · intro current hCurrent inner hInner
      have hFields := Finset.mem_filter.mp hCurrent
      have hInnerReach : inner ∈ child.futureReachable state :=
        hStepClosed current hFields.1 hInner
      refine Finset.mem_filter.mpr ⟨hInnerReach, ?_⟩
      have hRef : childState 0 inner ∈
          parent.referencedStates (childState 0 current) :=
        (mem_buildRecursionAutomaton_referencedStates_child signature name
          body hMarkers current (childState 0 inner)).mpr
          (Or.inl ⟨inner, hInner, rfl⟩)
      have hCurrentStates : childState 0 current ∈ parent.states := by
        have := hReachSubset hFields.1
        simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
          childStates, childState, this]
      exact (parent.futureReachable_subset_of_mem hParentClosed
        hTaggedState hFields.2)
        (parent.referencedStates_subset_futureReachable
          (childState 0 current) hParentClosed hCurrentStates hRef)
  exact (Finset.mem_filter.mp (hAllowed hq)).2

/-- When no recursive-call marker is reachable inside the body from `state`,
installing backedges adds nothing at all: same-cycle reachability in the
installed graph is exactly the tagged image of body reachability.  This is the
marker-free half of the recursion future bridge. -/
theorem futureReachable_buildRecursionAutomaton_child_of_no_marker
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ body.states)
    (hNoMarker : ∀ q ∈ (⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state,
      ¬ MarkerSource body name q) :
    (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).futureReachable (childState 0 state) =
      ((⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state).image (childState 0) := by
  classical
  set child : PendingAutomaton := ⟨body.states, body.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildRecursionAutomaton signature name body).states,
      (buildRecursionAutomaton signature name body).edges⟩ with hParent
  have hReachSubset : child.futureReachable state ⊆ body.states :=
    child.futureReachable_subset_of_reference_closed state body.states hState
      (fun current hCurrent => hBodyClosed current hCurrent)
  -- The body-reachable set is closed under body references.
  have hStepClosed : ∀ q ∈ child.futureReachable state,
      child.referencedStates q ⊆ child.futureReachable state := by
    intro q hq
    have hqStates : q ∈ child.states := hReachSubset hq
    exact (child.referencedStates_subset_futureReachable q hBodyClosed
      hqStates).trans
      (child.futureReachable_subset_of_mem hBodyClosed hState hq)
  have hTaggedState : childState 0 state ∈ parent.states := by
    simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, hState]
  apply Finset.Subset.antisymm
  · -- Nothing outside the tagged body-reachable set can be entered.
    apply parent.futureReachable_subset_of_reference_closed
    · exact Finset.mem_image.mpr ⟨state, child.mem_futureReachable_self _, rfl⟩
    · intro current hCurrent target hTarget
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hCurrent
      rcases (mem_buildRecursionAutomaton_referencedStates_child signature name
        body hMarkers q target).mp hTarget with
        ⟨inner, hInner, rfl⟩ | ⟨hMarkerSource, _⟩
      · exact Finset.mem_image.mpr ⟨inner, hStepClosed q hq hInner, rfl⟩
      · exact absurd hMarkerSource (hNoMarker q hq)
  · exact futureReachable_buildRecursionAutomaton_child_superset signature name
      body hMarkers hBodyClosed hParentClosed state hState

/-- Marker-free half of the recursion future bridge, at the level of menus:
if no recursive call is reachable inside the body, the installed graph
resolves exactly the body's own future menu. -/
theorem computeFuture_buildRecursionAutomaton_child_of_no_marker
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ body.states)
    (hNoMarker : ∀ q ∈ (⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state,
      ¬ MarkerSource body name q) :
    computeFuture
        (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
          PendingAutomaton)
        (childState 0 state) =
      computeFuture (⟨body.states, body.edges⟩ : PendingAutomaton) state := by
  classical
  unfold computeFuture
  rw [futureReachable_buildRecursionAutomaton_child_of_no_marker signature name
    body hMarkers hBodyClosed hParentClosed state hState hNoMarker,
    Finset.image_biUnion]
  exact Finset.biUnion_congr rfl (fun q _ =>
    buildRecursionAutomaton_offersAt_child signature name body hMarkers q)

/-- When a recursive-call marker *is* reachable inside the body, the installed
graph additionally reaches exactly what the tagged body entry reaches, and
nothing beyond it.  This is the marker-reachable half of the bridge. -/
theorem futureReachable_buildRecursionAutomaton_child_of_marker
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states)
    (state : TypeAutomatonState) (hState : state ∈ body.states)
    (hMarker : ∃ m ∈ (⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state,
      MarkerSource body name m) :
    (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).futureReachable (childState 0 state) =
      ((⟨body.states, body.edges⟩ :
          PendingAutomaton).futureReachable state).image (childState 0) ∪
        (⟨(buildRecursionAutomaton signature name body).states,
            (buildRecursionAutomaton signature name body).edges⟩ :
          PendingAutomaton).futureReachable (childState 0 body.initial) := by
  classical
  set child : PendingAutomaton := ⟨body.states, body.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildRecursionAutomaton signature name body).states,
      (buildRecursionAutomaton signature name body).edges⟩ with hParent
  have hReachSubset : child.futureReachable state ⊆ body.states :=
    child.futureReachable_subset_of_reference_closed state body.states hState
      (fun current hCurrent => hBodyClosed current hCurrent)
  have hStepClosed : ∀ q ∈ child.futureReachable state,
      child.referencedStates q ⊆ child.futureReachable state := by
    intro q hq
    have hqStates : q ∈ child.states := hReachSubset hq
    exact (child.referencedStates_subset_futureReachable q hBodyClosed
      hqStates).trans
      (child.futureReachable_subset_of_mem hBodyClosed hState hq)
  have hTaggedState : childState 0 state ∈ parent.states := by
    simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, hState]
  have hTaggedInitial : childState 0 body.initial ∈ parent.states := by
    simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, hBodyInitial]
  obtain ⟨m, hm, hmMarker⟩ := hMarker
  -- The marker source's tagged copy is reachable, and it references the entry.
  have hTaggedM : childState 0 m ∈ parent.futureReachable (childState 0 state) :=
    futureReachable_buildRecursionAutomaton_child_superset signature name body
      hMarkers hBodyClosed hParentClosed state hState
      (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hMStates : childState 0 m ∈ parent.states := by
    have := hReachSubset hm
    simp [hParent, buildRecursionAutomaton, finishAutomatonFragment,
      childStates, childState, this]
  have hInitialReach : childState 0 body.initial ∈
      parent.futureReachable (childState 0 state) := by
    have hRef : childState 0 body.initial ∈
        parent.referencedStates (childState 0 m) :=
      (mem_buildRecursionAutomaton_referencedStates_child signature name body
        hMarkers m (childState 0 body.initial)).mpr (Or.inr ⟨hmMarker, rfl⟩)
    exact (parent.futureReachable_subset_of_mem hParentClosed hTaggedState
      hTaggedM)
      (parent.referencedStates_subset_futureReachable (childState 0 m)
        hParentClosed hMStates hRef)
  apply Finset.Subset.antisymm
  · apply parent.futureReachable_subset_of_reference_closed
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨state, child.mem_futureReachable_self _, rfl⟩)
    · intro current hCurrent target hTarget
      rcases Finset.mem_union.mp hCurrent with hInT | hInZ
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hInT
        rcases (mem_buildRecursionAutomaton_referencedStates_child signature
          name body hMarkers q target).mp hTarget with
          ⟨inner, hInner, rfl⟩ | ⟨_, rfl⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨inner, hStepClosed q hq hInner, rfl⟩)
        · exact Finset.mem_union_right _ (parent.mem_futureReachable_self _)
      · have hCurrentStates : current ∈ parent.states :=
          (parent.futureReachable_subset_of_reference_closed
            (childState 0 body.initial) parent.states hTaggedInitial
            (fun c hc => hParentClosed c hc)) hInZ
        refine Finset.mem_union_right _ ?_
        exact (parent.futureReachable_subset_of_mem hParentClosed
          hTaggedInitial hInZ)
          (parent.referencedStates_subset_futureReachable current hParentClosed
            hCurrentStates hTarget)
  · intro candidate hCandidate
    rcases Finset.mem_union.mp hCandidate with hInT | hInZ
    · exact futureReachable_buildRecursionAutomaton_child_superset signature
        name body hMarkers hBodyClosed hParentClosed state hState hInT
    · exact (parent.futureReachable_subset_of_mem hParentClosed hTaggedState
        hInitialReach) hInZ

/-- Marker-reachable half at the level of menus: the installed graph resolves
the body's own menu together with whatever the tagged body entry resolves.
Together with `mem_computeFuture_markerAugmented` this is the recursion future
bridge; the entry's own menu is then pinned by guardedness. -/
theorem computeFuture_buildRecursionAutomaton_child_of_marker
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states)
    (state : TypeAutomatonState) (hState : state ∈ body.states)
    (hMarker : ∃ m ∈ (⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable state,
      MarkerSource body name m) :
    computeFuture
        (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
          PendingAutomaton)
        (childState 0 state) =
      computeFuture (⟨body.states, body.edges⟩ : PendingAutomaton) state ∪
        computeFuture
          (⟨(buildRecursionAutomaton signature name body).states,
            (buildRecursionAutomaton signature name body).edges⟩ :
            PendingAutomaton)
          (childState 0 body.initial) := by
  classical
  unfold computeFuture
  rw [futureReachable_buildRecursionAutomaton_child_of_marker signature name
    body hMarkers hBodyClosed hParentClosed hBodyInitial state hState hMarker]
  ext action
  simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨reached, (hInT | hInZ), hAction⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hInT
      refine Or.inl ⟨q, hq, ?_⟩
      rwa [buildRecursionAutomaton_offersAt_child signature name body hMarkers
        q] at hAction
    · exact Or.inr ⟨reached, hInZ, hAction⟩
  · rintro (⟨q, hq, hAction⟩ | ⟨reached, hInZ, hAction⟩)
    · refine ⟨childState 0 q, Or.inl (Finset.mem_image.mpr ⟨q, hq, rfl⟩), ?_⟩
      rwa [buildRecursionAutomaton_offersAt_child signature name body hMarkers q]
    · exact ⟨reached, Or.inr hInZ, hAction⟩

/-- **The recursion fixed point.**  At the tagged body entry the installed
backedge is not an escape: it points back to the entry, which is already
reachable.  So reachability from the entry collapses to the tagged image of
body reachability, with no extra material at all.

This is what pins the entry's menu.  The two decomposition lemmas above
degenerate here — at `body.initial` they only say `X = X` — so the fixed point
must be closed by this separate argument. -/
theorem futureReachable_buildRecursionAutomaton_child_at_initial
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states) :
    (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).futureReachable (childState 0 body.initial) =
      ((⟨body.states, body.edges⟩ :
        PendingAutomaton).futureReachable body.initial).image
          (childState 0) := by
  classical
  set child : PendingAutomaton := ⟨body.states, body.edges⟩ with hChild
  set parent : PendingAutomaton :=
    ⟨(buildRecursionAutomaton signature name body).states,
      (buildRecursionAutomaton signature name body).edges⟩ with hParent
  have hReachSubset : child.futureReachable body.initial ⊆ body.states :=
    child.futureReachable_subset_of_reference_closed body.initial body.states
      hBodyInitial (fun current hCurrent => hBodyClosed current hCurrent)
  have hStepClosed : ∀ q ∈ child.futureReachable body.initial,
      child.referencedStates q ⊆ child.futureReachable body.initial := by
    intro q hq
    have hqStates : q ∈ child.states := hReachSubset hq
    exact (child.referencedStates_subset_futureReachable q hBodyClosed
      hqStates).trans
      (child.futureReachable_subset_of_mem hBodyClosed hBodyInitial hq)
  apply Finset.Subset.antisymm
  · apply parent.futureReachable_subset_of_reference_closed
    · exact Finset.mem_image.mpr
        ⟨body.initial, child.mem_futureReachable_self _, rfl⟩
    · intro current hCurrent target hTarget
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hCurrent
      rcases (mem_buildRecursionAutomaton_referencedStates_child signature name
        body hMarkers q target).mp hTarget with
        ⟨inner, hInner, rfl⟩ | ⟨_, rfl⟩
      · exact Finset.mem_image.mpr ⟨inner, hStepClosed q hq hInner, rfl⟩
      · -- The backedge lands on the entry, which is reachable from itself.
        exact Finset.mem_image.mpr
          ⟨body.initial, child.mem_futureReachable_self _, rfl⟩
  · exact futureReachable_buildRecursionAutomaton_child_superset signature name
      body hMarkers hBodyClosed hParentClosed body.initial hBodyInitial

/-- Menu form of the fixed point: the tagged body entry resolves exactly the
body's own entry menu, however many recursive calls lead back to it. -/
theorem computeFuture_buildRecursionAutomaton_child_at_initial
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states) :
    computeFuture
        (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
          PendingAutomaton)
        (childState 0 body.initial) =
      computeFuture (⟨body.states, body.edges⟩ : PendingAutomaton)
        body.initial := by
  classical
  unfold computeFuture
  rw [futureReachable_buildRecursionAutomaton_child_at_initial signature name
    body hMarkers hBodyClosed hParentClosed hBodyInitial,
    Finset.image_biUnion]
  exact Finset.biUnion_congr rfl (fun q _ =>
    buildRecursionAutomaton_offersAt_child signature name body hMarkers q)

/-- Installing backedges for `name` leaves markers of any *other* still-open
binder untouched: only `.variable name` edges are rewritten, and the rewrite
produces a `.visible` silent edge, never another marker. -/
theorem buildRecursionAutomaton_markerSource_child
    (signature : TypeAlphabet) (name other : String) (body : AutomatonFragment)
    (hDistinct : other ≠ name) (q : TypeAutomatonState) :
    MarkerSource (buildRecursionAutomaton signature name body) other
        (childState 0 q) ↔
      MarkerSource body other q := by
  classical
  simp only [MarkerSource, buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    rcases hEdge with ⟨environment, _, rfl⟩ | ⟨original, hOriginal, rfl⟩
    · exact absurd hSource (by simp [childState])
    · by_cases hMarker :
          original.label = AutomatonConstructionLabel.variable name
      · rw [if_pos hMarker] at hLabel
        exact absurd hLabel (by simp)
      · rw [if_neg hMarker] at hSource hLabel
        exact ⟨original, hOriginal, by simpa [childState] using hSource, hLabel⟩
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    have hNotMarker :
        ¬ edge.label = AutomatonConstructionLabel.variable name := by
      rw [hLabel]
      simp [hDistinct]
    refine ⟨_, Or.inr ⟨edge, hEdge, rfl⟩, ?_, ?_⟩
    · rw [if_neg hNotMarker]
      simp [childState, hSource]
    · rw [if_neg hNotMarker]
      exact hLabel

/-- The fresh recursion header carries no marker of its own. -/
theorem not_buildRecursionAutomaton_markerSource_root
    (signature : TypeAlphabet) (name other : String)
    (body : AutomatonFragment) :
    ¬ MarkerSource (buildRecursionAutomaton signature name body) other
      TypeAutomatonState.root := by
  classical
  rintro ⟨edge, hEdge, hSource, hLabel⟩
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with ⟨environment, _, rfl⟩ | ⟨original, _, rfl⟩
  · exact absurd hLabel (by simp)
  · by_cases hMarker :
        original.label = AutomatonConstructionLabel.variable name
    · rw [if_pos hMarker] at hSource
      exact absurd hSource (by simp [childState])
    · rw [if_neg hMarker] at hSource
      exact absurd hSource (by simp [childState])

/-- The recursion header's only same-cycle reference is the tagged body
entry. -/
theorem buildRecursionAutomaton_referencedStates_root
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment) :
    (⟨(buildRecursionAutomaton signature name body).states,
        (buildRecursionAutomaton signature name body).edges⟩ :
      PendingAutomaton).referencedStates TypeAutomatonState.root =
      {childState 0 body.initial} := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_singleton, buildRecursionAutomaton,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨hEdge, hSource⟩, hTarget⟩
    rcases hEdge with ⟨environment, _, rfl⟩ | ⟨original, _, rfl⟩
    · simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent]
        using hTarget
    · by_cases hMarker :
          original.label = AutomatonConstructionLabel.variable name
      · rw [if_pos hMarker] at hSource
        exact absurd hSource (by simp [childState])
      · rw [if_neg hMarker] at hSource
        exact absurd hSource (by simp [childState])
  · intro hTarget
    refine ⟨{ source := TypeAutomatonState.root
              environment := TypeEnvironment.tock
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 0 body.initial) ∅
              target := childState 0 body.initial }, ⟨?_, rfl⟩, ?_⟩
    · exact Or.inl ⟨TypeEnvironment.tock, by simp [TypeAlphabet.localEnvironments],
        rfl⟩
    · simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent] using hTarget

/-- Marker reachability for a *different* still-open binder inside an installed
recursion.  Installation adds exactly one escape: a same-cycle reachable call
of `name` additionally exposes everything the tagged body entry reaches. -/
theorem buildRecursionAutomaton_markerReachable_child
    (signature : TypeAlphabet) (name other : String)
    (body : AutomatonFragment) (hDistinct : other ≠ name)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states)
    (state : TypeAutomatonState) (hState : state ∈ body.states) :
    MarkerReachable (buildRecursionAutomaton signature name body) other
        (childState 0 state) ↔
      (MarkerReachable body other state ∨
        (MarkerReachable body name state ∧
          MarkerReachable (buildRecursionAutomaton signature name body) other
            (childState 0 body.initial))) := by
  classical
  have hTagged : ∀ q, MarkerSource (buildRecursionAutomaton signature name body)
      other (childState 0 q) ↔ MarkerSource body other q :=
    fun q => buildRecursionAutomaton_markerSource_child signature name other
      body hDistinct q
  by_cases hMarker : MarkerReachable body name state
  · simp only [MarkerReachable]
    rw [futureReachable_buildRecursionAutomaton_child_of_marker signature name
      body hMarkers hBodyClosed hParentClosed hBodyInitial state hState hMarker]
    simp only [MarkerReachable, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨reached, hReached | hReached, hSource⟩
      · rcases hReached with ⟨q, hq, rfl⟩
        exact Or.inl ⟨q, hq, (hTagged q).mp hSource⟩
      · exact Or.inr ⟨hMarker, ⟨reached, hReached, hSource⟩⟩
    · rintro (⟨q, hq, hSource⟩ | ⟨_, reached, hReached, hSource⟩)
      · exact ⟨childState 0 q, Or.inl ⟨q, hq, rfl⟩, (hTagged q).mpr hSource⟩
      · exact ⟨reached, Or.inr hReached, hSource⟩
  · simp only [MarkerReachable]
    rw [futureReachable_buildRecursionAutomaton_child_of_no_marker signature
      name body hMarkers hBodyClosed hParentClosed state hState
        (by simpa [MarkerReachable] using hMarker)]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨reached, ⟨q, hq, rfl⟩, hSource⟩
      exact Or.inl ⟨q, hq, (hTagged q).mp hSource⟩
    · rintro (⟨q, hq, hSource⟩ | ⟨hAbsurd, _⟩)
      · exact ⟨childState 0 q, ⟨q, hq, rfl⟩, (hTagged q).mpr hSource⟩
      · exact absurd hAbsurd hMarker

/-- At the tagged body entry the installed backedge is not an escape: it points
back to the entry, which is already reachable.  Marker reachability there is
therefore exactly the body's own. -/
theorem buildRecursionAutomaton_markerReachable_child_at_initial
    (signature : TypeAlphabet) (name other : String)
    (body : AutomatonFragment) (hDistinct : other ≠ name)
    (hMarkers : MarkerEdgesInert body name)
    (hBodyClosed :
      (⟨body.states, body.edges⟩ : PendingAutomaton).ReferencesClosed)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed)
    (hBodyInitial : body.initial ∈ body.states) :
    MarkerReachable (buildRecursionAutomaton signature name body) other
        (childState 0 body.initial) ↔
      MarkerReachable body other body.initial := by
  classical
  simp only [MarkerReachable]
  rw [futureReachable_buildRecursionAutomaton_child_at_initial signature name
    body hMarkers hBodyClosed hParentClosed hBodyInitial]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨reached, ⟨q, hq, rfl⟩, hSource⟩
    exact ⟨q, hq, (buildRecursionAutomaton_markerSource_child signature name
      other body hDistinct q).mp hSource⟩
  · rintro ⟨q, hq, hSource⟩
    exact ⟨childState 0 q, ⟨q, hq, rfl⟩,
      (buildRecursionAutomaton_markerSource_child signature name other body
        hDistinct q).mpr hSource⟩

/-- Marker reachability from the recursion header is exactly marker
reachability from the tagged body entry. -/
theorem buildRecursionAutomaton_markerReachable_root
    (signature : TypeAlphabet) (name other : String)
    (body : AutomatonFragment)
    (hParentClosed :
      (⟨(buildRecursionAutomaton signature name body).states,
          (buildRecursionAutomaton signature name body).edges⟩ :
        PendingAutomaton).ReferencesClosed) :
    MarkerReachable (buildRecursionAutomaton signature name body) other
        TypeAutomatonState.root ↔
      MarkerReachable (buildRecursionAutomaton signature name body) other
        (childState 0 body.initial) := by
  classical
  have hRoot : TypeAutomatonState.root ∈
      (buildRecursionAutomaton signature name body).states := by
    simp [buildRecursionAutomaton, finishAutomatonFragment]
  have hReferences := buildRecursionAutomaton_referencedStates_root signature
    name body
  have hResult := markerReachable_root_of_entries
    (buildRecursionAutomaton signature name body) other TypeAutomatonState.root
      {childState 0 body.initial} hParentClosed hRoot
        (by rw [hReferences]; exact Finset.subset_insert _ _)
        (by rw [hReferences])
  rw [hResult]
  constructor
  · rintro (hMarker | ⟨entry, hEntry, hInner⟩)
    · exact absurd hMarker (not_buildRecursionAutomaton_markerSource_root
        signature name other body)
    · rw [Finset.mem_singleton] at hEntry
      exact hEntry ▸ hInner
  · intro hInner
    exact Or.inr ⟨childState 0 body.initial, Finset.mem_singleton_self _,
      hInner⟩

theorem buildRecursionAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.FutureTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    (buildRecursionAutomaton signature name body).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with hHeader | hBody
  · rcases hHeader with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
      childState, hBodyInitial]
  · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
    by_cases hVariable : bodyEdge.label = .variable name
    · simp only [hVariable, if_true] at hFuture
      cases hFuture
      simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
        childState, hBodyInitial]
    · simp only [hVariable, if_false] at hFuture
      cases hSpec : bodyEdge.future with
      | explicit offers =>
          simp [childFutureSpec, hSpec] at hFuture
      | «at» bodyTarget removed =>
          simp only [childFutureSpec, hSpec] at hFuture
          cases hFuture
          have hBodyTarget := hBodyTargets bodyEdge hBodyEdge
            bodyTarget removed hSpec
          simp [buildRecursionAutomaton, finishAutomatonFragment, childStates,
            childState, hBodyTarget]

/-- `buildRecursionAutomaton`'s completing set, unfolded to the reusable
`taggedFragment`/`completingBackClosure` embedding: a tagged body state
`childState 0 bodyState` is completing exactly when `bodyState` is in the
backward completion closure computed directly on `body`, seeded by whichever
of `body.completing` and (if `body`'s entry itself completes) the untagged
recursive-call sources apply.  The fresh `root` is completing exactly when it
was seeded, i.e. when `body.initial ∈ body.completing`. -/
theorem buildRecursionAutomaton_completing_eq
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment) :
    let untaggedSources :=
      (body.edges.filter fun edge => edge.label = .variable name).image
        fun edge => edge.source
    let untaggedSeed :=
      (if body.initial ∈ body.completing then untaggedSources else ∅) ∪
        body.completing
    (buildRecursionAutomaton signature name body).completing =
      (if body.initial ∈ body.completing then
        {TypeAutomatonState.root} else ∅) ∪
        (completingBackClosure body untaggedSeed).image (childState 0) := by
  classical
  intro untaggedSources untaggedSeed
  set taggedCarrierEdges : Finset PendingAutomatonEdge :=
    body.edges.image fun edge =>
      { source := childState 0 edge.source, environment := edge.environment,
        label := edge.label, current := edge.current, future := edge.future,
        target := childState 0 edge.target } with hTaggedCarrierEdgesDef
  have hGoal : (buildRecursionAutomaton signature name body).completing =
      completingBackClosure
        { states := {TypeAutomatonState.root} ∪ childStates 0 body
          initial := TypeAutomatonState.root, accepting := childAccepting 0 body
          skipping := childSkipping 0 body, completing := ∅
          edges := taggedCarrierEdges }
        ((if body.initial ∈ body.completing then
            {TypeAutomatonState.root} ∪
              (body.edges.filter fun edge => edge.label = .variable name).image
                fun edge => childState 0 edge.source
          else ∅) ∪ childCompleting 0 body) := by
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      hTaggedCarrierEdgesDef]
  rw [hGoal]
  have hSeedEq : ((if body.initial ∈ body.completing then
        {TypeAutomatonState.root} ∪
          (body.edges.filter fun edge => edge.label = .variable name).image
            fun edge => childState 0 edge.source
      else (∅ : Finset TypeAutomatonState)) ∪ childCompleting 0 body) =
      (if body.initial ∈ body.completing then
        ({TypeAutomatonState.root} : Finset TypeAutomatonState) else ∅) ∪
        untaggedSeed.image (childState 0) := by
    simp only [untaggedSeed, untaggedSources]
    split
    · rw [Finset.image_union, childCompleting, Finset.image_image]
      ext state
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
        Function.comp, or_assoc]
    · simp [childCompleting]
  rw [hSeedEq]
  have hEdgesAgree : ∀ source label target,
      (∃ edge ∈ taggedCarrierEdges,
        edge.source = source ∧ edge.label = label ∧ edge.target = target) ↔
      (∃ edge ∈ (taggedFragment 0 body).edges,
        edge.source = source ∧ edge.label = label ∧ edge.target = target) := by
    intro source label target
    simp only [hTaggedCarrierEdgesDef, taggedFragment, Finset.mem_image]
  have hRootNoIncoming : ∀ edge ∈ taggedCarrierEdges,
      edge.target ≠ TypeAutomatonState.root := by
    intro edge hEdge
    simp only [hTaggedCarrierEdgesDef, Finset.mem_image] at hEdge
    obtain ⟨original, _, rfl⟩ := hEdge
    simp [childState]
  have hEdgesEq : completingBackClosure
      { states := {TypeAutomatonState.root} ∪ childStates 0 body
        initial := TypeAutomatonState.root, accepting := childAccepting 0 body
        skipping := childSkipping 0 body, completing := ∅
        edges := taggedCarrierEdges }
      (untaggedSeed.image (childState 0)) =
      (completingBackClosure body untaggedSeed).image (childState 0) := by
    rw [completingBackClosure_eq_of_edges_agree _ _ hEdgesAgree _]
    exact completingBackClosure_taggedFragment_image 0 body untaggedSeed
  by_cases hInit : body.initial ∈ body.completing
  · simp only [hInit, if_true]
    rw [completingBackClosure_union_isolated_target _
        TypeAutomatonState.root (untaggedSeed.image (childState 0))
        hRootNoIncoming,
      hEdgesEq]
  · simp only [hInit, if_false, Finset.empty_union]
    exact hEdgesEq

/-- Upper bound on `buildRecursionAutomaton`'s installed completion metadata.

Backward completion closure travels along every edge whose *semantic* label is
not `TypeLabel.tock`.  Therefore a body state that (i) is not itself marked
completing by the body fragment, (ii) is not the source of a matching
recursive-call marker, and (iii) has no non-clock outgoing edge other than a
self-loop, is never marked completing by the binder, no matter what the rest of
the graph looks like.

This is the exact converse bound needed to audit the installed metadata against
the syntax predicate `PactType.CanCompleteBeforeTock` of the *substituted*
residual: any state whose substituted residual completes while satisfying
(i)-(iii) exhibits a mismatch. -/
theorem buildRecursionAutomaton_not_mem_completing_of_no_nonClock_escape
    (signature : TypeAlphabet) (name : String) (body : AutomatonFragment)
    (state : TypeAutomatonState)
    (hNotCompleting : state ∉ body.completing)
    (hNoVariable : ∀ edge ∈ body.edges, edge.source = state →
      edge.label ≠ AutomatonConstructionLabel.variable name)
    (hNoNonClockEscape : ∀ edge ∈ body.edges, edge.source = state →
      edge.label.semantic ≠ TypeLabel.tock → edge.target = state) :
    childState 0 state ∉
      (buildRecursionAutomaton signature name body).completing := by
  classical
  set taggedCarrierEdges : Finset PendingAutomatonEdge :=
    body.edges.image fun edge =>
      { source := childState 0 edge.source, environment := edge.environment,
        label := edge.label, current := edge.current, future := edge.future,
        target := childState 0 edge.target } with hTaggedCarrierEdgesDef
  set seedCompleting : Finset TypeAutomatonState :=
    (if body.initial ∈ body.completing then
        {TypeAutomatonState.root} ∪
          (body.edges.filter fun edge => edge.label = .variable name).image
            fun edge => childState 0 edge.source
      else ∅) ∪ childCompleting 0 body with hSeedCompletingDef
  have hGoal : (buildRecursionAutomaton signature name body).completing =
      completingBackClosure
        { states := {TypeAutomatonState.root} ∪ childStates 0 body
          initial := TypeAutomatonState.root, accepting := childAccepting 0 body
          skipping := childSkipping 0 body, completing := ∅
          edges := taggedCarrierEdges }
        seedCompleting := by
    simp only [buildRecursionAutomaton, finishAutomatonFragment,
      hTaggedCarrierEdgesDef, hSeedCompletingDef]
  rw [hGoal]
  have hTaggedSource : ∀ edge ∈ taggedCarrierEdges,
      edge.source = childState 0 state →
        ∃ original ∈ body.edges, original.source = state ∧
          original.label = edge.label ∧
          (original.target = state ↔ edge.target = childState 0 state) := by
    intro edge hEdge hSource
    simp only [hTaggedCarrierEdgesDef, Finset.mem_image] at hEdge
    obtain ⟨original, hOriginal, rfl⟩ := hEdge
    simp only at hSource ⊢
    have hOriginalSource : original.source = state := by
      simpa [childState] using hSource
    refine ⟨original, hOriginal, hOriginalSource, rfl, ?_⟩
    constructor
    · intro hTarget; simp [childState, hTarget]
    · intro hTarget; simpa [childState] using hTarget
  have hNotSeed : childState 0 state ∉ seedCompleting := by
    simp only [hSeedCompletingDef, Finset.mem_union, childCompleting,
      Finset.mem_image, not_or]
    constructor
    · split
      · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
          Finset.mem_filter, not_or]
        refine ⟨by simp [childState], ?_⟩
        rintro ⟨edge, ⟨hEdge, hLabel⟩, hEq⟩
        have hSource : edge.source = state := by simpa [childState] using hEq
        exact hNoVariable edge hEdge hSource hLabel
      · simp
    · rintro ⟨original, hOriginal, hEq⟩
      have hOriginalEq : original = state := by simpa [childState] using hEq
      exact hNotCompleting (hOriginalEq ▸ hOriginal)
  have hSubset : completingBackClosure
      { states := {TypeAutomatonState.root} ∪ childStates 0 body
        initial := TypeAutomatonState.root, accepting := childAccepting 0 body
        skipping := childSkipping 0 body, completing := ∅
        edges := taggedCarrierEdges }
      seedCompleting ⊆
      ((taggedCarrierEdges.image fun edge => edge.source) ∪
        seedCompleting).erase (childState 0 state) := by
    apply completingBackClosure_subset_of_predecessor_closed
    · intro candidate hCandidate
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_union_right _ hCandidate⟩
      rintro rfl
      exact hNotSeed hCandidate
    · intro edge hEdge hLabel hTarget
      refine Finset.mem_erase.mpr ⟨?_,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩)⟩
      intro hSourceEq
      obtain ⟨original, hOriginal, hOriginalSource, hOriginalLabel,
        hTargetIff⟩ := hTaggedSource edge hEdge hSourceEq
      have hOriginalTarget : original.target = state :=
        hNoNonClockEscape original hOriginal hOriginalSource
          (by rw [hOriginalLabel]; exact hLabel)
      exact (Finset.mem_erase.mp hTarget).1 (hTargetIff.mp hOriginalTarget)
  intro hMember
  exact (Finset.mem_erase.mp (hSubset hMember)).1 rfl

/--
Build a binary choice.

`Q` contains a fresh root and tagged copies of both child state sets. Selection
edges leave the root, and the accepting states are the union of both children.
The supplied labels distinguish ordinary epsilon choice from fair choice.
-/
def buildChoiceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) (selectionLeft selectionRight : TypeLabel) :
    AutomatonFragment :=
  let states := {TypeAutomatonState.root} ∪ childStates 0 left ∪ childStates 1 right
  let accepting := childAccepting 0 left ∪ childAccepting 1 right
  let skipping := childSkipping 0 left ∪ childSkipping 1 right
  let completing :=
    (if left.initial ∈ left.completing ∨ right.initial ∈ right.completing then
      {TypeAutomatonState.root}
    else ∅) ∪ childCompleting 0 left ∪ childCompleting 1 right
  let selections := signature.localEnvironments.biUnion fun environment =>
    { { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionLeft
        current := ∅
        future := .at (childState 0 left.initial) ∅
        target := childState 0 left.initial },
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible selectionRight
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial } }
  finishAutomatonFragment states .root accepting skipping completing
    (childPendingEdges 0 left ∪ childPendingEdges 1 right ∪ selections)

theorem buildChoiceAutomaton_outgoing_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 0 state ↔
      ∃ childEdge ∈ left.edges,
        childEdge.source = state ∧ edge = childPendingEdge 0 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hRight with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Or.inl ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

theorem buildChoiceAutomaton_outgoing_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) (edge : PendingAutomatonEdge) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    edge ∈ choice.edges ∧ edge.source = .child 1 state ↔
      ∃ childEdge ∈ right.edges,
        childEdge.source = state ∧ edge = childPendingEdge 1 childEdge := by
  classical
  constructor
  · rintro ⟨hEdge, hSource⟩
    simp only [buildChoiceAutomaton, finishAutomatonFragment,
      childPendingEdges, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with (hLeft | hRight) | hSelection
    · rcases hLeft with ⟨childEdge, _, hEdge⟩
      rw [← hEdge] at hSource
      simp [childPendingEdge, childState] at hSource
    · rcases hRight with ⟨childEdge, hChildEdge, hEdge⟩
      have hChildSource := hSource
      rw [← hEdge] at hChildSource
      simp [childPendingEdge, childState] at hChildSource
      exact ⟨childEdge, hChildEdge, hChildSource, hEdge.symm⟩
    · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
      · rw [hEdge] at hSource
        simp at hSource
      · rw [hEdge] at hSource
        simp at hSource
  · rintro ⟨childEdge, hChildEdge, hChildSource, rfl⟩
    constructor
    · simp only [buildChoiceAutomaton, finishAutomatonFragment,
        childPendingEdges, Finset.mem_union, Finset.mem_image,
        Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Or.inr ⟨childEdge, hChildEdge, rfl⟩)
    · simp [childPendingEdge, childState, hChildSource]

private theorem buildChoiceAutomaton_referencedStates_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.referencedStates (.child 0 state) =
      (child.referencedStates state).image (.child 0) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_left signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_referencedStates_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.referencedStates (.child 1 state) =
      (child.referencedStates state).image (.child 1) := by
  classical
  ext target
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_image]
  simp_rw [buildChoiceAutomaton_outgoing_right signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    parent.offersAt (.child 0 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_left signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

private theorem buildChoiceAutomaton_offersAt_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    parent.offersAt (.child 1 state) = child.offersAt state := by
  classical
  ext action
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  simp_rw [buildChoiceAutomaton_outgoing_right signature left right
    selectionLeft selectionRight]
  simp [childPendingEdge, childFutureSpec, childState]
  grind

/-- Future resolution inside the left tagged child of a choice is exactly the
child fragment's own future resolution. -/
theorem buildChoiceAutomaton_computeFuture_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ left.states)
    (hCard : left.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := left.states, edges := left.edges }
    computeFuture parent (.child 0 state) = computeFuture child state := by
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent : PendingAutomaton :=
    { states := choice.states, edges := choice.edges }
  let child : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  apply computeFuture_eq_of_embedding child parent (.child 0)
  · exact buildChoiceAutomaton_referencedStates_left signature left right
      selectionLeft selectionRight
  · exact buildChoiceAutomaton_offersAt_left signature left right
      selectionLeft selectionRight
  · exact hClosed
  · exact hState
  · exact hCard

/-- Future resolution inside the right tagged child of a choice is exactly the
child fragment's own future resolution. -/
theorem buildChoiceAutomaton_computeFuture_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    let choice := buildChoiceAutomaton signature left right
      selectionLeft selectionRight
    let parent : PendingAutomaton :=
      { states := choice.states, edges := choice.edges }
    let child : PendingAutomaton :=
      { states := right.states, edges := right.edges }
    computeFuture parent (.child 1 state) = computeFuture child state := by
  let choice := buildChoiceAutomaton signature left right
    selectionLeft selectionRight
  let parent : PendingAutomaton :=
    { states := choice.states, edges := choice.edges }
  let child : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  apply computeFuture_eq_of_embedding child parent (.child 1)
  · exact buildChoiceAutomaton_referencedStates_right signature left right
      selectionLeft selectionRight
  · exact buildChoiceAutomaton_offersAt_right signature left right
      selectionLeft selectionRight
  · exact hClosed
  · exact hState
  · exact hCard

/-- Marker reachability inside the left tagged child of a choice is exactly the
child fragment's own marker reachability. -/
theorem buildChoiceAutomaton_markerReachable_left
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (state : TypeAutomatonState)
    (hClosed : ({ states := left.states, edges := left.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ left.states)
    (hCard : left.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    MarkerReachable (buildChoiceAutomaton signature left right
        selectionLeft selectionRight) name (.child 0 state) ↔
      MarkerReachable left name state := by
  have hResult := markerReachable_of_embedding left
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    name (childState 0)
    (fun current => buildChoiceAutomaton_referencedStates_left signature left
      right selectionLeft selectionRight current)
    hClosed hCard
    (fun current _ => markerSource_of_outgoing_childPendingEdge _ left 0 name
      current (fun edge => buildChoiceAutomaton_outgoing_left signature left
        right selectionLeft selectionRight current edge))
    state hState
  simpa [childState] using hResult

/-- Marker reachability inside the right tagged child of a choice is exactly
the child fragment's own marker reachability. -/
theorem buildChoiceAutomaton_markerReachable_right
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel) (name : String)
    (state : TypeAutomatonState)
    (hClosed : ({ states := right.states, edges := right.edges } :
      PendingAutomaton).ReferencesClosed)
    (hState : state ∈ right.states)
    (hCard : right.states.card ≤
      (buildChoiceAutomaton signature left right
        selectionLeft selectionRight).states.card) :
    MarkerReachable (buildChoiceAutomaton signature left right
        selectionLeft selectionRight) name (.child 1 state) ↔
      MarkerReachable right name state := by
  have hResult := markerReachable_of_embedding right
    (buildChoiceAutomaton signature left right selectionLeft selectionRight)
    name (childState 1)
    (fun current => buildChoiceAutomaton_referencedStates_right signature left
      right selectionLeft selectionRight current)
    hClosed hCard
    (fun current _ => markerSource_of_outgoing_childPendingEdge _ right 1 name
      current (fun edge => buildChoiceAutomaton_outgoing_right signature left
        right selectionLeft selectionRight current edge))
    state hState
  simpa [childState] using hResult

theorem buildChoiceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (selectionLeft selectionRight : TypeLabel)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hLeftInitial : left.initial ∈ left.states)
    (hRightInitial : right.initial ∈ right.states) :
    (buildChoiceAutomaton signature left right
      selectionLeft selectionRight).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildChoiceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hEdge
  rcases hEdge with (hLeft | hRight) | hSelection
  · rcases hLeft with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hLeftTargets childEdge hChildEdge
          childTarget removed hSpec
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hRight with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hRightTargets childEdge hChildEdge
          childTarget removed hSpec
        simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
          childState, hChildTarget]
  · rcases hSelection with ⟨environment, _, hEdge | hEdge⟩
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hLeftInitial]
    · rw [hEdge] at hFuture
      simp only at hFuture
      cases hFuture
      simp [buildChoiceAutomaton, finishAutomatonFragment, childStates,
        childState, hRightInitial]

/--
Build sequential composition without collapsing its administrative step.

Left transitions remain inside the tagged left graph. Every completed left
state has a separate silent bridge into the right entry, representing
`skip ; τ → τ`. Only right accepting states are accepting for the sequence.
-/
def buildSequenceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) : AutomatonFragment :=
  let states := childStates 0 left ∪
    (left.edges.image fun edge => childState 0 edge.target) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  let skipping := childSkipping 1 right
  let completing :=
    (if right.initial ∈ right.completing then childCompleting 0 left else ∅) ∪
      childCompleting 1 right
  let leftEdges : Finset PendingAutomatonEdge := left.edges.image fun edge =>
    { source := childState 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := match edge.label with
        | .future => childFutureSpec 0 edge.future
        | _ => .at (childState 0 edge.target) edge.current
      target := childState 0 edge.target }
  let bridgeEdges : Finset PendingAutomatonEdge :=
    left.skipping.biUnion fun state =>
      signature.localEnvironments.image fun environment =>
        { source := childState 0 state
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState 1 right.initial) ∅
          target := childState 1 right.initial }
  let futureBridgeEdges : Finset PendingAutomatonEdge :=
    left.completing.image fun state =>
      { source := childState 0 state
        environment := .empty
        label := .future
        current := ∅
        future := .at (childState 1 right.initial) ∅
        -- This edge is bookkeeping-only (`.future` is never exported), but
        -- completion closure follows raw targets.  Its target must therefore
        -- agree with the continuation already named by `FutureSpec.at`.
        target := childState 1 right.initial }
  finishAutomatonFragment states (childState 0 left.initial) accepting skipping
    completing
    (leftEdges ∪ childPendingEdges 1 right ∪ bridgeEdges ∪ futureBridgeEdges)

theorem buildSequenceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (_hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton signature left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image,
    Finset.mem_biUnion] at hEdge
  rcases hEdge with ((hLeft | hRight) | hBridge) | hFutureBridge
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    cases hLabel : leftEdge.label with
    | future =>
        cases hSpec : leftEdge.future with
        | explicit offers =>
            simp [hLabel, childFutureSpec, hSpec] at hFuture
        | «at» childTarget childRemoved =>
            simp only [hLabel, childFutureSpec, hSpec] at hFuture
            cases hFuture
            have hChildTarget := _hLeftTargets leftEdge hLeftEdge
              childTarget removed hSpec
            simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
              childState, hChildTarget]
    | visible label =>
        simp only [hLabel] at hFuture
        cases hFuture
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        left
        right
        exact ⟨leftEdge, hLeftEdge, rfl⟩
    | «variable» name =>
        simp only [hLabel] at hFuture
        cases hFuture
        simp only [buildSequenceAutomaton, finishAutomatonFragment,
          Finset.mem_union, Finset.mem_image]
        left
        right
        exact ⟨leftEdge, hLeftEdge, rfl⟩
  · rcases hRight with ⟨rightEdge, hRightEdge, rfl⟩
    cases hSpec : rightEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» rightTarget removed =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hRightTarget := hRightTargets rightEdge hRightEdge
          rightTarget removed hSpec
        simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
          childState, hRightTarget]
  · rcases hBridge with ⟨leftState, hLeftSkipping, environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
      childState, hRightInitial]
  · rcases hFutureBridge with ⟨leftState, hLeftCompleting, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSequenceAutomaton, finishAutomatonFragment, childStates,
      childState, hRightInitial]

private def fragmentSuccessors (automaton : AutomatonFragment)
    (state : TypeAutomatonState) : Finset TypeAutomatonState :=
  (automaton.edges.filter fun edge => edge.source = state).image
    PendingAutomatonEdge.target

private def fragmentReachableAux (automaton : AutomatonFragment) :
    Nat → Finset TypeAutomatonState → Finset TypeAutomatonState
  | 0, reached => reached
  | fuel + 1, reached =>
      fragmentReachableAux automaton fuel
        (reached ∪ reached.biUnion (fragmentSuccessors automaton))

private theorem mem_fragmentReachableAux
    (automaton : AutomatonFragment) (state : TypeAutomatonState) :
    ∀ fuel reached,
      state ∈ reached → state ∈ fragmentReachableAux automaton fuel reached := by
  intro fuel
  induction fuel with
  | zero => simp [fragmentReachableAux]
  | succ fuel ih =>
      intro reached hState
      apply ih
      exact Finset.mem_union_left _ hState

private def restrictReachableFragment (automaton : AutomatonFragment) :
    AutomatonFragment :=
  let reachable := fragmentReachableAux automaton automaton.states.card {automaton.initial}
  { states := automaton.states.filter fun state => state ∈ reachable
    initial := automaton.initial
    accepting := automaton.accepting.filter fun state => state ∈ reachable
    skipping := automaton.skipping.filter fun state => state ∈ reachable
    completing := automaton.completing.filter fun state => state ∈ reachable
    edges := automaton.edges.filter fun edge =>
      edge.source ∈ reachable ∧ edge.target ∈ reachable }

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂`, the initial state is `(i₁,i₂)`, and accepting states are pairs
of accepting component states. Pairs of synchronizing transition edges are
retained as semantic edges, with their interface actions hidden. In addition,
each product state receives non-exported observation self-loops containing the
two component `computeFuture` menus. These internal edges preserve optimistic
same-cycle offers such as
the `{b!}` continuation of `skip |[{a}]| (a! ; b!)` without inventing a
semantic parallel step. The full finite Cartesian carrier is retained:
`TypeCompilationRelation` also relates syntactic product pairs that are
unreachable from the initial pair, and its step correspondence is intentionally
valid at those states as well.
-/
def buildParallelAutomaton (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let allLeftEdges := resolvedAutomatonEdges left
  let allRightEdges := resolvedAutomatonEdges right
  let leftEdges := allLeftEdges.filter fun edge => edge.label ≠ .future
  let rightEdges := allRightEdges.filter fun edge => edge.label ≠ .future
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let states : Finset TypeAutomatonState :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let accepting : Finset TypeAutomatonState :=
    left.accepting.biUnion fun leftState =>
      right.accepting.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let completing : Finset TypeAutomatonState :=
    left.completing.biUnion fun leftState =>
      right.completing.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let transitionEdges : Finset PendingAutomatonEdge :=
    leftEdges.biUnion fun leftEdge =>
    (rightEdges.filter fun rightEdge =>
      syncAutomatonEdges interface leftEdges rightEdges
        leftEdge rightEdge).image fun rightEdge =>
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := AutomatonConstructionLabel.combine interface
            leftEdge.label rightEdge.label
          current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
          future := .explicit
            (hideOffers interface (leftEdge.future ∪ rightEdge.future))
          target := .pair leftEdge.target rightEdge.target }
  let leftFutureEdges : Finset PendingAutomatonEdge :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface (computeFuture leftPending leftState)
          future := .explicit ∅
          target := .pair leftState rightState }
  let rightFutureEdges : Finset PendingAutomatonEdge :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        { source := .pair leftState rightState
          environment := .empty
          label := .future
          current := hideOffers interface (computeFuture rightPending rightState)
          future := .explicit ∅
          target := .pair leftState rightState }
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting ∅ completing
      (transitionEdges ∪ (leftFutureEdges ∪ rightFutureEdges))
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_filter] at hEdge
  rcases hEdge with hTransition | hObservation
  · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
    simp at hFuture
  · rcases hObservation with hLeft | hRight
    · rcases hLeft with ⟨leftEdge, _, rightState, _, rfl⟩
      simp at hFuture
    · rcases hRight with ⟨leftState, _, rightEdge, _, rfl⟩
      simp at hFuture

/-- Every offer reachable in the left component during the current cycle is
retained at the corresponding product state, independently of whether that
component currently has a synchronizable transition. -/
theorem buildParallelAutomaton_leftFuture_subset
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states) :
    hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState) ⊆
      computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) := by
  classical
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  rw [show computeFuture
      { states := (buildParallelAutomaton interface left right).states
        edges := (buildParallelAutomaton interface left right).edges }
      (.pair leftState rightState) = productPending.offersAt
        (.pair leftState rightState) by
      exact computeFuture_eq_offersAt_of_all_explicit productPending hExplicit _]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  let observation : PendingAutomatonEdge :=
    { source := .pair leftState rightState
      environment := .empty
      label := .future
      current := hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState)
      future := .explicit ∅
      target := .pair leftState rightState }
  refine ⟨observation, ⟨?_, rfl⟩, ?_⟩
  · simp [observation, productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, hLeftState, hRightState]
  · simpa [observation, AutomatonConstructionLabel.semantic] using hAction

/-- Symmetric optimistic-future preservation for the right component. -/
theorem buildParallelAutomaton_rightFuture_subset
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states) :
    hideOffers interface
        (computeFuture { states := right.states, edges := right.edges } rightState) ⊆
      computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) := by
  classical
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  rw [show computeFuture
      { states := (buildParallelAutomaton interface left right).states
        edges := (buildParallelAutomaton interface left right).edges }
      (.pair leftState rightState) = productPending.offersAt
        (.pair leftState rightState) by
      exact computeFuture_eq_offersAt_of_all_explicit productPending hExplicit _]
  intro action hAction
  simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
    Finset.mem_filter]
  let observation : PendingAutomatonEdge :=
    { source := .pair leftState rightState
      environment := .empty
      label := .future
      current := hideOffers interface
        (computeFuture { states := right.states, edges := right.edges } rightState)
      future := .explicit ∅
      target := .pair leftState rightState }
  refine ⟨observation, ⟨?_, rfl⟩, ?_⟩
  · simp [observation, productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, hLeftState, hRightState]
  · simpa [observation, AutomatonConstructionLabel.semantic] using hAction

/-- The future menu of a product state is exactly the hidden union of the two
component menus.  Synchronization controls semantic transitions, but does not
discard optimistic same-cycle continuations from either component. -/
theorem buildParallelAutomaton_computeFuture
    (interface : Interface) (left right : AutomatonFragment)
    (leftState rightState : TypeAutomatonState)
    (hLeftState : leftState ∈ left.states)
    (hRightState : rightState ∈ right.states)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates) :
    computeFuture
        { states := (buildParallelAutomaton interface left right).states
          edges := (buildParallelAutomaton interface left right).edges }
        (.pair leftState rightState) =
      hideOffers interface
        (computeFuture { states := left.states, edges := left.edges } leftState ∪
          computeFuture { states := right.states, edges := right.edges }
            rightState) := by
  classical
  let leftPending : PendingAutomaton :=
    { states := left.states, edges := left.edges }
  let rightPending : PendingAutomaton :=
    { states := right.states, edges := right.edges }
  let product := buildParallelAutomaton interface left right
  let productPending : PendingAutomaton :=
    { states := product.states, edges := product.edges }
  have hLeftClosed : leftPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates left hLeftTargets
  have hRightClosed : rightPending.ReferencesClosed :=
    PendingAutomaton.referencesClosed_of_futureTargetsInStates right hRightTargets
  have hExplicit : ∀ edge ∈ productPending.edges,
      ∃ offers, edge.future = .explicit offers := by
    intro edge hEdge
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with ⟨leftEdge, _, rightEdge, _, rfl⟩
      exact ⟨_, rfl⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
      · rcases hRight with ⟨leftSource, _, rightSource, _, rfl⟩
        exact ⟨_, rfl⟩
  change computeFuture productPending (.pair leftState rightState) = _
  rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, hOffer⟩
    simp only [productPending, product, buildParallelAutomaton,
      finishAutomatonFragment, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_image, Finset.mem_filter] at hEdge
    rcases hEdge with hTransition | hObservation
    · rcases hTransition with
        ⟨leftEdge, ⟨hLeftEdge, _⟩, rightEdge,
          ⟨⟨hRightEdge, _⟩, hSync⟩, rfl⟩
      injection hSource with hLeftSource hRightSource
      subst leftState
      subst rightState
      by_cases hClock :
          (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock
      · simp [hClock] at hOffer
      · simp only [hClock, if_false, FutureSpec.explicit,
          Finset.mem_union] at hOffer
        rcases hSync with
          ⟨leftWitness, _, rightWitness, _, hWitnesses⟩
        have hLabelSync : TypeLabel.Sync interface leftEdge.label.semantic
            rightEdge.label.semantic := by
          exact hWitnesses.2.2.2
        have hNonClock :=
          AutomatonConstructionLabel.component_nonclock_of_sync interface
            leftEdge.label rightEdge.label hLabelSync hClock
        have hLeftSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture left leftEdge
            hLeftEdge hLeftClosed hLeftState hNonClock.1
        have hRightSubset :=
          resolvedAutomatonEdge_offers_subset_computeFuture right rightEdge
            hRightEdge hRightClosed hRightState hNonClock.2
        simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hOffer ⊢
        rcases hOffer with hCurrent | hFuture
        · rcases hCurrent with ⟨hLeft | hRight, hOutside⟩
          · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_left _ hLeft)), hOutside⟩
          · exact ⟨Or.inr (hRightSubset (Finset.mem_union_left _ hRight)), hOutside⟩
        · rcases hFuture with ⟨hLeft | hRight, hOutside⟩
          · exact ⟨Or.inl (hLeftSubset (Finset.mem_union_right _ hLeft)), hOutside⟩
          · exact ⟨Or.inr (hRightSubset (Finset.mem_union_right _ hRight)), hOutside⟩
    · rcases hObservation with hLeft | hRight
      · rcases hLeft with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent,
          hideOffers] at hOffer ⊢
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        exact ⟨Or.inl hOffer.1, hOffer.2⟩
      · rcases hRight with ⟨leftSource, hLeftSource, rightSource,
          hRightSource, rfl⟩
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent,
          hideOffers] at hOffer ⊢
        injection hSource with hLeftEq hRightEq
        subst leftSource
        subst rightSource
        exact ⟨Or.inr hOffer.1, hOffer.2⟩
  · intro action hAction
    simp only [hideOffers, Finset.mem_filter, Finset.mem_union] at hAction
    rcases hAction with ⟨hLeft | hRight, hOutside⟩
    · have hHidden : action ∈ hideOffers interface
          (computeFuture { states := left.states, edges := left.edges }
            leftState) := Finset.mem_filter.mpr ⟨hLeft, hOutside⟩
      have hIncluded :=
        buildParallelAutomaton_leftFuture_subset interface left right
          leftState rightState hLeftState hRightState
          hHidden
      rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
        at hIncluded
      simpa [productPending, product] using hIncluded
    · have hHidden : action ∈ hideOffers interface
          (computeFuture { states := right.states, edges := right.edges }
            rightState) := Finset.mem_filter.mpr ⟨hRight, hOutside⟩
      have hIncluded :=
        buildParallelAutomaton_rightFuture_subset interface left right
          leftState rightState hLeftState hRightState
          hHidden
      rw [computeFuture_eq_offersAt_of_all_explicit productPending hExplicit]
        at hIncluded
      simpa [productPending, product] using hIncluded

theorem mem_foldl_union_iff
    {Element Item : Type} [DecidableEq Element]
    (items : List Item) (part : Item → Finset Element)
    (initial : Finset Element) (element : Element) :
    element ∈ items.foldl (fun accumulated item =>
      accumulated ∪ part item) initial ↔
      element ∈ initial ∨ ∃ item ∈ items, element ∈ part item := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

private theorem childPendingEdges_futureTargetsInStates
    (index : Nat) (fragment : AutomatonFragment)
    (hTargets : fragment.FutureTargetsInStates) :
    ∀ edge ∈ childPendingEdges index fragment, ∀ target removed,
      edge.future = .at target removed →
        target ∈ childStates index fragment := by
  classical
  intro edge hEdge target removed hFuture
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hSpec : childEdge.future with
  | explicit offers =>
      simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
  | «at» childTarget childRemoved =>
      simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
      cases hFuture
      have hChildTarget := hTargets childEdge hChildEdge childTarget
        removed hSpec
      simp [childStates, childState, hChildTarget]

def indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childStates (indexed.2 + 1) indexed.1.2) ∅

private def indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childAccepting (indexed.2 + 1) indexed.1.2) ∅

def indexedFragmentSkipping
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childSkipping (indexed.2 + 1) indexed.1.2) ∅

def indexedFragmentCompleting
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childCompleting (indexed.2 + 1) indexed.1.2) ∅

def indexedFragmentEdges
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset PendingAutomatonEdge :=
  automata.zipIdx.foldl (fun edges indexed =>
    edges ∪ childPendingEdges (indexed.2 + 1) indexed.1.2) ∅

private theorem indexedFragment_futureTargetsInStates
    (automata : List (BareMessage × AutomatonFragment))
    (hTargets : ∀ entry ∈ automata, entry.2.FutureTargetsInStates) :
    ∀ edge ∈ indexedFragmentEdges automata, ∀ target removed,
      edge.future = .at target removed →
        target ∈ indexedFragmentStates automata := by
  classical
  intro edge hEdge target removed hFuture
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    simp only [childPendingEdges, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget childRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hTargets indexed.1 hEntry childEdge hChildEdge
          childTarget removed hSpec
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        simp [childStates, childState, hChildTarget]

/--
Build an exclusive offer with one fresh root.

Child `0` is the else continuation; children `1..n` are branch continuations.
From the root there are three kinds of edges:

* `branchEdges`: fire an immediately enabled and resolved branch;
* `waitEdges`: remain at the root while a branch may still arrive this cycle;
* `elseEdges`: select the else continuation once no branch can still arrive.
-/
def buildExclusiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 elseAutomaton ∪
    indexedFragmentStates branchAutomata
  let accepting := childAccepting 0 elseAutomaton ∪
    indexedFragmentAccepting branchAutomata
  let skipping := childSkipping 0 elseAutomaton ∪
    indexedFragmentSkipping branchAutomata
  let completing :=
    (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
        branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
      {TypeAutomatonState.root}
    else ∅) ∪ childCompleting 0 elseAutomaton ∪
      indexedFragmentCompleting branchAutomata
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let branchEdges : Finset PendingAutomatonEdge := branchAutomata.zipIdx.foldl
    (fun edges indexed =>
      let index := indexed.2
      let action := indexed.1.1
      let automaton := indexed.1.2
      let newEdges : Finset PendingAutomatonEdge :=
        let enablingEnvironments := signature.localEnvironments.filter fun environment =>
          typeNeed action ∈ environment.immediate ∧
          needs ∩ environment.future = ∅
        enablingEnvironments.image fun environment =>
          { source := TypeAutomatonState.root
            environment := environment
            label := .visible (TypeLabel.message action.1 action.2)
            current := {action}
            future := .at (childState (index + 1) automaton.initial) ∅
            target := childState (index + 1) automaton.initial }
      edges ∪ newEdges) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting skipping completing
    (childPendingEdges 0 elseAutomaton ∪ indexedFragmentEdges branchAutomata ∪
      branchEdges ∪ waitEdges ∪ elseEdges)

theorem buildExclusiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton signature branches elseAutomaton
      branchAutomata).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates branchAutomata
      hBranchTargets edge hIndexed target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
    · simp at hEmpty
    · have hEntry : indexed.1 ∈ branchAutomata := by
        have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexedEntry
        simpa using hMapped
      simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hFuture
      cases hFuture
      have hInitial := hBranchInitial indexed.1 hEntry
      have hIndexedState :
          childState (indexed.2 + 1) indexed.1.2.initial ∈
            indexedFragmentStates branchAutomata := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexedEntry, ?_⟩
        simp [childStates, childState, hInitial]
      simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Legacy unspecialized conjunction builder, retained for the generic graph
lemmas about an arbitrary conjunction child.  The compiler uses the selected
builder below, which removes only the all-else outcome after an enabled branch
has witnessed entry. -/
def buildConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 conjunction ∪
    childStates 1 elseAutomaton
  let accepting := childAccepting 0 conjunction ∪ childAccepting 1 elseAutomaton
  let skipping := childSkipping 0 conjunction ∪ childSkipping 1 elseAutomaton
  let completing :=
    (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
        branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
      {TypeAutomatonState.root}
    else ∅) ∪ childCompleting 0 conjunction ∪
      childCompleting 1 elseAutomaton
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let enabledEdges : Finset PendingAutomatonEdge :=
    let enablingEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate ≠ ∅
    enablingEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 conjunction.initial) ∅
        target := childState 0 conjunction.initial }
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting skipping completing
    (childPendingEdges 0 conjunction ∪ childPendingEdges 1 elseAutomaton ∪
      enabledEdges ∪ waitEdges ∪ elseEdges)

theorem buildConjunctiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : conjunction.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : conjunction.initial ∈ conjunction.states) :
    (buildConjunctiveOfferAutomaton signature branches elseAutomaton
      conjunction).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElse) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 conjunction
      hConjunctionTargets edge hConjunction target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := childPendingEdges_futureTargetsInStates 1 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hConjunctionInitial]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Post-construction conjunctive-offer builder.  Each enabled witness enters
its own copy of the singleton product with that witness's synthetic else arm
removed; the other singleton else arms remain available. -/
def buildSelectedConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 elseAutomaton ∪
    indexedFragmentStates selectedConjunctions
  let accepting := childAccepting 0 elseAutomaton ∪
    indexedFragmentAccepting selectedConjunctions
  let skipping := childSkipping 0 elseAutomaton ∪
    indexedFragmentSkipping selectedConjunctions
  let completing :=
    (if elseAutomaton.initial ∈ elseAutomaton.completing ∨
        branches.any (fun branch => branch.2.CanCompleteBeforeTock) then
      {TypeAutomatonState.root}
    else ∅) ∪ childCompleting 0 elseAutomaton ∪
      indexedFragmentCompleting selectedConjunctions
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let enabledEdges : Finset PendingAutomatonEdge :=
    selectedConjunctions.zipIdx.foldl (fun edges indexed =>
      let index := indexed.2
      let action := indexed.1.1
      let conjunction := indexed.1.2
      let enablingEnvironments := signature.localEnvironments.filter
        fun environment => typeNeed action ∈ environment.immediate
      edges ∪ enablingEnvironments.image fun environment =>
        { source := TypeAutomatonState.root
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState (index + 1) conjunction.initial) ∅
          target := childState (index + 1) conjunction.initial }) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting skipping completing
    (childPendingEdges 0 elseAutomaton ∪
      indexedFragmentEdges selectedConjunctions ∪ enabledEdges ∪
        waitEdges ∪ elseEdges)

theorem buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    (buildSelectedConjunctiveOfferAutomaton signature branches elseAutomaton
      selectedConjunctions).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates
      selectedConjunctions hConjunctionTargets edge hConjunction target removed
        hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hFuture
      cases hFuture
      have hIndexedFields := List.mem_zipIdx hIndexed
      simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
        at hIndexedFields
      rcases hIndexedFields with ⟨hBound, hValue⟩
      have hEntry : indexed.1 ∈ selectedConjunctions := by
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hIndexedState : childState (indexed.2 + 1)
          indexed.1.2.initial ∈
          indexedFragmentStates selectedConjunctions := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        exact Or.inr ⟨indexed, hIndexed, Finset.mem_image.mpr
          ⟨indexed.1.2.initial, hConjunctionInitial indexed.1 hEntry, rfl⟩⟩
      simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-!
### Constructor compiler
-/

/-
`compileTypeFuel` also compiles the type generated for a conjunctive offer.
Consequently, a plain recursion-depth calculation on `PactType` is not quite
enough: the generated parallel tree must be accounted for as well.

These three mutually recursive functions calculate exactly the structural
budget needed by the calls below.  Atomic constructors need one unit.  A
compound constructor needs one unit plus the largest budget of any recursive
call that it makes.
-/
mutual
  def typeCompilationFuel : PactType → Nat
    | .message _ _ => 1
    | .progress _ => 1
    | .tock => 1
    | .skip => 1
    | .var _ => 1
    | .recur _ body => 1 + typeCompilationFuel body
    | .choice left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .fairChoice _ left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .seq left right =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .par left right _ =>
        1 + max (typeCompilationFuel left) (typeCompilationFuel right)
    | .xoffer elseType branches =>
        1 + max (typeCompilationFuel elseType)
          (typeBranchCompilationFuel branches)
    | .offer elseType branches =>
        1 + max (typeCompilationFuel elseType)
          (conjunctiveCompilationFuel branches)
  termination_by processType => sizeOf processType

  /-- Largest compilation budget among all branch continuations. -/
  def typeBranchCompilationFuel :
      List (BareMessage × PactType) → Nat
    | [] => 0
    | (_, processType) :: rest =>
        max (typeCompilationFuel processType)
          (typeBranchCompilationFuel rest)
  termination_by branches => sizeOf branches

  /-- Budget for the parallel singleton offers generated by an `offer`. -/
  def conjunctiveCompilationFuel :
      List (BareMessage × PactType) → Nat
    | [] => 1
    | [(_, processType)] =>
        1 + max 1 (typeCompilationFuel processType)
    | (_, processType) :: next :: rest =>
        1 + max
          (1 + max 1 (typeCompilationFuel processType))
          (conjunctiveCompilationFuel (next :: rest))
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

/--
The auxiliary budget is exactly the budget of the parallel type generated for
a conjunctive offer.  This is the non-structural recursive call that motivates
the custom fuel calculation.
-/
theorem typeCompilationFuel_parallelTypeBranches
    (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranches branches) =
      conjunctiveCompilationFuel branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranches, typeCompilationFuel,
        conjunctiveCompilationFuel]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            typeCompilationFuel, typeBranchCompilationFuel,
            conjunctiveCompilationFuel]
      | cons next tail =>
          simp [parallelTypeBranches, singletonTypeXOffer,
            typeCompilationFuel, typeBranchCompilationFuel,
            conjunctiveCompilationFuel, ih]

/-- Forcing one singleton branch removes only its synthetic else outcome and
does not change the compilation budget of the generated parallel product. -/
theorem typeCompilationFuel_parallelTypeBranchesSelecting
    (selected : BareMessage × PactType)
    (branches : List (BareMessage × PactType)) :
    typeCompilationFuel (parallelTypeBranchesSelecting selected branches) =
      conjunctiveCompilationFuel branches := by
  induction branches with
  | nil =>
      simp [parallelTypeBranchesSelecting, typeCompilationFuel,
        conjunctiveCompilationFuel]
  | cons branch rest ih =>
      rcases branch with ⟨action, processType⟩
      cases rest with
      | nil =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              typeCompilationFuel, typeBranchCompilationFuel,
              conjunctiveCompilationFuel]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, typeCompilationFuel,
              typeBranchCompilationFuel, conjunctiveCompilationFuel]
      | cons next tail =>
          by_cases hSelected : (action, processType) = selected
          · subst selected
            simp [parallelTypeBranchesSelecting, selectedTypeBranch,
              typeCompilationFuel, typeBranchCompilationFuel,
              conjunctiveCompilationFuel,
              typeCompilationFuel_parallelTypeBranches]
          · simp [parallelTypeBranchesSelecting, hSelected,
              singletonTypeXOffer, typeCompilationFuel,
              typeBranchCompilationFuel, conjunctiveCompilationFuel, ih]

/-- `fuel` covers every recursive call made while compiling `processType`. -/
def TypeCompilationFuelSufficient
    (processType : PactType) (fuel : Nat) : Prop :=
  typeCompilationFuel processType ≤ fuel

/-- The calculated compilation budget is sufficient by construction. -/
theorem typeCompilationFuel_sufficient (processType : PactType) :
    TypeCompilationFuelSufficient processType
      (typeCompilationFuel processType) := by
  exact le_rfl

/-- Every type receives at least the one unit needed to enter its constructor. -/
theorem typeCompilationFuel_positive (processType : PactType) :
    0 < typeCompilationFuel processType := by
  cases processType <;> simp [typeCompilationFuel] <;> omega

/-- Sufficient fuel can never select the defensive zero-fuel case at the root. -/
theorem TypeCompilationFuelSufficient.positive
    {processType : PactType} {fuel : Nat}
    (hFuel : TypeCompilationFuelSufficient processType fuel) :
    0 < fuel :=
  lt_of_lt_of_le (typeCompilationFuel_positive processType) hFuel

theorem typeCompilationFuel_le_typeBranchCompilationFuel
    (branches : List (BareMessage × PactType))
    (entry : BareMessage × PactType) (hEntry : entry ∈ branches) :
    typeCompilationFuel entry.2 ≤ typeBranchCompilationFuel branches := by
  induction branches with
  | nil => simp at hEntry
  | cons head rest ih =>
      rcases head with ⟨action, processType⟩
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hRest
      · simp [typeBranchCompilationFuel]
      · exact le_trans (ih hRest) (by
          simp [typeBranchCompilationFuel])

def compileTypeFuel (signature : TypeAlphabet) :
    Nat → PactType → AutomatonFragment
  -- Exhausted fuel is an unreachable defensive case for the public compiler.
  | 0, _ =>
      { states := {.root}
        initial := .root
        accepting := ∅
        skipping := ∅
        completing := ∅
        edges := ∅ }
  | fuel + 1, processType => by
      classical
      match processType with
      -- skip: Q = {root}, i = root, F = {root}; epsilon self-loops.
      | .skip =>
          let idleEnvironments := signature.localEnvironments.filter fun environment =>
            environment.clock = false ∧ environment.immediate = ∅
          exact finishAutomatonFragment {.root} .root {.root} {.root} {.root} <|
            idleEnvironments.image fun environment =>
              { source := .root
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .root }

      -- message: fire to final when its complement is immediate; otherwise wait.
      | .message msg dir =>
          let action : BareMessage := (msg, dir)
          let firingEdges : Finset PendingAutomatonEdge :=
            (signature.localEnvironments.filter fun environment =>
              environment.hasNeed action).image fun environment =>
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible (TypeLabel.message msg dir)
                  current := {action}
                  future := .explicit ∅
                  target := .final }
          let waitingEdges : Finset PendingAutomatonEdge :=
            (signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              ¬ environment.hasNeed action).image fun environment =>
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.silent
                  current := {action}
                  future := .explicit ∅
                  target := .root }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            {.root, .final}
            (firingEdges ∪ waitingEdges ∪ finalEdges)

      -- clock: a clock environment moves root to final; non-clock input waits.
      | .tock =>
          let actionEdges : Finset PendingAutomatonEdge :=
            signature.localEnvironments.image fun environment =>
              if environment.clock then
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.tock
                  current := ∅
                  future := .explicit ∅
                  target := .final }
              else
                { source := TypeAutomatonState.root
                  environment := environment
                  label := .visible TypeLabel.silent
                  current := ∅
                  future := .explicit ∅
                  target := .root }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            {.final}
            (actionEdges ∪ finalEdges)

      -- progress: emit the marker and enter final; final then idles silently.
      | .progress pid =>
          let actionEdges : Finset PendingAutomatonEdge :=
            signature.localEnvironments.image fun environment =>
              { source := TypeAutomatonState.root
                environment := environment
                label := .visible (TypeLabel.progress pid)
                current := ∅
                future := .explicit ∅
                target := .final }
          let finalEdges : Finset PendingAutomatonEdge :=
            let idleEnvironments := signature.localEnvironments.filter fun environment =>
              environment.clock = false ∧
              environment.immediate = ∅
            idleEnvironments.image fun environment =>
              { source := TypeAutomatonState.final
                environment := environment
                label := .visible TypeLabel.silent
                current := ∅
                future := .explicit ∅
                target := .final }
          exact finishAutomatonFragment {.root, .final} .root {.final} {.final}
            {.root, .final}
            (actionEdges ∪ finalEdges)

      -- variable: create a temporary labelled edge for an enclosing binder.
      | .var name =>
          exact finishAutomatonFragment {.root, .final} .root ∅ ∅ ∅ <|
            signature.localEnvironments.image fun environment =>
              { source := .root
                environment := environment
                label := .variable name
                current := ∅
                future := .explicit ∅
                target := .final }

      -- recursion: replace matching variable edges by silent back-edges.
      | .recur name body =>
          exact buildRecursionAutomaton signature name
            (compileTypeFuel signature fuel body)
      -- ordinary choice: add a fresh root with two silent selection edges.
      | .choice left right =>
          exact buildChoiceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            TypeLabel.silent TypeLabel.silent

      -- fair choice: use the same sum construction with observable outcomes.
      | .fairChoice bid left right =>
          exact buildChoiceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)
            (TypeLabel.fair bid true) (TypeLabel.fair bid false)

      -- sequence: redirect transitions entering a left final state into right.
      | .seq left right =>
          exact buildSequenceAutomaton signature
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)

      -- parallel: form the reachable synchronized product on `interface`.
      | .par left right interface =>
          exact buildParallelAutomaton interface
            (compileTypeFuel signature fuel left)
            (compileTypeFuel signature fuel right)

      -- exclusive offer: compile else and every branch independently first.
      | .xoffer elseType branches =>
          let elseAutomaton := compileTypeFuel signature fuel elseType
          let branchAutomata := branches.map fun branch =>
            (branch.1, compileTypeFuel signature fuel branch.2)
          exact buildExclusiveOfferAutomaton
            signature branches elseAutomaton branchAutomata

      -- conjunctive offer: compile its singleton-offer parallel product first.
      | .offer elseType branches =>
          let elseAutomaton := compileTypeFuel signature fuel elseType
          let selectedConjunctions := branches.map fun selected =>
            (selected.1, compileTypeFuel signature fuel
              (parallelTypeBranchesSelecting selected branches))
          exact buildSelectedConjunctiveOfferAutomaton
            signature branches elseAutomaton selectedConjunctions

/-- Once fuel covers the custom compilation budget, one more unit leaves the
constructor fragment unchanged. -/
private theorem compileTypeFuel_succ_stable (signature : TypeAlphabet) :
    ∀ fuel processType, typeCompilationFuel processType ≤ fuel →
      compileTypeFuel signature (fuel + 1) processType =
        compileTypeFuel signature fuel processType := by
  intro fuel
  induction fuel with
  | zero =>
      intro processType hFuel
      have hPositive := typeCompilationFuel_positive processType
      omega
  | succ fuel ih =>
      intro processType hFuel
      cases processType with
      | message msg dir => rfl
      | progress pid => rfl
      | tock => rfl
      | skip => rfl
      | var name => rfl
      | recur name body =>
          change buildRecursionAutomaton signature name
              (compileTypeFuel signature (fuel + 1) body) =
            buildRecursionAutomaton signature name
              (compileTypeFuel signature fuel body)
          rw [ih body (by
            simp [typeCompilationFuel] at hFuel
            omega)]
      | choice left right =>
          change buildChoiceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right)
              TypeLabel.silent TypeLabel.silent =
            buildChoiceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
              TypeLabel.silent TypeLabel.silent
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | fairChoice bid left right =>
          change buildChoiceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false) =
            buildChoiceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
              (TypeLabel.fair bid true) (TypeLabel.fair bid false)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | seq left right =>
          change buildSequenceAutomaton signature
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right) =
            buildSequenceAutomaton signature
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | par left right interface =>
          change buildParallelAutomaton interface
              (compileTypeFuel signature (fuel + 1) left)
              (compileTypeFuel signature (fuel + 1) right) =
            buildParallelAutomaton interface
              (compileTypeFuel signature fuel left)
              (compileTypeFuel signature fuel right)
          rw [ih left (by
              simp [typeCompilationFuel] at hFuel
              omega),
            ih right (by
              simp [typeCompilationFuel] at hFuel
              omega)]
      | xoffer elseType branches =>
          change buildExclusiveOfferAutomaton signature branches
              (compileTypeFuel signature (fuel + 1) elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel signature (fuel + 1) branch.2)) =
            buildExclusiveOfferAutomaton signature branches
              (compileTypeFuel signature fuel elseType)
              (branches.map fun branch =>
                (branch.1, compileTypeFuel signature fuel branch.2))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse]
          congr 1
          have hBranches : typeBranchCompilationFuel branches ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hMap : ∀ rest,
              typeBranchCompilationFuel rest ≤ fuel →
              (rest.map fun branch =>
                (branch.1, compileTypeFuel signature (fuel + 1) branch.2)) =
              (rest.map fun branch =>
                (branch.1, compileTypeFuel signature fuel branch.2)) := by
            intro rest
            induction rest with
            | nil => simp
            | cons branch tail tailIH =>
                intro hRest
                rcases branch with ⟨action, branchType⟩
                simp only [List.map_cons]
                have hBranch : typeCompilationFuel branchType ≤ fuel := by
                  simp [typeBranchCompilationFuel] at hRest
                  omega
                rw [ih branchType hBranch]
                congr 1
                apply tailIH
                simp [typeBranchCompilationFuel] at hRest ⊢
                omega
          exact hMap branches hBranches
      | offer elseType branches =>
          change buildSelectedConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature (fuel + 1) elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel signature (fuel + 1)
                  (parallelTypeBranchesSelecting selected branches))) =
            buildSelectedConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature fuel elseType)
              (branches.map fun selected =>
                (selected.1, compileTypeFuel signature fuel
                  (parallelTypeBranchesSelecting selected branches)))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse]
          congr 1
          apply List.map_congr_left
          intro selected hSelected
          congr 1
          apply ih
          rw [typeCompilationFuel_parallelTypeBranchesSelecting]
          simp [typeCompilationFuel] at hFuel
          omega

/-- Any two sufficient parent budgets produce the same constructor fragment. -/
private theorem compileTypeFuel_add_stable
    (signature : TypeAlphabet) (processType : PactType)
    (fuel extra : Nat) (hFuel : typeCompilationFuel processType ≤ fuel) :
    compileTypeFuel signature (fuel + extra) processType =
      compileTypeFuel signature fuel processType := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ,
        compileTypeFuel_succ_stable signature (fuel + extra) processType
          (by omega),
        ih]

theorem compileTypeFuel_eq_of_sufficient
    (signature : TypeAlphabet) (processType : PactType)
    {leftFuel rightFuel : Nat}
    (hLeft : TypeCompilationFuelSufficient processType leftFuel)
    (hRight : TypeCompilationFuelSufficient processType rightFuel) :
    compileTypeFuel signature leftFuel processType =
      compileTypeFuel signature rightFuel processType := by
  by_cases hOrder : leftFuel ≤ rightFuel
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hOrder
    exact (compileTypeFuel_add_stable signature processType leftFuel extra
      hLeft).symm
  · have hReverse : rightFuel ≤ leftFuel := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hReverse
    exact compileTypeFuel_add_stable signature processType rightFuel extra hRight

/-- A decorated automaton edge represented as the tuple `(q, σ, q')`. -/
structure TypeAutomatonEdge : Type where
  source : TypeAutomatonState
  symbol : TypeAutomatonSymbol
  target : TypeAutomatonState
  deriving DecidableEq

/-- Final finite automaton exposed to conformance and compatibility proofs. -/
structure TypeAutomaton : Type where
  signature : TypeAlphabet
  states : Finset TypeAutomatonState
  initial : TypeAutomatonState
  accepting : Finset TypeAutomatonState
  alphabet : Finset TypeAutomatonSymbol
  edges : Finset TypeAutomatonEdge

namespace TypeAutomaton

  /-- Membership of a decorated edge in the finite transition relation. -/
  def HasEdge (automaton : TypeAutomaton)
      (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
      (offers : TypeOfferSummary) (target : TypeAutomatonState) : Prop :=
    { source := source,
      symbol := { environment := env, label := label, offers := offers },
      target := target } ∈ automaton.edges

end TypeAutomaton

/-- States mentioned by a finite decorated edge relation. -/
private def typeAutomatonEdgeStates
    (edges : Finset TypeAutomatonEdge) : Finset TypeAutomatonState :=
  edges.biUnion fun edge => {edge.source, edge.target}

/--
Compile a type by composing its constructor automata,
then remove unresolved variable edges and transitions outside the fixed external alphabet.
-/
def compileType
    (signature : TypeAlphabet)
    (processType : PactType) : TypeAutomaton :=
  let fuel := typeCompilationFuel processType
  let constructed := compileTypeFuel signature fuel processType
  let constructedEdges := resolvedAutomatonEdges constructed
  let transitionAlphabet := signature.transitionAlphabet
  let edges : Finset TypeAutomatonEdge := constructedEdges.biUnion fun edge =>
    match edge.label with
    | .variable _ => ∅
    | .future => ∅
    | .visible label =>
        let symbol : TypeAutomatonSymbol :=
          { environment := edge.environment
            label := label
            offers := { current := edge.current, future := edge.future } }
        if symbol ∈ transitionAlphabet then
          {{ source := edge.source, symbol := symbol, target := edge.target }}
        else ∅
  { signature := signature
    -- Closing the exported carrier under edge endpoints makes the usual
    -- finite-automaton state invariant explicit even if an intermediate
    -- constructor has retained an otherwise unreachable endpoint.
    states := constructed.states ∪ typeAutomatonEdgeStates edges
    initial := constructed.initial
    accepting := constructed.accepting
    alphabet := transitionAlphabet
    edges := edges }

/-- A visible edge in a constructor fragment after resolving its symbolic
future field against that complete fragment.  This is the internal edge view
used by the structural correspondence proof, before the public alphabet
filter is applied. -/
def AutomatonFragment.HasResolvedEdge (fragment : AutomatonFragment)
    (source : TypeAutomatonState) (env : TypeEnvironment) (label : TypeLabel)
    (offers : TypeOfferSummary) (target : TypeAutomatonState) : Prop :=
  ∃ edge ∈ fragment.edges,
    edge.source = source ∧ edge.environment = env ∧
      edge.label = .visible label ∧ edge.current = offers.current ∧
      (match edge.future with
        | .explicit future => future
        | .at state removed =>
            computeFuture
              { states := fragment.states, edges := fragment.edges }
              state \ removed) = offers.future ∧
      edge.target = target

/-- Once a symbol belongs to the fixed alphabet, public edge membership is
exactly resolved membership in the constructor fragment. -/
theorem compileType_hasEdge_iff_hasResolvedEdge
    (signature : TypeAlphabet) (processType : PactType)
    (source target : TypeAutomatonState) (env : TypeEnvironment)
    (label : TypeLabel) (offers : TypeOfferSummary)
    (hSymbol : TypeAutomatonSymbol.mk env label offers ∈
      signature.transitionAlphabet) :
    (compileType signature processType).HasEdge source env label offers target ↔
      AutomatonFragment.HasResolvedEdge
        (compileTypeFuel signature (typeCompilationFuel processType) processType)
        source env label offers target := by
  classical
  simp [TypeAutomaton.HasEdge, compileType,
    AutomatonFragment.HasResolvedEdge, resolvedAutomatonEdges, hSymbol]
  aesop

/-- The source of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_source_mem
    (signature : TypeAlphabet) (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge
      source env label offers target) :
    source ∈ (compileType signature processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- The target of every compiled transition belongs to the exported state
carrier. -/
theorem compileType_edge_target_mem
    (signature : TypeAlphabet) (processType : PactType)
    {source target : TypeAutomatonState} {env : TypeEnvironment}
    {label : TypeLabel} {offers : TypeOfferSummary}
    (hEdge : (compileType signature processType).HasEdge
      source env label offers target) :
    target ∈ (compileType signature processType).states := by
  simp only [TypeAutomaton.HasEdge] at hEdge
  simp only [compileType, Finset.mem_union]
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨
    { source := source
      symbol := { environment := env, label := label, offers := offers }
      target := target }, hEdge, ?_⟩
  simp

/-- Regression theorem: compiled `skip` has no edge in a clock environment. -/
theorem compileType_skip_has_no_clock_edge
    (signature : TypeAlphabet) (offers : TypeOfferSummary)
    (target : TypeAutomatonState) :
    ¬ (compileType signature .skip).HasEdge
      (compileType signature .skip).initial
      TypeEnvironment.tock TypeLabel.silent offers target := by
  simp [TypeAutomaton.HasEdge, compileType, typeCompilationFuel,
    compileTypeFuel, finishAutomatonFragment, resolvedAutomatonEdges,
    TypeEnvironment.tock]
  intro environment _ hClock _
  split_ifs
  · simp only [Finset.mem_singleton]
    intro edgeEquality
    have clockEquality := congrArg
      (fun edge : TypeAutomatonEdge => edge.symbol.environment.clock)
      edgeEquality
    simp [hClock] at clockEquality
  · simp


end

end Pact
