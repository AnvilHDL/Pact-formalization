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
-/
inductive AutomatonConstructionLabel : Type where
  | visible : TypeLabel → AutomatonConstructionLabel
  | variable : String → AutomatonConstructionLabel
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

  /-- Combine product labels while preserving an unresolved recursion marker. -/
  def combine (interface : Interface)
      (left right : AutomatonConstructionLabel) : AutomatonConstructionLabel :=
    match left, right with
    | .variable name, _ => .variable name
    | _, .variable name => .variable name
    | .visible leftLabel, .visible rightLabel =>
        .visible (TypeLabel.combine interface leftLabel rightLabel)

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
    (accepting skipping : Finset TypeAutomatonState)
    (edges : Finset PendingAutomatonEdge) : AutomatonFragment :=
  { states := states
    initial := initial
    accepting := accepting
    skipping := skipping
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
  finishAutomatonFragment states .root accepting skipping (headerEdges ∪ bodyEdges)

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
  finishAutomatonFragment states .root accepting skipping
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
  let leftEdges : Finset PendingAutomatonEdge := left.edges.image fun edge =>
    { source := childState 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := .at (childState 0 edge.target) edge.current
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
  finishAutomatonFragment states (childState 0 left.initial) accepting skipping
    (leftEdges ∪ childPendingEdges 1 right ∪ bridgeEdges)

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
  rcases hEdge with (hLeft | hRight) | hBridge
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
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
    edges := automaton.edges.filter fun edge =>
      edge.source ∈ reachable ∧ edge.target ∈ reachable }

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂`, the initial state is `(i₁,i₂)`, and accepting states are pairs
of accepting component states. Only pairs of synchronizing edges are retained;
their interface actions are hidden before the resulting edge is exposed.  The
full finite Cartesian carrier is retained: `TypeCompilationRelation` also
relates syntactic product pairs that are unreachable from the initial pair,
and its step correspondence is intentionally valid at those states as well.
-/
def buildParallelAutomaton (interface : Interface)
    (left right : AutomatonFragment) : AutomatonFragment := by
  classical
  let leftEdges := resolvedAutomatonEdges left
  let rightEdges := resolvedAutomatonEdges right
  let states : Finset TypeAutomatonState :=
    left.states.biUnion fun leftState =>
      right.states.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let accepting : Finset TypeAutomatonState :=
    left.accepting.biUnion fun leftState =>
      right.accepting.image fun rightState =>
        TypeAutomatonState.pair leftState rightState
  let edges : Finset PendingAutomatonEdge := leftEdges.biUnion fun leftEdge =>
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
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting ∅ edges
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (interface : Interface) (left right : AutomatonFragment) :
    (buildParallelAutomaton interface left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with ⟨leftEdge, _, rightEdge, _, rfl⟩
  simp at hFuture

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

private def indexedFragmentEdges
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
  exact finishAutomatonFragment states .root accepting skipping
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

/--
Build a conjunctive offer with one fresh root.

If at least one branch is enabled, enter the precompiled parallel product of
singleton exclusive offers. If no branch is immediate or future, enter the
else continuation. The conjunction and else automata are tagged as children
`0` and `1`, respectively.
-/
def buildConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 conjunction ∪
    childStates 1 elseAutomaton
  let accepting := childAccepting 0 conjunction ∪ childAccepting 1 elseAutomaton
  let skipping := childSkipping 0 conjunction ∪ childSkipping 1 elseAutomaton
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
  exact finishAutomatonFragment states .root accepting skipping
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
        edges := ∅ }
  | fuel + 1, processType => by
      classical
      match processType with
      -- skip: Q = {root}, i = root, F = {root}; epsilon self-loops.
      | .skip =>
          let idleEnvironments := signature.localEnvironments.filter fun environment =>
            environment.clock = false ∧ environment.immediate = ∅
          exact finishAutomatonFragment {.root} .root {.root} {.root} <|
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
            (actionEdges ∪ finalEdges)

      -- variable: create a temporary labelled edge for an enclosing binder.
      | .var name =>
          exact finishAutomatonFragment {.root, .final} .root ∅ ∅ <|
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
          let conjunction := compileTypeFuel signature fuel
            (parallelTypeBranches branches)
          exact buildConjunctiveOfferAutomaton
            signature branches elseAutomaton conjunction

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
          change buildConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature (fuel + 1) elseType)
              (compileTypeFuel signature (fuel + 1)
                (parallelTypeBranches branches)) =
            buildConjunctiveOfferAutomaton signature branches
              (compileTypeFuel signature fuel elseType)
              (compileTypeFuel signature fuel (parallelTypeBranches branches))
          have hElse : typeCompilationFuel elseType ≤ fuel := by
            simp [typeCompilationFuel] at hFuel
            omega
          have hConjunction :
              typeCompilationFuel (parallelTypeBranches branches) ≤ fuel := by
            rw [typeCompilationFuel_parallelTypeBranches]
            simp [typeCompilationFuel] at hFuel
            omega
          rw [ih elseType hElse,
            ih (parallelTypeBranches branches) hConjunction]

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
