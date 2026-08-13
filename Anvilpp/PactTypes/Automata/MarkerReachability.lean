import Anvilpp.PactTypes.Automata.PendingAutomatonFuture

/-!
# Marker-augmented future resolution and same-cycle marker reachability
-/

namespace Pact

noncomputable section

/-- Forget fragment metadata and retain the pending graph. -/
def AutomatonFragment.toPending (fragment : AutomatonFragment) :
    PendingAutomaton :=
  { states := fragment.states, edges := fragment.edges }

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

/-- Stop unresolved calls of one name without changing the carrier or any
other edge.  This is useful when an execution view has followed a temporary
variable edge to its bookkeeping target, while an enclosing recursion
constructor is about to replace that edge by a backedge. -/
def markerStoppedFragment (fragment : AutomatonFragment) (name : String) :
    AutomatonFragment :=
  { states := fragment.states
    initial := fragment.initial
    accepting := fragment.accepting
    skipping := fragment.skipping
    completing := fragment.completing
    edges := fragment.edges.image fun edge =>
      if edge.label = AutomatonConstructionLabel.variable name then
        { edge with current := ∅, future := .explicit ∅ }
      else edge }

theorem markerStoppedFragment_markerEdgesInert
    (fragment : AutomatonFragment) (name : String) :
    MarkerEdgesInert (markerStoppedFragment fragment name) name := by
  classical
  intro edge hEdge hLabel
  simp only [markerStoppedFragment, Finset.mem_image] at hEdge
  rcases hEdge with ⟨original, hOriginal, rfl⟩
  by_cases hMarker : original.label =
      AutomatonConstructionLabel.variable name
  · simp [hMarker]
  · simp [hMarker] at hLabel

theorem markerStoppedFragment_futureTargetsInStates
    (fragment : AutomatonFragment) (name : String)
    (hTargets : fragment.FutureTargetsInStates) :
    (markerStoppedFragment fragment name).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [markerStoppedFragment, Finset.mem_image] at hEdge
  rcases hEdge with ⟨original, hOriginal, rfl⟩
  by_cases hMarker : original.label =
      AutomatonConstructionLabel.variable name
  · simp [hMarker] at hFuture
  · simp only [if_neg hMarker] at hFuture
    exact hTargets original hOriginal target removed hFuture

theorem markerStoppedFragment_markerSource
    (fragment : AutomatonFragment) (stopped query : String)
    (state : TypeAutomatonState) :
    MarkerSource (markerStoppedFragment fragment stopped) query state ↔
      MarkerSource fragment query state := by
  classical
  constructor
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    simp only [markerStoppedFragment, Finset.mem_image] at hEdge
    rcases hEdge with ⟨original, hOriginal, rfl⟩
    refine ⟨original, hOriginal, ?_, ?_⟩
    · split at hSource <;> simpa using hSource
    · split at hLabel <;> simpa using hLabel
  · rintro ⟨edge, hEdge, hSource, hLabel⟩
    refine ⟨if edge.label = AutomatonConstructionLabel.variable stopped then
        { edge with current := ∅, future := .explicit ∅ }
      else edge, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨edge, hEdge, rfl⟩
    · split <;> simpa using hSource
    · split <;> simpa using hLabel

theorem markerStoppedFragment_referencedStates_subset
    (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState) :
    (markerStoppedFragment fragment name : AutomatonFragment).toPending.referencedStates
        state ⊆
      (fragment : AutomatonFragment).toPending.referencedStates state := by
  classical
  intro target hTarget
  simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
    markerStoppedFragment, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image] at hTarget ⊢
  rcases hTarget with
    ⟨edge, ⟨⟨original, hOriginal, hEdge⟩, hSource⟩, hReference⟩
  rw [← hEdge] at hSource hReference
  by_cases hMarker : original.label =
      AutomatonConstructionLabel.variable name
  · simp [hMarker] at hReference
  · simp only [if_neg hMarker] at hSource hReference
    exact ⟨original, ⟨hOriginal, hSource⟩, hReference⟩

theorem markerStoppedFragment_referencedStates_eq_of_not_markerSource
    (fragment : AutomatonFragment) (name : String)
    (state : TypeAutomatonState)
    (hNoMarker : ¬ MarkerSource fragment name state) :
    (markerStoppedFragment fragment name).toPending.referencedStates state =
      fragment.toPending.referencedStates state := by
  classical
  apply Finset.Subset.antisymm
  · exact markerStoppedFragment_referencedStates_subset fragment name state
  · intro target hTarget
    simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
      Finset.mem_biUnion, Finset.mem_filter] at hTarget
    rcases hTarget with ⟨edge, ⟨hEdge, hSource⟩, hReference⟩
    have hNotMarker : edge.label ≠
        AutomatonConstructionLabel.variable name := by
      intro hLabel
      exact hNoMarker ⟨edge, hEdge, hSource, hLabel⟩
    simp only [PendingAutomaton.referencedStates, AutomatonFragment.toPending,
      markerStoppedFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image]
    exact ⟨edge, ⟨⟨edge, hEdge, by simp [hNotMarker]⟩,
      by simp [hNotMarker, hSource]⟩, by simpa [hNotMarker] using hReference⟩

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

/-- Removing the temporary execution reference leaving a marker cannot alter
whether that same marker is reachable.  If a path first tries to use a removed
reference, its source is already the required marker witness. -/
theorem markerStoppedFragment_markerReachable_self
    (fragment : AutomatonFragment) (name : String)
    (hClosed : fragment.toPending.ReferencesClosed)
    (state : TypeAutomatonState) (hState : state ∈ fragment.states) :
    MarkerReachable (markerStoppedFragment fragment name) name state ↔
      MarkerReachable fragment name state := by
  classical
  let stopped := markerStoppedFragment fragment name
  have hStoppedClosed : stopped.toPending.ReferencesClosed := by
    intro source hSource target hReference
    exact hClosed source (by simpa [stopped, markerStoppedFragment] using hSource)
      (markerStoppedFragment_referencedStates_subset fragment name source
        hReference)
  have hStoppedState : state ∈ stopped.states := by
    simpa [stopped, markerStoppedFragment] using hState
  have hSources : ∀ q,
      MarkerSource stopped name q ↔ MarkerSource fragment name q :=
    markerStoppedFragment_markerSource fragment name name
  constructor
  · rintro ⟨reached, hReached, hMarker⟩
    let allowed := fragment.toPending.futureReachable state
    have hInitial : state ∈ allowed :=
      fragment.toPending.mem_futureReachable_self state
    have hAllowedClosed : ∀ source ∈ allowed,
        stopped.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      have hSourceInStates :=
        fragment.toPending.futureReachable_subset_of_reference_closed state
          fragment.states hState hClosed hSource
      exact (fragment.toPending.futureReachable_subset_of_mem hClosed hState
        hSource)
        (fragment.toPending.referencedStates_subset_futureReachable source
          hClosed hSourceInStates
          (markerStoppedFragment_referencedStates_subset fragment name source
            hReference))
    have hSubset := stopped.toPending.futureReachable_subset_of_reference_closed
      state allowed hInitial hAllowedClosed hReached
    exact ⟨reached, hSubset, (hSources reached).mp hMarker⟩
  · intro hOriginal
    by_contra hStopped
    let allowed := stopped.toPending.futureReachable state
    have hInitial : state ∈ allowed :=
      stopped.toPending.mem_futureReachable_self state
    have hAllowedClosed : ∀ source ∈ allowed,
        fragment.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      have hNoSource : ¬ MarkerSource fragment name source := by
        intro hMarker
        exact hStopped ⟨source, hSource, (hSources source).mpr hMarker⟩
      rw [← markerStoppedFragment_referencedStates_eq_of_not_markerSource
        fragment name source hNoSource] at hReference
      have hSourceInStates :=
        stopped.toPending.futureReachable_subset_of_reference_closed state
          stopped.states hStoppedState hStoppedClosed hSource
      exact (stopped.toPending.futureReachable_subset_of_mem hStoppedClosed
        hStoppedState hSource)
        (stopped.toPending.referencedStates_subset_futureReachable source
          hStoppedClosed hSourceInStates hReference)
    rcases hOriginal with ⟨reached, hReached, hMarker⟩
    have hSubset := fragment.toPending.futureReachable_subset_of_reference_closed
      state allowed hInitial hAllowedClosed hReached
    exact hStopped ⟨reached, hSubset, (hSources reached).mpr hMarker⟩

/-- Stopping one marker also preserves reachability of every other marker when
the removed references point to sink bookkeeping states. -/
theorem markerStoppedFragment_markerReachable_of_target_sinks
    (fragment : AutomatonFragment) (stoppedName query : String)
    (hClosed : fragment.toPending.ReferencesClosed)
    (hReferencesTarget : ∀ marker ∈ fragment.edges,
      marker.label = AutomatonConstructionLabel.variable stoppedName →
      ∀ target removed, marker.future = .at target removed →
        target = marker.target)
    (hSinks : ∀ marker ∈ fragment.edges,
      marker.label = AutomatonConstructionLabel.variable stoppedName →
      ∀ edge ∈ fragment.edges, edge.source ≠ marker.target)
    (state : TypeAutomatonState) (hState : state ∈ fragment.states) :
    MarkerReachable (markerStoppedFragment fragment stoppedName) query state ↔
      MarkerReachable fragment query state := by
  classical
  let stopped := markerStoppedFragment fragment stoppedName
  let sinkTargets := (fragment.edges.filter fun edge =>
    edge.label = AutomatonConstructionLabel.variable stoppedName).image
      PendingAutomatonEdge.target
  have hStoppedClosed : stopped.toPending.ReferencesClosed := by
    intro source hSource target hReference
    exact hClosed source (by simpa [stopped, markerStoppedFragment] using hSource)
      (markerStoppedFragment_referencedStates_subset fragment stoppedName source
        hReference)
  have hStoppedState : state ∈ stopped.states := by
    simpa [stopped, markerStoppedFragment] using hState
  have hSources : ∀ q,
      MarkerSource stopped query q ↔ MarkerSource fragment query q :=
    markerStoppedFragment_markerSource fragment stoppedName query
  constructor
  · rintro ⟨reached, hReached, hMarker⟩
    let allowed := fragment.toPending.futureReachable state
    have hInitial : state ∈ allowed :=
      fragment.toPending.mem_futureReachable_self state
    have hAllowedClosed : ∀ source ∈ allowed,
        stopped.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      have hSourceInStates :=
        fragment.toPending.futureReachable_subset_of_reference_closed state
          fragment.states hState hClosed hSource
      exact (fragment.toPending.futureReachable_subset_of_mem hClosed hState
        hSource)
        (fragment.toPending.referencedStates_subset_futureReachable source
          hClosed hSourceInStates
          (markerStoppedFragment_referencedStates_subset fragment stoppedName
            source hReference))
    have hSubset := stopped.toPending.futureReachable_subset_of_reference_closed
      state allowed hInitial hAllowedClosed hReached
    exact ⟨reached, hSubset, (hSources reached).mp hMarker⟩
  · rintro ⟨reached, hReached, hMarker⟩
    let allowed := stopped.toPending.futureReachable state ∪ sinkTargets
    have hInitial : state ∈ allowed := Finset.mem_union_left _
      (stopped.toPending.mem_futureReachable_self state)
    have hAllowedClosed : ∀ source ∈ allowed,
        fragment.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      rcases Finset.mem_union.mp hSource with hStoppedReach | hSink
      · simp only [PendingAutomaton.referencedStates,
          AutomatonFragment.toPending, Finset.mem_biUnion,
          Finset.mem_filter] at hReference
        rcases hReference with
          ⟨referenceEdge, ⟨hReferenceEdge, hReferenceSource⟩,
            hReferenceTarget⟩
        by_cases hMarkerEdge : referenceEdge.label =
            AutomatonConstructionLabel.variable stoppedName
        · apply Finset.mem_union_right
          by_cases hClock : referenceEdge.label.semantic = TypeLabel.tock
          · simp [hClock] at hReferenceTarget
          · simp only [hClock, if_false] at hReferenceTarget
            cases hFuture : referenceEdge.future with
            | explicit offers => simp [hFuture] at hReferenceTarget
            | «at» referenced removed =>
                have hTarget : target = referenced := by
                  simpa [hFuture] using hReferenceTarget
                subst target
                rw [hReferencesTarget referenceEdge hReferenceEdge hMarkerEdge
                  referenced removed hFuture]
                exact Finset.mem_image.mpr ⟨referenceEdge,
                  Finset.mem_filter.mpr ⟨hReferenceEdge, hMarkerEdge⟩, rfl⟩
        · apply Finset.mem_union_left
          have hStoppedReference : target ∈
              stopped.toPending.referencedStates source := by
            simp only [PendingAutomaton.referencedStates,
              AutomatonFragment.toPending, stopped, markerStoppedFragment,
              Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
            exact ⟨referenceEdge,
              ⟨⟨referenceEdge, hReferenceEdge, by simp [hMarkerEdge]⟩,
                by simp [hMarkerEdge, hReferenceSource]⟩,
              by simpa [hMarkerEdge] using hReferenceTarget⟩
          have hSourceInStates :=
            stopped.toPending.futureReachable_subset_of_reference_closed state
              stopped.states hStoppedState hStoppedClosed hStoppedReach
          exact (stopped.toPending.futureReachable_subset_of_mem hStoppedClosed
            hStoppedState hStoppedReach)
            (stopped.toPending.referencedStates_subset_futureReachable source
              hStoppedClosed hSourceInStates hStoppedReference)
      · rcases Finset.mem_image.mp hSink with
          ⟨marker, hMarkerFiltered, hMarkerTarget⟩
        have hMarkerFields := Finset.mem_filter.mp hMarkerFiltered
        simp only [PendingAutomaton.referencedStates,
          AutomatonFragment.toPending, Finset.mem_biUnion,
          Finset.mem_filter] at hReference
        rcases hReference with
          ⟨referenceEdge, ⟨hReferenceEdge, hReferenceSource⟩, _⟩
        exfalso
        apply hSinks marker hMarkerFields.1 hMarkerFields.2 referenceEdge
          hReferenceEdge
        exact hReferenceSource.trans hMarkerTarget.symm
    have hReachedAllowed :=
      fragment.toPending.futureReachable_subset_of_reference_closed state
        allowed hInitial hAllowedClosed hReached
    rcases Finset.mem_union.mp hReachedAllowed with hStoppedReach | hSink
    · exact ⟨reached, hStoppedReach, (hSources reached).mpr hMarker⟩
    · rcases Finset.mem_image.mp hSink with
        ⟨marker, hMarkerFiltered, hMarkerTarget⟩
      have hMarkerFields := Finset.mem_filter.mp hMarkerFiltered
      rcases hMarker with ⟨edge, hEdge, hEdgeSource, _⟩
      exfalso
      apply hSinks marker hMarkerFields.1 hMarkerFields.2 edge hEdge
      exact hEdgeSource.trans hMarkerTarget.symm

/-- Stopping marker references to sink bookkeeping states also preserves the
computed offer menu.  The matching marker edge itself contributes no offers;
the only states removed from the reference closure are its offerless sinks. -/
theorem markerStoppedFragment_computeFuture_of_target_sinks
    (fragment : AutomatonFragment) (name : String)
    (hClosed : fragment.toPending.ReferencesClosed)
    (hMarkerShape : ∀ marker ∈ fragment.edges,
      marker.label = AutomatonConstructionLabel.variable name →
        marker.current = ∅ ∧ marker.future = .at marker.target ∅)
    (hSinks : ∀ marker ∈ fragment.edges,
      marker.label = AutomatonConstructionLabel.variable name →
      ∀ edge ∈ fragment.edges, edge.source ≠ marker.target)
    (state : TypeAutomatonState) (hState : state ∈ fragment.states) :
    computeFuture (markerStoppedFragment fragment name).toPending state =
      computeFuture fragment.toPending state := by
  classical
  let stopped := markerStoppedFragment fragment name
  let sinkTargets := (fragment.edges.filter fun edge =>
    edge.label = AutomatonConstructionLabel.variable name).image
      PendingAutomatonEdge.target
  have hStoppedClosed : stopped.toPending.ReferencesClosed := by
    intro source hSource target hReference
    exact hClosed source (by simpa [stopped, markerStoppedFragment] using hSource)
      (markerStoppedFragment_referencedStates_subset fragment name source
        hReference)
  have hStoppedState : state ∈ stopped.states := by
    simpa [stopped, markerStoppedFragment] using hState
  have hOffers : ∀ source,
      stopped.toPending.offersAt source = fragment.toPending.offersAt source := by
    intro source
    ext action
    simp only [PendingAutomaton.offersAt, AutomatonFragment.toPending,
      stopped, markerStoppedFragment, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_image]
    constructor
    · rintro ⟨edge, ⟨⟨original, hOriginal, hEdge⟩, hSource⟩, hAction⟩
      rw [← hEdge] at hSource hAction
      by_cases hMarker : original.label =
          AutomatonConstructionLabel.variable name
      · have hShape := hMarkerShape original hOriginal hMarker
        simp [hMarker, hShape.1] at hAction
      · exact ⟨original, ⟨hOriginal, by simpa [hMarker] using hSource⟩,
          by simpa [hMarker] using hAction⟩
    · rintro ⟨original, ⟨hOriginal, hSource⟩, hAction⟩
      by_cases hMarker : original.label =
          AutomatonConstructionLabel.variable name
      · have hShape := hMarkerShape original hOriginal hMarker
        rw [hMarker, hShape.1, hShape.2] at hAction
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hAction
      · refine ⟨original, ⟨⟨original, hOriginal, by simp [hMarker]⟩, ?_⟩, ?_⟩
        · simpa [hMarker] using hSource
        · simpa [hMarker] using hAction
  have hStoppedSubset : stopped.toPending.futureReachable state ⊆
      fragment.toPending.futureReachable state := by
    let allowed := fragment.toPending.futureReachable state
    have hInitial : state ∈ allowed :=
      fragment.toPending.mem_futureReachable_self state
    have hAllowedClosed : ∀ source ∈ allowed,
        stopped.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      have hSourceInStates :=
        fragment.toPending.futureReachable_subset_of_reference_closed state
          fragment.states hState hClosed hSource
      exact (fragment.toPending.futureReachable_subset_of_mem hClosed hState
        hSource)
        (fragment.toPending.referencedStates_subset_futureReachable source
          hClosed hSourceInStates
          (markerStoppedFragment_referencedStates_subset fragment name source
            hReference))
    exact stopped.toPending.futureReachable_subset_of_reference_closed state
      allowed hInitial hAllowedClosed
  have hOriginalSubset : fragment.toPending.futureReachable state ⊆
      stopped.toPending.futureReachable state ∪ sinkTargets := by
    let allowed := stopped.toPending.futureReachable state ∪ sinkTargets
    have hInitial : state ∈ allowed := Finset.mem_union_left _
      (stopped.toPending.mem_futureReachable_self state)
    have hAllowedClosed : ∀ source ∈ allowed,
        fragment.toPending.referencedStates source ⊆ allowed := by
      intro source hSource target hReference
      rcases Finset.mem_union.mp hSource with hStoppedReach | hSink
      · simp only [PendingAutomaton.referencedStates,
          AutomatonFragment.toPending, Finset.mem_biUnion,
          Finset.mem_filter] at hReference
        rcases hReference with
          ⟨referenceEdge, ⟨hReferenceEdge, hReferenceSource⟩,
            hReferenceTarget⟩
        by_cases hMarkerEdge : referenceEdge.label =
            AutomatonConstructionLabel.variable name
        · apply Finset.mem_union_right
          have hShape := hMarkerShape referenceEdge hReferenceEdge hMarkerEdge
          have hTarget : target = referenceEdge.target := by
            simpa [hMarkerEdge, hShape.2,
              AutomatonConstructionLabel.semantic, TypeLabel.silent] using
                hReferenceTarget
          subst target
          exact Finset.mem_image.mpr ⟨referenceEdge,
            Finset.mem_filter.mpr ⟨hReferenceEdge, hMarkerEdge⟩, rfl⟩
        · apply Finset.mem_union_left
          have hStoppedReference : target ∈
              stopped.toPending.referencedStates source := by
            simp only [PendingAutomaton.referencedStates,
              AutomatonFragment.toPending, stopped, markerStoppedFragment,
              Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
            exact ⟨referenceEdge,
              ⟨⟨referenceEdge, hReferenceEdge, by simp [hMarkerEdge]⟩,
                by simp [hMarkerEdge, hReferenceSource]⟩,
              by simpa [hMarkerEdge] using hReferenceTarget⟩
          have hSourceInStates :=
            stopped.toPending.futureReachable_subset_of_reference_closed state
              stopped.states hStoppedState hStoppedClosed hStoppedReach
          exact (stopped.toPending.futureReachable_subset_of_mem hStoppedClosed
            hStoppedState hStoppedReach)
            (stopped.toPending.referencedStates_subset_futureReachable source
              hStoppedClosed hSourceInStates hStoppedReference)
      · rcases Finset.mem_image.mp hSink with
          ⟨marker, hMarkerFiltered, hMarkerTarget⟩
        have hMarkerFields := Finset.mem_filter.mp hMarkerFiltered
        simp only [PendingAutomaton.referencedStates,
          AutomatonFragment.toPending, Finset.mem_biUnion,
          Finset.mem_filter] at hReference
        rcases hReference with
          ⟨referenceEdge, ⟨hReferenceEdge, hReferenceSource⟩, _⟩
        exfalso
        apply hSinks marker hMarkerFields.1 hMarkerFields.2 referenceEdge
          hReferenceEdge
        exact hReferenceSource.trans hMarkerTarget.symm
    exact fragment.toPending.futureReachable_subset_of_reference_closed state
      allowed hInitial hAllowedClosed
  ext action
  simp only [computeFuture, Finset.mem_biUnion]
  constructor
  · rintro ⟨reached, hReached, hAction⟩
    refine ⟨reached, hStoppedSubset hReached, ?_⟩
    rw [hOffers reached] at hAction
    exact hAction
  · rintro ⟨reached, hReached, hAction⟩
    rcases Finset.mem_union.mp (hOriginalSubset hReached) with
        hStoppedReach | hSink
    · refine ⟨reached, hStoppedReach, ?_⟩
      rw [hOffers reached]
      exact hAction
    · rcases Finset.mem_image.mp hSink with
        ⟨marker, hMarkerFiltered, hMarkerTarget⟩
      have hMarkerFields := Finset.mem_filter.mp hMarkerFiltered
      simp only [PendingAutomaton.offersAt, AutomatonFragment.toPending,
        Finset.mem_biUnion, Finset.mem_filter] at hAction
      rcases hAction with ⟨edge, ⟨hEdge, hSource⟩, _⟩
      exfalso
      apply hSinks marker hMarkerFields.1 hMarkerFields.2 edge hEdge
      exact hSource.trans hMarkerTarget.symm

/-- Marker reachability depends only on a closed graph's edge set; additional
bookkeeping states merely add redundant saturation rounds. -/
theorem markerReachable_iff_of_same_edges
    (first second : AutomatonFragment) (name : String)
    (hEdges : first.edges = second.edges)
    (hFirstClosed : first.toPending.ReferencesClosed)
    (hSecondClosed : second.toPending.ReferencesClosed)
    (state : TypeAutomatonState)
    (hFirstState : state ∈ first.states)
    (hSecondState : state ∈ second.states) :
    MarkerReachable first name state ↔ MarkerReachable second name state := by
  have hReach := PendingAutomaton.futureReachable_eq_of_same_edges
    first.toPending second.toPending hEdges hFirstClosed hSecondClosed state
      hFirstState hSecondState
  have hSource : ∀ q,
      MarkerSource first name q ↔ MarkerSource second name q := by
    intro q
    simp only [MarkerSource]
    rw [hEdges]
  simp only [MarkerReachable]
  change (∃ reached ∈ first.toPending.futureReachable state,
      MarkerSource first name reached) ↔
    ∃ reached ∈ second.toPending.futureReachable state,
      MarkerSource second name reached
  rw [hReach]
  constructor
  · rintro ⟨reached, hReached, hMarker⟩
    exact ⟨reached, hReached, (hSource reached).mp hMarker⟩
  · rintro ⟨reached, hReached, hMarker⟩
    exact ⟨reached, hReached, (hSource reached).mpr hMarker⟩

/-- Marker reachability propagates backwards across one same-cycle
reference. -/
theorem markerReachable_of_referencedState
    (fragment : AutomatonFragment) (name : String)
    (hClosed : fragment.toPending.ReferencesClosed)
    {source target : TypeAutomatonState}
    (hSource : source ∈ fragment.states)
    (hReference : target ∈ fragment.toPending.referencedStates source)
    (hTarget : MarkerReachable fragment name target) :
    MarkerReachable fragment name source := by
  rcases hTarget with ⟨reached, hReached, hMarker⟩
  have hTargetReached : target ∈ fragment.toPending.futureReachable source :=
    fragment.toPending.referencedStates_subset_futureReachable source hClosed
      hSource hReference
  exact ⟨reached,
    fragment.toPending.futureReachable_subset_of_mem hClosed hSource
      hTargetReached hReached,
    hMarker⟩

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

def childAccepting (index : Nat) (automaton : AutomatonFragment) :
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

end

end Pact
