import Anvilpp.PactTypes.Automata.PendingAutomatonFuture

/-!
# Marker-augmented future resolution and same-cycle marker reachability
-/

namespace Pact

noncomputable section

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
