import Anvilpp.PactTypes.Automata.MarkerReachability

/-!
# buildRecursionAutomaton and its future/marker correspondence lemmas
-/

namespace Pact

noncomputable section

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
  finishAutomatonFragment states .root accepting
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

end

end Pact
