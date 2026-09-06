import Anvilpp.PactTypes.Spec.Automata.BuildRecursionAutomatonDefs

namespace Pact

noncomputable section

/-- Installing backedges does not change the offers directly visible at a
tagged body state.  A matching marker contributes nothing before installation
(it is inert) and nothing after installation either, because the backedge it
becomes carries empty `current` and a symbolic `.at` future; every other body
edge keeps its `current`, and `childFutureSpec` preserves `.explicit`
payloads while sending `.at` to `.at`.  Header edges leave from `.root`, which
is never a tagged state. -/
theorem buildRecursionAutomaton_offersAt_child
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment)
    (hInert : body.MarkerOffersInert name)
    (q : TypeAutomatonState) :
    (⟨(buildRecursionAutomaton alphabet name body).states,
        (buildRecursionAutomaton alphabet name body).edges⟩ :
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
      obtain ⟨hCurrent, hFuture⟩ := hInert edge hEdge hMarker
      have hSem : ¬ (AutomatonConstructionLabel.variable name).semantic =
          TypeLabel.tock := by
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
      rw [hMarker] at hAction
      rw [if_neg hSem, hCurrent, Finset.empty_union] at hAction
      cases hSpec : edge.future with
      | explicit offers =>
          rw [hSpec, hFuture offers hSpec] at hAction
          simp at hAction
      | «at» target removed =>
          rw [hSpec] at hAction
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
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment)
    (q target : TypeAutomatonState) :
    target ∈ (⟨(buildRecursionAutomaton alphabet name body).states,
        (buildRecursionAutomaton alphabet name body).edges⟩ :
      PendingAutomaton).referencedStates (childState 0 q) ↔
      (∃ inner ∈ (⟨(markerStoppedFragment body name).states,
          (markerStoppedFragment body name).edges⟩ :
          PendingAutomaton).referencedStates q,
        target = childState 0 inner) ∨
        (MarkerSource body name q ∧ target = childState 0 body.initial) := by
  classical
  simp only [PendingAutomaton.referencedStates, Finset.mem_biUnion,
    Finset.mem_filter, buildRecursionAutomaton, markerStoppedFragment,
    finishAutomatonFragment, Finset.mem_union, Finset.mem_image]
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
              refine ⟨inner, ⟨_, ⟨⟨original, hOriginal, rfl⟩, ?_⟩, ?_⟩, ?_⟩
              · rw [if_neg hMarker]; exact hSourceEq
              · rw [if_neg hMarker]
                simp [hSpec, if_neg hTock]
              · simpa using hTarget
  · rintro (⟨inner, ⟨stopped, ⟨⟨original, hOriginal, hStopped⟩, hSourceEq⟩,
        hInner⟩, rfl⟩ |
      ⟨⟨original, hOriginal, hSourceEq, hMarker⟩, rfl⟩)
    -- A stopped marker edge publishes `.explicit ∅`, so it references nothing:
    -- the witness has to be an ordinary body edge, copied unchanged.
    · have hMarker : original.label ≠ AutomatonConstructionLabel.variable name := by
        intro hEq
        rw [← hStopped, if_pos hEq] at hInner
        simp at hInner
      rw [← hStopped, if_neg hMarker] at hSourceEq hInner
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

/-- Installing backedges for `name` leaves markers of any *other* still-open
binder untouched: only `.variable name` edges are rewritten, and the rewrite
produces a `.visible` silent edge, never another marker. -/
theorem buildRecursionAutomaton_markerSource_child
     (alphabet : PactTypeAlphabet)
    (name other : String) (body : AutomatonFragment)
    (hDistinct : other ≠ name) (q : TypeAutomatonState) :
    MarkerSource (buildRecursionAutomaton alphabet name body) other
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
     (alphabet : PactTypeAlphabet)
    (name other : String)
    (body : AutomatonFragment) :
    ¬ MarkerSource (buildRecursionAutomaton alphabet name body) other
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
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment) :
    (⟨(buildRecursionAutomaton alphabet name body).states,
        (buildRecursionAutomaton alphabet name body).edges⟩ :
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
              environment := TypeEnvironment.empty
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState 0 body.initial) ∅
              target := childState 0 body.initial }, ⟨?_, rfl⟩, ?_⟩
    · refine Or.inl ⟨TypeEnvironment.empty, ?_, rfl⟩
      constructor
      · simp only [PactTypeAlphabet.localEnvironments, Finset.mem_union,
          Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_powerset,
          Finset.mem_image]
        exact Or.inr ⟨∅, by simp, ∅, by simp [TypeEnvironment.empty], rfl⟩
      · rfl
    · simpa [AutomatonConstructionLabel.semantic, TypeLabel.silent] using hTarget

/-- Header edges carry an explicit `clock = false` guard, and copied body
edges keep the body's environment and label.

The marker branch is the delicate one: it rewrites the label to a *visible*
`silent`, discarding the body edge's own label.  It is sound only because a
marker edge can never be clocked in the first place — a clocked body edge is
tock-labelled by the body's own invariant, whereas a marker's semantic label
is `silent`.  This is precisely what the `clock = false` guard on the
compiler's `.var` marker edges buys. -/
theorem buildRecursionAutomaton_clockEdgesAreTock
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment)
    (hBodyClock : body.ClockEdgesAreTock) :
    (buildRecursionAutomaton alphabet name body).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildRecursionAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with hHeader | hBody
  · rcases hHeader with ⟨environment, ⟨_, hNotClock⟩, rfl⟩
    exfalso
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)
  · rcases hBody with ⟨bodyEdge, hBodyEdge, rfl⟩
    by_cases hVariable : bodyEdge.label = .variable name
    · -- A marker edge cannot be clocked: the body invariant would force its
      -- semantic label to be `tock`, but a `.variable` marker is `silent`.
      exfalso
      rw [if_pos hVariable] at hClock
      simp only at hClock
      have hTock := (hBodyClock bodyEdge hBodyEdge hClock).1
      rw [hVariable] at hTock
      simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hTock
    · rw [if_neg hVariable] at hClock ⊢
      simp only at hClock ⊢
      exact hBodyClock bodyEdge hBodyEdge hClock

theorem buildRecursionAutomaton_futureTargetsInStates
     (alphabet : PactTypeAlphabet)
    (name : String) (body : AutomatonFragment)
    (hBodyTargets : body.FutureTargetsInStates)
    (hBodyInitial : body.initial ∈ body.states) :
    (buildRecursionAutomaton alphabet name body).FutureTargetsInStates := by
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
