import Anvilpp.PactTypes.Automata.BuildChoiceAutomaton

/-!
# buildSequenceAutomaton
-/

namespace Pact

noncomputable section

/-!
### Sequential composition by redirecting the collapsed left state

With `seq_fuse`/`par_fuse` installed at the semantic level, a left residual
that steps to `.skip` reaches `right` in the *same* strong step, so the
compiled graph no longer needs a state standing for the intermediate
`skip ; right` residual. Every left accepting state other than the left
fragment's own initial state (accepting ⟺ the represented residual steps to
`.skip` in one hop, uniformly across every constructor — see
`CompilationAcceptingCorrect`) is therefore dropped from the carrier, and
every edge that used to land on one of those states is redirected to land on
`right`'s entry instead, keeping its own label/current. The initial state is
always kept even when it happens to be accepting itself (e.g. `left = .skip`),
matching the semantic administrative rules `skip_seq`/`seq_fuse` staying
available from the very first state.
-/

/-- The left states the sequence construction drops: every accepting state of
`left` other than its own entry.  Accepting means "the represented residual
steps to `.skip` in one hop" (see `CompilationAcceptingCorrect`), so these are
exactly the states whose only old outgoing family was the administrative
bridge into `right`.  The entry is always kept even when accepting itself
(e.g. `left = .skip`), matching `skip_seq`/`seq_fuse` staying available from
the very first state. -/
def sequenceDeleted (left : AutomatonFragment) : Finset TypeAutomatonState :=
  left.accepting \ {left.initial}

theorem mem_sequenceDeleted_iff {left : AutomatonFragment}
    {state : TypeAutomatonState} :
    state ∈ sequenceDeleted left ↔
      state ∈ left.accepting ∧ state ≠ left.initial := by
  simp [sequenceDeleted]

/-- The left entry survives the deletion even when it is itself accepting. -/
@[simp] theorem initial_not_mem_sequenceDeleted (left : AutomatonFragment) :
    left.initial ∉ sequenceDeleted left := by
  simp [sequenceDeleted]

theorem not_mem_sequenceDeleted_of_not_accepting {left : AutomatonFragment}
    {state : TypeAutomatonState} (hNotAccepting : state ∉ left.accepting) :
    state ∉ sequenceDeleted left := fun hDeleted =>
  hNotAccepting (mem_sequenceDeleted_iff.mp hDeleted).1

theorem accepting_of_mem_sequenceDeleted {left : AutomatonFragment}
    {state : TypeAutomatonState} (hDeleted : state ∈ sequenceDeleted left) :
    state ∈ left.accepting := (mem_sequenceDeleted_iff.mp hDeleted).1

/-- Where a left-child state lands in the sequence carrier: dropped states are
redirected onto `right`'s entry, every other state keeps its `0`-tag. -/
def sequenceRedirect (left right : AutomatonFragment)
    (state : TypeAutomatonState) : TypeAutomatonState :=
  if state ∈ sequenceDeleted left then childState 1 right.initial
  else childState 0 state

/-- A left-child edge as it appears in the sequence.  Note what is *not*
touched: `environment`, `label` and `current` are copied verbatim, and the
source only gains its `0`-tag.  Only the target — and the state named inside a
`.future` spec — are rewritten, and both by the same `sequenceRedirect`. -/
def sequenceLeftEdge (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) : PendingAutomatonEdge :=
  { source := childState 0 edge.source
    environment := edge.environment
    label := edge.label
    current := edge.current
    future := match edge.label with
      | .future =>
          match edge.future with
          | .explicit offers => .explicit offers
          | .at childTarget removed =>
              .at (sequenceRedirect left right childTarget) removed
      | _ => .at (sequenceRedirect left right edge.target) edge.current
    target := sequenceRedirect left right edge.target }

/-- The one edge family the redirect alone cannot produce: `skip_seq`'s own
step, `TypeTransition env (.seq .skip right) silent right`, unconditional on
`env` (unlike `.skip`'s self-loop, which needs an idle environment).  This
only arises when `left`'s own entry is already accepting — provably only
`left = .skip` itself, since every other constructor keeps its entry and its
accepting states on structurally disjoint tags — so redirecting `left`'s
in-edges (which `left = .skip` has none of beyond its own idle self-loops)
never reaches this transition.  One edge per local environment, matching
`skip_seq`'s guard exactly. -/
def sequenceEntryBridgeEdges (signature : TypeAlphabet)
    (left right : AutomatonFragment) : Finset PendingAutomatonEdge :=
  if left.initial ∈ left.accepting then
    signature.localEnvironments.image fun environment =>
      { source := childState 0 left.initial
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 1 right.initial) ∅
        target := childState 1 right.initial }
  else ∅

/-- The other edge family the redirect alone cannot produce.  `completing` is
pure analysis metadata, not the source of any semantic transition (see
`AutomatonFragment.completing`'s doc comment), so a state marked completing
has no edge for the redirect to rewrite on that basis alone.  `accepting` is
joined in too: redirect only rewrites a state's *in*-edges (via whatever
target they name), so an accepting state's own route into `right` for
`computeFuture` purposes depends on that state happening to carry a
self-referencing edge of its own — true for every atomic constructor's
`.skip`-shaped accepting state and preserved through verbatim-tagging
combinators, but not cheaply provable in general for the synchronized
product `.par` builds. Rather than lean on that structural fact, every
`left.accepting ∪ left.completing` state gets one bookkeeping-only `.future`
edge into `right`'s entry, independent of environment — `.future`-labeled
edges are never exported as real semantic steps, only consulted by
`computeFuture`'s closure — mirroring the pre-redirect `bridgeEdges`/
`futureBridgeEdges` pair exactly. -/
def sequenceCompletingBridgeEdges (left right : AutomatonFragment) :
    Finset PendingAutomatonEdge :=
  (left.accepting ∪ left.completing).image fun state =>
    { source := childState 0 state
      environment := .empty
      label := .future
      current := ∅
      future := .at (childState 1 right.initial) ∅
      target := childState 1 right.initial }

def buildSequenceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) : AutomatonFragment :=
  let states := (left.states \ sequenceDeleted left).image (childState 0) ∪
    (((left.edges.image fun edge => edge.target) \ sequenceDeleted left).image
      (childState 0)) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  let completing :=
    (if right.initial ∈ right.completing then childCompleting 0 left else ∅) ∪
      childCompleting 1 right
  finishAutomatonFragment states (childState 0 left.initial) accepting
    completing
    (left.edges.image (sequenceLeftEdge left right) ∪
      childPendingEdges 1 right ∪ sequenceEntryBridgeEdges signature left
        right ∪ sequenceCompletingBridgeEdges left right)

/-! ### `sequenceRedirect` / `sequenceLeftEdge` API

The two rewrite lemmas below let downstream proofs avoid ever unfolding the
`if`, and the field lemmas record Invariant 1 (the redirect touches only
targets) so that any property depending solely on
`environment`/`label`/`current` transfers verbatim from the left child. -/

@[simp] theorem sequenceRedirect_of_mem {left right : AutomatonFragment}
    {state : TypeAutomatonState} (hDeleted : state ∈ sequenceDeleted left) :
    sequenceRedirect left right state = childState 1 right.initial := by
  simp [sequenceRedirect, hDeleted]

@[simp] theorem sequenceRedirect_of_not_mem {left right : AutomatonFragment}
    {state : TypeAutomatonState} (hKept : state ∉ sequenceDeleted left) :
    sequenceRedirect left right state = childState 0 state := by
  simp [sequenceRedirect, hKept]

theorem sequenceRedirect_eq_or (left right : AutomatonFragment)
    (state : TypeAutomatonState) :
    sequenceRedirect left right state = childState 1 right.initial ∨
      sequenceRedirect left right state = childState 0 state := by
  by_cases hDeleted : state ∈ sequenceDeleted left
  · exact Or.inl (sequenceRedirect_of_mem hDeleted)
  · exact Or.inr (sequenceRedirect_of_not_mem hDeleted)

@[simp] theorem sequenceLeftEdge_source (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).source = childState 0 edge.source := rfl

@[simp] theorem sequenceLeftEdge_environment (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).environment = edge.environment := rfl

@[simp] theorem sequenceLeftEdge_label (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).label = edge.label := rfl

@[simp] theorem sequenceLeftEdge_current (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).current = edge.current := rfl

@[simp] theorem sequenceLeftEdge_target (left right : AutomatonFragment)
    (edge : PendingAutomatonEdge) :
    (sequenceLeftEdge left right edge).target =
      sequenceRedirect left right edge.target := rfl

/-- Invariant 2, in the form every reachability lemma needs: a redirected
state is always a state of the sequence fragment, provided the original was a
left state or a left edge target. -/
theorem sequenceRedirect_mem_states (signature : TypeAlphabet)
    (left right : AutomatonFragment)
    (hRightInitial : right.initial ∈ right.states)
    (state : TypeAutomatonState)
    (hState : state ∈ left.states ∨
      state ∈ left.edges.image (fun edge => edge.target)) :
    sequenceRedirect left right state ∈
      (buildSequenceAutomaton signature left right).states := by
  classical
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    Finset.mem_union, Finset.mem_image, childStates, childState,
    sequenceRedirect]
  by_cases hDeleted : state ∈ sequenceDeleted left
  · rw [if_pos hDeleted]
    exact Or.inr ⟨right.initial, hRightInitial, rfl⟩
  · rw [if_neg hDeleted]
    rcases hState with hStates | hEdges
    · exact Or.inl (Or.inl ⟨state, Finset.mem_sdiff.mpr ⟨hStates, hDeleted⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨state, Finset.mem_sdiff.mpr ⟨hEdges, hDeleted⟩, rfl⟩)

theorem buildSequenceAutomaton_futureTargetsInStates
    (signature : TypeAlphabet) (left right : AutomatonFragment)
    (hLeftTargets : left.FutureTargetsInStates)
    (hRightTargets : right.FutureTargetsInStates)
    (hRightInitial : right.initial ∈ right.states) :
    (buildSequenceAutomaton signature left right).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSequenceAutomaton, finishAutomatonFragment,
    childPendingEdges, Finset.mem_union, Finset.mem_image] at hEdge
  rcases hEdge with ((hLeft | hRight) | hEntryBridge) | hCompletingBridge
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    have hRedirectMem := sequenceRedirect_mem_states signature left right
      hRightInitial
    cases hLabel : leftEdge.label with
    | future =>
        cases hSpec : leftEdge.future with
        | explicit offers =>
            simp [sequenceLeftEdge, hLabel, hSpec] at hFuture
        | «at» childTarget childRemoved =>
            simp only [sequenceLeftEdge, hLabel, hSpec] at hFuture
            cases hFuture
            have hChildTarget := hLeftTargets leftEdge hLeftEdge
              childTarget removed hSpec
            exact hRedirectMem childTarget (Or.inl hChildTarget)
    | visible label =>
        simp only [sequenceLeftEdge, hLabel] at hFuture
        cases hFuture
        exact hRedirectMem leftEdge.target
          (Or.inr (Finset.mem_image_of_mem _ hLeftEdge))
    | «variable» name =>
        simp only [sequenceLeftEdge, hLabel] at hFuture
        cases hFuture
        exact hRedirectMem leftEdge.target
          (Or.inr (Finset.mem_image_of_mem _ hLeftEdge))
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
  · simp only [sequenceEntryBridgeEdges] at hEntryBridge
    split at hEntryBridge
    · simp only [Finset.mem_image] at hEntryBridge
      obtain ⟨environment, _, rfl⟩ := hEntryBridge
      simp only at hFuture
      cases hFuture
      simp only [buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, childStates, childState]
      exact Or.inr ⟨right.initial, hRightInitial, rfl⟩
    · simp at hEntryBridge
  · simp only [sequenceCompletingBridgeEdges, Finset.mem_image]
      at hCompletingBridge
    obtain ⟨state, _, rfl⟩ := hCompletingBridge
    simp only at hFuture
    cases hFuture
    simp only [buildSequenceAutomaton, finishAutomatonFragment,
      Finset.mem_union, Finset.mem_image, childStates, childState]
    exact Or.inr ⟨right.initial, hRightInitial, rfl⟩

end

end Pact
