import Anvilpp.PactTypes.Automata.BuildChoiceAutomaton

/-!
# buildSequenceAutomaton
-/

namespace Pact

noncomputable section

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

end

end Pact
