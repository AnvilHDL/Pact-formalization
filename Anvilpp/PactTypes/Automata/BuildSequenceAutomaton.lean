import Anvilpp.PactTypes.Automata.BuildChoiceAutomaton

/-!
# buildSequenceAutomaton
-/

namespace Pact

noncomputable section

/--
Build sequential composition by redirecting the collapsed left state.

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
def buildSequenceAutomaton (signature : TypeAlphabet)
    (left right : AutomatonFragment) : AutomatonFragment :=
  let deletedLeft := left.accepting \ {left.initial}
  let states := (left.states \ deletedLeft).image (childState 0) ∪
    (((left.edges.image fun edge => edge.target) \ deletedLeft).image
      (childState 0)) ∪
    childStates 1 right
  let accepting := childAccepting 1 right
  let completing :=
    (if right.initial ∈ right.completing then childCompleting 0 left else ∅) ∪
      childCompleting 1 right
  let redirect (state : TypeAutomatonState) : TypeAutomatonState :=
    if state ∈ deletedLeft then childState 1 right.initial else childState 0 state
  let leftEdges : Finset PendingAutomatonEdge := left.edges.image fun edge =>
    let target := redirect edge.target
    { source := childState 0 edge.source
      environment := edge.environment
      label := edge.label
      current := edge.current
      future := match edge.label with
        | .future =>
            match edge.future with
            | .explicit offers => .explicit offers
            | .at childTarget removed => .at (redirect childTarget) removed
        | _ => .at target edge.current
      target := target }
  finishAutomatonFragment states (childState 0 left.initial) accepting
    completing
    (leftEdges ∪ childPendingEdges 1 right)

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
  rcases hEdge with hLeft | hRight
  · rcases hLeft with ⟨leftEdge, hLeftEdge, rfl⟩
    have hRedirectMem : ∀ state, state ∈ left.states ∨
        state ∈ left.edges.image (fun edge => edge.target) →
        (if state ∈ left.accepting \ {left.initial} then
            childState 1 right.initial
          else childState 0 state) ∈
          (buildSequenceAutomaton signature left right).states := by
      intro state hState
      simp only [buildSequenceAutomaton, finishAutomatonFragment,
        Finset.mem_union, Finset.mem_image, childStates, childState]
      by_cases hDeleted : state ∈ left.accepting \ {left.initial}
      · rw [if_pos hDeleted]
        exact Or.inr ⟨right.initial, hRightInitial, rfl⟩
      · rw [if_neg hDeleted]
        rcases hState with hStates | hEdges
        · exact Or.inl (Or.inl ⟨state, Finset.mem_sdiff.mpr ⟨hStates, hDeleted⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨state, Finset.mem_sdiff.mpr ⟨hEdges, hDeleted⟩, rfl⟩)
    cases hLabel : leftEdge.label with
    | future =>
        cases hSpec : leftEdge.future with
        | explicit offers =>
            simp [hLabel, hSpec] at hFuture
        | «at» childTarget childRemoved =>
            simp only [hLabel, hSpec] at hFuture
            cases hFuture
            have hChildTarget := hLeftTargets leftEdge hLeftEdge
              childTarget removed hSpec
            exact hRedirectMem childTarget (Or.inl hChildTarget)
    | visible label =>
        simp only [hLabel] at hFuture
        cases hFuture
        exact hRedirectMem leftEdge.target
          (Or.inr (Finset.mem_image_of_mem _ hLeftEdge))
    | «variable» name =>
        simp only [hLabel] at hFuture
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

end

end Pact
