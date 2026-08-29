import Anvilpp.PactTypes.Automata.BuildSequenceAutomaton
import Anvilpp.PactTypes.Automata.SyncEdges

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

/-- Future spec used by redirected parallel product edges.

A synchronized clock edge that redirects to the completed state ends the
current cycle, so its public future offers are empty.  All other product edges
keep the usual symbolic reference to the target product state's global `OF`
equation. -/
def parallelFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if target = .final ∧ label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

/-- The unfiltered synchronized edges of a parallel product. Completing
component pairs are redirected to the dedicated `.final` state. -/
def parallelRawTransitionEdges (signature : TypeAlphabet)
    (leftAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  let allLeftEdges := resolveAutomatonEdgesWith left leftFuture
  let allRightEdges := resolveAutomatonEdgesWith right rightFuture
  exact
    allLeftEdges.biUnion fun leftEdge =>
    (allRightEdges.filter fun rightEdge =>
      syncAutomatonEdges signature leftAlphabet rightAlphabet interface
        leftEdge rightEdge).image fun rightEdge =>
        let bothAccept :=
          leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
        let target : TypeAutomatonState :=
          if bothAccept then .final
          else .pair leftEdge.target rightEdge.target
        let current := hideOffers interface (leftEdge.current ∪ rightEdge.current)
        let label := AutomatonConstructionLabel.combine interface
          leftEdge.label rightEdge.label
        { source := .pair leftEdge.source rightEdge.source
          environment := combineAutomatonEnvironment interface
            leftEdge.environment rightEdge.environment
          label := label
          current := current
          future := parallelFutureSpec label target current
          target := target }

/-- The non-clock idle edges attached to the completed parallel state. -/
def parallelDoneEdges (signature : TypeAlphabet)
    (alphabet : PactTypeAlphabet) : Finset PendingAutomatonEdge := by
  classical
  exact ((signature.localEnvironmentsFor alphabet).filter fun environment =>
    environment.clock = false).image fun environment =>
      { source := TypeAutomatonState.final
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }

/-- One raw graph step used by the paper's `Reach` side condition. -/
def ParallelRawStep (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (source target : TypeAutomatonState) : Prop :=
  ∃ edge ∈ parallelRawTransitionEdges signature leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture ∪
      parallelDoneEdges signature parentAlphabet,
    edge.source = source ∧ edge.target = target

/-- Joint reachability in the raw synchronized product. This is the
`Reach(τ₁ ∥_I τ₂)` premise appearing in `SyncEdges_I` in the paper. -/
def ParallelReachable (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (state : TypeAutomatonState) : Prop :=
  Relation.ReflTransGen
    (ParallelRawStep signature parentAlphabet leftAlphabet rightAlphabet
      interface left right leftFuture rightFuture)
    (.pair left.initial right.initial) state

theorem parallelReachable_initial (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    ParallelReachable signature parentAlphabet leftAlphabet rightAlphabet
      interface left right leftFuture rightFuture
      (.pair left.initial right.initial) :=
  Relation.ReflTransGen.refl

theorem ParallelReachable.tail_raw
    {signature : TypeAlphabet}
    {parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet}
    {interface : Interface}
    {left right : AutomatonFragment} {source target : TypeAutomatonState}
    {leftFuture rightFuture : TypeAutomatonState → Finset BareMessage}
    (hSource : ParallelReachable signature parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture source)
    (hStep : ParallelRawStep signature parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture source target) :
    ParallelReachable signature parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture target :=
  Relation.ReflTransGen.tail hSource hStep

/-- A raw synchronized edge extends a jointly reachable source to its target. -/
theorem ParallelReachable.target_of_rawTransition
    {signature : TypeAlphabet}
    {parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet}
    {interface : Interface}
    {left right : AutomatonFragment} {edge : PendingAutomatonEdge}
    {leftFuture rightFuture : TypeAutomatonState → Finset BareMessage}
    (hSource : ParallelReachable signature parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture edge.source)
    (hEdge : edge ∈ parallelRawTransitionEdges signature leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture) :
    ParallelReachable signature parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture edge.target :=
  hSource.tail_raw ⟨edge, Finset.mem_union_left _ hEdge, rfl, rfl⟩

/--
Build a synchronized parallel product.

`Q = Q₁ × Q₂ ∪ {q_done}`, the initial state is `(i₁,i₂)`, and
`F_τ = {q_done}`.  Synchronized component edges become product edges.  Their
interface offers are hidden from the product edge.  If both component targets
are accepting, the product edge is redirected to `q_done`; otherwise its
target is the target pair.  Finally, only product edges whose source is
reachable from `(i₁,i₂)` are retained, and `q_done` receives the usual
non-clock silent idle self-loop.
-/
def buildParallelAutomaton (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    AutomatonFragment := by
  classical
  let states : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      (left.states.biUnion fun leftState =>
        right.states.image fun rightState =>
          TypeAutomatonState.pair leftState rightState)
  -- `F_τ = {q_done}` exactly: a raw product state is not accepting on its own.
  let accepting : Finset TypeAutomatonState := {TypeAutomatonState.final}
  let transitionEdges :=
    (parallelRawTransitionEdges signature leftAlphabet rightAlphabet interface
      left right
      leftFuture rightFuture).filter fun edge =>
      ParallelReachable signature parentAlphabet leftAlphabet rightAlphabet
        interface left right
        leftFuture rightFuture edge.source
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting
      (transitionEdges ∪ parallelDoneEdges signature parentAlphabet)
  exact product

theorem buildParallelAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface) (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (hLeftEdgeTargets : ∀ edge ∈ left.edges, edge.target ∈ left.states)
    (hRightEdgeTargets : ∀ edge ∈ right.edges, edge.target ∈ right.states) :
    (buildParallelAutomaton signature parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    parallelRawTransitionEdges, parallelDoneEdges, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with
      ⟨⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _hSync⟩, rfl⟩, _⟩ |
      ⟨environment, _, rfl⟩
  · by_cases hAccept :
      leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
    · simp [hAccept] at hFuture
      by_cases hClock :
          (AutomatonConstructionLabel.combine interface leftEdge.label
            rightEdge.label).semantic = TypeLabel.tock
      · simp [parallelFutureSpec, hClock] at hFuture
      · simp [parallelFutureSpec, hClock] at hFuture
        obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
        rw [← hTargetEq]
        simp [buildParallelAutomaton, finishAutomatonFragment]
    · simp [hAccept] at hFuture
      have hPairNotFinal :
          ¬ TypeAutomatonState.pair leftEdge.target rightEdge.target =
            TypeAutomatonState.final := by
        intro hEq
        cases hEq
      simp [parallelFutureSpec, hPairNotFinal] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image]
        at hLeftEdge hRightEdge
      obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
      obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
      rw [← hLeftEq, ← hRightEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hLeftEdgeTargets leftRaw hLeftRaw,
        hRightEdgeTargets rightRaw hRightRaw]
  · simp at hFuture

end

end Pact
