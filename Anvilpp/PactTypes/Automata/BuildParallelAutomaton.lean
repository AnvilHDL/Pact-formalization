import Anvilpp.PactTypes.Automata.BuildSequenceAutomaton
import Anvilpp.PactTypes.Automata.SyncEdges

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

/-- Future spec used by parallel product edges.

A synchronized clock edge ends the current cycle, so its public future offers
are empty — whether or not it redirects to the completed state.  All other
product edges keep the usual symbolic reference to the target product state's
global `OF` equation. -/
def parallelFutureSpec (label : AutomatonConstructionLabel)
    (target : TypeAutomatonState) (removed : Finset BareMessage) :
    FutureSpec :=
  if label.semantic = TypeLabel.tock then .explicit ∅
  else .at target removed

/-- The unfiltered synchronized edges of a parallel product. Completing
component pairs are redirected to the dedicated `.final` state.  A
non-redirecting edge realizes the ordinary rule and so needs both sources
live; a redirecting one realizes the fusing rule, whose sources are
unconstrained. -/
def parallelRawTransitionEdges
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
      syncAutomatonEdges leftAlphabet rightAlphabet interface
        leftEdge rightEdge ∧
        (¬ (leftEdge.target ∈ left.accepting ∧
              rightEdge.target ∈ right.accepting) →
          leftEdge.source ∉ left.accepting ∧
          rightEdge.source ∉ right.accepting)).image fun rightEdge =>
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

/-- The unpartnered edges of a product state whose left component has already
reached an accepting state.  The surviving right component steps alone, so
there is nothing left to synchronize with: only the interface has to be empty
on both its offer fields. -/
def parallelLeftCompleteEdges
    (parentAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((left.accepting ∩ left.states).biUnion fun leftState =>
      ((resolveAutomatonEdgesWith right rightFuture).filter fun rightEdge =>
          rightEdge.target ∉ right.accepting ∧
          restrictTypeOffers interface rightEdge.current = ∅ ∧
          restrictTypeOffers interface rightEdge.future = ∅).biUnion
        fun rightEdge =>
          -- The survivor stands for the child re-stamped with the merged
          -- alphabet, so it is observable under every merged environment whose
          -- projection is the one the child's edge carries.
          ((parentAlphabet.localEnvironments).filter
            fun environment =>
              projectAutomatonEnvironment rightAlphabet environment =
                rightEdge.environment).image
            fun environment =>
              let target : TypeAutomatonState := .survivor 1 rightEdge.target
              { source := .pair leftState rightEdge.source
                environment := environment
                label := rightEdge.label
                current := rightEdge.current
                future := parallelFutureSpec rightEdge.label target rightEdge.current
                target := target })

/-- The mirror of `parallelLeftCompleteEdges` for a completed right
component. -/
def parallelRightCompleteEdges
    (parentAlphabet leftAlphabet : PactTypeAlphabet) (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((right.accepting ∩ right.states).biUnion fun rightState =>
      ((resolveAutomatonEdgesWith left leftFuture).filter fun leftEdge =>
          leftEdge.target ∉ left.accepting ∧
          restrictTypeOffers interface leftEdge.current = ∅ ∧
          restrictTypeOffers interface leftEdge.future = ∅).biUnion
        fun leftEdge =>
          ((parentAlphabet.localEnvironments).filter
            fun environment =>
              projectAutomatonEnvironment leftAlphabet environment =
                leftEdge.environment).image
            fun environment =>
              let target : TypeAutomatonState := .survivor 0 leftEdge.target
              { source := .pair leftEdge.source rightState
                environment := environment
                label := leftEdge.label
                current := leftEdge.current
                future := parallelFutureSpec leftEdge.label target leftEdge.current
                target := target })

/-- The continuation of `parallelLeftCompleteEdges` inside the survivor
region: the surviving right component keeps stepping from `survivor 1`. -/
def parallelLeftCompleteSurvivorEdges
    (parentAlphabet rightAlphabet : PactTypeAlphabet) (interface : Interface)
    (right : AutomatonFragment)
    (rightFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith right rightFuture).filter fun rightEdge =>
        rightEdge.target ∉ right.accepting ∧
        restrictTypeOffers interface rightEdge.current = ∅ ∧
        restrictTypeOffers interface rightEdge.future = ∅).biUnion
      fun rightEdge =>
        ((parentAlphabet.localEnvironments).filter
          fun environment =>
            projectAutomatonEnvironment rightAlphabet environment =
              rightEdge.environment).image
          fun environment =>
            let target : TypeAutomatonState := .survivor 1 rightEdge.target
            { source := .survivor 1 rightEdge.source
              environment := environment
              label := rightEdge.label
              current := rightEdge.current
              future := parallelFutureSpec rightEdge.label target rightEdge.current
              target := target }

/-- The mirror of `parallelLeftCompleteSurvivorEdges` for a surviving left
component, stepping from `survivor 0`. -/
def parallelRightCompleteSurvivorEdges
    (parentAlphabet leftAlphabet : PactTypeAlphabet) (interface : Interface)
    (left : AutomatonFragment)
    (leftFuture : TypeAutomatonState → Finset BareMessage) :
    Finset PendingAutomatonEdge := by
  classical
  exact
    ((resolveAutomatonEdgesWith left leftFuture).filter fun leftEdge =>
        leftEdge.target ∉ left.accepting ∧
        restrictTypeOffers interface leftEdge.current = ∅ ∧
        restrictTypeOffers interface leftEdge.future = ∅).biUnion
      fun leftEdge =>
        ((parentAlphabet.localEnvironments).filter
          fun environment =>
            projectAutomatonEnvironment leftAlphabet environment =
              leftEdge.environment).image
          fun environment =>
            let target : TypeAutomatonState := .survivor 0 leftEdge.target
            { source := .survivor 0 leftEdge.source
              environment := environment
              label := leftEdge.label
              current := leftEdge.current
              future := parallelFutureSpec leftEdge.label target leftEdge.current
              target := target }

/-- The non-clock idle edges attached to the completed parallel state. -/
def parallelDoneEdges
    (alphabet : PactTypeAlphabet) : Finset PendingAutomatonEdge := by
  classical
  exact ((alphabet.localEnvironments).filter fun environment =>
    environment.clock = false).image fun environment =>
      { source := TypeAutomatonState.final
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .explicit ∅
        target := .final }

/-- One raw graph step used by the paper's `Reach` side condition. -/
def ParallelRawStep
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (source target : TypeAutomatonState) : Prop :=
  ∃ edge ∈ parallelRawTransitionEdges leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture ∪
      parallelLeftCompleteEdges parentAlphabet rightAlphabet
        interface left right rightFuture ∪
      parallelRightCompleteEdges parentAlphabet leftAlphabet
        interface left right leftFuture ∪
      parallelLeftCompleteSurvivorEdges parentAlphabet rightAlphabet
        interface right rightFuture ∪
      parallelRightCompleteSurvivorEdges parentAlphabet leftAlphabet
        interface left leftFuture ∪
      parallelDoneEdges parentAlphabet,
    edge.source = source ∧ edge.target = target

/-- Joint reachability in the raw synchronized product. This is the
`Reach(τ₁ ∥_I τ₂)` premise appearing in `SyncEdges_I` in the paper. -/
def ParallelReachable
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (state : TypeAutomatonState) : Prop :=
  Relation.ReflTransGen
    (ParallelRawStep parentAlphabet leftAlphabet rightAlphabet
      interface left right leftFuture rightFuture)
    (.pair left.initial right.initial) state

theorem parallelReachable_initial
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    ParallelReachable parentAlphabet leftAlphabet rightAlphabet
      interface left right leftFuture rightFuture
      (.pair left.initial right.initial) :=
  Relation.ReflTransGen.refl

theorem ParallelReachable.tail_raw

    {parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet}
    {interface : Interface}
    {left right : AutomatonFragment} {source target : TypeAutomatonState}
    {leftFuture rightFuture : TypeAutomatonState → Finset BareMessage}
    (hSource : ParallelReachable parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture source)
    (hStep : ParallelRawStep parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture source target) :
    ParallelReachable parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture target :=
  Relation.ReflTransGen.tail hSource hStep

/-- A raw synchronized edge extends a jointly reachable source to its target. -/
theorem ParallelReachable.target_of_rawTransition

    {parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet}
    {interface : Interface}
    {left right : AutomatonFragment} {edge : PendingAutomatonEdge}
    {leftFuture rightFuture : TypeAutomatonState → Finset BareMessage}
    (hSource : ParallelReachable parentAlphabet leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture edge.source)
    (hEdge : edge ∈ parallelRawTransitionEdges leftAlphabet
      rightAlphabet interface left right
      leftFuture rightFuture) :
    ParallelReachable parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture edge.target :=
  hSource.tail_raw
    ⟨edge, Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hEdge)))), rfl, rfl⟩

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
def buildParallelAutomaton
    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage) :
    AutomatonFragment := by
  classical
  let states : Finset TypeAutomatonState :=
    insert TypeAutomatonState.final
      ((left.states.biUnion fun leftState =>
        right.states.image fun rightState =>
          TypeAutomatonState.pair leftState rightState) ∪
        (left.states.image (TypeAutomatonState.survivor 0)) ∪
        (right.states.image (TypeAutomatonState.survivor 1)))
  -- `F_τ = {q_done}` exactly: a raw product state is not accepting on its own.
  let accepting : Finset TypeAutomatonState := {TypeAutomatonState.final}
  let transitionEdges :=
    (parallelRawTransitionEdges leftAlphabet rightAlphabet interface
      left right
      leftFuture rightFuture ∪
      parallelLeftCompleteEdges parentAlphabet rightAlphabet
        interface left right rightFuture ∪
      parallelRightCompleteEdges parentAlphabet leftAlphabet
        interface left right leftFuture ∪
      parallelLeftCompleteSurvivorEdges parentAlphabet rightAlphabet
        interface right rightFuture ∪
      parallelRightCompleteSurvivorEdges parentAlphabet leftAlphabet
        interface left leftFuture).filter
      fun edge =>
      ParallelReachable parentAlphabet leftAlphabet rightAlphabet
        interface left right
        leftFuture rightFuture edge.source
  let product := finishAutomatonFragment
    states (.pair left.initial right.initial) accepting
      (transitionEdges ∪ parallelDoneEdges parentAlphabet)
  exact product

/-- A product edge is clocked exactly when both components are, by
`combineAutomatonEnvironment`'s `left.clock && right.clock` gate.  Both
components are then tock-labelled with empty offers, so `combine` produces
`tock` and `hideOffers` filters the empty union to `∅`. -/
theorem buildParallelAutomaton_clockEdgesAreTock

    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface) (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (hLeftClock : left.ClockEdgesAreTock)
    (hRightClock : right.ClockEdgesAreTock) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelDoneEdges, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, Finset.mem_inter] at hEdge
  rcases hEdge with
      ⟨⟨⟨⟨⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _hSync⟩, rfl⟩ |
        ⟨leftState, ⟨_, hLeftState⟩, rightEdge, ⟨hRightEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩⟩ |
        ⟨rightState, ⟨_, hRightState⟩, leftEdge, ⟨hLeftEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩⟩ |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩⟩ |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩,
        _⟩ |
      ⟨environment, ⟨_, hNotClock⟩, rfl⟩
  · -- The combined environment is clocked only on the `tock` branch, which
    -- requires both component environments to be clocked.
    simp only at hClock
    have hBoth : leftEdge.environment.clock = true ∧
        rightEdge.environment.clock = true := by
      by_cases hAnd : leftEdge.environment.clock && rightEdge.environment.clock
      · simpa using hAnd
      · exfalso
        rw [combineAutomatonEnvironment, if_neg (by simpa using hAnd)] at hClock
        exact absurd hClock (by simp)
    -- Pull each component back to its own pending edge: resolving future
    -- fields preserves environment, label, and current offers.
    simp only [resolveAutomatonEdgesWith, Finset.mem_image]
      at hLeftEdge hRightEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    have hLeftEnv : leftRaw.environment = leftEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hLeftEq
    have hRightEnv : rightRaw.environment = rightEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hRightEq
    have hLeftLabel : leftRaw.label = leftEdge.label :=
      congrArg AutomatonFragmentEdge.label hLeftEq
    have hRightLabel : rightRaw.label = rightEdge.label :=
      congrArg AutomatonFragmentEdge.label hRightEq
    have hLeftCurrent : leftRaw.current = leftEdge.current :=
      congrArg AutomatonFragmentEdge.current hLeftEq
    have hRightCurrent : rightRaw.current = rightEdge.current :=
      congrArg AutomatonFragmentEdge.current hRightEq
    obtain ⟨hLeftTock, hLeftEmpty⟩ :=
      hLeftClock leftRaw hLeftRaw (by rw [hLeftEnv]; exact hBoth.1)
    obtain ⟨hRightTock, hRightEmpty⟩ :=
      hRightClock rightRaw hRightRaw (by rw [hRightEnv]; exact hBoth.2)
    rw [hLeftLabel] at hLeftTock
    rw [hRightLabel] at hRightTock
    rw [hLeftCurrent] at hLeftEmpty
    rw [hRightCurrent] at hRightEmpty
    -- `combine` yields `tock` only from two `.visible tock` components.
    cases hLeftForm : leftEdge.label with
    | «variable» _ =>
        exfalso
        rw [hLeftForm] at hLeftTock
        simp [AutomatonConstructionLabel.semantic, TypeLabel.silent] at hLeftTock
    | visible leftVisible =>
        cases hRightForm : rightEdge.label with
        | «variable» _ =>
            exfalso
            rw [hRightForm] at hRightTock
            simp [AutomatonConstructionLabel.semantic, TypeLabel.silent]
              at hRightTock
        | visible rightVisible =>
            rw [hLeftForm] at hLeftTock
            rw [hRightForm] at hRightTock
            simp only [AutomatonConstructionLabel.semantic] at hLeftTock hRightTock
            refine ⟨?_, ?_⟩
            · simp only [AutomatonConstructionLabel.combine,
                AutomatonConstructionLabel.semantic]
              exact (TypeLabel.combine_eq_tock_iff interface leftVisible
                rightVisible).mpr ⟨hLeftTock, hRightTock⟩
            · simp [hLeftEmpty, hRightEmpty, hideOffers]
  · -- The surviving right component carries its own environment, so its own
    -- clock discipline applies unchanged.
    simp only at hClock ⊢
    -- A clocked survivor environment projects to `tock`, so the child edge is
    -- clocked too and its own discipline applies.
    have hChildClock : rightEdge.environment.clock = true := by
      rw [← hProject, projectAutomatonEnvironment_of_clock hClock]; rfl
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    have hEnv : rightRaw.environment = rightEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hRightEq
    have hLabel : rightRaw.label = rightEdge.label :=
      congrArg AutomatonFragmentEdge.label hRightEq
    have hCurrent : rightRaw.current = rightEdge.current :=
      congrArg AutomatonFragmentEdge.current hRightEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRightClock rightRaw hRightRaw (by rw [hEnv]; exact hChildClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The mirror case for a surviving left component.
    simp only at hClock ⊢
    have hChildClock : leftEdge.environment.clock = true := by
      rw [← hProject, projectAutomatonEnvironment_of_clock hClock]; rfl
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    have hEnv : leftRaw.environment = leftEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hLeftEq
    have hLabel : leftRaw.label = leftEdge.label :=
      congrArg AutomatonFragmentEdge.label hLeftEq
    have hCurrent : leftRaw.current = leftEdge.current :=
      congrArg AutomatonFragmentEdge.current hLeftEq
    obtain ⟨hTock, hEmpty⟩ :=
      hLeftClock leftRaw hLeftRaw (by rw [hEnv]; exact hChildClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The right survivor continuing inside the survivor region.
    simp only at hClock ⊢
    -- A clocked survivor environment projects to `tock`, so the child edge is
    -- clocked too and its own discipline applies.
    have hChildClock : rightEdge.environment.clock = true := by
      rw [← hProject, projectAutomatonEnvironment_of_clock hClock]; rfl
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    have hEnv : rightRaw.environment = rightEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hRightEq
    have hLabel : rightRaw.label = rightEdge.label :=
      congrArg AutomatonFragmentEdge.label hRightEq
    have hCurrent : rightRaw.current = rightEdge.current :=
      congrArg AutomatonFragmentEdge.current hRightEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRightClock rightRaw hRightRaw (by rw [hEnv]; exact hChildClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The mirror case for a left survivor continuing.
    simp only at hClock ⊢
    have hChildClock : leftEdge.environment.clock = true := by
      rw [← hProject, projectAutomatonEnvironment_of_clock hClock]; rfl
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    have hEnv : leftRaw.environment = leftEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hLeftEq
    have hLabel : leftRaw.label = leftEdge.label :=
      congrArg AutomatonFragmentEdge.label hLeftEq
    have hCurrent : leftRaw.current = leftEdge.current :=
      congrArg AutomatonFragmentEdge.current hLeftEq
    obtain ⟨hTock, hEmpty⟩ :=
      hLeftClock leftRaw hLeftRaw (by rw [hEnv]; exact hChildClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · exfalso
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)

theorem buildParallelAutomaton_futureTargetsInStates

    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface) (left right : AutomatonFragment)
    (leftFuture rightFuture : TypeAutomatonState → Finset BareMessage)
    (hLeftEdgeTargets : ∀ edge ∈ left.edges, edge.target ∈ left.states)
    (hRightEdgeTargets : ∀ edge ∈ right.edges, edge.target ∈ right.states) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right
      leftFuture rightFuture).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelDoneEdges, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, Finset.mem_inter] at hEdge
  rcases hEdge with
      ⟨⟨⟨⟨⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _hSync⟩, rfl⟩ |
        ⟨leftState, ⟨_, hLeftState⟩, rightEdge, ⟨hRightEdge, _hAllowed⟩,
          _survivorEnv, -, rfl⟩⟩ |
        ⟨rightState, ⟨_, hRightState⟩, leftEdge, ⟨hLeftEdge, _hAllowed⟩,
          _survivorEnv, -, rfl⟩⟩ |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩, _survivorEnv, -, rfl⟩⟩ |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩, _survivorEnv, -, rfl⟩,
        _⟩ |
      ⟨environment, _, rfl⟩
  · by_cases hClock :
        (AutomatonConstructionLabel.combine interface leftEdge.label
          rightEdge.label).semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · by_cases hAccept :
        leftEdge.target ∈ left.accepting ∧ rightEdge.target ∈ right.accepting
      · simp [hAccept, parallelFutureSpec, hClock] at hFuture
        obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
        rw [← hTargetEq]
        simp [buildParallelAutomaton, finishAutomatonFragment]
      · simp [hAccept, parallelFutureSpec, hClock] at hFuture
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
  · by_cases hClock : rightEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
      obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
      rw [← hRightEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hRightEdgeTargets rightRaw hRightRaw]
  · by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
      obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
      rw [← hLeftEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hLeftEdgeTargets leftRaw hLeftRaw]
  · by_cases hClock : rightEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
      obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
      rw [← hRightEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hRightEdgeTargets rightRaw hRightRaw]
  · by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
      obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
      rw [← hLeftEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hLeftEdgeTargets leftRaw hLeftRaw]
  · simp at hFuture

end

end Pact
