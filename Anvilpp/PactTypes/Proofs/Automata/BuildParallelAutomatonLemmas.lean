import Anvilpp.PactTypes.Spec.Automata.BuildParallelAutomaton

/-!
# buildParallelAutomaton
-/

namespace Pact

noncomputable section

/-- A product edge is clocked exactly when both components are, by
`combineAutomatonEnvironment`'s `left.clock && right.clock` gate.  Both
components are then tock-labelled with empty offers, so `combine` produces
`tock` and `hideOffers` filters the empty union to `∅`.  The survivor and
completion families copy a re-stamped child edge verbatim, so they inherit
that child's own clock discipline. -/
theorem buildParallelAutomaton_clockEdgesAreTock

    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hLeftClock : left.ClockEdgesAreTock)
    (hRightClock : right.ClockEdgesAreTock)
    (hRestampedLeftClock : restampedLeft.ClockEdgesAreTock)
    (hRestampedRightClock : restampedRight.ClockEdgesAreTock) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture
      restampedRightFuture).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelLeftCompleteDoneEdges,
    parallelRightCompleteDoneEdges, parallelDoneEdges, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, Finset.mem_inter] at hEdge
  rcases hEdge with
      ((((((⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _hSync⟩, rfl⟩ |
        ⟨leftState, ⟨_, hLeftState⟩, rightEdge, ⟨hRightEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩) |
        ⟨rightState, ⟨_, hRightState⟩, leftEdge, ⟨hLeftEdge, _hAllowed⟩,
          survivorEnv, ⟨_, hProject⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩, rfl⟩) |
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
  · -- The surviving right component carries a merged environment projecting to
    -- the child's own, so the child's clock discipline applies unchanged.
    simp only at hClock ⊢
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
  · -- The re-stamped right component continuing inside the survivor region:
    -- its environment is copied verbatim.
    simp only at hClock ⊢
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    have hEnv : rightRaw.environment = rightEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hRightEq
    have hLabel : rightRaw.label = rightEdge.label :=
      congrArg AutomatonFragmentEdge.label hRightEq
    have hCurrent : rightRaw.current = rightEdge.current :=
      congrArg AutomatonFragmentEdge.current hRightEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRestampedRightClock rightRaw hRightRaw (by rw [hEnv]; exact hClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The mirror case for the re-stamped left component continuing.
    simp only at hClock ⊢
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    have hEnv : leftRaw.environment = leftEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hLeftEq
    have hLabel : leftRaw.label = leftEdge.label :=
      congrArg AutomatonFragmentEdge.label hLeftEq
    have hCurrent : leftRaw.current = leftEdge.current :=
      congrArg AutomatonFragmentEdge.current hLeftEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRestampedLeftClock leftRaw hLeftRaw (by rw [hEnv]; exact hClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The re-stamped right component's completing step into `q_done`.
    simp only at hClock ⊢
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hRightEdge
    obtain ⟨rightRaw, hRightRaw, hRightEq⟩ := hRightEdge
    have hEnv : rightRaw.environment = rightEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hRightEq
    have hLabel : rightRaw.label = rightEdge.label :=
      congrArg AutomatonFragmentEdge.label hRightEq
    have hCurrent : rightRaw.current = rightEdge.current :=
      congrArg AutomatonFragmentEdge.current hRightEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRestampedRightClock rightRaw hRightRaw (by rw [hEnv]; exact hClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · -- The mirror case for the re-stamped left component's completing step.
    simp only at hClock ⊢
    simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
    obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
    have hEnv : leftRaw.environment = leftEdge.environment :=
      congrArg AutomatonFragmentEdge.environment hLeftEq
    have hLabel : leftRaw.label = leftEdge.label :=
      congrArg AutomatonFragmentEdge.label hLeftEq
    have hCurrent : leftRaw.current = leftEdge.current :=
      congrArg AutomatonFragmentEdge.current hLeftEq
    obtain ⟨hTock, hEmpty⟩ :=
      hRestampedLeftClock leftRaw hLeftRaw (by rw [hEnv]; exact hClock)
    rw [hLabel] at hTock
    rw [hCurrent] at hEmpty
    exact ⟨hTock, hEmpty⟩
  · exfalso
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)

/-- Every symbolic future reference of the product points at a declared product
state: the pair families land in `Q₁ × Q₂`, the survivor families in the
`survivor` images of the component carriers, and the completing families in
`q_done`. -/
theorem buildParallelAutomaton_futureTargetsInStates

    (parentAlphabet leftAlphabet rightAlphabet : PactTypeAlphabet)
    (interface : Interface)
    (left right restampedLeft restampedRight : AutomatonFragment)
    (leftFuture rightFuture restampedLeftFuture restampedRightFuture :
      TypeAutomatonState → Finset BareMessage)
    (hLeftEdgeTargets : ∀ edge ∈ left.edges, edge.target ∈ left.states)
    (hRightEdgeTargets : ∀ edge ∈ right.edges, edge.target ∈ right.states)
    (hRestampedLeftEdgeTargets :
      ∀ edge ∈ restampedLeft.edges, edge.target ∈ left.states)
    (hRestampedRightEdgeTargets :
      ∀ edge ∈ restampedRight.edges, edge.target ∈ right.states) :
    (buildParallelAutomaton parentAlphabet leftAlphabet rightAlphabet
      interface left right restampedLeft restampedRight
      leftFuture rightFuture restampedLeftFuture
      restampedRightFuture).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildParallelAutomaton, finishAutomatonFragment, Finset.mem_union,
    parallelRawTransitionEdges, parallelLeftCompleteEdges,
    parallelRightCompleteEdges, parallelLeftCompleteSurvivorEdges,
    parallelRightCompleteSurvivorEdges, parallelLeftCompleteDoneEdges,
    parallelRightCompleteDoneEdges, parallelDoneEdges, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, Finset.mem_inter] at hEdge
  rcases hEdge with
      ((((((⟨leftEdge, hLeftEdge, rightEdge, ⟨hRightEdge, _hSync⟩, rfl⟩ |
        ⟨leftState, ⟨_, hLeftState⟩, rightEdge, ⟨hRightEdge, _hAllowed⟩,
          _survivorEnv, -, rfl⟩) |
        ⟨rightState, ⟨_, hRightState⟩, leftEdge, ⟨hLeftEdge, _hAllowed⟩,
          _survivorEnv, -, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩, rfl⟩) |
        ⟨rightEdge, ⟨hRightEdge, _hAllowed⟩, rfl⟩) |
        ⟨leftEdge, ⟨hLeftEdge, _hAllowed⟩, rfl⟩) |
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
        hRestampedRightEdgeTargets rightRaw hRightRaw]
  · by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp only [resolveAutomatonEdgesWith, Finset.mem_image] at hLeftEdge
      obtain ⟨leftRaw, hLeftRaw, hLeftEq⟩ := hLeftEdge
      rw [← hLeftEq]
      simp [buildParallelAutomaton, finishAutomatonFragment,
        hRestampedLeftEdgeTargets leftRaw hLeftRaw]
  · by_cases hClock : rightEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp [buildParallelAutomaton, finishAutomatonFragment]
  · by_cases hClock : leftEdge.label.semantic = TypeLabel.tock
    · simp [parallelFutureSpec, hClock] at hFuture
    · simp [parallelFutureSpec, hClock] at hFuture
      obtain ⟨hTargetEq, _hRemovedEq⟩ := hFuture
      rw [← hTargetEq]
      simp [buildParallelAutomaton, finishAutomatonFragment]
  · simp at hFuture

end
end Pact
