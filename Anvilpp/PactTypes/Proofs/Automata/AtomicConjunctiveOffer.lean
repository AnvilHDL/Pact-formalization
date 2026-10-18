import Anvilpp.PactTypes.Spec.Automata.BuildAtomicConjunctiveOffer
import Anvilpp.PactTypes.Proofs.Automata.BuildOfferAutomataLemmas
import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResiduals

namespace Pact

noncomputable section

open Classical

/-- Every firing edge communicates exactly the enabled subset and enters its residual copy. -/
theorem mem_conjunctiveFiringEdges (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (residuals : List (Finset Nat × AutomatonFragment)) (edge : PendingAutomatonEdge) :
    edge ∈ conjunctiveFiringEdges alphabet branches residuals ↔
      ∃ entry ∈ residuals.zipIdx, ∃ env ∈ alphabet.localEnvironments,
        entry.1.1.Nonempty ∧ typeEnabledBranches env branches = entry.1.1 ∧
        edge = {
          source := .root
          environment := env
          label := .visible (typeBranchBatchLabel branches entry.1.1)
          current := typeBranchActions branches ∩ alphabet.actions
          future := .at (childState (entry.2 + 1) entry.1.2.initial)
            (typeBranchActions branches ∩ alphabet.actions)
          target := childState (entry.2 + 1) entry.1.2.initial } := by
  simp only [conjunctiveFiringEdges, mem_foldl_union_iff, Finset.notMem_empty,
    false_or, Finset.mem_image, Finset.mem_filter]
  aesop

/-- Atomic communication cannot fire in a clock environment. -/
theorem conjunctiveFiringEdges_clock_false (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (residuals : List (Finset Nat × AutomatonFragment)) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ conjunctiveFiringEdges alphabet branches residuals) :
    edge.environment.clock = false := by
  obtain ⟨entry, _, env, hEnv, hNonempty, hSelected, rfl⟩ :=
    (mem_conjunctiveFiringEdges alphabet branches residuals edge).mp hEdge
  by_cases hClock : env.clock = true
  · have hEmpty := PactTypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
      hEnv hClock
    have hNone : typeEnabledBranches env branches = ∅ :=
      (typeEnabledBranches_eq_empty_iff env branches).mpr (by
        simp [TypeNoImmediateBranch, hEmpty])
    rw [← hSelected, hNone] at hNonempty
    exact False.elim (Finset.not_nonempty_empty hNonempty)
  · simpa using hClock

/-- The edge's future field reads its residual target and removes all declared heads. -/
theorem conjunctiveFiringEdges_offers (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (residuals : List (Finset Nat × AutomatonFragment)) (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ conjunctiveFiringEdges alphabet branches residuals) :
    edge.current = typeBranchActions branches ∩ alphabet.actions ∧
      edge.future = .at edge.target edge.current := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ :=
    (mem_conjunctiveFiringEdges alphabet branches residuals edge).mp hEdge
  exact ⟨rfl, rfl⟩

/-- The constructor preserves the clock-edge invariant of all copied fragments. -/
theorem buildAtomicConjunctiveOfferAutomaton_clockEdgesAreTock
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment) (residuals : List (Finset Nat × AutomatonFragment))
    (hElse : elseAutomaton.ClockEdgesAreTock)
    (hResiduals : ∀ entry ∈ residuals, entry.2.ClockEdgesAreTock) :
    (buildAtomicConjunctiveOfferAutomaton alphabet branches elseAutomaton residuals).ClockEdgesAreTock := by
  intro edge hEdge hClock
  simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hDefault | hResidual) | hFire) | hWait) | hElseEdge)
  · exact childPendingEdges_clockEdgesAreTock 0 elseAutomaton hElse edge hDefault hClock
  · exact indexedFragment_clockEdgesAreTock residuals hResiduals edge hResidual hClock
  · rw [conjunctiveFiringEdges_clock_false alphabet branches residuals edge hFire] at hClock
    contradiction
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨env, ⟨_, hNotClock, _⟩, rfl⟩ := hWait
    simp only at hClock
    rw [hNotClock] at hClock
    contradiction
  · simp only [Finset.mem_image, Finset.mem_filter] at hElseEdge
    obtain ⟨env, ⟨_, hNotClock, _⟩, rfl⟩ := hElseEdge
    simp only at hClock
    rw [hNotClock] at hClock
    contradiction

/-- Every symbolic future reference points into its copied fragment or to the root. -/
theorem buildAtomicConjunctiveOfferAutomaton_futureTargetsInStates
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment) (residuals : List (Finset Nat × AutomatonFragment))
    (hElse : elseAutomaton.FutureTargetsInStates)
    (hResiduals : ∀ entry ∈ residuals, entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hResidualInitial : ∀ entry ∈ residuals, entry.2.initial ∈ entry.2.states) :
    (buildAtomicConjunctiveOfferAutomaton alphabet branches elseAutomaton residuals).FutureTargetsInStates := by
  intro edge hEdge target hFuture
  simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hDefault | hResidual) | hFire) | hWait) | hElseEdge)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton hElse
      edge hDefault target hFuture
    simp [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates residuals hResiduals
      edge hResidual target hFuture
    simp [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · obtain ⟨entry, hEntry, env, _, _, _, rfl⟩ :=
      (mem_conjunctiveFiringEdges alphabet branches residuals edge).mp hFire
    cases hFuture
    have hInitial := hResidualInitial entry.1 (List.fst_mem_of_mem_zipIdx hEntry)
    have hState : childState (entry.2 + 1) entry.1.2.initial ∈ indexedFragmentStates residuals := by
      rw [indexedFragmentStates, mem_foldl_union_iff]
      exact Or.inr ⟨entry, hEntry, Finset.mem_image.mpr ⟨_, hInitial, rfl⟩⟩
    simp [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment, hState]
  · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
    cases hFuture
    simp [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment]
  · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hElseEdge
    cases hFuture
    simp [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Every root edge advertises all declared heads, whether it fires, waits, or defaults. -/
theorem buildAtomicConjunctiveOfferAutomaton_root_current
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment) (residuals : List (Finset Nat × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildAtomicConjunctiveOfferAutomaton alphabet branches elseAutomaton residuals).edges)
    (hSource : edge.source = .root) :
    edge.current = typeBranchActions branches ∩ alphabet.actions := by
  simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hDefault | hResidual) | hFire) | hWait) | hElseEdge)
  · obtain ⟨childEdge, _, rfl⟩ := Finset.mem_image.mp hDefault
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hResidual
    rcases hResidual with hEmpty | ⟨entry, _, hCopy⟩
    · simp at hEmpty
    · obtain ⟨childEdge, _, rfl⟩ := Finset.mem_image.mp hCopy
      simp [childPendingEdge, childState] at hSource
  · exact (conjunctiveFiringEdges_offers alphabet branches residuals edge hFire).1
  · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hWait
    rfl
  · obtain ⟨env, _, rfl⟩ := Finset.mem_image.mp hElseEdge
    rfl

/-- The direct root-menu contribution is exactly the declared head set. -/
theorem buildAtomicConjunctiveOfferAutomaton_offersAt_root
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment) (residuals : List (Finset Nat × AutomatonFragment)) :
    ({ states := (buildAtomicConjunctiveOfferAutomaton alphabet branches elseAutomaton residuals).states
       edges := (buildAtomicConjunctiveOfferAutomaton alphabet branches elseAutomaton residuals).edges } :
      PendingAutomaton).offersAt .root = typeBranchActions branches ∩ alphabet.actions := by
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion, Finset.mem_filter] at hAction
    obtain ⟨edge, ⟨hEdge, hSource⟩, hAction⟩ := hAction
    split_ifs at hAction with hClock
    · simp at hAction
    · rwa [buildAtomicConjunctiveOfferAutomaton_root_current alphabet branches elseAutomaton
        residuals edge hEdge hSource] at hAction
  · intro action hAction
    let edge : PendingAutomatonEdge := {
      source := .root
      environment := TypeEnvironment.empty
      label := .visible TypeLabel.silent
      current := typeBranchActions branches ∩ alphabet.actions
      future := .at (childState 0 elseAutomaton.initial)
        (typeBranchActions branches ∩ alphabet.actions)
      target := childState 0 elseAutomaton.initial }
    apply Finset.mem_biUnion.mpr
    refine ⟨edge, Finset.mem_filter.mpr ⟨?_, rfl⟩, ?_⟩
    · simp only [buildAtomicConjunctiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union]
      apply Or.inr
      refine Finset.mem_image.mpr ⟨TypeEnvironment.empty, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
      · exact PactTypeAlphabet.empty_mem_localEnvironments alphabet
      · simp [TypeEnvironment.empty]
    · simpa [edge, AutomatonConstructionLabel.semantic, TypeLabel.silent] using hAction

/-- Root menu steps stay at the root or enter a default or subset residual copy. -/
theorem buildAtomicConjunctiveOfferAutomaton_menuStep_root_subset
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (Finset Nat × AutomatonFragment)) :
    ({ states := (buildAtomicConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).states
       edges := (buildAtomicConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).edges } :
        PendingAutomaton).menuStep TypeAutomatonState.root ⊆
      insert TypeAutomatonState.root
        (conjunctiveOfferEntries elseAutomaton selectedConjunctions) := by
  classical
  intro state hState
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter] at hState
  obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hState
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · rw [if_pos hTock] at hIn
    exact absurd hIn (Finset.notMem_empty _)
  · rw [if_neg hTock] at hIn
    simp only [buildAtomicConjunctiveOfferAutomaton, conjunctiveFiringEdges, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with
      ((((hElseCopy | hConjunctionCopy) | hEnabled) | hWait) | hResolved)
    ·
      exfalso
      rw [childPendingEdges, Finset.mem_image] at hElseCopy
      obtain ⟨childEdge, -, hEq⟩ := hElseCopy
      rw [← hEq] at hSource
      simp [childPendingEdge, childState] at hSource
    ·
      exfalso
      rw [indexedFragmentEdges, mem_foldl_union_iff] at hConjunctionCopy
      rcases hConjunctionCopy with hEmpty | ⟨indexed, -, hCopy⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [childPendingEdges, Finset.mem_image] at hCopy
        obtain ⟨childEdge, -, hEq⟩ := hCopy
        rw [← hEq] at hSource
        simp [childPendingEdge, childState] at hSource
    · rw [mem_foldl_union_iff] at hEnabled
      rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
      · exact absurd hEmpty (Finset.notMem_empty _)
      · rw [Finset.mem_image] at hNewEdge
        obtain ⟨environment, -, hEq⟩ := hNewEdge
        have hTarget : edge.target =
            childState (indexed.2 + 1) indexed.1.2.initial := by
          rw [← hEq]
        rw [hTarget, Finset.mem_singleton] at hIn
        subst hIn
        refine Finset.mem_insert_of_mem ?_
        simp only [conjunctiveOfferEntries, Finset.mem_insert,
          List.mem_toFinset, List.mem_map]
        exact Or.inr ⟨indexed, hIndexed, rfl⟩
    · rw [Finset.mem_image] at hWait
      obtain ⟨environment, -, hEq⟩ := hWait
      have hTarget : edge.target = TypeAutomatonState.root := by
        rw [← hEq]
      rw [hTarget, Finset.mem_singleton] at hIn
      subst hIn
      exact Finset.mem_insert_self _ _
    · rw [Finset.mem_image] at hResolved
      obtain ⟨environment, -, hEq⟩ := hResolved
      have hTarget : edge.target = childState 0 elseAutomaton.initial := by
        rw [← hEq]
      rw [hTarget, Finset.mem_singleton] at hIn
      subst hIn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

end

end Pact
