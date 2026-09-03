import Anvilpp.PactTypes.Automata.BuildOfferAutomataDefs

namespace Pact

noncomputable section

theorem mem_foldl_union_iff
    {Element Item : Type} [DecidableEq Element]
    (items : List Item) (part : Item → Finset Element)
    (initial : Finset Element) (element : Element) :
    element ∈ items.foldl (fun accumulated item =>
      accumulated ∪ part item) initial ↔
      element ∈ initial ∨ ∃ item ∈ items, element ∈ part item := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [Finset.mem_union, List.mem_cons]
      aesop

private theorem childPendingEdges_futureTargetsInStates
    (index : Nat) (fragment : AutomatonFragment)
    (hTargets : fragment.FutureTargetsInStates) :
    ∀ edge ∈ childPendingEdges index fragment, ∀ target removed,
      edge.future = .at target removed →
        target ∈ childStates index fragment := by
  classical
  intro edge hEdge target removed hFuture
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hSpec : childEdge.future with
  | explicit offers =>
      simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
  | «at» childTarget childRemoved =>
      simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
      cases hFuture
      have hChildTarget := hTargets childEdge hChildEdge childTarget
        removed hSpec
      simp [childStates, childState, hChildTarget]

private theorem childPendingEdges_clockEdgesAreTock
    (index : Nat) (fragment : AutomatonFragment)
    (hClockEdges : fragment.ClockEdgesAreTock) :
    ∀ edge ∈ childPendingEdges index fragment,
      edge.environment.clock = true →
        edge.label.semantic = TypeLabel.tock ∧ edge.current = ∅ := by
  classical
  intro edge hEdge hClock
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  exact hClockEdges childEdge hChildEdge hClock

private theorem indexedFragment_clockEdgesAreTock
    (automata : List (BareMessage × AutomatonFragment))
    (hClockEdges : ∀ entry ∈ automata, entry.2.ClockEdgesAreTock) :
    ∀ edge ∈ indexedFragmentEdges automata,
      edge.environment.clock = true →
        edge.label.semantic = TypeLabel.tock ∧ edge.current = ∅ := by
  classical
  intro edge hEdge hClock
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    exact childPendingEdges_clockEdgesAreTock (indexed.2 + 1) indexed.1.2
      (hClockEdges indexed.1 hEntry) edge hChildEdge hClock

private theorem indexedFragment_futureTargetsInStates
    (automata : List (BareMessage × AutomatonFragment))
    (hTargets : ∀ entry ∈ automata, entry.2.FutureTargetsInStates) :
    ∀ edge ∈ indexedFragmentEdges automata, ∀ target removed,
      edge.future = .at target removed →
        target ∈ indexedFragmentStates automata := by
  classical
  intro edge hEdge target removed hFuture
  rw [indexedFragmentEdges, mem_foldl_union_iff] at hEdge
  rcases hEdge with hEmpty | ⟨indexed, hIndexed, hChildEdge⟩
  · simp at hEmpty
  · have hEntry : indexed.1 ∈ automata := by
      have hMapped : indexed.1 ∈ automata.zipIdx.map Prod.fst :=
        List.mem_map_of_mem (f := Prod.fst) hIndexed
      simpa using hMapped
    simp only [childPendingEdges, Finset.mem_image] at hChildEdge
    rcases hChildEdge with ⟨childEdge, hChildEdge, rfl⟩
    cases hSpec : childEdge.future with
    | explicit offers =>
        simp [childPendingEdge, childFutureSpec, hSpec] at hFuture
    | «at» childTarget childRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec] at hFuture
        cases hFuture
        have hChildTarget := hTargets indexed.1 hEntry childEdge hChildEdge
          childTarget removed hSpec
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        simp [childStates, childState, hChildTarget]

/-- Wait and else edges carry explicit `clock = false` guards; branch edges
require an immediate need, which a clocked environment (empty `immediate`)
cannot supply. -/
theorem buildExclusiveOfferAutomaton_clockEdgesAreTock
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseClock : elseAutomaton.ClockEdgesAreTock)
    (hBranchClock : ∀ entry ∈ branchAutomata, entry.2.ClockEdgesAreTock) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · exact childPendingEdges_clockEdgesAreTock 0 elseAutomaton hElseClock
      edge hElse hClock
  · exact indexedFragment_clockEdgesAreTock branchAutomata hBranchClock
      edge hIndexed hClock
  · exfalso
    rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hEnvMem, hEnabled, _⟩, rfl⟩ := hNewEdge
      simp only at hClock
      rw [PactTypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
        hEnvMem hClock] at hEnabled
      exact absurd hEnabled (by simp)
  · exfalso
    simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨_, hNotClock, _⟩, rfl⟩ := hWait
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)
  · exfalso
    simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨_, hNotClock, _⟩, rfl⟩ := hResolved
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)

theorem buildExclusiveOfferAutomaton_futureTargetsInStates
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates branchAutomata
      hBranchTargets edge hIndexed target removed hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexedEntry, hNewEdge⟩
    · simp at hEmpty
    · have hEntry : indexed.1 ∈ branchAutomata := by
        have hMapped : indexed.1 ∈ branchAutomata.zipIdx.map Prod.fst :=
          List.mem_map_of_mem (f := Prod.fst) hIndexedEntry
        simpa using hMapped
      simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hFuture
      cases hFuture
      have hInitial := hBranchInitial indexed.1 hEntry
      have hIndexedState :
          childState (indexed.2 + 1) indexed.1.2.initial ∈
            indexedFragmentStates branchAutomata := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexedEntry, ?_⟩
        simp [childStates, childState, hInitial]
      simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Wait and else edges carry explicit `clock = false` guards; enabled edges
require an immediate need, which a clocked environment cannot supply. -/
theorem buildSelectedConjunctiveOfferAutomaton_clockEdgesAreTock
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseClock : elseAutomaton.ClockEdgesAreTock)
    (hConjunctionClock : ∀ entry ∈ selectedConjunctions,
      entry.2.ClockEdgesAreTock) :
    (buildSelectedConjunctiveOfferAutomaton alphabet branches
      elseAutomaton selectedConjunctions).ClockEdgesAreTock := by
  classical
  intro edge hEdge hClock
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) | hResolved)
  · exact childPendingEdges_clockEdgesAreTock 0 elseAutomaton hElseClock
      edge hElse hClock
  · exact indexedFragment_clockEdgesAreTock selectedConjunctions
      hConjunctionClock edge hConjunction hClock
  · exfalso
    rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, _, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      obtain ⟨environment, ⟨hEnvMem, hEnabledNeed, _⟩, rfl⟩ := hNewEdge
      simp only at hClock
      rw [PactTypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
        hEnvMem hClock] at hEnabledNeed
      exact absurd hEnabledNeed (by simp)
  · exfalso
    simp only [Finset.mem_image, Finset.mem_filter] at hWait
    obtain ⟨environment, ⟨_, hNotClock, _⟩, rfl⟩ := hWait
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)
  · exfalso
    simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    obtain ⟨environment, ⟨_, hNotClock, _⟩, rfl⟩ := hResolved
    simp only at hClock
    rw [hNotClock] at hClock
    exact absurd hClock (by simp)

theorem buildSelectedConjunctiveOfferAutomaton_futureTargetsInStates
     (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    (buildSelectedConjunctiveOfferAutomaton alphabet branches
      elseAutomaton selectedConjunctions).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates
      selectedConjunctions hConjunctionTargets edge hConjunction target removed
        hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · rw [mem_foldl_union_iff] at hEnabled
    rcases hEnabled with hEmpty | ⟨indexed, hIndexed, hNewEdge⟩
    · simp at hEmpty
    · simp only [Finset.mem_image, Finset.mem_filter] at hNewEdge
      rcases hNewEdge with ⟨environment, _, rfl⟩
      simp only at hFuture
      cases hFuture
      have hIndexedFields := List.mem_zipIdx hIndexed
      simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and]
        at hIndexedFields
      rcases hIndexedFields with ⟨hBound, hValue⟩
      have hEntry : indexed.1 ∈ selectedConjunctions := by
        have hMember := List.getElem_mem hBound
        simpa [hValue] using hMember
      have hIndexedState : childState (indexed.2 + 1)
          indexed.1.2.initial ∈
          indexedFragmentStates selectedConjunctions := by
        rw [indexedFragmentStates, mem_foldl_union_iff]
        exact Or.inr ⟨indexed, hIndexed, Finset.mem_image.mpr
          ⟨indexed.1.2.initial, hConjunctionInitial indexed.1 hEntry, rfl⟩⟩
      simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
        hIndexedState]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- The edges leaving an exclusive-offer root are its branch, wait and default
edges; the two copied families are tagged and never source the root. -/
theorem buildExclusiveOfferAutomaton_root_edge_cases
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildExclusiveOfferAutomaton alphabet branches
      elseAutomaton branchAutomata).edges)
    (hSource : edge.source = TypeAutomatonState.root) :
    (∃ indexed ∈ branchAutomata.zipIdx,
        edge.current = {indexed.1.1} ∧
          edge.future = .at (childState (indexed.2 + 1)
            indexed.1.2.initial) {indexed.1.1} ∧
          edge.target = childState (indexed.2 + 1) indexed.1.2.initial ∧
          edge.label = .visible (TypeLabel.message indexed.1.1.1
            indexed.1.1.2)) ∨
      (∃ environment : TypeEnvironment,
        edge.current = (environment.future.image typeNeed) ∩
            typeBranchActions branches ∧
          edge.future = .at TypeAutomatonState.root
            ((environment.future.image typeNeed) ∩
              typeBranchActions branches) ∧
          edge.target = TypeAutomatonState.root) ∨
      (edge.current = ∅ ∧
        edge.future = .at (childState 0 elseAutomaton.initial) ∅ ∧
        edge.target = childState 0 elseAutomaton.initial) := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with (((hElseCopy | hBranchCopy) | hBranch) | hWait) | hElse
  · -- a copied default edge is tagged, so it cannot source the root
    exfalso
    rw [childPendingEdges, Finset.mem_image] at hElseCopy
    obtain ⟨childEdge, -, hEq⟩ := hElseCopy
    rw [← hEq] at hSource
    simp [childPendingEdge, childState] at hSource
  · -- a copied branch edge is tagged too
    exfalso
    rw [indexedFragmentEdges, mem_foldl_union_iff] at hBranchCopy
    rcases hBranchCopy with hEmpty | ⟨indexed, -, hIn⟩
    · exact absurd hEmpty (Finset.notMem_empty _)
    · rw [childPendingEdges, Finset.mem_image] at hIn
      obtain ⟨childEdge, -, hEq⟩ := hIn
      rw [← hEq] at hSource
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, hIndexed, hIn⟩
    · exact absurd hEmpty (Finset.notMem_empty _)
    · rw [Finset.mem_image] at hIn
      obtain ⟨environment, -, hEq⟩ := hIn
      exact Or.inl ⟨indexed, hIndexed, by rw [← hEq], by rw [← hEq],
        by rw [← hEq], by rw [← hEq]⟩
  · rw [Finset.mem_image] at hWait
    obtain ⟨environment, -, hEq⟩ := hWait
    exact Or.inr (Or.inl ⟨environment, by rw [← hEq], by rw [← hEq],
      by rw [← hEq]⟩)
  · rw [Finset.mem_image] at hElse
    obtain ⟨environment, -, hEq⟩ := hElse
    exact Or.inr (Or.inr ⟨by rw [← hEq], by rw [← hEq], by rw [← hEq]⟩)

end

end Pact
