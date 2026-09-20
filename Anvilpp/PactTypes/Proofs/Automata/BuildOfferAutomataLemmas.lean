import Anvilpp.PactTypes.Spec.Automata.BuildOfferAutomataDefs

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
    ∀ edge ∈ childPendingEdges index fragment, ∀ target,
      edge.future.referenced = some target →
        target ∈ childStates index fragment := by
  classical
  intro edge hEdge target hFuture
  simp only [childPendingEdges, Finset.mem_image] at hEdge
  rcases hEdge with ⟨childEdge, hChildEdge, rfl⟩
  cases hSpec : childEdge.future with
  | explicit offers =>
      simp [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
  | «at» childTarget childRemoved =>
      simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
      cases hFuture
      have hChildTarget := hTargets childEdge hChildEdge childTarget
        (by simp [hSpec, FutureSpec.referenced])
      simp [childStates, childState, hChildTarget]

  | atUnion offers childTarget childRemoved =>
      simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
      cases hFuture
      have hChildTarget := hTargets childEdge hChildEdge childTarget
        (by simp [hSpec, FutureSpec.referenced])
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
    ∀ edge ∈ indexedFragmentEdges automata, ∀ target,
      edge.future.referenced = some target →
        target ∈ indexedFragmentStates automata := by
  classical
  intro edge hEdge target hFuture
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
        simp [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
    | «at» childTarget childRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hTargets indexed.1 hEntry childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
        rw [indexedFragmentStates, mem_foldl_union_iff]
        right
        refine ⟨indexed, hIndexed, ?_⟩
        simp [childStates, childState, hChildTarget]

    | atUnion offers childTarget childRemoved =>
        simp only [childPendingEdge, childFutureSpec, hSpec, FutureSpec.referenced] at hFuture
        cases hFuture
        have hChildTarget := hTargets indexed.1 hEntry childEdge hChildEdge
          childTarget (by simp [hSpec, FutureSpec.referenced])
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
    (_hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
      branchAutomata).FutureTargetsInStates := by
  classical
  intro edge hEdge target hFuture
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hIndexed) | hBranch) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target hFuture
    simp [buildExclusiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates branchAutomata
      hBranchTargets edge hIndexed target hFuture
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
      simp [buildExclusiveOfferAutomaton, finishAutomatonFragment]
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
      childStates, childState]

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
      obtain ⟨environment, ⟨hEnvMem, hEnabledNeed⟩, rfl⟩ := hNewEdge
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
  intro edge hEdge target hFuture
  simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hElse | hConjunction) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 elseAutomaton
      hElseTargets edge hElse target hFuture
    simp [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := indexedFragment_futureTargetsInStates
      selectedConjunctions hConjunctionTargets edge hConjunction target
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
        simp [hValue]
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
          edge.future = .at TypeAutomatonState.root
            (typeBranchActions branches) ∧
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
        edge.future = .at TypeAutomatonState.root
          (typeBranchActions branches) ∧
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

/-- Complementing an admissible environment menu yields declared actions. -/
theorem typeNeed_image_subset_actions {offers actions : Finset BareMessage}
    (h : offers ⊆ actions.image typeNeed) : offers.image typeNeed ⊆ actions := by
  intro action ha
  obtain ⟨need, hNeed, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨original, hOriginal, rfl⟩ := Finset.mem_image.mp (h hNeed)
  simpa [typeNeed] using hOriginal

theorem buildExclusiveOfferAutomaton_root_current_subset
    (alphabet : PactTypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment) (branchAutomata : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildExclusiveOfferAutomaton alphabet branches elseAutomaton branchAutomata).edges)
    (hSource : edge.source = .root) : edge.current ⊆ alphabet.actions := by
  classical
  simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment, Finset.mem_union,
    childPendingEdges, Finset.mem_image, Finset.mem_filter] at hEdge
  rcases hEdge with (((hElse | hIndexed) | hBranch) | hWait) | hDefault
  · obtain ⟨child, _, rfl⟩ := hElse
    simp [childPendingEdge, childState] at hSource
  · rw [indexedFragmentEdges, mem_foldl_union_iff] at hIndexed
    rcases hIndexed with hEmpty | ⟨indexed, _, hChild⟩
    · simp at hEmpty
    · obtain ⟨child, _, rfl⟩ := Finset.mem_image.mp hChild
      simp [childPendingEdge, childState] at hSource
  · rw [mem_foldl_union_iff] at hBranch
    rcases hBranch with hEmpty | ⟨indexed, _, hRoot⟩
    · simp at hEmpty
    · obtain ⟨env, hEnv, rfl⟩ := Finset.mem_image.mp hRoot
      obtain ⟨hLocal, hNeed, _⟩ := Finset.mem_filter.mp hEnv
      have hBound := typeNeed_image_subset_actions
        (PactTypeAlphabet.environment_wellFormed hLocal).2.2.1
      simpa [typeNeed] using hBound (Finset.mem_image_of_mem typeNeed hNeed)
  · obtain ⟨env, ⟨hLocal, _⟩, rfl⟩ := hWait
    exact Finset.Subset.trans Finset.inter_subset_left
      (typeNeed_image_subset_actions (PactTypeAlphabet.environment_wellFormed hLocal).2.2.2)
  · obtain ⟨env, _, rfl⟩ := hDefault
    exact Finset.empty_subset _

/-- An exclusive root exposes exactly the declared branch heads. -/
theorem buildExclusiveOfferAutomaton_offersAt_root
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hHeads : branchAutomata.map Prod.fst = branches.map Prod.fst) :
    ({ states := (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
         branchAutomata).states
       edges := (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
         branchAutomata).edges } : PendingAutomaton).offersAt
        TypeAutomatonState.root =
      typeBranchActions branches ∩ alphabet.actions := by
  classical
  apply Finset.Subset.antisymm
  · intro action hAction
    simp only [PendingAutomaton.offersAt, Finset.mem_biUnion,
      Finset.mem_filter] at hAction
    obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hAction
    by_cases hTock : edge.label.semantic = TypeLabel.tock
    · rw [if_pos hTock] at hIn
      exact absurd hIn (Finset.notMem_empty _)
    · rw [if_neg hTock] at hIn
      refine Finset.mem_inter.mpr ⟨?_,
        buildExclusiveOfferAutomaton_root_current_subset alphabet branches elseAutomaton
          branchAutomata edge hEdge hSource hIn⟩
      rcases buildExclusiveOfferAutomaton_root_edge_cases alphabet branches
          elseAutomaton branchAutomata edge hEdge hSource with
        ⟨indexed, hIndexed, hCurrent, hFuture, -, -⟩ |
        ⟨environment, hCurrent, hFuture, -⟩ | ⟨hCurrent, hFuture, -⟩
      · rw [hCurrent, Finset.mem_singleton] at hIn
        subst hIn
        have hGet : branchAutomata[indexed.2]? = some indexed.1 := by
          rw [← List.mk_mem_zipIdx_iff_getElem?]
          simpa using hIndexed
        have hMem : indexed.1 ∈ branchAutomata := List.mem_of_getElem? hGet
        have hHead : indexed.1.1 ∈ branchAutomata.map Prod.fst :=
          List.mem_map_of_mem hMem
        rw [hHeads] at hHead
        exact List.mem_toFinset.mpr hHead
      · rw [hCurrent] at hIn
        exact (Finset.mem_inter.mp hIn).2
      · rw [hCurrent] at hIn
        exact absurd hIn (Finset.notMem_empty _)
  · intro action hAction
    obtain ⟨hAction, hDeclaredAction⟩ := Finset.mem_inter.mp hAction
    rw [typeBranchActions, List.mem_toFinset, List.mem_map] at hAction
    obtain ⟨branch, hBranch, rfl⟩ := hAction
    have hHead : branch.1 ∈ branchAutomata.map Prod.fst := by
      rw [hHeads]
      exact List.mem_map_of_mem hBranch
    rw [List.mem_map] at hHead
    obtain ⟨entry, hEntry, hEntryHead⟩ := hHead
    obtain ⟨index, hGet⟩ := List.getElem?_of_mem hEntry
    have hIndexed : (entry, index) ∈ branchAutomata.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr hGet
    have hDeclared : entry.1 ∈ alphabet.actions := by
      rw [hEntryHead]
      exact hDeclaredAction
    set environment : TypeEnvironment :=
      { immediate := {typeNeed entry.1}, future := ∅, clock := false }
      with hEnvironmentDef
    set edge : PendingAutomatonEdge :=
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible (TypeLabel.message entry.1.1 entry.1.2)
        current := {entry.1}
        future := .at TypeAutomatonState.root (typeBranchActions branches)
        target := childState (index + 1) entry.2.initial }
      with hEdgeDef
    refine Finset.mem_biUnion.mpr ⟨edge, Finset.mem_filter.mpr ⟨?_, rfl⟩, ?_⟩
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [mem_foldl_union_iff]
      refine Or.inr ⟨(entry, index), hIndexed, ?_⟩
      rw [Finset.mem_image]
      refine ⟨environment, Finset.mem_filter.mpr
        ⟨PactTypeAlphabet.singleton_need_mem_localEnvironments alphabet
          hDeclared, Finset.mem_singleton_self _, Finset.inter_empty _⟩, rfl⟩
    · rw [if_neg (by
        rw [hEdgeDef]
        simp [AutomatonConstructionLabel.semantic, TypeLabel.message]), hEdgeDef]
      simp only [Finset.mem_singleton]
      exact hEntryHead.symm

/-- The states an exclusive-offer root can reach within the cycle: the default
entry, the branch entries, and possibly the root itself via a wait loop. -/
def exclusiveOfferEntries (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  insert (childState 0 elseAutomaton.initial)
    (branchAutomata.zipIdx.map fun indexed =>
      childState (indexed.2 + 1) indexed.1.2.initial).toFinset

/-- The entry states of a compiled conjunctive offer: the copied default entry
and one copied entry per selected conjunction. -/
def conjunctiveOfferEntries (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  insert (childState 0 elseAutomaton.initial)
    (selectedConjunctions.zipIdx.map fun indexed =>
      childState (indexed.2 + 1) indexed.1.2.initial).toFinset

/-- A root's non-clock targets are itself and the branch entries. -/
theorem buildExclusiveOfferAutomaton_menuStep_root_subset
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    ({ states := (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
         branchAutomata).states
       edges := (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
         branchAutomata).edges } : PendingAutomaton).menuStep
        TypeAutomatonState.root ⊆
      insert TypeAutomatonState.root
        (exclusiveOfferEntries elseAutomaton branchAutomata) := by
  classical
  intro state hState
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter] at hState
  obtain ⟨edge, ⟨hEdge, hSource⟩, hIn⟩ := hState
  by_cases hTock : edge.label.semantic = TypeLabel.tock
  · rw [if_pos hTock] at hIn
    exact absurd hIn (Finset.notMem_empty _)
  · rw [if_neg hTock] at hIn
    rcases buildExclusiveOfferAutomaton_root_edge_cases alphabet branches
        elseAutomaton branchAutomata edge hEdge hSource with
      ⟨indexed, hIndexed, -, -, hTarget, -⟩ |
      ⟨environment, -, -, hTarget⟩ | ⟨-, -, hTarget⟩
    · rw [hTarget, Finset.mem_singleton] at hIn
      subst state
      apply Finset.mem_insert_of_mem
      simp only [exclusiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
        List.mem_map]
      exact Or.inr ⟨indexed, hIndexed, rfl⟩
    · rw [hTarget, Finset.mem_singleton] at hIn
      subst hIn
      exact Finset.mem_insert_self _ _
    · rw [hTarget, Finset.mem_singleton] at hIn
      subst hIn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- And it references every one of them: the default is taken by the empty
environment, each branch by the environment demanding exactly its head. -/
theorem buildExclusiveOfferAutomaton_entries_subset_menuStep_root
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hHeads : branchAutomata.map Prod.fst = branches.map Prod.fst)
    (hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    exclusiveOfferEntries elseAutomaton branchAutomata ⊆
      ({ states := (buildExclusiveOfferAutomaton alphabet branches
           elseAutomaton branchAutomata).states
         edges := (buildExclusiveOfferAutomaton alphabet branches elseAutomaton
           branchAutomata).edges } : PendingAutomaton).menuStep
        TypeAutomatonState.root := by
  classical
  intro state hState
  simp only [exclusiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
    List.mem_map] at hState
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter]
  rcases hState with rfl | ⟨indexed, hIndexed, rfl⟩
  · -- the default entry, taken when nothing is demanded or pending
    refine ⟨{ source := TypeAutomatonState.root
              environment := TypeEnvironment.empty
              label := .visible TypeLabel.silent
              current := ∅
              future := .at TypeAutomatonState.root (typeBranchActions branches)
              target := childState 0 elseAutomaton.initial },
      ⟨?_, rfl⟩, ?_⟩
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inr ?_
      rw [Finset.mem_image]
      refine ⟨TypeEnvironment.empty, Finset.mem_filter.mpr
        ⟨PactTypeAlphabet.empty_mem_localEnvironments alphabet, rfl, ?_, ?_⟩, rfl⟩
      · simp [TypeEnvironment.empty]
      · simp [TypeEnvironment.empty]
    · rw [if_neg (by simp [AutomatonConstructionLabel.semantic,
        TypeLabel.silent])]
      exact Finset.mem_singleton_self _
  · -- a branch entry, taken by the environment demanding exactly its head
    have hGet : branchAutomata[indexed.2]? = some indexed.1 := by
      rw [← List.mk_mem_zipIdx_iff_getElem?]
      simpa using hIndexed
    have hMem : indexed.1 ∈ branchAutomata := List.mem_of_getElem? hGet
    have hDeclared : indexed.1.1 ∈ alphabet.actions := by
      have hHead : indexed.1.1 ∈ branchAutomata.map Prod.fst :=
        List.mem_map_of_mem hMem
      rw [hHeads, List.mem_map] at hHead
      obtain ⟨branch, hBranch, hEq⟩ := hHead
      rw [← hEq]
      exact hGuard branch hBranch
    set environment : TypeEnvironment :=
      { immediate := {typeNeed indexed.1.1}, future := ∅, clock := false }
      with hEnvironmentDef
    refine ⟨{ source := TypeAutomatonState.root
              environment := environment
              label := .visible (TypeLabel.message indexed.1.1.1 indexed.1.1.2)
              current := {indexed.1.1}
              future := .at TypeAutomatonState.root (typeBranchActions branches)
              target := childState (indexed.2 + 1) indexed.1.2.initial },
      ⟨?_, rfl⟩, ?_⟩
    · simp only [buildExclusiveOfferAutomaton, finishAutomatonFragment,
        Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [mem_foldl_union_iff]
      refine Or.inr ⟨indexed, hIndexed, ?_⟩
      rw [Finset.mem_image]
      refine ⟨environment, Finset.mem_filter.mpr
        ⟨PactTypeAlphabet.singleton_need_mem_localEnvironments alphabet
          hDeclared, Finset.mem_singleton_self _, Finset.inter_empty _⟩, rfl⟩
    · rw [if_neg (by simp [AutomatonConstructionLabel.semantic,
        TypeLabel.message])]
      exact Finset.mem_singleton_self _

/-- A conjunctive-offer root references nothing beyond itself and those
entries. -/
theorem buildSelectedConjunctiveOfferAutomaton_menuStep_root_subset
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    ({ states := (buildSelectedConjunctiveOfferAutomaton alphabet branches
         elseAutomaton selectedConjunctions).states
       edges := (buildSelectedConjunctiveOfferAutomaton alphabet branches
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
    simp only [buildSelectedConjunctiveOfferAutomaton, finishAutomatonFragment,
      Finset.mem_union] at hEdge
    rcases hEdge with
      ((((hElseCopy | hConjunctionCopy) | hEnabled) | hWait) | hResolved)
    · -- a copied default edge is tagged, so it cannot source the root
      exfalso
      rw [childPendingEdges, Finset.mem_image] at hElseCopy
      obtain ⟨childEdge, -, hEq⟩ := hElseCopy
      rw [← hEq] at hSource
      simp [childPendingEdge, childState] at hSource
    · -- a copied conjunction edge is tagged too
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

/-- And it references every one of them: the default is taken by the empty
environment, each conjunction by the environment demanding exactly its head. -/
theorem buildSelectedConjunctiveOfferAutomaton_entries_subset_menuStep_root
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hHeads : selectedConjunctions.map Prod.fst = branches.map Prod.fst)
    (hGuard : ∀ branch ∈ branches, branch.1 ∈ alphabet.actions) :
    conjunctiveOfferEntries elseAutomaton selectedConjunctions ⊆
      ({ states := (buildSelectedConjunctiveOfferAutomaton alphabet branches
           elseAutomaton selectedConjunctions).states
         edges := (buildSelectedConjunctiveOfferAutomaton alphabet branches
           elseAutomaton selectedConjunctions).edges } :
          PendingAutomaton).menuStep TypeAutomatonState.root := by
  classical
  intro state hState
  simp only [conjunctiveOfferEntries, Finset.mem_insert, List.mem_toFinset,
    List.mem_map] at hState
  simp only [PendingAutomaton.menuStep, Finset.mem_biUnion,
    Finset.mem_filter]
  rcases hState with rfl | ⟨indexed, hIndexed, rfl⟩
  · -- the default entry, taken when nothing is demanded or pending
    refine ⟨{ source := TypeAutomatonState.root
              environment := TypeEnvironment.empty
              label := .visible TypeLabel.silent
              current := typeBranchActions branches ∩ alphabet.actions
              future := .at (childState 0 elseAutomaton.initial)
                (typeBranchActions branches ∩ alphabet.actions)
              target := childState 0 elseAutomaton.initial },
      ⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      refine Or.inr ?_
      rw [Finset.mem_image]
      refine ⟨TypeEnvironment.empty, Finset.mem_filter.mpr
        ⟨PactTypeAlphabet.empty_mem_localEnvironments alphabet, rfl, ?_, ?_⟩, rfl⟩
      · simp [TypeEnvironment.empty]
      · simp [TypeEnvironment.empty]
    · rw [if_neg (by simp [AutomatonConstructionLabel.semantic,
        TypeLabel.silent])]
      exact Finset.mem_singleton_self _
  · -- a conjunction entry, taken by the environment demanding exactly its head
    have hGet : selectedConjunctions[indexed.2]? = some indexed.1 := by
      rw [← List.mk_mem_zipIdx_iff_getElem?]
      simpa using hIndexed
    have hMem : indexed.1 ∈ selectedConjunctions := List.mem_of_getElem? hGet
    have hDeclared : indexed.1.1 ∈ alphabet.actions := by
      have hHead : indexed.1.1 ∈ selectedConjunctions.map Prod.fst :=
        List.mem_map_of_mem hMem
      rw [hHeads, List.mem_map] at hHead
      obtain ⟨branch, hBranch, hEq⟩ := hHead
      rw [← hEq]
      exact hGuard branch hBranch
    set environment : TypeEnvironment :=
      { immediate := {typeNeed indexed.1.1}, future := ∅, clock := false }
      with hEnvironmentDef
    refine ⟨{ source := TypeAutomatonState.root
              environment := environment
              label := .visible TypeLabel.silent
              current := ∅
              future := .at (childState (indexed.2 + 1) indexed.1.2.initial) ∅
              target := childState (indexed.2 + 1) indexed.1.2.initial },
      ⟨?_, rfl⟩, ?_⟩
    · simp only [buildSelectedConjunctiveOfferAutomaton,
        finishAutomatonFragment, Finset.mem_union]
      refine Or.inl (Or.inl (Or.inr ?_))
      rw [mem_foldl_union_iff]
      refine Or.inr ⟨indexed, hIndexed, ?_⟩
      rw [Finset.mem_image]
      refine ⟨environment, Finset.mem_filter.mpr
        ⟨PactTypeAlphabet.singleton_need_mem_localEnvironments alphabet
          hDeclared, Finset.mem_singleton_self _⟩, rfl⟩
    · rw [if_neg (by simp [AutomatonConstructionLabel.semantic,
        TypeLabel.silent])]
      exact Finset.mem_singleton_self _

end

end Pact
