import Anvilpp.PactTypes.Automata.BuildParallelAutomaton

/-!
# Indexed branch-fragment helpers and the exclusive/conjunctive/selected offer automata
-/

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

def indexedFragmentStates
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childStates (indexed.2 + 1) indexed.1.2) ∅

def indexedFragmentAccepting
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childAccepting (indexed.2 + 1) indexed.1.2) ∅


def indexedFragmentEdges
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset PendingAutomatonEdge :=
  automata.zipIdx.foldl (fun edges indexed =>
    edges ∪ childPendingEdges (indexed.2 + 1) indexed.1.2) ∅

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

/--
Build an exclusive offer with one fresh root.

Child `0` is the else continuation; children `1..n` are branch continuations.
From the root there are three kinds of edges:

* `branchEdges`: fire an immediately enabled and resolved branch;
* `waitEdges`: remain at the root while a branch may still arrive this cycle;
* `elseEdges`: select the else continuation once no branch can still arrive.

All three root families are gated on `alphabet`, exactly as the semantic
`xoffer_*` rules are: a partly-declared offer emits no root edge at all.
-/
def buildExclusiveOfferAutomaton (signature : TypeAlphabet)
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 elseAutomaton ∪
    indexedFragmentStates branchAutomata
  let accepting := childAccepting 0 elseAutomaton ∪
    indexedFragmentAccepting branchAutomata
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let branchEdges : Finset PendingAutomatonEdge := branchAutomata.zipIdx.foldl
    (fun edges indexed =>
      let index := indexed.2
      let action := indexed.1.1
      let automaton := indexed.1.2
      let newEdges : Finset PendingAutomatonEdge :=
        let enablingEnvironments := signature.localEnvironments.filter fun environment =>
          typeNeed action ∈ environment.immediate ∧
          needs ∩ environment.future = ∅ ∧
          ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
        enablingEnvironments.image fun environment =>
          { source := TypeAutomatonState.root
            environment := environment
            label := .visible (TypeLabel.message action.1 action.2)
            current := {action}
            future := .at (childState (index + 1) automaton.initial) ∅
            target := childState (index + 1) automaton.initial }
      edges ∪ newEdges) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.future ≠ ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting
    (childPendingEdges 0 elseAutomaton ∪ indexedFragmentEdges branchAutomata ∪
      branchEdges ∪ waitEdges ∪ elseEdges)

/-- Wait and else edges carry explicit `clock = false` guards; branch edges
require an immediate need, which a clocked environment (empty `immediate`)
cannot supply. -/
theorem buildExclusiveOfferAutomaton_clockEdgesAreTock
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseClock : elseAutomaton.ClockEdgesAreTock)
    (hBranchClock : ∀ entry ∈ branchAutomata, entry.2.ClockEdgesAreTock) :
    (buildExclusiveOfferAutomaton signature alphabet branches elseAutomaton
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
      rw [TypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hBranchTargets : ∀ entry ∈ branchAutomata,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hBranchInitial : ∀ entry ∈ branchAutomata,
      entry.2.initial ∈ entry.2.states) :
    (buildExclusiveOfferAutomaton signature alphabet branches elseAutomaton
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

/-- Legacy unspecialized conjunction builder, retained for the generic graph
lemmas about an arbitrary conjunction child.  The compiler uses the selected
builder below, which removes only the all-else outcome after an enabled branch
has witnessed entry. -/
def buildConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment) : AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 conjunction ∪
    childStates 1 elseAutomaton
  let accepting := childAccepting 0 conjunction ∪ childAccepting 1 elseAutomaton
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let enabledEdges : Finset PendingAutomatonEdge :=
    let enablingEnvironments := signature.localEnvironments.filter fun environment =>
      needs ∩ environment.immediate ≠ ∅
    enablingEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at (childState 0 conjunction.initial) ∅
        target := childState 0 conjunction.initial }
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 1 elseAutomaton.initial) ∅
        target := childState 1 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting
    (childPendingEdges 0 conjunction ∪ childPendingEdges 1 elseAutomaton ∪
      enabledEdges ∪ waitEdges ∪ elseEdges)

theorem buildConjunctiveOfferAutomaton_futureTargetsInStates
    (signature : TypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton conjunction : AutomatonFragment)
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : conjunction.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : conjunction.initial ∈ conjunction.states) :
    (buildConjunctiveOfferAutomaton signature branches elseAutomaton
      conjunction).FutureTargetsInStates := by
  classical
  intro edge hEdge target removed hFuture
  simp only [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
    Finset.mem_union] at hEdge
  rcases hEdge with ((((hConjunction | hElse) | hEnabled) | hWait) | hResolved)
  · have hTarget := childPendingEdges_futureTargetsInStates 0 conjunction
      hConjunctionTargets edge hConjunction target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · have hTarget := childPendingEdges_futureTargetsInStates 1 elseAutomaton
      hElseTargets edge hElse target removed hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment, hTarget]
  · simp only [Finset.mem_image, Finset.mem_filter] at hEnabled
    rcases hEnabled with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hConjunctionInitial]
  · simp only [Finset.mem_image, Finset.mem_filter] at hWait
    rcases hWait with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment]
  · simp only [Finset.mem_image, Finset.mem_filter] at hResolved
    rcases hResolved with ⟨environment, _, rfl⟩
    simp only at hFuture
    cases hFuture
    simp [buildConjunctiveOfferAutomaton, finishAutomatonFragment,
      childStates, childState, hElseInitial]

/-- Post-construction conjunctive-offer builder.  Each enabled witness enters
its own copy of the singleton product with that witness's synthetic else arm
removed; the other singleton else arms remain available.

All three root families are gated on `alphabet`, exactly as the semantic
`offer_*` rules are: a partly-declared offer emits no root edge at all. -/
def buildSelectedConjunctiveOfferAutomaton (signature : TypeAlphabet)
    (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    AutomatonFragment := by
  classical
  let states := {TypeAutomatonState.root} ∪ childStates 0 elseAutomaton ∪
    indexedFragmentStates selectedConjunctions
  let accepting := childAccepting 0 elseAutomaton ∪
    indexedFragmentAccepting selectedConjunctions
  let needs := typeBranchNeeds branches
  let actions := typeBranchActions branches
  let enabledEdges : Finset PendingAutomatonEdge :=
    selectedConjunctions.zipIdx.foldl (fun edges indexed =>
      let index := indexed.2
      let action := indexed.1.1
      let conjunction := indexed.1.2
      let enablingEnvironments := signature.localEnvironments.filter
        fun environment => typeNeed action ∈ environment.immediate ∧
          ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
      edges ∪ enablingEnvironments.image fun environment =>
        { source := TypeAutomatonState.root
          environment := environment
          label := .visible TypeLabel.silent
          current := ∅
          future := .at (childState (index + 1) conjunction.initial) ∅
          target := childState (index + 1) conjunction.initial }) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    waitingEnvironments.image fun environment =>
      let waiting := (environment.future.image typeNeed) ∩ actions
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := waiting
        future := .at TypeAutomatonState.root waiting
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments := signature.localEnvironments.filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 0 elseAutomaton.initial) ∅
        target := childState 0 elseAutomaton.initial }
  exact finishAutomatonFragment states .root accepting
    (childPendingEdges 0 elseAutomaton ∪
      indexedFragmentEdges selectedConjunctions ∪ enabledEdges ∪
        waitEdges ∪ elseEdges)

/-- Wait and else edges carry explicit `clock = false` guards; enabled edges
require an immediate need, which a clocked environment cannot supply. -/
theorem buildSelectedConjunctiveOfferAutomaton_clockEdgesAreTock
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseClock : elseAutomaton.ClockEdgesAreTock)
    (hConjunctionClock : ∀ entry ∈ selectedConjunctions,
      entry.2.ClockEdgesAreTock) :
    (buildSelectedConjunctiveOfferAutomaton signature alphabet branches
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
      rw [TypeAlphabet.immediate_eq_empty_of_mem_localEnvironments_of_clock
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
    (signature : TypeAlphabet) (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (hElseTargets : elseAutomaton.FutureTargetsInStates)
    (hConjunctionTargets : ∀ entry ∈ selectedConjunctions,
      entry.2.FutureTargetsInStates)
    (hElseInitial : elseAutomaton.initial ∈ elseAutomaton.states)
    (hConjunctionInitial : ∀ entry ∈ selectedConjunctions,
      entry.2.initial ∈ entry.2.states) :
    (buildSelectedConjunctiveOfferAutomaton signature alphabet branches
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

end

end Pact
