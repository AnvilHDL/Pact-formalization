import Anvilpp.PactTypes.Spec.Automata.BuildParallelAutomaton

namespace Pact

noncomputable section

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


def indexedFragmentCompletes
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState :=
  automata.zipIdx.foldl (fun states indexed =>
    states ∪ childCompletes (indexed.2 + 1) indexed.1.2) ∅

/-- `c(⊕(τ₀,B)) = c(∧(τ₀,B))`: the head gate, and either the default or some
selected branch. -/
def offerRootCompletes (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (branchAutomata : List (BareMessage × AutomatonFragment)) :
    Finset TypeAutomatonState := by
  classical
  exact
    if (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) ∧
        (elseAutomaton.initial ∈ elseAutomaton.completes ∨
          ∃ entry ∈ branchAutomata, entry.2.initial ∈ entry.2.completes) then
      {TypeAutomatonState.root}
    else ∅

def indexedFragmentEdges
    (automata : List (BareMessage × AutomatonFragment)) :
    Finset PendingAutomatonEdge :=
  automata.zipIdx.foldl (fun edges indexed =>
    edges ∪ childPendingEdges (indexed.2 + 1) indexed.1.2) ∅

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
def buildExclusiveOfferAutomaton
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
        let enablingEnvironments :=
          (alphabet.localEnvironments).filter fun environment =>
          typeNeed action ∈ environment.immediate ∧
          needs ∩ environment.future = ∅ ∧
          ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
        enablingEnvironments.image fun environment =>
          { source := TypeAutomatonState.root
            environment := environment
            label := .visible (TypeLabel.message action.1 action.2)
            current := {action}
            future := .at TypeAutomatonState.root actions
            target := childState (index + 1) automaton.initial }
      edges ∪ newEdges) ∅
  let waitEdges : Finset PendingAutomatonEdge :=
    let waitingEnvironments :=
      (alphabet.localEnvironments).filter fun environment =>
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
    let resolvedEnvironments :=
      (alphabet.localEnvironments).filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := ∅
        future := .at TypeAutomatonState.root actions
        target := childState 0 elseAutomaton.initial }
  let completes := childCompletes 0 elseAutomaton ∪
    indexedFragmentCompletes branchAutomata ∪
    offerRootCompletes alphabet branches elseAutomaton branchAutomata
  exact finishAutomatonFragment states .root accepting completes
    (childPendingEdges 0 elseAutomaton ∪ indexedFragmentEdges branchAutomata ∪
      branchEdges ∪ waitEdges ∪ elseEdges)

/-- Post-construction conjunctive-offer builder.  Each enabled witness enters
its own copy of the singleton product with that witness's synthetic else arm
removed; the other singleton else arms remain available.

All three root families are gated on `alphabet`, exactly as the semantic
`offer_*` rules are: a partly-declared offer emits no root edge at all. -/
def buildSelectedConjunctiveOfferAutomaton
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
      let enablingEnvironments := (alphabet.localEnvironments).filter
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
    let waitingEnvironments :=
      (alphabet.localEnvironments).filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future ≠ ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    waitingEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at TypeAutomatonState.root actions
        target := TypeAutomatonState.root }
  let elseEdges : Finset PendingAutomatonEdge :=
    let resolvedEnvironments :=
      (alphabet.localEnvironments).filter fun environment =>
      environment.clock = false ∧
      needs ∩ environment.immediate = ∅ ∧
      needs ∩ environment.future = ∅ ∧
      ∀ branch ∈ branches, branch.1 ∈ alphabet.actions
    resolvedEnvironments.image fun environment =>
      { source := TypeAutomatonState.root
        environment := environment
        label := .visible TypeLabel.silent
        current := actions
        future := .at (childState 0 elseAutomaton.initial) actions
        target := childState 0 elseAutomaton.initial }
  let completes := childCompletes 0 elseAutomaton ∪
    indexedFragmentCompletes selectedConjunctions ∪
    offerRootCompletes alphabet branches elseAutomaton selectedConjunctions
  exact finishAutomatonFragment states .root accepting completes
    (childPendingEdges 0 elseAutomaton ∪
      indexedFragmentEdges selectedConjunctions ∪ enabledEdges ∪
        waitEdges ∪ elseEdges)

end

end Pact
