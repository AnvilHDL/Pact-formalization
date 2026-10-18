import Anvilpp.PactTypes.Spec.Automata.BuildOfferAutomataDefs

namespace Pact

noncomputable section

/-- Firing enters the residual for exactly the enabled subset, consuming its heads. -/
def conjunctiveFiringEdges (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType))
    (residuals : List (Finset Nat × AutomatonFragment)) : Finset PendingAutomatonEdge := by
  classical
  let current := typeBranchActions branches ∩ alphabet.actions
  exact residuals.zipIdx.foldl (fun edges entry =>
    let selected := entry.1.1
    let residual := entry.1.2
    let target := childState (entry.2 + 1) residual.initial
    let environments := alphabet.localEnvironments.filter fun env =>
      selected.Nonempty ∧ typeEnabledBranches env branches = selected
    edges ∪ environments.image fun env =>
      { source := .root
        environment := env
        label := .visible (typeBranchBatchLabel branches selected)
        current := current
        future := .at target current
        target := target }) ∅

/-- One root with a default copy and disjoint copies of all nonempty subset residuals. -/
def buildAtomicConjunctiveOfferAutomaton (alphabet : PactTypeAlphabet)
    (branches : List (BareMessage × PactType)) (elseAutomaton : AutomatonFragment)
    (residuals : List (Finset Nat × AutomatonFragment)) : AutomatonFragment := by
  classical
  let states := {.root} ∪ childStates 0 elseAutomaton ∪ indexedFragmentStates residuals
  let accepting := childAccepting 0 elseAutomaton ∪ indexedFragmentAccepting residuals
  let needs := typeBranchNeeds branches
  let current := typeBranchActions branches ∩ alphabet.actions
  let waitEdges : Finset PendingAutomatonEdge :=
    (alphabet.localEnvironments.filter fun env =>
      env.clock = false ∧ needs ∩ env.immediate = ∅ ∧ needs ∩ env.future ≠ ∅).image
      fun env =>
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := current
          future := .at .root current
          target := .root }
  let elseEdges : Finset PendingAutomatonEdge :=
    (alphabet.localEnvironments.filter fun env =>
      env.clock = false ∧ needs ∩ env.immediate = ∅ ∧ needs ∩ env.future = ∅).image
      fun env =>
        { source := .root
          environment := env
          label := .visible TypeLabel.silent
          current := current
          future := .at (childState 0 elseAutomaton.initial) current
          target := childState 0 elseAutomaton.initial }
  let completes := childCompletes 0 elseAutomaton ∪ indexedFragmentCompletes residuals ∪
    offerRootCompletes alphabet branches elseAutomaton residuals
  exact finishAutomatonFragment states .root accepting completes
    (childPendingEdges 0 elseAutomaton ∪ indexedFragmentEdges residuals ∪
      conjunctiveFiringEdges alphabet branches residuals ∪ waitEdges ∪ elseEdges)

end

end Pact
