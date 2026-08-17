import Anvilpp.PactTypes.Correspondence.CorrespondenceOfferBranchLeaf

/-!
# offer regular leaf
-/

namespace Pact

noncomputable section

/-- Conjunctive-offer closure packages the generated branch product and its
enabled/else/wait root classifiers. -/
private theorem compilationFutureCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.offer elseType branches) :=
  sorry
private theorem compilationCompletingCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationCompletingCorrect signature (.offer elseType branches) :=
  sorry
private theorem compilationFragmentStepCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hFuture : CompilationFutureCorrect signature (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.offer elseType branches) :=
  sorry
theorem conjunctiveOffer_execution_completion_regression
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    let branches : List (BareMessage × PactType) := [(action, .tock)]
    let processType : PactType := .offer .tock branches
    let fragment := compileTypeFuel signature
      (typeCompilationFuel processType) processType
    let execution := sequenceExecutionAutomaton fragment
    processType.CanCompleteBeforeTock = false ∧
      ∃ completed ∈ execution.futureReachable .root,
        completed ∈ fragment.completing :=
  sorry
theorem conjunctiveOffer_not_sequenceExecutionCorrect
    (signature : TypeAlphabet) (action : BareMessage)
    (hAvailable : typeNeed action ∈ signature.localEnvironmentActions) :
    ¬ CompilationSequenceExecutionCorrect signature
      (.offer .tock [(action, .tock)]) :=
  sorry
private theorem canCompleteBeforeTock_parallelTypeBranches
    (branches : List (BareMessage × PactType)) :
    (parallelTypeBranches branches).CanCompleteBeforeTock = true :=
  sorry
private theorem canCompleteBeforeTock_parallelTypeBranchesSelecting_of_mem
    (selected : BareMessage × PactType) :
    ∀ branches : List (BareMessage × PactType), selected ∈ branches →
      (parallelTypeBranchesSelecting selected branches).CanCompleteBeforeTock =
        selected.2.CanCompleteBeforeTock :=
  sorry
private theorem compiledSelectedConjunction_zipIdx_cases
    (signature : TypeAlphabet) (fuel : Nat)
    (branches : List (BareMessage × PactType))
    (indexed : (BareMessage × AutomatonFragment) × Nat)
    (hIndexed : indexed ∈
      (branches.map fun selected =>
        (selected.1, compileTypeFuel signature fuel
          (parallelTypeBranchesSelecting selected branches))).zipIdx) :
    ∃ selected, branches[indexed.2]? = some selected ∧
      indexed.1 = (selected.1, compileTypeFuel signature fuel
        (parallelTypeBranchesSelecting selected branches)) :=
  sorry
private theorem sequenceExecution_buildSelectedConjunctiveOffer_root_shape_leaf
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (edge : PendingAutomatonEdge)
    (hEdge : edge ∈ (buildSelectedConjunctiveOfferAutomaton signature branches
      elseAutomaton selectedConjunctions).edges)
    (hSource : edge.source = .root) :
    edge.label ≠ .future ∧
      ∃ removed, edge.future = .at edge.target removed :=
  sorry
private theorem buildSelectedConjunctiveOffer_child0_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).accepting ↔
      state ∈ elseAutomaton.accepting :=
  sorry
private theorem buildSelectedConjunctiveOffer_child0_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (state : TypeAutomatonState) :
    childState 0 state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).completing ↔
      state ∈ elseAutomaton.completing :=
  sorry
private theorem buildSelectedConjunctiveOffer_root_not_accepting
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment)) :
    (.root : TypeAutomatonState) ∉
      (buildSelectedConjunctiveOfferAutomaton signature branches
        elseAutomaton selectedConjunctions).accepting :=
  sorry
private theorem buildSelectedConjunctiveOffer_conjunction_accepting_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).accepting ↔
      state ∈ entry.2.accepting :=
  sorry
private theorem buildSelectedConjunctiveOffer_conjunction_completing_iff
    (signature : TypeAlphabet) (branches : List (BareMessage × PactType))
    (elseAutomaton : AutomatonFragment)
    (selectedConjunctions : List (BareMessage × AutomatonFragment))
    (index : Nat) (entry : BareMessage × AutomatonFragment)
    (hEntry : selectedConjunctions[index]? = some entry)
    (state : TypeAutomatonState) :
    childState (index + 1) state ∈
        (buildSelectedConjunctiveOfferAutomaton signature branches
          elseAutomaton selectedConjunctions).completing ↔
      state ∈ entry.2.completing :=
  sorry
private theorem compilationSequenceExecutionCorrect_offer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationSequenceExecutionCorrect signature
      (.offer elseType branches) :=
  sorry
theorem compilationProofBundle_offer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.offer elseType branches))
    (hBranchesClosed : PactType.AllBranchVariablesBound [] branches)
    (hGuarded : PactType.ClockGuarded (.offer elseType branches))
    (hTail : PactType.TailRecursive (.offer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.offer elseType branches))
    (hScoped : PactType.InterfaceScoped (.offer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.offer elseType branches) :=
  sorry
end

end Pact
