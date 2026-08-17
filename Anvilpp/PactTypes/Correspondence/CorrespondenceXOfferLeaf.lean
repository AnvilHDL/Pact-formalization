import Anvilpp.PactTypes.Correspondence.CorrespondenceRecursionLeaf

/-!
# xoffer regular leaf
-/

namespace Pact

noncomputable section


/-- Exclusive-offer closure packages its indexed branch/else/wait
classifiers.  Completion is supplied by the strong-induction hypotheses for
the else continuation and every indexed branch. -/

private theorem compilationFutureCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationFutureCorrect signature (.xoffer elseType branches) :=
  sorry
private theorem compilationFragmentStepCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hFuture : CompilationFutureCorrect signature
      (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationScopedFragmentStepCorrect signature
      (.xoffer elseType branches) :=
  sorry
private theorem compilationSequenceExecutionCorrect_xoffer_regular_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationSequenceExecutionCorrect signature
      (.xoffer elseType branches) :=
  sorry
theorem compilationProofBundle_xoffer_leaf
    (signature : TypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType))
    (hSignature : signature.WellFormed)
    (hSupports : signature.Supports (.xoffer elseType branches))
    (hGuarded : PactType.ClockGuarded (.xoffer elseType branches))
    (hTail : PactType.TailRecursive (.xoffer elseType branches))
    (hLinear : PactType.SameCycleMessageLinear (.xoffer elseType branches))
    (hScoped : PactType.InterfaceScoped (.xoffer elseType branches))
    (hElse : CompilationProofBundle signature elseType)
    (hBranches : ∀ (action : BareMessage) (branchType : PactType)
      (index : Nat), branches[index]? = some (action, branchType) →
        CompilationProofBundle signature branchType) :
    CompilationProofBundle signature (.xoffer elseType branches) :=
  sorry
end

end Pact
