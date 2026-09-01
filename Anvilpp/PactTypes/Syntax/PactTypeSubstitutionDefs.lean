import Anvilpp.PactTypes.Syntax.PactTypeCompletionEval

namespace Pact

noncomputable section

/-- Every free variable sits in a tail position.  A closed type has this
property vacuously, and every subterm of such a type inherits it. -/
def PactType.TailClosed (processType : PactType) : Prop :=
  ∀ name : String, processType.TailOccurrences name True

/-- Branch-list form of `TailClosed`. -/
def PactType.TailClosedBranches (branches : List (BareMessage × PactType)) :
    Prop :=
  ∀ name : String, PactType.TailBranchOccurrences name True branches

end

end Pact
