import Anvilpp.PactTypes.Proofs.Syntax.TypeDynamicsCoreLemmas

namespace Pact

noncomputable section

mutual
  /-- Structural view used by completion and substitution transport.
  Alphabet annotations do not gate optimistic completion. -/
  def PactType.completionView : PactType → PactType
    | .message alphabet name polarity =>
        .message alphabet name polarity
    | .progress alphabet name => .progress alphabet name
    | .skip alphabet => .skip alphabet
    | .tock alphabet => .tock alphabet
    | .var alphabet name => .var alphabet name
    | .recur alphabet name body => .recur alphabet name body.completionView
    | .choice alphabet left right => .choice alphabet left.completionView right.completionView
    | .fairChoice alphabet bid left right => .fairChoice alphabet bid left.completionView right.completionView
    | .seq alphabet left right => .seq alphabet left.completionView right.completionView
    | .par alphabet left right interface => .par alphabet left.completionView right.completionView interface
    | .xoffer alphabet other branches =>
        .xoffer alphabet other.completionView (PactType.completionViewBranches branches)
    | .offer alphabet other branches =>
        .offer alphabet other.completionView (PactType.completionViewBranches branches)
  termination_by ty => sizeOf ty

  def PactType.completionViewBranches : List (BareMessage × PactType) → List (BareMessage × PactType)
    | [] => []
    | (action, ty) :: rest => (action, ty.completionView) :: PactType.completionViewBranches rest
  termination_by branches => sizeOf branches
decreasing_by all_goals simp_wf; omega
end

/-- Alphabet-independent optimistic completion before the next clock. -/
def PactType.CanCompleteDeclared (ty : PactType) : Bool := ty.completionView.CanCompleteBeforeTock

def PactType.BranchCanCompleteDeclared (branches : List (BareMessage × PactType)) : Bool :=
  PactType.BranchCanCompleteBeforeTock (PactType.completionViewBranches branches)

theorem PactType.canCompleteDeclared_eq (ty : PactType) :
    ty.CanCompleteDeclared = match ty with
    | .message _ _ _ => true
    | .progress _ _ | .skip _ => true
    | .tock _ | .var _ _ => false
    | .recur _ _ body => body.CanCompleteDeclared
    | .choice _ left right | .fairChoice _ _ left right => left.CanCompleteDeclared || right.CanCompleteDeclared
    | .seq _ left right | .par _ left right _ => left.CanCompleteDeclared && right.CanCompleteDeclared
    | .xoffer _ other branches | .offer _ other branches =>
        other.CanCompleteDeclared || PactType.BranchCanCompleteDeclared branches := by
  classical
  cases ty <;> simp only [CanCompleteDeclared, completionView, BranchCanCompleteDeclared]
  all_goals simp only [CanCompleteBeforeTock]

theorem PactType.branchCanCompleteDeclared_nil : PactType.BranchCanCompleteDeclared [] = false := by
  simp [BranchCanCompleteDeclared, completionViewBranches, BranchCanCompleteBeforeTock]

theorem PactType.branchCanCompleteDeclared_cons (action : BareMessage) (ty : PactType)
    (rest : List (BareMessage × PactType)) :
    PactType.BranchCanCompleteDeclared ((action, ty) :: rest) =
      (ty.CanCompleteDeclared || PactType.BranchCanCompleteDeclared rest) := by
  simp [BranchCanCompleteDeclared, completionViewBranches, BranchCanCompleteBeforeTock, CanCompleteDeclared]

end

end Pact
