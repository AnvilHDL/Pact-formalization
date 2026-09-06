import Anvilpp.PactTypes.Proofs.Syntax.TypeDynamicsCoreLemmas

namespace Pact

noncomputable section

mutual
  /-- The structural completion view blocks undeclared actions and offer heads.
  It is used only by the completion analysis, not by the execution compiler. -/
  def PactType.completionView : PactType → PactType
    | .message alphabet name polarity =>
        if (name, polarity) ∈ alphabet.actions then .message alphabet name polarity
        else .tock alphabet
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
        if ∀ branch ∈ branches, branch.1 ∈ alphabet.actions then
          .xoffer alphabet other.completionView (PactType.completionViewBranches branches)
        else .tock alphabet
    | .offer alphabet other branches =>
        if ∀ branch ∈ branches, branch.1 ∈ alphabet.actions then
          .offer alphabet other.completionView (PactType.completionViewBranches branches)
        else .tock alphabet
  termination_by ty => sizeOf ty

  def PactType.completionViewBranches : List (BareMessage × PactType) → List (BareMessage × PactType)
    | [] => []
    | (action, ty) :: rest => (action, ty.completionView) :: PactType.completionViewBranches rest
  termination_by branches => sizeOf branches
decreasing_by all_goals simp_wf; omega
end

/-- Optimistic completion, including every written alphabet gate. -/
def PactType.CanCompleteDeclared (ty : PactType) : Bool := ty.completionView.CanCompleteBeforeTock

def PactType.BranchCanCompleteDeclared (branches : List (BareMessage × PactType)) : Bool :=
  PactType.BranchCanCompleteBeforeTock (PactType.completionViewBranches branches)

theorem PactType.canCompleteDeclared_eq (ty : PactType) :
    ty.CanCompleteDeclared = match ty with
    | .message alphabet name polarity => decide ((name, polarity) ∈ alphabet.actions)
    | .progress _ _ | .skip _ => true
    | .tock _ | .var _ _ => false
    | .recur _ _ body => body.CanCompleteDeclared
    | .choice _ left right | .fairChoice _ _ left right => left.CanCompleteDeclared || right.CanCompleteDeclared
    | .seq _ left right | .par _ left right _ => left.CanCompleteDeclared && right.CanCompleteDeclared
    | .xoffer alphabet other branches | .offer alphabet other branches =>
        decide (∀ branch ∈ branches, branch.1 ∈ alphabet.actions) &&
          (other.CanCompleteDeclared || PactType.BranchCanCompleteDeclared branches) := by
  classical
  cases ty <;> simp only [CanCompleteDeclared, completionView, BranchCanCompleteDeclared]
  all_goals try split_ifs
  all_goals simp_all only [CanCompleteBeforeTock, decide_true, decide_false,
    Bool.true_and, Bool.false_and, implies_true]

theorem PactType.branchCanCompleteDeclared_nil : PactType.BranchCanCompleteDeclared [] = false := by
  simp [BranchCanCompleteDeclared, completionViewBranches, BranchCanCompleteBeforeTock]

theorem PactType.branchCanCompleteDeclared_cons (action : BareMessage) (ty : PactType)
    (rest : List (BareMessage × PactType)) :
    PactType.BranchCanCompleteDeclared ((action, ty) :: rest) =
      (ty.CanCompleteDeclared || PactType.BranchCanCompleteDeclared rest) := by
  simp [BranchCanCompleteDeclared, completionViewBranches, BranchCanCompleteBeforeTock, CanCompleteDeclared]

end

end Pact
