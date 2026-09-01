import Anvilpp.PactTypes.Syntax.TypeFutureOffersFuelLemmas

/-!
# Valuation-polymorphic completion evaluator and its substitution/hygiene transport
-/

namespace Pact

noncomputable section

mutual
  /-- `CanCompleteBeforeTock`, but every occurrence of `.var name` contributes
  `value` instead of the unconditional `false` used by `CanCompleteBeforeTock`
  itself.  Respects the same capture-avoiding shadowing as `replaceVar`: a
  nested `.recur name _` binder stops the substitution view of its own body,
  matching `replaceVar`'s `if var = other then .recur other body else ...`
  clause. -/
  def PactType.canCompleteBeforeTockSubst
      (name : String) (value : Bool) : PactType → Bool
    | .message _ _ _ | .progress _ _ | .skip _ => true
    | .tock _ => false
    | .var _ other => if name = other then value else false
    | .recur _ other body =>
        if name = other then PactType.CanCompleteBeforeTock body
        else canCompleteBeforeTockSubst name value body
    | .choice _ left right | .fairChoice _ _ left right =>
        canCompleteBeforeTockSubst name value left ||
          canCompleteBeforeTockSubst name value right
    | .seq _ left right | .par _ left right _ =>
        canCompleteBeforeTockSubst name value left &&
          canCompleteBeforeTockSubst name value right
    | .xoffer _ elseType branches | .offer _ elseType branches =>
        canCompleteBeforeTockSubst name value elseType ||
          branchCanCompleteBeforeTockSubst name value branches
  termination_by processType => sizeOf processType

  def PactType.branchCanCompleteBeforeTockSubst
      (name : String) (value : Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        canCompleteBeforeTockSubst name value processType ||
          branchCanCompleteBeforeTockSubst name value rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  /-- Optimistic completion under a finite-control interpretation of the free
  recursion variables.  Entering a binder shadows its own name with the
  ordinary (unfolded-call-free) value `false`; an installed backedge is
  represented separately by updating that name to the binder's completion
  value when its body is analysed. -/
  def PactType.completionEval (valuation : String → Bool) : PactType → Bool
    | .message _ _ _ | .progress _ _ | .skip _ => true
    | .tock _ => false
    | .var _ name => valuation name
    | .recur _ name body => completionEval (Function.update valuation name false) body
    | .choice _ left right | .fairChoice _ _ left right =>
        completionEval valuation left || completionEval valuation right
    | .seq _ left right | .par _ left right _ =>
        completionEval valuation left && completionEval valuation right
    | .xoffer _ elseType branches | .offer _ elseType branches =>
        completionEval valuation elseType ||
          branchCompletionEval valuation branches
  termination_by processType => sizeOf processType

  def PactType.branchCompletionEval (valuation : String → Bool) :
      List (BareMessage × PactType) → Bool
    | [] => false
    | (_, processType) :: rest =>
        completionEval valuation processType || branchCompletionEval valuation rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end



end

end Pact
