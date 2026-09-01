import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas

namespace Pact

set_option maxHeartbeats 1000000

inductive PactShape : Type where
  | message : MessageId → MessageDir → PactShape
  | progress : ProcId → PactShape
  | tock : PactShape
  | skip : PactShape
  | var : String → PactShape
  | choice : PactShape → PactShape → PactShape
  | seq : PactShape → PactShape → PactShape
  | par : PactShape → PactShape → Interface → PactShape
  | recur : String → PactShape → PactShape
  | fairChoice : BranchId → PactShape → PactShape → PactShape
  | xoffer : PactShape → List (BareMessage × PactShape) → PactShape
  | offer : PactShape → List (BareMessage × PactShape) → PactShape

namespace PactType

mutual
  def shape : PactType → PactShape
    | .message _ msg dir => .message msg dir
    | .progress _ pid => .progress pid
    | .tock _ => .tock
    | .skip _ => .skip
    | .var _ name => .var name
    | .choice _ left right => .choice (shape left) (shape right)
    | .seq _ left right => .seq (shape left) (shape right)
    | .par _ left right interface => .par (shape left) (shape right) interface
    | .recur _ name body => .recur name (shape body)
    | .fairChoice _ bid left right => .fairChoice bid (shape left) (shape right)
    | .xoffer _ elseType branches => .xoffer (shape elseType) (branchShapes branches)
    | .offer _ elseType branches => .offer (shape elseType) (branchShapes branches)
  termination_by processType => sizeOf processType

  def branchShapes : List (BareMessage × PactType) → List (BareMessage × PactShape)
    | [] => []
    | (action, processType) :: rest => (action, shape processType) :: branchShapes rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end PactType

/-! ### `CanCompleteBeforeTock` and `PrefixMessageIds` factor through the shape -/

namespace PactShape

mutual
  def canComplete : PactShape → Bool
    | .message _ _ => true
    | .progress _ => true
    | .skip => true
    | .tock => false
    | .var _ => false
    | .recur _ body => canComplete body
    | .choice left right => canComplete left || canComplete right
    | .fairChoice _ left right => canComplete left || canComplete right
    | .seq left right => canComplete left && canComplete right
    | .par left right _ => canComplete left && canComplete right
    | .xoffer elseShape branches => canComplete elseShape || branchCanComplete branches
    | .offer elseShape branches => canComplete elseShape || branchCanComplete branches
  termination_by processShape => sizeOf processShape

  def branchCanComplete : List (BareMessage × PactShape) → Bool
    | [] => false
    | (_, processShape) :: rest => canComplete processShape || branchCanComplete rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  def prefixIds : PactShape → Finset MessageId
    | .message msg _ => {msg}
    | .progress _ | .tock | .skip | .var _ => ∅
    | .recur _ body => prefixIds body
    | .choice left right | .fairChoice _ left right | .par left right _ =>
        prefixIds left ∪ prefixIds right
    | .seq left right =>
        prefixIds left ∪ (if canComplete left then prefixIds right else ∅)
    | .xoffer elseShape branches | .offer elseShape branches =>
        prefixIds elseShape ∪ branchPrefixIds branches
  termination_by processShape => sizeOf processShape

  def branchPrefixIds : List (BareMessage × PactShape) → Finset MessageId
    | [] => ∅
    | (action, processShape) :: rest =>
        {action.1} ∪ prefixIds processShape ∪ branchPrefixIds rest
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end PactShape

end Pact
