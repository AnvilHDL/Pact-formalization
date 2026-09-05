import Anvilpp.PactTypes.Syntax.PactTypeShapeDefs

namespace Pact

set_option maxHeartbeats 1000000

namespace PactType

mutual
  theorem shape_reannotate (alphabet : PactTypeAlphabet) :
      ∀ processType : PactType, shape (processType.reannotate alphabet) = shape processType
    | .message _ _ _ => by simp [reannotate, shape]
    | .progress _ _ => by simp [reannotate, shape]
    | .tock _ => by simp [reannotate, shape]
    | .skip _ => by simp [reannotate, shape]
    | .var _ _ => by simp [reannotate, shape]
    | .choice _ left right => by
        simp only [reannotate, shape, shape_reannotate alphabet left,
          shape_reannotate alphabet right]
    | .seq _ left right => by
        simp only [reannotate, shape, shape_reannotate alphabet left,
          shape_reannotate alphabet right]
    | .par _ left right interface => by
        simp only [reannotate, shape, shape_reannotate _ left,
          shape_reannotate _ right]
    | .recur _ name body => by
        simp only [reannotate, shape, shape_reannotate alphabet body]
    | .fairChoice _ bid left right => by
        simp only [reannotate, shape, shape_reannotate alphabet left,
          shape_reannotate alphabet right]
    | .xoffer _ elseType branches => by
        simp only [reannotate, shape, shape_reannotate alphabet elseType,
          branchShapes_reannotateBranches alphabet branches]
    | .offer _ elseType branches => by
        simp only [reannotate, shape, shape_reannotate alphabet elseType,
          branchShapes_reannotateOfferBranches alphabet ∅ branches]
  termination_by processType => sizeOf processType

  theorem branchShapes_reannotateBranches (alphabet : PactTypeAlphabet) :
      ∀ branches : List (BareMessage × PactType),
        branchShapes (reannotateBranches alphabet branches) = branchShapes branches
    | [] => by simp [branchShapes]
    | (action, processType) :: rest => by
        simp only [reannotateBranches, branchShapes,
          shape_reannotate alphabet processType,
          branchShapes_reannotateBranches alphabet rest]
  termination_by branches => sizeOf branches

  theorem branchShapes_reannotateOfferBranches (alphabet : PactTypeAlphabet)
      (seen : Finset BareMessage) :
      ∀ branches : List (BareMessage × PactType),
        branchShapes (reannotateOfferBranches alphabet seen branches) =
          branchShapes branches
    | [] => by simp [reannotateOfferBranches_nil, branchShapes]
    | (action, processType) :: rest => by
        simp only [reannotateOfferBranches_cons, branchShapes,
          shape_reannotate _ processType,
          branchShapes_reannotateOfferBranches alphabet seen rest]
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end PactType

/-! ### Shapes are strictly bigger than their components -/

namespace PactType

mutual
  theorem canComplete_shape :
      ∀ processType : PactType,
        PactShape.canComplete (shape processType) = processType.CanCompleteBeforeTock
    | .message _ _ _ => by simp [shape, PactShape.canComplete, CanCompleteBeforeTock]
    | .progress _ _ => by simp [shape, PactShape.canComplete, CanCompleteBeforeTock]
    | .tock _ => by simp [shape, PactShape.canComplete, CanCompleteBeforeTock]
    | .skip _ => by simp [shape, PactShape.canComplete, CanCompleteBeforeTock]
    | .var _ _ => by simp [shape, PactShape.canComplete, CanCompleteBeforeTock]
    | .recur _ _ body => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape body]
    | .choice _ left right => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape left, canComplete_shape right]
    | .fairChoice _ _ left right => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape left, canComplete_shape right]
    | .seq _ left right => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape left, canComplete_shape right]
    | .par _ left right _ => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape left, canComplete_shape right]
    | .xoffer _ elseType branches => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape elseType, branchCanComplete_branchShapes branches]
    | .offer _ elseType branches => by
        simp only [shape, PactShape.canComplete, CanCompleteBeforeTock,
          canComplete_shape elseType, branchCanComplete_branchShapes branches]
  termination_by processType => sizeOf processType

  theorem branchCanComplete_branchShapes :
      ∀ branches : List (BareMessage × PactType),
        PactShape.branchCanComplete (branchShapes branches) =
          BranchCanCompleteBeforeTock branches
    | [] => by simp [branchShapes, PactShape.branchCanComplete,
        BranchCanCompleteBeforeTock]
    | (action, processType) :: rest => by
        simp only [branchShapes, PactShape.branchCanComplete,
          BranchCanCompleteBeforeTock, canComplete_shape processType,
          branchCanComplete_branchShapes rest]
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

mutual
  theorem prefixIds_shape :
      ∀ processType : PactType,
        PactShape.prefixIds (shape processType) = PrefixMessageIds processType
    | .message _ _ _ => by simp [shape, PactShape.prefixIds, PrefixMessageIds]
    | .progress _ _ => by simp [shape, PactShape.prefixIds, PrefixMessageIds]
    | .tock _ => by simp [shape, PactShape.prefixIds, PrefixMessageIds]
    | .skip _ => by simp [shape, PactShape.prefixIds, PrefixMessageIds]
    | .var _ _ => by simp [shape, PactShape.prefixIds, PrefixMessageIds]
    | .recur _ _ body => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds, prefixIds_shape body]
    | .choice _ left right => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape left, prefixIds_shape right]
    | .fairChoice _ _ left right => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape left, prefixIds_shape right]
    | .par _ left right _ => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape left, prefixIds_shape right]
    | .seq _ left right => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape left, prefixIds_shape right, canComplete_shape left]
    | .xoffer _ elseType branches => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape elseType, branchPrefixIds_branchShapes branches]
    | .offer _ elseType branches => by
        simp only [shape, PactShape.prefixIds, PrefixMessageIds,
          prefixIds_shape elseType, branchPrefixIds_branchShapes branches]
  termination_by processType => sizeOf processType

  theorem branchPrefixIds_branchShapes :
      ∀ branches : List (BareMessage × PactType),
        PactShape.branchPrefixIds (branchShapes branches) =
          BranchPrefixMessageIds branches
    | [] => by simp [branchShapes, PactShape.branchPrefixIds, BranchPrefixMessageIds]
    | (action, processType) :: rest => by
        simp only [branchShapes, PactShape.branchPrefixIds, BranchPrefixMessageIds,
          prefixIds_shape processType, branchPrefixIds_branchShapes rest]
  termination_by branches => sizeOf branches
decreasing_by
  all_goals
    simp_wf
    omega
end

end PactType

/-! ### Per-constructor equations for `PrefixMessageIds` -/

/-! ### A branch head is in the prefix of its own expansion -/

/-! ### The exclusion -/

end Pact

