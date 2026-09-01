import Anvilpp.PactTypes.Syntax.TypeTransitionSystem

/-!
Alphabet-erased shape of a type.  `reannotate` only rewrites alphabet
annotations, so it preserves the shape; shape equality is therefore the
reannotation-stable weakening of target equality.
-/

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
          branchShapes_reannotateBranches alphabet branches]
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
decreasing_by
  all_goals
    simp_wf
    omega
end

theorem shape_eq_of_reannotate_eq {t₁ t₂ : PactType} {alphabet : PactTypeAlphabet}
    (h : t₁.reannotate alphabet = t₂.reannotate alphabet) : shape t₁ = shape t₂ := by
  rw [← shape_reannotate alphabet t₁, ← shape_reannotate alphabet t₂, h]

theorem eq_skip_of_shape_skip {t : PactType} (h : shape t = PactShape.skip) :
    t = .skip t.alphabet := by
  cases t <;> simp [shape, PactType.alphabet] at h ⊢

end PactType

/-! ### Shapes are strictly bigger than their components -/

theorem shape_seq_ne_right (left right : PactShape) :
    PactShape.seq left right ≠ right := by
  intro h
  have hLt : sizeOf right < sizeOf (PactShape.seq left right) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

theorem shape_xoffer_ne_else (elseShape : PactShape)
    (branches : List (BareMessage × PactShape)) :
    PactShape.xoffer elseShape branches ≠ elseShape := by
  intro h
  have hLt : sizeOf elseShape < sizeOf (PactShape.xoffer elseShape branches) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

theorem shape_offer_ne_else (elseShape : PactShape)
    (branches : List (BareMessage × PactShape)) :
    PactShape.offer elseShape branches ≠ elseShape := by
  intro h
  have hLt : sizeOf elseShape < sizeOf (PactShape.offer elseShape branches) := by
    simp_wf
    omega
  rw [h] at hLt
  omega

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

/-- Prefix message ids only depend on the shape. -/
theorem prefixMessageIds_congr_of_shape {t₁ t₂ : PactType}
    (h : shape t₁ = shape t₂) : PrefixMessageIds t₁ = PrefixMessageIds t₂ := by
  rw [← prefixIds_shape, ← prefixIds_shape, h]

end PactType

/-! ### Per-constructor equations for `PrefixMessageIds` -/

theorem prefix_message (alphabet : PactTypeAlphabet) (msg : MessageId)
    (dir : MessageDir) :
    PactType.PrefixMessageIds (.message alphabet msg dir) = {msg} := by
  rw [PactType.PrefixMessageIds.eq_def]

theorem prefix_seq (alphabet : PactTypeAlphabet) (left right : PactType) :
    PactType.PrefixMessageIds (.seq alphabet left right) =
      PactType.PrefixMessageIds left ∪
        (if left.CanCompleteBeforeTock then PactType.PrefixMessageIds right
          else ∅) := by
  rw [PactType.PrefixMessageIds.eq_def]

theorem prefix_par (alphabet : PactTypeAlphabet) (left right : PactType)
    (interface : Interface) :
    PactType.PrefixMessageIds (.par alphabet left right interface) =
      PactType.PrefixMessageIds left ∪ PactType.PrefixMessageIds right := by
  rw [PactType.PrefixMessageIds.eq_def]

theorem prefix_xoffer (alphabet : PactTypeAlphabet) (elseType : PactType)
    (branches : List (BareMessage × PactType)) :
    PactType.PrefixMessageIds (.xoffer alphabet elseType branches) =
      PactType.PrefixMessageIds elseType ∪
        PactType.BranchPrefixMessageIds branches := by
  rw [PactType.PrefixMessageIds.eq_def]

theorem branchPrefix_cons (action : BareMessage) (processType : PactType)
    (rest : List (BareMessage × PactType)) :
    PactType.BranchPrefixMessageIds ((action, processType) :: rest) =
      {action.1} ∪ PactType.PrefixMessageIds processType ∪
        PactType.BranchPrefixMessageIds rest := by
  rw [PactType.BranchPrefixMessageIds.eq_def]

/-! ### A branch head is in the prefix of its own expansion -/

theorem head_mem_prefix_selectedTypeBranchAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    branch.1.1 ∈ PactType.PrefixMessageIds (selectedTypeBranchAt alphabet branch) := by
  rw [selectedTypeBranchAt, prefix_seq, prefix_message]
  simp

theorem head_mem_prefix_singletonTypeXOfferAt (alphabet : PactTypeAlphabet)
    (branch : BareMessage × PactType) :
    branch.1.1 ∈
      PactType.PrefixMessageIds (singletonTypeXOfferAt alphabet branch) := by
  rw [singletonTypeXOfferAt, prefix_xoffer, branchPrefix_cons]
  simp

theorem head_mem_prefix_parallelTypeBranchesSelecting
    (alphabet : PactTypeAlphabet) (enabled branch : BareMessage × PactType)
    (rest : List (BareMessage × PactType)) :
    branch.1.1 ∈ PactType.PrefixMessageIds
      (parallelTypeBranchesSelecting alphabet enabled (branch :: rest)) := by
  rw [parallelTypeBranchesSelecting]
  cases rest with
  | nil =>
      rw [parallelTypeBranchesSelectingWithin]
      split_ifs
      · exact head_mem_prefix_selectedTypeBranchAt _ _
      · exact head_mem_prefix_singletonTypeXOfferAt _ _
  | cons head tail =>
      rw [parallelTypeBranchesSelectingWithin]
      all_goals
        first
          | (split_ifs <;>
              · rw [prefix_par]
                simp only [Finset.mem_union]
                refine Or.inl ?_
                first
                  | exact head_mem_prefix_selectedTypeBranchAt _ _
                  | exact head_mem_prefix_singletonTypeXOfferAt _ _)
          | simp

/-! ### The exclusion -/

theorem parallelTypeBranchesSelecting_ne_elseType
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {enabled : BareMessage × PactType}
    (hLinear : ∀ branch ∈ branches,
      branch.1.1 ∉ PactType.PrefixMessageIds elseType)
    (hNonempty : branches ≠ []) :
    parallelTypeBranchesSelecting alphabet enabled branches ≠ elseType := by
  intro hEq
  cases branches with
  | nil => exact hNonempty rfl
  | cons branch rest =>
      refine hLinear branch (by simp) ?_
      rw [← hEq]
      exact head_mem_prefix_parallelTypeBranchesSelecting alphabet enabled branch rest

/-- Shape-level form: the selecting expansion of a non-empty branch list cannot
even have the same shape as the else arm. -/
theorem shape_parallelTypeBranchesSelecting_ne_elseType
    {alphabet : PactTypeAlphabet} {elseType : PactType}
    {branches : List (BareMessage × PactType)}
    {enabled : BareMessage × PactType}
    (hLinear : ∀ branch ∈ branches,
      branch.1.1 ∉ PactType.PrefixMessageIds elseType)
    (hNonempty : branches ≠ []) :
    PactType.shape (parallelTypeBranchesSelecting alphabet enabled branches) ≠
      PactType.shape elseType := by
  intro hShape
  cases branches with
  | nil => exact hNonempty rfl
  | cons branch rest =>
      refine hLinear branch (by simp) ?_
      rw [← PactType.prefixMessageIds_congr_of_shape hShape]
      exact head_mem_prefix_parallelTypeBranchesSelecting alphabet enabled branch rest


/-- A selecting expansion of a non-empty branch list is a `seq`, an `xoffer` or
a `par` — never an `offer`. -/
theorem shape_parallelTypeBranchesSelecting_ne_offer
    (alphabet : PactTypeAlphabet) (enabled branch : BareMessage × PactType)
    (rest : List (BareMessage × PactType)) (elseShape : PactShape)
    (branchShapes : List (BareMessage × PactShape)) :
    PactType.shape
        (parallelTypeBranchesSelecting alphabet enabled (branch :: rest)) ≠
      PactShape.offer elseShape branchShapes := by
  rw [parallelTypeBranchesSelecting]
  cases rest with
  | nil =>
      rw [parallelTypeBranchesSelectingWithin]
      split_ifs <;>
        simp [selectedTypeBranchAt, singletonTypeXOfferAt, PactType.shape]
  | cons head tail =>
      rw [parallelTypeBranchesSelectingWithin]
      all_goals
        first
          | (split_ifs <;> simp [PactType.shape])
          | simp


end Pact

#print axioms Pact.shape_parallelTypeBranchesSelecting_ne_elseType
#print axioms Pact.parallelTypeBranchesSelecting_ne_elseType
