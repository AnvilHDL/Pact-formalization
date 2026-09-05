import Anvilpp.PactTypes.Syntax.TypeLabelOwnershipDefs

namespace Pact

set_option maxHeartbeats 1000000

open Classical

/-! ## Membership helpers for `sends` and `combine` -/

/-! ## Branch declarations -/

/-- Everything one branch declares by name is declared by the branch list. -/
theorem branch_subset_branchMessageIds
    {branches : List (BareMessage × PactType)} {branch : BareMessage × PactType}
    (hMem : branch ∈ branches) :
    {branch.1.1} ∪ PactType.MessageIds branch.2 ⊆
      PactType.BranchMessageIds branches := by
  induction branches with
  | nil => cases hMem
  | cons head tail ih =>
      rcases head with ⟨action, branchType⟩
      simp only [PactType.BranchMessageIds]
      simp only [List.mem_cons] at hMem
      rcases hMem with hEq | hTail
      · cases hEq
        exact Finset.subset_union_left
      · exact (ih hTail).trans Finset.subset_union_right

namespace PactType.LabelOwned

/-- The clock label observes nothing. -/
theorem tock (source : PactType) : source.LabelOwned TypeLabel.tock := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [TypeLabel.contains]

end PactType.LabelOwned

/-! ## A decorated step only observes what its source declares -/

/-! ## Separation of sibling labels at a parallel node -/

end Pact
