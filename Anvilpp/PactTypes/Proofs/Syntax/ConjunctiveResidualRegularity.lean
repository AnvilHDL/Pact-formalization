import Anvilpp.PactTypes.Proofs.Syntax.ConjunctiveResiduals

namespace Pact

noncomputable section

open Classical

/-- Atomic residuals preserve tail recursion of branch bodies. -/
theorem parallelTypeBranchesFiringFrom_tailRecursive 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.TailRecursive branch.2) :
    ∀ index, PactType.TailRecursive (parallelTypeBranchesFiringFrom alphabet selected index branches) := by
  induction branches with
  | nil => intro index; simp [parallelTypeBranchesFiringFrom, PactType.TailRecursive]
  | cons head rest ih =>
      intro index
      have hHead : PactType.TailRecursive (if index ∈ selected then head.2.reannotate alphabet
          else singletonTypeXOfferAt alphabet head) := by
        split
        · exact PactType.reannotate_tailRecursive head.2 alphabet (hBranches head (by simp))
        · exact singletonTypeXOfferAt_tailRecursive alphabet head (hBranches head (by simp))
      cases rest with
      | nil => exact hHead
      | cons next rest =>
          rw [parallelTypeBranchesFiringFrom, PactType.TailRecursive]
          exact ⟨hHead, ih (fun b hb => hBranches b (List.mem_cons_of_mem _ hb)) (index + 1)⟩

theorem parallelTypeBranchesFiring_tailRecursive 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.TailRecursive branch.2) :
    PactType.TailRecursive (parallelTypeBranchesFiring alphabet selected branches) :=
  parallelTypeBranchesFiringFrom_tailRecursive alphabet selected branches hBranches 0

/-- Atomic residuals preserve clock guarding of branch bodies. -/
theorem parallelTypeBranchesFiringFrom_clockGuarded 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.ClockGuarded branch.2) :
    ∀ index, PactType.ClockGuarded (parallelTypeBranchesFiringFrom alphabet selected index branches) := by
  induction branches with
  | nil => intro index; simp [parallelTypeBranchesFiringFrom, PactType.ClockGuarded]
  | cons head rest ih =>
      intro index
      have hHead : PactType.ClockGuarded (if index ∈ selected then head.2.reannotate alphabet
          else singletonTypeXOfferAt alphabet head) := by
        split
        · exact PactType.reannotate_clockGuarded head.2 alphabet (hBranches head (by simp))
        · exact singletonTypeXOfferAt_clockGuarded alphabet head (hBranches head (by simp))
      cases rest with
      | nil => exact hHead
      | cons next rest =>
          rw [parallelTypeBranchesFiringFrom, PactType.ClockGuarded]
          exact ⟨hHead, ih (fun b hb => hBranches b (List.mem_cons_of_mem _ hb)) (index + 1)⟩

theorem parallelTypeBranchesFiring_clockGuarded 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.ClockGuarded branch.2) :
    PactType.ClockGuarded (parallelTypeBranchesFiring alphabet selected branches) :=
  parallelTypeBranchesFiringFrom_clockGuarded alphabet selected branches hBranches 0

/-- Atomic residuals preserve binder freshness of branch bodies. -/
theorem parallelTypeBranchesFiringFrom_binderFreshFor (bound : List String) 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.BinderFreshFor bound branch.2) :
    ∀ index, PactType.BinderFreshFor bound (parallelTypeBranchesFiringFrom alphabet selected index branches) := by
  induction branches with
  | nil => intro index; simp [parallelTypeBranchesFiringFrom, PactType.BinderFreshFor]
  | cons head rest ih =>
      intro index
      have hHead : PactType.BinderFreshFor bound (if index ∈ selected then head.2.reannotate alphabet
          else singletonTypeXOfferAt alphabet head) := by
        split
        · exact PactType.reannotate_binderFreshFor bound head.2 alphabet (hBranches head (by simp))
        · exact by
            simp only [singletonTypeXOfferAt, PactType.BinderFreshFor, PactType.BinderFreshForBranches]
            exact ⟨trivial, PactType.reannotate_binderFreshFor bound head.2 alphabet
              (hBranches head (by simp)), trivial⟩
      cases rest with
      | nil => exact hHead
      | cons next rest =>
          rw [parallelTypeBranchesFiringFrom, PactType.BinderFreshFor]
          exact ⟨hHead, ih (fun b hb => hBranches b (List.mem_cons_of_mem _ hb)) (index + 1)⟩

theorem parallelTypeBranchesFiring_binderFreshFor (bound : List String) 
    (alphabet : PactTypeAlphabet) (selected : Finset Nat)
    (branches : List (BareMessage × PactType))
    (hBranches : ∀ branch ∈ branches, PactType.BinderFreshFor bound branch.2) :
    PactType.BinderFreshFor bound (parallelTypeBranchesFiring alphabet selected branches) :=
  parallelTypeBranchesFiringFrom_binderFreshFor bound alphabet selected branches hBranches 0

end

end Pact

