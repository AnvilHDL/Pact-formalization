import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-- No clock label occurs in the half-open interval `[i,j)`. -/
def TypeLogNoClockBetween (log : TypeLog) (i j : Nat) : Prop :=
  ∀ k, i ≤ k → k < j → ¬ (log k).2.isTock

/-- Helper Lemma H11: same-cycle characterization of honesty. -/
lemma helper_h11_same_cycle_honesty (log : TypeLog) :
    HonestTypeLog log ↔
      ∀ i j,
        i < j →
        TypeLogNoClockBetween log i j →
        typeAvailable (log j).1 ⊆ (log i).1.future := by
  sorry -- TODO(section7): induction on `j - i`.

end

end Pact
