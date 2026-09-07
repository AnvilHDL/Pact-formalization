import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-- No clock label occurs in the half-open interval `[i,j)`. -/
def TypeLogNoClockBetween (log : TypeLog) (i j : Nat) : Prop :=
  ∀ k, i ≤ k → k < j → ¬ (log k).2.isTock

/-- The future component is one half of the available set. -/
lemma future_subset_typeAvailable (env : TypeEnvironment) :
    env.future ⊆ typeAvailable env := by
  intro msg hMem
  simp [typeAvailable, hMem]

/-- Helper Lemma H11: same-cycle characterization of honesty. -/
lemma helper_h11_same_cycle_honesty (log : TypeLog) :
    HonestTypeLog log ↔
      ∀ i j,
        i < j →
        TypeLogNoClockBetween log i j →
        typeAvailable (log j).1 ⊆ (log i).1.future := by
  constructor
  · intro hHonest i j hLess hNoClock
    induction j with
    | zero => exact absurd hLess (Nat.not_lt_zero i)
    | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hLess with hLt | hEq
        · have hInner : TypeLogNoClockBetween log i j := by
            intro k hLow hHigh
            exact hNoClock k hLow (Nat.lt_succ_of_lt hHigh)
          have hPrefix : typeAvailable (log j).1 ⊆ (log i).1.future :=
            ih hLt hInner
          have hStep : typeAvailable (log (j + 1)).1 ⊆ (log j).1.future := by
            rcases hHonest j with hTock | hSub
            · exact absurd hTock (hNoClock j (Nat.le_of_lt hLt) (Nat.lt_succ_self j))
            · exact hSub
          exact hStep.trans ((future_subset_typeAvailable (log j).1).trans hPrefix)
        · subst hEq
          rcases hHonest i with hTock | hSub
          · exact absurd hTock (hNoClock i (Nat.le_refl i) (Nat.lt_succ_self i))
          · exact hSub
  · intro hSame index
    by_cases hTock : (log index).2.isTock
    · exact Or.inl hTock
    · refine Or.inr (hSame index (index + 1) (Nat.lt_succ_self index) ?_)
      intro k hLow hHigh
      have : k = index := Nat.le_antisymm (Nat.lt_succ_iff.mp hHigh) hLow
      exact this ▸ hTock

end

end Pact
