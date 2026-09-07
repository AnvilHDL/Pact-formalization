import Mathlib.Data.Set.Finite.Lattice
import Anvilpp.ProofHelpers.CompatibilityGame

namespace Pact

noncomputable section

open Classical

/-! ## Round-robin monitors

The recurrence analysis of `M_d`: its completion flag is raised infinitely
often exactly when every member of its request set is observed infinitely
often. -/

/-- On `ℕ`, infinitude is unboundedness. -/
lemma set_infinite_nat_iff {s : Set ℕ} :
    s.Infinite ↔ ∀ bound, ∃ n ∈ s, bound ≤ n := by
  constructor
  · intro hInfinite bound
    by_contra hCon
    push_neg at hCon
    exact hInfinite
      (Set.Finite.subset (Set.finite_lt_nat bound) fun n hMem => hCon n hMem)
  · intro hUnbounded hFinite
    obtain ⟨bound, hBound⟩ := Set.Finite.bddAbove hFinite
    obtain ⟨n, hMem, hLe⟩ := hUnbounded (bound + 1)
    exact absurd (hBound hMem) (by omega)

lemma monitorAdvance_eq (req pending marks : Finset TypeMark) :
    monitorAdvance req pending marks =
      if pending \ marks = ∅ then (req, true) else (pending \ marks, false) :=
  rfl

/-- The outstanding requirements and completion flag of `M_d` after reading the
first `n` mark sets of a run. -/
def monitorRun (req : Finset TypeMark) (marks : ℕ → Finset TypeMark) :
    ℕ → Finset TypeMark × Bool
  | 0 => (req, false)
  | n + 1 => monitorAdvance req (monitorRun req marks n).1 (marks n)

@[simp] lemma monitorRun_zero (req : Finset TypeMark)
    (marks : ℕ → Finset TypeMark) : monitorRun req marks 0 = (req, false) :=
  rfl

@[simp] lemma monitorRun_succ (req : Finset TypeMark)
    (marks : ℕ → Finset TypeMark) (n : ℕ) :
    monitorRun req marks (n + 1) =
      monitorAdvance req (monitorRun req marks n).1 (marks n) :=
  rfl

lemma monitorRun_flag_succ (req : Finset TypeMark)
    (marks : ℕ → Finset TypeMark) (n : ℕ) :
    (monitorRun req marks (n + 1)).2 = true ↔
      (monitorRun req marks n).1 \ marks n = ∅ := by
  simp only [monitorRun_succ, monitorAdvance_eq]
  split <;> simp_all

lemma monitorRun_pending_succ_of_flag {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark} {n : ℕ}
    (hFlag : (monitorRun req marks (n + 1)).2 = true) :
    (monitorRun req marks (n + 1)).1 = req := by
  rw [monitorRun_flag_succ] at hFlag
  simp only [monitorRun_succ, monitorAdvance_eq, hFlag]
  simp

lemma monitorRun_pending_succ_of_not_flag {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark} {n : ℕ}
    (hFlag : (monitorRun req marks (n + 1)).2 = false) :
    (monitorRun req marks (n + 1)).1 = (monitorRun req marks n).1 \ marks n := by
  have hNe : (monitorRun req marks n).1 \ marks n ≠ ∅ := by
    intro hEmpty
    have hTrue := (monitorRun_flag_succ req marks n).mpr hEmpty
    exact Bool.noConfusion (hTrue.symm.trans hFlag)
  simp only [monitorRun_succ, monitorAdvance_eq, if_neg hNe]

lemma monitorRun_pending_subset_req (req : Finset TypeMark)
    (marks : ℕ → Finset TypeMark) (n : ℕ) :
    (monitorRun req marks n).1 ⊆ req := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hFlag : (monitorRun req marks (n + 1)).2 = true
      · rw [monitorRun_pending_succ_of_flag hFlag]
      · rw [monitorRun_pending_succ_of_not_flag (by simpa using hFlag)]
        exact (Finset.sdiff_subset).trans ih

/-- An unmet requirement stays outstanding while it goes unobserved, whether or
not the monitor completes a round in the meantime. -/
lemma monitorRun_mem_pending {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark} {mark : TypeMark}
    (hReq : mark ∈ req) (start stop : ℕ) (hLe : start ≤ stop)
    (hStart : mark ∈ (monitorRun req marks start).1)
    (hUnseen : ∀ index, start ≤ index → index < stop → mark ∉ marks index) :
    mark ∈ (monitorRun req marks stop).1 := by
  induction stop with
  | zero =>
      have : start = 0 := Nat.le_zero.mp hLe
      exact this ▸ hStart
  | succ stop ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hLe) with hLt | hEq
      · have hPrev : mark ∈ (monitorRun req marks stop).1 :=
          ih (Nat.lt_succ_iff.mp hLt) fun index hLow hHigh =>
            hUnseen index hLow (Nat.lt_succ_of_lt hHigh)
        by_cases hFlag : (monitorRun req marks (stop + 1)).2 = true
        · rw [monitorRun_pending_succ_of_flag hFlag]; exact hReq
        · rw [monitorRun_pending_succ_of_not_flag (by simpa using hFlag)]
          exact Finset.mem_sdiff.mpr
            ⟨hPrev, hUnseen stop (Nat.lt_succ_iff.mp hLt) (Nat.lt_succ_self stop)⟩
      · exact hEq ▸ hStart

/-- While no round completes, the outstanding set only shrinks. -/
lemma monitorRun_pending_mono {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark} (start stop : ℕ) (hLe : start ≤ stop)
    (hNoFlag : ∀ index, start < index → index ≤ stop →
      (monitorRun req marks index).2 = false) :
    (monitorRun req marks stop).1 ⊆ (monitorRun req marks start).1 := by
  induction stop with
  | zero =>
      have : start = 0 := Nat.le_zero.mp hLe
      exact this ▸ subset_rfl
  | succ stop ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hLe) with hLt | hEq
      · have hPrev := ih (Nat.lt_succ_iff.mp hLt) fun index hLow hHigh =>
          hNoFlag index hLow (Nat.le_succ_of_le hHigh)
        have hFlag := hNoFlag (stop + 1) (Nat.lt_succ_of_le (Nat.lt_succ_iff.mp hLt))
          (Nat.le_refl _)
        rw [monitorRun_pending_succ_of_not_flag hFlag]
        exact (Finset.sdiff_subset).trans hPrev
      · exact hEq ▸ subset_rfl

/-- An observed requirement is struck off and stays off while no round
completes. -/
lemma monitorRun_not_mem_pending {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark} {mark : TypeMark}
    (start seen stop : ℕ) (hStartSeen : start ≤ seen) (hSeenStop : seen < stop)
    (hNoFlag : ∀ index, start < index → index ≤ stop →
      (monitorRun req marks index).2 = false)
    (hSeen : mark ∈ marks seen) :
    mark ∉ (monitorRun req marks stop).1 := by
  induction stop with
  | zero => exact absurd hSeenStop (Nat.not_lt_zero seen)
  | succ stop ih =>
      have hFlag := hNoFlag (stop + 1)
        (Nat.lt_succ_of_le (Nat.le_trans hStartSeen (Nat.lt_succ_iff.mp hSeenStop)))
        (Nat.le_refl _)
      rw [monitorRun_pending_succ_of_not_flag hFlag]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hSeenStop with hLt | hEq
      · exact fun hMem =>
          ih hLt (fun index hLow hHigh => hNoFlag index hLow (Nat.le_succ_of_le hHigh))
            (Finset.mem_sdiff.mp hMem).1
      · exact fun hMem => (Finset.mem_sdiff.mp hMem).2 (hEq ▸ hSeen)

/-- From any position the monitor eventually completes a round, provided every
requirement is still observed at some later point. -/
lemma monitorRun_exists_flag {req : Finset TypeMark}
    {marks : ℕ → Finset TypeMark}
    (hAll : ∀ mark ∈ req, ∀ bound, ∃ index, bound ≤ index ∧ mark ∈ marks index) :
    ∀ (budget start : ℕ), (monitorRun req marks start).1.card ≤ budget →
      ∃ stop, start < stop ∧ (monitorRun req marks stop).2 = true := by
  intro budget
  induction budget with
  | zero =>
      intro start hCard
      have hEmpty : (monitorRun req marks start).1 = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hCard)
      exact ⟨start + 1, Nat.lt_succ_self start,
        (monitorRun_flag_succ req marks start).mpr (by simp [hEmpty])⟩
  | succ budget ih =>
      intro start hCard
      by_cases hEmpty : (monitorRun req marks start).1 = ∅
      · exact ⟨start + 1, Nat.lt_succ_self start,
          (monitorRun_flag_succ req marks start).mpr (by simp [hEmpty])⟩
      obtain ⟨mark, hMark⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hReq : mark ∈ req := monitorRun_pending_subset_req req marks start hMark
      obtain ⟨seen, hSeen, hMem⟩ := hAll mark hReq start
      by_cases hFlag :
          ∃ stop, start < stop ∧ stop ≤ seen + 1 ∧ (monitorRun req marks stop).2 = true
      · obtain ⟨stop, hLt, -, hTrue⟩ := hFlag
        exact ⟨stop, hLt, hTrue⟩
      · push_neg at hFlag
        have hNoFlag : ∀ index, start < index → index ≤ seen + 1 →
            (monitorRun req marks index).2 = false := fun index hLow hHigh => by
          simpa using hFlag index hLow hHigh
        have hSubset : (monitorRun req marks (seen + 1)).1 ⊆
            (monitorRun req marks start).1.erase mark := by
          intro other hOther
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · rintro rfl
            exact monitorRun_not_mem_pending start seen (seen + 1) hSeen
              (Nat.lt_succ_self seen) hNoFlag hMem hOther
          · exact monitorRun_pending_mono start (seen + 1)
              (Nat.le_succ_of_le hSeen) hNoFlag hOther
        have hCard' : (monitorRun req marks (seen + 1)).1.card ≤ budget := by
          have := Finset.card_le_card hSubset
          rw [Finset.card_erase_of_mem hMark] at this
          omega
        obtain ⟨stop, hLt, hTrue⟩ := ih (seen + 1) hCard'
        exact ⟨stop, by omega, hTrue⟩

/-- The round-robin recurrence: `M_d` raises its completion flag infinitely
often exactly when every request recurs. -/
theorem monitorRun_flag_infinite_iff (req : Finset TypeMark)
    (marks : ℕ → Finset TypeMark) :
    Set.Infinite {n | (monitorRun req marks n).2 = true} ↔
      ∀ mark ∈ req, Set.Infinite {n | mark ∈ marks n} := by
  rw [set_infinite_nat_iff]
  constructor
  · intro hFlags mark hReq
    rw [set_infinite_nat_iff]
    intro bound
    by_contra hCon
    push_neg at hCon
    have hUnseen : ∀ index, bound ≤ index → mark ∉ marks index := fun index hLe hMem =>
      Nat.not_lt.mpr hLe (hCon index hMem)
    obtain ⟨start, hStartFlag, hStartLe⟩ := hFlags bound
    obtain ⟨stop, hStopFlag, hStopLe⟩ := hFlags (start + 1)
    obtain ⟨start', rfl⟩ : ∃ start', start = start' + 1 := by
      cases start with
      | zero => simp at hStartFlag
      | succ k => exact ⟨k, rfl⟩
    obtain ⟨stop', rfl⟩ : ∃ stop', stop = stop' + 1 := by
      cases stop with
      | zero => simp at hStopFlag
      | succ k => exact ⟨k, rfl⟩
    have hPending : mark ∈ (monitorRun req marks (start' + 1)).1 := by
      rw [monitorRun_pending_succ_of_flag hStartFlag]; exact hReq
    have hStopMem : mark ∈ (monitorRun req marks stop').1 :=
      monitorRun_mem_pending hReq (start' + 1) stop' (by omega) hPending
        fun index hLow _ => hUnseen index (by omega)
    have hEmpty := (monitorRun_flag_succ req marks stop').mp hStopFlag
    have : mark ∈ (monitorRun req marks stop').1 \ marks stop' :=
      Finset.mem_sdiff.mpr ⟨hStopMem, hUnseen stop' (by omega)⟩
    rw [hEmpty] at this
    exact absurd this (Finset.notMem_empty mark)
  · intro hMarks bound
    have hAll : ∀ mark ∈ req, ∀ start, ∃ index, start ≤ index ∧ mark ∈ marks index := by
      intro mark hReq start
      obtain ⟨index, hMem, hLe⟩ := (set_infinite_nat_iff.mp (hMarks mark hReq)) start
      exact ⟨index, hLe, hMem⟩
    obtain ⟨stop, hLt, hTrue⟩ :=
      monitorRun_exists_flag hAll (monitorRun req marks bound).1.card bound (Nat.le_refl _)
    exact ⟨stop, hTrue, by omega⟩

end

end Pact
