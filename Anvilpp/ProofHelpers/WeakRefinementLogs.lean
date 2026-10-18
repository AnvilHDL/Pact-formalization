import Anvilpp.ProofHelpers.RoundRobin

namespace Pact

noncomputable section

open Classical

/-- Boundaries of finite, nonempty blocks covering every round of an infinite log. -/
structure RoundPartition where
  cut : Nat → Nat
  zero : cut 0 = 0
  increasing : StrictMono cut

namespace RoundPartition

def InBlock (partition : RoundPartition) (block index : Nat) : Prop :=
  partition.cut block ≤ index ∧ index < partition.cut (block + 1)

def Occurs (partition : RoundPartition) (predicate : Nat → Prop) (block : Nat) : Prop :=
  ∃ index, partition.InBlock block index ∧ predicate index

/-- Every round belongs to a finite block. -/
theorem exists_block (partition : RoundPartition) (index : Nat) :
    ∃ block, partition.InBlock block index := by
  have hBound : ∃ n, index < partition.cut n :=
    ⟨index + 1, lt_of_lt_of_le (Nat.lt_succ_self index) partition.increasing.le_apply⟩
  have hPositive : 0 < Nat.find hBound := by
    have hFound := Nat.find_spec hBound
    by_contra h
    have hZero : Nat.find hBound = 0 := by omega
    rw [hZero, partition.zero] at hFound
    omega
  refine ⟨Nat.find hBound - 1, ?_, ?_⟩
  · have hMinimal := Nat.find_min hBound (show Nat.find hBound - 1 < Nat.find hBound by omega)
    omega
  · simpa [Nat.sub_add_cancel hPositive] using Nat.find_spec hBound

/-- Infinitely many occurrences are equivalent to infinitely many blocks containing one. -/
theorem infinite_iff_blocks (partition : RoundPartition) (predicate : Nat → Prop) :
    Set.Infinite {index | predicate index} ↔
      Set.Infinite {block | partition.Occurs predicate block} := by
  rw [set_infinite_nat_iff, set_infinite_nat_iff]
  constructor
  · intro hInfinite bound
    obtain ⟨index, hPredicate, hBound⟩ := hInfinite (partition.cut bound)
    obtain ⟨block, hLow, hHigh⟩ := partition.exists_block index
    refine ⟨block, ⟨index, ⟨hLow, hHigh⟩, hPredicate⟩, ?_⟩
    by_contra h
    have hLe : block + 1 ≤ bound := by omega
    have := partition.increasing.monotone hLe
    omega
  · intro hInfinite bound
    obtain ⟨block, ⟨index, ⟨hLow, _⟩, hPredicate⟩, hBound⟩ := hInfinite bound
    exact ⟨index, hPredicate,
      hBound.trans (partition.increasing.le_apply.trans hLow)⟩

/-- A partition with one round in each block. -/
def singleton : RoundPartition := ⟨id, rfl, strictMono_id⟩

@[simp] theorem occurs_singleton (predicate : Nat → Prop) (block : Nat) :
    singleton.Occurs predicate block ↔ predicate block := by
  constructor
  · rintro ⟨index, ⟨hLow, hHigh⟩, hPredicate⟩
    have : index = block := by change block ≤ index at hLow; change index < block + 1 at hHigh; omega
    simpa [this] using hPredicate
  · intro hPredicate
    exact ⟨block, ⟨le_rfl, Nat.lt_succ_self _⟩, hPredicate⟩

end RoundPartition

/-- Corresponding finite blocks contain the same observations and agree on clock occurrence. -/
structure TypeLogBlockMatch (left right : TypeLog) where
  leftBlocks : RoundPartition
  rightBlocks : RoundPartition
  observations : ∀ observation block,
    leftBlocks.Occurs (fun index => (left index).2.contains observation) block ↔
      rightBlocks.Occurs (fun index => (right index).2.contains observation) block
  clocks : ∀ block,
    leftBlocks.Occurs (fun index => (left index).2 = TypeLabel.tock) block ↔
      rightBlocks.Occurs (fun index => (right index).2 = TypeLabel.tock) block

namespace TypeLogBlockMatch

private theorem infinite_iff {left right : RoundPartition} {p q : Nat → Prop}
    (agreement : ∀ block, left.Occurs p block ↔ right.Occurs q block) :
    Set.Infinite {index | p index} ↔ Set.Infinite {index | q index} := by
  rw [left.infinite_iff_blocks p, right.infinite_iff_blocks q]
  have hSets : {block | left.Occurs p block} = {block | right.Occurs q block} :=
    Set.ext agreement
  rw [hSets]

/-- Finite regrouping preserves recurrence of each observation. -/
theorem observation_iff {left right : TypeLog} (matching : TypeLogBlockMatch left right)
    (observation : TypeObservation) :
    TypeObservationOccursInfinitely observation left ↔
      TypeObservationOccursInfinitely observation right :=
  infinite_iff (matching.observations observation)

/-- Finite regrouping preserves recurring clocks. -/
theorem tock_iff {left right : TypeLog} (matching : TypeLogBlockMatch left right) :
    TypeTockOccursInfinitely left ↔ TypeTockOccursInfinitely right :=
  infinite_iff matching.clocks

/-- Matching blocks preserve fairness for equal fair-choice identifier sets. -/
theorem fair_iff {left right : TypeLog} (matching : TypeLogBlockMatch left right)
    {precise abstract : PactType} (hIds : typeFairIds precise = typeFairIds abstract) :
    FairTypeLog precise left ↔ FairTypeLog abstract right := by
  simp only [FairTypeLog, matching.observation_iff, hIds]

/-- A winning matching log transfers its objective when the receiving log is honest. -/
theorem winning_of_honest {left right : TypeLog} (matching : TypeLogBlockMatch left right)
    {precise abstract : PactType} {progress : Finset ProcId}
    (hIds : typeFairIds precise = typeFairIds abstract) (hHonest : HonestTypeLog left)
    (hWinning : TypeWinningObjective abstract progress right) :
    TypeWinningObjective precise progress left := by
  refine ⟨hHonest, matching.tock_iff.mpr hWinning.2.1, ?_⟩
  intro hFair pid hPid
  exact (matching.observation_iff (.progress pid)).mpr
    (hWinning.2.2 ((matching.fair_iff hIds).mp hFair) pid hPid)

end TypeLogBlockMatch

/-- Each original round is preceded by finitely many silent entries under its environment. -/
structure TypeLogSilentExpansion (expanded original : TypeLog) where
  blocks : RoundPartition
  entry : ∀ block index, blocks.InBlock block index →
    expanded index = ((original block).1,
      if index + 1 = blocks.cut (block + 1) then (original block).2 else TypeLabel.silent)

namespace TypeLogSilentExpansion

private theorem last_in_block (blocks : RoundPartition) (block : Nat) :
    blocks.InBlock block (blocks.cut (block + 1) - 1) := by
  have : blocks.cut block < blocks.cut (block + 1) :=
    blocks.increasing (Nat.lt_succ_self block)
  change blocks.cut block ≤ blocks.cut (block + 1) - 1 ∧
    blocks.cut (block + 1) - 1 < blocks.cut (block + 1)
  constructor <;> omega

private theorem last_entry {expanded original : TypeLog}
    (expansion : TypeLogSilentExpansion expanded original) (block : Nat) :
    expanded (expansion.blocks.cut (block + 1) - 1) = original block := by
  have hPositive : expansion.blocks.cut block < expansion.blocks.cut (block + 1) :=
    expansion.blocks.increasing (Nat.lt_succ_self block)
  rw [expansion.entry block _ (last_in_block _ _)]
  simp [show expansion.blocks.cut (block + 1) - 1 + 1 =
    expansion.blocks.cut (block + 1) by omega]

/-- Silent insertion does not add or remove an observation from its original round's block. -/
def blockMatch {expanded original : TypeLog}
    (expansion : TypeLogSilentExpansion expanded original) :
    TypeLogBlockMatch expanded original where
  leftBlocks := expansion.blocks
  rightBlocks := .singleton
  observations := by
    intro observation block
    rw [RoundPartition.occurs_singleton]
    constructor
    · rintro ⟨index, hIn, hOccurs⟩
      rw [expansion.entry block index hIn] at hOccurs
      split_ifs at hOccurs with hLast
      · exact hOccurs
      · simp [TypeLabel.contains, TypeLabel.silent] at hOccurs
    · intro hOccurs
      exact ⟨_, last_in_block _ _, by simpa [expansion.last_entry] using hOccurs⟩
  clocks := by
    intro block
    rw [RoundPartition.occurs_singleton]
    constructor
    · rintro ⟨index, hIn, hClock⟩
      rw [expansion.entry block index hIn] at hClock
      split_ifs at hClock with hLast
      · exact hClock
      · simp [TypeLabel.silent] at hClock
    · intro hClock
      exact ⟨_, last_in_block _ _, by simpa [expansion.last_entry] using hClock⟩

/-- Retained-offer honesty is preserved by finite silent insertion under unchanged environments. -/
theorem honest {expanded original : TypeLog}
    (expansion : TypeLogSilentExpansion expanded original) (hHonest : HonestTypeLog original) :
    HonestTypeLog expanded := by
  intro index
  obtain ⟨block, hIn⟩ := expansion.blocks.exists_block index
  by_cases hLast : index + 1 = expansion.blocks.cut (block + 1)
  · have hNext : expansion.blocks.InBlock (block + 1) (index + 1) := by
      rw [hLast]
      exact ⟨le_rfl, expansion.blocks.increasing (Nat.lt_succ_self _)⟩
    rw [expansion.entry block index hIn, expansion.entry (block + 1) (index + 1) hNext]
    simpa [hLast] using hHonest block
  · have hNext : expansion.blocks.InBlock block (index + 1) := by
      rcases hIn with ⟨hLow, hHigh⟩
      constructor <;> omega
    rw [expansion.entry block index hIn, expansion.entry block (index + 1) hNext]
    apply Or.inr
    simp [hLast, typeAvailable, TypeEnvironment.honestyRemainder_silent,
      Finset.union_comm]

/-- Finite silent insertion preserves the complete compatibility objective. -/
theorem winning {expanded original : TypeLog}
    (expansion : TypeLogSilentExpansion expanded original)
    {precise abstract : PactType} {progress : Finset ProcId}
    (hIds : typeFairIds precise = typeFairIds abstract)
    (hWinning : TypeWinningObjective abstract progress original) :
    TypeWinningObjective precise progress expanded :=
  expansion.blockMatch.winning_of_honest hIds (expansion.honest hWinning.1) hWinning

end TypeLogSilentExpansion

end

end Pact
