import Anvilpp.ProofHelpers.WeakRefinementLogs
import Anvilpp.ProofHelpers.PrefixPlayMatch

namespace Pact

noncomputable section

open Classical

/-- A strategy supplies an admissible environment at every prefix it generates. -/
def WellFormedTypeStrategy (initial : PactType) (strategy : TypeStrategy) : Prop :=
  ∀ history, FollowsTypeStrategy initial strategy history →
    (strategy history.entries).WellFormed initial.alphabet

/-- Matching finite blocks contain at most one clock, at their common closing boundary. -/
structure TypeLogClockBlockMatch (left right : TypeLog) extends TypeLogBlockMatch left right where
  leftClockLast : ∀ block index, leftBlocks.InBlock block index →
    (left index).2 = .tock → index + 1 = leftBlocks.cut (block + 1)
  rightClockLast : ∀ block index, rightBlocks.InBlock block index →
    (right index).2 = .tock → index + 1 = rightBlocks.cut (block + 1)

namespace TypeLogClockBlockMatch

/-- Identical logs match in singleton blocks. -/
def refl (log : TypeLog) : TypeLogClockBlockMatch log log where
  leftBlocks := .singleton
  rightBlocks := .singleton
  observations := fun _ _ => Iff.rfl
  clocks := fun _ => Iff.rfl
  leftClockLast := by
    intro block index hIn _
    change block ≤ index ∧ index < block + 1 at hIn
    change index + 1 = block + 1
    omega
  rightClockLast := by
    intro block index hIn _
    change block ≤ index ∧ index < block + 1 at hIn
    change index + 1 = block + 1
    omega

private def leadingPair : RoundPartition where
  cut
    | 0 => 0
    | n + 1 => n + 2
  zero := rfl
  increasing := by
    intro a b h
    cases a <;> cases b <;> simp_all

private theorem occurs_leadingPair (predicate : Nat → Prop) (block : Nat) :
    leadingPair.Occurs predicate block ↔
      (if block = 0 then predicate 0 ∨ predicate 1 else predicate (block + 1)) := by
  cases block with
  | zero =>
      simp only [RoundPartition.Occurs, RoundPartition.InBlock, leadingPair, if_true]
      constructor
      · rintro ⟨index, hIn, hPredicate⟩
        have : index = 0 ∨ index = 1 := by omega
        rcases this with rfl | rfl
        · exact Or.inl hPredicate
        · exact Or.inr hPredicate
      · rintro (hZero | hOne)
        · exact ⟨0, by omega, hZero⟩
        · exact ⟨1, by omega, hOne⟩
  | succ block =>
      simp only [RoundPartition.Occurs, RoundPartition.InBlock, leadingPair,
        Nat.succ_ne_zero, if_false]
      constructor
      · rintro ⟨index, hIn, hPredicate⟩
        have : index = block + 2 := by omega
        simpa [this] using hPredicate
      · exact fun h => ⟨block + 2, by omega, h⟩

/-- A silent first round can be grouped with the next round, even if environments differ. -/
def silentHead {log : TypeLog} (hSilent : (log 0).2 = TypeLabel.silent) :
    TypeLogClockBlockMatch log (fun n => log (n + 1)) where
  leftBlocks := leadingPair
  rightBlocks := .singleton
  observations := by
    intro observation block
    rw [occurs_leadingPair, RoundPartition.occurs_singleton]
    split_ifs with hZero
    · subst block
      simp [hSilent, TypeLabel.contains, TypeLabel.silent]
    · rfl
  clocks := by
    intro block
    rw [occurs_leadingPair, RoundPartition.occurs_singleton]
    split_ifs with hZero
    · subst block
      simp [hSilent, TypeLabel.silent]
    · rfl
  leftClockLast := by
    intro block index hIn hClock
    cases block with
    | zero =>
        have hIndex : index ≠ 0 := by
          rintro rfl
          simp [hSilent, TypeLabel.silent] at hClock
        change 0 ≤ index ∧ index < 2 at hIn
        change index + 1 = 2
        omega
    | succ block =>
        change block + 2 ≤ index ∧ index < block + 3 at hIn
        change index + 1 = block + 3
        omega
  rightClockLast := by
    intro block index hIn _
    change block ≤ index ∧ index < block + 1 at hIn
    change index + 1 = block + 1
    omega

end TypeLogClockBlockMatch

/-- Strategy comparison by honest completed executions with clock-aligned finite blocks. -/
structure HonestBlockRefinement (precise abstract : PactType) : Prop where
  alphabet : precise.alphabet = abstract.alphabet
  fairIds : typeFairIds precise = typeFairIds abstract
  progressIds : precise.ProgressIds = abstract.ProgressIds
  transfer : ∀ strategy, WellFormedTypeStrategy abstract strategy →
    HonestTypeStrategy abstract strategy →
    ∃ preciseStrategy,
      WellFormedTypeStrategy precise preciseStrategy ∧
      HonestTypeStrategy precise preciseStrategy ∧
      ∀ log, CompletedTypeLog precise preciseStrategy log →
        ∃ abstractLog, CompletedTypeLog abstract strategy abstractLog ∧
          Nonempty (TypeLogClockBlockMatch log abstractLog)

namespace HonestBlockRefinement

/-- Each strategy matches itself without changing its rounds. -/
theorem refl (source : PactType) : HonestBlockRefinement source source := by
  refine ⟨rfl, rfl, rfl, fun strategy hWF hHonest =>
    ⟨strategy, hWF, hHonest, fun log hCompleted => ?_⟩⟩
  exact ⟨log, hCompleted, ⟨TypeLogClockBlockMatch.refl log⟩⟩

/-- Honest block comparison transfers the semantic compatibility objective. -/
theorem semantic_compatible {precise abstract : PactType} {progress : Finset ProcId}
    (refinement : HonestBlockRefinement precise abstract)
    (hWF : TypeWellFormedIn [] abstract)
    (hCompatible : SemanticTypeCompatible abstract progress) :
    SemanticTypeCompatible precise progress := by
  obtain ⟨strategy, hWins⟩ := hCompatible
  obtain ⟨preciseStrategy, _, hHonest, hMatch⟩ := refinement.transfer strategy
    (fun _ hFollows => strategy_wellFormed hWF hWins hFollows)
    (fun log hCompleted => (hWins log hCompleted).1)
  refine ⟨preciseStrategy, fun log hCompleted => ?_⟩
  obtain ⟨abstractLog, hAbstract, ⟨matching⟩⟩ := hMatch log hCompleted
  exact matching.toTypeLogBlockMatch.winning_of_honest refinement.fairIds
    (hHonest log hCompleted) (hWins abstractLog hAbstract)

/-- Honest block comparison transfers compiled-game compatibility for well-formed types. -/
theorem compatible {precise abstract : PactType} {progress : Finset ProcId}
    (refinement : HonestBlockRefinement precise abstract)
    (hPrecise : TypeWellFormedIn [] precise) (hAbstract : TypeWellFormedIn [] abstract)
    (hCompatible : TypeCompatible abstract progress) : TypeCompatible precise progress :=
  game_reduction_backward hPrecise
    (refinement.semantic_compatible hAbstract (game_reduction_forward hAbstract hCompatible))

end HonestBlockRefinement

end

end Pact
