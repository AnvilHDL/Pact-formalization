import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

/-- Boundary actions consumed by at least one label of a finite block. -/
def TypeLabel.blockUsed (labels : List TypeLabel) : Finset BareMessage :=
  labels.foldr (fun label used => label.usedEnvironmentActions ∪ used) ∅

namespace TypeEnvironment

/-- Retain promises and remove the immediate actions consumed by a non-clock response. -/
def afterNonclock (env : TypeEnvironment) (label : TypeLabel) : TypeEnvironment :=
  { env with immediate := env.immediate \ label.usedEnvironmentActions }

/-- Update the environment using only the labels already observed in a block. -/
def afterBlock (env : TypeEnvironment) : List TypeLabel → TypeEnvironment
  | [] => env
  | label :: labels => (env.afterNonclock label).afterBlock labels

/-- Removing consumed immediate actions preserves environment admissibility. -/
theorem afterNonclock_wellFormed {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) (label : TypeLabel) :
    (env.afterNonclock label).WellFormed alphabet := by
  refine ⟨?_, ?_, Finset.Subset.trans Finset.sdiff_subset hWF.2.2.1, hWF.2.2.2⟩
  · intro hClock
    obtain ⟨hImmediate, hFuture⟩ := hWF.1 hClock
    simp [afterNonclock, hImmediate, hFuture]
  · intro hClock
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro action hAction
    have hBoth := Finset.mem_inter.mp hAction
    have hImpossible := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hBoth.1).1, hBoth.2⟩
    change action ∈ env.immediate ∩ env.future at hImpossible
    rw [hWF.2.1 hClock] at hImpossible
    simp at hImpossible

/-- The next environment advertises exactly the preceding honesty remainder. -/
theorem available_afterNonclock (env : TypeEnvironment) (label : TypeLabel) :
    typeAvailable (env.afterNonclock label) = env.honestyRemainder label := by
  simp [typeAvailable, afterNonclock, honestyRemainder, Finset.union_comm]

/-- A block update can be computed from any earlier prefix and its subsequent responses. -/
theorem afterBlock_append (env : TypeEnvironment) (before after : List TypeLabel) :
    env.afterBlock (before ++ after) = (env.afterBlock before).afterBlock after := by
  induction before generalizing env with
  | nil => rfl
  | cons label labels ih => exact ih (env.afterNonclock label)

/-- Block updates preserve the fixed alphabet's admissibility. -/
theorem afterBlock_wellFormed {env : TypeEnvironment} {alphabet : PactTypeAlphabet}
    (hWF : env.WellFormed alphabet) (labels : List TypeLabel) :
    (env.afterBlock labels).WellFormed alphabet := by
  induction labels generalizing env with
  | nil => exact hWF
  | cons label labels ih => exact ih (afterNonclock_wellFormed hWF label)

/-- The final environment removes exactly the actions consumed within the block. -/
theorem afterBlock_eq (env : TypeEnvironment) (labels : List TypeLabel) :
    env.afterBlock labels =
      { env with immediate := env.immediate \ TypeLabel.blockUsed labels } := by
  induction labels generalizing env with
  | nil => simp [afterBlock, TypeLabel.blockUsed]
  | cons label labels ih =>
    rw [afterBlock, ih]
    simp only [afterNonclock, TypeLabel.blockUsed, List.foldr_cons]
    congr 1
    ext action
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- Promises remain unchanged until the block boundary. -/
theorem afterBlock_future (env : TypeEnvironment) (labels : List TypeLabel) :
    (env.afterBlock labels).future = env.future := by
  rw [afterBlock_eq]

/-- A block of non-clock updates preserves the environment's clock flag. -/
theorem afterBlock_clock (env : TypeEnvironment) (labels : List TypeLabel) :
    (env.afterBlock labels).clock = env.clock := by
  rw [afterBlock_eq]

/-- An immediate need remains enabled precisely until it is consumed. -/
theorem afterBlock_hasNeed (env : TypeEnvironment) (labels : List TypeLabel)
    (action : BareMessage) :
    (env.afterBlock labels).hasNeed action ↔
      env.hasNeed action ∧ (action.1, action.2.invert) ∉ TypeLabel.blockUsed labels := by
  rw [afterBlock_eq]
  simp [hasNeed]

/-- Splitting a label's consumption leaves exactly its original honesty remainder. -/
theorem available_afterBlock_of_same_used {env : TypeEnvironment}
    {labels : List TypeLabel} {label : TypeLabel}
    (hUsed : TypeLabel.blockUsed labels = label.usedEnvironmentActions) :
    typeAvailable (env.afterBlock labels) = env.honestyRemainder label := by
  rw [afterBlock_eq, hUsed]
  exact available_afterNonclock env label

/-- A successor permitted after the unsplit response is permitted after its split block. -/
theorem successor_available_afterBlock {env next : TypeEnvironment}
    {labels : List TypeLabel} {label : TypeLabel}
    (hUsed : TypeLabel.blockUsed labels = label.usedEnvironmentActions)
    (hNext : typeAvailable next ⊆ env.honestyRemainder label) :
    typeAvailable next ⊆ typeAvailable (env.afterBlock labels) := by
  rw [available_afterBlock_of_same_used hUsed]
  exact hNext

end TypeEnvironment

/-- An observation-preserving split preserves the set of consumed boundary actions. -/
theorem TypeLabel.blockUsed_eq_of_observations {labels : List TypeLabel}
    {label : TypeLabel} (hNonclock : ∀ part ∈ labels, part ≠ .tock)
    (hLabel : label ≠ .tock)
    (hObservations : ∀ observation,
      (∃ part ∈ labels, part.contains observation) ↔ label.contains observation) :
    TypeLabel.blockUsed labels = label.usedEnvironmentActions := by
  have hMem (action : BareMessage) : action ∈ TypeLabel.blockUsed labels ↔
      ∃ part ∈ labels, action ∈ part.usedEnvironmentActions := by
    clear hNonclock hObservations hLabel
    induction labels with
    | nil => simp [TypeLabel.blockUsed]
    | cons part rest ih =>
      change action ∈ part.usedEnvironmentActions ∪ TypeLabel.blockUsed rest ↔ _
      simpa only [Finset.mem_union, List.mem_cons, exists_eq_or_imp] using or_congr Iff.rfl ih
  ext action
  rw [hMem]
  cases label with
  | tock => exact (hLabel rfl).elim
  | actions observations =>
    constructor
    · rintro ⟨part, hPart, hUsed⟩
      cases part with
      | tock => exact (hNonclock _ hPart rfl).elim
      | actions parts =>
        simp only [TypeLabel.usedEnvironmentActions, Finset.mem_biUnion] at hUsed ⊢
        obtain ⟨observation, hObs, hAction⟩ := hUsed
        exact ⟨observation, (hObservations observation).mp ⟨_, hPart, hObs⟩, hAction⟩
    · intro hUsed
      simp only [TypeLabel.usedEnvironmentActions, Finset.mem_biUnion] at hUsed
      obtain ⟨observation, hObs, hAction⟩ := hUsed
      obtain ⟨part, hPart, hContains⟩ := (hObservations observation).mpr hObs
      refine ⟨part, hPart, ?_⟩
      cases part with
      | tock => exact (hNonclock _ hPart rfl).elim
      | actions parts => exact Finset.mem_biUnion.mpr ⟨observation, hContains, hAction⟩

end

end Pact
