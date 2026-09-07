import Anvilpp.ProofHelpers.CompatibilityGame

namespace Pact

noncomputable section

open Classical

/-! ## Fixed component compositions -/

/-- Right-associated composition with explicit interfaces. -/
def composeTypes : List PactType → List Interface → Option PactType
  | [], _ => none
  | [processType], [] => some processType
  | processType :: next :: rest, interface :: interfaces =>
      match composeTypes (next :: rest) interfaces with
      | some suffix => some (parallelType processType suffix interface)
      | none => none
  | _, _ => none

/-- Right-associated parallel composition, mirroring `parallelType`: the
parent alphabet is the two child alphabets with the interface hidden. -/
def parallelProc (left right : Proc) (interface : Interface) : Proc :=
  .par (PactTypeAlphabet.mergeHidden left.alphabet right.alphabet interface)
    left right interface

def composeProcesses : List Proc → List Interface → Option Proc
  | [], _ => none
  | [process], [] => some process
  | process :: next :: rest, interface :: interfaces =>
      match composeProcesses (next :: rest) interfaces with
      | some suffix => some (parallelProc process suffix interface)
      | none => none
  | _, _ => none

def TypeTupleCompatible
    (types : List PactType) (interfaces : List Interface)
    (progress : Finset ProcId) : Prop :=
  ∃ composition,
    composeTypes types interfaces = some composition ∧
    TypeCompatible composition progress

def ComponentwiseRefines (precise abstract : List PactType) : Prop :=
  List.Forall₂ Refines precise abstract

/-- Composition succeeds on any tuple of the same length: the fixed
parenthesization only inspects the shape of the two lists. -/
lemma composeTypes_congr_length : ∀ (precise abstract : List PactType)
    (interfaces : List Interface) (composition : PactType),
    precise.length = abstract.length →
    composeTypes abstract interfaces = some composition →
    ∃ preciseComposition, composeTypes precise interfaces = some preciseComposition := by
  intro precise
  induction precise with
  | nil =>
      intro abstract interfaces composition hLength hAbstract
      have hNil : abstract = [] := List.eq_nil_of_length_eq_zero hLength.symm
      subst hNil
      simp [composeTypes] at hAbstract
  | cons head rest ih =>
      intro abstract interfaces composition hLength hAbstract
      cases rest with
      | nil =>
          obtain ⟨single, rfl⟩ : ∃ single, abstract = [single] := by
            cases abstract with
            | nil => simp at hLength
            | cons a as =>
                cases as with
                | nil => exact ⟨a, rfl⟩
                | cons _ _ => simp at hLength
          cases interfaces with
          | nil => exact ⟨head, rfl⟩
          | cons i is => simp [composeTypes] at hAbstract
      | cons next tail =>
          obtain ⟨first, second, more, rfl⟩ :
              ∃ first second more, abstract = first :: second :: more := by
            cases abstract with
            | nil => simp at hLength
            | cons a as =>
                cases as with
                | nil => simp at hLength
                | cons b bs => exact ⟨a, b, bs, rfl⟩
          cases interfaces with
          | nil => simp [composeTypes] at hAbstract
          | cons i is =>
              rw [composeTypes] at hAbstract
              cases hSuffix : composeTypes (second :: more) is with
              | none => rw [hSuffix] at hAbstract; simp at hAbstract
              | some suffix =>
                  obtain ⟨preciseSuffix, hPreciseSuffix⟩ :=
                    ih (second :: more) is suffix (by simpa using hLength) hSuffix
                  refine ⟨parallelType head preciseSuffix i, ?_⟩
                  rw [composeTypes, hPreciseSuffix]

/-! ## Objectives and strategy transfer -/

end

end Pact
