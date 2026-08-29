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

def composeProcesses : List Proc → List Interface → Option Proc
  | [], _ => none
  | [process], [] => some process
  | process :: next :: rest, interface :: interfaces =>
      match composeProcesses (next :: rest) interfaces with
      | some suffix =>
          some (.par
            (PactTypeAlphabet.mergeHidden process.alphabet suffix.alphabet
              interface)
            process suffix interface)
      | none => none
  | _, _ => none

def TypeTupleCompatible (signature : TypeAlphabet)
    (types : List PactType) (interfaces : List Interface)
    (progress : Finset ProcId) : Prop :=
  ∃ composition,
    composeTypes types interfaces = some composition ∧
    TypeCompatible signature composition progress

def ComponentwiseRefines (precise abstract : List PactType) : Prop :=
  List.Forall₂ Refines precise abstract

/-! ## Objectives and strategy transfer -/

end

end Pact
