import Anvilpp.ProofHelpers.Process
import Anvilpp.ProofHelpers.TypeSemantics

namespace Pact

noncomputable section

open Classical

def eraseProcessLog (log : ProcessLog) : TypeLog :=
  fun index =>
    (eraseEnvironment (log index).1, eraseLabel (log index).2)

abbrev ProcessObjective := Set ProcessLog

def ValueOblivious (objective : ProcessObjective) : Prop :=
  ∀ left right,
    eraseProcessLog left = eraseProcessLog right →
    (left ∈ objective ↔ right ∈ objective)

def ErasedObjective (objective : ProcessObjective) (log : TypeLog) : Prop :=
  ∃ processLog,
    eraseProcessLog processLog = log ∧ processLog ∈ objective

end

end Pact
