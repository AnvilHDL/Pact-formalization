import Anvilpp.PactTypes.Spec.Automata.SyncEdgesDefs

namespace Pact

noncomputable section

/-- A clocked parent environment projects to `tock`. -/
theorem projectAutomatonEnvironment_of_clock {alphabet : PactTypeAlphabet}
    {environment : TypeEnvironment} (hClock : environment.clock = true) :
    projectAutomatonEnvironment alphabet environment = TypeEnvironment.tock := by
  simp [projectAutomatonEnvironment, hClock]

end

end Pact
