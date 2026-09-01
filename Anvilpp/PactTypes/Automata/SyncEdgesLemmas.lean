import Anvilpp.PactTypes.Automata.SyncEdgesDefs

namespace Pact

noncomputable section

/-- A clocked parent environment projects to `tock`. -/
theorem projectAutomatonEnvironment_of_clock {alphabet : PactTypeAlphabet}
    {environment : TypeEnvironment} (hClock : environment.clock = true) :
    projectAutomatonEnvironment alphabet environment = TypeEnvironment.tock := by
  simp [projectAutomatonEnvironment, hClock]

/-- Only a clocked parent environment has a clocked projection. -/
theorem clock_of_projectAutomatonEnvironment_clock {alphabet : PactTypeAlphabet}
    {environment : TypeEnvironment}
    (hClock : (projectAutomatonEnvironment alphabet environment).clock = true) :
    environment.clock = true := by
  by_cases hParent : environment.clock
  · exact hParent
  · simp [projectAutomatonEnvironment, hParent] at hClock

end

end Pact
