import Anvilpp.PactTypes.Proofs.Automata.FiniteMenuGraph
import Anvilpp.PactTypes.Proofs.Automata.PendingAutomatonFutureLemmas

namespace Pact

noncomputable section

def menuDependencyTargets
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState))
    (source : TypeAutomatonState) : Finset TypeAutomatonState :=
  (dependencies.filter fun link => link.1 = source).image Prod.snd


namespace PendingAutomaton

def withMenuDependencies (automaton : PendingAutomaton)
    (dependencies : Finset (TypeAutomatonState × TypeAutomatonState)) :
    FiniteMenuGraph :=
  { states := automaton.states
    referencedStates := fun source =>
      automaton.menuStep source ∪
        menuDependencyTargets dependencies source }


end PendingAutomaton

end

end Pact
