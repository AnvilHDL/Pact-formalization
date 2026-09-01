import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas
import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Syntax.TypeLabelCombine

namespace Pact

set_option maxHeartbeats 1000000

open Classical

/-! ## Label ownership -/

/-- Every observation a label carries is declared by the type the step started from:
message actions by `MessageActions`/`MessageIds`, progress identifiers by `ProgressIds`,
fair-choice identifiers by `FairChoiceIds`, and a resolved message by the interface of
some parallel binder inside the type — which is also a message name the type uses. -/
def PactType.LabelOwned (source : PactType) (label : TypeLabel) : Prop :=
  (∀ msg dir, label.contains (.message msg dir) →
      (msg, dir) ∈ source.MessageActions ∧ msg ∈ source.MessageIds) ∧
    (∀ pid, label.contains (.progress pid) → pid ∈ source.ProgressIds) ∧
    (∀ bid taken, label.contains (.fair bid taken) → bid ∈ source.FairChoiceIds) ∧
    (∀ msg, label.contains (.resolved msg) →
      msg ∈ source.ParallelInterfaces ∧ msg ∈ source.MessageIds)

end Pact
