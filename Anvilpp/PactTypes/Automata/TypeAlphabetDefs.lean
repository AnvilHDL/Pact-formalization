import Anvilpp.PactTypes.Syntax.PactTypeRegularityLemmas
import Anvilpp.PactTypes.Syntax.TypeTransitionSystemLemmas

namespace Pact

noncomputable section

/-! ## Constructor-based finite automata -/

namespace PactTypeAlphabet

  /-- Environment polarities complementary to the actions a type declares. -/
  def localEnvironmentActions (alphabet : PactTypeAlphabet) : Finset BareMessage :=
    alphabet.actions.image typeNeed

  /-- Well-formed environments over the actions a type declares. -/
  def localEnvironments (alphabet : PactTypeAlphabet) : Finset TypeEnvironment :=
    {TypeEnvironment.tock} ∪
      alphabet.localEnvironmentActions.powerset.biUnion fun immediate =>
        (alphabet.localEnvironmentActions \ immediate).powerset.image fun future =>
          { immediate := immediate, future := future, clock := false }

  /-- Offer summaries over the actions a type declares. -/
  def localOfferSummaries (alphabet : PactTypeAlphabet) : Finset TypeOfferSummary :=
    alphabet.actions.powerset.biUnion fun current =>
      alphabet.actions.powerset.image fun future =>
        { current := current, future := future }

end PactTypeAlphabet

namespace PactType

  /-- Both polarities of every message a type synchronizes on. -/
  def interfaceActions (processType : PactType) : Finset BareMessage :=
    (PactType.ParallelInterfaces processType).biUnion fun msg =>
      {(msg, .send), (msg, .recv)}

  /-- Actions a type may name in a label: the ones it declares, plus the
  interface actions an enclosing parallel node has yet to hide. -/
  def localActionsWithInterface (processType : PactType) : Finset BareMessage :=
    processType.alphabet.actions ∪ processType.interfaceActions

  /-- Observations a type may emit, all read off its own syntax. -/
  def observations (processType : PactType) : Finset TypeObservation :=
    processType.localActionsWithInterface.image
        (fun action => TypeObservation.message action.1 action.2) ∪
      (PactType.ParallelInterfaces processType).image TypeObservation.resolved ∪
      (PactType.ProgressIds processType).image TypeObservation.progress ∪
      (PactType.FairChoiceIds processType).biUnion (fun bid =>
        {TypeObservation.fair bid false, TypeObservation.fair bid true})

  /-- `Lab_τ = 2^(Label(τ)) ∪ {#}`; the empty subset is epsilon. -/
  def labels (processType : PactType) : Finset TypeLabel :=
    processType.observations.powerset.image TypeLabel.actions ∪ {TypeLabel.tock}

end PactType

/-- One letter of the decorated transition alphabet `Σ_τ`. -/
structure TypeAutomatonSymbol : Type where
  environment : TypeEnvironment
  label : TypeLabel
  offers : TypeOfferSummary
  deriving DecidableEq

/-- `Σ_τ`, read entirely off the type: environments and offers from the actions
it declares, labels from those actions together with the interfaces it resolves
and the identifiers its syntax mentions. -/
def PactType.transitionAlphabet (processType : PactType) :
    Finset TypeAutomatonSymbol :=
  processType.alphabet.localEnvironments.biUnion fun environment =>
    processType.labels.biUnion fun label =>
      processType.alphabet.localOfferSummaries.image fun offers =>
        { environment := environment, label := label, offers := offers }

end

end Pact
