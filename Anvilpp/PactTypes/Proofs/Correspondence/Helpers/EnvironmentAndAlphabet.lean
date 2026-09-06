import Anvilpp.ProofHelpers
import Anvilpp.PactTypes.Proofs.Correspondence.CompileWFHelpers

namespace Pact

noncomputable section

open Classical
open Pact.NewCorrespondence

@[simp] theorem PactTypeAlphabet.mem_localOfferSummaries_iff
    (alphabet : PactTypeAlphabet)
    (current future : Finset BareMessage) :
    TypeOfferSummary.mk current future ∈
        alphabet.localOfferSummaries ↔
      current ⊆ alphabet.actions ∧
      future ⊆ alphabet.actions := by
  classical
  simp [PactTypeAlphabet.localOfferSummaries]

/- Decorated type transitions are intentionally not target-deterministic.  For
example, an unresolved choice may silently select either branch while exposing
the same offers.  The correspondence proof therefore establishes target
relation membership with the relation clause for the source constructor. -/

/-- Proves a built relation set relates each automaton state to at most one residual. -/
lemma relationMembership_functional
    (ty : PactType) (auto : TypeAutomaton)
    {residual residual' : PactType} {state : TypeAutomatonState}
    (hRelated : relationMembership (buildRelationSet ty auto) residual state)
    (hRelated' : relationMembership (buildRelationSet ty auto) residual' state) :
    residual = residual' := by
  unfold relationMembership buildRelationSet at hRelated hRelated'
  exact buildRelationSetCore_functional ty hRelated hRelated'

end

end Pact
